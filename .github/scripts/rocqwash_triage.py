#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""rocqwash_triage.py - Main CI furnace red triage via the local rocqwash MCP
server (workflow rocqwash-triage.yml companion driver, 20261114).

Purpose.  When the Main CI 9.3 furnace goes red, this driver speaks MCP over
stdio to the resident rocqwash MCP server and asks it to triage the failed
run, then records the verdict in the rocqwash experience ledger.  It writes
three artifact files for upload and optionally mirrors them into the desk
inbox directory on this machine (the runner is the desk machine itself).

MCP conversation (newline-delimited JSON-RPC 2.0):
    initialize -> notifications/initialized
    tools/call ci_triage   {repo, run}          -> triage report text
    tools/call exp_append  {tool, points, ...}  -> ledger entry id text

The ci_triage tool fetches the failed run's job logs itself (read-only GET,
token from the machine ~/.netrc github.com line).  It is net-gated at the
tool level, so the server is launched with ROCQWASH_MCP_ALLOW_NET=1, the
same wiring as the user-level MCP config.

Verdict handling.  A red verdict is data, not a tool failure: the driver
exits 0 whenever a triage report was obtained.  Non-zero exits mean the
watch leg itself is broken (wiring, protocol, or the triage tool returned
a failed result) so the job shows red and the desk sees it.

Exit codes.  0 = triage report obtained; 2 = MCP wiring or protocol
failure; 3 = triage tool returned a failed result; 4 = usage error.

Config surface (env overrides, defaults mirror the user-level MCP config):
    ROCQWASH_HOME        root handed to the server (default D:/ComplexAnalysis/rocqwash)
    ROCQWASH_PYTHON      interpreter for the server (default C:\\Program Files\\Python313\\python.exe)
    ROCQWASH_SERVER      server script path (default <HOME>/tools/mcp_server.py)
"""
import argparse
import datetime
import json
import os
import re
import shutil
import subprocess
import sys
import threading
import time
import queue
import urllib.error
import urllib.request

SCHEMA = "rocqwash-watch/1"

DEFAULT_HOME = r"D:/ComplexAnalysis/rocqwash"
DEFAULT_PYTHON = r"C:\Program Files\Python313\python.exe"
DEFAULT_MIRROR = r"D:/ComplexAnalysis/ConstructiveWorld-Main"
FURNACE_WORKFLOW_FILE = "coq93.yml"
FURNACE_NAME = "Main CI 9.3"
RECONCILE_WINDOW_H = 48
RECONCILE_MAX_PER_PASS = 2
MAX_QUEUED_FURNACE_RUNS = 3
AUTOFIX_BUDGET_PER_BRANCH = 2

INIT_RESULT_ID = 1
TRIAGE_RESULT_ID = 2
LEDGER_RESULT_ID = 3
HEAL_LEDGER_RESULT_ID = 4

VERDICT_RE = re.compile(r"RUN VERDICT: family=(\S+) .*? action=(\S+)")

# Families the heal leg may act on: rerun-safe transient classes only.
# Content reds are handled by the autofix leg (mechanical comment-surface
# surgery) when its rewrite coverage is sufficient; non-coverable residue
# is reported for the seat.
HEAL_ACTIONS = {"rerun-after-stable-window"}
HEAL_FAMILIES = {"runner-lost", "E-runner-lost"}
HEAL_BUDGET_PER_RUN = 1


def log(msg):
    sys.stdout.write("[triage] %s\n" % msg)
    sys.stdout.flush()


class McpClient(object):
    """Minimal newline-delimited JSON-RPC 2.0 client over stdin/stdout."""

    def __init__(self, python_exe, server_script, home, timeout_s):
        env = dict(os.environ)
        env["ROCQWASH_HOME"] = home
        env["ROCQWASH_MCP_ALLOW_NET"] = "1"
        env.setdefault("PYTHONIOENCODING", "utf-8")
        self.proc = subprocess.Popen(
            [python_exe, "-I", server_script],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            env=env,
        )
        self.timeout_s = timeout_s
        self.deadline = time.time() + timeout_s
        self.lines = queue.Queue()
        self.stderr_chunks = []
        self._reader = threading.Thread(target=self._pump, daemon=True)
        self._reader.start()
        self._errpump = threading.Thread(target=self._pump_err, daemon=True)
        self._errpump.start()
        self._next_id = 0

    def _pump(self):
        for raw in self.proc.stdout:
            self.lines.put(raw.decode("utf-8", errors="replace").strip())

    def _pump_err(self):
        for raw in self.proc.stderr:
            self.stderr_chunks.append(raw.decode("utf-8", errors="replace"))

    def _send(self, obj):
        self.proc.stdin.write((json.dumps(obj) + "\n").encode("utf-8"))
        self.proc.stdin.flush()

    def request(self, method, params, result_id):
        self._send({"jsonrpc": "2.0", "id": result_id, "method": method,
                    "params": params})
        while True:
            remaining = self.deadline - time.time()
            if remaining <= 0:
                raise RuntimeError("MCP deadline exceeded (%ds)" % self.timeout_s)
            try:
                line = self.lines.get(timeout=remaining)
            except queue.Empty:
                raise RuntimeError("MCP deadline exceeded while waiting for id=%d" % result_id)
            if not line:
                continue
            try:
                msg = json.loads(line)
            except ValueError:
                continue  # not a JSON line; skip
            if msg.get("id") != result_id:
                continue  # not our response
            if "error" in msg:
                raise RuntimeError("MCP error for %s: %s" % (method, msg["error"]))
            return msg.get("result") or {}

    def notify(self, method):
        self._send({"jsonrpc": "2.0", "method": method})

    def close(self):
        try:
            self.proc.stdin.close()
        except Exception:
            pass
        try:
            self.proc.wait(timeout=15)
        except Exception:
            self.proc.kill()

    def stderr_text(self):
        return "".join(self.stderr_chunks)


def call_tool(client, name, arguments, result_id):
    result = client.request("tools/call",
                            {"name": name, "arguments": arguments}, result_id)
    is_error = bool(result.get("isError"))
    parts = []
    for item in result.get("content") or []:
        if isinstance(item, dict) and item.get("type") == "text":
            parts.append(item.get("text") or "")
    return is_error, "\n".join(parts)


def write_artifacts(out_dir, files):
    os.makedirs(out_dir, exist_ok=True)
    for name, text in files:
        with open(os.path.join(out_dir, name), "w", encoding="utf-8",
                  newline="\n") as fh:
            fh.write(text)


def gh_api(token, path, method="GET", body=None):
    """One REST call.  GET retries twice on transient transport
    failures (truncated reads / connection resets in the NETRED window
    truncated the ~600KB runs listing twice on 20261115, disarming the
    queue governor); POST stays single-shot (non-idempotent)."""
    attempts = 2 if method == "GET" else 1
    last_err = None
    for attempt in range(attempts):
        url = "https://api.github.com" + path
        data = json.dumps(body).encode("utf-8") if body is not None else \
            (b"" if method == "POST" else None)
        req = urllib.request.Request(url, method=method, data=data, headers={
            "Authorization": "Bearer " + token,
            "Accept": "application/vnd.github+json",
            "User-Agent": "rocqwash-triage-watch",
        })
        try:
            with urllib.request.urlopen(req, timeout=60) as resp:
                raw = resp.read()
            return (json.loads(raw) if raw else None), None
        except urllib.error.HTTPError as exc:
            return None, "%d %s" % (exc.code, exc.reason)
        except Exception as exc:
            last_err = exc
            if attempt + 1 < attempts:
                time.sleep(3 + attempt * 5)
    return None, repr(last_err)


def mcp_append(args, tool, points, evidence):
    """One-shot exp_append through a short-lived MCP client session."""
    home = os.environ.get("ROCQWASH_HOME", DEFAULT_HOME)
    python_exe = os.environ.get("ROCQWASH_PYTHON", DEFAULT_PYTHON)
    server = os.environ.get("ROCQWASH_SERVER",
                            os.path.join(home, "tools", "mcp_server.py"))
    if not os.path.isfile(server):
        return "server missing"
    client = McpClient(python_exe, server, home, 300)
    try:
        client.request("initialize", {
            "protocolVersion": "2024-11-05", "capabilities": {},
            "clientInfo": {"name": "rocqwash-watch", "version": "1"},
        }, 1)
        client.notify("notifications/initialized")
        err, text = call_tool(client, "exp_append",
                              {"tool": tool, "points": points,
                               "evidence": evidence, "batch": args.batch}, 2)
        return ("failed: " + text) if err else text.strip()[:120]
    except Exception as exc:
        return "error: %r" % exc
    finally:
        client.close()


class _NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        return None


def download_artifact_file(token, repo, run_id, member, dest):
    """Download the run's gate4-report artifact bundle and extract one file.
    The archive endpoint 302s to a signed blob URL: first hop carries the
    token, second hop must be header-less (same dance as the job-log
    fetch; forwarding the token to blob storage yields 401 Azure)."""
    runs, err = gh_api(token, "/repos/%s/actions/runs/%d/artifacts" % (repo, run_id))
    if err or not runs:
        return "artifact list failed: %s" % err
    import io
    import zipfile
    opener = urllib.request.build_opener(_NoRedirect)
    last_err = "-"
    for art in runs.get("artifacts") or []:
        if art.get("expired"):
            continue
        try:
            req = urllib.request.Request(art["archive_download_url"], headers={
                "Authorization": "Bearer " + token,
                "User-Agent": "rocqwash-triage-watch",
            })
            loc = None
            try:
                with opener.open(req, timeout=120) as resp:
                    blob = resp.read()
            except urllib.error.HTTPError as e302:
                if e302.code in (301, 302, 303, 307):
                    loc = e302.headers.get("Location")
                else:
                    raise
            if loc:
                req2 = urllib.request.Request(loc, headers={
                    "User-Agent": "rocqwash-triage-watch"})
                with urllib.request.urlopen(req2, timeout=180) as r2:
                    blob = r2.read()
            zf = zipfile.ZipFile(io.BytesIO(blob))
            names = [n for n in zf.namelist()
                     if n.endswith(member) or n == member]
            if names:
                with open(dest, "wb") as fh:
                    fh.write(zf.read(names[0]))
                return None
        except Exception as exc:
            last_err = repr(exc)
    return "artifact %s not found (last: %s)" % (member, last_err)


def autofix_leg(args, run_id, repo, head_branch, head_sha):
    """Mechanical comment-surface repair: clone the red head, extract the
    red run's gate4 report, run the closed-loop fixer, push to the
    triggering branch only when the local scan is green.  Budget-capped
    per branch; every outcome lands in the returned detail string."""
    token = os.environ.get("GITHUB_TOKEN", "")
    if not token:
        return "skipped(no-token)", "GITHUB_TOKEN absent"
    state_dir = args.state_dir or args.inbox
    if not state_dir:
        return "skipped(no-state-dir)", "no state dir"
    os.makedirs(state_dir, exist_ok=True)
    state, path = heal_state_load(state_dir)
    key = "fix:%s" % head_branch
    used = int(state.get(key, 0))
    if used >= AUTOFIX_BUDGET_PER_BRANCH:
        return ("skipped(budget)", "autofix budget %d used on %s"
                % (used, head_branch))

    work = os.path.join(args.out, "autofix_tree")
    report_path = os.path.join(args.out, "gate4_report.json")
    err = download_artifact_file(token, repo, run_id,
                                 "gate4_report.json", report_path)
    if err:
        return "skipped(no-report)", err
    g = lambda *a: subprocess.run(["git"] + list(a), capture_output=True,
                                  text=True, encoding="utf-8",
                                  errors="replace", timeout=300)
    r = g("fetch", "--no-tags", "origin", head_sha)
    if r.returncode != 0:
        return "skipped(fetch-failed)", r.stderr[-200:]
    if os.path.isdir(work):
        shutil.rmtree(work, ignore_errors=True)
    r = g("clone", "--quiet", "--no-hardlinks", "--local", os.getcwd(), work)
    if r.returncode != 0:
        return "skipped(clone-failed)", r.stderr[-200:]
    r = g("-C", work, "checkout", "--quiet", "--force", head_sha)
    if r.returncode != 0:
        return "skipped(checkout-failed)", r.stderr[-200:]

    fixer = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                         "gate4_autofix.py")
    fx = subprocess.run([sys.executable, "-I", fixer, "--repo-root", work,
                         "--run-report", report_path, "--max-rounds", "3"],
                        capture_output=True, text=True, encoding="utf-8",
                        errors="replace", timeout=1800)
    detail = (fx.stdout or "")[-1500:] + (fx.stderr or "")[-400:]
    if fx.returncode != 0:
        return "no-green(residue)", detail

    r = g("-C", work, "config", "user.name", "rocqwash-watch")
    r2 = g("-C", work, "config", "user.email",
           "rocqwash-watch@users.noreply.github.com")
    r = g("-C", work, "add", "-A")
    r = g("-C", work, "commit", "-m",
          "ci(gate4-autofix): mechanical comment-surface repair "
          "(date stamps + admission-vocab rewording; desk-approved table)")
    if r.returncode != 0:
        return "skipped(nothing-to-commit)", r.stdout[-200:] + r.stderr[-200:]
    push_url = "https://x-access-token:%s@github.com/%s.git" % (token, repo)
    r = g("-C", work, "push", push_url, "HEAD:refs/heads/%s" % head_branch)
    if r.returncode != 0:
        return "failed(push)", r.stderr[-300:]
    try:
        heal_state_bump(path, state, key)
    except Exception:
        pass
    return "pushed", detail


def git_out(mirror, argv, timeout=120):
    return subprocess.run(
        ["git", "-C", mirror, "-c", "gc.auto=0"] + argv,
        capture_output=True, text=True, timeout=timeout)


def mirror_ff_sync(mirror):
    """Fast-forward the bridge mirror main to origin/main, guarded.

    The 20261114 run #69 checkout red: another seat pushed to the real shore
    and the mirror synced ~3 minutes later - the furnace checkout raced the
    sync window ("not our ref").  Guards: clean tree only, strictly
    fast-forward only, fail-soft verdict string either way.
    """
    if not os.path.isdir(mirror):
        return "no-mirror:" + mirror
    if not os.path.isdir(os.path.join(mirror, ".git")):
        return "not-a-worktree:" + mirror
    st = git_out(mirror, ["status", "--porcelain"])
    if st.returncode != 0:
        return "status-failed"
    if st.stdout.strip():
        return "dirty-tree"
    f = git_out(mirror, ["fetch", "--no-tags", "origin", "main"])
    if f.returncode != 0:
        return "fetch-failed"
    cur = git_out(mirror, ["rev-parse", "refs/heads/main"])
    new = git_out(mirror, ["rev-parse", "refs/remotes/origin/main"])
    if cur.returncode != 0 or new.returncode != 0:
        return "revparse-failed"
    if cur.stdout.strip() == new.stdout.strip():
        return "up-to-date"
    anc = git_out(mirror, ["merge-base", "--is-ancestor",
                           "refs/heads/main", "refs/remotes/origin/main"])
    if anc.returncode != 0:
        return "not-fast-forward"
    m = git_out(mirror, ["merge", "--ff-only", "refs/remotes/origin/main"])
    if m.returncode != 0:
        return "merge-failed"
    return "ff->" + new.stdout.strip()[:7]


def heal_state_load(state_dir):
    path = os.path.join(state_dir, "heal_state.json")
    try:
        with open(path, encoding="utf-8") as fh:
            return json.load(fh), path
    except Exception:
        return {}, path


def heal_state_bump(path, state, run_id):
    state[str(run_id)] = state.get(str(run_id), 0) + 1
    tmp = path + ".tmp"
    with open(tmp, "w", encoding="utf-8", newline="\n") as fh:
        json.dump(state, fh, sort_keys=True)
    os.replace(tmp, path)


def try_heal(args, family, action, run_id, repo):
    """Auto-heal leg: mirror sync + rerun-failed-jobs for rerun-safe reds.

    Best effort and budget-capped; every outcome lands in the returned
    verdict string and the artifacts, so a silent heal is impossible.
    Returns (verdict, detail) - verdict for the summary line, detail for
    the heal-note artifact and the ledger entry.
    """
    if not args.heal:
        return "skipped(disabled)", "heal leg disabled (no --heal)"
    if action not in HEAL_ACTIONS and family not in HEAL_FAMILIES:
        return ("skipped(family-not-healable)",
                "family=%s action=%s not in heal whitelist %s / %s"
                % (family, action, sorted(HEAL_ACTIONS), sorted(HEAL_FAMILIES)))
    token = os.environ.get("GITHUB_TOKEN", "")
    if not token:
        return "skipped(no-token)", "GITHUB_TOKEN absent (local run?)"
    state_dir = args.state_dir or args.inbox
    if not state_dir:
        return "skipped(no-state-dir)", "no state dir for heal budget"
    os.makedirs(state_dir, exist_ok=True)
    state, path = heal_state_load(state_dir)
    used = int(state.get(str(run_id), 0))
    if used >= HEAL_BUDGET_PER_RUN:
        return ("skipped(budget)",
                "heal budget %d already used for run %d"
                % (used, run_id))

    log("heal: stable-window delay %ds before rerun" % args.heal_delay)
    time.sleep(args.heal_delay)

    sync = mirror_ff_sync(args.mirror)
    log("heal: mirror=%s" % sync)
    if sync.startswith(("no-mirror", "not-a-worktree", "status-failed",
                        "dirty-tree", "fetch-failed", "revparse-failed",
                        "not-fast-forward", "merge-failed")):
        return "skipped(mirror-sync:" + sync + ")", "mirror sync failed: " + sync

    # 20261115 desk order: a manually cancelled run must NOT be
    # resurrected.  Re-fetch the run's live state right before the
    # rerun POST; if the desk cancelled it since the failure
    # (conclusion now cancelled / status no longer completed), drop
    # the heal attempt.
    live, lerr = gh_api(token, "/repos/%s/actions/runs/%d" % (repo, run_id))
    if lerr:
        return "skipped(live-check: %s)" % lerr, \
            "heal live-check failed: %s" % lerr
    if (live or {}).get("conclusion") == "cancelled" or \
            (live or {}).get("status") != "completed":
        return ("skipped(intent-cancelled)",
                "run %d live status=%s conclusion=%s - desk intent, "
                "not resurrected" % (run_id, (live or {}).get("status"),
                                     (live or {}).get("conclusion")))
    # 20261115 desk order (fission guard): a failed run whose branch has
    # moved on is superseded - rerunning it grows the run tree for
    # nothing.  Compare against the newest furnace run of the same
    # head_branch; the heal budget (1/run) additionally caps reruns
    # at most once per run.
    hb = (live or {}).get("head_branch") or ""
    hs = (live or {}).get("head_sha") or ""
    if hb and hs:
        newest, nerr = gh_api(
            token,
            "/repos/%s/actions/workflows/%s/runs?head_branch=%s"
            "&per_page=1" % (repo, FURNACE_WORKFLOW_FILE, hb))
        nb = (newest or {}).get("workflow_runs") or []
        if not nerr and nb and (nb[0] or {}).get("head_sha") \
                and nb[0]["head_sha"] != hs:
            new_sha = nb[0]["head_sha"]
            # 20261115 desk follow-up: "branch moved" alone does NOT
            # mean covered - only a descendant head contains the old
            # content.  Compare API discriminates: ahead/identical =
            # covered (true superseded, skip); behind/diverged/errors
            # = coverage NOT proven (force-push, rebase with drops,
            # revert chains) - the rerun PROCEEDS, bounded by the
            # 1/run heal budget and the live-cancel check above
            # (at-most-once per run).
            cmpv, cerr = gh_api(token,
                                "/repos/%s/compare/%s...%s"
                                % (repo, hs, new_sha))
            vstat = (cmpv or {}).get("status") or ""
            if vstat in ("ahead", "identical"):
                return ("skipped(superseded-covered)",
                        "run %d head %s is ancestor-covered by %s on %s "
                        "(compare=%s) - not rerun (fission guard)"
                        % (run_id, hs[:7], new_sha[:7], hb, vstat))
            log("heal: head %s not provably covered by %s on %s "
                "(compare=%s%s) - rerun proceeds (budget-capped)"
                % (hs[:7], new_sha[:7], hb, vstat or "err",
                   (": " + cerr) if cerr else ""))
    url = ("https://api.github.com/repos/%s/actions/runs/%d/rerun-failed-jobs"
           % (repo, run_id))
    req = urllib.request.Request(url, method="POST", data=b"", headers={
        "Authorization": "Bearer " + token,
        "Accept": "application/vnd.github+json",
        "User-Agent": "rocqwash-triage-watch",
    })
    try:
        with urllib.request.urlopen(req, timeout=60) as resp:
            code = resp.status
    except urllib.error.HTTPError as exc:
        code = exc.code
        detail = "heal rerun HTTP %d: %s" % (code, exc.reason)
        return "refused(http-%d)" % code, detail
    except Exception as exc:
        return "failed(exception)", "heal rerun error: %r" % exc

    try:
        heal_state_bump(path, state, run_id)
    except Exception as exc:
        log("heal: state bump failed: %r" % exc)
    detail = ("heal rerun dispatched: HTTP %d, mirror=%s, budget now %d/%d "
              "for run %d" % (code, sync,
                              used + 1, HEAL_BUDGET_PER_RUN, run_id))
    return "dispatched(http-%d)" % code, detail


def reconcile_leg(args, repo):
    """Scheduled pass over recent furnace runs.  Cancelled runs are
    recorded as intent (desk manual cancel or infra cancel) and NOT
    revived - revival is opt-in only via --reconcile-revive (desk-run
    emergency lever; 20261115 order: manual cancels stay dead).  The
    pass is read-only unless that flag is set."""
    token = os.environ.get("GITHUB_TOKEN", "")
    if not token:
        return ["skipped(no-token)"]
    state_dir = args.state_dir or args.inbox
    if not state_dir:
        return ["skipped(no-state-dir)"]
    os.makedirs(state_dir, exist_ok=True)
    state, path = heal_state_load(state_dir)
    runs, err = gh_api(token, "/repos/%s/actions/workflows/%s/runs"
                       "?per_page=40" % (repo, FURNACE_WORKFLOW_FILE))
    if err or not runs:
        return ["skipped(runs-list: %s)" % err]
    recent = []
    queued = []
    busy = False
    now = datetime.datetime.now(datetime.timezone.utc)
    for r in runs.get("workflow_runs") or []:
        created = r.get("created_at", "").replace("Z", "+00:00")
        age_h = None
        try:
            age_h = (now - datetime.datetime.fromisoformat(created)
                     ).total_seconds() / 3600.0
        except ValueError:
            continue
        if r.get("status") in ("in_progress", "queued"):
            busy = True
        if r.get("status") == "queued":
            queued.append((r["id"], r["run_number"]))
        if (r.get("conclusion") == "cancelled" and age_h is not None
                and age_h <= RECONCILE_WINDOW_H):
            recent.append((r["id"], r["run_number"], age_h))
    queued.reverse()  # oldest first (the runs listing is newest-first)
    out = []
    # 20261115 desk order (queue governor): the pending queue must be
    # bounded - unbounded queued runs pile up when pushes outpace the
    # furnace.  Keep at most MAX_QUEUED_FURNACE_RUNS queued runs (newest
    # win); cancel the oldest overflow.  In-progress runs are never
    # touched; the trimmed ones stay dead under the intent rule.
    if len(queued) > MAX_QUEUED_FURNACE_RUNS:
        overflow = queued[:len(queued) - MAX_QUEUED_FURNACE_RUNS]
        for gid, gnum in overflow:
            _, cerr = gh_api(token, "/repos/%s/actions/runs/%d/cancel"
                             % (repo, gid), method="POST")
            if cerr:
                out.append("#%d queue-trim cancel failed: %s"
                           % (gnum, cerr))
                continue
            out.append("#%d queue-trimmed (queued beyond cap %d)"
                       % (gnum, MAX_QUEUED_FURNACE_RUNS))
            mcp_append(args, "watch-queue-governor",
                       "queued furnace run #%d cancelled - queue depth %d "
                       "over cap %d (oldest-first trim)"
                       % (gnum, len(queued), MAX_QUEUED_FURNACE_RUNS),
                       "https://github.com/%s/actions/runs/%d"
                       % (repo, gid))
    if busy:
        if not out:
            return ["skipped(furnace-busy)"]
        return out
    for run_id, num, age_h in sorted(recent, key=lambda x: -x[2])[
            :RECONCILE_MAX_PER_PASS]:
        # 20261115 desk order: manually cancelled runs are intent - the
        # watch must NOT auto-revive them.  With cancel-in-progress=false
        # on both furnaces (8c527f1) concurrency cancels no longer occur,
        # so revival is opt-in only via --reconcile-revive.
        if not args.reconcile_revive:
            out.append("skip #%d (cancelled=intent; not revived - manual "
                       "rerun only, age %.1fh)" % (num, age_h))
            continue
        key = "reconcile:%d" % run_id
        if int(state.get(key, 0)) >= 1:
            out.append("skip #%d (already reconciled)" % num)
            continue
        _, err = gh_api(token, "/repos/%s/actions/runs/%d/rerun" % (repo, run_id),
                        method="POST")
        if err:
            out.append("#%d revive failed: %s" % (num, err))
            continue
        try:
            heal_state_bump(path, state, key)  # keyed cap: at-most-once per run
        except Exception:
            pass
        out.append("#%d revived (age %.1fh)" % (num, age_h))
        mcp_append(args, "watch-reconcile",
                   "cancelled furnace run #%d revived for backlog recovery "
                   "(age %.1fh, window %dh)" % (num, age_h, RECONCILE_WINDOW_H),
                   "https://github.com/%s/actions/runs/%d" % (repo, run_id))
    if not out:
        out = ["clean (no recent cancelled runs in window)"]
    return out


def main():
    ap = argparse.ArgumentParser(description="rocqwash MCP triage driver")
    ap.add_argument("--repo", required=True, help="ORG/REPO slug")
    ap.add_argument("--run", required=True, type=int, help="CI run id")
    ap.add_argument("--out", required=True, help="artifact output directory")
    ap.add_argument("--inbox", default=None,
                    help="optional desk inbox directory to mirror artifacts into")
    ap.add_argument("--batch", default="main-ci93-watch",
                    help="experience ledger batch label")
    ap.add_argument("--heal", action="store_true",
                    help="enable the auto-heal leg (mirror sync + rerun for "
                         "rerun-safe families)")
    ap.add_argument("--heal-delay", type=int, default=90,
                    help="stable-window seconds to wait before a heal rerun")
    ap.add_argument("--mirror", default=DEFAULT_MIRROR,
                    help="bridge mirror worktree path for the heal sync")
    ap.add_argument("--state-dir", default=None,
                    help="heal budget state dir (defaults to the inbox dir)")
    ap.add_argument("--timeout", type=int, default=900,
                    help="whole MCP conversation deadline in seconds")
    ap.add_argument("--reconcile", action="store_true",
                    help="reconcile mode: record recent cancelled furnace "
                         "runs (intent; not revived - scheduled pass; "
                         "triage skipped)")
    ap.add_argument("--reconcile-revive", action="store_true",
                    help="emergency lever with --reconcile: actually rerun "
                         "cancelled runs (default off: cancelled = intent)")
    ap.add_argument("--autofix", action="store_true",
                    help="enable the autofix leg (mechanical comment-surface "
                         "repair pushed to the triggering branch)")
    ap.add_argument("--head-branch", default=None,
                    help="branch of the triggering run (for the autofix push)")
    ap.add_argument("--head-sha", default=None,
                    help="head sha of the triggering run (for the autofix tree)")
    args = ap.parse_args()

    if args.reconcile:
        lines = reconcile_leg(args, args.repo)
        report = "reconcile pass:\n" + "\n".join(lines) + "\n"
        write_artifacts(args.out, [("reconcile-report.txt", report)])
        if args.inbox:
            write_artifacts(args.inbox, [("reconcile-report.txt", report)])
        print(report)
        return 0

    home = os.environ.get("ROCQWASH_HOME", DEFAULT_HOME)
    python_exe = os.environ.get("ROCQWASH_PYTHON", DEFAULT_PYTHON)
    server = os.environ.get("ROCQWASH_SERVER",
                            os.path.join(home, "tools", "mcp_server.py"))
    if not os.path.isfile(server):
        sys.stderr.write("server script missing: %s\n" % server)
        return 2

    client = McpClient(python_exe, server, home, args.timeout)
    try:
        client.request("initialize", {
            "protocolVersion": "2024-11-05",
            "capabilities": {},
            "clientInfo": {"name": "rocqwash-triage-watch", "version": "1"},
        }, INIT_RESULT_ID)
        client.notify("notifications/initialized")

        err, report = call_tool(client, "ci_triage",
                                {"repo": args.repo, "run": args.run},
                                TRIAGE_RESULT_ID)
        if err:
            write_artifacts(args.out, [
                ("triage-report.txt", report or "(empty failed result)"),
                ("triage-summary.txt",
                 "verdict=TOOL-FAILED run=%d repo=%s" % (args.run, args.repo)),
                ("server-stderr.log", client.stderr_text()),
            ])
            sys.stderr.write("ci_triage returned a failed result:\n%s\n"
                             % (report or "(no text)"))
            return 3

        m = VERDICT_RE.search(report)
        family, action = (m.group(1), m.group(2)) if m else ("unknown", "unknown")

        try:
            heal_verdict, heal_detail = try_heal(args, family, action,
                                                 args.run, args.repo)
        except Exception as exc:  # heal must never mask the triage verdict
            heal_verdict, heal_detail = "failed(exception)", repr(exc)
        log("heal: %s" % heal_verdict)

        autofix_verdict, autofix_detail = "skipped(disabled)", "no --autofix"
        if args.autofix:
            if not (args.head_branch and args.head_sha):
                token = os.environ.get("GITHUB_TOKEN", "")
                info, err = gh_api(token, "/repos/%s/actions/runs/%d"
                                   % (args.repo, args.run)) if token else \
                    (None, "no-token")
                if info and not err:
                    args.head_branch = args.head_branch or info.get(
                        "head_branch")
                    args.head_sha = args.head_sha or info.get("head_sha")
            if args.head_branch and args.head_sha:
                try:
                    autofix_verdict, autofix_detail = autofix_leg(
                        args, args.run, args.repo, args.head_branch,
                        args.head_sha)
                except Exception as exc:  # never mask the triage verdict
                    autofix_verdict, autofix_detail = \
                        "failed(exception)", repr(exc)
            else:
                autofix_verdict, autofix_detail = \
                    "skipped(no-head)", err or "head unknown"
        log("autofix: %s" % autofix_verdict)

        points = ("Main CI 9.3 red run %d: family=%s action=%s (auto triage "
                  "by rocqwash-triage workflow)" % (args.run, family, action))
        evidence = "https://github.com/%s/actions/runs/%d" % (args.repo, args.run)
        lerr, ledger = call_tool(client, "exp_append",
                                 {"tool": "ci_triage", "points": points,
                                  "evidence": evidence, "batch": args.batch},
                                 LEDGER_RESULT_ID)
        if heal_verdict.startswith(("dispatched", "refused", "failed")):
            herr, hledger = call_tool(
                client, "exp_append",
                {"tool": "watch-heal",
                 "points": "run %d heal=%s: %s" % (args.run, heal_verdict,
                                                   heal_detail),
                 "evidence": evidence, "batch": args.batch},
                HEAL_LEDGER_RESULT_ID)
        else:
            herr, hledger = False, "heal not attempted: " + heal_verdict
    finally:
        client.close()

    files = [
        ("triage-report.txt", report),
        ("ledger-entry.txt",
         ("failed result:\n%s" % ledger) if lerr else ledger),
        ("heal-note.txt", heal_verdict + "\n" + heal_detail + "\n"
         + (("failed result:\n%s" % hledger) if herr else hledger)),
        ("autofix-note.txt", autofix_verdict + "\n" + autofix_detail),
        ("triage-summary.txt",
         "verdict=OBTAINED run=%d repo=%s family=%s action=%s heal=%s "
         "autofix=%s" % (args.run, args.repo, family, action, heal_verdict,
                         autofix_verdict)),
        ("server-stderr.log", client.stderr_text()),
    ]
    write_artifacts(args.out, files)

    if args.inbox:
        inbox_run = os.path.join(args.inbox, "run%d" % args.run)
        write_artifacts(inbox_run, files)

    log("run=%d family=%s action=%s heal=%s autofix=%s artifacts=%s%s"
        % (args.run, family, action, heal_verdict, autofix_verdict,
           args.out, (" inbox=%s" % args.inbox) if args.inbox else ""))
    return 0


if __name__ == "__main__":
    sys.exit(main())
