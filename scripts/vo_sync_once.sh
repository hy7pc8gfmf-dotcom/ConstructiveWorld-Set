#!/bin/bash
# vo_sync_once.sh — 跨机 vo 信任缓存一次性同步（CI 起步步形态；亦可手动单发）
#
# 使命（四基准④ CI 内联化）：本侧认证 job 起步先查对侧最近绿 run 的 vo-trust-cache
# artifact——有新则下载并镜像合并进本侧缓存目录，使对侧新增模块在本轮 build 即可
# SKIP（缺者由 parallel_build 编译·变者由 PBLD_CHANGED_SINCE 代差失效重编）——
# 「一侧新增模块推送 CI、对侧自动本地化+认证」闭环的内联半环；常驻半环由
# vo_sync_watch.ps1/.sh 承担。
#
# fail-open 契约：网络窗抖动/artifact 缺席/解压失败一律 WARN 后 exit 0——同步是
# 增强件，认证主链不依赖它（缺件必被 build 补编，正确性不受影响）。禁把本步做成红闸。
#
# 环境变量：
#   SYNC_ARTIFACT   对侧 artifact 名（vo-trust-cache-windows | vo-trust-cache-macos）
#   SYNC_CACHE_DIR  本侧缓存目录（Windows seed 源=/d/ComplexAnalysis/ConstructiveWorld-Main/ConstructiveWorld_vo
#                   mac=/Users/apple/vo_ci_cache_mac）
#   SYNC_STATE_FILE 已同步 run 记录（默认 $SYNC_CACHE_DIR/.vo_sync_last_run）
#   REPO / GITHUB_TOKEN（缺 token 时 git credential fill 兜底）
set -u
REPO="${REPO:-hy7pc8gfmf-dotcom/ConstructiveWorld-Main}"
ARTIFACT="${SYNC_ARTIFACT:?SYNC_ARTIFACT required}"
CACHE_DIR="${SYNC_CACHE_DIR:?SYNC_CACHE_DIR required}"
STATE="${SYNC_STATE_FILE:-$CACHE_DIR/.vo_sync_last_run}"
mkdir -p "$CACHE_DIR" 2>/dev/null || { echo "VO_SYNC_ONCE: cache dir not creatable - fail-open exit 0"; exit 0; }
PY="${PYTHON:-python3}"; command -v "$PY" >/dev/null 2>&1 || { PY=python; command -v "$PY" >/dev/null 2>&1 || PY=py; }
command -v "$PY" >/dev/null 2>&1 || PY=""

TOKEN="${GITHUB_TOKEN:-}"
if [ -z "$TOKEN" ]; then
  TOKEN=$(printf "protocol=https\nhost=github.com\n" | git credential fill 2>/dev/null | grep '^password=' | cut -d= -f2)
fi
AUTH=""; [ -n "$TOKEN" ] && AUTH="Authorization: token $TOKEN"

RUN=$(curl -s -m 20 ${AUTH:+-H "$AUTH"} \
  "https://api.github.com/repos/$REPO/actions/runs?branch=main&status=success&per_page=1" \
  | ${PY:+"$PY"} -c "import json,sys
try: print(json.load(sys.stdin)['workflow_runs'][0]['id'])
except Exception: print(0)" 2>/dev/null || echo 0)
LAST=0; [ -f "$STATE" ] && LAST=$(cat "$STATE" 2>/dev/null || echo 0)
case "${RUN:-0}" in ''|*[!0-9]*) RUN=0 ;; esac
if [ "${RUN:-0}" -le "${LAST:-0}" ]; then
  echo "VO_SYNC_ONCE: no fresh green run ($RUN <= $LAST) - skip"
  exit 0
fi

AID=$(curl -s -m 20 ${AUTH:+-H "$AUTH"} \
  "https://api.github.com/repos/$REPO/actions/runs/$RUN/artifacts?per_page=100" \
  | ${PY:+"$PY"} -c "import json,sys
try:
    print(next(a['id'] for a in json.load(sys.stdin).get('artifacts', []) if a['name'] == '$ARTIFACT'))
except Exception:
    print(0)" 2>/dev/null || echo 0)
case "${AID:-0}" in ''|*[!0-9]*) AID=0 ;; esac
if [ "${AID:-0}" -eq 0 ]; then
  echo "VO_SYNC_ONCE: run $RUN has no $ARTIFACT (peer not green or not uploaded) - mark-seen (fail-open)"
  echo "$RUN" > "$STATE" 2>/dev/null || true
  exit 0
fi

TMP=$(mktemp -d)
if [ -z "$TOKEN" ]; then
  echo "VO_SYNC_ONCE: no token, artifact download skipped - fail-open (observe mode, state not written)"
  rm -rf "$TMP"; exit 0
fi
if curl -sL -m 600 -H "Authorization: token $TOKEN" \
     "https://api.github.com/repos/$REPO/actions/artifacts/$AID/zip" -o "$TMP/vo.zip" \
   && [ -s "$TMP/vo.zip" ] \
   && unzip -qo "$TMP/vo.zip" -d "$TMP/vo" 2>/dev/null; then
  N=$(find "$TMP/vo" -name '*.vo' | wc -l)
  find "$CACHE_DIR" -maxdepth 1 -name '*.vo' -delete 2>/dev/null
  find "$TMP/vo" -name '*.vo' -exec cp {} "$CACHE_DIR"/ \; 2>/dev/null
  echo "VO_SYNC_ONCE: run $RUN synced $N .vo -> $CACHE_DIR"
  echo "$RUN" > "$STATE" 2>/dev/null || true
else
  echo "VO_SYNC_ONCE: download or extract failed - fail-open (retry next round)"
fi
rm -rf "$TMP"
exit 0
