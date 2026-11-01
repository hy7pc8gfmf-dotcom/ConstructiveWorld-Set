(* ===== ForwardKLAdjudication.v =====
   Mission. Record the adjudication for the three entries left in the head of
   UpReqForwardKLFamily.v (forward beta-weighted one-step iteration identity /
   forward multi-step iteration contraction chain / unconditional forward
   triangle upper bound): per account the four-element verdict record (slot
   coordinates / original narrative / structural root cause of the
   non-realizability / replacement true-form citations), plus the assembled
   citation triple of the honest in-library forward-KL forms and the closing
   adjudication registration.
   Form. Pure adjudication-record module: zero Require, zero new theorems, zero
   declarations (the verdict-record class authorization allows a verdict piece
   to carry zero new theorems); nothing is declared, so the statement face is
   empty and Set-layer by absence; every citation face was re-checked against
   the tree source to guard against phantom citations.
   Dependencies. None. No library Require of any kind; the Rocq prelude
   suffices.
   References. Fulfillment-record section form of EntropyUnsatMark.v (fa52
   precedent). Citation targets read from the tree source:
   UpReqForwardKLFamily.v / UpReqWeakTriangle.v / S05_AlignmentGRPO.v /
   S08_RealMainlineDPO.v / UpRealLeB.v / WeakTriangleClose.v (candidate
   closure piece, registered pending its gate, closing part).
   Constructivity. Zero Require and zero declarations give an axiom-free
   surface by construction. The three accounts are narrative downgrades, not
   proof debts: the provable faces are closed by the additive chain identities
   plus the conditional weak triangle; only the unconditional strong narratives
   are unsatisfiable under the constructive Set-layer discipline.
   Build. rocq c -native-compiler no -q -Q . "" ForwardKLAdjudication.v (Rocq
   9.1 toolchain; single -Q root, empty logical prefix). Body = comments only
   plus one empty built-in Section/End carrier pair; no environment entries.
   ===== *)

Section ForwardKLAdjudicationVerdicts.

(* ================= Part 1. The recorded entries verbatim: per-account
   four-element adjudication for the three accounts ================= *)

(* ---- Account 1 (forward beta-weighted one-step iteration identity) ----
   Element 1, slot coordinates: UpReqForwardKLFamily.v:29 (head-note dual-table
     entry 1, the recorded-verdict line); the recorded-narrative source is
     S05_AlignmentGRPO.v:3865 policy_iter_backward_kl_step_beta (the exact
     identity of the three beta-weighted KLs, first of the five backward
     baseline pieces).
   Element 2, original narrative: apply the direction flip from KL(p||q) to
     KL(q||p) to the beta-weighted three-KL one-step identity, to obtain a
     forward policy-improvement step identity (strong-duality narrative: flip
     and it follows).
   Element 3, structural root cause: forward iteration has no kappa^t
     contraction; after the flip the (1 - eta) linear contraction factor
     becomes a nonlinear factor, and the library has no matching identity
     engine (the original recorded verdict at lines 28-29); the geometric-rate
     territory UpReqIterGeomRate is a declared no-touch piece (engine-chain
     declaration at lines 63-64), so this is not a construction gap.
   Element 4, replacement true-form citations: the same module's finished
     fkl_pt_split_flip (UpReqForwardKLFamily.v:141, the direction-flip
     isomorphic honest form, with nontriviality grade [low] honestly labeled)
     covers the entire provable identity face of that direction; the
     beta-weighted one-step narrative stays in the backward-baseline original
     (S05_AlignmentGRPO.v:3865) and is not overturned.
     Verdict: the strong-duality flip narrative is downgraded to an
     isomorphic-identity narrative; this is a narrative downgrade, not a proof
     debt. *)

(* ---- Account 2 (forward multi-step iteration contraction chain) ----
   Element 1, slot coordinates: UpReqForwardKLFamily.v:37 (head-note dual-table
     entry 4, the recorded-verdict line); the recorded-narrative source is
     S05_AlignmentGRPO.v:4205 policy_iter_backward_kl_iter_le (the iteration
     contraction chain, the <= form).
   Element 2, original narrative: a forward multi-step iteration contraction
     chain, with the kappa^t geometric decay rate tightened bound by bound.
   Element 3, structural root cause: as in Account 1, forward iteration has no
     kappa^t contraction (the original recorded verdict at line 37, "same as
     Account 1"); the in-library forward chain identity is additive (the
     residual is explicit step by step), with no multiplicative contraction
     factor to accumulate; the territory is in progress and must not be touched
     (original note).
   Element 4, replacement true-form citations: fkl_path_split_pt
     (UpReqForwardKLFamily.v:228) and fkl_path_split_sum (line 258) give the
     exact additive identities for each step and for the whole chain
     (sum KL(f||h) == sum KL(f||g) + sum f*(log g - log h)); the multi-step
     aggregated upper-bound narrative is carried by the conditional weak
     triangle wtl_cond_triangle (Part 2, piece 1).
     Verdict: the geometric-rate narrative is downgraded to an additive chain
     identity plus conditional upper-bound narrative; the provable face is
     closed. *)

(* ---- Account 3 (unconditional forward triangle upper bound) ----
   Element 1, slot coordinates: UpReqForwardKLFamily.v:45 (head-note appended
     entry, the forward triangle upper bound, lines 44-46; the original
     recorded verdict "theoremization = recorded entry (obstacle account)").
     Correction-history source: UpReqWeakTriangle.v lines 10-18, the direction
     declaration section (spec item c of EXP-D3B: the conclusion proved for a
     false proposition, and the true-form correction).
   Element 2, original narrative: the unconditional forward triangle
     inequality KL(p,r) <=_B f(KL(p,q), KL(q,r)) (uncertificated strong
     triangle narrative).
   Element 3, structural root cause: no upper-bound engine for the residual.
     The reverse Pinsker does not exist (original recorded verdict at lines
     44-45), and the third limb of the chain identity, E_p[log q - log r], has
     no fixed sign (same-source recorded verdict at line 34), so the
     unconditional <= form does not close. Empirical face: the EXP-D3 analytic
     counterexample Q=(1/2,1/2), R=(9/10,1/10), P=(0,1) gives RHS - LHS =
     ln(3/5) < 0 (recorded at UpReqWeakTriangle.v lines 12-14; near-degenerate
     violations 77/3000).
   Element 4, replacement true-form citations: wtl_cond_triangle
     (UpReqWeakTriangle.v:158, assumption-inventory entry #279, already in the
     library): the conditional weak triangle true form KL(p||r) <=_B
     sum KL(p||q) + sum KL(q||r) + log(1/c), with certificate c*q_s <=_real
     r_s; the corrected version stress-tested 0/20000 (recorded at lines
     17-18).
     Verdict: the uncertificated strong-triangle narrative is downgraded to
     the certificate-conditioned narrative; the provable face is fully closed,
     not a proof debt. *)

(* ================= Part 2. Replacement-narrative assembly: the honest
   in-library forward-KL form triple (citation re-check record) ================= *)
(* The triple = the conditional triangle upper bound + the KL non-negativity
   eps/B engines + the residual-explicit identity exit; together they form the
   full spectrum of the honest form of the forward KL in this library. Each
   citation was re-checked by grep/sed (against phantom citations).
   Piece 1, the weak-triangle true form: UpReqWeakTriangle.v ::
   wtl_cond_triangle (Theorem declaration read at line 158; the wtl_family
   sigT closure at line 525; the Q-layer certificate trio wtl_qdiv_pos:81 /
   wtl_min_ratio_lb:96 / wtl_min_ratio_pos:116; registered at line 279 of the
   assumption-inventory addendum).
   Piece 2, the Real-layer eps form: S08_RealMainlineDPO.v:501
   real_gibbs_inequality_eps (0 <= sum_s kl(p s||q s) + eps, the real_le
   form; the declaration at line 501 sed-read). The Bishop wrapper:
   UpRealLeB.v:600 real_gibbs_inequality_B (line 612 cites the eps piece
   directly inside, sed-read); cross-corroborated with the triage record #29
   proven conclusion that only the eps/B forms are reachable at the Real
   layer.
   Piece 3, the residual-explicit identity form: UpReqForwardKLFamily.v:228
   fkl_path_split_pt / line 258 fkl_path_split_sum (KL(p||r) == KL(p||q) +
   E_p[log q - log r]; the residual is explicit, not hidden; the source
   module close-read in full; the four-check face rests on its delivered vo
   state). *)

(* Account 1 verdict: the forward beta-weighted one-step identity is a
   narrative downgrade, not a proof debt; the provable face of the flipped
   direction is already covered by the fkl_pt_split_flip isomorphic honest
   form, and the geometric-rate narrative is registered in its permanent slot
   and never scheduled.
   Account 2 verdict: the forward iteration contraction chain is a narrative
   downgrade, not a proof debt; the additive chain identities
   (fkl_path_split_pt / fkl_path_split_sum) plus the conditional weak triangle
   (wtl_cond_triangle) cover the aggregated upper-bound provable face, and the
   kappa^t geometric-rate narrative is registered in its permanent slot and
   never scheduled.
   Account 3 verdict: the unconditional forward triangle upper bound is a
   narrative downgrade, not a proof debt; the certificate-conditioned true
   form (wtl_cond_triangle, entry #279) covers the triangle upper-bound
   provable face, and the uncertificated strong-triangle narrative is
   registered in its permanent slot and never scheduled.
   Overall judgment: the root causes of all three accounts are engine-level
   (no kappa^t contraction engine; no reverse Pinsker and no residual
   upper-bound engine), not construction-level. The honest in-library form
   triple already covers their entire provable face; what the three accounts
   lack is not "proof" but "unconditional strong narrative", and that
   narrative is unsatisfiable under this library's constructive Set-layer
   discipline.
   Lineage note: same lineage and same verdict as the G07 KL wall family (the
   unconditional layer unreachable, the eps/conditioned layer reachable);
   zero overturning. *)

(* ================= Part 4. Forward-merge slot, pending-gate registration
   (fka_weak_triangle_ref) ================= *)
(*
   (1) Landed on disk: WeakTriangleClose.v (the closure piece, 391 lines) is
   complete in form: main piece wtc_weak_triangle_load / the sigT closure
   wtc_family / the four-element re-check head note / the end-of-file Print
   Assumptions audit slot. Note: its content is the weak-triangle territory's
   G3 CS weight-transfer limb closure (the binary Gram kernel
   (sum a*b)^2 <= sum a^2 * sum b^2), NOT the KL weak-triangle true form
   itself (the true form = Part 2 piece 1, wtl_cond_triangle); when merging,
   the citation roles must be divided honestly.
   (2) Require-able: NO. Both local trust roots measured unavailable: at the
   local vo root and at the vorebuild_901 rebuild base alike, S01_BaseRing.vo
   and UpReqWeakTriangle.vo both report inconsistent assumptions (magic
   number mismatch), and fa53_compat_abs.vo is missing from both roots.
   (3) Disposition: per the forward-introduction precedent discipline (the
   cited main piece must pass its gate before introduction), this piece
   installs no forwarding theorem; fka_weak_triangle_ref is registered
   pending its gate, with the install form fixed as follows (one hop once the
   gate opens):
       Require Import S01_BaseRing. Require Import fa53_compat_abs.
       Require Import WeakTriangleClose.
       Theorem fka_weak_triangle_ref : forall RI DO a b c d : R (statement
         face verbatim per wtc_weak_triangle_load). Proof.
         exact wtc_weak_triangle_load. Qed.
   (The fka_ prefix has zero same-name conflicts library-wide: three-tree
   grep measured zero hits: ConstructiveWorld_Live / the ablation tree /
   Live/vorebuild_901.)
   Red-line self-audit: zero Require, zero new theorems, zero declarations
   (a pure adjudication-registration face).
   The origin tree is read-only (ConstructiveWorld_Live is read-only); this
   piece writes only to its own seat workspace. *)

End ForwardKLAdjudicationVerdicts.
