(* ===================================================================== *)
(*  abl_audit_base_v6.v - audit-carrier expansion v6: direct audit of the  *)
(*  audit engine's own reliability surface (five-carrier closure file).    *)
(*  Mission. Five true-use carriers for five main theorems of the S13      *)
(*  audit-engine reliability surface; use = the proof body genuinely       *)
(*  exercises the upstream theorem (non-vacuous):                          *)
(*  (1) abf_early_stop_fuel_and_run - early_stop_confidence (stop flag OR  *)
(*  fuel-ledger disjunction) at threshold 1, 5 steps, acc [[0]], conjoined *)
(*  with the zero-step sampling computation face (result constant [[0]]);  *)
(*  (2) abf_early_stop_all_pass_concrete - early_stop_confidence' (a stop  *)
(*  is a unanimous pass) at candidates [[0]], threshold 1;                *)
(*  (3) abf_top_p_cumulative_concrete - top_p_cumulative_ge (mass bound of *)
(*  the truncated prefix) at p=1, sorted [0;1], uniform weights;           *)
(*  (4) abf_q_branch_weight_conserved - q_branch_weight general form plus  *)
(*  seed-ray instance (weight 4 = 2+2 over two sub-rays);                  *)
(*  (5) abf_resample_fallback - resample_terminates (audit pass OR safe    *)
(*  fallback sequence) at fallback [0], plus its computation face.         *)
(*  Dependencies. S01_BaseRing S02_CauchyComplete S12_B5RecycleSF          *)
(*  S13_NLiveAudit (plain module LCAudit imported explicitly; QId and      *)
(*  qid_intro arrive via S12); Stdlib QArith.QArith QArith.Qabs            *)
(*  Lists.List Arith.Arith; Extraction exit bay at file end.               *)
(*  References. abl_audit_base_v5, same-family in-tree precedent shape.    *)
(*  Constructivity. Conjunctions S01.And, disjunctions S01.Or, equalities  *)
(*  S01.Id / QId, comparisons QleT': all Set level; no Prop-valued         *)
(*  statements, no classical logic. The Qle premise slot of                *)
(*  top_p_cumulative_ge is fed via Qle_bool reflection (in-tree form).     *)
(*  Build. source toolchain env; unset COQLIB ROCQLIB; ulimit -s 65532;    *)
(*  rocq c -native-compiler no -q -Q <world-dir> "" abl_audit_base_v6.v    *)
(*  (single -Q pool; world supplied by the Live tree generation).          *)
(* ===================================================================== *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
From Stdlib Require Import QArith.QArith QArith.Qabs
               Lists.List Arith.Arith.
Import ListNotations.
Local Open Scope Q_scope.
Import S13_NLiveAudit.LCAudit.

(* ============================================================ *)
(* Sec.0 Internal fittings bay (constant generators and concrete *)
(* objects; not carrier statements)                              *)
(* ============================================================ *)

(* Constant drawer: emits the same sequence [t] on every call and returns  *)
(* the seed stream unchanged (PRNG-stream-independent face).               *)
Definition abf_const_draw (t : nat) : PRNG -> Sequence * PRNG :=
  fun p => (t :: nil, p).

(* Uniform weights: every token has weight 1 (used by the top-p concrete   *)
(* instance).                                                              *)
Definition abf_uniform_w (t : nat) : Q := 1%Q.

(* Seed ray: position origin, tangent (1,0), weight 4, no history bits,    *)
(* zero accumulated deflection.                                            *)
Definition abf_seed_ray : QRay :=
  Build_QRay 0 0 1 0 4 nil 0.

(* ============================================================ *)
(* Sec.1 Carrier 1 - sequential confidence stopping (A): fuel-ledger *)
(* main theorem concrete instance + early-stop computation face      *)
(* (Set-level Id wings x2, And-conjoined, double use)                *)
(* ============================================================ *)

Theorem abf_early_stop_fuel_and_run :
  forall prng0 : PRNG,
    And (Id (orb (stop_condition 1
                   (fst (sample_until_confident 1 5%nat ((0%nat :: nil) :: nil)
                          (abf_const_draw 0) prng0)))
                (Nat.eqb (length (fst (sample_until_confident 1 5%nat
                              ((0%nat :: nil) :: nil) (abf_const_draw 0) prng0)))
                         (length ((0%nat :: nil) :: nil) + 5)%nat))
           true)
        (Id (fst (sample_until_confident 1 5%nat ((0%nat :: nil) :: nil)
                   (abf_const_draw 0) prng0))
            ((0%nat :: nil) :: nil)).
Proof.
  intros prng0. split.
  - (* Fuel-ledger wing: main theorem instantiated at threshold:=1,        *)
    (* max_iter:=5, acc:=[[0]] (true use - the let envelope closes up to    *)
    (* conversion).                                                         *)
    exact (early_stop_confidence 1 5%nat ((0%nat :: nil) :: nil)
             (abf_const_draw 0) prng0).
  - (* Early-stop computation face: the sole candidate [0] has self-coherence *)
    (* 1 >= 1, the stop condition computes to true, sampling takes zero steps, *)
    (* and the result is constantly [[0]] regardless of the seed stream        *)
    (* (id_refl, definitional).                                                *)
    exact id_refl.
Qed.

(* ============================================================ *)
(* Sec.2 Carrier 2 - sequential confidence stopping (B): early-stop  *)
(* pass main theorem concrete instance - a stop is a unanimous pass  *)
(* (conclusion QleT', Set-level comparison face)                     *)
(* ============================================================ *)

Theorem abf_early_stop_all_pass_concrete :
  forall prng0 : PRNG,
    And (Id (stop_condition 1 ((0%nat :: nil) :: nil)) true)
        (QleT' 1 (self_consistency_score (0%nat :: nil) ((0%nat :: nil) :: nil))).
Proof.
  intros prng0. split.
  - (* Stop condition computed: forallb sees every candidate pass the       *)
    (* Qle_bool 1 1 = true test.                                            *)
    exact id_refl.
  - (* Pass face: early-stop pass main theorem instantiated at max_iter:=0;  *)
    (* the stop slot is fed the first wing, the membership slot receives the *)
    (* reduced zero-step sampling shape and then the head witness (true use).*)
    apply (early_stop_confidence' 1 0%nat ((0%nat :: nil) :: nil)
             (abf_const_draw 0) prng0 id_refl (0%nat :: nil)).
    cbn [sample_until_confident fst]. apply InT_here.
Qed.

(* ============================================================ *)
(* Sec.3 Carrier 3 - top-p truncation: cumulative main theorem       *)
(* concrete instance - truncated prefix by computation + mass        *)
(* lower bound (conclusion lands on the Set-typed QleT' of the       *)
(* current tree generation)                                          *)
(* ============================================================ *)

Theorem abf_top_p_cumulative_concrete :
  And (Id (top_p_prefix 1 (0%nat :: 1%nat :: nil) abf_uniform_w)
          (0%nat :: nil))
      (QleT' 1 (qsum_w abf_uniform_w
                 (top_p_prefix 1 (0%nat :: 1%nat :: nil) abf_uniform_w))).
Proof.
  split.
  - (* Truncation computed: p=1>0 so no early cutoff; w 0 = 1 hits the cap   *)
    (* so the prefix is exactly [0].                                         *)
    exact id_refl.
  - (* Mass lower bound: cumulative main theorem instantiated at p:=1,       *)
    (* sorted:=[0;1], uniform weights. The premise Qle 1 (1+(1+0)) is        *)
    (* supplied by Qle_bool reflection with eq_refl (premise position,       *)
    (* in-tree precedent); the upstream conclusion is already Set-typed      *)
    (* QleT' in the current tree generation and lands on the goal directly   *)
    (* (true use).                                                           *)
    apply (top_p_cumulative_ge 1 (0%nat :: 1%nat :: nil) abf_uniform_w).
    apply (proj1 (Qle_bool_iff 1 (qsum_w abf_uniform_w (0%nat :: 1%nat :: nil)))).
    exact eq_refl.
Qed.

(* ============================================================ *)
(* Sec.4 Carrier 4 - PRNG random walk: branch-weight conservation    *)
(* main theorem general form verbatim + concrete instance (seed      *)
(* ray weight 4 splits into two sub-rays 2+2=4), double use          *)
(* ============================================================ *)

Theorem abf_q_branch_weight_conserved :
  And (forall (phi : Q) (r : QRay),
         QId (rw (fst (q_branch phi r)) + rw (snd (q_branch phi r))) (rw r))
      (QId (rw (fst (q_branch 1 abf_seed_ray))
            + rw (snd (q_branch 1 abf_seed_ray)))
           4%Q).
Proof.
  split.
  - (* General form: main theorem cited verbatim (cross-file direct audit    *)
    (* wing).                                                                *)
    intros phi r. exact (q_branch_weight phi r).
  - (* Concrete instance: each sub-ray carries weight 4/2; QId enters via     *)
    (* qid_intro and closes by field.                                        *)
    cbn [abf_seed_ray q_branch rw fst snd].
    apply qid_intro. field.
Qed.

(* ============================================================ *)
(* Sec.5 Carrier 5 - audit resampling fallback: main theorem with    *)
(* leading section argument default_seq resolved at [0]              *)
(* (S01.Or Set-level disjunction, direct) + fallback computation     *)
(* face, double use                                                  *)
(* ============================================================ *)

Theorem abf_resample_fallback :
  And (forall (post_aud : PostAud) (g : nat -> Sequence) (attempts : nat),
         Or (Id (post_aud (resample_attempt (0%nat :: nil) post_aud g attempts))
                true)
            (Id (resample_attempt (0%nat :: nil) post_aud g attempts)
                (0%nat :: nil)))
      (Id (resample_attempt (0%nat :: nil) (fun _ => false) (fun _ => (1%nat :: nil)) 2%nat)
          (0%nat :: nil)).
Proof.
  split.
  - (* General form: fallback main theorem with its leading section argument  *)
    (* default_seq located at [0] by explicit instantiation (true use).       *)
    intros post_aud g attempts.
    exact (resample_terminates (0%nat :: nil) post_aud g attempts).
  - (* Concrete instance: the audit always rejects, the generator always      *)
    (* emits [1], and after two tries the fallback returns [0] (computation). *)
    exact id_refl.
Qed.

(* ============================================================ *)
(* Sec.6 Tail bay - assumption audit (cross-file audit of the S13    *)
(* reliability-surface main-theorem family + self-audit of the five  *)
(* carriers). Expected reading: all eleven lines print               *)
(* "Closed under the global context".                                *)
(* First 6 = the S13 audit-engine reliability-surface main-theorem   *)
(* family (including the qle_to_qleT bridge lemma adjacent to the    *)
(* top-p conclusion); last 5 = the five carriers of this file.       *)
(* Note: the Require closure spans the S01-S12 chain; the            *)
(* environment-level closure audit is kept separate from the         *)
(* per-theorem audit and is not introduced by this file.             *)
(* ============================================================ *)

Print Assumptions S13_NLiveAudit.LCAudit.early_stop_confidence.
Print Assumptions S13_NLiveAudit.LCAudit.early_stop_confidence'.
Print Assumptions S13_NLiveAudit.LCAudit.top_p_cumulative_ge.
Print Assumptions S13_NLiveAudit.LCAudit.resample_terminates.
Print Assumptions S13_NLiveAudit.q_branch_weight.
Print Assumptions S13_NLiveAudit.LCAudit.qle_to_qleT.
Print Assumptions abf_early_stop_fuel_and_run.
Print Assumptions abf_early_stop_all_pass_concrete.
Print Assumptions abf_top_p_cumulative_concrete.
Print Assumptions abf_q_branch_weight_conserved.
Print Assumptions abf_resample_fallback.

(* ============================================================ *)
(* Sec.7 Exit bay - carriers double as extraction ports            *)
(* (the extraction face carries zero magic constants)              *)
(* ============================================================ *)

From Stdlib Require Import Extraction.
Separate Extraction abf_early_stop_fuel_and_run
  abf_early_stop_all_pass_concrete abf_top_p_cumulative_concrete
  abf_q_branch_weight_conserved abf_resample_fallback.
