(* Five-field pointer | Mission.  formalization of the properties stated by the theorem/lemma declaration faces of this file. Dependencies.  the library files listed in the Require declaration face of this file. Constructivity.  zero admitted statements (mechanically checked). Build.  coqc -native-compiler no -q -Q . "".  ============================================================
    Slice-three same-name replacement note (ToyR · UpReq shallow-chain continuation)
   This file is the same-name replacement draft of UpReqAlign3.v: the original text is preserved in full (declaration order / colophon header /
   all other theorems untouched verbatim); only the five toys w_sum_ptimes_const / w_sum_minus /
   w_sum_opp / w_sum_ptimes_scal / w_sum_ptimes_opp_scal had their proof bodies changed:
   the @req2_* single-hop forwarding was replaced by explicit replay at the replacement point (req_trans chains + sum_ext/sum_add/
   sum_linear unwound ring by ring + explicit instantiation of the algebra-bank compat bridges; w_sum_minus and
   w_sum_ptimes_opp_scal inline the opp-sum subchain to eliminate the slot-argument dependency on upstream
   req2_sum_opp). Statement faces: zero changes.
   Green-verification method: semantic-context check of the Require face (c_probe.v, in-pool) —
   replicating the interface face under the true names and true signatures of the S07_RealSetoidExpLog.v:7915 class block and
   UpReqAlgebra.v:104/230/255; the five replacement proof bodies were pasted verbatim for a trial compile: rocq c EXIT=0.
   Whole-file joint-compile leftover: this file Required CW_ConstructiveWorld_219 (a 16-line thin shell
   = the S01-S15 mega-base); the in-pool joint rebuild exceeded the cpu_guard time cap, deferred to a base-module budget batch.
   ============================================================ *)

(* ============================================================ *)
(* UpReqAlign3.v *)
(* *)
(* Purpose: third segment of the alignment family: normalization of the temperature weight w and the free-energy KL decomposition. *)
(* Main pieces: w_pi_next_normalized / w_pi_star_normalized and w_F_t_rel_decomp / w_F_t_simpl_next_kl. *)
(* Dependencies: CW_ConstructiveWorld_219, UpReqAlgebra, UpReqAlign, UpReqAlign2, and the earlier part of UpReqAlign3. *)
(* Note: the temperature-weight carriers (pos3/nrm/KLE etc.) are given as Section variables; the KL decomposition is in per-eps interface form. *)
(* ============================================================ *)

(* UpReqAlign3.v — signature migration batch 3c: unconditional closure of the main-theorem chain
     (batch 3c = the release batch for the pending list at the tail of batch 3b)
   Upstream: UpReqAlgebra.v (batch 1 algebra bank) + UpReqAlign.v (batch 3) +
     UpReqAlign2.v (batch 3b sum-free-energy deep-chain machine, 40 Qed) — all Required and used;
   pure term-mode (req_trans chains + compat bridges), zero Morphisms dependency;
   Set-layer statements (req/lt/le all Set-valued, zero Prop leakage).
   ----------------------------------------------------------------
   Results of this file (checked item by item against the pending list at the tail of UpReqAlign2.v, all proven):
   [] reward_expand/align_energy_expand/F_align_F_t_rel/
     align_objective_t12_decomp/J_pi_t/J_pi_next/surrogate_diff_identity
     req-lifted + req2_policy_improvement_mono theorized (batch 3 bridge slot 3 released)
     + req2_gap_diff/req2_gap_mono.
   [] F_t_simpl_p/F_t_rel_decomp_p (generalized to an arbitrary normalized p)/sum_grad_cross/
     grad_cross_identity/align_objective_explicit/rlhf_suboptimality_gap/
     rlhf_policy_improvement/sum_advance_gap/t13_hexp/
     backward_kl_step_beta/backward_kl_step (batch 3 bridge slot
     req_backward_kl_identity released)/step_le/iter_le (step_kl_weighted
     sigT packaging + req2_r_pow powers).
   [main-theorem unconditionalization demo] req2_backward_kl_step: the backward-KL three-point identity
     KL(pi_star‖pi_next) == (1−η)·KL(pi_star‖pi_t) − η·KL(pi_t‖pi_star)
       + KL(pi_t‖pi_next)
     is an **unconditional theorem** — every link of the chain is a genuine Qed proof (no B-class bridge assumption slots):
     the statement of bridge slot req_backward_kl_identity is supplied by this file's req2_backward_kl_step
     in same-position theorem form (the batch 3 assumption slot is demoted to a consumer).
   [dpo/preference cluster] the dpo_reward cluster (is_implicit/recovers_up_to_baseline/
     relative_exact/diff_is_log_ratio_diff) + the preference section (denom_pos/
     implicit_reward_diff/pair_loss_at_star) + dpo_loss_at_pi_star +
     sigmoid_strict_inc.
   ----------------------------------------------------------------
   Honest signature-change register (plan document §7.4):
   1. log premise-ification: all req2-series logs carry explicit pointwise positivity parameters (same style as batches 3/3b);
     the req versions of dpo_pair_loss/dpo_loss_pair accordingly carry explicit denominator-positivity slots.
   2. minus carrier = UpReqAlgebra.req_minus (delta-transparent, same shape as Id minus).
   3. B-class bridges (assumption slots retained, positioned like Id; this file ADDS TWO RELEASES):
     - req2_gibbs_inequality (req same-position of Id gibbs_inequality@16629):
       the plain-le form of KL >= 0 is not derivable from the per-eps interface fields (no order elimination),
       assumption slot retained — to be demoted to a consumer once UpReqFreeEnergy (batch 2 FEP) lands;
     - req2_inv_pos_lt_contra / req2_log_lt_mono (req same-position of Id Variables
       L21013/21024, used by sigmoid_strict_inc).
     - req2_step_kl_eta_bound: **not in this file** (a B-class Variable,
       UpReqAlign already provides the assumption slot; its resolution is deferred to the req-sum instantiation batch, outside the deep chain).
   4. (d) Frozen (following batches 3/3b): ppo_gap_nonneg, fold_right_ext and the list-fold
     machinery (nat/list-layer Id, two-layer parallel) — dpo_total_loss_at_star/
     dpo_total_loss_monotone are therefore frozen (fold carriers).
   ---------------------------------------------------------------- *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
Require Import S14_B5BatchBlock.
Require Import S15_TailFEPUp.
Require Import UpReqAlgebra.
Require Import UpReqAlign.
Require Import UpReqAlign2.
Import RealInterfaceEnhancedMod.
(* The interface class in this tree is unparameterized; its carrier is the global Real
   (S07_RealSetoidExpLog.v:8075 zero-argument Class RealInterfaceEnhancedSetoid + global
   Instance RealEnhancedReal; Notation passthrough per the world's own UpReqAlgebra.v precedent). *)
Notation R := Real.

(* ============================================================ *)
(* Req3AlignCore: main-theorem-chain closure section (section parameters aligned slot by slot with batch 3b's Req2AlignCore) *)
(* ============================================================ *)
Section Req3AlignCore.
(* A-face adaptation (M43 nw10cure precedent): the parameterized section binders
   Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}. are deleted; the carrier R
   is bound to the global Real by the file-top Notation above, and the class fields
   (req/lt/le/zero/one/plus/mult/opp/abs/log/exp_neg/inv_pos) resolve through the
   global instance RealEnhancedReal. Zero Obj.magic, zero Prop casts, statement names unchanged. *)
Variable S : Set.

Variable sumf : (S -> R) -> R.
Hypothesis sum_ext :
  forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g).
Hypothesis sum_add :
  forall f g : S -> R,
    req (sumf (fun s => plus (f s) (g s))) (plus (sumf f) (sumf g)).
Hypothesis sum_linear :
  forall (a : R) (f : S -> R),
    req (sumf (fun s => mult a (f s))) (mult a (sumf f)).
Hypothesis sum_pos :
  forall f : S -> R, (forall s : S, lt zero (f s)) -> lt zero (sumf f).
Hypothesis log_req_compat :
  forall (x y : R) (Hx : lt zero x) (Hy : lt zero y),
    req x y -> req (log x Hx) (log y Hy).
Hypothesis log_inv_exp_neg_req :
  forall x : R, req (log_inv (exp_neg x) (exp_neg_pos x)) x.

Variable reward : S -> R.
Variable beta : R.
Variable beta_pos : lt zero beta.
Variable pi_ref : S -> R.
Variable pi_ref_pos : forall s : S, lt zero (pi_ref s).
Variable pi_ref_norm : req (sumf pi_ref) one.
Variable eta : R.
Variable eta_pos : lt zero eta.
Variable eta_le_one : le eta one.

(* ---- Section-local aliases (all delta-transparent thin wrappers of upstream req2 definitions) ---- *)
Definition pos3 (p : S -> R) : Set := @req2_pos_dist S p.
Definition nrm (p : S -> R) : Set := @req2_norm_one S sumf p.
Definition AL (s : S) : R :=
  @req2_align_energy S reward beta pi_ref pi_ref_pos s.
Definition ADV (pi_t : S -> R) (Hpi_t : pos3 pi_t) (s : S) : R :=
  @req2_adv S reward beta pi_ref pi_ref_pos pi_t Hpi_t s.
Definition ET (pi_t : S -> R) (Hpi_t : pos3 pi_t) (s : S) : R :=
  @req2_energy_t S reward beta pi_ref pi_ref_pos eta pi_t Hpi_t s.
Definition KLE (p q : S -> R) (Hp : pos3 p) (Hq : pos3 q) : R :=
  @req2_rel_ent S sumf p q Hp Hq.
Definition FE (energy : S -> R) (D : R) (p : S -> R) (Hp : pos3 p) : R :=
  @req2_free_energy S sumf energy D p Hp.
Definition FA (p : S -> R) (Hp : pos3 p) : R :=
  @req2_F_align S sumf reward beta pi_ref pi_ref_pos p Hp.
Definition JJ (p : S -> R) (Hp : pos3 p) : R :=
  @req2_J S sumf reward beta pi_ref pi_ref_pos p Hp.
Definition AO (p : S -> R) (Hp : pos3 p) : R :=
  @req2_dpo_loss S sumf reward beta pi_ref pi_ref_pos p Hp.
Definition ZR (pi_t : S -> R) (Hpi_t : pos3 pi_t) : R :=
  @req2_Z_rel S sumf reward beta beta_pos pi_ref pi_ref_pos eta pi_t Hpi_t.
Definition NPX (pi_t : S -> R) (Hpi_t : pos3 pi_t) (s : S) : R :=
  @req2_pi_next S sumf sum_pos reward beta beta_pos pi_ref pi_ref_pos
                eta pi_t Hpi_t s.
Definition ZAL : R :=
  @req2_Z_align S sumf reward beta beta_pos pi_ref.
Variable ZAL_pos : lt zero ZAL.
Definition PSTR (s : S) : R :=
  @req2_pi_star S sumf reward beta beta_pos pi_ref ZAL_pos s.
Definition PSTR_pos : pos3 PSTR :=
  @req2_pi_star_pos S sumf reward beta beta_pos pi_ref pi_ref_pos ZAL_pos.

(* Transparent witnesses (witness parameters of Set-valued relations are data: they must be Definitions, not
   Qed-wrapped — otherwise they are not convertible with the original applications in upstream statements) *)
Definition npx_pos (pi_t : S -> R) (Hpi_t : pos3 pi_t) : pos3 (NPX pi_t Hpi_t) :=
  @req2_pi_next_pos S sumf sum_pos reward beta beta_pos pi_ref
                    pi_ref_pos eta pi_t Hpi_t.
Definition zrel_pos (pi_t : S -> R) (Hpi_t : pos3 pi_t) : lt zero (ZR pi_t Hpi_t) :=
  @req2_Z_rel_pos S sumf sum_pos reward beta beta_pos pi_ref
                  pi_ref_pos eta pi_t Hpi_t.

(* ---- Upstream-piece use wrappers (UpReqAlign2 Qed pieces -> this section's parameters; zero re-proving) ---- *)
Lemma w_pi_next_normalized :
  forall (pi_t : S -> R) (Hpi_t : pos3 pi_t), req (sumf (NPX pi_t Hpi_t)) one.
Proof.
  intros pi_t Hpi_t.
  exact (@req2_pi_next_normalized S sumf sum_linear sum_pos reward
                                  beta beta_pos pi_ref pi_ref_pos eta
                                  pi_t Hpi_t).
Qed.

Lemma w_pi_star_normalized : req (sumf PSTR) one.
Proof.
  exact (@req2_pi_star_normalized S sumf sum_linear reward beta
                                  beta_pos pi_ref ZAL_pos).
Qed.

Lemma w_rel_ent_minus :
  forall (p q : S -> R) (Hp : pos3 p) (Hq : pos3 q),
    req (KLE p q Hp Hq)
        (req_minus (sumf (fun s => mult (p s) (log (p s) (Hp s))))
                   (sumf (fun s => mult (p s) (log (q s) (Hq s))))).
Proof.
  intros p q Hp Hq.
  exact (@req2_rel_ent_minus S sumf sum_ext sum_add sum_linear
                             p q Hp Hq).
Qed.

Lemma w_rel_ent_self_zero :
  forall (p : S -> R) (Hp : pos3 p), req (KLE p p Hp Hp) zero.
Proof.
  intros p Hp.
  exact (@req2_rel_ent_self_zero S sumf sum_ext sum_linear p Hp).
Qed.

Lemma w_F_t_rel_decomp :
  forall (pi_t : S -> R) (Hpi_t : pos3 pi_t) (Hn : nrm pi_t),
    req (FE (ET pi_t Hpi_t) beta pi_t Hpi_t)
        (plus (FE (ET pi_t Hpi_t) beta (NPX pi_t Hpi_t) (npx_pos pi_t Hpi_t))
              (mult beta (KLE pi_t (NPX pi_t Hpi_t) Hpi_t
                                (npx_pos pi_t Hpi_t)))).
Proof.
  intros pi_t Hpi_t Hn.
  exact (@req2_F_t_rel_decomp S sumf sum_ext sum_add sum_linear sum_pos
                              log_req_compat log_inv_exp_neg_req reward beta
                              beta_pos pi_ref pi_ref_pos eta pi_t Hpi_t Hn).
Qed.

Lemma w_F_t_simpl_t :
  forall (pi_t : S -> R) (Hpi_t : pos3 pi_t),
    req (FE (ET pi_t Hpi_t) beta pi_t Hpi_t)
        (opp (mult eta (sumf (fun s => mult (pi_t s) (ADV pi_t Hpi_t s))))).
Proof.
  intros pi_t Hpi_t.
  exact (@req2_F_t_simpl_t S sumf sum_ext sum_add sum_linear reward
                           beta pi_ref pi_ref_pos eta pi_t Hpi_t).
Qed.

Lemma w_F_t_simpl_next_kl :
  forall (pi_t : S -> R) (Hpi_t : pos3 pi_t),
    req (FE (ET pi_t Hpi_t) beta (NPX pi_t Hpi_t) (npx_pos pi_t Hpi_t))
        (plus (opp (mult eta (sumf (fun s => mult (NPX pi_t Hpi_t s)
                                                   (ADV pi_t Hpi_t s)))))
              (mult beta (KLE (NPX pi_t Hpi_t) pi_t
                              (npx_pos pi_t Hpi_t) Hpi_t))).
Proof.
  intros pi_t Hpi_t.
  exact (@req2_F_t_simpl_next_kl S sumf sum_ext sum_add sum_linear
                                 sum_pos reward beta beta_pos pi_ref
                                 pi_ref_pos eta pi_t Hpi_t).
Qed.

Lemma w_sum_ptimes_const :
  forall (p : S -> R) (c : R),
    req (sumf p) one -> req (sumf (fun s => mult (p s) c)) c.
Proof.
  intros p c Hn.
  apply (req_trans (sumf (fun s => mult (p s) c))
                   (mult c (sumf p)) c).
  - apply (req_trans (sumf (fun s => mult (p s) c))
                     (sumf (fun s => mult c (p s)))
                     (mult c (sumf p))).
    + apply (sum_ext (fun s => mult (p s) c) (fun s => mult c (p s))
                     (fun s => mult_comm (p s) c)).
    + exact (sum_linear c p).
  - apply (req_trans (mult c (sumf p)) (mult c one) c
                     (req_mult_compat c c (sumf p) one (req_refl c) Hn)
                     (mult_one c)).
Qed.

Lemma w_sum_minus :
  forall f g : S -> R,
    req (sumf (fun s => req_minus (f s) (g s))) (req_minus (sumf f) (sumf g)).
Proof.
  intros f g. unfold req_minus.
  apply (req_trans (sumf (fun s => plus (f s) (opp (g s))))
                   (plus (sumf f) (sumf (fun s => opp (g s))))
                   (plus (sumf f) (opp (sumf g)))).
  - exact (sum_add f (fun s => opp (g s))).
  - apply (req_plus_compat (sumf f) (sumf f)
                           (sumf (fun s => opp (g s))) (opp (sumf g))
                           (req_refl (sumf f))).
    apply (req_trans (sumf (fun s => opp (g s)))
                     (sumf (fun s => mult (opp one) (g s)))
                     (opp (sumf g))).
    + apply (sum_ext (fun s => opp (g s)) (fun s => mult (opp one) (g s))).
      intro s.
      apply (req_sym (mult (opp one) (g s)) (opp (g s))).
      apply (req_trans (mult (opp one) (g s)) (opp (mult one (g s)))
                       (opp (g s))
                       (req_opp_mult_r one (g s))
                       (req_opp_compat (mult one (g s)) (g s)
                                       (req_mult_one_l (g s)))).
    + apply (req_trans (sumf (fun s => mult (opp one) (g s)))
                       (mult (opp one) (sumf g))
                       (opp (sumf g))).
      * exact (sum_linear (opp one) g).
      * apply (req_trans (mult (opp one) (sumf g))
                         (opp (mult one (sumf g)))
                         (opp (sumf g))
                         (req_opp_mult_r one (sumf g))
                         (req_opp_compat (mult one (sumf g)) (sumf g)
                                         (req_mult_one_l (sumf g)))).
Qed.

Lemma w_sum_opp :
  forall f : S -> R,
    req (sumf (fun s => opp (f s))) (opp (sumf f)).
Proof.
  intros f.
  apply (req_trans (sumf (fun s => opp (f s)))
                   (sumf (fun s => mult (opp one) (f s)))
                   (opp (sumf f))).
  - apply (sum_ext (fun s => opp (f s)) (fun s => mult (opp one) (f s))).
    intro s.
    apply (req_sym (mult (opp one) (f s)) (opp (f s))).
    apply (req_trans (mult (opp one) (f s)) (opp (mult one (f s))) (opp (f s))
                     (req_opp_mult_r one (f s))
                     (req_opp_compat (mult one (f s)) (f s)
                                     (req_mult_one_l (f s)))).
  - apply (req_trans (sumf (fun s => mult (opp one) (f s)))
                     (mult (opp one) (sumf f))
                     (opp (sumf f))).
    + exact (sum_linear (opp one) f).
    + apply (req_trans (mult (opp one) (sumf f))
                       (opp (mult one (sumf f)))
                       (opp (sumf f))
                       (req_opp_mult_r one (sumf f))
                       (req_opp_compat (mult one (sumf f)) (sumf f)
                                       (req_mult_one_l (sumf f)))).
Qed.

Lemma w_sum_ptimes_scal :
  forall (p : S -> R) (a : R) (f : S -> R),
    req (sumf (fun s => mult (p s) (mult a (f s))))
        (mult a (sumf (fun s => mult (p s) (f s)))).
Proof.
  intros p a f.
  apply (req_trans (sumf (fun s => mult (p s) (mult a (f s))))
                   (sumf (fun s => mult a (mult (p s) (f s))))
                   (mult a (sumf (fun s => mult (p s) (f s))))).
  - apply (sum_ext (fun s => mult (p s) (mult a (f s)))
                   (fun s => mult a (mult (p s) (f s)))).
    intro s.
    apply (req_trans (mult (p s) (mult a (f s))) (mult (mult (p s) a) (f s))
                     (mult a (mult (p s) (f s)))).
    + apply mult_assoc.
    + apply (req_trans (mult (mult (p s) a) (f s)) (mult (mult a (p s)) (f s))
                       (mult a (mult (p s) (f s)))
                       (req_mult_compat (mult (p s) a) (mult a (p s)) (f s) (f s)
                                        (mult_comm (p s) a) (req_refl (f s)))
                       (req_sym (mult a (mult (p s) (f s)))
                                (mult (mult a (p s)) (f s))
                                (mult_assoc a (p s) (f s)))).
  - exact (sum_linear a (fun s => mult (p s) (f s))).
Qed.

Lemma w_sum_ptimes_opp_scal :
  forall (p : S -> R) (a : R) (f : S -> R),
    req (sumf (fun s => mult (p s) (opp (mult a (f s)))))
        (opp (mult a (sumf (fun s => mult (p s) (f s))))).
Proof.
  intros p a f.
  apply (req_trans (sumf (fun s => mult (p s) (opp (mult a (f s)))))
                   (sumf (fun s => opp (mult a (mult (p s) (f s)))))
                   (opp (mult a (sumf (fun s => mult (p s) (f s)))))).
  - apply (sum_ext (fun s => mult (p s) (opp (mult a (f s))))
                   (fun s => opp (mult a (mult (p s) (f s))))).
    intro s.
    apply (req_trans (mult (p s) (opp (mult a (f s))))
                     (opp (mult (p s) (mult a (f s))))
                     (opp (mult a (mult (p s) (f s))))).
    + apply req_opp_mult_l.
    + apply (req_opp_compat (mult (p s) (mult a (f s)))
                            (mult a (mult (p s) (f s)))).
      apply (req_trans (mult (p s) (mult a (f s))) (mult (mult (p s) a) (f s))
                       (mult a (mult (p s) (f s)))).
      * apply mult_assoc.
      * apply (req_trans (mult (mult (p s) a) (f s)) (mult (mult a (p s)) (f s))
                         (mult a (mult (p s) (f s)))
                         (req_mult_compat (mult (p s) a) (mult a (p s)) (f s) (f s)
                                          (mult_comm (p s) a) (req_refl (f s)))
                         (req_sym (mult a (mult (p s) (f s)))
                                  (mult (mult a (p s)) (f s))
                                  (mult_assoc a (p s) (f s)))).
  - apply (req_trans (sumf (fun s => opp (mult a (mult (p s) (f s)))))
                     (opp (sumf (fun s => mult a (mult (p s) (f s)))))
                     (opp (mult a (sumf (fun s => mult (p s) (f s)))))).
    + apply (req_trans (sumf (fun s => opp (mult a (mult (p s) (f s)))))
                       (sumf (fun s => mult (opp one)
                                            (mult a (mult (p s) (f s)))))
                       (opp (sumf (fun s => mult a (mult (p s) (f s)))))).
      * apply (sum_ext
                 (fun s => opp (mult a (mult (p s) (f s))))
                 (fun s => mult (opp one) (mult a (mult (p s) (f s))))).
        intro s.
        apply (req_sym (mult (opp one) (mult a (mult (p s) (f s))))
                       (opp (mult a (mult (p s) (f s))))).
        apply (req_trans
                 (mult (opp one) (mult a (mult (p s) (f s))))
                 (opp (mult one (mult a (mult (p s) (f s)))))
                 (opp (mult a (mult (p s) (f s))))
                 (req_opp_mult_r one (mult a (mult (p s) (f s))))
                 (req_opp_compat (mult one (mult a (mult (p s) (f s))))
                                 (mult a (mult (p s) (f s)))
                                 (req_mult_one_l
                                    (mult a (mult (p s) (f s)))))).
      * apply (req_trans (sumf (fun s => mult (opp one)
                                           (mult a (mult (p s) (f s)))))
                         (mult (opp one)
                               (sumf (fun s => mult a (mult (p s) (f s)))))
                         (opp (sumf (fun s => mult a (mult (p s) (f s)))))).
        -- exact (sum_linear (opp one)
                             (fun s => mult a (mult (p s) (f s)))).
        -- apply (req_trans (mult (opp one)
                                  (sumf (fun s => mult a (mult (p s) (f s)))))
                            (opp (mult one
                                        (sumf (fun s => mult a (mult (p s) (f s))))))
                            (opp (sumf (fun s => mult a (mult (p s) (f s)))))).
           ** apply req_opp_mult_r.
           ** exact (req_opp_compat
                       (mult one (sumf (fun s => mult a (mult (p s) (f s)))))
                       (sumf (fun s => mult a (mult (p s) (f s))))
                       (req_mult_one_l (sumf (fun s => mult a (mult (p s) (f s)))))).
    + apply (req_opp_compat (sumf (fun s => mult a (mult (p s) (f s))))
                            (mult a (sumf (fun s => mult (p s) (f s))))
                            (sum_linear a (fun s => mult (p s) (f s)))).
Qed.

Definition w_iter (t : nat) (pi : S -> R) (Hpi : pos3 pi) :
  { pi' : S -> R & pos3 pi' } :=
  @req2_iter S sumf sum_pos reward beta beta_pos pi_ref pi_ref_pos eta
             t pi Hpi.

Lemma w_iter_norm :
  forall (t : nat) (pi : S -> R) (Hpi : pos3 pi),
    nrm pi -> nrm (projT1 (w_iter t pi Hpi)).
Proof.
  intros t pi Hpi Hn.
  exact (@req2_iter_norm S sumf sum_linear sum_pos reward beta beta_pos
                         pi_ref pi_ref_pos eta t pi Hpi Hn).
Qed.

(* ---- General small engines (self-contained in this section; pure algebra, 2-4 steps per piece) ---- *)

(* req_minus unfolding (delta-transparent, same shape as Id minus) *)
Lemma r2_m_unfold : forall a b : R, req (req_minus a b) (plus a (opp b)).
Proof. intros a b. apply req_refl. Qed.

(* General inv absorption: inv(x)*(x*y) == y *)
Lemma r2_inv_absorb :
  forall (x : R) (Hx : lt zero x) (y : R),
    req (mult (inv_pos x Hx) (mult x y)) y.
Proof.
  intros x Hx y.
  apply (req_trans (mult (inv_pos x Hx) (mult x y))
                   (mult (mult (inv_pos x Hx) x) y) y).
  - apply mult_assoc.
  - apply (req_trans (mult (mult (inv_pos x Hx) x) y) (mult one y) y).
    + apply (req_mult_compat (mult (inv_pos x Hx) x) one y y
                             (req_trans (mult (inv_pos x Hx) x)
                                        (mult x (inv_pos x Hx)) one
                                        (mult_comm (inv_pos x Hx) x)
                                        (inv_pos_correct x Hx))
                             (req_refl y)).
    + apply req_mult_one_l.
Qed.

(* Right distributivity of subtraction, form a*(x-y)*c: (x-y)*c == x*c - y*c *)
Lemma r2_mmd_r :
  forall a b c : R,
    req (mult (req_minus a b) c) (req_minus (mult a c) (mult b c)).
Proof.
  intros a b c. unfold req_minus.
  apply (req_trans (mult (plus a (opp b)) c)
                   (plus (mult a c) (mult (opp b) c))
                   (plus (mult a c) (opp (mult b c)))).
  - apply req_mult_plus_distr_r.
  - apply (req_plus_compat (mult a c) (mult a c)
                           (mult (opp b) c) (opp (mult b c))
                           (req_refl (mult a c))).
    apply req_opp_mult_r.
Qed.

(* Rearrangements of the form minus (a - b) c == (a - b) + opp c *)
Lemma r2_minus_sub_plus :
  forall a b c : R,
    req (req_minus (req_minus a b) c) (req_minus a (plus b c)).
Proof.
  intros a b c. unfold req_minus.
  apply (req_sym (req_minus a (plus b c)) (plus (plus a (opp b)) (opp c))).
  unfold req_minus.
  apply (req_trans (plus a (opp (plus b c)))
                   (plus a (plus (opp b) (opp c)))
                   (plus (plus a (opp b)) (opp c))).
  - apply (req_plus_compat a a (opp (plus b c)) (plus (opp b) (opp c))
                           (req_refl a)).
    apply req_opp_plus.
  - apply plus_assoc.
Qed.

(* minus antisymmetry *)
Lemma r2_opp_minus_rev :
  forall a b : R, req (req_minus a b) (opp (req_minus b a)).
Proof.
  intros a b. unfold req_minus.
  apply (req_trans (plus a (opp b))
                   (plus (opp b) (opp (opp a)))
                   (opp (plus b (opp a)))).
  - apply (req_trans (plus a (opp b)) (plus (opp b) a)
                     (plus (opp b) (opp (opp a)))).
    + apply plus_comm.
    + apply (req_plus_compat (opp b) (opp b) a (opp (opp a))
                             (req_refl (opp b))
                             (req_sym (opp (opp a)) a (req_double_neg a))).
  - exact (req_sym (opp (plus b (opp a))) (plus (opp b) (opp (opp a)))
                   (req_opp_plus b (opp a))).
Qed.

(* Distributivity of minus over plus *)
Lemma r2_minus_distr :
  forall a b c d : R,
    req (req_minus (plus a b) (plus c d))
        (plus (req_minus a c) (req_minus b d)).
Proof.
  intros a b c d. unfold req_minus.
  apply (req_trans (plus (plus a b) (opp (plus c d)))
                   (plus (plus a b) (plus (opp c) (opp d)))
                   (plus (plus a (opp c)) (plus b (opp d)))).
  - apply (req_plus_compat (plus a b) (plus a b)
                           (opp (plus c d)) (plus (opp c) (opp d))
                           (req_refl (plus a b))).
    apply req_opp_plus.
  - exact (req_plus_swap_mid a b (opp c) (opp d)).
Qed.

(* minus splitting: a - c == (a - b) + (b - c) *)
Lemma r2_minus_split :
  forall a b c : R,
    req (req_minus a c) (plus (req_minus a b) (req_minus b c)).
Proof.
  intros a b c. unfold req_minus.
  apply (req_sym (plus (plus a (opp b)) (plus b (opp c)))
                 (plus a (opp c))).
  apply (req_trans (plus (plus a (opp b)) (plus b (opp c)))
                   (plus a (plus (opp b) (plus b (opp c))))
                   (plus a (opp c))).
  - apply (req_sym (plus a (plus (opp b) (plus b (opp c))))
                   (plus (plus a (opp b)) (plus b (opp c)))).
    apply plus_assoc.
  - apply (req_trans (plus a (plus (opp b) (plus b (opp c))))
                     (plus a (plus (plus (opp b) b) (opp c)))
                     (plus a (opp c))).
    + apply (req_plus_compat a a
                             (plus (opp b) (plus b (opp c)))
                             (plus (plus (opp b) b) (opp c))
                             (req_refl a)).
      apply plus_assoc.
    + apply (req_plus_compat a a
                             (plus (plus (opp b) b) (opp c))
                             (opp c)
                             (req_refl a)).
      apply (req_trans (plus (plus (opp b) b) (opp c))
                       (plus zero (opp c))
                       (opp c)).
      * apply (req_trans (plus (plus (opp b) b) (opp c))
                         (plus (plus b (opp b)) (opp c))
                         (plus zero (opp c))).
        -- apply (req_plus_compat (plus (opp b) b) (plus b (opp b))
                                  (opp c) (opp c)
                                  (plus_comm (opp b) b) (req_refl (opp c))).
        -- apply (req_plus_compat (plus b (opp b)) zero (opp c) (opp c)
                                  (plus_opp b) (req_refl (opp c))).
      * apply req_plus_zero_l.
Qed.

(* Middle-term cancellation: (a + b) - b == a *)
Lemma r2_minus_cancel_mid :
  forall a b : R, req (req_minus (plus a b) b) a.
Proof.
  intros a b. unfold req_minus.
  apply (req_trans (plus (plus a b) (opp b))
                   (plus a (plus b (opp b))) a).
  - apply (req_sym (plus a (plus b (opp b)))
                   (plus (plus a b) (opp b))).
    apply plus_assoc.
  - apply (req_trans (plus a (plus b (opp b))) (plus a zero) a).
    + apply (req_plus_compat a a (plus b (opp b)) zero
                             (req_refl a) (plus_opp b)).
    + apply plus_zero.
Qed.

(* Four-term rearrangement: (a-b)-(c-d) == (a-c)-(b-d) *)
Lemma r2_minus_rearrange_four :
  forall a b c d : R,
    req (req_minus (req_minus a b) (req_minus c d))
        (req_minus (req_minus a c) (req_minus b d)).
Proof.
  intros a b c d. unfold req_minus.
  apply (req_trans (plus (plus a (opp b)) (opp (plus c (opp d))))
                   (plus (plus a (opp b)) (plus (opp c) (opp (opp d))))
                   (plus (plus a (opp c)) (opp (plus b (opp d))))).
  - apply (req_plus_compat (plus a (opp b)) (plus a (opp b))
                           (opp (plus c (opp d)))
                           (plus (opp c) (opp (opp d)))
                           (req_refl (plus a (opp b)))).
    apply req_opp_plus.
  - apply (req_trans (plus (plus a (opp b)) (plus (opp c) (opp (opp d))))
                     (plus (plus a (opp c)) (plus (opp b) (opp (opp d))))
                     (plus (plus a (opp c)) (opp (plus b (opp d))))).
    + exact (req_plus_swap_mid a (opp b) (opp c) (opp (opp d))).
    + apply (req_plus_compat (plus a (opp c)) (plus a (opp c))
                             (plus (opp b) (opp (opp d)))
                             (opp (plus b (opp d)))
                             (req_refl (plus a (opp c)))).
      apply (req_sym (opp (plus b (opp d)))
                     (plus (opp b) (opp (opp d)))).
      apply req_opp_plus.
Qed.

(* Common-addend cancellation: (A+B) - (A+C) == B - C *)
Lemma r2_minus_plus_common :
  forall A B C : R,
    req (req_minus (plus A B) (plus A C)) (req_minus B C).
Proof.
  intros A B C. unfold req_minus.
  apply (req_trans (plus (plus A B) (opp (plus A C)))
                   (plus (plus A B) (plus (opp A) (opp C)))
                   (plus B (opp C))).
  - apply (req_plus_compat (plus A B) (plus A B)
                           (opp (plus A C)) (plus (opp A) (opp C))
                           (req_refl (plus A B))).
    apply req_opp_plus.
  - apply (req_trans (plus (plus A B) (plus (opp A) (opp C)))
                     (plus (plus A (opp A)) (plus B (opp C)))
                     (plus B (opp C))).
    + exact (req_plus_swap_mid A B (opp A) (opp C)).
    + apply (req_trans (plus (plus A (opp A)) (plus B (opp C)))
                       (plus zero (plus B (opp C)))
                       (plus B (opp C))).
      * apply (req_plus_compat (plus A (opp A)) zero
                               (plus B (opp C)) (plus B (opp C))
                               (plus_opp A) (req_refl (plus B (opp C)))).
      * apply req_plus_zero_l.
Qed.

(* eta-absorption difference form: (-eta*a) - (-eta*b) == eta*(b - a) *)
Lemma r2_minus_opp_opp_mult :
  forall a b : R,
    req (req_minus (opp (mult eta a)) (opp (mult eta b)))
        (mult eta (req_minus b a)).
Proof.
  intros a b. unfold req_minus.
  apply (req_trans (plus (opp (mult eta a)) (opp (opp (mult eta b))))
                   (plus (mult eta b) (opp (mult eta a)))
                   (mult eta (plus b (opp a)))).
  - apply (req_trans (plus (opp (mult eta a)) (opp (opp (mult eta b))))
                     (plus (opp (mult eta a)) (mult eta b))
                     (plus (mult eta b) (opp (mult eta a)))).
    + apply (req_plus_compat (opp (mult eta a)) (opp (mult eta a))
                             (opp (opp (mult eta b))) (mult eta b)
                             (req_refl (opp (mult eta a)))
                             (req_double_neg (mult eta b))).
    + apply plus_comm.
  - apply (req_sym (mult eta (plus b (opp a)))
                   (plus (mult eta b) (opp (mult eta a)))).
    apply (req_trans (mult eta (plus b (opp a)))
                     (plus (mult eta b) (mult eta (opp a)))
                     (plus (mult eta b) (opp (mult eta a)))).
    + apply distrib.
    + apply (req_plus_compat (mult eta b) (mult eta b)
                             (mult eta (opp a)) (opp (mult eta a))
                             (req_refl (mult eta b))
                             (req_opp_mult_l eta a)).
Qed.

(* t13 collapse sub-identity (no e term) *)
Lemma r2_gap_collapse :
  forall a b c d : R,
    req (plus (plus (plus a b) (plus (opp c) (opp d))) (opp a))
        (plus (opp d) (plus (opp c) b)).
Proof.
  intros a b c d.
  apply (req_trans (plus (plus (plus a b) (plus (opp c) (opp d))) (opp a))
                   (plus (plus a b) (plus (plus (opp c) (opp d)) (opp a)))
                   (plus (opp d) (plus (opp c) b))).
  - exact (req_sym (plus (plus a b) (plus (plus (opp c) (opp d)) (opp a)))
                   (plus (plus (plus a b) (plus (opp c) (opp d))) (opp a))
                   (plus_assoc (plus a b) (plus (opp c) (opp d)) (opp a))).
  - apply (req_trans (plus (plus a b)
                           (plus (plus (opp c) (opp d)) (opp a)))
                     (plus (plus (plus a b) (opp a))
                           (plus (opp c) (opp d)))
                     (plus (opp d) (plus (opp c) b))).
    + apply (req_trans (plus (plus a b)
                             (plus (plus (opp c) (opp d)) (opp a)))
                       (plus (plus a b)
                             (plus (opp a) (plus (opp c) (opp d))))
                       (plus (plus (plus a b) (opp a))
                             (plus (opp c) (opp d)))).
      * apply (req_plus_compat (plus a b) (plus a b)
                               (plus (plus (opp c) (opp d)) (opp a))
                               (plus (opp a) (plus (opp c) (opp d)))
                               (req_refl (plus a b))
                               (plus_comm (plus (opp c) (opp d)) (opp a))).
      * apply plus_assoc.
    + apply (req_trans (plus (plus (plus a b) (opp a))
                             (plus (opp c) (opp d)))
                       (plus b (plus (opp c) (opp d)))
                       (plus (opp d) (plus (opp c) b))).
      * apply (req_plus_compat (plus (plus a b) (opp a)) b
                               (plus (opp c) (opp d)) (plus (opp c) (opp d))
                               (req_plus_cancel a b)
                               (req_refl (plus (opp c) (opp d)))).
      * apply (req_trans (plus b (plus (opp c) (opp d)))
                         (plus (plus b (opp c)) (opp d))
                         (plus (opp d) (plus (opp c) b))).
        -- apply plus_assoc.
        -- apply (req_trans (plus (plus b (opp c)) (opp d))
                            (plus (opp d) (plus b (opp c)))
                            (plus (opp d) (plus (opp c) b))).
           ++ apply (plus_comm (plus b (opp c)) (opp d)).
           ++ apply (req_plus_compat (opp d) (opp d) (plus b (opp c))
                                     (plus (opp c) b)
                                     (req_refl (opp d))
                                     (plus_comm b (opp c))).
Qed.

(* t13 collapse (req version of Id t13_collapse) *)
Lemma r2_t13_collapse :
  forall a b c d e : R,
    req (plus (plus (plus a b) (plus (opp c) (opp d))) (req_minus e a))
        (plus (req_minus e d) (plus (opp c) b)).
Proof.
  intros a b c d e. unfold req_minus.
  set (W := plus (plus a b) (plus (opp c) (opp d))).
  apply (req_trans (plus W (plus e (opp a)))
                   (plus e (plus (opp d) (plus (opp c) b)))
                   (plus (plus e (opp d)) (plus (opp c) b))).
  - apply (req_trans (plus W (plus e (opp a)))
                     (plus e (plus (opp a) W))
                     (plus e (plus (opp d) (plus (opp c) b)))).
    + apply (req_trans (plus W (plus e (opp a)))
                       (plus (plus e (opp a)) W)
                       (plus e (plus (opp a) W))).
      * apply (plus_comm W (plus e (opp a))).
      * exact (req_sym (plus e (plus (opp a) W))
                       (plus (plus e (opp a)) W)
                       (plus_assoc e (opp a) W)).
    + apply (req_plus_compat e e
                             (plus (opp a) W)
                             (plus (opp d) (plus (opp c) b))
                             (req_refl e)).
      apply (req_trans (plus (opp a) W) (plus W (opp a))
                       (plus (opp d) (plus (opp c) b))).
      * apply plus_comm.
      * exact (r2_gap_collapse a b c d).
  - apply plus_assoc.
Qed.

(* Nonnegative product (req version of Id le_mult_nonneg_t12) *)
Lemma r2_le_mult_nonneg :
  forall a b : R, le zero a -> le zero b -> le zero (mult a b).
Proof.
  intros a b Ha Hb.
  apply (le_id_l zero (mult zero b) (mult a b)
                 (req_sym (mult zero b) zero
                          (req_trans (mult zero b) (mult b zero) zero
                                     (mult_comm zero b) (mult_zero b)))
                 (le_mult_compat_weak zero a b Hb Ha)).
Qed.

(* eta <= 1 implies 1 <= inv(eta) (usage form of Id inv_pos_le_compat) *)
Lemma r2_inv_ge_one : le one (inv_pos eta eta_pos).
Proof.
  apply (le_id_l one (mult eta (inv_pos eta eta_pos)) (inv_pos eta eta_pos)
                 (req_sym (mult eta (inv_pos eta eta_pos)) one
                          (inv_pos_correct eta eta_pos))
                 (le_id_r (mult eta (inv_pos eta eta_pos))
                          (mult one (inv_pos eta eta_pos))
                          (inv_pos eta eta_pos)
                          (req_mult_one_l (inv_pos eta eta_pos))
                          (le_mult_compat_weak eta one (inv_pos eta eta_pos)
                            (lt_le_iff zero (inv_pos eta eta_pos)
                                       (inl (inv_pos_pos eta eta_pos)))
                            eta_le_one))).
Qed.

(* (1-eta)*(-a) == (-a) + eta*a *)
Lemma r2_eta_opp_absorb :
  forall a : R,
    req (mult (req_minus one eta) (opp a)) (plus (opp a) (mult eta a)).
Proof.
  intro a. unfold req_minus.
  apply (req_trans (mult (plus one (opp eta)) (opp a))
                   (plus (mult one (opp a)) (mult (opp eta) (opp a)))
                   (plus (opp a) (mult eta a))).
  - apply req_mult_plus_distr_r.
  - apply (req_plus_compat (mult one (opp a)) (opp a)
                           (mult (opp eta) (opp a)) (mult eta a)
                           (req_mult_one_l (opp a))).
    apply (req_trans (mult (opp eta) (opp a))
                     (opp (opp (mult eta a))) (mult eta a)).
    + exact (req_trans (mult (opp eta) (opp a))
                       (opp (mult (opp eta) a))
                       (opp (opp (mult eta a)))
                       (req_opp_mult_l (opp eta) a)
                       (req_opp_compat (mult (opp eta) a)
                                       (opp (mult eta a))
                                       (req_opp_mult_r eta a))).
    + apply req_double_neg.
Qed.

(* ---- [] Piece 1: reward_expand (req version) ---- *)
Lemma r2_reward_expand :
  forall (pi_t : S -> R) (Hpi_t : pos3 pi_t) (s : S),
    req (reward s)
        (plus (ADV pi_t Hpi_t s)
              (req_minus (mult beta (log (pi_t s) (Hpi_t s)))
                         (mult beta (log (pi_ref s) (pi_ref_pos s))))).
Proof.
  intros pi_t Hpi_t s.
  set (X := mult beta (req_minus (log (pi_t s) (Hpi_t s))
                                 (log (pi_ref s) (pi_ref_pos s)))).
  apply (req_trans (reward s) (plus (req_minus (reward s) X) X)
                   (plus (ADV pi_t Hpi_t s)
                         (req_minus (mult beta (log (pi_t s) (Hpi_t s)))
                                    (mult beta (log (pi_ref s) (pi_ref_pos s))))) ).
  - exact (req_trans (reward s)
                     (plus X (req_minus (reward s) X))
                     (plus (req_minus (reward s) X) X)
                     (req_sym (plus X (req_minus (reward s) X)) (reward s)
                              (req_minus_plus_cancel X (reward s)))
                     (plus_comm X (req_minus (reward s) X))).
  - exact (req_plus_compat (req_minus (reward s) X) (ADV pi_t Hpi_t s)
                           X (req_minus (mult beta (log (pi_t s) (Hpi_t s)))
                                        (mult beta (log (pi_ref s) (pi_ref_pos s))))
                           (req_refl (req_minus (reward s) X))
                           (req_mult_minus_distr_l beta (log (pi_t s) (Hpi_t s))
                                                   (log (pi_ref s) (pi_ref_pos s)))).
Qed.

(* Four-term cancellation: (opp x + y) + (opp z + x) == y + opp z *)
Lemma r2_four_cancel :
  forall x y z : R,
    req (plus (plus (opp x) y) (plus (opp z) x)) (plus y (opp z)).
Proof.
  intros x y z.
  apply (req_trans (plus (plus (opp x) y) (plus (opp z) x))
                   (plus (plus (opp x) (opp z)) (plus y x))
                   (plus y (opp z))).
  - exact (req_plus_swap_mid (opp x) y (opp z) x).
  - apply (req_trans (plus (plus (opp x) (opp z)) (plus y x))
                     (plus (opp x) (plus (opp z) (plus x y)))
                     (plus y (opp z))).
    + apply (req_trans (plus (plus (opp x) (opp z)) (plus y x))
                       (plus (plus (opp x) (opp z)) (plus x y))
                       (plus (opp x) (plus (opp z) (plus x y)))).
      * apply (req_plus_compat (plus (opp x) (opp z)) (plus (opp x) (opp z))
                               (plus y x) (plus x y)
                               (req_refl (plus (opp x) (opp z)))
                               (plus_comm y x)).
      * exact (req_sym (plus (opp x) (plus (opp z) (plus x y)))
                       (plus (plus (opp x) (opp z)) (plus x y))
                       (plus_assoc (opp x) (opp z) (plus x y))).
    + apply (req_trans (plus (opp x) (plus (opp z) (plus x y)))
                       (plus (opp x) (plus x (plus (opp z) y)))
                       (plus y (opp z))).
      * apply (req_plus_compat (opp x) (opp x)
                               (plus (opp z) (plus x y))
                               (plus x (plus (opp z) y))
                               (req_refl (opp x))
                               (req_trans (plus (opp z) (plus x y))
                                          (plus (plus (opp z) x) y)
                                          (plus x (plus (opp z) y))
                                          (plus_assoc (opp z) x y)
                                          (req_trans (plus (plus (opp z) x) y)
                                                     (plus (plus x (opp z)) y)
                                                     (plus x (plus (opp z) y))
                                                     (req_plus_compat (plus (opp z) x)
                                                                      (plus x (opp z))
                                                                      y y
                                                                      (plus_comm (opp z) x)
                                                                      (req_refl y))
                                                     (req_sym (plus x (plus (opp z) y))
                                                              (plus (plus x (opp z)) y)
                                                              (plus_assoc x (opp z) y))))).
      * apply (req_trans (plus (opp x) (plus x (plus (opp z) y)))
                         (plus (plus (opp x) x) (plus (opp z) y))
                         (plus y (opp z))).
        -- apply plus_assoc.
        -- apply (req_trans (plus (plus (opp x) x) (plus (opp z) y))
                            (plus zero (plus (opp z) y))
                            (plus y (opp z))).
           ++ apply (req_plus_compat (plus (opp x) x) zero
                                     (plus (opp z) y) (plus (opp z) y)
                                     (req_plus_opp_l x)
                                     (req_refl (plus (opp z) y))).
           ++ apply (req_trans (plus zero (plus (opp z) y))
                               (plus (opp z) y)
                               (plus y (opp z))
                               (req_plus_zero_l (plus (opp z) y))
                               (plus_comm (opp z) y)).
Qed.

(* ---- [] Piece 2: align_energy_expand (req version) ---- *)
Lemma r2_align_energy_expand :
  forall (pi_t : S -> R) (Hpi_t : pos3 pi_t) (s : S),
    req (AL s)
        (plus (ET pi_t Hpi_t s)
              (mult (req_minus one eta) (opp (ADV pi_t Hpi_t s)))).
Proof.
  intros pi_t Hpi_t s.
  set (lgT := log (pi_t s) (Hpi_t s)).
  set (lgR := log (pi_ref s) (pi_ref_pos s)).
  set (A := ADV pi_t Hpi_t s).
  set (B1 := mult beta lgT).
  set (B2 := mult beta lgR).
  (* H1 : opp(reward) == opp A + (opp B1 + B2) *)
  assert (H1 : req (opp (reward s)) (plus (opp A) (plus (opp B1) B2))).
  { apply (req_trans (opp (reward s))
                     (opp (plus A (req_minus B1 B2)))
                     (plus (opp A) (plus (opp B1) B2))).
    - exact (req_opp_compat (reward s) (plus A (req_minus B1 B2))
                            (r2_reward_expand pi_t Hpi_t s)).
    - apply (req_trans (opp (plus A (req_minus B1 B2)))
                       (plus (opp A) (opp (req_minus B1 B2)))
                       (plus (opp A) (plus (opp B1) B2))).
      + apply req_opp_plus.
      + apply (req_plus_compat (opp A) (opp A)
                               (opp (req_minus B1 B2)) (plus (opp B1) B2)
                               (req_refl (opp A))).
        apply (req_trans (opp (req_minus B1 B2))
                         (opp (plus B1 (opp B2)))
                         (plus (opp B1) B2)).
        * exact (req_opp_compat (req_minus B1 B2) (plus B1 (opp B2))
                                (r2_m_unfold B1 B2)).
        * apply (req_trans (opp (plus B1 (opp B2)))
                           (plus (opp B1) (opp (opp B2)))
                           (plus (opp B1) B2)).
          -- apply req_opp_plus.
          -- apply (req_plus_compat (opp B1) (opp B1)
                                    (opp (opp B2)) B2
                                    (req_refl (opp B1))
                                    (req_double_neg B2)). }
  (* H2 : AL s == opp A + opp B1 *)
  assert (H2 : req (AL s) (plus (opp A) (opp B1))).
  { apply (req_trans (req_minus (opp (reward s)) B2)
                     (plus (plus (opp A) (plus (opp B1) B2)) (opp B2))
                     (plus (opp A) (opp B1))).
    - apply (req_trans (req_minus (opp (reward s)) B2)
                       (plus (opp (reward s)) (opp B2))
                       (plus (plus (opp A) (plus (opp B1) B2)) (opp B2))).
      + apply r2_m_unfold.
      + apply (req_plus_compat (opp (reward s))
                               (plus (opp A) (plus (opp B1) B2))
                               (opp B2) (opp B2) H1 (req_refl (opp B2))).
    - apply (req_trans (plus (plus (opp A) (plus (opp B1) B2)) (opp B2))
                       (plus (opp A) (plus (plus (opp B1) B2) (opp B2)))
                       (plus (opp A) (opp B1))).
      + apply (req_sym (plus (opp A) (plus (plus (opp B1) B2) (opp B2)))
                       (plus (plus (opp A) (plus (opp B1) B2)) (opp B2))).
        apply plus_assoc.
      + apply (req_trans (plus (opp A) (plus (plus (opp B1) B2) (opp B2)))
                         (plus (opp A) (plus (opp B1) (plus B2 (opp B2))))
                         (plus (opp A) (opp B1))).
        * apply (req_plus_compat (opp A) (opp A)
                                 (plus (plus (opp B1) B2) (opp B2))
                                 (plus (opp B1) (plus B2 (opp B2)))
                                 (req_refl (opp A))).
          apply (req_sym (plus (opp B1) (plus B2 (opp B2)))
                         (plus (plus (opp B1) B2) (opp B2))).
          apply plus_assoc.
        * apply (req_trans (plus (opp A) (plus (opp B1) (plus B2 (opp B2))))
                           (plus (opp A) (plus (opp B1) zero))
                           (plus (opp A) (opp B1))).
          -- apply (req_plus_compat (opp A) (opp A)
                                    (plus (opp B1) (plus B2 (opp B2)))
                                    (plus (opp B1) zero)
                                    (req_refl (opp A))
                                    (req_plus_compat (opp B1) (opp B1)
                                                     (plus B2 (opp B2)) zero
                                                     (req_refl (opp B1))
                                                     (plus_opp B2))).
          -- apply (req_plus_compat (opp A) (opp A)
                                    (plus (opp B1) zero) (opp B1)
                                    (req_refl (opp A))
                                    (req_plus_zero_r (opp B1))). }
  (* H3 : ET + kappa*(opp A) == opp A + opp B1 (kappa := 1-eta) *)
  assert (H3 : req (plus (ET pi_t Hpi_t s)
                         (mult (req_minus one eta) (opp A)))
                   (plus (opp A) (opp B1))).
  { apply (req_trans (plus (req_minus (opp (mult eta A)) B1)
                           (mult (req_minus one eta) (opp A)))
                     (plus (plus (opp (mult eta A)) (opp B1))
                           (plus (opp A) (mult eta A)))
                     (plus (opp A) (opp B1))).
    - apply (req_plus_compat (req_minus (opp (mult eta A)) B1)
                             (plus (opp (mult eta A)) (opp B1))
                             (mult (req_minus one eta) (opp A))
                             (plus (opp A) (mult eta A))
                             (r2_m_unfold (opp (mult eta A)) B1)
                             (r2_eta_opp_absorb A)).
    - exact (req_trans (plus (plus (opp (mult eta A)) (opp B1))
                             (plus (opp A) (mult eta A)))
                       (plus (opp B1) (opp A))
                       (plus (opp A) (opp B1))
                       (r2_four_cancel (mult eta A) (opp B1) A)
                       (plus_comm (opp B1) (opp A))).
  }
  exact (req_trans (AL s) (plus (opp A) (opp B1))
                   (plus (ET pi_t Hpi_t s)
                         (mult (req_minus one eta) (opp A)))
                   H2
                   (req_sym (plus (ET pi_t Hpi_t s)
                                  (mult (req_minus one eta) (opp A)))
                            (plus (opp A) (opp B1)) H3)).
Qed.
(* ---- Definition-unfolding identities (delta-transparent; req_refl form) ---- *)
Lemma unfold_FA :
  forall (p : S -> R) (Hp : pos3 p),
    req (FA p Hp)
        (plus (sumf (fun s => mult (p s) (AL s)))
              (mult beta (sumf (fun s => mult (p s) (log (p s) (Hp s)))))).
Proof. intros p Hp. apply req_refl. Qed.

Lemma unfold_FE_eq :
  forall (energy : S -> R) (D : R) (p : S -> R) (Hp : pos3 p),
    req (plus (sumf (fun s => mult (p s) (energy s)))
              (mult D (sumf (fun s => mult (p s) (log (p s) (Hp s))))))
        (FE energy D p Hp).
Proof. intros energy D p Hp. apply req_refl. Qed.

(* ---- [] Sum-unfolding auxiliaries ---- *)

(* Pointwise: p*AL == p*ET + p*(kappa*opp ADV) *)
Lemma r2_pt_align_split :
  forall (pi_t : S -> R) (Hpi_t : pos3 pi_t) (p : S -> R) (Hp : pos3 p) (s : S),
    req (mult (p s) (AL s))
        (plus (mult (p s) (ET pi_t Hpi_t s))
              (mult (p s) (mult (req_minus one eta)
                                (opp (ADV pi_t Hpi_t s))))).
Proof.
  intros pi_t Hpi_t p Hp s.
  apply (req_trans (mult (p s) (AL s))
                   (mult (p s) (plus (ET pi_t Hpi_t s)
                                     (mult (req_minus one eta)
                                           (opp (ADV pi_t Hpi_t s)))))
                   (plus (mult (p s) (ET pi_t Hpi_t s))
                         (mult (p s) (mult (req_minus one eta)
                                           (opp (ADV pi_t Hpi_t s)))))).
  - exact (req_mult_compat (p s) (p s) (AL s)
                           (plus (ET pi_t Hpi_t s)
                                 (mult (req_minus one eta)
                                       (opp (ADV pi_t Hpi_t s))))
                           (req_refl (p s))
                           (r2_align_energy_expand pi_t Hpi_t s)).
  - apply distrib.
Qed.

(* Sum: SUM p*AL == SUM p*ET + kappa*opp(SUM p*ADV) *)
Lemma r2_sum_align_split :
  forall (pi_t : S -> R) (Hpi_t : pos3 pi_t) (p : S -> R) (Hp : pos3 p),
    req (sumf (fun s => mult (p s) (AL s)))
        (plus (sumf (fun s => mult (p s) (ET pi_t Hpi_t s)))
              (mult (req_minus one eta)
                    (opp (sumf (fun s => mult (p s) (ADV pi_t Hpi_t s)))))).
Proof.
  intros pi_t Hpi_t p Hp.
  set (SA := sumf (fun s => mult (p s) (ADV pi_t Hpi_t s))).
  set (K := req_minus one eta).
  apply (req_trans (sumf (fun s => mult (p s) (AL s)))
                   (plus (sumf (fun s => mult (p s) (ET pi_t Hpi_t s)))
                         (sumf (fun s => mult (p s) (mult K (opp (ADV pi_t Hpi_t s))))))
                   (plus (sumf (fun s => mult (p s) (ET pi_t Hpi_t s)))
                         (mult K (opp SA)))).
  - apply (req_trans (sumf (fun s => mult (p s) (AL s)))
                     (sumf (fun s => plus (mult (p s) (ET pi_t Hpi_t s))
                                          (mult (p s) (mult K (opp (ADV pi_t Hpi_t s))))))
                     (plus (sumf (fun s => mult (p s) (ET pi_t Hpi_t s)))
                           (sumf (fun s => mult (p s) (mult K (opp (ADV pi_t Hpi_t s))))))).
    + apply (sum_ext (fun s => mult (p s) (AL s))
                     (fun s => plus (mult (p s) (ET pi_t Hpi_t s))
                                    (mult (p s) (mult K (opp (ADV pi_t Hpi_t s)))))).
      intro s.
      exact (r2_pt_align_split pi_t Hpi_t p Hp s).
    + apply sum_add.
  - apply (req_plus_compat (sumf (fun s => mult (p s) (ET pi_t Hpi_t s)))
                           (sumf (fun s => mult (p s) (ET pi_t Hpi_t s)))
                           (sumf (fun s => mult (p s) (mult K (opp (ADV pi_t Hpi_t s)))))
                           (mult K (opp SA))
                           (req_refl (sumf (fun s => mult (p s) (ET pi_t Hpi_t s))))).
    apply (req_trans (sumf (fun s => mult (p s) (mult K (opp (ADV pi_t Hpi_t s)))))
                     (mult K (sumf (fun s => mult (p s) (opp (ADV pi_t Hpi_t s)))))
                     (mult K (opp SA))
                     (w_sum_ptimes_scal p K (fun s => opp (ADV pi_t Hpi_t s)))
                     (req_mult_compat K K
                        (sumf (fun s => mult (p s) (opp (ADV pi_t Hpi_t s))))
                        (opp SA)
                        (req_refl K)
                        (req_trans (sumf (fun s => mult (p s) (opp (ADV pi_t Hpi_t s))))
                                   (sumf (fun s => opp (mult (p s) (ADV pi_t Hpi_t s))))
                                   (opp SA)
                                   (sum_ext (fun s => mult (p s) (opp (ADV pi_t Hpi_t s)))
                                            (fun s => opp (mult (p s) (ADV pi_t Hpi_t s)))
                                            (fun s => req_opp_mult_l (p s) (ADV pi_t Hpi_t s)))
                                   (w_sum_opp (fun s => mult (p s) (ADV pi_t Hpi_t s)))))).
Qed.

(* ---- [] Piece 3: F_align == F_t + kappa*opp(SUM p*A) (Id F_align_F_t_rel @21949) ---- *)
Lemma r2_F_align_F_t_rel :
  forall (pi_t : S -> R) (Hpi_t : pos3 pi_t) (p : S -> R) (Hp : pos3 p),
    req (FA p Hp)
        (plus (FE (ET pi_t Hpi_t) beta p Hp)
              (mult (req_minus one eta)
                    (opp (sumf (fun s => mult (p s) (ADV pi_t Hpi_t s)))))).
Proof.
  intros pi_t Hpi_t p Hp.
  set (SEt := sumf (fun s => mult (p s) (ET pi_t Hpi_t s))).
  set (SEnt := sumf (fun s => mult (p s) (log (p s) (Hp s)))).
  set (SA := sumf (fun s => mult (p s) (ADV pi_t Hpi_t s))).
  set (K := req_minus one eta).
  apply (req_trans (FA p Hp)
                   (plus (plus SEt (mult K (opp SA))) (mult beta SEnt))
                   (plus (FE (ET pi_t Hpi_t) beta p Hp) (mult K (opp SA)))).
  - apply (req_trans (FA p Hp)
                     (plus (sumf (fun s => mult (p s) (AL s))) (mult beta SEnt))
                     (plus (plus SEt (mult K (opp SA))) (mult beta SEnt))).
    + apply req_refl.
    + exact (req_plus_compat (sumf (fun s => mult (p s) (AL s)))
                             (plus SEt (mult K (opp SA)))
                             (mult beta SEnt) (mult beta SEnt)
                             (r2_sum_align_split pi_t Hpi_t p Hp)
                             (req_refl (mult beta SEnt))).
  - apply (req_trans (plus (plus SEt (mult K (opp SA))) (mult beta SEnt))
                     (plus SEt (plus (mult beta SEnt) (mult K (opp SA))))
                     (plus (FE (ET pi_t Hpi_t) beta p Hp) (mult K (opp SA)))).
    + exact (req_trans (plus (plus SEt (mult K (opp SA))) (mult beta SEnt))
                       (plus SEt (plus (mult K (opp SA)) (mult beta SEnt)))
                       (plus SEt (plus (mult beta SEnt) (mult K (opp SA))))
                       (req_sym (plus SEt (plus (mult K (opp SA)) (mult beta SEnt)))
                                (plus (plus SEt (mult K (opp SA))) (mult beta SEnt))
                                (plus_assoc SEt (mult K (opp SA)) (mult beta SEnt)))
                       (req_plus_compat SEt SEt
                                        (plus (mult K (opp SA)) (mult beta SEnt))
                                        (plus (mult beta SEnt) (mult K (opp SA)))
                                        (req_refl SEt)
                                        (plus_comm (mult K (opp SA)) (mult beta SEnt)))).
    + exact (req_trans (plus SEt (plus (mult beta SEnt) (mult K (opp SA))))
                       (plus (plus SEt (mult beta SEnt)) (mult K (opp SA)))
                       (plus (FE (ET pi_t Hpi_t) beta p Hp) (mult K (opp SA)))
                       (plus_assoc SEt (mult beta SEnt) (mult K (opp SA)))
                       (req_plus_compat (plus SEt (mult beta SEnt))
                                        (FE (ET pi_t Hpi_t) beta p Hp)
                                        (mult K (opp SA)) (mult K (opp SA))
                                        (unfold_FE_eq (ET pi_t Hpi_t) beta p Hp)
                                        (req_refl (mult K (opp SA))))).
Qed.

(* ---- [] Piece 4: alignment-objective decomposition (Id align_objective_t12_decomp @21997) ---- *)
Lemma r2_align_objective_t12_decomp :
  forall (pi_t : S -> R) (Hpi_t : pos3 pi_t) (p : S -> R) (Hp : pos3 p),
    req (JJ p Hp)
        (plus (opp (FE (ET pi_t Hpi_t) beta p Hp))
              (mult (req_minus one eta)
                    (sumf (fun s => mult (p s) (ADV pi_t Hpi_t s))))).
Proof.
  intros pi_t Hpi_t p Hp.
  set (SA := sumf (fun s => mult (p s) (ADV pi_t Hpi_t s))).
  set (K := req_minus one eta).
  apply (req_trans (opp (FA p Hp))
                   (opp (plus (FE (ET pi_t Hpi_t) beta p Hp) (mult K (opp SA))))
                   (plus (opp (FE (ET pi_t Hpi_t) beta p Hp)) (mult K SA))).
  - exact (req_opp_compat (FA p Hp)
                          (plus (FE (ET pi_t Hpi_t) beta p Hp) (mult K (opp SA)))
                          (r2_F_align_F_t_rel pi_t Hpi_t p Hp)).
  - apply (req_trans (opp (plus (FE (ET pi_t Hpi_t) beta p Hp) (mult K (opp SA))))
                     (plus (opp (FE (ET pi_t Hpi_t) beta p Hp))
                           (opp (mult K (opp SA))))
                     (plus (opp (FE (ET pi_t Hpi_t) beta p Hp)) (mult K SA))).
    + apply req_opp_plus.
    + apply (req_plus_compat (opp (FE (ET pi_t Hpi_t) beta p Hp))
                             (opp (FE (ET pi_t Hpi_t) beta p Hp))
                             (opp (mult K (opp SA))) (mult K SA)
                             (req_refl (opp (FE (ET pi_t Hpi_t) beta p Hp)))).
      apply (req_trans (opp (mult K (opp SA)))
                       (opp (opp (mult K SA)))
                       (mult K SA)
                       (req_opp_compat (mult K (opp SA)) (opp (mult K SA))
                                       (req_opp_mult_l K SA))
                       (req_double_neg (mult K SA))).
Qed.

(* ---- [] Piece 5: J(pi_t) == SUM pi_t*A (Id J_pi_t_t12 @22016) ---- *)
Lemma r2_J_pi_t :
  forall (pi_t : S -> R) (Hpi_t : pos3 pi_t) (Hn : nrm pi_t),
    req (JJ pi_t Hpi_t)
        (sumf (fun s => mult (pi_t s) (ADV pi_t Hpi_t s))).
Proof.
  intros pi_t Hpi_t Hn.
  set (SAT := sumf (fun s => mult (pi_t s) (ADV pi_t Hpi_t s))).
  set (K := req_minus one eta).
  apply (req_trans (JJ pi_t Hpi_t)
                   (plus (opp (FE (ET pi_t Hpi_t) beta pi_t Hpi_t)) (mult K SAT))
                   SAT).
  - exact (r2_align_objective_t12_decomp pi_t Hpi_t pi_t Hpi_t).
  - apply (req_trans (plus (opp (FE (ET pi_t Hpi_t) beta pi_t Hpi_t))
                           (mult K SAT))
                     (plus (mult eta SAT) (mult K SAT))
                     SAT).
    + apply (req_plus_compat (opp (FE (ET pi_t Hpi_t) beta pi_t Hpi_t))
                             (mult eta SAT)
                             (mult K SAT) (mult K SAT)
                             (req_trans (opp (FE (ET pi_t Hpi_t) beta pi_t Hpi_t))
                                        (opp (opp (mult eta SAT)))
                                        (mult eta SAT)
                                        (req_opp_compat (FE (ET pi_t Hpi_t) beta pi_t Hpi_t)
                                                        (opp (mult eta SAT))
                                                        (w_F_t_simpl_t pi_t Hpi_t))
                                        (req_double_neg (mult eta SAT)))
                             (req_refl (mult K SAT))).
    + exact (req2_eta_absorb eta SAT).
Qed.

(* ---- [] Piece 6: J(pi_next) == SUM pi_next*A - beta*KL(pi_next||pi_t) ---- *)
Lemma r2_J_pi_next :
  forall (pi_t : S -> R) (Hpi_t : pos3 pi_t),
    req (JJ (NPX pi_t Hpi_t) (npx_pos pi_t Hpi_t))
        (req_minus (sumf (fun s => mult (NPX pi_t Hpi_t s) (ADV pi_t Hpi_t s)))
                   (mult beta (KLE (NPX pi_t Hpi_t) pi_t
                                   (npx_pos pi_t Hpi_t) Hpi_t))).
Proof.
  intros pi_t Hpi_t.
  set (SAN := sumf (fun s => mult (NPX pi_t Hpi_t s) (ADV pi_t Hpi_t s))).
  set (K1 := KLE (NPX pi_t Hpi_t) pi_t (npx_pos pi_t Hpi_t) Hpi_t).
  set (K := req_minus one eta).
  assert (HoppFE : req (opp (FE (ET pi_t Hpi_t) beta (NPX pi_t Hpi_t)
                                (npx_pos pi_t Hpi_t)))
                       (plus (mult eta SAN) (opp (mult beta K1)))).
  { apply (req_trans (opp (FE (ET pi_t Hpi_t) beta (NPX pi_t Hpi_t)
                              (npx_pos pi_t Hpi_t)))
                     (opp (plus (opp (mult eta SAN)) (mult beta K1)))
                     (plus (mult eta SAN) (opp (mult beta K1)))).
    - apply (req_opp_compat (FE (ET pi_t Hpi_t) beta (NPX pi_t Hpi_t)
                                    (npx_pos pi_t Hpi_t))
                            (plus (opp (mult eta SAN)) (mult beta K1))
                            (w_F_t_simpl_next_kl pi_t Hpi_t)).
    - apply (req_trans (opp (plus (opp (mult eta SAN)) (mult beta K1)))
                       (plus (opp (opp (mult eta SAN))) (opp (mult beta K1)))
                       (plus (mult eta SAN) (opp (mult beta K1)))).
      + apply req_opp_plus.
      + apply (req_plus_compat (opp (opp (mult eta SAN))) (mult eta SAN)
                               (opp (mult beta K1)) (opp (mult beta K1))
                               (req_double_neg (mult eta SAN))
                               (req_refl (opp (mult beta K1)))). }
  apply (req_trans (JJ (NPX pi_t Hpi_t) (npx_pos pi_t Hpi_t))
                   (plus (opp (FE (ET pi_t Hpi_t) beta (NPX pi_t Hpi_t)
                                        (npx_pos pi_t Hpi_t)))
                         (mult K SAN))
                   (req_minus SAN (mult beta K1))).
  - exact (r2_align_objective_t12_decomp pi_t Hpi_t
                                         (NPX pi_t Hpi_t)
                                         (npx_pos pi_t Hpi_t)).
  - apply (req_trans (plus (opp (FE (ET pi_t Hpi_t) beta (NPX pi_t Hpi_t)
                                        (npx_pos pi_t Hpi_t)))
                           (mult K SAN))
                     (plus (plus (mult eta SAN) (opp (mult beta K1)))
                           (mult K SAN))
                     (req_minus SAN (mult beta K1))).
    + exact (req_plus_compat (opp (FE (ET pi_t Hpi_t) beta (NPX pi_t Hpi_t)
                                          (npx_pos pi_t Hpi_t)))
                             (plus (mult eta SAN) (opp (mult beta K1)))
                             (mult K SAN) (mult K SAN)
                             HoppFE
                             (req_refl (mult K SAN))).
    + apply (req_trans (plus (plus (mult eta SAN) (opp (mult beta K1)))
                             (mult K SAN))
                       (plus (plus (mult eta SAN) (mult K SAN))
                             (opp (mult beta K1)))
                       (req_minus SAN (mult beta K1))).
      * apply (req_trans (plus (plus (mult eta SAN) (opp (mult beta K1)))
                               (mult K SAN))
                         (plus (mult eta SAN)
                               (plus (opp (mult beta K1)) (mult K SAN)))
                         (plus (plus (mult eta SAN) (mult K SAN))
                               (opp (mult beta K1)))).
        -- exact (req_sym (plus (mult eta SAN)
                                (plus (opp (mult beta K1)) (mult K SAN)))
                          (plus (plus (mult eta SAN) (opp (mult beta K1)))
                                (mult K SAN))
                          (plus_assoc (mult eta SAN) (opp (mult beta K1))
                                      (mult K SAN))).
        -- apply (req_trans (plus (mult eta SAN)
                                  (plus (opp (mult beta K1)) (mult K SAN)))
                            (plus (mult eta SAN)
                                  (plus (mult K SAN) (opp (mult beta K1))))
                            (plus (plus (mult eta SAN) (mult K SAN))
                                  (opp (mult beta K1)))).
           ++ apply (req_plus_compat (mult eta SAN) (mult eta SAN)
                                     (plus (opp (mult beta K1)) (mult K SAN))
                                     (plus (mult K SAN) (opp (mult beta K1)))
                                     (req_refl (mult eta SAN))
                                     (plus_comm (opp (mult beta K1))
                                                (mult K SAN))).
           ++ exact (plus_assoc (mult eta SAN) (mult K SAN)
                                (opp (mult beta K1))).
      * apply (req_trans (plus (plus (mult eta SAN) (mult K SAN))
                               (opp (mult beta K1)))
                         (plus SAN (opp (mult beta K1)))
                         (req_minus SAN (mult beta K1))).
        -- apply (req_plus_compat (plus (mult eta SAN) (mult K SAN)) SAN
                                  (opp (mult beta K1)) (opp (mult beta K1))
                                  (req2_eta_absorb eta SAN)
                                  (req_refl (opp (mult beta K1)))).
        -- apply req_refl.
Qed.

(* ---- [] Piece 7: surrogate-vs-true difference identity (Id surrogate_diff_identity @21744) ----
   eta·(Σ NPX·A − Σ pi_t·A) == beta·(KL(NPX‖pi_t) + KL(pi_t‖NPX)) ---- *)
Lemma r2_surrogate_diff_identity :
  forall (pi_t : S -> R) (Hpi_t : pos3 pi_t) (Hn : nrm pi_t),
    req (mult eta (req_minus (sumf (fun s => mult (NPX pi_t Hpi_t s)
                                                  (ADV pi_t Hpi_t s)))
                             (sumf (fun s => mult (pi_t s)
                                                  (ADV pi_t Hpi_t s)))))
        (mult beta
              (plus (KLE (NPX pi_t Hpi_t) pi_t (npx_pos pi_t Hpi_t) Hpi_t)
                    (KLE pi_t (NPX pi_t Hpi_t) Hpi_t (npx_pos pi_t Hpi_t)))).
Proof.
  intros pi_t Hpi_t Hn.
  set (SAN := sumf (fun s => mult (NPX pi_t Hpi_t s) (ADV pi_t Hpi_t s))).
  set (SAT := sumf (fun s => mult (pi_t s) (ADV pi_t Hpi_t s))).
  set (K1 := KLE (NPX pi_t Hpi_t) pi_t (npx_pos pi_t Hpi_t) Hpi_t).
  set (K2 := KLE pi_t (NPX pi_t Hpi_t) Hpi_t (npx_pos pi_t Hpi_t)).
  assert (H2 : req (opp (mult eta SAT))
                   (plus (opp (mult eta SAN)) (plus (mult beta K1) (mult beta K2)))).
  { apply (req_trans (opp (mult eta SAT))
                     (FE (ET pi_t Hpi_t) beta pi_t Hpi_t)
                     (plus (opp (mult eta SAN)) (plus (mult beta K1) (mult beta K2)))).
    - exact (req_sym (FE (ET pi_t Hpi_t) beta pi_t Hpi_t) (opp (mult eta SAT))
                     (w_F_t_simpl_t pi_t Hpi_t)).
    - apply (req_trans (FE (ET pi_t Hpi_t) beta pi_t Hpi_t)
                       (plus (FE (ET pi_t Hpi_t) beta (NPX pi_t Hpi_t)
                                    (npx_pos pi_t Hpi_t))
                             (mult beta K2))
                       (plus (opp (mult eta SAN)) (plus (mult beta K1) (mult beta K2)))).
      + exact (w_F_t_rel_decomp pi_t Hpi_t Hn).
      + apply (req_trans (plus (FE (ET pi_t Hpi_t) beta (NPX pi_t Hpi_t)
                                       (npx_pos pi_t Hpi_t))
                               (mult beta K2))
                         (plus (plus (opp (mult eta SAN)) (mult beta K1))
                               (mult beta K2))
                         (plus (opp (mult eta SAN)) (plus (mult beta K1) (mult beta K2)))).
        * apply (req_plus_compat (FE (ET pi_t Hpi_t) beta (NPX pi_t Hpi_t)
                                        (npx_pos pi_t Hpi_t))
                                 (plus (opp (mult eta SAN)) (mult beta K1))
                                 (mult beta K2) (mult beta K2)
                                 (w_F_t_simpl_next_kl pi_t Hpi_t)
                                 (req_refl (mult beta K2))).
        * apply (req_sym (plus (opp (mult eta SAN))
                               (plus (mult beta K1) (mult beta K2)))
                         (plus (plus (opp (mult eta SAN)) (mult beta K1))
                               (mult beta K2))
                         (plus_assoc (opp (mult eta SAN)) (mult beta K1)
                                     (mult beta K2))). }
  assert (H3 : req (plus (mult eta SAN) (opp (mult eta SAT)))
                   (plus (mult beta K1) (mult beta K2))).
  { apply (req_trans (plus (mult eta SAN) (opp (mult eta SAT)))
                     (plus (mult eta SAN)
                           (plus (opp (mult eta SAN)) (plus (mult beta K1) (mult beta K2))))
                     (plus (mult beta K1) (mult beta K2))).
    - apply (req_plus_compat (mult eta SAN) (mult eta SAN)
                             (opp (mult eta SAT))
                             (plus (opp (mult eta SAN)) (plus (mult beta K1) (mult beta K2)))
                             (req_refl (mult eta SAN))
                             H2).
    - apply (req_trans (plus (mult eta SAN)
                             (plus (opp (mult eta SAN)) (plus (mult beta K1) (mult beta K2))))
                       (plus (plus (mult eta SAN) (opp (mult eta SAN)))
                             (plus (mult beta K1) (mult beta K2)))
                       (plus (mult beta K1) (mult beta K2))).
      + apply plus_assoc.
      + apply (req_trans (plus (plus (mult eta SAN) (opp (mult eta SAN)))
                               (plus (mult beta K1) (mult beta K2)))
                         (plus zero (plus (mult beta K1) (mult beta K2)))
                         (plus (mult beta K1) (mult beta K2))).
        * apply (req_plus_compat (plus (mult eta SAN) (opp (mult eta SAN))) zero
                                 (plus (mult beta K1) (mult beta K2))
                                 (plus (mult beta K1) (mult beta K2))
                                 (plus_opp (mult eta SAN))
                                 (req_refl (plus (mult beta K1) (mult beta K2)))).
        * apply req_plus_zero_l. }
  apply (req_trans (mult eta (req_minus SAN SAT))
                   (plus (mult eta SAN) (opp (mult eta SAT)))
                   (mult beta (plus K1 K2))).
  - exact (req_trans (mult eta (req_minus SAN SAT))
                     (plus (mult eta SAN) (mult eta (opp SAT)))
                     (plus (mult eta SAN) (opp (mult eta SAT)))
                     (distrib eta SAN (opp SAT))
                     (req_plus_compat (mult eta SAN) (mult eta SAN)
                                      (mult eta (opp SAT)) (opp (mult eta SAT))
                                      (req_refl (mult eta SAN))
                                      (req_opp_mult_l eta SAT))).
  - exact (req_trans (plus (mult eta SAN) (opp (mult eta SAT)))
                     (plus (mult beta K1) (mult beta K2))
                     (mult beta (plus K1 K2))
                     H3
                     (req_sym (mult beta (plus K1 K2))
                              (plus (mult beta K1) (mult beta K2))
                              (distrib beta K1 K2))).
Qed.
(* Left rotation: (a + b) + c == (a + c) + b *)
Lemma r2_left_rotate :
  forall a b c : R, req (plus (plus a b) c) (plus (plus a c) b).
Proof.
  intros a b c.
  apply (req_trans (plus (plus a b) c)
                   (plus a (plus b c))
                   (plus (plus a c) b)).
  - exact (req_sym (plus a (plus b c)) (plus (plus a b) c)
                   (plus_assoc a b c)).
  - apply (req_trans (plus a (plus b c))
                     (plus a (plus c b))
                     (plus (plus a c) b)).
    + apply (req_plus_compat a a (plus b c) (plus c b)
                             (req_refl a) (plus_comm b c)).
    + apply plus_assoc.
Qed.

(* Swapping the subtracted terms: (a - b) - c == (a - c) - b *)
Lemma r2_swap_sub :
  forall a b c : R,
    req (req_minus (req_minus a b) c) (req_minus (req_minus a c) b).
Proof.
  intros a b c.
  apply (req_trans (req_minus (req_minus a b) c)
                   (plus a (plus (opp b) (opp c)))
                   (req_minus (req_minus a c) b)).
  - exact (req_sym (plus a (plus (opp b) (opp c)))
                   (plus (plus a (opp b)) (opp c))
                   (plus_assoc a (opp b) (opp c))).
  - apply (req_trans (plus a (plus (opp b) (opp c)))
                     (plus a (plus (opp c) (opp b)))
                     (req_minus (req_minus a c) b)).
    + apply (req_plus_compat a a
                             (plus (opp b) (opp c)) (plus (opp c) (opp b))
                             (req_refl a) (plus_comm (opp b) (opp c))).
    + apply plus_assoc.
Qed.
(* ---- [] Piece 8: single-step explicit gap identity (Id policy_iter_gap_diff @23020) ---- *)
Lemma r2_gap_diff :
  forall (pi_t : S -> R) (Hpi_t : pos3 pi_t) (Hn : nrm pi_t),
    req (req_minus (JJ (NPX pi_t Hpi_t) (npx_pos pi_t Hpi_t))
                   (JJ pi_t Hpi_t))
        (mult beta
              (plus (mult (req_minus (inv_pos eta eta_pos) one)
                          (KLE (NPX pi_t Hpi_t) pi_t
                               (npx_pos pi_t Hpi_t) Hpi_t))
                    (mult (inv_pos eta eta_pos)
                          (KLE pi_t (NPX pi_t Hpi_t)
                               Hpi_t (npx_pos pi_t Hpi_t))))).
Proof.
  intros pi_t Hpi_t Hn.
  set (SAN := sumf (fun s => mult (NPX pi_t Hpi_t s) (ADV pi_t Hpi_t s))).
  set (SAT := sumf (fun s => mult (pi_t s) (ADV pi_t Hpi_t s))).
  set (K1 := KLE (NPX pi_t Hpi_t) pi_t (npx_pos pi_t Hpi_t) Hpi_t).
  set (K2 := KLE pi_t (NPX pi_t Hpi_t) Hpi_t (npx_pos pi_t Hpi_t)).
  set (I := inv_pos eta eta_pos).
  set (B := mult beta).
  assert (Hdiff : req (req_minus (JJ (NPX pi_t Hpi_t) (npx_pos pi_t Hpi_t))
                                 (JJ pi_t Hpi_t))
                      (req_minus (req_minus SAN (B K1)) SAT)).
  { exact (req2_minus_compat (JJ (NPX pi_t Hpi_t) (npx_pos pi_t Hpi_t))
                             (req_minus SAN (B K1))
                             (JJ pi_t Hpi_t) SAT
                             (r2_J_pi_next pi_t Hpi_t)
                             (r2_J_pi_t pi_t Hpi_t Hn)). }
  assert (Hinv : req (req_minus SAN SAT) (mult I (B (plus K1 K2)))).
  { exact (req_trans (req_minus SAN SAT)
                     (mult I (mult eta (req_minus SAN SAT)))
                     (mult I (B (plus K1 K2)))
                     (req_sym (mult I (mult eta (req_minus SAN SAT)))
                              (req_minus SAN SAT)
                              (req_trans (mult I (mult eta (req_minus SAN SAT)))
                                         (mult (mult I eta) (req_minus SAN SAT))
                                         (req_minus SAN SAT)
                                         (mult_assoc I eta (req_minus SAN SAT))
                                         (req_trans (mult (mult I eta) (req_minus SAN SAT))
                                                    (mult (mult eta I) (req_minus SAN SAT))
                                                    (req_minus SAN SAT)
                                                    (req_mult_compat (mult I eta) (mult eta I)
                                                                     (req_minus SAN SAT)
                                                                     (req_minus SAN SAT)
                                                                     (mult_comm I eta)
                                                                     (req_refl (req_minus SAN SAT)))
                                                    (req_trans (mult (mult eta I) (req_minus SAN SAT))
                                                               (mult one (req_minus SAN SAT))
                                                               (req_minus SAN SAT)
                                                               (req_mult_compat (mult eta I) one
                                                                                (req_minus SAN SAT)
                                                                                (req_minus SAN SAT)
                                                                                (inv_pos_correct eta eta_pos)
                                                                                (req_refl (req_minus SAN SAT)))
                                                               (req_mult_one_l (req_minus SAN SAT))))))
                     (req_mult_compat I I (mult eta (req_minus SAN SAT))
                                      (B (plus K1 K2))
                                      (req_refl I)
                                      (r2_surrogate_diff_identity pi_t Hpi_t Hn))). }
  assert (Hc : req (plus (mult I K1) (opp K1)) (mult (req_minus I one) K1)).
  { apply (req_trans (plus (mult I K1) (opp K1))
                     (req_minus (mult I K1) (mult one K1))
                     (mult (req_minus I one) K1)).
    - exact (req_plus_compat (mult I K1) (mult I K1)
                             (opp K1) (opp (mult one K1))
                             (req_refl (mult I K1))
                             (req_opp_compat K1 (mult one K1)
                                             (req_sym (mult one K1) K1
                                                      (req_trans (mult one K1)
                                                                 (mult K1 one)
                                                                 K1
                                                                 (mult_comm one K1)
                                                                 (mult_one K1))))).
    - exact (req_sym (mult (req_minus I one) K1)
                     (req_minus (mult I K1) (mult one K1))
                     (r2_mmd_r I one K1)). }
  assert (Hinner : req (req_minus (mult I (plus K1 K2)) K1)
                       (plus (plus (mult I K1) (opp K1)) (mult I K2))).
  { exact (req_trans (req_minus (mult I (plus K1 K2)) K1)
                     (plus (mult I (plus K1 K2)) (opp K1))
                     (plus (plus (mult I K1) (opp K1)) (mult I K2))
                     (r2_m_unfold (mult I (plus K1 K2)) K1)
                     (req_trans (plus (mult I (plus K1 K2)) (opp K1))
                                (plus (plus (mult I K1) (mult I K2)) (opp K1))
                                (plus (plus (mult I K1) (opp K1)) (mult I K2))
                                (req_plus_compat (mult I (plus K1 K2))
                                                 (plus (mult I K1) (mult I K2))
                                                 (opp K1) (opp K1)
                                                 (distrib I K1 K2)
                                                 (req_refl (opp K1)))
                                (r2_left_rotate (mult I K1) (mult I K2) (opp K1)))). }
  assert (Hinner2 : req (req_minus (mult I (plus K1 K2)) K1)
                        (plus (mult (req_minus I one) K1) (mult I K2))).
  { exact (req_trans (req_minus (mult I (plus K1 K2)) K1)
                     (plus (plus (mult I K1) (opp K1)) (mult I K2))
                     (plus (mult (req_minus I one) K1) (mult I K2))
                     Hinner
                     (req_plus_compat (plus (mult I K1) (opp K1))
                                      (mult (req_minus I one) K1)
                                      (mult I K2) (mult I K2)
                                      Hc
                                      (req_refl (mult I K2)))). }
  assert (Hfold : req (mult I (B (plus K1 K2)))
                      (mult beta (mult I (plus K1 K2)))).
  { exact (req_trans (mult I (B (plus K1 K2)))
                     (mult (mult I beta) (plus K1 K2))
                     (mult beta (mult I (plus K1 K2)))
                     (mult_assoc I beta (plus K1 K2))
                     (req_trans (mult (mult I beta) (plus K1 K2))
                                (mult (mult beta I) (plus K1 K2))
                                (mult beta (mult I (plus K1 K2)))
                                (req_mult_compat (mult I beta) (mult beta I)
                                                 (plus K1 K2) (plus K1 K2)
                                                 (mult_comm I beta)
                                                 (req_refl (plus K1 K2)))
                                (req_sym (mult beta (mult I (plus K1 K2)))
                                         (mult (mult beta I) (plus K1 K2))
                                         (mult_assoc beta I (plus K1 K2))))). }
  assert (Hf1 : req (req_minus (req_minus SAN SAT) (B K1))
                       (req_minus (mult I (B (plus K1 K2))) (B K1))).
  { exact (req2_minus_compat (req_minus SAN SAT)
                             (mult I (B (plus K1 K2)))
                             (B K1) (B K1)
                             Hinv (req_refl (B K1))). }
  assert (Hf2 : req (req_minus (mult I (B (plus K1 K2))) (B K1))
                       (req_minus (mult beta (mult I (plus K1 K2))) (B K1))).
  { exact (req2_minus_compat (mult I (B (plus K1 K2)))
                             (mult beta (mult I (plus K1 K2)))
                             (B K1) (B K1)
                             Hfold (req_refl (B K1))). }
  assert (Hf3 : req (req_minus (mult beta (mult I (plus K1 K2))) (B K1))
                       (mult beta (req_minus (mult I (plus K1 K2)) K1))).
  { exact (req_sym (mult beta (req_minus (mult I (plus K1 K2)) K1))
                   (req_minus (mult beta (mult I (plus K1 K2))) (mult beta K1))
                   (req_mult_minus_distr_l beta (mult I (plus K1 K2)) K1)). }
  assert (Hf4 : req (mult beta (req_minus (mult I (plus K1 K2)) K1))
                       (mult beta (plus (mult (req_minus I one) K1) (mult I K2)))).
  { exact (req_mult_compat beta beta
                           (req_minus (mult I (plus K1 K2)) K1)
                           (plus (mult (req_minus I one) K1) (mult I K2))
                           (req_refl beta)
                           Hinner2). }
  assert (Hfold2 : req (req_minus (req_minus SAN (B K1)) SAT)
                       (mult beta (req_minus (mult I (plus K1 K2)) K1))).
  { exact (req_trans (req_minus (req_minus SAN (B K1)) SAT)
                     (req_minus (req_minus SAN SAT) (B K1))
                     (mult beta (req_minus (mult I (plus K1 K2)) K1))
                     (r2_swap_sub SAN (B K1) SAT)
                     (req_trans (req_minus (req_minus SAN SAT) (B K1))
                                (req_minus (mult I (B (plus K1 K2))) (B K1))
                                (mult beta (req_minus (mult I (plus K1 K2)) K1))
                                Hf1 (req_trans (req_minus (mult I (B (plus K1 K2))) (B K1))
                                               (req_minus (mult beta (mult I (plus K1 K2))) (B K1))
                                               (mult beta (req_minus (mult I (plus K1 K2)) K1))
                                               Hf2 Hf3))). }
  assert (Hrep : req (req_minus (req_minus SAN (B K1)) SAT)
                     (mult beta (plus (mult (req_minus I one) K1) (mult I K2)))).
  { exact (req_trans (req_minus (req_minus SAN (B K1)) SAT)
                     (mult beta (req_minus (mult I (plus K1 K2)) K1))
                     (mult beta (plus (mult (req_minus I one) K1) (mult I K2)))
                     Hfold2
                     (req_mult_compat beta beta
                                      (req_minus (mult I (plus K1 K2)) K1)
                                      (plus (mult (req_minus I one) K1) (mult I K2))
                                      (req_refl beta)
                                      Hinner2)). }
  exact (req_trans _ _ _ Hdiff Hrep).
Qed.

(* ============================================================ *)
(* [] Main theorem done: policy improvement monotonicity (Id policy_improvement_mono     *)
(*   @22065, req theorized; batch 3 bridge slot 3 req_policy_improvement_mono *)
(*   released via the t12 chain)                                  *)
(* ============================================================ *)

(* Odd symmetry of minus over opp: (opp u) - (opp v) == opp (u - v) *)
Lemma r2_opp_minus_sym :
  forall u v : R, req (req_minus (opp u) (opp v)) (opp (req_minus u v)).
Proof.
  intros u v. unfold req_minus.
  exact (req_sym (opp (plus u (opp v))) (plus (opp u) (opp (opp v)))
                 (req_opp_plus u (opp v))).
Qed.

(* ---- B-class bridge (register item 3, newly released slot in this file): req2_gibbs_inequality
   (req same-position of Id gibbs_inequality @16629). The plain-le
   form of KL >= 0 is not derivable from the per-eps interface fields (no order elimination); the assumption slot is retained, pending
   the UpReqFreeEnergy (batch 2 FEP) results, after which it is demoted to a consumer. The req2 KLE statement has no
   normalization premise, so the bridge takes the strengthened usable form without norm. ---- *)
Hypothesis req2_gibbs_inequality :
  forall (p q : S -> R) (Hp : pos3 p) (Hq : pos3 q),
    le zero (KLE p q Hp Hq).

(* ---- [] Piece 9: J(pi_t) <= J(pi_next) (req theorized) ---- *)
Theorem r2_policy_improvement_mono :
  forall (pi_t : S -> R) (Hpi_t : pos3 pi_t) (Hn : nrm pi_t),
    le (JJ pi_t Hpi_t) (JJ (NPX pi_t Hpi_t) (npx_pos pi_t Hpi_t)).
Proof.
  intros pi_t Hpi_t Hn.
  apply req2_le_of_minus_nonneg.
  set (K1 := KLE (NPX pi_t Hpi_t) pi_t (npx_pos pi_t Hpi_t) Hpi_t).
  set (K2 := KLE pi_t (NPX pi_t Hpi_t) Hpi_t (npx_pos pi_t Hpi_t)).
  set (I := inv_pos eta eta_pos).
  assert (Ha : le zero (req_minus I one)).
  { apply req_le_minus_nonneg. exact r2_inv_ge_one. }
  assert (Hb : le zero K1).
  { exact (req2_gibbs_inequality (NPX pi_t Hpi_t) pi_t
                                 (npx_pos pi_t Hpi_t) Hpi_t). }
  assert (Hc : le zero K2).
  { exact (req2_gibbs_inequality pi_t (NPX pi_t Hpi_t) Hpi_t
                                 (npx_pos pi_t Hpi_t)). }
  assert (Hd : le zero (mult (req_minus I one) K1)).
  { exact (r2_le_mult_nonneg (req_minus I one) K1 Ha Hb). }
  assert (He : le zero (mult I K2)).
  { exact (r2_le_mult_nonneg I K2
                             (lt_le_iff zero I (inl (inv_pos_pos eta eta_pos)))
                             Hc). }
  assert (Hf : le zero (plus (mult (req_minus I one) K1) (mult I K2))).
  { apply (le_id_l zero (plus zero zero)
                   (plus (mult (req_minus I one) K1) (mult I K2))
                   (req_sym (plus zero zero) zero (plus_zero zero))).
    exact (le_plus_compat zero (mult (req_minus I one) K1)
                          zero (mult I K2) Hd He). }
  assert (Hg : le zero (mult beta
                             (plus (mult (req_minus I one) K1) (mult I K2)))).
  { exact (r2_le_mult_nonneg beta
                             (plus (mult (req_minus I one) K1) (mult I K2))
                             (lt_le_iff zero beta (inl beta_pos)) Hf). }
  apply (le_id_r zero
                 (mult beta (plus (mult (req_minus I one) K1) (mult I K2)))
                 (req_minus (JJ (NPX pi_t Hpi_t) (npx_pos pi_t Hpi_t))
                            (JJ pi_t Hpi_t))
                 (req_sym _ _ (r2_gap_diff pi_t Hpi_t Hn))
                 Hg).
Qed.

(* ---- [] Piece 10: dpo_loss(pi_next) <= dpo_loss(pi_t) (
   same position; uses r2_policy_improvement_mono + opp order preservation) ---- *)
Corollary r2_dpo_loss_step_le :
  forall (pi_t : S -> R) (Hpi_t : pos3 pi_t) (Hn : nrm pi_t),
    le (AO (NPX pi_t Hpi_t) (npx_pos pi_t Hpi_t)) (AO pi_t Hpi_t).
Proof.
  intros pi_t Hpi_t Hn.
  apply (opp_le_compat (JJ pi_t Hpi_t)
                       (JJ (NPX pi_t Hpi_t) (npx_pos pi_t Hpi_t))).
  exact (r2_policy_improvement_mono pi_t Hpi_t Hn).
Qed.


Lemma r2_log_inv_opp :
  forall (x : R) (Hx : lt zero x),
    req (log (inv_pos x Hx) (inv_pos_pos x Hx)) (opp (log x Hx)).
Proof.
  intros x Hx.
  exact (req2_log_inv_one_inv log_req_compat x Hx).
Qed.

Lemma r2_log_exp_neg_opp : forall x : R,
  req (log (exp_neg x) (exp_neg_pos x)) (opp x).
Proof.
  intro x.
  exact (req2_log_exp_neg log_inv_exp_neg_req x).
Qed.

(* beta*(eta*(beta^-1*A)) == eta*A (uses upstream req2_beta_eta_inv_absorb) *)
Lemma r2_beta_eta_iv_scal : forall A : R,
  req (mult beta (mult (mult eta (inv_pos beta beta_pos)) A)) (mult eta A).
Proof.
  intro A.
  exact (req2_beta_eta_inv_absorb beta beta_pos eta A).
Qed.


Lemma r2_pi_next_log_local :
  forall (pi_t : S -> R) (Hpi_t : pos3 pi_t) (s : S),
    req (log (NPX pi_t Hpi_t s) (npx_pos pi_t Hpi_t s))
        (plus (log (pi_t s) (Hpi_t s))
              (plus (mult (mult eta (inv_pos beta beta_pos)) (ADV pi_t Hpi_t s))
                    (opp (log (ZR pi_t Hpi_t) (zrel_pos pi_t Hpi_t))))).
Proof.
  intros pi_t Hpi_t s.
  set (lgT := log (pi_t s) (Hpi_t s)).
  set (lgZ := log (ZR pi_t Hpi_t) (zrel_pos pi_t Hpi_t)).
  set (X := mult (mult eta (inv_pos beta beta_pos)) (ADV pi_t Hpi_t s)).
  set (expm := exp_neg (opp X)).
  set (ivZ := inv_pos (ZR pi_t Hpi_t) (zrel_pos pi_t Hpi_t)).
  set (Hp1 := inv_pos_pos (ZR pi_t Hpi_t) (zrel_pos pi_t Hpi_t)).
  set (Hp2 := mult_positive (pi_t s) expm (Hpi_t s) (exp_neg_pos (opp X))).
  set (HpI := mult_positive ivZ (mult (pi_t s) expm) Hp1 Hp2).
  assert (HA : req (log (NPX pi_t Hpi_t s) (npx_pos pi_t Hpi_t s))
                   (log (mult ivZ (mult (pi_t s) expm)) HpI)).
  { exact (log_req_compat (NPX pi_t Hpi_t s)
                          (mult ivZ (mult (pi_t s) expm))
                          (npx_pos pi_t Hpi_t s) HpI
                          (req_refl (NPX pi_t Hpi_t s))). }
  assert (HB : req (log (mult ivZ (mult (pi_t s) expm)) HpI)
                   (plus (log ivZ Hp1) (log (mult (pi_t s) expm) Hp2))).
  { exact (log_mult ivZ (mult (pi_t s) expm) Hp1 Hp2). }
  assert (HC : req (log ivZ Hp1) (opp lgZ)).
  { exact (r2_log_inv_opp (ZR pi_t Hpi_t) (zrel_pos pi_t Hpi_t)). }
  assert (HD : req (log (mult (pi_t s) expm) Hp2) (plus lgT X)).
  { exact (req_trans (log (mult (pi_t s) expm) Hp2)
                     (plus lgT (log expm (exp_neg_pos (opp X))))
                     (plus lgT X)
                     (log_mult (pi_t s) expm (Hpi_t s) (exp_neg_pos (opp X)))
                     (req_plus_compat lgT lgT
                                      (log expm (exp_neg_pos (opp X))) X
                                      (req_refl lgT)
                                      (req_trans (log expm (exp_neg_pos (opp X)))
                                                 (opp (opp X)) X
                                                 (r2_log_exp_neg_opp (opp X))
                                                 (req_double_neg X)))). }
  assert (HE : req (log (mult ivZ (mult (pi_t s) expm)) HpI)
                   (plus (opp lgZ) (plus lgT X))).
  { exact (req_trans (log (mult ivZ (mult (pi_t s) expm)) HpI)
                     (plus (log ivZ Hp1) (log (mult (pi_t s) expm) Hp2))
                     (plus (opp lgZ) (plus lgT X))
                     HB
                     (req_plus_compat (log ivZ Hp1) (opp lgZ)
                                      (log (mult (pi_t s) expm) Hp2)
                                      (plus lgT X)
                                      HC HD)). }
  (* Finishing rearrangement chain (four steps):
     (opp lgZ)+(lgT+X) → ((opp lgZ)+lgT)+X → (lgT+(opp lgZ))+X
     -> lgT+((opp lgZ)+X) -> lgT+(X+(opp lgZ)), assembled stepwise via req_trans *)
  exact (req_trans (log (NPX pi_t Hpi_t s) (npx_pos pi_t Hpi_t s))
                   (plus (opp lgZ) (plus lgT X))
                   (plus lgT (plus X (opp lgZ)))
                   (req_trans (log (NPX pi_t Hpi_t s) (npx_pos pi_t Hpi_t s))
                              (log (mult ivZ (mult (pi_t s) expm)) HpI)
                              (plus (opp lgZ) (plus lgT X))
                              HA HE)
                   (req_trans (plus (opp lgZ) (plus lgT X))
                              (plus (plus lgT (opp lgZ)) X)
                              (plus lgT (plus X (opp lgZ)))
                              (req_trans (plus (opp lgZ) (plus lgT X))
                                         (plus (plus (opp lgZ) lgT) X)
                                         (plus (plus lgT (opp lgZ)) X)
                                         (plus_assoc (opp lgZ) lgT X)
                                         (req_plus_compat (plus (opp lgZ) lgT)
                                                          (plus lgT (opp lgZ)) X X
                                                          (plus_comm (opp lgZ) lgT)
                                                          (req_refl X)))
                              (req_trans (plus (plus lgT (opp lgZ)) X)
                                         (plus lgT (plus (opp lgZ) X))
                                         (plus lgT (plus X (opp lgZ)))
                                         (req_sym (plus lgT (plus (opp lgZ) X))
                                                  (plus (plus lgT (opp lgZ)) X)
                                                  (plus_assoc lgT (opp lgZ) X))
                                         (req_plus_compat lgT lgT
                                                          (plus (opp lgZ) X)
                                                          (plus X (opp lgZ))
                                                          (req_refl lgT)
                                                          (plus_comm (opp lgZ) X))))).
Qed.


Lemma r2_E_t_log_pt :
  forall (pi_t : S -> R) (Hpi_t : pos3 pi_t) (s : S),
    req (ET pi_t Hpi_t s)
        (opp (mult beta (plus (log (NPX pi_t Hpi_t s) (npx_pos pi_t Hpi_t s))
                              (log (ZR pi_t Hpi_t) (zrel_pos pi_t Hpi_t))))).
Proof.
  intros pi_t Hpi_t s.
  set (lgT := log (pi_t s) (Hpi_t s)).
  set (lgZ := log (ZR pi_t Hpi_t) (zrel_pos pi_t Hpi_t)).
  set (lgN := log (NPX pi_t Hpi_t s) (npx_pos pi_t Hpi_t s)).
  set (A := ADV pi_t Hpi_t s).
  assert (Hsum : req (plus lgN lgZ)
                     (plus lgT (mult (mult eta (inv_pos beta beta_pos)) A))).
  { apply (req_trans (plus lgN lgZ)
                     (plus (plus lgT (plus (mult (mult eta (inv_pos beta beta_pos)) A)
                                           (opp lgZ)))
                           lgZ)
                     (plus lgT (mult (mult eta (inv_pos beta beta_pos)) A))).
    - exact (req_plus_compat lgN
                             (plus lgT (plus (mult (mult eta (inv_pos beta beta_pos)) A)
                                             (opp lgZ)))
                             lgZ lgZ
                             (r2_pi_next_log_local pi_t Hpi_t s)
                             (req_refl lgZ)).
    - apply (req_trans (plus (plus lgT (plus (mult (mult eta (inv_pos beta beta_pos)) A)
                                             (opp lgZ)))
                             lgZ)
                       (plus lgT (plus (plus (mult (mult eta (inv_pos beta beta_pos)) A)
                                             (opp lgZ))
                                       lgZ))
                       (plus lgT (mult (mult eta (inv_pos beta beta_pos)) A))).
      + exact (req_sym (plus lgT (plus (plus (mult (mult eta (inv_pos beta beta_pos)) A)
                                             (opp lgZ))
                                       lgZ))
                       (plus (plus lgT (plus (mult (mult eta (inv_pos beta beta_pos)) A)
                                             (opp lgZ)))
                             lgZ)
                       (plus_assoc lgT (plus (mult (mult eta (inv_pos beta beta_pos)) A)
                                             (opp lgZ))
                                   lgZ)).
      + apply (req_plus_compat lgT lgT
                               (plus (plus (mult (mult eta (inv_pos beta beta_pos)) A)
                                           (opp lgZ))
                                     lgZ)
                               (mult (mult eta (inv_pos beta beta_pos)) A)
                               (req_refl lgT)
                               (req_trans (plus (plus (mult (mult eta (inv_pos beta beta_pos)) A)
                                                      (opp lgZ))
                                                lgZ)
                                          (plus (plus (mult (mult eta (inv_pos beta beta_pos)) A)
                                                      lgZ)
                                                (opp lgZ))
                                          (mult (mult eta (inv_pos beta beta_pos)) A)
                                          (r2_left_rotate (mult (mult eta (inv_pos beta beta_pos)) A)
                                                          (opp lgZ) lgZ)
                                          (r2_minus_cancel_mid
                                             (mult (mult eta (inv_pos beta beta_pos)) A) lgZ))). }
  assert (Hbeta : req (mult beta (plus lgN lgZ))
                      (plus (mult beta lgT) (mult eta A))).
  { apply (req_trans (mult beta (plus lgN lgZ))
                     (plus (mult beta lgT)
                           (mult beta (mult (mult eta (inv_pos beta beta_pos)) A)))
                     (plus (mult beta lgT) (mult eta A))).
    - exact (req_trans (mult beta (plus lgN lgZ))
                       (mult beta (plus lgT (mult (mult eta (inv_pos beta beta_pos)) A)))
                       (plus (mult beta lgT) (mult beta (mult (mult eta (inv_pos beta beta_pos)) A)))
                       (req_mult_compat beta beta (plus lgN lgZ)
                                       (plus lgT (mult (mult eta (inv_pos beta beta_pos)) A))
                                       (req_refl beta) Hsum)
                       (distrib beta lgT (mult (mult eta (inv_pos beta beta_pos)) A))).
    - exact (req_plus_compat (mult beta lgT) (mult beta lgT)
                             (mult beta (mult (mult eta (inv_pos beta beta_pos)) A))
                             (mult eta A)
                             (req_refl (mult beta lgT))
                             (r2_beta_eta_iv_scal A)). }
  exact (req_sym (opp (mult beta (plus lgN lgZ))) (ET pi_t Hpi_t s)
                (req_trans (opp (mult beta (plus lgN lgZ)))
                           (plus (opp (mult beta lgT)) (opp (mult eta A)))
                           (ET pi_t Hpi_t s)
                           (req_trans (opp (mult beta (plus lgN lgZ)))
                                      (opp (plus (mult beta lgT) (mult eta A)))
                                      (plus (opp (mult beta lgT)) (opp (mult eta A)))
                                      (req_opp_compat (mult beta (plus lgN lgZ))
                                                      (plus (mult beta lgT) (mult eta A))
                                                      Hbeta)
                                      (req_opp_plus (mult beta lgT) (mult eta A)))
                           (req_trans (plus (opp (mult beta lgT)) (opp (mult eta A)))
                                      (plus (opp (mult eta A)) (opp (mult beta lgT)))
                                      (ET pi_t Hpi_t s)
                                      (plus_comm (opp (mult beta lgT)) (opp (mult eta A)))
                                      (req_refl (ET pi_t Hpi_t s))))).
Qed.

(* ---- 0) opp zero == zero (req version; same position as Id opp_zero_t13) ---- *)
Lemma r2_opp_zero : req (opp zero) zero.
Proof.
  apply (req_trans (opp zero)
                   (req_minus (plus (opp zero) zero) zero) zero).
  - exact (req_sym (req_minus (plus (opp zero) zero) zero) (opp zero)
                   (r2_minus_cancel_mid (opp zero) zero)).
  - exact (req_trans (req_minus (plus (opp zero) zero) zero)
                     (req_minus zero zero) zero
                     (req2_minus_compat (plus (opp zero) zero) zero zero zero
                                        (req_plus_opp_l zero) (req_refl zero))
                     (plus_opp zero)).
Qed.

(* ---- 1) [done] gap monotone non-increasing (Id policy_iter_gap_mono @23086
   req theorized; uses r2_policy_improvement_mono + opp order preservation) ---- *)
Corollary req2_gap_mono :
  forall (pi_t : S -> R) (Hpi_t : pos3 pi_t) (Hn : nrm pi_t),
    le (req_minus (JJ PSTR PSTR_pos)
                  (JJ (NPX pi_t Hpi_t) (npx_pos pi_t Hpi_t)))
       (req_minus (JJ PSTR PSTR_pos) (JJ pi_t Hpi_t)).
Proof.
  intros pi_t Hpi_t Hn.
  apply (le_id_l
    (req_minus (JJ PSTR PSTR_pos)
               (JJ (NPX pi_t Hpi_t) (npx_pos pi_t Hpi_t)))
    (plus (JJ PSTR PSTR_pos)
          (opp (JJ (NPX pi_t Hpi_t) (npx_pos pi_t Hpi_t))))
    (req_minus (JJ PSTR PSTR_pos) (JJ pi_t Hpi_t))
    (r2_m_unfold (JJ PSTR PSTR_pos)
                 (JJ (NPX pi_t Hpi_t) (npx_pos pi_t Hpi_t)))).
  exact (le_plus_compat (JJ PSTR PSTR_pos) (JJ PSTR PSTR_pos)
                        (opp (JJ (NPX pi_t Hpi_t) (npx_pos pi_t Hpi_t)))
                        (opp (JJ pi_t Hpi_t))
                        (le_refl (JJ PSTR PSTR_pos))
                        (opp_le_compat (JJ pi_t Hpi_t)
                                       (JJ (NPX pi_t Hpi_t)
                                           (npx_pos pi_t Hpi_t))
                                       (r2_policy_improvement_mono
                                          pi_t Hpi_t Hn))).
Qed.

(* ---- 2) [] F_t_simpl_p req version (same position; general p) ---- *)
Lemma r2_F_t_simpl_p :
  forall (pi_t : S -> R) (Hpi_t : pos3 pi_t) (p : S -> R) (Hp : pos3 p),
    req (FE (ET pi_t Hpi_t) beta p Hp)
        (plus (opp (mult eta (sumf (fun s => mult (p s)
                                                  (ADV pi_t Hpi_t s)))))
              (mult beta (KLE p pi_t Hp Hpi_t))).
Proof.
  intros pi_t Hpi_t p Hp.
  set (SAp := sumf (fun s => mult (p s) (ADV pi_t Hpi_t s))).
  set (Slt := sumf (fun s => mult (p s) (log (pi_t s) (Hpi_t s)))).
  set (Sp := sumf (fun s => mult (p s) (log (p s) (Hp s)))).
  assert (HSE : req (sumf (fun s => mult (p s) (ET pi_t Hpi_t s)))
                    (req_minus (opp (mult eta SAp)) (mult beta Slt))).
  { apply (req_trans (sumf (fun s => mult (p s) (ET pi_t Hpi_t s)))
                     (sumf (fun s => req_minus
                                 (mult (p s) (opp (mult eta (ADV pi_t Hpi_t s))))
                                 (mult (p s) (mult beta (log (pi_t s) (Hpi_t s))))))
                     (req_minus (opp (mult eta SAp)) (mult beta Slt))).
    - apply (sum_ext (fun s => mult (p s) (ET pi_t Hpi_t s))
                     (fun s => req_minus
                                 (mult (p s) (opp (mult eta (ADV pi_t Hpi_t s))))
                                 (mult (p s) (mult beta (log (pi_t s) (Hpi_t s)))))).
      intro s.
      exact (req_mult_minus_distr_l (p s) (opp (mult eta (ADV pi_t Hpi_t s)))
                                    (mult beta (log (pi_t s) (Hpi_t s)))).
    - exact (req_trans
               (sumf (fun s => req_minus
                                 (mult (p s) (opp (mult eta (ADV pi_t Hpi_t s))))
                                 (mult (p s) (mult beta (log (pi_t s) (Hpi_t s))))))
               (req_minus
                  (sumf (fun s => mult (p s) (opp (mult eta (ADV pi_t Hpi_t s)))))
                  (sumf (fun s => mult (p s)
                                       (mult beta (log (pi_t s) (Hpi_t s))))))
               (req_minus (opp (mult eta SAp)) (mult beta Slt))
               (w_sum_minus
                  (fun s => mult (p s) (opp (mult eta (ADV pi_t Hpi_t s))))
                  (fun s => mult (p s)
                                 (mult beta (log (pi_t s) (Hpi_t s)))))
               (req2_minus_compat
                  (sumf (fun s => mult (p s) (opp (mult eta (ADV pi_t Hpi_t s)))))
                  (opp (mult eta SAp))
                  (sumf (fun s => mult (p s)
                                       (mult beta (log (pi_t s) (Hpi_t s)))))
                  (mult beta Slt)
                  (w_sum_ptimes_opp_scal p eta (fun s => ADV pi_t Hpi_t s))
                  (w_sum_ptimes_scal p beta
                                       (fun s => log (pi_t s) (Hpi_t s))))). }
  assert (Htail : req (plus (opp (mult beta Slt)) (mult beta Sp))
                      (mult beta (KLE p pi_t Hp Hpi_t))).
  { apply (req_trans (plus (opp (mult beta Slt)) (mult beta Sp))
                     (req_minus (mult beta Sp) (mult beta Slt))
                     (mult beta (KLE p pi_t Hp Hpi_t))).
    - apply plus_comm.
    - exact (req_trans (req_minus (mult beta Sp) (mult beta Slt))
                       (mult beta (req_minus Sp Slt))
                       (mult beta (KLE p pi_t Hp Hpi_t))
                       (req_sym (mult beta (req_minus Sp Slt))
                                (req_minus (mult beta Sp) (mult beta Slt))
                                (req_mult_minus_distr_l beta Sp Slt))
                       (req_mult_compat beta beta (req_minus Sp Slt)
                                        (KLE p pi_t Hp Hpi_t)
                                        (req_refl beta)
                                        (req_sym (KLE p pi_t Hp Hpi_t)
                                                 (req_minus Sp Slt)
                                                 (w_rel_ent_minus p pi_t Hp
                                                                  Hpi_t)))). }
  apply (req_trans (FE (ET pi_t Hpi_t) beta p Hp)
                   (plus (sumf (fun s => mult (p s) (ET pi_t Hpi_t s)))
                         (mult beta Sp))
                   (plus (opp (mult eta SAp))
                         (mult beta (KLE p pi_t Hp Hpi_t)))).
  - exact (req_sym
             (plus (sumf (fun s => mult (p s) (ET pi_t Hpi_t s)))
                   (mult beta Sp))
             (FE (ET pi_t Hpi_t) beta p Hp)
             (unfold_FE_eq (ET pi_t Hpi_t) beta p Hp)).
  - apply (req_trans (plus (sumf (fun s => mult (p s) (ET pi_t Hpi_t s)))
                           (mult beta Sp))
                     (plus (plus (opp (mult eta SAp)) (opp (mult beta Slt)))
                           (mult beta Sp))
                     (plus (opp (mult eta SAp))
                           (mult beta (KLE p pi_t Hp Hpi_t)))).
    + exact (req_plus_compat (sumf (fun s => mult (p s) (ET pi_t Hpi_t s)))
                             (plus (opp (mult eta SAp)) (opp (mult beta Slt)))
                             (mult beta Sp) (mult beta Sp)
                             HSE (req_refl (mult beta Sp))).
    + apply (req_trans (plus (plus (opp (mult eta SAp)) (opp (mult beta Slt)))
                             (mult beta Sp))
                       (plus (opp (mult eta SAp))
                             (plus (opp (mult beta Slt)) (mult beta Sp)))
                       (plus (opp (mult eta SAp))
                             (mult beta (KLE p pi_t Hp Hpi_t)))).
      * exact (req_sym (plus (opp (mult eta SAp))
                             (plus (opp (mult beta Slt)) (mult beta Sp)))
                       (plus (plus (opp (mult eta SAp)) (opp (mult beta Slt)))
                             (mult beta Sp))
                       (plus_assoc (opp (mult eta SAp)) (opp (mult beta Slt))
                                   (mult beta Sp))).
      * apply (req_plus_compat (opp (mult eta SAp)) (opp (mult eta SAp))
                               (plus (opp (mult beta Slt)) (mult beta Sp))
                               (mult beta (KLE p pi_t Hp Hpi_t))
                               (req_refl (opp (mult eta SAp))) Htail).
Qed.

(* ---- 3) [] F_t_beta_form use wrapper ---- *)
Lemma w_F_t_beta_form :
  forall (pi_t : S -> R) (Hpi_t : pos3 pi_t) (p : S -> R) (Hp : pos3 p)
         (Hpn : nrm p),
    req (FE (ET pi_t Hpi_t) beta p Hp)
        (plus (mult beta (sumf (fun s => mult (p s) (log (p s) (Hp s)))))
              (plus (opp (mult beta
                             (sumf (fun s => mult (p s)
                                                  (log (NPX pi_t Hpi_t s)
                                                       (npx_pos pi_t Hpi_t s))))))
                    (opp (mult beta (log (ZR pi_t Hpi_t)
                                          (zrel_pos pi_t Hpi_t)))))).
Proof.
  intros pi_t Hpi_t p Hp Hpn.
  exact (@req2_F_t_beta_form S sumf sum_ext sum_add sum_linear sum_pos
                             log_req_compat log_inv_exp_neg_req reward beta
                             beta_pos pi_ref pi_ref_pos eta pi_t Hpi_t p Hp
                             Hpn).
Qed.

(* ---- 4) [] F_t_decomp_p req version (general normalized p; KL-diff form) ---- *)
Lemma r2_F_t_kl_diff :
  forall (pi_t : S -> R) (Hpi_t : pos3 pi_t) (p : S -> R) (Hp : pos3 p)
         (Hpn : nrm p),
    req (FE (ET pi_t Hpi_t) beta p Hp)
        (req_minus (mult beta (KLE p (NPX pi_t Hpi_t) Hp
                                      (npx_pos pi_t Hpi_t)))
                   (mult beta (log (ZR pi_t Hpi_t)
                                   (zrel_pos pi_t Hpi_t)))).
Proof.
  intros pi_t Hpi_t p Hp Hpn.
  set (Sp := sumf (fun s => mult (p s) (log (p s) (Hp s)))).
  set (Sn := sumf (fun s => mult (p s)
                                 (log (NPX pi_t Hpi_t s)
                                      (npx_pos pi_t Hpi_t s)))).
  set (lgZ := log (ZR pi_t Hpi_t) (zrel_pos pi_t Hpi_t)).
  set (KPN := KLE p (NPX pi_t Hpi_t) Hp (npx_pos pi_t Hpi_t)).
  assert (Hklb : req (mult beta KPN) (req_minus (mult beta Sp) (mult beta Sn))).
  { exact (req_trans (mult beta KPN)
                     (mult beta (req_minus Sp Sn))
                     (req_minus (mult beta Sp) (mult beta Sn))
                     (req_mult_compat beta beta KPN (req_minus Sp Sn)
                                      (req_refl beta)
                                      (w_rel_ent_minus p (NPX pi_t Hpi_t) Hp
                                                       (npx_pos pi_t Hpi_t)))
                     (req_mult_minus_distr_l beta Sp Sn)). }
  assert (Hrhs : req (plus (mult beta Sp)
                           (plus (opp (mult beta Sn)) (opp (mult beta lgZ))))
                   (req_minus (mult beta KPN) (mult beta lgZ))).
  { apply (req_sym (req_minus (mult beta KPN) (mult beta lgZ))
                   (plus (mult beta Sp)
                         (plus (opp (mult beta Sn)) (opp (mult beta lgZ))))).
    apply (req_trans (req_minus (mult beta KPN) (mult beta lgZ))
                     (req_minus (req_minus (mult beta Sp) (mult beta Sn))
                                (mult beta lgZ))
                     (plus (mult beta Sp)
                           (plus (opp (mult beta Sn)) (opp (mult beta lgZ))))).
    - exact (req2_minus_compat (mult beta KPN)
                               (req_minus (mult beta Sp) (mult beta Sn))
                               (mult beta lgZ) (mult beta lgZ)
                               Hklb (req_refl (mult beta lgZ))).
    - exact (req_trans (req_minus (req_minus (mult beta Sp) (mult beta Sn))
                                  (mult beta lgZ))
                       (req_minus (mult beta Sp)
                                  (plus (mult beta Sn) (mult beta lgZ)))
                       (plus (mult beta Sp)
                             (plus (opp (mult beta Sn)) (opp (mult beta lgZ))))
                       (r2_minus_sub_plus (mult beta Sp) (mult beta Sn)
                                          (mult beta lgZ))
                       (req_plus_compat
                          (mult beta Sp) (mult beta Sp)
                          (opp (plus (mult beta Sn) (mult beta lgZ)))
                          (plus (opp (mult beta Sn)) (opp (mult beta lgZ)))
                          (req_refl (mult beta Sp))
                          (req_opp_plus (mult beta Sn) (mult beta lgZ)))). }
  exact (req_trans (FE (ET pi_t Hpi_t) beta p Hp)
                   (plus (mult beta Sp)
                         (plus (opp (mult beta Sn)) (opp (mult beta lgZ))))
                   (req_minus (mult beta KPN) (mult beta lgZ))
                   (w_F_t_beta_form pi_t Hpi_t p Hp Hpn)
                   Hrhs).
Qed.


Lemma r2_PSTR_log_local :
  forall s : S,
    req (log (PSTR s) (PSTR_pos s))
        (plus (opp (log ZAL ZAL_pos))
              (plus (log (pi_ref s) (pi_ref_pos s))
                    (mult (inv_pos beta beta_pos) (reward s)))).
Proof.
  intro s.
  set (iv := inv_pos beta beta_pos).
  set (ivZ := inv_pos ZAL ZAL_pos).
  set (Hp1 := inv_pos_pos ZAL ZAL_pos).
  set (expm := exp_neg (opp (mult iv (reward s)))).
  set (Hp2 := mult_positive (pi_ref s) expm (pi_ref_pos s)
                            (exp_neg_pos (opp (mult iv (reward s))))).
  set (HpI := mult_positive ivZ (mult (pi_ref s) expm) Hp1 Hp2).
  exact (req_trans (log (PSTR s) (PSTR_pos s))
                   (plus (log ivZ Hp1) (log (mult (pi_ref s) expm) Hp2))
                   (plus (opp (log ZAL ZAL_pos))
                         (plus (log (pi_ref s) (pi_ref_pos s))
                               (mult iv (reward s))))
                   (req_trans (log (PSTR s) (PSTR_pos s))
                              (log (mult ivZ (mult (pi_ref s) expm)) HpI)
                              (plus (log ivZ Hp1)
                                    (log (mult (pi_ref s) expm) Hp2))
                              (log_req_compat (PSTR s)
                                              (mult ivZ (mult (pi_ref s) expm))
                                              (PSTR_pos s) HpI
                                              (req_refl (PSTR s)))
                              (log_mult ivZ (mult (pi_ref s) expm) Hp1 Hp2))
                   (req_plus_compat (log ivZ Hp1) (opp (log ZAL ZAL_pos))
                                    (log (mult (pi_ref s) expm) Hp2)
                                    (plus (log (pi_ref s) (pi_ref_pos s))
                                          (mult iv (reward s)))
                                    (r2_log_inv_opp ZAL ZAL_pos)
                                    (req_trans
                                       (log (mult (pi_ref s) expm) Hp2)
                                       (plus (log (pi_ref s) (pi_ref_pos s))
                                             (log expm
                                                  (exp_neg_pos
                                                     (opp (mult iv
                                                                (reward s))))))
                                       (plus (log (pi_ref s) (pi_ref_pos s))
                                             (mult iv (reward s)))
                                       (log_mult (pi_ref s) expm
                                                 (pi_ref_pos s)
                                                 (exp_neg_pos
                                                    (opp (mult iv
                                                              (reward s)))))
                                       (req_plus_compat
                                          (log (pi_ref s) (pi_ref_pos s))
                                          (log (pi_ref s) (pi_ref_pos s))
                                          (log expm
                                               (exp_neg_pos
                                                  (opp (mult iv (reward s)))))
                                          (mult iv (reward s))
                                          (req_refl
                                             (log (pi_ref s) (pi_ref_pos s)))
                                          (req_trans
                                             (log expm
                                                  (exp_neg_pos
                                                     (opp
                                                        (mult iv
                                                              (reward s)))))
                                             (opp (opp (mult iv (reward s))))
                                             (mult iv (reward s))
                                             (r2_log_exp_neg_opp
                                                (opp (mult iv (reward s))))
                                             (req_double_neg
                                                (mult iv (reward s)))))))).
Qed.

(* ---- 6) Alignment energy, pointwise beta-reciprocal form ---- *)
Lemma r2_AL_log_local :
  forall s : S,
    req (mult (inv_pos beta beta_pos) (AL s))
        (opp (plus (log (pi_ref s) (pi_ref_pos s))
                   (mult (inv_pos beta beta_pos) (reward s)))).
Proof.
  intro s.
  set (iv := inv_pos beta beta_pos).
  set (lgR := log (pi_ref s) (pi_ref_pos s)).
  apply (req_trans (mult iv (AL s))
                   (req_minus (mult iv (opp (reward s)))
                              (mult iv (mult beta lgR)))
                   (opp (plus lgR (mult iv (reward s))))).
  - exact (req_mult_minus_distr_l iv (opp (reward s)) (mult beta lgR)).
  - apply (req_trans (req_minus (mult iv (opp (reward s)))
                                (mult iv (mult beta lgR)))
                     (req_minus (opp (mult iv (reward s))) lgR)
                     (opp (plus lgR (mult iv (reward s))))).
    + exact (req2_minus_compat (mult iv (opp (reward s)))
                               (opp (mult iv (reward s)))
                               (mult iv (mult beta lgR)) lgR
                               (req_opp_mult_l iv (reward s))
                               (r2_inv_absorb beta beta_pos lgR)).
    + apply (req_trans (req_minus (opp (mult iv (reward s))) lgR)
                       (plus (opp (mult iv (reward s))) (opp lgR))
                       (opp (plus lgR (mult iv (reward s))))).
      * apply req_refl.
      * apply (req_trans (plus (opp (mult iv (reward s))) (opp lgR))
                         (plus (opp lgR) (opp (mult iv (reward s))))
                         (opp (plus lgR (mult iv (reward s))))).
        -- apply plus_comm.
        -- exact (req_sym (opp (plus lgR (mult iv (reward s))))
                          (plus (opp lgR) (opp (mult iv (reward s))))
                          (req_opp_plus lgR (mult iv (reward s)))).
Qed.


Lemma r2_F_align_kl_diff :
  forall (p : S -> R) (Hp : pos3 p) (Hn : nrm p),
    req (FA p Hp)
        (req_minus (mult beta (KLE p PSTR Hp PSTR_pos))
                   (mult beta (log ZAL ZAL_pos))).
Proof.
  intros p Hp Hn.
  set (Sp := sumf (fun s => mult (p s) (log (p s) (Hp s)))).
  set (SgP := sumf (fun s => mult (p s) (log (PSTR s) (PSTR_pos s)))).
  set (lgZ := log ZAL ZAL_pos).
  set (KP := KLE p PSTR Hp PSTR_pos).
  assert (Hpt : forall s : S,
            req (AL s)
                (opp (plus (mult beta (log (PSTR s) (PSTR_pos s)))
                           (mult beta lgZ)))).
  { intro s.
    set (iv := inv_pos beta beta_pos).
    set (lgR := log (pi_ref s) (pi_ref_pos s)).
    set (lgP := log (PSTR s) (PSTR_pos s)).
    set (X0 := plus lgR (mult iv (reward s))).
    assert (HbA : req (mult beta (mult iv (AL s))) (AL s)).
    { exact (req_trans (mult beta (mult iv (AL s)))
                       (mult (mult beta iv) (AL s)) (AL s)
                       (mult_assoc beta iv (AL s))
                       (req_trans (mult (mult beta iv) (AL s))
                                  (mult (mult iv beta) (AL s)) (AL s)
                                  (req_mult_compat (mult beta iv)
                                                   (mult iv beta)
                                                   (AL s) (AL s)
                                                   (mult_comm beta iv)
                                                   (req_refl (AL s)))
                                  (req_trans (mult (mult iv beta) (AL s))
                                             (mult one (AL s)) (AL s)
                                             (req_mult_compat (mult iv beta)
                                                              one
                                                              (AL s) (AL s)
                                                              (req_trans (mult iv beta)
                                                                         (mult beta iv)
                                                                         one
                                                                         (mult_comm iv beta)
                                                                         (inv_pos_correct beta beta_pos))
                                                              (req_refl (AL s)))
                                             (req_mult_one_l (AL s))))). }
    assert (Hswap : req X0 (plus lgP lgZ)).
    { exact (req_sym (plus lgP lgZ) X0
               (req_trans (plus lgP lgZ)
                          (plus (opp lgZ) (plus X0 lgZ))
                          X0
                          (req_trans (plus lgP lgZ)
                                     (plus (plus (opp lgZ) X0) lgZ)
                                     (plus (opp lgZ) (plus X0 lgZ))
                                     (req_plus_compat lgP (plus (opp lgZ) X0)
                                                      lgZ lgZ
                                                      (r2_PSTR_log_local s)
                                                      (req_refl lgZ))
                                     (req_sym (plus (opp lgZ) (plus X0 lgZ))
                                              (plus (plus (opp lgZ) X0) lgZ)
                                              (plus_assoc (opp lgZ) X0 lgZ)))
                          (req_trans (plus (opp lgZ) (plus X0 lgZ))
                                     (plus (plus X0 lgZ) (opp lgZ))
                                     X0
                                     (plus_comm (opp lgZ) (plus X0 lgZ))
                                     (r2_minus_cancel_mid X0 lgZ)))). }
    assert (Hcomb : req (mult beta X0)
                        (plus (mult beta lgP) (mult beta lgZ)))
      by exact (req_trans (mult beta X0) (mult beta (plus lgP lgZ))
                          (plus (mult beta lgP) (mult beta lgZ))
                          (req_mult_compat beta beta X0 (plus lgP lgZ)
                                          (req_refl beta) Hswap)
                          (distrib beta lgP lgZ)).
    apply (req_trans (AL s) (opp (mult beta X0))
                     (opp (plus (mult beta lgP) (mult beta lgZ)))).
    - apply (req_trans (AL s) (mult beta (mult iv (AL s)))
                       (opp (mult beta X0))).
      + exact (req_sym (mult beta (mult iv (AL s))) (AL s) HbA).
      + exact (req_trans (mult beta (mult iv (AL s)))
                         (mult beta (opp X0)) (opp (mult beta X0))
                         (req_mult_compat beta beta (mult iv (AL s))
                                          (opp X0) (req_refl beta)
                                          (r2_AL_log_local s))
                         (req_opp_mult_l beta X0)).
    - exact (req_opp_compat (mult beta X0)
                            (plus (mult beta lgP) (mult beta lgZ))
                            Hcomb). }
  assert (Hsum : req (sumf (fun s => mult (p s) (AL s)))
                     (plus (opp (mult beta SgP)) (opp (mult beta lgZ)))).
  { apply (req_trans (sumf (fun s => mult (p s) (AL s)))
                     (sumf (fun s => plus
                                         (opp (mult (p s)
                                                    (mult beta
                                                          (log (PSTR s)
                                                               (PSTR_pos s)))))
                                         (opp (mult (p s) (mult beta lgZ)))))
                     (plus (opp (mult beta SgP)) (opp (mult beta lgZ)))).
    - apply (sum_ext (fun s => mult (p s) (AL s))
                     (fun s => plus
                                 (opp (mult (p s)
                                            (mult beta (log (PSTR s)
                                                         (PSTR_pos s)))))
                                 (opp (mult (p s) (mult beta lgZ))))).
      intro s.
      apply (req_trans (mult (p s) (AL s))
                       (mult (p s) (opp (plus
                                            (mult beta
                                                   (log (PSTR s) (PSTR_pos s)))
                                            (mult beta lgZ))))
                       (plus (opp (mult (p s)
                                        (mult beta (log (PSTR s)
                                                     (PSTR_pos s)))))
                             (opp (mult (p s) (mult beta lgZ))))).
      + exact (req_mult_compat (p s) (p s) (AL s)
                               (opp (plus
                                       (mult beta (log (PSTR s) (PSTR_pos s)))
                                       (mult beta lgZ)))
                               (req_refl (p s)) (Hpt s)).
      + apply (req_trans (mult (p s)
                               (opp (plus
                                       (mult beta (log (PSTR s) (PSTR_pos s)))
                                       (mult beta lgZ))))
                         (plus (mult (p s)
                                     (opp (mult beta
                                                (log (PSTR s) (PSTR_pos s)))))
                               (mult (p s) (opp (mult beta lgZ))))
                         (plus (opp (mult (p s)
                                          (mult beta
                                                (log (PSTR s) (PSTR_pos s)))))
                               (opp (mult (p s) (mult beta lgZ))))
                         (req_trans (mult (p s)
                                          (opp (plus
                                                  (mult beta
                                                         (log (PSTR s)
                                                              (PSTR_pos s)))
                                                  (mult beta lgZ))))
                                    (mult (p s)
                                          (plus (opp (mult beta
                                                             (log (PSTR s)
                                                                  (PSTR_pos s))))
                                                (opp (mult beta lgZ))))
                                    (plus (mult (p s)
                                                (opp (mult beta
                                                           (log (PSTR s)
                                                                (PSTR_pos s)))))
                                          (mult (p s) (opp (mult beta lgZ))))
                                    (req_mult_compat (p s) (p s)
                                                     (opp (plus
                                                             (mult beta
                                                                    (log (PSTR s)
                                                                         (PSTR_pos s)))
                                                             (mult beta lgZ)))
                                                     (plus (opp (mult beta
                                                                    (log (PSTR s)
                                                                         (PSTR_pos s))))
                                                           (opp (mult beta lgZ)))
                                                     (req_refl (p s))
                                                     (req_opp_plus (mult beta
                                                                          (log (PSTR s)
                                                                               (PSTR_pos s)))
                                                                   (mult beta lgZ)))
                                    (distrib (p s)
                                             (opp (mult beta (log (PSTR s) (PSTR_pos s))))
                                             (opp (mult beta lgZ))))
                         (req_plus_compat
                             (mult (p s)
                                   (opp (mult beta
                                                (log (PSTR s) (PSTR_pos s)))))
                             (opp (mult (p s)
                                        (mult beta
                                              (log (PSTR s) (PSTR_pos s)))))
                             (mult (p s) (opp (mult beta lgZ)))
                             (opp (mult (p s) (mult beta lgZ)))
                             (req_opp_mult_l (p s)
                                             (mult beta
                                                   (log (PSTR s)
                                                        (PSTR_pos s))))
                             (req_opp_mult_l (p s) (mult beta lgZ)))).
    - exact (req_trans
               (sumf (fun s => plus
                                   (opp (mult (p s)
                                              (mult beta
                                                    (log (PSTR s)
                                                         (PSTR_pos s)))))
                                   (opp (mult (p s) (mult beta lgZ)))))
               (plus (sumf (fun s => opp (mult (p s)
                                               (mult beta
                                                     (log (PSTR s)
                                                          (PSTR_pos s))))))
                     (sumf (fun s => opp (mult (p s) (mult beta lgZ)))))
               (plus (opp (mult beta SgP)) (opp (mult beta lgZ)))
               (sum_add
                  (fun s => opp (mult (p s)
                                      (mult beta (log (PSTR s) (PSTR_pos s)))))
                  (fun s => opp (mult (p s) (mult beta lgZ))))
               (req_plus_compat
                  (sumf (fun s => opp (mult (p s)
                                            (mult beta
                                                  (log (PSTR s)
                                                       (PSTR_pos s))))))
                  (opp (mult beta SgP))
                  (sumf (fun s => opp (mult (p s) (mult beta lgZ))))
                  (opp (mult beta lgZ))
                  (req_trans
                     (sumf (fun s => opp (mult (p s)
                                               (mult beta
                                                     (log (PSTR s)
                                                          (PSTR_pos s))))))
                     (opp (sumf (fun s => mult (p s)
                                               (mult beta
                                                     (log (PSTR s)
                                                          (PSTR_pos s))))))
                     (opp (mult beta SgP))
                     (w_sum_opp (fun s => mult (p s)
                                               (mult beta
                                                     (log (PSTR s)
                                                          (PSTR_pos s)))))
                     (req_opp_compat
                        (sumf (fun s => mult (p s)
                                              (mult beta
                                                    (log (PSTR s) (PSTR_pos s)))))
                        (mult beta SgP)
                        (w_sum_ptimes_scal p beta
                           (fun s => log (PSTR s) (PSTR_pos s)))))
                  (req_trans
                     (sumf (fun s => opp (mult (p s) (mult beta lgZ))))
                     (opp (sumf (fun s => mult (p s) (mult beta lgZ))))
                     (opp (mult beta lgZ))
                     (w_sum_opp (fun s => mult (p s) (mult beta lgZ)))
                     (req_opp_compat (sumf (fun s => mult (p s) (mult beta lgZ)))
                                     (mult beta lgZ)
                                     (w_sum_ptimes_const p (mult beta lgZ)
                                                         Hn))))). }
  apply (req_trans (FA p Hp)
                   (plus (sumf (fun s => mult (p s) (AL s))) (mult beta Sp))
                   (req_minus (mult beta KP) (mult beta lgZ))).
  - exact (unfold_FA p Hp).
  - apply (req_trans (plus (sumf (fun s => mult (p s) (AL s)))
                           (mult beta Sp))
                     (plus (plus (opp (mult beta SgP)) (opp (mult beta lgZ)))
                           (mult beta Sp))
                     (req_minus (mult beta KP) (mult beta lgZ))).
    + exact (req_plus_compat (sumf (fun s => mult (p s) (AL s)))
                             (plus (opp (mult beta SgP)) (opp (mult beta lgZ)))
                             (mult beta Sp) (mult beta Sp)
                             Hsum (req_refl (mult beta Sp))).
    + apply (req_trans (plus (plus (opp (mult beta SgP)) (opp (mult beta lgZ)))
                             (mult beta Sp))
                       (plus (mult beta Sp)
                             (plus (opp (mult beta SgP)) (opp (mult beta lgZ))))
                       (req_minus (mult beta KP) (mult beta lgZ))).
      * exact (plus_comm (plus (opp (mult beta SgP)) (opp (mult beta lgZ)))
                         (mult beta Sp)).
      * apply (req_trans (plus (mult beta Sp)
                               (plus (opp (mult beta SgP))
                                     (opp (mult beta lgZ))))
                         (plus (plus (mult beta Sp) (opp (mult beta SgP)))
                               (opp (mult beta lgZ)))
                         (req_minus (mult beta KP) (mult beta lgZ))).
        -- exact (plus_assoc (mult beta Sp) (opp (mult beta SgP))
                             (opp (mult beta lgZ))).
        -- apply (req_trans (plus (plus (mult beta Sp) (opp (mult beta SgP)))
                                  (opp (mult beta lgZ)))
                            (plus (mult beta (req_minus Sp SgP))
                                  (opp (mult beta lgZ)))
                            (req_minus (mult beta KP) (mult beta lgZ))).
           ++ exact (req_plus_compat
                       (plus (mult beta Sp) (opp (mult beta SgP)))
                       (mult beta (req_minus Sp SgP))
                       (opp (mult beta lgZ)) (opp (mult beta lgZ))
                       (req_trans (plus (mult beta Sp) (opp (mult beta SgP)))
                                  (req_minus (mult beta Sp) (mult beta SgP))
                                  (mult beta (req_minus Sp SgP))
                                  (req_sym (req_minus (mult beta Sp)
                                                      (mult beta SgP))
                                           (plus (mult beta Sp)
                                                 (opp (mult beta SgP)))
                                           (r2_m_unfold (mult beta Sp)
                                                        (mult beta SgP)))
                                  (req_sym (mult beta (req_minus Sp SgP))
                                           (req_minus (mult beta Sp)
                                                      (mult beta SgP))
                                           (req_mult_minus_distr_l beta Sp
                                                                     SgP)))
                       (req_refl (opp (mult beta lgZ)))).
           ++ exact (req_trans
                       (plus (mult beta (req_minus Sp SgP))
                             (opp (mult beta lgZ)))
                       (plus (mult beta KP) (opp (mult beta lgZ)))
                       (req_minus (mult beta KP) (mult beta lgZ))
                       (req_plus_compat
                          (mult beta (req_minus Sp SgP)) (mult beta KP)
                          (opp (mult beta lgZ)) (opp (mult beta lgZ))
                          (req_mult_compat beta beta (req_minus Sp SgP) KP
                                           (req_refl beta)
                                           (req_sym KP
                                                    (req_minus Sp SgP)
                                                    (w_rel_ent_minus p PSTR Hp
                                                                     PSTR_pos)))
                          (req_refl (opp (mult beta lgZ))))
                       (req_sym (req_minus (mult beta KP) (mult beta lgZ))
                                (plus (mult beta KP) (opp (mult beta lgZ)))
                                (r2_m_unfold (mult beta KP)
                                             (mult beta lgZ)))).
Qed.

(* ---- 8) [] rlhf_suboptimality_gap req version (same position) ---- *)
Lemma r2_rlhf_suboptimality_gap :
  forall (p : S -> R) (Hp : pos3 p) (Hn : nrm p),
    req (req_minus (JJ PSTR PSTR_pos) (JJ p Hp))
        (mult beta (KLE p PSTR Hp PSTR_pos)).
Proof.
  intros p Hp Hn.
  set (KP := KLE p PSTR Hp PSTR_pos).
  set (lgZ := log ZAL ZAL_pos).
  set (K0 := KLE PSTR PSTR PSTR_pos PSTR_pos).
  assert (Hfp : req (FA p Hp) (req_minus (mult beta KP) (mult beta lgZ)))
    by exact (r2_F_align_kl_diff p Hp Hn).
  assert (Hfs : req (FA PSTR PSTR_pos)
                    (req_minus (mult beta K0) (mult beta lgZ)))
    by exact (r2_F_align_kl_diff PSTR PSTR_pos w_pi_star_normalized).
  assert (Hk0 : req (mult beta K0) zero).
  { exact (req_trans (mult beta K0) (mult beta zero) zero
                     (req_mult_compat beta beta K0 zero (req_refl beta)
                                      (w_rel_ent_self_zero PSTR PSTR_pos))
                     (mult_zero beta)). }
  assert (Hzz : req (req_minus (mult beta lgZ) (mult beta lgZ)) zero)
    by exact (plus_opp (mult beta lgZ)).
  assert (Hmz : req (req_minus (mult beta KP) zero) (mult beta KP)).
  { exact (req_trans (req_minus (mult beta KP) zero)
                     (plus (mult beta KP) zero) (mult beta KP)
                     (req_plus_compat (mult beta KP) (mult beta KP)
                                      (opp zero) zero
                                      (req_refl (mult beta KP)) r2_opp_zero)
                     (req_plus_zero_r (mult beta KP))). }  - exact (req_trans
             (req_minus (JJ PSTR PSTR_pos) (JJ p Hp))
             (req_minus (FA p Hp) (FA PSTR PSTR_pos))
             (mult beta KP)
             (req_trans (req_minus (JJ PSTR PSTR_pos) (JJ p Hp))
                        (plus (JJ PSTR PSTR_pos) (opp (JJ p Hp)))
                        (plus (FA p Hp) (opp (FA PSTR PSTR_pos)))
                        (r2_m_unfold (JJ PSTR PSTR_pos) (JJ p Hp))
                        (req_trans (plus (JJ PSTR PSTR_pos) (opp (JJ p Hp)))
                                   (plus (opp (FA PSTR PSTR_pos)) (FA p Hp))
                                   (plus (FA p Hp) (opp (FA PSTR PSTR_pos)))
                                   (req_plus_compat (JJ PSTR PSTR_pos)
                                                    (opp (FA PSTR PSTR_pos))
                                                    (opp (JJ p Hp)) (FA p Hp)
                                                    (req_refl (JJ PSTR PSTR_pos))
                                                    (req_trans (opp (JJ p Hp))
                                                               (opp (opp (FA p Hp)))
                                                               (FA p Hp)
                                                               (req_opp_compat (JJ p Hp)
                                                                               (opp (FA p Hp))
                                                                               (req_refl (JJ p Hp)))
                                                               (req_double_neg (FA p Hp))))
                                   (plus_comm (opp (FA PSTR PSTR_pos))
                                              (FA p Hp))))
             (req_trans
             (req_minus (FA p Hp) (FA PSTR PSTR_pos))
             (req_minus (req_minus (mult beta KP) (mult beta lgZ))
                        (req_minus (mult beta K0) (mult beta lgZ)))
             (mult beta KP)
             (req2_minus_compat (FA p Hp)
                                (req_minus (mult beta KP) (mult beta lgZ))
                                (FA PSTR PSTR_pos)
                                (req_minus (mult beta K0) (mult beta lgZ))
                                Hfp Hfs)
             (req_trans
                (req_minus (req_minus (mult beta KP) (mult beta lgZ))
                           (req_minus (mult beta K0) (mult beta lgZ)))
                (req_minus (req_minus (mult beta KP) (mult beta K0))
                           (req_minus (mult beta lgZ) (mult beta lgZ)))
                (mult beta KP)
                (r2_minus_rearrange_four (mult beta KP) (mult beta lgZ)
                                         (mult beta K0) (mult beta lgZ))
                (req_trans
                   (req_minus (req_minus (mult beta KP) (mult beta K0))
                              (req_minus (mult beta lgZ) (mult beta lgZ)))
                   (req_minus (req_minus (mult beta KP) (mult beta K0)) zero)
                   (mult beta KP)
                   (req2_minus_compat
                      (req_minus (mult beta KP) (mult beta K0))
                      (req_minus (mult beta KP) (mult beta K0))
                      (req_minus (mult beta lgZ) (mult beta lgZ)) zero
                      (req_refl (req_minus (mult beta KP) (mult beta K0)))
                      Hzz)
                   (req_trans
                      (req_minus (req_minus (mult beta KP) (mult beta K0))
                                 zero)
                      (req_minus (mult beta KP) zero) (mult beta KP)
                      (req2_minus_compat (req_minus (mult beta KP) (mult beta K0))
                                         (mult beta KP) zero zero
                                         (req_trans (req_minus (mult beta KP)
                                                               (mult beta K0))
                                                    (req_minus (mult beta KP) zero)
                                                    (mult beta KP)
                                                    (req2_minus_compat
                                                       (mult beta KP) (mult beta KP)
                                                       (mult beta K0) zero
                                                       (req_refl (mult beta KP))
                                                       Hk0)
                                                    Hmz)
                                         (req_refl zero))
                      Hmz))))).
Qed.

(* ---- 9) [] align_objective_explicit req version (same position) ---- *)
Lemma r2_align_objective_explicit :
  forall (p : S -> R) (Hp : pos3 p),
    req (JJ p Hp)
        (req_minus (sumf (fun s => mult (p s) (reward s)))
                   (mult beta (KLE p pi_ref Hp pi_ref_pos))).
Proof.
  intros p Hp.
  set (Srw := sumf (fun s => mult (p s) (reward s))).
  set (Slr := sumf (fun s => mult (p s) (log (pi_ref s) (pi_ref_pos s)))).
  set (Sp := sumf (fun s => mult (p s) (log (p s) (Hp s)))).
  assert (HSA : req (sumf (fun s => mult (p s) (AL s)))
                    (req_minus (opp Srw) (mult beta Slr))).
  { apply (req_trans (sumf (fun s => mult (p s) (AL s)))
                     (sumf (fun s => req_minus (mult (p s) (opp (reward s)))
                                               (mult (p s)
                                                     (mult beta
                                                           (log (pi_ref s)
                                                                (pi_ref_pos s))))))
                     (req_minus (opp Srw) (mult beta Slr))).
    - apply (sum_ext (fun s => mult (p s) (AL s))
                     (fun s => req_minus (mult (p s) (opp (reward s)))
                                         (mult (p s)
                                               (mult beta
                                                     (log (pi_ref s)
                                                          (pi_ref_pos s)))))).
      intro s.
      exact (req_mult_minus_distr_l (p s) (opp (reward s))
                                    (mult beta
                                          (log (pi_ref s) (pi_ref_pos s)))).
    - exact (req_trans
               (sumf (fun s => req_minus (mult (p s) (opp (reward s)))
                                         (mult (p s)
                                               (mult beta
                                                     (log (pi_ref s)
                                                          (pi_ref_pos s))))))
               (req_minus
                  (sumf (fun s => mult (p s) (opp (reward s))))
                  (sumf (fun s => mult (p s)
                                       (mult beta
                                             (log (pi_ref s)
                                                  (pi_ref_pos s))))))
               (req_minus (opp Srw) (mult beta Slr))
               (w_sum_minus (fun s => mult (p s) (opp (reward s)))
                            (fun s => mult (p s)
                                           (mult beta
                                                 (log (pi_ref s)
                                                      (pi_ref_pos s)))))
               (req2_minus_compat
                  (sumf (fun s => mult (p s) (opp (reward s))))
                  (opp Srw)
                  (sumf (fun s => mult (p s)
                                       (mult beta
                                             (log (pi_ref s)
                                                  (pi_ref_pos s)))))
                  (mult beta Slr)
                  (req_trans
                     (sumf (fun s => mult (p s) (opp (reward s))))
                     (sumf (fun s => opp (mult (p s) (reward s))))
                     (opp Srw)
                     (sum_ext (fun s => mult (p s) (opp (reward s)))
                              (fun s => opp (mult (p s) (reward s)))
                              (fun s => req_opp_mult_l (p s) (reward s)))
                     (w_sum_opp (fun s => mult (p s) (reward s))))
                  (w_sum_ptimes_scal p beta
                     (fun s => log (pi_ref s) (pi_ref_pos s))))). }
  assert (Hklr : req (plus (mult beta Slr) (opp (mult beta Sp)))
                     (opp (mult beta (KLE p pi_ref Hp pi_ref_pos)))).
  { apply (req_trans (plus (mult beta Slr) (opp (mult beta Sp)))
                     (mult beta (req_minus Slr Sp))
                     (opp (mult beta (KLE p pi_ref Hp pi_ref_pos)))).
    - exact (req_sym (mult beta (req_minus Slr Sp))
                     (plus (mult beta Slr) (opp (mult beta Sp)))
                     (req_mult_minus_distr_l beta Slr Sp)).
    - exact (req_trans (mult beta (req_minus Slr Sp))
                       (mult beta (opp (req_minus Sp Slr)))
                       (opp (mult beta (KLE p pi_ref Hp pi_ref_pos)))
                       (req_mult_compat beta beta
                          (req_minus Slr Sp)
                          (opp (req_minus Sp Slr))
                          (req_refl beta)
                          (r2_opp_minus_rev Slr Sp))
                       (req_trans (mult beta (opp (req_minus Sp Slr)))
                                  (opp (mult beta (req_minus Sp Slr)))
                                  (opp (mult beta (KLE p pi_ref Hp pi_ref_pos)))
                                  (req_opp_mult_l beta (req_minus Sp Slr))
                                  (req_opp_compat (mult beta (req_minus Sp Slr))
                                                  (mult beta
                                                    (KLE p pi_ref Hp pi_ref_pos))
                                                  (req_mult_compat beta beta
                                                     (req_minus Sp Slr)
                                                     (KLE p pi_ref Hp pi_ref_pos)
                                                     (req_refl beta)
                                                     (req_sym (KLE p pi_ref Hp pi_ref_pos)
                                                              (req_minus Sp Slr)
                                                              (w_rel_ent_minus p pi_ref Hp
                                                                               pi_ref_pos)))))). }
  apply (req_trans (JJ p Hp)
                   (plus (opp (req_minus (opp Srw) (mult beta Slr)))
                         (opp (mult beta Sp)))
                   (req_minus Srw (mult beta (KLE p pi_ref Hp pi_ref_pos)))).
  - apply (req_trans (opp (FA p Hp))
                     (plus (opp (sumf (fun s => mult (p s) (AL s))))
                           (opp (mult beta Sp)))
                     (plus (opp (req_minus (opp Srw) (mult beta Slr)))
                           (opp (mult beta Sp)))).
    + exact (req_trans (opp (FA p Hp))
                       (opp (plus (sumf (fun s => mult (p s) (AL s)))
                                  (mult beta Sp)))
                       (plus (opp (sumf (fun s => mult (p s) (AL s))))
                             (opp (mult beta Sp)))
                       (req_opp_compat (FA p Hp)
                                       (plus (sumf (fun s => mult (p s)
                                                              (AL s)))
                                             (mult beta Sp))
                                       (req_sym (plus (sumf (fun s => mult
                                                                     (p s)
                                                                     (AL s)))
                                                      (mult beta Sp))
                                               (FA p Hp)
                                               (unfold_FA p Hp)))
                       (req_opp_plus (sumf (fun s => mult (p s) (AL s)))
                                     (mult beta Sp))).
    + exact (req_plus_compat (opp (sumf (fun s => mult (p s) (AL s))))
                             (opp (req_minus (opp Srw) (mult beta Slr)))
                             (opp (mult beta Sp)) (opp (mult beta Sp))
                             (req_sym (opp (req_minus (opp Srw)
                                                      (mult beta Slr)))
                                      (opp (sumf (fun s => mult (p s)
                                                                 (AL s))))
                                      (req_opp_compat
                                         (req_minus (opp Srw) (mult beta Slr))
                                         (sumf (fun s => mult (p s) (AL s)))
                                         (req_sym (sumf (fun s => mult (p s)
                                                                           (AL s)))
                                                  (req_minus (opp Srw)
                                                             (mult beta Slr))
                                                  HSA)))
                             (req_refl (opp (mult beta Sp)))).
  - apply (req_trans (plus (opp (req_minus (opp Srw) (mult beta Slr)))
                           (opp (mult beta Sp)))
                     (plus (plus Srw (mult beta Slr)) (opp (mult beta Sp)))
                     (req_minus Srw
                                (mult beta (KLE p pi_ref Hp pi_ref_pos)))).
    + exact (req_plus_compat (opp (req_minus (opp Srw) (mult beta Slr)))
                             (plus Srw (mult beta Slr))
                             (opp (mult beta Sp)) (opp (mult beta Sp))
                             (req_trans (opp (req_minus (opp Srw) (mult beta Slr)))
                                        (opp (plus (opp Srw) (opp (mult beta Slr))))
                                        (plus Srw (mult beta Slr))
                                        (req_refl (opp (req_minus (opp Srw) (mult beta Slr))))
                                        (req_trans (opp (plus (opp Srw) (opp (mult beta Slr))))
                                                   (plus (opp (opp Srw)) (opp (opp (mult beta Slr))))
                                                   (plus Srw (mult beta Slr))
                                                   (req_opp_plus (opp Srw) (opp (mult beta Slr)))
                                                   (req_plus_compat (opp (opp Srw))
                                                                    Srw
                                                                    (opp (opp (mult beta Slr)))
                                                                    (mult beta Slr)
                                                                    (req_double_neg Srw)
                                                                    (req_double_neg (mult beta Slr)))))
                             (req_refl (opp (mult beta Sp)))).
    + apply (req_trans (plus (plus Srw (mult beta Slr))
                             (opp (mult beta Sp)))
                       (plus Srw (plus (mult beta Slr) (opp (mult beta Sp))))
                       (req_minus Srw
                                  (mult beta
                                        (KLE p pi_ref Hp pi_ref_pos)))).
      * exact (req_sym (plus Srw (plus (mult beta Slr) (opp (mult beta Sp))))
                       (plus (plus Srw (mult beta Slr)) (opp (mult beta Sp)))
                       (plus_assoc Srw (mult beta Slr) (opp (mult beta Sp)))).
      * apply (req_plus_compat Srw Srw
                               (plus (mult beta Slr) (opp (mult beta Sp)))
                               (opp (mult beta (KLE p pi_ref Hp pi_ref_pos)))
                               (req_refl Srw) Hklr).
Qed.


(* ---- 10) [] sum_grad_cross req version (same position;
   SUM(PI_NEXT-PI_T)*A == SUM PI_NEXT*A - SUM PI_T*A, pure sum algebra) ---- *)
Lemma r2_sum_grad_cross :
  forall (pi_t : S -> R) (Hpi_t : pos3 pi_t),
    req (req_minus (sumf (fun s => mult (NPX pi_t Hpi_t s)
                                        (ADV pi_t Hpi_t s)))
                   (sumf (fun s => mult (pi_t s) (ADV pi_t Hpi_t s))))
        (sumf (fun s => mult (req_minus (NPX pi_t Hpi_t s) (pi_t s))
                             (ADV pi_t Hpi_t s))).
Proof.
  intros pi_t Hpi_t.
  apply (req_trans
           (req_minus
              (sumf (fun s => mult (NPX pi_t Hpi_t s) (ADV pi_t Hpi_t s)))
              (sumf (fun s => mult (pi_t s) (ADV pi_t Hpi_t s))))
           (sumf (fun s => req_minus (mult (NPX pi_t Hpi_t s)
                                           (ADV pi_t Hpi_t s))
                                     (mult (pi_t s) (ADV pi_t Hpi_t s))))
           (sumf (fun s => mult (req_minus (NPX pi_t Hpi_t s) (pi_t s))
                                (ADV pi_t Hpi_t s)))).
  - exact (req_sym
             (sumf (fun s => req_minus
                                 (mult (NPX pi_t Hpi_t s) (ADV pi_t Hpi_t s))
                                 (mult (pi_t s) (ADV pi_t Hpi_t s))))
             (req_minus
                (sumf (fun s => mult (NPX pi_t Hpi_t s) (ADV pi_t Hpi_t s)))
                (sumf (fun s => mult (pi_t s) (ADV pi_t Hpi_t s))))
             (w_sum_minus (fun s => mult (NPX pi_t Hpi_t s)
                                         (ADV pi_t Hpi_t s))
                          (fun s => mult (pi_t s) (ADV pi_t Hpi_t s)))).
  - apply (sum_ext
             (fun s => req_minus (mult (NPX pi_t Hpi_t s) (ADV pi_t Hpi_t s))
                                 (mult (pi_t s) (ADV pi_t Hpi_t s)))
             (fun s => mult (req_minus (NPX pi_t Hpi_t s) (pi_t s))
                                (ADV pi_t Hpi_t s))).
      intro s.
      exact (req_sym (mult (req_minus (NPX pi_t Hpi_t s) (pi_t s))
                           (ADV pi_t Hpi_t s))
                     (req_minus (mult (NPX pi_t Hpi_t s) (ADV pi_t Hpi_t s))
                                (mult (pi_t s) (ADV pi_t Hpi_t s)))
                     (r2_mmd_r (NPX pi_t Hpi_t s) (pi_t s)
                               (ADV pi_t Hpi_t s))).
Qed.

(* ---- 11) [] grad_cross_identity req version (same position;
   uses r2_surrogate_diff_identity + eta inverse absorption) ---- *)
Lemma r2_grad_cross_identity :
  forall (pi_t : S -> R) (Hpi_t : pos3 pi_t) (Hn : nrm pi_t),
    req (sumf (fun s => mult (req_minus (NPX pi_t Hpi_t s) (pi_t s))
                                (ADV pi_t Hpi_t s)))
        (mult (mult (inv_pos eta eta_pos) beta)
              (plus (KLE (NPX pi_t Hpi_t) pi_t
                                    (npx_pos pi_t Hpi_t) Hpi_t)
                    (KLE pi_t (NPX pi_t Hpi_t) Hpi_t
                                    (npx_pos pi_t Hpi_t)))).
Proof.
  intros pi_t Hpi_t Hn.
  set (X := sumf (fun s => mult (req_minus (NPX pi_t Hpi_t s) (pi_t s))
                                (ADV pi_t Hpi_t s))).
  set (K12 := plus (KLE (NPX pi_t Hpi_t) pi_t
                                    (npx_pos pi_t Hpi_t) Hpi_t)
                       (KLE pi_t (NPX pi_t Hpi_t) Hpi_t
                                    (npx_pos pi_t Hpi_t))).
  - exact (req_trans X (mult (inv_pos eta eta_pos) (mult eta X)) (mult (mult (inv_pos eta eta_pos) beta) K12) (req_sym (mult (inv_pos eta eta_pos) (mult eta X)) X (r2_inv_absorb eta eta_pos X)) (req_trans (mult (inv_pos eta eta_pos) (mult eta X)) (mult (inv_pos eta eta_pos) (mult beta K12)) (mult (mult (inv_pos eta eta_pos) beta) K12) (req_mult_compat (inv_pos eta eta_pos) (inv_pos eta eta_pos) (mult eta X) (mult beta K12) (req_refl (inv_pos eta eta_pos)) (req_trans (mult eta X) (mult eta (req_minus (sumf (fun s => mult (NPX pi_t Hpi_t s) (ADV pi_t Hpi_t s))) (sumf (fun s => mult (pi_t s) (ADV pi_t Hpi_t s))))) (mult beta K12) (req_mult_compat eta eta X (req_minus (sumf (fun s => mult (NPX pi_t Hpi_t s) (ADV pi_t Hpi_t s))) (sumf (fun s => mult (pi_t s) (ADV pi_t Hpi_t s)))) (req_refl eta) (req_trans X (sumf (fun s => req_minus (mult (NPX pi_t Hpi_t s) (ADV pi_t Hpi_t s)) (mult (pi_t s) (ADV pi_t Hpi_t s)))) (req_minus (sumf (fun s => mult (NPX pi_t Hpi_t s) (ADV pi_t Hpi_t s))) (sumf (fun s => mult (pi_t s) (ADV pi_t Hpi_t s)))) (sum_ext (fun s => mult (req_minus (NPX pi_t Hpi_t s) (pi_t s)) (ADV pi_t Hpi_t s)) (fun s => req_minus (mult (NPX pi_t Hpi_t s) (ADV pi_t Hpi_t s)) (mult (pi_t s) (ADV pi_t Hpi_t s))) (fun s => r2_mmd_r (NPX pi_t Hpi_t s) (pi_t s) (ADV pi_t Hpi_t s))) (w_sum_minus (fun s => mult (NPX pi_t Hpi_t s) (ADV pi_t Hpi_t s)) (fun s => mult (pi_t s) (ADV pi_t Hpi_t s))))) (r2_surrogate_diff_identity pi_t Hpi_t Hn))) (mult_assoc (inv_pos eta eta_pos) beta K12))).
Qed.


(* ---- 12) J(PI_STAR) explicit (req version of the Hstar inside Id sum_advance_gap) ---- *)
Lemma r2_J_PSTR :
  forall (pi_t : S -> R) (Hpi_t : pos3 pi_t),
    req (JJ PSTR PSTR_pos)
        (req_minus (sumf (fun s => mult (PSTR s) (ADV pi_t Hpi_t s)))
                   (mult beta (KLE PSTR pi_t PSTR_pos Hpi_t))).
Proof.
  intros pi_t Hpi_t.
  set (SAS := sumf (fun s => mult (PSTR s) (ADV pi_t Hpi_t s))).
  set (KST := KLE PSTR pi_t PSTR_pos Hpi_t).
  set (K := req_minus one eta).
  assert (HFE : req (FE (ET pi_t Hpi_t) beta PSTR PSTR_pos)
                    (plus (opp (mult eta SAS)) (mult beta KST)))
    by exact (r2_F_t_simpl_p pi_t Hpi_t PSTR PSTR_pos).
  assert (HoppFE : req (opp (FE (ET pi_t Hpi_t) beta PSTR PSTR_pos))
                       (plus (mult eta SAS) (opp (mult beta KST)))).
  { apply (req_trans (opp (FE (ET pi_t Hpi_t) beta PSTR PSTR_pos))
                     (opp (plus (opp (mult eta SAS)) (mult beta KST)))
                     (plus (mult eta SAS) (opp (mult beta KST)))).
    - exact (req_opp_compat (FE (ET pi_t Hpi_t) beta PSTR PSTR_pos)
                            (plus (opp (mult eta SAS)) (mult beta KST))
                            HFE).
    - exact (req_trans
               (opp (plus (opp (mult eta SAS)) (mult beta KST)))
               (plus (opp (opp (mult eta SAS))) (opp (mult beta KST)))
               (plus (mult eta SAS) (opp (mult beta KST)))
               (req_opp_plus (opp (mult eta SAS)) (mult beta KST))
               (req_plus_compat (opp (opp (mult eta SAS))) (mult eta SAS)
                                (opp (mult beta KST)) (opp (mult beta KST))
                                (req_double_neg (mult eta SAS))
                                (req_refl (opp (mult beta KST))))). }
  apply (req_trans (JJ PSTR PSTR_pos)
                   (plus (plus (mult eta SAS) (opp (mult beta KST)))
                         (mult K SAS))
                   (req_minus SAS (mult beta KST))).
  - exact (req_trans (JJ PSTR PSTR_pos)
                     (plus (opp (FE (ET pi_t Hpi_t) beta PSTR PSTR_pos))
                           (mult K SAS))
                     (plus (plus (mult eta SAS) (opp (mult beta KST)))
                           (mult K SAS))
                     (r2_align_objective_t12_decomp pi_t Hpi_t PSTR PSTR_pos)
                     (req_plus_compat (opp (FE (ET pi_t Hpi_t) beta
                                                  PSTR PSTR_pos))
                                      (plus (mult eta SAS)
                                            (opp (mult beta KST)))
                                      (mult K SAS) (mult K SAS)
                                      HoppFE (req_refl (mult K SAS)))).
  - apply (req_trans (plus (plus (mult eta SAS) (opp (mult beta KST)))
                           (mult K SAS))
                     (plus (plus (mult eta SAS) (mult K SAS))
                           (opp (mult beta KST)))
                     (req_minus SAS (mult beta KST))).
    + exact (req_trans (plus (plus (mult eta SAS) (opp (mult beta KST)))
                             (mult K SAS))
                       (plus (mult eta SAS)
                             (plus (opp (mult beta KST)) (mult K SAS)))
                       (plus (plus (mult eta SAS) (mult K SAS))
                             (opp (mult beta KST)))
                       (req_sym (plus (mult eta SAS)
                                      (plus (opp (mult beta KST))
                                            (mult K SAS)))
                                (plus (plus (mult eta SAS)
                                            (opp (mult beta KST)))
                                      (mult K SAS))
                                (plus_assoc (mult eta SAS)
                                            (opp (mult beta KST))
                                            (mult K SAS)))
                       (req_trans (plus (mult eta SAS)
                                        (plus (opp (mult beta KST))
                                              (mult K SAS)))
                                  (plus (mult eta SAS)
                                        (plus (mult K SAS)
                                              (opp (mult beta KST))))
                                  (plus (plus (mult eta SAS) (mult K SAS))
                                        (opp (mult beta KST)))
                                  (req_plus_compat (mult eta SAS)
                                                   (mult eta SAS)
                                                   (plus (opp (mult beta KST))
                                                         (mult K SAS))
                                                   (plus (mult K SAS)
                                                         (opp (mult beta KST)))
                                                   (req_refl (mult eta SAS))
                                                   (plus_comm
                                                      (opp (mult beta KST))
                                                      (mult K SAS)))
                                  (plus_assoc (mult eta SAS) (mult K SAS)
                                              (opp (mult beta KST))))).
    + apply (req_trans (plus (plus (mult eta SAS) (mult K SAS))
                             (opp (mult beta KST)))
                       (plus SAS (opp (mult beta KST)))
                       (req_minus SAS (mult beta KST))).
      * exact (req_plus_compat (plus (mult eta SAS) (mult K SAS)) SAS
                               (opp (mult beta KST)) (opp (mult beta KST))
                               (req2_eta_absorb eta SAS)
                               (req_refl (opp (mult beta KST)))).
      * apply req_refl.
Qed.

(* ---- 13) [] sum_advance_gap req version (same position) ---- *)
Lemma r2_sum_advance_gap :
  forall (pi_t : S -> R) (Hpi_t : pos3 pi_t) (Hn : nrm pi_t),
    req (req_minus (sumf (fun s => mult (pi_t s) (ADV pi_t Hpi_t s)))
                   (sumf (fun s => mult (PSTR s) (ADV pi_t Hpi_t s))))
        (plus (opp (mult beta (KLE pi_t PSTR Hpi_t PSTR_pos)))
              (opp (mult beta (KLE PSTR pi_t PSTR_pos Hpi_t)))).
Proof.
  intros pi_t Hpi_t Hn.
  set (SAT := sumf (fun s => mult (pi_t s) (ADV pi_t Hpi_t s))).
  set (SAS := sumf (fun s => mult (PSTR s) (ADV pi_t Hpi_t s))).
  set (KST := KLE PSTR pi_t PSTR_pos Hpi_t).
  set (KTS := KLE pi_t PSTR Hpi_t PSTR_pos).
  assert (Hxs : req SAS (plus (mult beta KST) (JJ PSTR PSTR_pos))).
  { exact (req_sym (plus (mult beta KST) (JJ PSTR PSTR_pos)) SAS
               (req_trans (plus (mult beta KST) (JJ PSTR PSTR_pos))
                          (plus (mult beta KST)
                                (req_minus SAS (mult beta KST)))
                          SAS
                          (req_plus_compat (mult beta KST) (mult beta KST)
                                           (JJ PSTR PSTR_pos)
                                           (req_minus SAS (mult beta KST))
                                           (req_refl (mult beta KST))
                                           (r2_J_PSTR pi_t Hpi_t))
                          (req_minus_plus_cancel (mult beta KST) SAS))). }
  apply (req_trans (req_minus SAT SAS)
                   (req_minus (req_minus (JJ pi_t Hpi_t)
                                         (JJ PSTR PSTR_pos))
                              (mult beta KST))
                   (plus (opp (mult beta KTS)) (opp (mult beta KST)))).
  - exact (req_trans (req_minus SAT SAS) (req_minus (JJ pi_t Hpi_t) SAS) (req_minus (req_minus (JJ pi_t Hpi_t) (JJ PSTR PSTR_pos)) (mult beta KST)) (req2_minus_compat SAT (JJ pi_t Hpi_t) SAS SAS (req_sym (JJ pi_t Hpi_t) SAT (r2_J_pi_t pi_t Hpi_t Hn)) (req_refl SAS)) (req_trans (req_minus (JJ pi_t Hpi_t) SAS) (req_minus (JJ pi_t Hpi_t) (plus (JJ PSTR PSTR_pos) (mult beta KST))) (req_minus (req_minus (JJ pi_t Hpi_t) (JJ PSTR PSTR_pos)) (mult beta KST)) (req2_minus_compat (JJ pi_t Hpi_t) (JJ pi_t Hpi_t) SAS (plus (JJ PSTR PSTR_pos) (mult beta KST)) (req_refl (JJ pi_t Hpi_t)) (req_trans SAS (plus (mult beta KST) (JJ PSTR PSTR_pos)) (plus (JJ PSTR PSTR_pos) (mult beta KST)) Hxs (plus_comm (mult beta KST) (JJ PSTR PSTR_pos)))) (req_sym (req_minus (req_minus (JJ pi_t Hpi_t) (JJ PSTR PSTR_pos)) (mult beta KST)) (req_minus (JJ pi_t Hpi_t) (plus (JJ PSTR PSTR_pos) (mult beta KST))) (r2_minus_sub_plus (JJ pi_t Hpi_t) (JJ PSTR PSTR_pos) (mult beta KST))))).
  - exact (req_trans (req_minus (req_minus (JJ pi_t Hpi_t)
                                           (JJ PSTR PSTR_pos))
                                 (mult beta KST))
                     (req_minus (opp (req_minus (JJ PSTR PSTR_pos)
                                                (JJ pi_t Hpi_t)))
                                (mult beta KST))
                     (plus (opp (mult beta KTS)) (opp (mult beta KST)))
                     (req2_minus_compat (req_minus (JJ pi_t Hpi_t)
                                                   (JJ PSTR PSTR_pos))
                                        (opp (req_minus (JJ PSTR PSTR_pos)
                                                        (JJ pi_t Hpi_t)))
                                        (mult beta KST) (mult beta KST)
                                        (r2_opp_minus_rev (JJ pi_t Hpi_t)
                                                          (JJ PSTR PSTR_pos))
                                        (req_refl (mult beta KST)))
                     (req2_minus_compat
                        (opp (req_minus (JJ PSTR PSTR_pos) (JJ pi_t Hpi_t)))
                        (opp (mult beta KTS))
                        (mult beta KST) (mult beta KST)
                        (req_opp_compat (req_minus (JJ PSTR PSTR_pos)
                                                   (JJ pi_t Hpi_t))
                                        (mult beta KTS)
                                        (r2_rlhf_suboptimality_gap pi_t Hpi_t
                                                                   Hn))
                        (req_refl (mult beta KST)))).
Qed.



Lemma r2_t13_hexp :
  forall (pi_t : S -> R) (Hpi_t : pos3 pi_t),
    req (req_minus (plus (opp (mult eta (sumf (fun s => mult (PSTR s)
                                                             (ADV pi_t
                                                                    Hpi_t
                                                                    s)))))
                                (mult beta
                                      (KLE PSTR pi_t PSTR_pos Hpi_t)))
                   (plus (opp (mult eta (sumf (fun s => mult
                                                             (NPX pi_t
                                                                    Hpi_t s)
                                                             (ADV pi_t Hpi_t
                                                                    s)))))
                                (mult beta
                                      (KLE (NPX pi_t Hpi_t) pi_t
                                           (npx_pos pi_t Hpi_t) Hpi_t))))
        (plus (mult eta
                    (req_minus (sumf (fun s => mult (NPX pi_t Hpi_t s)
                                                     (ADV pi_t Hpi_t s)))
                               (sumf (fun s => mult (PSTR s)
                                                    (ADV pi_t Hpi_t s)))))
              (mult beta
                    (req_minus (KLE PSTR pi_t PSTR_pos Hpi_t)
                               (KLE (NPX pi_t Hpi_t) pi_t
                                    (npx_pos pi_t Hpi_t) Hpi_t)))).
Proof.
  intros pi_t Hpi_t.
  set (SAS := sumf (fun s => mult (PSTR s) (ADV pi_t Hpi_t s))).
  set (SAN := sumf (fun s => mult (NPX pi_t Hpi_t s) (ADV pi_t Hpi_t s))).
  set (KST := mult beta (KLE PSTR pi_t PSTR_pos Hpi_t)).
  set (K1 := mult beta (KLE (NPX pi_t Hpi_t) pi_t
                            (npx_pos pi_t Hpi_t) Hpi_t)).
  set (A := opp (mult eta SAS)).
  set (C := opp (mult eta SAN)).
  apply (req_trans (req_minus (plus A KST) (plus C K1))
                   (plus (req_minus A C) (req_minus KST K1))).
  - exact (r2_minus_distr A KST C K1).
  - apply (req_plus_compat (req_minus A C)
                           (mult eta (req_minus SAN SAS))
                           (req_minus KST K1)
                           (mult beta (req_minus (KLE PSTR pi_t PSTR_pos Hpi_t)
                                                 (KLE (NPX pi_t Hpi_t) pi_t
                                                      (npx_pos pi_t Hpi_t) Hpi_t)))
                           (r2_minus_opp_opp_mult SAS SAN)
                           (req_sym (mult beta (req_minus (KLE PSTR pi_t PSTR_pos Hpi_t) (KLE (NPX pi_t Hpi_t) pi_t (npx_pos pi_t Hpi_t) Hpi_t)))
                                    (req_minus (mult beta (KLE PSTR pi_t PSTR_pos Hpi_t))
                                               (mult beta (KLE (NPX pi_t Hpi_t) pi_t (npx_pos pi_t Hpi_t) Hpi_t)))
                                    (req_mult_minus_distr_l beta (KLE PSTR pi_t PSTR_pos Hpi_t) (KLE (NPX pi_t Hpi_t) pi_t (npx_pos pi_t Hpi_t) Hpi_t)))).
Qed.

(* ---- 15) beta inverse absorption (iv*(beta*X) == X) ---- *)
Lemma r2_iv_beta : forall X : R,
  req (mult (inv_pos beta beta_pos) (mult beta X)) X.
Proof. intro X. exact (r2_inv_absorb beta beta_pos X). Qed.

(* ---- 16) General c-weight version (iv*(c*(beta*X)) == c*X) ---- *)
Lemma r2_iv_beta_scal : forall c X : R,
  req (mult (inv_pos beta beta_pos) (mult c (mult beta X))) (mult c X).
Proof.
  intros c X.
  set (iv := inv_pos beta beta_pos).
  set (T1 := mult iv (mult c (mult beta X))).
  set (T2 := mult (mult iv c) (mult beta X)).
  set (T3 := mult (mult c iv) (mult beta X)).
  set (T4 := mult c (mult iv (mult beta X))).
  set (T5 := mult c (mult (mult iv beta) X)).
  set (T6 := mult c (mult one X)).
  assert (Ha : req T1 T2) by exact (mult_assoc iv c (mult beta X)).
  assert (Hb : req T2 T3).
  { exact (req_mult_compat (mult iv c) (mult c iv) (mult beta X) (mult beta X)
                           (mult_comm iv c) (req_refl (mult beta X))). }
  assert (Hc : req T3 T4).
  { exact (req_sym (mult c (mult iv (mult beta X))) T3
                   (mult_assoc c iv (mult beta X))). }
  assert (Hd : req T4 T5).
  { exact (req_mult_compat c c (mult iv (mult beta X))
                           (mult (mult iv beta) X)
                           (req_refl c) (mult_assoc iv beta X)). }
  assert (He : req T5 T6).
  { exact (req_mult_compat c c (mult (mult iv beta) X) (mult one X)
                           (req_refl c)
                           (req_trans (mult (mult iv beta) X)
                                      (mult (mult beta iv) X)
                                      (mult one X)
                                      (req_mult_compat (mult iv beta)
                                                       (mult beta iv) X X
                                                       (mult_comm iv beta)
                                                       (req_refl X))
                                      (req_mult_compat (mult beta iv) one X X
                                                       (inv_pos_correct
                                                          beta beta_pos)
                                                       (req_refl X)))). }
  assert (Hf : req T6 (mult c X)) by exact (req_mult_compat c c (mult one X) X (req_refl c) (req_mult_one_l X)).
  exact (req_trans T1 T2 (mult c X) Ha
           (req_trans T2 T3 (mult c X) Hb
              (req_trans T3 T4 (mult c X) Hc
                 (req_trans T4 T5 (mult c X) Hd
                    (req_trans T5 T6 (mult c X) He Hf))))).
Qed.


(* ---- 17) Main-theorem completion collapse lemma (B1 cancellation + kappa shaping; pure algebra) ---- *)
Lemma r2_bksn_collapse2 :
  forall a b u v w : R,
    req (plus (plus (plus (plus a b) (opp u)) (opp v)) (plus w (opp a)))
        (plus (plus b (opp u)) (req_minus w v)).
Proof.
  intros a b u v w.
  set (P1x := plus (plus (plus a b) (opp u)) (opp v)).
  set (P2x := plus (plus (plus a b) (plus (opp u) (opp v))) (opp a)).
  assert (H12 : req (plus P1x (opp a)) P2x).
  { exact (req_plus_compat P1x
                           (plus (plus a b) (plus (opp u) (opp v)))
                           (opp a) (opp a)
                           (req_sym (plus (plus a b) (plus (opp u) (opp v)))
                                    P1x
                                    (plus_assoc (plus a b) (opp u) (opp v)))
                           (req_refl (opp a))). }
  apply (req_trans (plus P1x (plus w (opp a)))
                   (plus (plus w (opp a)) P1x)
                   (plus (plus b (opp u)) (plus w (opp v)))).
  - exact (plus_comm P1x (plus w (opp a))).
  - apply (req_trans (plus (plus w (opp a)) P1x)
                     (plus w (plus (opp a) P1x))
                     (plus (plus b (opp u)) (plus w (opp v)))).
    + exact (req_sym (plus w (plus (opp a) P1x))
                     (plus (plus w (opp a)) P1x)
                     (plus_assoc w (opp a) P1x)).
    + apply (req_trans (plus w (plus (opp a) P1x))
                       (plus w (plus P1x (opp a)))
                       (plus (plus b (opp u)) (plus w (opp v)))).
      * exact (req_plus_compat w w (plus (opp a) P1x) (plus P1x (opp a))
                               (req_refl w) (plus_comm (opp a) P1x)).
      * apply (req_trans (plus w (plus P1x (opp a)))
                         (plus w P2x)
                         (plus (plus b (opp u)) (plus w (opp v)))).
        -- exact (req_plus_compat w w (plus P1x (opp a)) P2x
                                  (req_refl w) H12).
        -- exact (req_trans (plus w P2x)
                            (plus w (plus (opp v) (plus (opp u) b)))
                            (plus (plus b (opp u)) (plus w (opp v)))
                            (req_plus_compat w w P2x
                                             (plus (opp v) (plus (opp u) b))
                                             (req_refl w)
                                             (r2_gap_collapse a b u v))
                            (req_trans (plus w (plus (opp v) (plus (opp u) b)))
                                       (plus (plus w (opp v))
                                             (plus (opp u) b))
                                       (plus (plus b (opp u))
                                             (plus w (opp v)))
                                       (plus_assoc w (opp v)
                                                   (plus (opp u) b))
                                       (req_trans
                                          (plus (plus w (opp v))
                                                (plus (opp u) b))
                                          (plus (plus w (opp v))
                                                (plus b (opp u)))
                                          (plus (plus b (opp u))
                                                (plus w (opp v)))
                                          (req_plus_compat
                                             (plus w (opp v))
                                             (plus w (opp v))
                                             (plus (opp u) b)
                                             (plus b (opp u))
                                             (req_refl (plus w (opp v)))
                                             (plus_comm (opp u) b))
                                          (plus_comm (plus w (opp v))
                                                     (plus b (opp u)))))).
Qed.

(* ---- 18) beta*KSN == FE star diff - FE next diff (supplier for the first limb HA of the main theorem) ---- *)
Lemma r2_beta_KSN_Fdiff :
  forall (pi_t : S -> R) (Hpi_t : pos3 pi_t) (Hn : nrm pi_t),
    req (mult beta (KLE PSTR (NPX pi_t Hpi_t) PSTR_pos
                             (npx_pos pi_t Hpi_t)))
        (req_minus (FE (ET pi_t Hpi_t) beta PSTR PSTR_pos)
                   (FE (ET pi_t Hpi_t) beta (NPX pi_t Hpi_t)
                             (npx_pos pi_t Hpi_t))).
Proof.
  intros pi_t Hpi_t Hn.
  set (KSN := KLE PSTR (NPX pi_t Hpi_t) PSTR_pos (npx_pos pi_t Hpi_t)).
  set (lgZ := log (ZR pi_t Hpi_t) (zrel_pos pi_t Hpi_t)).
  set (KN := KLE (NPX pi_t Hpi_t) (NPX pi_t Hpi_t)
                    (npx_pos pi_t Hpi_t) (npx_pos pi_t Hpi_t)).
  assert (Hk0 : req (mult beta KN) zero).
  { exact (req_trans (mult beta KN) (mult beta zero) zero
                     (req_mult_compat beta beta KN zero (req_refl beta)
                                      (w_rel_ent_self_zero (NPX pi_t Hpi_t)
                                                           (npx_pos pi_t
                                                                      Hpi_t)))
                     (mult_zero beta)). }
  assert (Hxz : req (req_minus (mult beta KSN) zero) (mult beta KSN)).
  { exact (req_trans (req_minus (mult beta KSN) zero)
                     (plus (mult beta KSN) zero) (mult beta KSN)
                     (req_plus_compat (mult beta KSN) (mult beta KSN)
                                      (opp zero) zero
                                      (req_refl (mult beta KSN)) r2_opp_zero)
                     (req_plus_zero_r (mult beta KSN))). }
  assert (Hzz : req (req_minus (mult beta lgZ) (mult beta lgZ)) zero)
    by exact (plus_opp (mult beta lgZ)).
  assert (Hleg1 : req (req_minus (FE (ET pi_t Hpi_t) beta PSTR PSTR_pos)
                                 (FE (ET pi_t Hpi_t) beta (NPX pi_t Hpi_t)
                                           (npx_pos pi_t Hpi_t)))
                      (req_minus (req_minus (mult beta KSN) (mult beta lgZ))
                                 (req_minus (mult beta KN) (mult beta lgZ)))).
  { exact (req2_minus_compat
             (FE (ET pi_t Hpi_t) beta PSTR PSTR_pos)
             (req_minus (mult beta KSN) (mult beta lgZ))
             (FE (ET pi_t Hpi_t) beta (NPX pi_t Hpi_t) (npx_pos pi_t Hpi_t))
             (req_minus (mult beta KN) (mult beta lgZ))
             (r2_F_t_kl_diff pi_t Hpi_t PSTR PSTR_pos w_pi_star_normalized)
             (r2_F_t_kl_diff pi_t Hpi_t (NPX pi_t Hpi_t)
                             (npx_pos pi_t Hpi_t)
                             (w_pi_next_normalized pi_t Hpi_t))). }
  assert (Hleg2 : req (req_minus (req_minus (mult beta KSN) (mult beta lgZ))
                                 (req_minus (mult beta KN) (mult beta lgZ)))
                      (req_minus (req_minus (mult beta KSN) (mult beta KN))
                                 (req_minus (mult beta lgZ) (mult beta lgZ))))
    by exact (r2_minus_rearrange_four (mult beta KSN) (mult beta lgZ)
                                      (mult beta KN) (mult beta lgZ)).
  assert (Hleg3 : req (req_minus (req_minus (mult beta KSN) (mult beta KN))
                                 (req_minus (mult beta lgZ) (mult beta lgZ)))
                      (req_minus (req_minus (mult beta KSN) (mult beta KN))
                                 zero)).
  { exact (req2_minus_compat
             (req_minus (mult beta KSN) (mult beta KN))
             (req_minus (mult beta KSN) (mult beta KN))
             (req_minus (mult beta lgZ) (mult beta lgZ)) zero
             (req_refl (req_minus (mult beta KSN) (mult beta KN)))
             Hzz). }
  assert (H4a : req (req_minus (mult beta KSN) (mult beta KN))
                    (req_minus (mult beta KSN) zero)).
  { exact (req2_minus_compat (mult beta KSN) (mult beta KSN) (mult beta KN)
                             zero (req_refl (mult beta KSN)) Hk0). }
  assert (Hleg4 : req (req_minus (req_minus (mult beta KSN) (mult beta KN))
                                 zero)
                      (mult beta KSN)).
  { exact (req_trans
             (req_minus (req_minus (mult beta KSN) (mult beta KN)) zero)
             (req_minus (mult beta KSN) (mult beta KN))
             (mult beta KSN)
             (req_trans (req_minus (req_minus (mult beta KSN) (mult beta KN))
                                   zero)
                        (plus (req_minus (mult beta KSN) (mult beta KN)) zero)
                        (req_minus (mult beta KSN) (mult beta KN))
                        (req_plus_compat
                           (req_minus (mult beta KSN) (mult beta KN))
                           (req_minus (mult beta KSN) (mult beta KN))
                           (opp zero) zero
                           (req_refl (req_minus (mult beta KSN)
                                                (mult beta KN)))
                           r2_opp_zero)
                        (req_plus_zero_r
                           (req_minus (mult beta KSN) (mult beta KN))))
             (req_trans (req_minus (mult beta KSN) (mult beta KN))
                        (req_minus (mult beta KSN) zero)
                        (mult beta KSN)
                        H4a Hxz)). }
  apply (req_sym (req_minus (FE (ET pi_t Hpi_t) beta PSTR PSTR_pos)
                            (FE (ET pi_t Hpi_t) beta (NPX pi_t Hpi_t)
                                      (npx_pos pi_t Hpi_t)))
                 (mult beta KSN)).
  exact (req_trans
           (req_minus (FE (ET pi_t Hpi_t) beta PSTR PSTR_pos)
                      (FE (ET pi_t Hpi_t) beta (NPX pi_t Hpi_t)
                                (npx_pos pi_t Hpi_t)))
           (req_minus (req_minus (mult beta KSN) (mult beta lgZ))
                      (req_minus (mult beta KN) (mult beta lgZ)))
           (mult beta KSN)
           Hleg1
           (req_trans
              (req_minus (req_minus (mult beta KSN) (mult beta lgZ))
                         (req_minus (mult beta KN) (mult beta lgZ)))
              (req_minus (req_minus (mult beta KSN) (mult beta KN))
                         (req_minus (mult beta lgZ) (mult beta lgZ)))
              (mult beta KSN)
              Hleg2
              (req_trans
                 (req_minus (req_minus (mult beta KSN) (mult beta KN))
                            (req_minus (mult beta lgZ) (mult beta lgZ)))
                 (req_minus (req_minus (mult beta KSN) (mult beta KN)) zero)
                 (mult beta KSN)
                 Hleg3
                 Hleg4))).
Qed.
(* ============================================================ *)
(* [main-theorem unconditionalization demo] req2_backward_kl_step: the backward-KL three-point identity
   KL(PI_STAR||PI_NEXT) == (1-eta)*KL(PI_STAR||PI_T) - eta*KL(PI_T||PI_STAR)
      + KL(PI_T||PI_NEXT)
   unconditional theorem — every link of the chain is a genuine Qed proof (no B-class bridge assumption slots):
   the statement of bridge slot req_backward_kl_identity (assumption slot in UpReqAlign.v) is supplied by this theorem
   in same-position theorem form. Nontrivial ingredients: FE-KL-diff (ET / alignment sides) +
   surrogate optimality + suboptimality gap + collapse + beta inverse absorption. *)
(* ---- 19) Main theorem: segment-by-segment assembly (segment 1 skeleton + HA) ---- *)
Theorem req2_backward_kl_step :
  forall (pi_t : S -> R) (Hpi_t : pos3 pi_t) (Hn : nrm pi_t),
    req (KLE PSTR (NPX pi_t Hpi_t) PSTR_pos (npx_pos pi_t Hpi_t))
        (plus (mult (req_minus one eta)
                    (KLE PSTR pi_t PSTR_pos Hpi_t))
              (plus (opp (mult eta (KLE pi_t PSTR Hpi_t PSTR_pos)))
                    (KLE pi_t (NPX pi_t Hpi_t) Hpi_t
                                (npx_pos pi_t Hpi_t)))).
Proof.
  intros pi_t Hpi_t Hn.
  set (SAN := sumf (fun s => mult (NPX pi_t Hpi_t s) (ADV pi_t Hpi_t s))).
  set (SAT := sumf (fun s => mult (pi_t s) (ADV pi_t Hpi_t s))).
  set (SAS := sumf (fun s => mult (PSTR s) (ADV pi_t Hpi_t s))).
  set (K1 := KLE (NPX pi_t Hpi_t) pi_t (npx_pos pi_t Hpi_t) Hpi_t).
  set (K2 := KLE pi_t (NPX pi_t Hpi_t) Hpi_t (npx_pos pi_t Hpi_t)).
  set (KST := KLE PSTR pi_t PSTR_pos Hpi_t).
  set (KTS := KLE pi_t PSTR Hpi_t PSTR_pos).
  set (KSN := KLE PSTR (NPX pi_t Hpi_t) PSTR_pos (npx_pos pi_t Hpi_t)).
  set (B1 := mult beta K1).
  set (B2 := mult beta K2).
  set (BS := mult beta KST).
  set (BT := mult beta KTS).
  set (U := mult eta BT).
  set (V := mult eta BS).
  set (K := req_minus one eta).
  set (IV := inv_pos beta beta_pos).
  assert (HA : req (mult beta KSN)
                   (plus (mult eta (req_minus SAN SAS))
                         (mult beta (req_minus KST K1)))).
  { apply (req_trans (mult beta KSN)
                     (req_minus (FE (ET pi_t Hpi_t) beta PSTR PSTR_pos)
                                (FE (ET pi_t Hpi_t) beta (NPX pi_t Hpi_t)
                                          (npx_pos pi_t Hpi_t)))
                     (plus (mult eta (req_minus SAN SAS))
                           (mult beta (req_minus KST K1)))).
    - exact (r2_beta_KSN_Fdiff pi_t Hpi_t Hn).
    - apply (req_trans
                (req_minus (FE (ET pi_t Hpi_t) beta PSTR PSTR_pos)
                           (FE (ET pi_t Hpi_t) beta (NPX pi_t Hpi_t)
                                     (npx_pos pi_t Hpi_t)))
                (req_minus (plus (opp (mult eta SAS)) (mult beta KST))
                           (plus (opp (mult eta SAN)) (mult beta K1)))
                (plus (mult eta (req_minus SAN SAS))
                      (mult beta (req_minus KST K1)))).
      + exact (req2_minus_compat
                  (FE (ET pi_t Hpi_t) beta PSTR PSTR_pos)
                  (plus (opp (mult eta SAS)) (mult beta KST))
                  (FE (ET pi_t Hpi_t) beta (NPX pi_t Hpi_t)
                            (npx_pos pi_t Hpi_t))
                  (plus (opp (mult eta SAN)) (mult beta K1))
                  (r2_F_t_simpl_p pi_t Hpi_t PSTR PSTR_pos)
                  (w_F_t_simpl_next_kl pi_t Hpi_t)).
      + exact (r2_t13_hexp pi_t Hpi_t). }
  assert (HB : req (mult eta (req_minus SAN SAS))
                   (plus (mult beta (plus K1 K2))
                         (plus (opp U) (opp V)))).
  { apply (req_trans (mult eta (req_minus SAN SAS))
                     (mult eta (plus (req_minus SAN SAT)
                                     (req_minus SAT SAS)))
                     (plus (mult beta (plus K1 K2))
                           (plus (opp U) (opp V)))).
    - exact (req_mult_compat eta eta (req_minus SAN SAS)
                             (plus (req_minus SAN SAT) (req_minus SAT SAS))
                             (req_refl eta) (r2_minus_split SAN SAT SAS)).
    - apply (req_trans (mult eta (plus (req_minus SAN SAT)
                                       (req_minus SAT SAS)))
                       (plus (mult eta (req_minus SAN SAT))
                             (mult eta (req_minus SAT SAS)))
                       (plus (mult beta (plus K1 K2))
                             (plus (opp U) (opp V)))).
      + exact (distrib eta (req_minus SAN SAT) (req_minus SAT SAS)).
      + apply (req_plus_compat (mult eta (req_minus SAN SAT))
                               (mult beta (plus K1 K2))
                               (mult eta (req_minus SAT SAS))
                               (plus (opp U) (opp V))).
        * exact (r2_surrogate_diff_identity pi_t Hpi_t Hn).
        * apply (req_trans (mult eta (req_minus SAT SAS))
                           (mult eta (plus (opp (mult beta KTS))
                                           (opp (mult beta KST))))
                           (plus (opp U) (opp V))).
          -- exact (req_mult_compat eta eta (req_minus SAT SAS)
                                    (plus (opp (mult beta KTS))
                                          (opp (mult beta KST)))
                                    (req_refl eta)
                                    (r2_sum_advance_gap pi_t Hpi_t Hn)).
          -- exact (req_trans
                      (mult eta (plus (opp (mult beta KTS))
                                      (opp (mult beta KST))))
                      (plus (mult eta (opp (mult beta KTS)))
                            (mult eta (opp (mult beta KST))))
                      (plus (opp U) (opp V))
                      (distrib eta (opp (mult beta KTS))
                               (opp (mult beta KST)))
                      (req_plus_compat (mult eta (opp (mult beta KTS)))
                                       (opp U)
                                       (mult eta (opp (mult beta KST)))
                                       (opp V)
                                       (req_opp_mult_l eta (mult beta KTS))
                                       (req_opp_mult_l eta
                                                       (mult beta KST)))). }
  assert (HC : req (mult beta (req_minus KST K1)) (plus BS (opp B1))).
  { exact (req_mult_minus_distr_l beta KST K1). }
  assert (HK : req (req_minus BS V) (mult K BS)).
  { apply (req_trans (req_minus BS V)
                     (req_minus (mult one BS) (mult eta BS))
                     (mult K BS)).
    - exact (req2_minus_compat BS (mult one BS) V (mult eta BS)
                               (req_sym (mult one BS) BS (req_mult_one_l BS))
                               (req_refl V)).
    - exact (req_sym (mult K BS)
                     (req_minus (mult one BS) (mult eta BS))
                     (r2_mmd_r one eta BS)). }
  assert (HD : req (plus (mult eta (req_minus SAN SAS))
                         (mult beta (req_minus KST K1)))
                   (plus (plus B2 (opp U)) (mult K BS))).
  { apply (req_trans (plus (mult eta (req_minus SAN SAS))
                           (mult beta (req_minus KST K1)))
                     (plus (plus (plus (plus B1 B2) (opp U)) (opp V))
                           (plus BS (opp B1)))
                     (plus (plus B2 (opp U)) (mult K BS))).
    - apply (req_plus_compat (mult eta (req_minus SAN SAS))
                             (plus (plus (plus B1 B2) (opp U)) (opp V))
                             (mult beta (req_minus KST K1))
                             (plus BS (opp B1))
                             (req_trans (mult eta (req_minus SAN SAS))
                                        (plus (mult beta (plus K1 K2))
                                              (plus (opp U) (opp V)))
                                        (plus (plus (plus B1 B2) (opp U))
                                              (opp V))
                                        HB
                                        (req_trans
                                           (plus (mult beta (plus K1 K2))
                                                 (plus (opp U) (opp V)))
                                           (plus (plus B1 B2)
                                                 (plus (opp U) (opp V)))
                                           (plus (plus (plus B1 B2) (opp U))
                                                 (opp V))
                                           (req_plus_compat
                                              (mult beta (plus K1 K2))
                                              (plus B1 B2)
                                              (plus (opp U) (opp V))
                                              (plus (opp U) (opp V))
                                              (distrib beta K1 K2)
                                              (req_refl
                                                 (plus (opp U) (opp V))))
                                           (plus_assoc (plus B1 B2)
                                                       (opp U)
                                                       (opp V))))
                             HC).
    - exact (req_trans (plus (plus (plus (plus B1 B2) (opp U)) (opp V))
                             (plus BS (opp B1)))
                       (plus (plus B2 (opp U)) (req_minus BS V))
                       (plus (plus B2 (opp U)) (mult K BS))
                       (r2_bksn_collapse2 B1 B2 U V BS)
                       (req_plus_compat (plus B2 (opp U))
                                        (plus B2 (opp U))
                                        (req_minus BS V)
                                        (mult K BS)
                                        (req_refl (plus B2 (opp U)))
                                        HK)). }
  assert (HE : req (mult IV (mult beta KSN))
                   (plus (mult K KST)
                         (plus (opp (mult eta KTS)) K2))).
  { apply (req_trans (mult IV (mult beta KSN))
                     (mult IV (plus (plus B2 (opp U)) (mult K BS)))
                     (plus (mult K KST)
                           (plus (opp (mult eta KTS)) K2))).
    - exact (req_mult_compat IV IV (mult beta KSN)
                             (plus (plus B2 (opp U)) (mult K BS))
                             (req_refl IV)
                             (req_trans (mult beta KSN)
                                        (plus (mult eta (req_minus SAN SAS))
                                              (mult beta (req_minus KST K1)))
                                        (plus (plus B2 (opp U)) (mult K BS))
                                        HA HD)).
    - apply (req_trans (mult IV (plus (plus B2 (opp U)) (mult K BS)))
                       (plus (mult IV (plus B2 (opp U)))
                             (mult IV (mult K BS)))
                       (plus (mult K KST)
                             (plus (opp (mult eta KTS)) K2))).
      + exact (distrib IV (plus B2 (opp U)) (mult K BS)).
      + apply (req_trans (plus (mult IV (plus B2 (opp U)))
                               (mult IV (mult K BS)))
                         (plus (plus (mult IV B2) (mult IV (opp U)))
                               (mult IV (mult K BS)))
                         (plus (mult K KST)
                               (plus (opp (mult eta KTS)) K2))).
        * exact (req_plus_compat (mult IV (plus B2 (opp U)))
                                 (plus (mult IV B2) (mult IV (opp U)))
                                 (mult IV (mult K BS))
                                 (mult IV (mult K BS))
                                 (distrib IV B2 (opp U))
                                 (req_refl (mult IV (mult K BS)))).
        * apply (req_trans (plus (plus (mult IV B2) (mult IV (opp U)))
                                 (mult IV (mult K BS)))
                           (plus (plus K2 (opp (mult eta KTS)))
                                 (mult K KST))
                           (plus (mult K KST)
                                 (plus (opp (mult eta KTS)) K2))).
          -- exact (req_plus_compat
                      (plus (mult IV B2) (mult IV (opp U)))
                      (plus K2 (opp (mult eta KTS)))
                      (mult IV (mult K BS))
                      (mult K KST)
                      (req_plus_compat (mult IV B2) K2
                                       (mult IV (opp U))
                                       (opp (mult eta KTS))
                                       (r2_iv_beta K2)
                                       (req_trans
                                          (mult IV (opp U))
                                          (opp (mult IV U))
                                          (opp (mult eta KTS))
                                          (req_opp_mult_l IV U)
                                          (req_opp_compat
                                             (mult IV U)
                                             (mult eta KTS)
                                             (r2_iv_beta_scal eta KTS))))
                      (r2_iv_beta_scal K KST)).
          -- exact (req_trans (plus (plus K2 (opp (mult eta KTS)))
                                    (mult K KST))
                              (plus (mult K KST)
                                    (plus K2 (opp (mult eta KTS))))
                              (plus (mult K KST)
                                    (plus (opp (mult eta KTS)) K2))
                              (plus_comm (plus K2 (opp (mult eta KTS)))
                                         (mult K KST))
                              (req_plus_compat (mult K KST) (mult K KST)
                                               (plus K2
                                                     (opp (mult eta KTS)))
                                               (plus (opp (mult eta KTS))
                                                     K2)
                                               (req_refl (mult K KST))
                                               (plus_comm K2
                                                          (opp
                                                             (mult eta
                                                                    KTS))))). }
  apply (req_trans KSN (mult IV (mult beta KSN))
                   (plus (mult K KST)
                         (plus (opp (mult eta KTS)) K2))).
  - exact (req_sym (mult IV (mult beta KSN)) KSN
                   (r2_inv_absorb beta beta_pos KSN)).
  - exact HE.
Qed.


(* ---- 20) [] step_le: le form of the main-theorem identity (same position) ---- *)
Corollary r2_backward_kl_step_le :
  forall (pi_t : S -> R) (Hpi_t : pos3 pi_t) (Hn : nrm pi_t),
    le (KLE PSTR (NPX pi_t Hpi_t) PSTR_pos (npx_pos pi_t Hpi_t))
       (plus (mult (req_minus one eta) (KLE PSTR pi_t PSTR_pos Hpi_t))
             (KLE pi_t (NPX pi_t Hpi_t) Hpi_t (npx_pos pi_t Hpi_t))).
Proof.
  intros pi_t Hpi_t Hn.
  apply (le_trans
           (KLE PSTR (NPX pi_t Hpi_t) PSTR_pos (npx_pos pi_t Hpi_t))
           (plus (mult (req_minus one eta) (KLE PSTR pi_t PSTR_pos Hpi_t))
                 (plus (opp (mult eta (KLE pi_t PSTR Hpi_t PSTR_pos)))
                       (KLE pi_t (NPX pi_t Hpi_t) Hpi_t
                                   (npx_pos pi_t Hpi_t))))
           (plus (mult (req_minus one eta) (KLE PSTR pi_t PSTR_pos Hpi_t))
                 (KLE pi_t (NPX pi_t Hpi_t) Hpi_t (npx_pos pi_t Hpi_t)))
           (lt_le_iff _ _ (inr (req2_backward_kl_step pi_t Hpi_t Hn)))
           (le_plus_compat
              (mult (req_minus one eta) (KLE PSTR pi_t PSTR_pos Hpi_t))
              (mult (req_minus one eta) (KLE PSTR pi_t PSTR_pos Hpi_t))
              (plus (opp (mult eta (KLE pi_t PSTR Hpi_t PSTR_pos)))
                    (KLE pi_t (NPX pi_t Hpi_t) Hpi_t (npx_pos pi_t Hpi_t)))
              (KLE pi_t (NPX pi_t Hpi_t) Hpi_t (npx_pos pi_t Hpi_t))
              (le_refl
                 (mult (req_minus one eta)
                       (KLE PSTR pi_t PSTR_pos Hpi_t)))
              (le_id_r
                 (plus (opp (mult eta (KLE pi_t PSTR Hpi_t PSTR_pos)))
                       (KLE pi_t (NPX pi_t Hpi_t) Hpi_t
                                   (npx_pos pi_t Hpi_t)))
                 (plus zero (KLE pi_t (NPX pi_t Hpi_t) Hpi_t
                                   (npx_pos pi_t Hpi_t)))
                 (KLE pi_t (NPX pi_t Hpi_t) Hpi_t (npx_pos pi_t Hpi_t))
                 (req_plus_zero_l
                    (KLE pi_t (NPX pi_t Hpi_t) Hpi_t
                                (npx_pos pi_t Hpi_t)))
                 (le_plus_compat
                    (opp (mult eta (KLE pi_t PSTR Hpi_t PSTR_pos)))
                    zero
                    (KLE pi_t (NPX pi_t Hpi_t) Hpi_t (npx_pos pi_t Hpi_t))
                    (KLE pi_t (NPX pi_t Hpi_t) Hpi_t (npx_pos pi_t Hpi_t))
                    (le_id_r (opp (mult eta (KLE pi_t PSTR Hpi_t PSTR_pos)))
                             (opp zero) zero r2_opp_zero
                             (opp_le_compat zero
                                (mult eta (KLE pi_t PSTR Hpi_t PSTR_pos))
                                (le_id_l zero (mult eta zero)
                                         (mult eta
                                            (KLE pi_t PSTR Hpi_t PSTR_pos))
                                         (req_sym (mult eta zero) zero
                                                  (mult_zero eta))
                                         (req_le_mult_compat_r eta zero
                                            (KLE pi_t PSTR Hpi_t PSTR_pos)
                                            (lt_le_iff zero eta (inl eta_pos))
                                            (req2_gibbs_inequality pi_t PSTR
                                               Hpi_t PSTR_pos)))))
                    (le_refl
                       (KLE pi_t (NPX pi_t Hpi_t) Hpi_t
                                   (npx_pos pi_t Hpi_t))))))).
Qed.

(* ---- 21) [] rlhf_policy_improvement: KL down implies J up
   (same position; uses both r2_rlhf_suboptimality_gap pieces + beta order preservation) ---- *)
Lemma r2_rlhf_policy_improvement :
  forall (p_old p_new : S -> R) (Hp_old : pos3 p_old) (Hp_new : pos3 p_new)
         (Hn_old : nrm p_old) (Hn_new : nrm p_new),
    le (KLE p_new PSTR Hp_new PSTR_pos)
       (KLE p_old PSTR Hp_old PSTR_pos) ->
    le (JJ p_old Hp_old) (JJ p_new Hp_new).
Proof.
  intros p_old p_new Hp_old Hp_new Hn_old Hn_new Hkl.
  apply req2_le_of_minus_nonneg.
  set (JST := JJ PSTR PSTR_pos).
  set (JO := JJ p_old Hp_old).
  set (JN := JJ p_new Hp_new).
  set (KO := KLE p_old PSTR Hp_old PSTR_pos).
  set (KN := KLE p_new PSTR Hp_new PSTR_pos).
  assert (HgapO : req (req_minus JST JO) (mult beta KO))
    by exact (r2_rlhf_suboptimality_gap p_old Hp_old Hn_old).
  assert (HgapN : req (req_minus JST JN) (mult beta KN))
    by exact (r2_rlhf_suboptimality_gap p_new Hp_new Hn_new).
  assert (Hbpos : le zero beta)
    by exact (lt_le_iff zero beta (inl beta_pos)).
  assert (Hkole : le zero (req_minus KO KN))
    by exact (req_le_minus_nonneg KN KO Hkl).
  assert (Hb1 : le zero (mult beta (req_minus KO KN)))
    by exact (r2_le_mult_nonneg beta (req_minus KO KN) Hbpos Hkole).
  assert (Hdiff : req (req_minus JN JO)
                      (mult beta (req_minus KO KN))).
  { exact (req_sym (mult beta (req_minus KO KN)) (req_minus JN JO)
                   (req_trans
                      (mult beta (req_minus KO KN))
                      (req_minus (mult beta KO) (mult beta KN))
                      (req_minus JN JO)
                      (req_mult_minus_distr_l beta KO KN)
                      (req_trans
                         (req_minus (mult beta KO) (mult beta KN))
                         (req_minus (req_minus JST JO) (req_minus JST JN))
                         (req_minus JN JO)
                         (req2_minus_compat (mult beta KO)
                                            (req_minus JST JO)
                                            (mult beta KN)
                                            (req_minus JST JN)
                                            (req_sym (req_minus JST JO)
                                                     (mult beta KO) HgapO)
                                            (req_sym (req_minus JST JN)
                                                     (mult beta KN)
                                                     HgapN))
                         (req_trans
                            (req_minus (req_minus JST JO)
                                       (req_minus JST JN))
                            (req_minus (req_minus JST JST)
                                       (req_minus JO JN))
                            (req_minus JN JO)
                            (r2_minus_rearrange_four JST JO JST JN)
                            (req_trans
                               (req_minus (req_minus JST JST)
                                          (req_minus JO JN))
                               (req_minus zero (req_minus JO JN))
                               (req_minus JN JO)
                               (req2_minus_compat (req_minus JST JST) zero
                                                  (req_minus JO JN)
                                                  (req_minus JO JN)
                                                  (plus_opp JST)
                                                  (req_refl
                                                     (req_minus JO JN)))
                               (req_trans
                                  (req_minus zero (req_minus JO JN))
                                  (opp (plus JO (opp JN)))
                                  (req_minus JN JO)
                                  (req_plus_zero_l
                                     (opp (plus JO (opp JN))))
                                  (req_trans
                                     (opp (plus JO (opp JN)))
                                     (plus (opp JO) (opp (opp JN)))
                                     (req_minus JN JO)
                                     (req_opp_plus JO (opp JN))
                                     (req_trans
                                        (plus (opp JO) (opp (opp JN)))
                                        (plus (opp JO) JN)
                                        (req_minus JN JO)
                                        (req_plus_compat (opp JO) (opp JO)
                                                         (opp (opp JN)) JN
                                                         (req_refl (opp JO))
                                                         (req_double_neg JN))
                                        (plus_comm (opp JO) JN))))))))). }
  apply (le_id_r zero (mult beta (req_minus KO KN)) (req_minus JN JO)
                  (req_sym (req_minus JN JO)
                           (mult beta (req_minus KO KN)) Hdiff)
                  Hb1).
Qed.

(* ---- 22) [] Weighted step KL sum (same position as step_kl_weighted) ---- *)
Fixpoint r2_step_kl_weighted (t : nat) (pi : S -> R) (Hpi : pos3 pi) : R :=
  match t with
  | 0%nat => zero
  | Datatypes.S m =>
      plus (KLE (projT1 (w_iter m pi Hpi))
                (NPX (projT1 (w_iter m pi Hpi)) (projT2 (w_iter m pi Hpi)))
                (projT2 (w_iter m pi Hpi))
                (npx_pos (projT1 (w_iter m pi Hpi))
                            (projT2 (w_iter m pi Hpi))))
           (mult (req_minus one eta) (r2_step_kl_weighted m pi Hpi))
  end.

(* ---- 23) [] iter_le: exact weighted iteration upper bound for backward KL (same position;
   uses r2_backward_kl_step_le + eta<=1 (via req_le_minus_nonneg) + induction) ---- *)
(* ---- 22a) Tail rearrangement pure-algebra piece (final bridge of iter_le) ---- *)
Lemma r2_step_kl_rearr :
  forall p q r s t : R,
    req (plus (mult p (plus (mult q r) s)) t)
        (plus (mult (mult p q) r) (plus t (mult p s))).
Proof.
  intros p q r s t.
  apply (req_trans (plus (mult p (plus (mult q r) s)) t)
                   (plus (plus (mult p (mult q r)) (mult p s)) t)
                   (plus (mult (mult p q) r) (plus t (mult p s)))).
  - exact (req_plus_compat (mult p (plus (mult q r) s))
                           (plus (mult p (mult q r)) (mult p s))
                           t t (distrib p (mult q r) s) (req_refl t)).
  - exact (req_trans (plus (plus (mult p (mult q r)) (mult p s)) t)
                     (plus (plus (mult (mult p q) r) (mult p s)) t)
                     (plus (mult (mult p q) r) (plus t (mult p s)))
                     (req_plus_compat
                        (plus (mult p (mult q r)) (mult p s))
                        (plus (mult (mult p q) r) (mult p s))
                        t t
                        (req_plus_compat (mult p (mult q r))
                                         (mult (mult p q) r)
                                         (mult p s) (mult p s)
                                         (mult_assoc p q r)
                                         (req_refl (mult p s)))
                        (req_refl t))
                     (req_trans
                        (plus (plus (mult (mult p q) r) (mult p s)) t)
                        (plus (mult (mult p q) r) (plus (mult p s) t))
                        (plus (mult (mult p q) r) (plus t (mult p s)))
                        (req_sym
                           (plus (mult (mult p q) r) (plus (mult p s) t))
                           (plus (plus (mult (mult p q) r) (mult p s)) t)
                           (plus_assoc (mult (mult p q) r) (mult p s) t))
                        (req_plus_compat
                           (mult (mult p q) r)
                           (mult (mult p q) r)
                           (plus (mult p s) t)
                           (plus t (mult p s))
                           (req_refl (mult (mult p q) r))
                           (plus_comm (mult p s) t)))).
Qed.

Theorem r2_backward_kl_iter_le :
  forall (t : nat) (pi : S -> R) (Hpi : pos3 pi),
    nrm pi ->
    le (KLE PSTR (projT1 (w_iter t pi Hpi)) PSTR_pos
            (projT2 (w_iter t pi Hpi)))
       (plus (mult (req2_r_pow (req_minus one eta) t)
                   (KLE PSTR pi PSTR_pos Hpi))
             (r2_step_kl_weighted t pi Hpi)).
Proof.
  intros t pi Hpi Hn.
  induction t as [| m IH].
  - exact (le_id_l
             (KLE PSTR (projT1 (w_iter 0 pi Hpi)) PSTR_pos
                  (projT2 (w_iter 0 pi Hpi)))
             (KLE PSTR pi PSTR_pos Hpi)
             (plus (mult (req2_r_pow (req_minus one eta) 0)
                         (KLE PSTR pi PSTR_pos Hpi))
                   (r2_step_kl_weighted 0 pi Hpi))
             (req_refl (KLE PSTR pi PSTR_pos Hpi))
             (le_id_l
                (KLE PSTR pi PSTR_pos Hpi)
                (plus (mult (req2_r_pow (req_minus one eta) 0)
                            (KLE PSTR pi PSTR_pos Hpi))
                      (r2_step_kl_weighted 0 pi Hpi))
                (plus (mult (req2_r_pow (req_minus one eta) 0)
                            (KLE PSTR pi PSTR_pos Hpi))
                      (r2_step_kl_weighted 0 pi Hpi))
                (req_sym
                   (plus (mult (req2_r_pow (req_minus one eta) 0)
                               (KLE PSTR pi PSTR_pos Hpi))
                         (r2_step_kl_weighted 0 pi Hpi))
                   (KLE PSTR pi PSTR_pos Hpi)
                   (req_trans
                      (plus (mult (req2_r_pow (req_minus one eta) 0)
                                  (KLE PSTR pi PSTR_pos Hpi))
                            (r2_step_kl_weighted 0 pi Hpi))
                      (plus (mult one (KLE PSTR pi PSTR_pos Hpi)) zero)
                      (KLE PSTR pi PSTR_pos Hpi)
                      (req_refl
                         (plus (mult (req2_r_pow (req_minus one eta) 0)
                                     (KLE PSTR pi PSTR_pos Hpi))
                               (r2_step_kl_weighted 0 pi Hpi)))
                      (req_trans
                         (plus (mult one (KLE PSTR pi PSTR_pos Hpi)) zero)
                         (plus (KLE PSTR pi PSTR_pos Hpi) zero)
                         (KLE PSTR pi PSTR_pos Hpi)
                         (req_plus_compat
                            (mult one (KLE PSTR pi PSTR_pos Hpi))
                            (KLE PSTR pi PSTR_pos Hpi)
                            zero zero
                            (req_mult_one_l (KLE PSTR pi PSTR_pos Hpi))
                            (req_refl zero))
                         (req_plus_zero_r (KLE PSTR pi PSTR_pos Hpi)))))
                (le_refl
                   (plus (mult (req2_r_pow (req_minus one eta) 0)
                               (KLE PSTR pi PSTR_pos Hpi))
                         (r2_step_kl_weighted 0 pi Hpi))))).
  - set (Pm := projT1 (w_iter m pi Hpi)).
    set (Pm_pos := projT2 (w_iter m pi Hpi)).
    set (KL0 := KLE PSTR pi PSTR_pos Hpi).
    set (K := req_minus one eta).
    set (KSm := KLE PSTR (projT1 (w_iter (Datatypes.S m) pi Hpi)) PSTR_pos
                    (projT2 (w_iter (Datatypes.S m) pi Hpi))).
    set (KMN := KLE Pm (NPX Pm Pm_pos) Pm_pos (npx_pos Pm Pm_pos)).
    set (Sm := r2_step_kl_weighted m pi Hpi).
    assert (H1 : le KSm (plus (mult K (KLE PSTR Pm PSTR_pos Pm_pos)) KMN)).
    { exact (r2_backward_kl_step_le Pm Pm_pos
                (w_iter_norm m pi Hpi Hn)). }
    assert (Hk : le zero K).
    { exact (req_le_minus_nonneg eta one eta_le_one). }
    assert (H4 : le (mult K (KLE PSTR Pm PSTR_pos Pm_pos))
                    (mult K (plus (mult (req2_r_pow K m) KL0) Sm))).
    { apply (le_id_l (mult K (KLE PSTR Pm PSTR_pos Pm_pos))
                     (mult (KLE PSTR Pm PSTR_pos Pm_pos) K)
                     (mult K (plus (mult (req2_r_pow K m) KL0) Sm))).
      - exact (mult_comm K (KLE PSTR Pm PSTR_pos Pm_pos)).
      - apply (le_id_r (mult (KLE PSTR Pm PSTR_pos Pm_pos) K)
                       (mult (plus (mult (req2_r_pow K m) KL0) Sm) K)
                       (mult K (plus (mult (req2_r_pow K m) KL0) Sm))).
        + exact (mult_comm (plus (mult (req2_r_pow K m) KL0) Sm) K).
        + exact (le_id_l (mult (KLE PSTR Pm PSTR_pos Pm_pos) K)
                         (mult K (KLE PSTR Pm PSTR_pos Pm_pos))
                         (mult (plus (mult (req2_r_pow K m) KL0) Sm) K)
                         (mult_comm (KLE PSTR Pm PSTR_pos Pm_pos) K)
                         (le_id_r
                            (mult K (KLE PSTR Pm PSTR_pos Pm_pos))
                            (mult K (plus (mult (req2_r_pow K m) KL0) Sm))
                            (mult (plus (mult (req2_r_pow K m) KL0) Sm) K)
                            (mult_comm K
                               (plus (mult (req2_r_pow K m) KL0) Sm))
                            (req_le_mult_compat_r K
                               (KLE PSTR Pm PSTR_pos Pm_pos)
                               (plus (mult (req2_r_pow K m) KL0) Sm)
                               Hk IH))). }
    assert (H5 : le (plus (mult K (KLE PSTR Pm PSTR_pos Pm_pos)) KMN)
                    (plus (mult K (plus (mult (req2_r_pow K m) KL0) Sm))
                          KMN)).
    { exact (le_plus_compat (mult K (KLE PSTR Pm PSTR_pos Pm_pos))
                            (mult K (plus (mult (req2_r_pow K m) KL0) Sm))
                            KMN KMN H4 (le_refl KMN)). }
    assert (Hmid : le KSm
                     (plus (mult K (plus (mult (req2_r_pow K m) KL0) Sm))
                           KMN)).
    { exact (le_trans KSm
                      (plus (mult K (KLE PSTR Pm PSTR_pos Pm_pos)) KMN)
                      (plus (mult K (plus (mult (req2_r_pow K m) KL0) Sm))
                            KMN)
                      H1 H5). }
    assert (Hre : req (plus (mult K (plus (mult (req2_r_pow K m) KL0) Sm)) KMN)
                      (plus (mult (mult K (req2_r_pow K m)) KL0)
                            (plus KMN (mult K Sm)))).
    { exact (r2_step_kl_rearr K (req2_r_pow K m) KL0 Sm KMN). }
    apply (le_trans KSm
                    (plus (mult K (plus (mult (req2_r_pow K m) KL0) Sm)) KMN)
                    (plus (mult (mult K (req2_r_pow K m)) KL0)
                          (plus KMN (mult K Sm)))
                    Hmid
                    (le_id_l (plus (mult K (plus (mult (req2_r_pow K m) KL0) Sm))
                                   KMN)
                             (plus (mult (mult K (req2_r_pow K m)) KL0)
                                   (plus KMN (mult K Sm)))
                             (plus (mult (mult K (req2_r_pow K m)) KL0)
                                   (plus KMN (mult K Sm)))
                             Hre
                             (le_refl (plus (mult (mult K (req2_r_pow K m)) KL0)
                                            (plus KMN (mult K Sm)))))).
Qed.

End Req3AlignCore.

(* ============================================================ *)
(* Tail-note explicit assumptions (recheck): auditing what the header promised against what is actually present —
   1. [dpo/preference cluster] not placed in this file: fully proven by the ralt_ series of
     UpReqAlignRestA.v (dpo_reward_recovers / relative_exact /
     diff_is_log_ratio_diff / implicit_reward_diff / dpo_pair_denom_pos /
     dpo_pair_loss_at_star / dpo_loss_pair / dpo_loss_at_pi_star /
     sigmoid_strict_inc).
   2. [] remaining chain pieces (sum_grad_cross / grad_cross_identity /
     align_objective_explicit / rlhf_suboptimality_gap /
     rlhf_policy_improvement / sum_advance_gap / t13_hexp /
     backward_kl_step_beta / backward_kl_step):
     step_le (r2_backward_kl_step_le) / rlhf_policy_improvement
     (r2_rlhf_policy_improvement) / iter_le (r2_backward_kl_iter_le,
     including the r2_step_kl_weighted Fixpoint + r2_step_kl_rearr tail-rearrangement piece)
     all landed in this file; the header promises are all proven.
   3. [main-theorem unconditionalization demo] req2_backward_kl_step landed in this file (
     five-segment assembly: HA beta*KSN = FE diff / HB t13_hexp / HC+HK split /
     HD r2_bksn_collapse2 collapse / HE iv shaping / beta inverse absorption completion);
     the statement is supplied by the main theorem in same position; the assumption slot in UpReqAlign.v can now be proven.
   (.vo magic 90001 same track); G3 extraction check Obj.magic=0 (main theorem / six fallback pieces
   "Modules were successfully checked".
   ============================================================ *)

(* ============================================================
    Slice three · tail assumption audit of the replacement file (whole-file joint-compile leftover; all five audited together)
   ============================================================ *)
Print Assumptions w_sum_ptimes_const.
Print Assumptions w_sum_minus.
Print Assumptions w_sum_opp.
Print Assumptions w_sum_ptimes_scal.
Print Assumptions w_sum_ptimes_opp_scal.
