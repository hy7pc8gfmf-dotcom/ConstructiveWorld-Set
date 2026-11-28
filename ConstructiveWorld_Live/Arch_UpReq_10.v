(* ========================================================================= *)
(* Module   : Arch_UpReq_10                                                 *)
(* Mission. Statement families of the PPO/RLHF alignment cluster and the      *)
(*            log-depth decay selector: state_value_req, advantage_req,       *)
(*            kl_to_ref_req, rppo_pistar, rppo_pistar_pos, policy_ratio_req,  *)
(*            the sum machine (rppo_opp_one_mult, rppo_sum_opp,               *)
(*            rppo_sum_minus), the alignment-objective decomposition cluster, *)
(*            the Q-carried selector mixd_k_select_log_cert with its          *)
(*            certificates and accounts, and mixd_k_select_log.               *)
(* Dependencies. S01_BaseRing through S15_TailFEPUp, UpReqAlgebra,            *)
(*            UpReqAlign, UpReqIterGeomRate, UpTVDoeblin, UpReqMixingTime,    *)
(*            KLWallClosed of this development; Stdlib ZArith, QArith, Lia.   *)
(* References. Arch_UpReq_10.v, the baseline module of ConstructiveWorld-Main *)
(*            whose statement names are carried over verbatim with            *)
(*            statement-face Set-carrier completion (UpReqAlign /             *)
(*            UpReqAlgebra consumed as landed).                               *)
(* Constructivity. Every statement face is Set-carried: real_eq / real_lt /   *)
(*            real_le, decidable QeqT / QltT / QleT', NatLe, the Set-level    *)
(*            And of S01; the only Prop inside a Set carrier is the S02       *)
(*            existing-form mirror (real_lt embeds sigT/And over QltT,        *)
(*            real_le embeds Or over real_lt/real_eq), consumed as landed;    *)
(*            Prop otherwise appears only inside proof bodies.  Zero axioms,  *)
(*            zero admissions; carriers are transparent (term-form or        *)
(*            Defined, incl. every certificate producer consumed by a        *)
(*            Definition); Qed is confined to Prop-derivation bridge         *)
(*            lemmas that never enter a Definition body.                     *)
(* Build. rocq c -native-compiler no -q -Q <this development root> ""         *)
(*            Arch_UpReq_10.v (single shot); the artifact starts with         *)
(*            436f7121 00015ff4.                                              *)
(* ========================================================================= *)

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
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
Require Import UpReqIterGeomRate.
Require Import UpTVDoeblin.
Require Import UpReqMixingTime.
Require Import KLWallClosed.

(* ================= Section 1: the state_value_req family ================= *)
Import RealInterfaceEnhancedMod.

(* ReqPPOAdvantage: the PPO/advantage cluster request body. *)
Section ReqPPOAdvantage.
Variable S : Set.

(* SumOver interface docking surface (UpReqAlign ReqAlignCore same shape). *)
Variable sumf : (S -> Real) -> Real.
Hypothesis sum_ext :
  forall f g : S -> Real, (forall s : S, real_eq (f s) (g s)) -> real_eq (sumf f) (sumf g).
Hypothesis sum_add :
  forall f g : S -> Real,
    real_eq (sumf (fun s => plus (f s) (g s))) (plus (sumf f) (sumf g)).
Hypothesis sum_linear :
  forall (a : Real) (f : S -> Real),
    real_eq (sumf (fun s => mult a (f s))) (mult a (sumf f)).

(* pi_star_req canonical-signature slot: sum_pos threaded first, per the    *)
(* Z_align_pos derivation of UpReqAlign.                                    *)
Hypothesis rppo_sum_pos :
  forall f : S -> Real, (forall s : S, real_lt zero (f s)) -> real_lt zero (sumf f).

Hypothesis rppo_log_req_compat :
  forall (x y : Real) (Hx : real_lt zero x) (Hy : real_lt zero y),
    real_eq x y -> real_eq (log x Hx) (log y Hy).

(* Section parameters. *)
Variable reward : S -> Real.
Variable beta : Real.
Variable beta_pos : real_lt zero beta.
Variable pi_ref : S -> Real.
Variable pi_ref_pos : forall s : S, real_lt zero (pi_ref s).
Variable pi_ref_norm : real_eq (sumf pi_ref) one.
(* The partition-function positivity slot is derived, not premised:         *)
(* UpReqAlign proves Z_align_pos from sum_pos + pi_ref_pos.                 *)
Definition Zap : real_lt zero (Z_align_req S sumf reward beta beta_pos pi_ref) :=
  Z_align_pos S sumf rppo_sum_pos reward beta beta_pos pi_ref pi_ref_pos.

(* real_eq-system in-section definitions. *)
Definition state_value_req (p : S -> Real) : Real :=
  sumf (fun s => mult (p s) (reward s)).
Definition advantage_req (p : S -> Real) (s : S) : Real :=
  req_minus (reward s) (state_value_req p).
Definition kl_to_ref_req (p : S -> Real) (Hp : pos_dist S p) : Real :=
  relative_entropy_req S sumf p pi_ref Hp pi_ref_pos.
Definition rppo_pistar (s : S) : Real :=
  pi_star_req S sumf rppo_sum_pos reward beta beta_pos pi_ref pi_ref_pos s.
Definition rppo_pistar_pos (s : S) : real_lt zero (rppo_pistar s) :=
  req_pi_star_pos S sumf rppo_sum_pos reward beta beta_pos pi_ref pi_ref_pos s.
Definition policy_ratio_req (pi p_old : S -> Real) (s : S) (Hpos : real_lt zero (p_old s)) : Real :=
  mult (pi s) (inv_pos (p_old s) Hpos).

(* ============ Sum machine (inner machines rppo_sum_star family) ============ *)

(* Inner machine 0: mult (opp 1) * x == opp x. *)
Lemma rppo_opp_one_mult : forall x : Real, real_eq (mult (opp one) x) (opp x).
Proof.
  intro x.
  apply (req_trans (mult (opp one) x) (opp (mult one x)) (opp x)).
  - exact (req_opp_mult_r one x).
  - apply (req_opp_compat (mult one x) x). apply req_mult_one_l.
Qed.

(* Inner machine 1: sum opp f == opp sum f. *)
Lemma rppo_sum_opp :
  forall f : S -> Real, real_eq (sumf (fun s => opp (f s))) (opp (sumf f)).
Proof.
  intro f.
  apply (req_trans (sumf (fun s => opp (f s)))
                   (sumf (fun s => mult (opp one) (f s)))
                   (opp (sumf f))).
  - apply (sum_ext (fun s => opp (f s)) (fun s => mult (opp one) (f s))).
    intro s. apply (req_sym (mult (opp one) (f s)) (opp (f s))).
    exact (rppo_opp_one_mult (f s)).
  - apply (req_trans (sumf (fun s => mult (opp one) (f s)))
                     (mult (opp one) (sumf f))
                     (opp (sumf f))).
    + apply (sum_linear (opp one) f).
    + exact (rppo_opp_one_mult (sumf f)).
Qed.

(* Inner machine 2: sum (f - g) == sum f - sum g. *)
Lemma rppo_sum_minus :
  forall f g : S -> Real,
    real_eq (sumf (fun s => req_minus (f s) (g s))) (req_minus (sumf f) (sumf g)).
Proof.
  intros f g.
  unfold req_minus.
  apply (req_trans (sumf (fun s => plus (f s) (opp (g s))))
                   (plus (sumf f) (sumf (fun s => opp (g s))))
                   (plus (sumf f) (opp (sumf g)))).
  - apply sum_add.
  - apply (req_plus_compat (sumf f) (sumf f)
                           (sumf (fun s => opp (g s))) (opp (sumf g))
                           (req_refl (sumf f)) (rppo_sum_opp g)).
Qed.

(* Inner machine 3: KL(p,p) == 0 (pointwise req_minus self-zero + sum-zero collapse). *)
Lemma rppo_KL_self_zero :
  forall (p : S -> Real) (Hp : pos_dist S p),
    real_eq (relative_entropy_req S sumf p p Hp Hp) zero.
Proof.
  intros p Hp.
  apply (req_trans (relative_entropy_req S sumf p p Hp Hp)
                   (sumf (fun _ : S => zero)) zero).
  - apply (sum_ext (fun s => mult (p s) (req_minus (log (p s) (Hp s)) (log (p s) (Hp s))))
                   (fun _ : S => zero)).
    intro s.
    apply (req_trans (mult (p s) (req_minus (log (p s) (Hp s)) (log (p s) (Hp s))))
                     (mult (p s) zero) zero).
    + apply (req_mult_compat (p s) (p s)
                             (req_minus (log (p s) (Hp s)) (log (p s) (Hp s))) zero
                             (req_refl (p s))).
      unfold req_minus. apply plus_opp.
    + apply mult_zero.
  - apply (req_trans (sumf (fun _ : S => zero))
                     (sumf (fun s => mult zero (p s))) zero).
    + apply (sum_ext (fun _ : S => zero) (fun s => mult zero (p s))).
      intro s.
      exact (req_sym (mult zero (p s)) zero
                     (req_trans (mult zero (p s)) (mult (p s) zero) zero
                                (mult_comm zero (p s)) (mult_zero (p s)))).
    + apply (req_trans (sumf (fun s => mult zero (p s)))
                       (mult zero (sumf p)) zero).
      * apply (sum_linear zero p).
      * apply (req_trans (mult zero (sumf p)) (mult (sumf p) zero) zero).
        -- apply mult_comm.
        -- apply mult_zero.
Qed.

(* Inner machine 4: sum p*c == c (constant extraction + normalization collapse). *)
Lemma rppo_constant_sum :
  forall (c : Real) (p : S -> Real),
    real_eq (sumf p) one -> real_eq (sumf (fun s => mult (p s) c)) c.
Proof.
  intros c p Hnorm.
  apply (req_trans (sumf (fun s => mult (p s) c))
                   (mult c (sumf p)) c).
  - apply (req_trans (sumf (fun s => mult (p s) c))
                     (sumf (fun s => mult c (p s)))
                     (mult c (sumf p))).
    + apply (sum_ext (fun s => mult (p s) c) (fun s => mult c (p s))).
      intro s. apply req_mult_comm_rewrite.
    + apply (sum_linear c (fun s => p s)).
  - apply (req_trans (mult c (sumf p)) (mult c one) c).
    + apply (req_mult_compat c c (sumf p) one (req_refl c) Hnorm).
    + apply req_mult_one_r.
Qed.

(* Inner machine 6: x + opp(y + x) == opp y (collapse engine). *)
Lemma rppo_plus_opp_plus_r : forall x y : Real,
  real_eq (plus x (opp (plus y x))) (opp y).
Proof.
  intros x y.
  apply (req_trans (plus x (opp (plus y x)))
                   (plus x (plus (opp y) (opp x)))
                   (opp y)).
  - apply (req_plus_compat x x (opp (plus y x)) (plus (opp y) (opp x)) (req_refl x)).
    apply (req_opp_plus y x).
  - apply (req_trans (plus x (plus (opp y) (opp x)))
                     (plus (plus x (opp x)) (opp y))
                     (opp y)).
    + apply (req_trans (plus x (plus (opp y) (opp x)))
                       (plus x (plus (opp x) (opp y)))
                       (plus (plus x (opp x)) (opp y))).
      * apply (req_plus_compat x x (plus (opp y) (opp x)) (plus (opp x) (opp y))
                               (req_refl x) (plus_comm (opp y) (opp x))).
      * apply plus_assoc.
    + apply (req_trans (plus (plus x (opp x)) (opp y))
                       (plus zero (opp y))
                       (opp y)).
      * apply (req_plus_compat (plus x (opp x)) zero (opp y) (opp y)
                               (plus_opp x) (req_refl (opp y))).
      * apply (req_trans (plus zero (opp y)) (plus (opp y) zero) (opp y)).
        -- apply plus_comm.
        -- apply plus_zero.
Qed.

(* Inner machine 5: advantage sum, sum pi*A_ref == V(pi) - V(pi_ref) (normalized face). *)
Lemma rppo_advantage_sum_ref :
  forall (pi : S -> Real),
    real_eq (sumf pi) one ->
    real_eq (sumf (fun s => mult (pi s) (advantage_req pi_ref s)))
        (req_minus (state_value_req pi) (state_value_req pi_ref)).
Proof.
  intros pi Hnorm.
  apply (req_trans (sumf (fun s => mult (pi s) (advantage_req pi_ref s)))
                   (sumf (fun s => req_minus (mult (pi s) (reward s))
                                             (mult (pi s) (state_value_req pi_ref))))
                   (req_minus (state_value_req pi) (state_value_req pi_ref))).
  - apply (sum_ext (fun s => mult (pi s) (advantage_req pi_ref s))
                   (fun s => req_minus (mult (pi s) (reward s))
                                       (mult (pi s) (state_value_req pi_ref)))).
    intro s. unfold advantage_req. apply req_mult_minus_distr_l.
  - apply (req_trans (sumf (fun s => req_minus (mult (pi s) (reward s))
                                               (mult (pi s) (state_value_req pi_ref))))
                     (req_minus (sumf (fun s => mult (pi s) (reward s)))
                                (sumf (fun s => mult (pi s) (state_value_req pi_ref))))
                     (req_minus (state_value_req pi) (state_value_req pi_ref))).
    + apply rppo_sum_minus.
    + apply (req_plus_compat (state_value_req pi) (state_value_req pi)
                             (opp (sumf (fun s => mult (pi s) (state_value_req pi_ref))))
                             (opp (state_value_req pi_ref))
                             (req_refl (state_value_req pi))).
      apply (req_opp_compat (sumf (fun s => mult (pi s) (state_value_req pi_ref)))
                            (state_value_req pi_ref)).
      exact (rppo_constant_sum (state_value_req pi_ref) pi Hnorm).
Qed.

(* ============ Block 1: dpo_reward + advantage expectation cluster ============ *)

(* Item 1 dpo_reward_is_implicit: idempotent delta duality, log premise face. *)
Definition dpo_reward_explicit_req (pi : S -> Real) (Hpi : pos_dist S pi) (s : S) : Real :=
  mult beta (req_minus (log (pi s) (Hpi s)) (log (pi_ref s) (pi_ref_pos s))).
Definition dpo_implicit_reward_req (pi : S -> Real) (Hpi : pos_dist S pi) (s : S) : Real :=
  mult beta (req_minus (log (pi s) (Hpi s)) (log (pi_ref s) (pi_ref_pos s))).

Lemma rppo_dpo_reward_is_implicit :
  forall (pi : S -> Real) (Hpi : pos_dist S pi) (s : S),
    real_eq (dpo_reward_explicit_req pi Hpi s) (dpo_implicit_reward_req pi Hpi s).
Proof.
  intros pi Hpi s.
  unfold dpo_reward_explicit_req, dpo_implicit_reward_req.
  exact (req_refl (mult beta (req_minus (log (pi s) (Hpi s))
                                          (log (pi_ref s) (pi_ref_pos s))))).
Qed.

(* Item 2 advantage_expectation_zero: sum pi*A_pi == 0. *)
Lemma rppo_advantage_expectation_zero :
  forall (pi : S -> Real),
    real_eq (sumf pi) one ->
    real_eq (sumf (fun s => mult (pi s) (advantage_req pi s))) zero.
Proof.
  intros pi Hnorm.
  apply (req_trans (sumf (fun s => mult (pi s) (advantage_req pi s)))
                   (sumf (fun s => req_minus (mult (pi s) (reward s))
                                             (mult (pi s) (state_value_req pi))))
                   zero).
  - apply (sum_ext (fun s => mult (pi s) (advantage_req pi s))
                   (fun s => req_minus (mult (pi s) (reward s))
                                       (mult (pi s) (state_value_req pi)))).
    intro s. unfold advantage_req. apply req_mult_minus_distr_l.
  - apply (req_trans (sumf (fun s => req_minus (mult (pi s) (reward s))
                                               (mult (pi s) (state_value_req pi))))
                     (req_minus (sumf (fun s => mult (pi s) (reward s)))
                                (sumf (fun s => mult (pi s) (state_value_req pi))))
                     zero).
    + apply rppo_sum_minus.
    + apply (req_trans (req_minus (sumf (fun s => mult (pi s) (reward s)))
                                  (sumf (fun s => mult (pi s) (state_value_req pi))))
                       (req_minus (state_value_req pi) (state_value_req pi))
                       zero).
      * apply (req_plus_compat (state_value_req pi) (state_value_req pi)
                               (opp (sumf (fun s => mult (pi s) (state_value_req pi))))
                               (opp (state_value_req pi))
                               (req_refl (state_value_req pi))).
        apply (req_opp_compat (sumf (fun s => mult (pi s) (state_value_req pi)))
                              (state_value_req pi)).
        exact (rppo_constant_sum (state_value_req pi) pi Hnorm).
      * unfold req_minus. apply plus_opp.
Qed.

(* ============ Block 2 front machine: align_objective explicit decomposition ============ *)

(* Item 8 align_objective_decomp: J(p) == V(p) - beta*KL(p,pi_ref). *)
Lemma rppo_align_objective_decomp :
  forall (p : S -> Real) (Hp : pos_dist S p),
    real_eq (align_objective_req S sumf reward beta pi_ref pi_ref_pos p Hp)
        (req_minus (state_value_req p)
                   (mult beta (relative_entropy_req S sumf p pi_ref Hp pi_ref_pos))).
Proof.
  intros p Hp.
  (* Step A: sum p*E_align == (sum p*opp r) - (sum p*beta*lgR). *)
  assert (HA : real_eq (sumf (fun s => mult (p s) (align_energy_req S reward beta pi_ref pi_ref_pos s)))
                   (req_minus (sumf (fun s => mult (p s) (opp (reward s))))
                              (sumf (fun s => mult (p s) (mult beta (log (pi_ref s) (pi_ref_pos s))))))).
  { apply (req_trans (sumf (fun s => mult (p s) (align_energy_req S reward beta pi_ref pi_ref_pos s)))
                     (sumf (fun s => req_minus (mult (p s) (opp (reward s)))
                                               (mult (p s) (mult beta (log (pi_ref s) (pi_ref_pos s))))))
                     (req_minus (sumf (fun s => mult (p s) (opp (reward s))))
                                (sumf (fun s => mult (p s) (mult beta (log (pi_ref s) (pi_ref_pos s))))))).
    - apply (sum_ext (fun s => mult (p s) (align_energy_req S reward beta pi_ref pi_ref_pos s))
                     (fun s => req_minus (mult (p s) (opp (reward s)))
                                         (mult (p s) (mult beta (log (pi_ref s) (pi_ref_pos s)))))).
      intro s. exact (req_mult_minus_distr_l (p s) (opp (reward s))
                                             (mult beta (log (pi_ref s) (pi_ref_pos s)))).
    - apply rppo_sum_minus. }
  (* Step B: opp(sum p*opp r) == V(p). *)
  assert (HB : real_eq (opp (sumf (fun s => mult (p s) (opp (reward s)))))
                   (state_value_req p)).
  { apply (req_trans (opp (sumf (fun s => mult (p s) (opp (reward s)))))
                     (opp (sumf (fun s => opp (mult (p s) (reward s)))))
                     (state_value_req p)).
    - apply (req_opp_compat (sumf (fun s => mult (p s) (opp (reward s))))
                            (sumf (fun s => opp (mult (p s) (reward s))))).
      apply (sum_ext (fun s => mult (p s) (opp (reward s)))
                     (fun s => opp (mult (p s) (reward s)))).
      intro s. apply req_opp_mult_l.
    - apply (req_trans (opp (sumf (fun s => opp (mult (p s) (reward s)))))
                       (opp (opp (sumf (fun s => mult (p s) (reward s)))))
                       (state_value_req p)).
      + apply (req_opp_compat (sumf (fun s => opp (mult (p s) (reward s))))
                              (opp (sumf (fun s => mult (p s) (reward s))))).
        apply rppo_sum_opp.
      + apply req_double_neg. }
  (* Step C: opp(sum p*E) == V(p) + sum p*beta*lgR. *)
  assert (HC : real_eq (opp (sumf (fun s => mult (p s) (align_energy_req S reward beta pi_ref pi_ref_pos s))))
                   (plus (state_value_req p)
                         (sumf (fun s => mult (p s) (mult beta (log (pi_ref s) (pi_ref_pos s))))))).
  { apply (req_trans (opp (sumf (fun s => mult (p s) (align_energy_req S reward beta pi_ref pi_ref_pos s))))
                     (opp (req_minus (sumf (fun s => mult (p s) (opp (reward s))))
                                     (sumf (fun s => mult (p s) (mult beta (log (pi_ref s) (pi_ref_pos s)))))))
                     (plus (state_value_req p)
                           (sumf (fun s => mult (p s) (mult beta (log (pi_ref s) (pi_ref_pos s))))))).
    - apply (req_opp_compat (sumf (fun s => mult (p s) (align_energy_req S reward beta pi_ref pi_ref_pos s)))
                            (req_minus (sumf (fun s => mult (p s) (opp (reward s))))
                                       (sumf (fun s => mult (p s) (mult beta (log (pi_ref s) (pi_ref_pos s))))))).
      exact HA.
    - apply (req_trans (opp (req_minus (sumf (fun s => mult (p s) (opp (reward s))))
                                       (sumf (fun s => mult (p s) (mult beta (log (pi_ref s) (pi_ref_pos s)))))))
                       (plus (opp (sumf (fun s => mult (p s) (opp (reward s)))))
                             (sumf (fun s => mult (p s) (mult beta (log (pi_ref s) (pi_ref_pos s))))))
                       (plus (state_value_req p)
                             (sumf (fun s => mult (p s) (mult beta (log (pi_ref s) (pi_ref_pos s))))))).
      + exact (req_opp_minus (sumf (fun s => mult (p s) (opp (reward s))))
                             (sumf (fun s => mult (p s) (mult beta (log (pi_ref s) (pi_ref_pos s)))))).
      + apply (req_plus_compat (opp (sumf (fun s => mult (p s) (opp (reward s)))))
                               (state_value_req p)
                               (sumf (fun s => mult (p s) (mult beta (log (pi_ref s) (pi_ref_pos s)))))
                               (sumf (fun s => mult (p s) (mult beta (log (pi_ref s) (pi_ref_pos s)))))
                               HB (req_refl (sumf (fun s => mult (p s) (mult beta (log (pi_ref s) (pi_ref_pos s))))))). }
  (* Step D: sum p*beta*lgR == beta*sum p*lgR. *)
  assert (HD : real_eq (sumf (fun s => mult (p s) (mult beta (log (pi_ref s) (pi_ref_pos s)))))
                   (mult beta (sumf (fun s => mult (p s) (log (pi_ref s) (pi_ref_pos s)))))).
  { apply (req_trans (sumf (fun s => mult (p s) (mult beta (log (pi_ref s) (pi_ref_pos s)))))
                     (sumf (fun s => mult beta (mult (p s) (log (pi_ref s) (pi_ref_pos s)))))
                     (mult beta (sumf (fun s => mult (p s) (log (pi_ref s) (pi_ref_pos s)))))).
    - apply (sum_ext (fun s => mult (p s) (mult beta (log (pi_ref s) (pi_ref_pos s))))
                     (fun s => mult beta (mult (p s) (log (pi_ref s) (pi_ref_pos s))))).
      intro s.
      apply (req_trans (mult (p s) (mult beta (log (pi_ref s) (pi_ref_pos s))))
                       (mult (mult (p s) beta) (log (pi_ref s) (pi_ref_pos s)))
                       (mult beta (mult (p s) (log (pi_ref s) (pi_ref_pos s))))).
      + apply mult_assoc.
      + apply (req_trans (mult (mult (p s) beta) (log (pi_ref s) (pi_ref_pos s)))
                         (mult (mult beta (p s)) (log (pi_ref s) (pi_ref_pos s)))
                         (mult beta (mult (p s) (log (pi_ref s) (pi_ref_pos s))))).
        * apply (req_mult_compat (mult (p s) beta) (mult beta (p s))
                                 (log (pi_ref s) (pi_ref_pos s)) (log (pi_ref s) (pi_ref_pos s))
                                 (mult_comm (p s) beta) (req_refl (log (pi_ref s) (pi_ref_pos s)))).
        * apply (req_sym _ _ (mult_assoc beta (p s) (log (pi_ref s) (pi_ref_pos s)))).
    - apply (sum_linear beta (fun s => mult (p s) (log (pi_ref s) (pi_ref_pos s)))). }

  assert (HE : real_eq (sumf (fun s => mult (p s) (log (p s) (Hp s))))
                   (plus (relative_entropy_req S sumf p pi_ref Hp pi_ref_pos)
                         (sumf (fun s => mult (p s) (log (pi_ref s) (pi_ref_pos s)))))).
  { apply (req_trans (sumf (fun s => mult (p s) (log (p s) (Hp s))))
                     (sumf (fun s => plus (mult (p s) (req_minus (log (p s) (Hp s)) (log (pi_ref s) (pi_ref_pos s))))
                                          (mult (p s) (log (pi_ref s) (pi_ref_pos s)))))
                     (plus (relative_entropy_req S sumf p pi_ref Hp pi_ref_pos)
                           (sumf (fun s => mult (p s) (log (pi_ref s) (pi_ref_pos s)))))).
    - apply (sum_ext (fun s => mult (p s) (log (p s) (Hp s)))
                     (fun s => plus (mult (p s) (req_minus (log (p s) (Hp s)) (log (pi_ref s) (pi_ref_pos s))))
                                    (mult (p s) (log (pi_ref s) (pi_ref_pos s))))).
      intro s.
      apply (req_trans (mult (p s) (log (p s) (Hp s)))
                       (plus (req_minus (mult (p s) (log (p s) (Hp s)))
                                        (mult (p s) (log (pi_ref s) (pi_ref_pos s))))
                             (mult (p s) (log (pi_ref s) (pi_ref_pos s))))
                       (plus (mult (p s) (req_minus (log (p s) (Hp s)) (log (pi_ref s) (pi_ref_pos s))))
                             (mult (p s) (log (pi_ref s) (pi_ref_pos s))))).
      + apply (req_trans (mult (p s) (log (p s) (Hp s)))
                         (plus (mult (p s) (log (pi_ref s) (pi_ref_pos s)))
                               (req_minus (mult (p s) (log (p s) (Hp s)))
                                          (mult (p s) (log (pi_ref s) (pi_ref_pos s)))))
                         (plus (req_minus (mult (p s) (log (p s) (Hp s)))
                                          (mult (p s) (log (pi_ref s) (pi_ref_pos s))))
                               (mult (p s) (log (pi_ref s) (pi_ref_pos s))))).
        * exact (req_sym _ _ (req_minus_plus_cancel (mult (p s) (log (pi_ref s) (pi_ref_pos s)))
                                                    (mult (p s) (log (p s) (Hp s))))).
        * apply plus_comm.
      + apply (req_plus_compat (req_minus (mult (p s) (log (p s) (Hp s)))
                                          (mult (p s) (log (pi_ref s) (pi_ref_pos s))))
                               (mult (p s) (req_minus (log (p s) (Hp s)) (log (pi_ref s) (pi_ref_pos s))))
                               (mult (p s) (log (pi_ref s) (pi_ref_pos s)))
                               (mult (p s) (log (pi_ref s) (pi_ref_pos s)))
                               (req_sym _ _ (req_mult_minus_distr_l (p s) (log (p s) (Hp s))
                                                                    (log (pi_ref s) (pi_ref_pos s))))
                               (req_refl (mult (p s) (log (pi_ref s) (pi_ref_pos s))))).
    - apply (req_trans (sumf (fun s => plus (mult (p s) (req_minus (log (p s) (Hp s)) (log (pi_ref s) (pi_ref_pos s))))
                                            (mult (p s) (log (pi_ref s) (pi_ref_pos s)))))
                       (plus (sumf (fun s => mult (p s) (req_minus (log (p s) (Hp s)) (log (pi_ref s) (pi_ref_pos s)))))
                             (sumf (fun s => mult (p s) (log (pi_ref s) (pi_ref_pos s)))))
                       (plus (relative_entropy_req S sumf p pi_ref Hp pi_ref_pos)
                             (sumf (fun s => mult (p s) (log (pi_ref s) (pi_ref_pos s)))))).
      + apply sum_add.
      + apply (req_plus_compat (sumf (fun s => mult (p s) (req_minus (log (p s) (Hp s)) (log (pi_ref s) (pi_ref_pos s)))))
                               (relative_entropy_req S sumf p pi_ref Hp pi_ref_pos)
                               (sumf (fun s => mult (p s) (log (pi_ref s) (pi_ref_pos s))))
                               (sumf (fun s => mult (p s) (log (pi_ref s) (pi_ref_pos s))))
                               (req_refl (relative_entropy_req S sumf p pi_ref Hp pi_ref_pos))
                               (req_refl (sumf (fun s => mult (p s) (log (pi_ref s) (pi_ref_pos s)))))). }
  (* Step F: compose. *)
  apply (req_trans (align_objective_req S sumf reward beta pi_ref pi_ref_pos p Hp)
                   (plus (plus (state_value_req p)
                               (sumf (fun s => mult (p s) (mult beta (log (pi_ref s) (pi_ref_pos s))))))
                         (opp (mult beta (sumf (fun s => mult (p s) (log (p s) (Hp s)))))))
                   (req_minus (state_value_req p)
                              (mult beta (relative_entropy_req S sumf p pi_ref Hp pi_ref_pos)))).
  -
    apply (req_trans (align_objective_req S sumf reward beta pi_ref pi_ref_pos p Hp)
                     (plus (opp (sumf (fun s => mult (p s) (align_energy_req S reward beta pi_ref pi_ref_pos s))))
                           (opp (mult beta (sumf (fun s => mult (p s) (log (p s) (Hp s)))))))
                     (plus (plus (state_value_req p)
                                 (sumf (fun s => mult (p s) (mult beta (log (pi_ref s) (pi_ref_pos s))))))
                           (opp (mult beta (sumf (fun s => mult (p s) (log (p s) (Hp s)))))))).
    + (* align_objective_req unfolds to opp(F_align_req) = opp(plus sumE beta*sum log p). *)
      unfold align_objective_req, F_align_req.
      exact (req_opp_plus (sumf (fun s => mult (p s) (align_energy_req S reward beta pi_ref pi_ref_pos s)))
                          (mult beta (sumf (fun s => mult (p s) (log (p s) (Hp s)))))).
    + apply (req_plus_compat (opp (sumf (fun s => mult (p s) (align_energy_req S reward beta pi_ref pi_ref_pos s))))
                             (plus (state_value_req p)
                                   (sumf (fun s => mult (p s) (mult beta (log (pi_ref s) (pi_ref_pos s))))))
                             (opp (mult beta (sumf (fun s => mult (p s) (log (p s) (Hp s))))))
                             (opp (mult beta (sumf (fun s => mult (p s) (log (p s) (Hp s))))))
                             HC (req_refl (opp (mult beta (sumf (fun s => mult (p s) (log (p s) (Hp s)))))))).
  - (* Inner collapse: W + opp(beta*(KL + Lref)) == opp(beta*KL); req_minus shape. *)
    apply (req_trans (plus (plus (state_value_req p)
                                 (sumf (fun s => mult (p s) (mult beta (log (pi_ref s) (pi_ref_pos s))))))
                           (opp (mult beta (sumf (fun s => mult (p s) (log (p s) (Hp s)))))))
                     (plus (state_value_req p)
                           (plus (mult beta (sumf (fun s => mult (p s) (log (pi_ref s) (pi_ref_pos s)))))
                                 (opp (plus (mult beta (relative_entropy_req S sumf p pi_ref Hp pi_ref_pos))
                                            (mult beta (sumf (fun s => mult (p s) (log (pi_ref s) (pi_ref_pos s)))))))))
                     (req_minus (state_value_req p)
                                (mult beta (relative_entropy_req S sumf p pi_ref Hp pi_ref_pos)))).
    + (* assoc regrouping + W shape change (steps D/E). *)
      assert (HBeta : real_eq (mult beta (sumf (fun s => mult (p s) (log (p s) (Hp s)))))
                          (plus (mult beta (relative_entropy_req S sumf p pi_ref Hp pi_ref_pos))
                                (mult beta (sumf (fun s => mult (p s) (log (pi_ref s) (pi_ref_pos s))))))).
      { apply (req_trans (mult beta (sumf (fun s => mult (p s) (log (p s) (Hp s)))))
                         (mult beta (plus (relative_entropy_req S sumf p pi_ref Hp pi_ref_pos)
                                          (sumf (fun s => mult (p s) (log (pi_ref s) (pi_ref_pos s))))))
                         (plus (mult beta (relative_entropy_req S sumf p pi_ref Hp pi_ref_pos))
                               (mult beta (sumf (fun s => mult (p s) (log (pi_ref s) (pi_ref_pos s))))))).
        - apply (req_mult_compat beta beta
                                 (sumf (fun s => mult (p s) (log (p s) (Hp s))))
                                 (plus (relative_entropy_req S sumf p pi_ref Hp pi_ref_pos)
                                       (sumf (fun s => mult (p s) (log (pi_ref s) (pi_ref_pos s)))))
                                 (req_refl beta) HE).
        - exact (distrib beta (relative_entropy_req S sumf p pi_ref Hp pi_ref_pos)
                              (sumf (fun s => mult (p s) (log (pi_ref s) (pi_ref_pos s))))). }
      assert (Hinner : real_eq (plus (sumf (fun s => mult (p s) (mult beta (log (pi_ref s) (pi_ref_pos s)))))
                                 (opp (mult beta (sumf (fun s => mult (p s) (log (p s) (Hp s)))))))
                           (plus (mult beta (sumf (fun s => mult (p s) (log (pi_ref s) (pi_ref_pos s)))))
                                 (opp (plus (mult beta (relative_entropy_req S sumf p pi_ref Hp pi_ref_pos))
                                            (mult beta (sumf (fun s => mult (p s) (log (pi_ref s) (pi_ref_pos s))))))))).
      { apply (req_plus_compat (sumf (fun s => mult (p s) (mult beta (log (pi_ref s) (pi_ref_pos s)))))
                               (mult beta (sumf (fun s => mult (p s) (log (pi_ref s) (pi_ref_pos s)))))
                               (opp (mult beta (sumf (fun s => mult (p s) (log (p s) (Hp s))))))
                               (opp (plus (mult beta (relative_entropy_req S sumf p pi_ref Hp pi_ref_pos))
                                          (mult beta (sumf (fun s => mult (p s) (log (pi_ref s) (pi_ref_pos s)))))))
                               HD
                               (req_opp_compat (mult beta (sumf (fun s => mult (p s) (log (p s) (Hp s)))))
                                               (plus (mult beta (relative_entropy_req S sumf p pi_ref Hp pi_ref_pos))
                                                     (mult beta (sumf (fun s => mult (p s) (log (pi_ref s) (pi_ref_pos s))))))
                                               HBeta)). }
      apply (req_trans (plus (plus (state_value_req p)
                                   (sumf (fun s => mult (p s) (mult beta (log (pi_ref s) (pi_ref_pos s))))))
                             (opp (mult beta (sumf (fun s => mult (p s) (log (p s) (Hp s)))))))
                       (plus (state_value_req p)
                             (plus (sumf (fun s => mult (p s) (mult beta (log (pi_ref s) (pi_ref_pos s)))))
                                   (opp (mult beta (sumf (fun s => mult (p s) (log (p s) (Hp s))))))))
                       (plus (state_value_req p)
                             (plus (mult beta (sumf (fun s => mult (p s) (log (pi_ref s) (pi_ref_pos s)))))
                                   (opp (plus (mult beta (relative_entropy_req S sumf p pi_ref Hp pi_ref_pos))
                                              (mult beta (sumf (fun s => mult (p s) (log (pi_ref s) (pi_ref_pos s)))))))))).
      * apply (req_sym _ _ (plus_assoc (state_value_req p)
                                       (sumf (fun s => mult (p s) (mult beta (log (pi_ref s) (pi_ref_pos s)))))
                                       (opp (mult beta (sumf (fun s => mult (p s) (log (p s) (Hp s)))))))).
      * apply (req_plus_compat (state_value_req p) (state_value_req p) _ _
                               (req_refl (state_value_req p)) Hinner).
    + (* x + opp(y + x) == opp(y), x := beta*Lref, y := beta*KL (inner machine 6). *)
      assert (Hcol : real_eq (plus (mult beta (sumf (fun s => mult (p s) (log (pi_ref s) (pi_ref_pos s)))))
                               (opp (plus (mult beta (relative_entropy_req S sumf p pi_ref Hp pi_ref_pos))
                                          (mult beta (sumf (fun s => mult (p s) (log (pi_ref s) (pi_ref_pos s))))))))
                          (opp (mult beta (relative_entropy_req S sumf p pi_ref Hp pi_ref_pos)))).
      { exact (rppo_plus_opp_plus_r
                 (mult beta (sumf (fun s => mult (p s) (log (pi_ref s) (pi_ref_pos s)))))
                 (mult beta (relative_entropy_req S sumf p pi_ref Hp pi_ref_pos))). }
      apply (req_trans (plus (state_value_req p)
                             (plus (mult beta (sumf (fun s => mult (p s) (log (pi_ref s) (pi_ref_pos s)))))
                                   (opp (plus (mult beta (relative_entropy_req S sumf p pi_ref Hp pi_ref_pos))
                                              (mult beta (sumf (fun s => mult (p s) (log (pi_ref s) (pi_ref_pos s)))))))))
                       (plus (state_value_req p)
                             (opp (mult beta (relative_entropy_req S sumf p pi_ref Hp pi_ref_pos))))
                       (req_minus (state_value_req p)
                                  (mult beta (relative_entropy_req S sumf p pi_ref Hp pi_ref_pos)))).
      * apply (req_plus_compat (state_value_req p) (state_value_req p) _ _ (req_refl (state_value_req p)) Hcol).
      * unfold req_minus. apply req_refl.
Qed.

(* Item 3 exact_improvement_identity. *)
Lemma rppo_exact_improvement_identity :
  forall (pi_new : S -> Real) (Hnorm : real_eq (sumf pi_new) one) (Hpos : pos_dist S pi_new),
    real_eq (req_minus (align_objective_req S sumf reward beta pi_ref pi_ref_pos pi_new Hpos)
                   (align_objective_req S sumf reward beta pi_ref pi_ref_pos pi_ref pi_ref_pos))
        (req_minus (sumf (fun s => mult (pi_new s) (advantage_req pi_ref s)))
                   (mult beta (relative_entropy_req S sumf pi_new pi_ref Hpos pi_ref_pos))).
Proof.
  intros pi_new Hnorm Hpos.
  (* Step 1: J(pi_ref) == V(pi_ref) (KL self-zero + req_minus zero-right collapse). *)
  assert (Hr : real_eq (align_objective_req S sumf reward beta pi_ref pi_ref_pos pi_ref pi_ref_pos)
                   (state_value_req pi_ref)).
  { apply (req_trans (align_objective_req S sumf reward beta pi_ref pi_ref_pos pi_ref pi_ref_pos)
                     (req_minus (state_value_req pi_ref)
                                (mult beta (relative_entropy_req S sumf pi_ref pi_ref pi_ref_pos pi_ref_pos)))
                     (state_value_req pi_ref)).
    - exact (rppo_align_objective_decomp pi_ref pi_ref_pos).
    - apply (req_trans (req_minus (state_value_req pi_ref)
                                  (mult beta (relative_entropy_req S sumf pi_ref pi_ref pi_ref_pos pi_ref_pos)))
                       (req_minus (state_value_req pi_ref) zero)
                       (state_value_req pi_ref)).
      + apply (req_plus_compat (state_value_req pi_ref) (state_value_req pi_ref)
                               (opp (mult beta (relative_entropy_req S sumf pi_ref pi_ref pi_ref_pos pi_ref_pos)))
                               (opp zero)
                               (req_refl (state_value_req pi_ref))).
        apply (req_opp_compat (mult beta (relative_entropy_req S sumf pi_ref pi_ref pi_ref_pos pi_ref_pos)) zero).
        apply (req_trans (mult beta (relative_entropy_req S sumf pi_ref pi_ref pi_ref_pos pi_ref_pos))
                         (mult beta zero) zero).
        * apply (req_mult_compat beta beta
                                 (relative_entropy_req S sumf pi_ref pi_ref pi_ref_pos pi_ref_pos) zero
                                 (req_refl beta) (rppo_KL_self_zero pi_ref pi_ref_pos)).
        * apply mult_zero.
      + apply (req_trans (req_minus (state_value_req pi_ref) zero)
                         (plus (state_value_req pi_ref) (opp zero))
                         (state_value_req pi_ref)).
        * unfold req_minus. apply req_refl.
        * apply (req_trans (plus (state_value_req pi_ref) (opp zero))
                           (plus (state_value_req pi_ref) zero)
                           (state_value_req pi_ref)).
          -- apply (req_plus_compat (state_value_req pi_ref) (state_value_req pi_ref)
                                    (opp zero) zero (req_refl (state_value_req pi_ref))).
             exact (rkl_opp_zero).
          -- apply plus_zero. }
  (* Step 2: J(new) - J(ref) -> (V_n - beta*KL - V_r) -> E_adv - beta*KL. *)
  apply (req_trans (req_minus (align_objective_req S sumf reward beta pi_ref pi_ref_pos pi_new Hpos)
                              (align_objective_req S sumf reward beta pi_ref pi_ref_pos pi_ref pi_ref_pos))
                   (req_minus (align_objective_req S sumf reward beta pi_ref pi_ref_pos pi_new Hpos)
                              (state_value_req pi_ref))
                   (req_minus (sumf (fun s => mult (pi_new s) (advantage_req pi_ref s)))
                              (mult beta (relative_entropy_req S sumf pi_new pi_ref Hpos pi_ref_pos)))).
  - apply (req_plus_compat (align_objective_req S sumf reward beta pi_ref pi_ref_pos pi_new Hpos)
                           (align_objective_req S sumf reward beta pi_ref pi_ref_pos pi_new Hpos)
                           (opp (align_objective_req S sumf reward beta pi_ref pi_ref_pos pi_ref pi_ref_pos))
                           (opp (state_value_req pi_ref))
                           (req_refl (align_objective_req S sumf reward beta pi_ref pi_ref_pos pi_new Hpos))
                           (req_opp_compat (align_objective_req S sumf reward beta pi_ref pi_ref_pos pi_ref pi_ref_pos)
                                           (state_value_req pi_ref) Hr)).
  - apply (req_trans (req_minus (align_objective_req S sumf reward beta pi_ref pi_ref_pos pi_new Hpos)
                                (state_value_req pi_ref))
                     (req_minus (req_minus (state_value_req pi_new)
                                           (mult beta (relative_entropy_req S sumf pi_new pi_ref Hpos pi_ref_pos)))
                                (state_value_req pi_ref))
                     (req_minus (sumf (fun s => mult (pi_new s) (advantage_req pi_ref s)))
                                (mult beta (relative_entropy_req S sumf pi_new pi_ref Hpos pi_ref_pos)))).
    + apply (req_plus_compat (align_objective_req S sumf reward beta pi_ref pi_ref_pos pi_new Hpos)
                             (req_minus (state_value_req pi_new)
                                        (mult beta (relative_entropy_req S sumf pi_new pi_ref Hpos pi_ref_pos)))
                             (opp (state_value_req pi_ref)) (opp (state_value_req pi_ref))
                             (rppo_align_objective_decomp pi_new Hpos) (req_refl (opp (state_value_req pi_ref)))).
    + apply (req_trans (req_minus (req_minus (state_value_req pi_new)
                                             (mult beta (relative_entropy_req S sumf pi_new pi_ref Hpos pi_ref_pos)))
                                  (state_value_req pi_ref))
                       (req_minus (state_value_req pi_new)
                                  (plus (mult beta (relative_entropy_req S sumf pi_new pi_ref Hpos pi_ref_pos))
                                        (state_value_req pi_ref)))
                       (req_minus (sumf (fun s => mult (pi_new s) (advantage_req pi_ref s)))
                                  (mult beta (relative_entropy_req S sumf pi_new pi_ref Hpos pi_ref_pos)))).
      * exact (req_sym _ _ (req_minus_plus_r (state_value_req pi_new)
                                             (mult beta (relative_entropy_req S sumf pi_new pi_ref Hpos pi_ref_pos))
                                             (state_value_req pi_ref))).
      * apply (req_trans (req_minus (state_value_req pi_new)
                                    (plus (mult beta (relative_entropy_req S sumf pi_new pi_ref Hpos pi_ref_pos))
                                          (state_value_req pi_ref)))
                         (req_minus (state_value_req pi_new)
                                    (plus (state_value_req pi_ref)
                                          (mult beta (relative_entropy_req S sumf pi_new pi_ref Hpos pi_ref_pos))))
                         (req_minus (sumf (fun s => mult (pi_new s) (advantage_req pi_ref s)))
                                    (mult beta (relative_entropy_req S sumf pi_new pi_ref Hpos pi_ref_pos)))).
        -- apply (req_plus_compat (state_value_req pi_new) (state_value_req pi_new)
                                  (opp (plus (mult beta (relative_entropy_req S sumf pi_new pi_ref Hpos pi_ref_pos))
                                             (state_value_req pi_ref)))
                                  (opp (plus (state_value_req pi_ref)
                                             (mult beta (relative_entropy_req S sumf pi_new pi_ref Hpos pi_ref_pos))))
                                  (req_refl (state_value_req pi_new))).
           apply (req_opp_compat (plus (mult beta (relative_entropy_req S sumf pi_new pi_ref Hpos pi_ref_pos))
                                       (state_value_req pi_ref))
                                 (plus (state_value_req pi_ref)
                                       (mult beta (relative_entropy_req S sumf pi_new pi_ref Hpos pi_ref_pos)))).
           apply plus_comm.
        -- apply (req_trans (req_minus (state_value_req pi_new)
                                       (plus (state_value_req pi_ref)
                                             (mult beta (relative_entropy_req S sumf pi_new pi_ref Hpos pi_ref_pos))))
                            (req_minus (req_minus (state_value_req pi_new) (state_value_req pi_ref))
                                       (mult beta (relative_entropy_req S sumf pi_new pi_ref Hpos pi_ref_pos)))
                            (req_minus (sumf (fun s => mult (pi_new s) (advantage_req pi_ref s)))
                                       (mult beta (relative_entropy_req S sumf pi_new pi_ref Hpos pi_ref_pos)))).
           ++ apply req_minus_plus_r.
           ++ apply (req_plus_compat (req_minus (state_value_req pi_new) (state_value_req pi_ref))
                                     (sumf (fun s => mult (pi_new s) (advantage_req pi_ref s)))
                                     (opp (mult beta (relative_entropy_req S sumf pi_new pi_ref Hpos pi_ref_pos)))
                                     (opp (mult beta (relative_entropy_req S sumf pi_new pi_ref Hpos pi_ref_pos)))
                                     (req_sym _ _ (rppo_advantage_sum_ref pi_new Hnorm))
                                     (req_refl (opp (mult beta (relative_entropy_req S sumf pi_new pi_ref Hpos pi_ref_pos))))).
Qed.

(* Item 4 ppo_monotonic_improvement. *)
Lemma rppo_ppo_monotonic_improvement :
  forall (pi_new : S -> Real) (Hnorm : real_eq (sumf pi_new) one) (Hpos : pos_dist S pi_new),
    real_le zero (req_minus (sumf (fun s => mult (pi_new s) (advantage_req pi_ref s)))
                       (mult beta (relative_entropy_req S sumf pi_new pi_ref Hpos pi_ref_pos))) ->
    real_le (align_objective_req S sumf reward beta pi_ref pi_ref_pos pi_ref pi_ref_pos)
       (align_objective_req S sumf reward beta pi_ref pi_ref_pos pi_new Hpos).
Proof.
  intros pi_new Hnorm Hpos Hur.
  apply (req_le_of_minus_nonneg
           (align_objective_req S sumf reward beta pi_ref pi_ref_pos pi_new Hpos)
           (align_objective_req S sumf reward beta pi_ref pi_ref_pos pi_ref pi_ref_pos)).
  apply (req_le_compat zero zero
           (req_minus (sumf (fun s => mult (pi_new s) (advantage_req pi_ref s)))
                      (mult beta (relative_entropy_req S sumf pi_new pi_ref Hpos pi_ref_pos)))
           (req_minus (align_objective_req S sumf reward beta pi_ref pi_ref_pos pi_new Hpos)
                      (align_objective_req S sumf reward beta pi_ref pi_ref_pos pi_ref pi_ref_pos))).
  - apply req_refl.
  - apply (req_sym _ _).
    exact (rppo_exact_improvement_identity pi_new Hnorm Hpos).
  - exact Hur.
Qed.

(* Item 5 kl_penalty_sufficient. *)
Lemma rppo_kl_penalty_sufficient :
  forall (pi_new : S -> Real) (eps : Real)
         (Hnorm : real_eq (sumf pi_new) one) (Hpos : pos_dist S pi_new),
    real_le (relative_entropy_req S sumf pi_new pi_ref Hpos pi_ref_pos) eps ->
    real_le (mult beta eps) (sumf (fun s => mult (pi_new s) (advantage_req pi_ref s))) ->
    real_le (align_objective_req S sumf reward beta pi_ref pi_ref_pos pi_ref pi_ref_pos)
       (align_objective_req S sumf reward beta pi_ref pi_ref_pos pi_new Hpos).
Proof.
  intros pi_new eps Hnorm Hpos Hkl Hadv.
  apply (rppo_ppo_monotonic_improvement pi_new Hnorm Hpos).
  apply (req_le_minus_nonneg (mult beta (relative_entropy_req S sumf pi_new pi_ref Hpos pi_ref_pos))
                             (sumf (fun s => mult (pi_new s) (advantage_req pi_ref s)))).
  apply (le_trans (mult beta (relative_entropy_req S sumf pi_new pi_ref Hpos pi_ref_pos))
                  (mult beta eps)
                  (sumf (fun s => mult (pi_new s) (advantage_req pi_ref s)))).
  - apply (req_le_mult_compat_r beta
                                (relative_entropy_req S sumf pi_new pi_ref Hpos pi_ref_pos) eps
                                (lt_le_iff zero beta (inl beta_pos)) Hkl).
  - exact Hadv.
Qed.

(* ============ Block 2: PPO gap / ratio cluster ============ *)

Variable pi_old : S -> Real.
Variable pi_old_pos : forall s : S, real_lt zero (pi_old s).
Variable advantage_fn : S -> Real.
Variable epsilon : Real.

(* Importance sampling ratio (pi*/pi_old). *)
Definition rppo_star_old_ratio (s : S) : Real :=
  mult (rppo_pistar s) (inv_pos (pi_old s) (pi_old_pos s)).
(* Clipping (min/r_max as carrier only). *)
Definition rppo_clip (r : Real) : Real :=
  r_max (min r (plus one epsilon)) (req_minus one epsilon).
(* PPO clipped surrogate objective. *)
Definition rppo_ppo_objective : Real :=
  sumf (fun s => mult (pi_old s)
                      (mult (min (rppo_star_old_ratio s) (rppo_clip (rppo_star_old_ratio s)))
                            (advantage_fn s))).
(* Unclipped IS objective. *)
Definition rppo_is_objective : Real :=
  sumf (fun s => mult (pi_old s) (mult (rppo_star_old_ratio s) (advantage_fn s))).

(* Item 6 ppo_gap_exact (zero le usage on min/r_max). *)
Lemma rppo_ppo_gap_exact :
  real_eq (req_minus rppo_is_objective rppo_ppo_objective)
      (sumf (fun s => mult (pi_old s)
                           (mult (req_minus (rppo_star_old_ratio s)
                                            (min (rppo_star_old_ratio s) (rppo_clip (rppo_star_old_ratio s))))
                                 (advantage_fn s)))).
Proof.
  (* Pointwise: p*(r*A) - p*(m*A) == p*((r-m)*A) (double distributivity + reordering). *)
  assert (Hpt : forall s : S,
    real_eq (req_minus (mult (pi_old s) (mult (rppo_star_old_ratio s) (advantage_fn s)))
                   (mult (pi_old s) (mult (min (rppo_star_old_ratio s) (rppo_clip (rppo_star_old_ratio s)))
                                          (advantage_fn s))))
        (mult (pi_old s) (mult (req_minus (rppo_star_old_ratio s)
                                          (min (rppo_star_old_ratio s) (rppo_clip (rppo_star_old_ratio s))))
                               (advantage_fn s)))).
  { intro s.
    (* Outer: p*X - p*Y == p*(X - Y). *)
    assert (H1 : real_eq (req_minus (mult (pi_old s) (mult (rppo_star_old_ratio s) (advantage_fn s)))
                                (mult (pi_old s) (mult (min (rppo_star_old_ratio s) (rppo_clip (rppo_star_old_ratio s)))
                                                       (advantage_fn s))))
                     (mult (pi_old s) (req_minus (mult (rppo_star_old_ratio s) (advantage_fn s))
                                                 (mult (min (rppo_star_old_ratio s) (rppo_clip (rppo_star_old_ratio s)))
                                                       (advantage_fn s)))))
      by exact (req_sym _ _ (req_mult_minus_distr_l (pi_old s)
                                                    (mult (rppo_star_old_ratio s) (advantage_fn s))
                                                    (mult (min (rppo_star_old_ratio s) (rppo_clip (rppo_star_old_ratio s)))
                                                          (advantage_fn s)))).
    (* Inner: (r*A) - (m*A) == (r - m)*A (comm + distrib-backward + comm back). *)
    assert (H2 : real_eq (req_minus (mult (rppo_star_old_ratio s) (advantage_fn s))
                                (mult (min (rppo_star_old_ratio s) (rppo_clip (rppo_star_old_ratio s)))
                                      (advantage_fn s)))
                     (mult (req_minus (rppo_star_old_ratio s)
                                      (min (rppo_star_old_ratio s) (rppo_clip (rppo_star_old_ratio s))))
                           (advantage_fn s))).
    { apply (req_sym (mult (req_minus (rppo_star_old_ratio s)
                                      (min (rppo_star_old_ratio s) (rppo_clip (rppo_star_old_ratio s))))
                           (advantage_fn s))
                     (req_minus (mult (rppo_star_old_ratio s) (advantage_fn s))
                                (mult (min (rppo_star_old_ratio s) (rppo_clip (rppo_star_old_ratio s)))
                                      (advantage_fn s)))).
      apply (req_trans (mult (req_minus (rppo_star_old_ratio s)
                                        (min (rppo_star_old_ratio s) (rppo_clip (rppo_star_old_ratio s))))
                             (advantage_fn s))
                       (mult (advantage_fn s) (req_minus (rppo_star_old_ratio s)
                                                         (min (rppo_star_old_ratio s) (rppo_clip (rppo_star_old_ratio s)))))
                       (req_minus (mult (rppo_star_old_ratio s) (advantage_fn s))
                                  (mult (min (rppo_star_old_ratio s) (rppo_clip (rppo_star_old_ratio s)))
                                        (advantage_fn s)))).
      - apply mult_comm.
      - apply (req_trans (mult (advantage_fn s) (req_minus (rppo_star_old_ratio s)
                                                           (min (rppo_star_old_ratio s) (rppo_clip (rppo_star_old_ratio s)))))
                         (req_minus (mult (advantage_fn s) (rppo_star_old_ratio s))
                                    (mult (advantage_fn s) (min (rppo_star_old_ratio s) (rppo_clip (rppo_star_old_ratio s)))))
                         (req_minus (mult (rppo_star_old_ratio s) (advantage_fn s))
                                    (mult (min (rppo_star_old_ratio s) (rppo_clip (rppo_star_old_ratio s)))
                                          (advantage_fn s)))).
        + exact (req_mult_minus_distr_l (advantage_fn s) (rppo_star_old_ratio s)
                                        (min (rppo_star_old_ratio s) (rppo_clip (rppo_star_old_ratio s)))).
        + unfold req_minus.
          apply (req_plus_compat (mult (advantage_fn s) (rppo_star_old_ratio s))
                                 (mult (rppo_star_old_ratio s) (advantage_fn s))
                                 (opp (mult (advantage_fn s) (min (rppo_star_old_ratio s) (rppo_clip (rppo_star_old_ratio s)))))
                                 (opp (mult (min (rppo_star_old_ratio s) (rppo_clip (rppo_star_old_ratio s)))
                                            (advantage_fn s)))
                                 (mult_comm (advantage_fn s) (rppo_star_old_ratio s))).
          apply (req_opp_compat (mult (advantage_fn s) (min (rppo_star_old_ratio s) (rppo_clip (rppo_star_old_ratio s))))
                                (mult (min (rppo_star_old_ratio s) (rppo_clip (rppo_star_old_ratio s))) (advantage_fn s))).
          apply mult_comm. }
    apply (req_trans (req_minus (mult (pi_old s) (mult (rppo_star_old_ratio s) (advantage_fn s)))
                                (mult (pi_old s) (mult (min (rppo_star_old_ratio s) (rppo_clip (rppo_star_old_ratio s)))
                                                       (advantage_fn s))))
                     (mult (pi_old s) (req_minus (mult (rppo_star_old_ratio s) (advantage_fn s))
                                                 (mult (min (rppo_star_old_ratio s) (rppo_clip (rppo_star_old_ratio s)))
                                                       (advantage_fn s))))
                     (mult (pi_old s) (mult (req_minus (rppo_star_old_ratio s)
                                                       (min (rppo_star_old_ratio s) (rppo_clip (rppo_star_old_ratio s))))
                                            (advantage_fn s)))).
    - exact H1.
    - apply (req_mult_compat (pi_old s) (pi_old s) _ _ (req_refl (pi_old s)) H2). }
  (* Sum transport: sum(f - g) == sum f - sum g (backward) + pointwise. *)
  apply (req_trans (req_minus rppo_is_objective rppo_ppo_objective)
                   (sumf (fun s => req_minus (mult (pi_old s) (mult (rppo_star_old_ratio s) (advantage_fn s)))
                                             (mult (pi_old s)
                                                   (mult (min (rppo_star_old_ratio s)
                                                              (rppo_clip (rppo_star_old_ratio s)))
                                                         (advantage_fn s)))))
                   (sumf (fun s => mult (pi_old s)
                                        (mult (req_minus (rppo_star_old_ratio s)
                                                         (min (rppo_star_old_ratio s) (rppo_clip (rppo_star_old_ratio s))))
                                              (advantage_fn s))))).
  - apply (req_sym _ _ (rppo_sum_minus (fun s => mult (pi_old s) (mult (rppo_star_old_ratio s) (advantage_fn s)))
                                       (fun s => mult (pi_old s)
                                                      (mult (min (rppo_star_old_ratio s) (rppo_clip (rppo_star_old_ratio s)))
                                                            (advantage_fn s))))).
  - apply (sum_ext (fun s => req_minus (mult (pi_old s) (mult (rppo_star_old_ratio s) (advantage_fn s)))
                                       (mult (pi_old s)
                                             (mult (min (rppo_star_old_ratio s) (rppo_clip (rppo_star_old_ratio s)))
                                                   (advantage_fn s))))
                   (fun s => mult (pi_old s)
                                  (mult (req_minus (rppo_star_old_ratio s)
                                                   (min (rppo_star_old_ratio s) (rppo_clip (rppo_star_old_ratio s))))
                                        (advantage_fn s)))).
    exact Hpt.
Qed.

(* Item 9 importance_ratio_self_one (idempotent delta duality). *)
Lemma rppo_importance_ratio_self_one :
  forall (p : S -> Real) (Hp : pos_dist S p) (s : S),
    real_eq (policy_ratio_req p p s (Hp s)) one.
Proof.
  intros p Hp s.
  unfold policy_ratio_req.
  apply inv_pos_correct.
Qed.

(* Item 10 ppo_surrogate_raw_is_value_improvement. *)
Lemma rppo_ppo_surrogate_raw_is_value_improvement :
  forall (pi p_old : S -> Real) (Hpos : forall s : S, real_lt zero (p_old s))
         (Hnorm : real_eq (sumf pi) one),
    real_eq (sumf (fun s => mult (p_old s)
                             (mult (policy_ratio_req pi p_old s (Hpos s)) (advantage_req p_old s))))
        (req_minus (state_value_req pi) (state_value_req p_old)).
Proof.
  intros pi p_old Hpos Hnorm.
  (* Pointwise ratio cancellation: p*((pi/p)*X) == pi*X. *)
  assert (Hpt : forall s : S,
    real_eq (mult (p_old s) (mult (policy_ratio_req pi p_old s (Hpos s)) (advantage_req p_old s)))
        (mult (pi s) (advantage_req p_old s))).
  { intro s.
    assert (H1 : real_eq (mult (p_old s) (mult (mult (pi s) (inv_pos (p_old s) (Hpos s))) (advantage_req p_old s)))
                     (mult (mult (p_old s) (mult (pi s) (inv_pos (p_old s) (Hpos s))))
                           (advantage_req p_old s)))
      by exact (mult_assoc (p_old s) (mult (pi s) (inv_pos (p_old s) (Hpos s))) (advantage_req p_old s)).
    assert (H2 : real_eq (mult (mult (p_old s) (mult (pi s) (inv_pos (p_old s) (Hpos s))))
                           (advantage_req p_old s))
                     (mult (mult (mult (p_old s) (pi s)) (inv_pos (p_old s) (Hpos s)))
                           (advantage_req p_old s)))
      by exact (req_mult_compat (mult (p_old s) (mult (pi s) (inv_pos (p_old s) (Hpos s))))
                                (mult (mult (p_old s) (pi s)) (inv_pos (p_old s) (Hpos s)))
                                (advantage_req p_old s) (advantage_req p_old s)
                                (mult_assoc (p_old s) (pi s) (inv_pos (p_old s) (Hpos s)))
                                (req_refl (advantage_req p_old s))).
    assert (H3 : real_eq (mult (mult (mult (p_old s) (pi s)) (inv_pos (p_old s) (Hpos s)))
                           (advantage_req p_old s))
                     (mult (mult (mult (pi s) (p_old s)) (inv_pos (p_old s) (Hpos s)))
                           (advantage_req p_old s)))
      by exact (req_mult_compat (mult (mult (p_old s) (pi s)) (inv_pos (p_old s) (Hpos s)))
                                (mult (mult (pi s) (p_old s)) (inv_pos (p_old s) (Hpos s)))
                                (advantage_req p_old s) (advantage_req p_old s)
                                (req_mult_compat (mult (p_old s) (pi s)) (mult (pi s) (p_old s))
                                                 (inv_pos (p_old s) (Hpos s))
                                                 (inv_pos (p_old s) (Hpos s))
                                                 (mult_comm (p_old s) (pi s))
                                                 (req_refl (inv_pos (p_old s) (Hpos s))))
                                (req_refl (advantage_req p_old s))).
    assert (H3b : real_eq (mult (mult (mult (pi s) (p_old s)) (inv_pos (p_old s) (Hpos s)))
                            (advantage_req p_old s))
                     (mult (mult (pi s) (mult (p_old s) (inv_pos (p_old s) (Hpos s))))
                           (advantage_req p_old s)))
      by exact (req_mult_compat (mult (mult (pi s) (p_old s)) (inv_pos (p_old s) (Hpos s)))
                                (mult (pi s) (mult (p_old s) (inv_pos (p_old s) (Hpos s))))
                                (advantage_req p_old s) (advantage_req p_old s)
                                (req_sym _ _ (mult_assoc (pi s) (p_old s) (inv_pos (p_old s) (Hpos s))))
                                (req_refl (advantage_req p_old s))).
    assert (H4 : real_eq (mult (mult (pi s) (mult (p_old s) (inv_pos (p_old s) (Hpos s))))
                           (advantage_req p_old s))
                     (mult (mult (pi s) one) (advantage_req p_old s)))
      by exact (req_mult_compat (mult (pi s) (mult (p_old s) (inv_pos (p_old s) (Hpos s))))
                                (mult (pi s) one)
                                (advantage_req p_old s) (advantage_req p_old s)
                                (req_mult_compat (pi s) (pi s)
                                                 (mult (p_old s) (inv_pos (p_old s) (Hpos s))) one
                                                 (req_refl (pi s)) (inv_pos_correct (p_old s) (Hpos s)))
                                (req_refl (advantage_req p_old s))).
    assert (H5 : real_eq (mult (mult (pi s) one) (advantage_req p_old s))
                     (mult (pi s) (advantage_req p_old s)))
      by exact (req_mult_compat (mult (pi s) one) (pi s)
                                (advantage_req p_old s) (advantage_req p_old s)
                                (req_mult_one_r (pi s)) (req_refl (advantage_req p_old s))).
    unfold policy_ratio_req.
    apply (req_trans (mult (p_old s) (mult (mult (pi s) (inv_pos (p_old s) (Hpos s))) (advantage_req p_old s)))
                     (mult (mult (p_old s) (mult (pi s) (inv_pos (p_old s) (Hpos s)))) (advantage_req p_old s))
                     (mult (pi s) (advantage_req p_old s))).
    - exact H1.
    - apply (req_trans (mult (mult (p_old s) (mult (pi s) (inv_pos (p_old s) (Hpos s)))) (advantage_req p_old s))
                       (mult (mult (mult (p_old s) (pi s)) (inv_pos (p_old s) (Hpos s))) (advantage_req p_old s))
                       (mult (pi s) (advantage_req p_old s))).
      + exact H2.
      + apply (req_trans (mult (mult (mult (p_old s) (pi s)) (inv_pos (p_old s) (Hpos s))) (advantage_req p_old s))
                         (mult (mult (mult (pi s) (p_old s)) (inv_pos (p_old s) (Hpos s))) (advantage_req p_old s))
                         (mult (pi s) (advantage_req p_old s))).
        * exact H3.
        * apply (req_trans (mult (mult (mult (pi s) (p_old s)) (inv_pos (p_old s) (Hpos s))) (advantage_req p_old s))
                           (mult (mult (pi s) (mult (p_old s) (inv_pos (p_old s) (Hpos s)))) (advantage_req p_old s))
                           (mult (pi s) (advantage_req p_old s))).
          -- exact H3b.
          -- apply (req_trans (mult (mult (pi s) (mult (p_old s) (inv_pos (p_old s) (Hpos s)))) (advantage_req p_old s))
                              (mult (mult (pi s) one) (advantage_req p_old s))
                              (mult (pi s) (advantage_req p_old s))).
             ++ exact H4.
              ++ exact H5. }
  apply (req_trans (sumf (fun s => mult (p_old s)
                                        (mult (policy_ratio_req pi p_old s (Hpos s)) (advantage_req p_old s))))
                   (sumf (fun s => mult (pi s) (advantage_req p_old s)))
                   (req_minus (state_value_req pi) (state_value_req p_old))).
  - apply (sum_ext (fun s => mult (p_old s)
                                  (mult (policy_ratio_req pi p_old s (Hpos s)) (advantage_req p_old s)))
                   (fun s => mult (pi s) (advantage_req p_old s))).
    exact Hpt.
  - apply (req_trans (sumf (fun s => mult (pi s) (advantage_req p_old s)))
                     (req_minus (sumf (fun s => mult (pi s) (reward s)))
                                (sumf (fun s => mult (pi s) (state_value_req p_old))))
                     (req_minus (state_value_req pi) (state_value_req p_old))).
    + apply (req_trans (sumf (fun s => mult (pi s) (advantage_req p_old s)))
                       (sumf (fun s => req_minus (mult (pi s) (reward s))
                                                 (mult (pi s) (state_value_req p_old))))
                       (req_minus (sumf (fun s => mult (pi s) (reward s)))
                                  (sumf (fun s => mult (pi s) (state_value_req p_old))))).
      * apply (sum_ext (fun s => mult (pi s) (advantage_req p_old s))
                       (fun s => req_minus (mult (pi s) (reward s))
                                           (mult (pi s) (state_value_req p_old)))).
        intro s. unfold advantage_req. apply req_mult_minus_distr_l.
      * apply rppo_sum_minus.
    + apply (req_plus_compat (state_value_req pi) (state_value_req pi)
                             (opp (sumf (fun s => mult (pi s) (state_value_req p_old))))
                             (opp (state_value_req p_old))
                             (req_refl (state_value_req pi))).
      apply (req_opp_compat (sumf (fun s => mult (pi s) (state_value_req p_old)))
                            (state_value_req p_old)).
      exact (rppo_constant_sum (state_value_req p_old) pi Hnorm).
Qed.

(* ============ Block 3: explicit value / FEP explicit / Boltzmann / extensional cluster ============ *)

(* Item 7 rlhf_optimal_value (assembly). *)
Lemma rppo_rlhf_optimal_value :
  real_eq (align_objective_req S sumf reward beta pi_ref pi_ref_pos rppo_pistar rppo_pistar_pos)
      (req_minus (state_value_req rppo_pistar)
                 (mult beta (relative_entropy_req S sumf rppo_pistar pi_ref rppo_pistar_pos pi_ref_pos))).
Proof.
  exact (rppo_align_objective_decomp rppo_pistar rppo_pistar_pos).
Qed.

(* Item 13 pi_star_objective_value (kept as a separate same-face item; not merged). *)
Lemma rppo_pi_star_objective_value :
  real_eq (align_objective_req S sumf reward beta pi_ref pi_ref_pos rppo_pistar rppo_pistar_pos)
      (req_minus (state_value_req rppo_pistar)
                 (mult beta (relative_entropy_req S sumf rppo_pistar pi_ref rppo_pistar_pos pi_ref_pos))).
Proof.
  exact (rppo_align_objective_decomp rppo_pistar rppo_pistar_pos).
Qed.

(* Item 11 align_free_energy_explicit. *)
Lemma rppo_align_free_energy_explicit :
  forall (p : S -> Real) (Hp : pos_dist S p),
    real_eq (F_align_req S sumf reward beta pi_ref pi_ref_pos p Hp)
        (plus (opp (state_value_req p))
              (mult beta (relative_entropy_req S sumf p pi_ref Hp pi_ref_pos))).
Proof.
  intros p Hp.
  apply (req_trans (F_align_req S sumf reward beta pi_ref pi_ref_pos p Hp)
                   (opp (align_objective_req S sumf reward beta pi_ref pi_ref_pos p Hp))
                   (plus (opp (state_value_req p))
                         (mult beta (relative_entropy_req S sumf p pi_ref Hp pi_ref_pos)))).
  - apply (req_sym (opp (opp (F_align_req S sumf reward beta pi_ref pi_ref_pos p Hp)))
                   (F_align_req S sumf reward beta pi_ref pi_ref_pos p Hp)).
    exact (req_double_neg (F_align_req S sumf reward beta pi_ref pi_ref_pos p Hp)).
  - apply (req_trans (opp (align_objective_req S sumf reward beta pi_ref pi_ref_pos p Hp))
                     (opp (req_minus (state_value_req p)
                                     (mult beta (relative_entropy_req S sumf p pi_ref Hp pi_ref_pos))))
                     (plus (opp (state_value_req p))
                           (mult beta (relative_entropy_req S sumf p pi_ref Hp pi_ref_pos)))).
    + apply (req_opp_compat (align_objective_req S sumf reward beta pi_ref pi_ref_pos p Hp)
                            (req_minus (state_value_req p)
                                       (mult beta (relative_entropy_req S sumf p pi_ref Hp pi_ref_pos)))
                            (rppo_align_objective_decomp p Hp)).
    + unfold req_minus.
      apply (req_trans (opp (plus (state_value_req p)
                                  (opp (mult beta (relative_entropy_req S sumf p pi_ref Hp pi_ref_pos)))))
                       (plus (opp (state_value_req p))
                             (opp (opp (mult beta (relative_entropy_req S sumf p pi_ref Hp pi_ref_pos)))))
                       (plus (opp (state_value_req p))
                             (mult beta (relative_entropy_req S sumf p pi_ref Hp pi_ref_pos)))).
      * apply req_opp_plus.
      * apply (req_plus_compat (opp (state_value_req p)) (opp (state_value_req p)) _ _
                               (req_refl (opp (state_value_req p)))).
        apply req_double_neg.
Qed.

(* Item 15 free_energy_ext_gen: generalized energy/temperature free energy extension. *)
Definition F_gen_req (energy : S -> Real) (D : Real) (p : S -> Real) (Hp : pos_dist S p) : Real :=
  plus (sumf (fun s => mult (p s) (energy s)))
       (mult D (sumf (fun s => mult (p s) (log (p s) (Hp s))))).

Lemma rppo_free_energy_ext_gen :
  forall (energy : S -> Real) (D : Real) (p q : S -> Real)
         (Hp : pos_dist S p) (Hq : pos_dist S q),
    (forall s : S, real_eq (p s) (q s)) ->
    real_eq (F_gen_req energy D p Hp) (F_gen_req energy D q Hq).
Proof.
  intros energy D p q Hp Hq Hpq.
  unfold F_gen_req.
  apply (req_plus_compat (sumf (fun s => mult (p s) (energy s)))
                         (sumf (fun s => mult (q s) (energy s)))
                         (mult D (sumf (fun s => mult (p s) (log (p s) (Hp s)))))
                         (mult D (sumf (fun s => mult (q s) (log (q s) (Hq s)))))).
  - apply (sum_ext (fun s => mult (p s) (energy s)) (fun s => mult (q s) (energy s))).
    intro s.
    apply (req_mult_compat (p s) (q s) (energy s) (energy s) (Hpq s) (req_refl (energy s))).
  - apply (req_mult_compat D D (sumf (fun s => mult (p s) (log (p s) (Hp s))))
                               (sumf (fun s => mult (q s) (log (q s) (Hq s))))
                               (req_refl D)).
    apply (sum_ext (fun s => mult (p s) (log (p s) (Hp s)))
                   (fun s => mult (q s) (log (q s) (Hq s)))).
    intro s.
    apply (req_mult_compat (p s) (q s) (log (p s) (Hp s)) (log (q s) (Hq s)) (Hpq s)).
    apply (rppo_log_req_compat (p s) (q s) (Hp s) (Hq s) (Hpq s)).
Qed.

(* Boltzmann distribution (same shape as the align instance) + positivity. *)
Definition rppo_boltzmann (s : S) : Real :=
  mult (inv_pos (Z_align_req S sumf reward beta beta_pos pi_ref) Zap)
       (exp_neg (mult (inv_pos beta beta_pos)
                      (align_energy_req S reward beta pi_ref pi_ref_pos s))).

Lemma rppo_boltzmann_pos : pos_dist S rppo_boltzmann.
Proof.
  intro s.
  unfold rppo_boltzmann.
  apply mult_positive.
  - apply inv_pos_pos.
  - apply exp_neg_pos.
Qed.

(* Item 12 align_free_energy_pi_star: pi* and the Boltzmann distribution share
   the alignment free energy (F extension + pointwise closed-form exponential identity). *)
Lemma rppo_align_free_energy_pi_star :
  real_eq (F_gen_req (align_energy_req S reward beta pi_ref pi_ref_pos) beta
                 rppo_pistar rppo_pistar_pos)
      (F_gen_req (align_energy_req S reward beta pi_ref pi_ref_pos) beta
                 rppo_boltzmann rppo_boltzmann_pos).
Proof.
  apply (rppo_free_energy_ext_gen (align_energy_req S reward beta pi_ref pi_ref_pos) beta
                                  rppo_pistar rppo_boltzmann
                                  rppo_pistar_pos rppo_boltzmann_pos).
  intro s.
  apply (req_trans (rppo_pistar s)
                   (mult (inv_pos (Z_align_req S sumf reward beta beta_pos pi_ref) Zap)
                         (mult (pi_ref s)
                               (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))))
                   (rppo_boltzmann s)).
  - (* Canonical pi* vs the pinned closed form differ only in the inv_pos
       positivity proof argument; req_mult_cancel_l + inv_pos_correct fold. *)
    unfold rppo_pistar.
    apply (req_mult_compat _ _ _ _
      (req_mult_cancel_l (Z_align_req S sumf reward beta beta_pos pi_ref) _ _
         Zap
         (req_trans _ _ _
            (inv_pos_correct (Z_align_req S sumf reward beta beta_pos pi_ref)
               Zap)
            (req_sym _ _
               (inv_pos_correct (Z_align_req S sumf reward beta beta_pos pi_ref)
                  Zap))))
      (req_refl (mult (pi_ref s)
                      (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))))).
  - apply (req_mult_compat (inv_pos (Z_align_req S sumf reward beta beta_pos pi_ref) Zap)
                           (inv_pos (Z_align_req S sumf reward beta beta_pos pi_ref) Zap)
                           (mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s)))))
                           (exp_neg (mult (inv_pos beta beta_pos)
                                          (align_energy_req S reward beta pi_ref pi_ref_pos s)))
                           (req_refl (inv_pos (Z_align_req S sumf reward beta beta_pos pi_ref) Zap))).
    apply (req_sym _ _).
    exact (req_align_energy_exp S reward beta beta_pos pi_ref pi_ref_pos s).
Qed.

(* Item 16 front machine: b + ((a-b) - c) == a - c (promoted standalone collapse lemma). *)
Lemma rppo_b_collapse_minus :
  forall a b c : Real,
  real_eq (plus b (req_minus (req_minus a b) c)) (req_minus a c).
Proof.
  intros a b c. unfold req_minus.
  apply (req_trans (plus b (plus (plus a (opp b)) (opp c)))
                   (plus (plus b (plus a (opp b))) (opp c))
                   (plus a (opp c))).
  - apply plus_assoc.
  - apply (req_trans (plus (plus b (plus a (opp b))) (opp c))
                     (plus (plus a (plus b (opp b))) (opp c))
                     (plus a (opp c))).
    + apply (req_plus_compat (plus b (plus a (opp b)))
                             (plus a (plus b (opp b)))
                             (opp c) (opp c)
                             (req_trans (plus b (plus a (opp b)))
                                        (plus (plus b a) (opp b))
                                        (plus a (plus b (opp b)))
                                        (plus_assoc b a (opp b))
                                        (req_trans (plus (plus b a) (opp b))
                                                   (plus (plus a b) (opp b))
                                                   (plus a (plus b (opp b)))
                                                   (req_plus_compat (plus b a) (plus a b)
                                                                    (opp b) (opp b)
                                                                    (plus_comm b a)
                                                                    (req_refl (opp b)))
                                                   (req_sym _ _ (plus_assoc a b (opp b)))))
                             (req_refl (opp c))).
    + apply (req_trans (plus (plus a (plus b (opp b))) (opp c))
                       (plus (plus a zero) (opp c))
                       (plus a (opp c))).
      * apply (req_plus_compat (plus a (plus b (opp b)))
                               (plus a zero) (opp c) (opp c)
                               (req_plus_compat a a (plus b (opp b)) zero
                                                (req_refl a) (plus_opp b))
                               (req_refl (opp c))).
      * apply (req_plus_compat (plus a zero) a (opp c) (opp c)
                               (plus_zero a) (req_refl (opp c))).
Qed.

(* Inner machine 7: J(pi_ref) == V(pi_ref) (KL diagonal self-zero + zero-right cancel). *)
Lemma rppo_J_ref_eq_value :
  real_eq (align_objective_req S sumf reward beta pi_ref pi_ref_pos pi_ref pi_ref_pos)
      (state_value_req pi_ref).
Proof.
  apply (req_trans (align_objective_req S sumf reward beta pi_ref pi_ref_pos pi_ref pi_ref_pos)
                   (req_minus (state_value_req pi_ref)
                              (mult beta (relative_entropy_req S sumf pi_ref pi_ref pi_ref_pos pi_ref_pos)))
                   (state_value_req pi_ref)).
  - exact (rppo_align_objective_decomp pi_ref pi_ref_pos).
  - apply (req_trans (req_minus (state_value_req pi_ref)
                                (mult beta (relative_entropy_req S sumf pi_ref pi_ref pi_ref_pos pi_ref_pos)))
                     (req_minus (state_value_req pi_ref) zero)
                     (state_value_req pi_ref)).
    + apply (req_plus_compat (state_value_req pi_ref) (state_value_req pi_ref)
                             (opp (mult beta (relative_entropy_req S sumf pi_ref pi_ref pi_ref_pos pi_ref_pos)))
                             (opp zero)
                             (req_refl (state_value_req pi_ref))).
      apply (req_opp_compat (mult beta (relative_entropy_req S sumf pi_ref pi_ref pi_ref_pos pi_ref_pos)) zero).
      apply (req_trans (mult beta (relative_entropy_req S sumf pi_ref pi_ref pi_ref_pos pi_ref_pos))
                       (mult beta zero) zero).
      * apply (req_mult_compat beta beta
                               (relative_entropy_req S sumf pi_ref pi_ref pi_ref_pos pi_ref_pos) zero
                               (req_refl beta) (rppo_KL_self_zero pi_ref pi_ref_pos)).
      * apply mult_zero.
    + apply (req_trans (req_minus (state_value_req pi_ref) zero)
                       (plus (state_value_req pi_ref) (opp zero))
                       (state_value_req pi_ref)).
      * unfold req_minus. apply req_refl.
      * apply (req_trans (plus (state_value_req pi_ref) (opp zero))
                         (plus (state_value_req pi_ref) zero)
                         (state_value_req pi_ref)).
        -- apply (req_plus_compat (state_value_req pi_ref) (state_value_req pi_ref)
                                  (opp zero) zero (req_refl (state_value_req pi_ref))).
           exact (rkl_opp_zero).
        -- apply plus_zero.
Qed.

(* Item 16 align_objective_advantage_decomp: J(pi) == J(pi_ref) + (sum pi*A_ref - beta*KL). *)
Lemma rppo_align_objective_advantage_decomp :
  forall (pi : S -> Real) (Hnorm : real_eq (sumf pi) one) (Hpos : pos_dist S pi),
    real_eq (align_objective_req S sumf reward beta pi_ref pi_ref_pos pi Hpos)
        (plus (align_objective_req S sumf reward beta pi_ref pi_ref_pos pi_ref pi_ref_pos)
              (req_minus (sumf (fun s => mult (pi s) (advantage_req pi_ref s)))
                         (mult beta (relative_entropy_req S sumf pi pi_ref Hpos pi_ref_pos)))).
Proof.
  intros pi Hnorm Hpos.
  (* Composition: J(pi) -> V_pi - beta*KL -> V_r + ((V_pi - V_r) - beta*KL) [machine 6 backward]
     -> J(ref) + (sum pi A_ref - beta*KL). *)
  apply (req_trans (align_objective_req S sumf reward beta pi_ref pi_ref_pos pi Hpos)
                   (req_minus (state_value_req pi)
                              (mult beta (relative_entropy_req S sumf pi pi_ref Hpos pi_ref_pos)))
                   (plus (align_objective_req S sumf reward beta pi_ref pi_ref_pos pi_ref pi_ref_pos)
                         (req_minus (sumf (fun s => mult (pi s) (advantage_req pi_ref s)))
                                    (mult beta (relative_entropy_req S sumf pi pi_ref Hpos pi_ref_pos))))).
  - exact (rppo_align_objective_decomp pi Hpos).
  - apply (req_trans (req_minus (state_value_req pi)
                                (mult beta (relative_entropy_req S sumf pi pi_ref Hpos pi_ref_pos)))
                     (plus (state_value_req pi_ref)
                           (req_minus (req_minus (state_value_req pi) (state_value_req pi_ref))
                                      (mult beta (relative_entropy_req S sumf pi pi_ref Hpos pi_ref_pos))))
                     (plus (align_objective_req S sumf reward beta pi_ref pi_ref_pos pi_ref pi_ref_pos)
                           (req_minus (sumf (fun s => mult (pi s) (advantage_req pi_ref s)))
                                      (mult beta (relative_entropy_req S sumf pi pi_ref Hpos pi_ref_pos))))).
    + exact (req_sym _ _ (rppo_b_collapse_minus (state_value_req pi) (state_value_req pi_ref)
                           (mult beta (relative_entropy_req S sumf pi pi_ref Hpos pi_ref_pos)))).
    + apply (req_plus_compat (state_value_req pi_ref)
                             (align_objective_req S sumf reward beta pi_ref pi_ref_pos pi_ref pi_ref_pos)
                             (req_minus (req_minus (state_value_req pi) (state_value_req pi_ref))
                                        (mult beta (relative_entropy_req S sumf pi pi_ref Hpos pi_ref_pos)))
                             (req_minus (sumf (fun s => mult (pi s) (advantage_req pi_ref s)))
                                        (mult beta (relative_entropy_req S sumf pi pi_ref Hpos pi_ref_pos)))
                             (req_sym _ _ rppo_J_ref_eq_value)
                             (req_plus_compat (req_minus (state_value_req pi) (state_value_req pi_ref))
                                              (sumf (fun s => mult (pi s) (advantage_req pi_ref s)))
                                              (opp (mult beta (relative_entropy_req S sumf pi pi_ref Hpos pi_ref_pos)))
                                              (opp (mult beta (relative_entropy_req S sumf pi pi_ref Hpos pi_ref_pos)))
                                              (req_sym _ _ (rppo_advantage_sum_ref pi Hnorm))
                                              (req_refl (opp (mult beta (relative_entropy_req S sumf pi pi_ref Hpos pi_ref_pos)))))).
Qed.
End ReqPPOAdvantage.
(* ================= Section 2: the mixd_qeq_mult_r family ================= *)
From Stdlib Require Import QArith.QArith.
From Stdlib Require Import QArith.Qring.

Local Open Scope Q_scope.

(* Part 0: Q-carrier shims (QeqT congruence / transport), all statement faces Set. *)

Lemma mixd_qeq_mult_r : forall a b c : Q, QeqT a b -> QeqT (a * c) (b * c).
Proof.
  intros a b c H.
  apply qeq_imp_qeqT.
  exact (@Qmult_comp a b (qeqT_imp_qeq _ _ H) c c (Qeq_refl c)).
Qed.

Lemma mixd_qeq_mult_l : forall a b c : Q, QeqT a b -> QeqT (c * a) (c * b).
Proof.
  intros a b c H.
  apply qeq_imp_qeqT.
  apply (Qeq_trans _ (a * c) _).
  - apply Qmult_comm.
  - apply (Qeq_trans _ (b * c) _).
    + exact (@Qmult_comp a b (qeqT_imp_qeq _ _ H) c c (Qeq_refl c)).
    + apply Qmult_comm.
Qed.

Lemma mixd_qeqT_trans_l : forall a b c : Q, QeqT a b -> QeqT b c -> QeqT a c.
Proof.
  intros a b c Hab Hbc.
  apply qeq_imp_qeqT.
  transitivity b.
  - exact (qeqT_imp_qeq a b Hab).
  - exact (qeqT_imp_qeq b c Hbc).
Qed.

(* QleT' transport along QeqT (Set-face transport leaf; Qle_comp instance application). *)
Lemma mixd_leT_transport : forall a b c : Q, QeqT a b -> QleT' a c -> QleT' b c.
Proof.
  intros a b c Hab Hac.
  exact (Qle_to_QleT' b c
           (proj1 (@Qle_comp a b (qeqT_imp_qeq a b Hab) c c (Qeq_refl c))
              (QleT'_to_Qle a c Hac))).
Qed.

Lemma mixd_qlt_eq_l : forall a b c : Q, QeqT a b -> QltT a c -> QltT b c.
Proof.
  intros a b c Hab Hac.
  exact (Qlt_to_QltT b c
           (proj1 (@Qlt_compat a b (qeqT_imp_qeq a b Hab) c c (Qeq_refl c))
              (QltT_to_Qlt a c Hac))).
Qed.

Lemma mixd_qlt_eq_r : forall a b c : Q, QeqT b c -> QltT a b -> QltT a c.
Proof.
  intros a b c Hbc Hab.
  exact (Qlt_to_QltT a c
           (proj1 (@Qlt_compat a a (Qeq_refl a) b c (qeqT_imp_qeq b c Hbc))
              (QltT_to_Qlt a b Hab))).
Qed.

Lemma mixd_qle_eq_l : forall a b c : Q, QeqT a b -> QleT' a c -> QleT' b c.
Proof.
  intros a b c Hab Hac.
  exact (Qle_to_QleT' b c
           (proj1 (@Qle_comp a b (qeqT_imp_qeq a b Hab) c c (Qeq_refl c))
              (QleT'_to_Qle a c Hac))).
Qed.

Lemma mixd_qle_eq_r : forall a b c : Q, QeqT b c -> QleT' a b -> QleT' a c.
Proof.
  intros a b c Hbc Hab.
  exact (Qle_to_QleT' a c
           (proj1 (@Qle_comp a a (Qeq_refl a) b c (qeqT_imp_qeq b c Hbc))
              (QleT'_to_Qle a b Hab))).
Qed.

Lemma mixd_qleT'_trans : forall a b c : Q, QleT' a b -> QleT' b c -> QleT' a c.
Proof.
  intros a b c Hab Hbc.
  exact (Qle_to_QleT' a c
           (Qle_trans a b c (QleT'_to_Qle _ _ Hab) (QleT'_to_Qle _ _ Hbc))).
Qed.

(* Power congruence along base equality. *)
Lemma mixd_qpow_eq_compat : forall (a b : Q) (H : QeqT a b) (m : nat),
  QeqT (igr_qpow a m) (igr_qpow b m).
Proof.
  intros a b H m. induction m as [| m IH].
  - apply qeq_imp_qeqT. apply Qeq_refl.
  - cbn [igr_qpow].
    apply qeq_imp_qeqT.
    exact (@Qmult_comp a b (qeqT_imp_qeq _ _ H)
                       (igr_qpow a m) (igr_qpow b m) (qeqT_imp_qeq _ _ IH)).
Qed.

Lemma mixd_qring_cancel_r : forall x k : Q, QeqT k ((k - x) + x).
Proof.
  intros x k. apply qeq_imp_qeqT. ring.
Qed.

Lemma mixd_half_pos : QltT 0 (1#2).
Proof. apply Qlt_to_QltT. unfold Qlt. cbn. lia. Qed.

Lemma mixd_half_lt_one : QltT (1#2) 1.
Proof. apply Qlt_to_QltT. unfold Qlt. cbn. lia. Qed.

(* 0 < z implies x < x + z. *)
Lemma mixd_qlt_add_pos : forall x z : Q, QltT 0 z -> QltT x (x + z).
Proof.
  intros x z Hz.
  apply (mixd_qlt_eq_l (x + 0) x (x + z)).
  - apply qeq_imp_qeqT. apply Qplus_0_r.
  - apply Qlt_to_QltT.
    apply (proj2 (Qplus_lt_r 0 z x)). exact (QltT_to_Qlt _ _ Hz).
Qed.

(* a + a < b implies a < b - a. *)
Lemma mixd_qsub_lt2 : forall a b : Q, QltT (a + a) b -> QltT a (b - a).
Proof.
  intros a b H.
  apply Qlt_to_QltT.
  apply (proj1 (Qplus_lt_r a (b - a) a)).
  assert (Heq : QeqT b (a + (b - a))).
  { apply qeq_imp_qeqT. ring. }
  exact (QltT_to_Qlt _ _
           (mixd_qlt_eq_r (a + a) b (a + (b - a)) Heq H)).
Qed.

Lemma mixd_qsub_le : forall w : Q, QleT' 0 w -> QleT' (1 - w) 1.
Proof.
  intros w Hw.
  pose proof (QleT'_to_Qle 0 w Hw) as Hwq.
  apply Qle_to_QleT'.
  unfold Qle in *.
  destruct w as [nw dw].
  cbn [Qnum Qden Qminus Qopp Qplus] in *.
  lia.
Qed.

Lemma mixd_qsub_ge0 : forall w : Q, QleT' w 1 -> QleT' 0 (1 - w).
Proof.
  intros w Hw.
  pose proof (QleT'_to_Qle w 1 Hw) as Hwq.
  apply Qle_to_QleT'.
  unfold Qle in *.
  destruct w as [nw dw].
  cbn [Qnum Qden Qminus Qopp Qplus] in *.
  lia.
Qed.

Lemma mixd_qsub_pos : forall w : Q, QltT w 1 -> QltT 0 (1 - w).
Proof.
  intros w Hw.
  apply Qlt_to_QltT.
  apply (proj1 (Qplus_lt_r 0 (1 - w) w)).
  assert (Heq : QeqT 1 (w + (1 - w))).
  { apply qeq_imp_qeqT. ring. }
  assert (Hmid : QltT (w + 0) 1).
  { exact (mixd_qlt_eq_l w (w + 0) 1
             (qeq_imp_qeqT _ _ (Qeq_sym _ _ (Qplus_0_r w))) Hw). }
  exact (QltT_to_Qlt _ _ (mixd_qlt_eq_r (w + 0) 1 (w + (1 - w)) Heq Hmid)).
Qed.

(* Qle_bool false reflection: Qle_bool x y = false implies y < x. *)
Lemma mixd_qle_bool_false_lt : forall x y : Q, Id (Qle_bool x y) false -> QltT y x.
Proof.
  intros x y E.
  assert (Hn : ~ (x <= y)).
  { intro Hc.
    assert (Ht : Qle_bool x y = true) by (apply Qle_bool_iff; exact Hc).
    rewrite Ht in E. inversion E. }
  exact (Qlt_to_QltT _ _ (Qnot_le_lt x y Hn)).
Qed.

(* Q-max as an if-Qle_bool form (the stdlib Qmax is a generic gmax form, not adopted). *)
Definition mixd_qmax (a b : Q) : Q := if Qle_bool a b then b else a.

Lemma mixd_qmax_eq_l : forall a b : Q, Id (Qle_bool a b) false -> QeqT (mixd_qmax a b) a.
Proof.
  intros a b E.
  unfold mixd_qmax. destruct (Qle_bool a b) eqn:Eb.
  - exfalso. inversion E.
  - apply qeq_imp_qeqT. apply Qeq_refl.
Qed.

Lemma mixd_qmax_eq_r : forall a b : Q, Id (Qle_bool a b) true -> QeqT (mixd_qmax a b) b.
Proof.
  intros a b E.
  unfold mixd_qmax. destruct (Qle_bool a b) eqn:Eb.
  - apply qeq_imp_qeqT. apply Qeq_refl.
  - exfalso. inversion E.
Qed.

(* 0 <= m * w for m : nat and 0 < w. *)
Lemma mixd_qnatw_nonneg : forall (w : Q) (Hw : QltT 0 w) (m : nat),
  QleT' 0 (Qmake (Z.of_nat m) 1 * w).
Proof.
  intros w Hw m.
  apply (mixd_qle_eq_l (0 * w) 0 (Qmake (Z.of_nat m) 1 * w)).
  - apply qeq_imp_qeqT. apply Qmult_0_l.
  - apply Qle_to_QleT'.
    apply (Qmult_le_compat_r 0 (Qmake (Z.of_nat m) 1) w).
    + unfold Qle. cbn [Qnum Qden]. lia.
    + apply (Qlt_le_weak 0 w (QltT_to_Qlt _ _ Hw)).
Qed.

(* 0 <= q implies 0 <= q^m. *)
Lemma mixd_qpow_nonneg : forall (q : Q) (Hq : QleT' 0 q) (m : nat),
  QleT' 0 (igr_qpow q m).
Proof.
  intros q Hq m. induction m as [| m IH].
  - cbn [igr_qpow]. apply Qle_to_QleT'. unfold Qle. cbn [Qnum Qden]. lia.
  - cbn [igr_qpow].
    apply Qle_to_QleT'.
    exact (Qmult_le_0_compat q (igr_qpow q m) (QleT'_to_Qle _ _ Hq) (QleT'_to_Qle _ _ IH)).
Qed.

(* e > 0 implies e*(1/2) < e. *)
Lemma mixd_half_lt : forall e : Q, QltT 0 e -> QltT (e * (1#2)) e.
Proof.
  intros e He.
  apply (mixd_qlt_eq_l ((1#2) * e) (e * (1#2)) e).
  - apply qeq_imp_qeqT. ring.
  - apply (mixd_qlt_eq_r ((1#2) * e) (1 * e) e).
    + apply qeq_imp_qeqT. apply Qmult_1_l.
    + apply Qlt_to_QltT.
      exact (Qmult_lt_compat_r (1#2) 1 e (QltT_to_Qlt _ _ He)
                (QltT_to_Qlt _ _ mixd_half_lt_one)).
Qed.

(* Left multiplication preserves order (stdlib only has the _r form). *)
Lemma mixd_qmult_le_compat_l : forall x y z : Q,
  QleT' x y -> QleT' 0 z -> QleT' (z * x) (z * y).
Proof.
  intros x y z Hxy Hz.
  apply (mixd_qle_eq_l (x * z) (z * x) (z * y)).
  - apply qeq_imp_qeqT. ring.
  - apply (mixd_qle_eq_r (x * z) (y * z) (z * y)).
    + apply qeq_imp_qeqT. ring.
    + apply Qle_to_QleT'.
      exact (Qmult_le_compat_r x y z (QleT'_to_Qle _ _ Hxy) (QleT'_to_Qle _ _ Hz)).
Qed.

(* Part 1: power monotonicity (Q-layer direct). *)

Lemma mixd_qpow_le1 : forall (q : Q) (Hq1 : QleT' q 1) (Hq0 : QleT' 0 q) (m : nat),
  QleT' (igr_qpow q m) 1.
Proof.
  intros q Hq1 Hq0 m. induction m as [| m IH].
  - cbn [igr_qpow]. apply Qle_to_QleT'. apply Qle_refl.
  - cbn [igr_qpow].
    apply Qle_to_QleT'.
    apply (Qle_trans _ (igr_qpow q m) 1).
    + exact (QleT'_to_Qle _ _ (mixd_qle_eq_r (q * igr_qpow q m) (1 * igr_qpow q m)
                                 (igr_qpow q m)
                                 (qeq_imp_qeqT _ _ (Qmult_1_l (igr_qpow q m)))
                                 (Qle_to_QleT' _ _
                                    (Qmult_le_compat_r q 1 (igr_qpow q m)
                                       (QleT'_to_Qle _ _ Hq1)
                                       (QleT'_to_Qle _ _ (mixd_qpow_nonneg q Hq0 m)))))).
    + exact (QleT'_to_Qle _ _ IH).
Qed.

(* Strictly-positive base, antitone exponent: a <= b implies q^b <= q^a. *)
Lemma mixd_qpow_anti : forall (q : Q) (Hq0 : QltT 0 q) (Hq1 : QleT' q 1)
    (b a : nat), NatLe a b -> QleT' (igr_qpow q b) (igr_qpow q a).
Proof.
  intros q Hq0 Hq1 b. induction b as [| b IH]; intros a Hab.
  - pose proof (NatLe_drop a 0%nat Hab) as Ha0le.
    assert (Ha0 : a = 0%nat) by lia. subst a.
    cbn [igr_qpow]. apply Qle_to_QleT'. apply Qle_refl.
  - destruct a as [| a].
    + apply (mixd_qle_eq_r (igr_qpow q (Datatypes.S b)) 1%Q (igr_qpow q 0%nat)).
      * apply qeq_imp_qeqT. exact (Qeq_refl 1).
      * exact (mixd_qpow_le1 q Hq1 (qltT_leT' 0 q Hq0) (Datatypes.S b)).
    + pose proof (NatLe_drop a b Hab) as Ha'.
      assert (Ha'le : (a <= b)%nat) by lia.
      apply Qle_to_QleT'.
      apply (Qle_trans _ (q * igr_qpow q a) (igr_qpow q (Datatypes.S a))).
      * cbn [igr_qpow].
        exact (QleT'_to_Qle _ _ (mixd_qmult_le_compat_l (igr_qpow q b) (igr_qpow q a) q
                   (IH a Hab) (qltT_leT' 0 q Hq0))).
      * apply Qle_refl.
Qed.

(* Strict failure downward: a <= b and b fails implies a fails. *)
Lemma mixd_fail_down : forall (k0 v b0 : Q) (Hq0 : QltT 0 k0) (Hq1 : QleT' k0 1)
    (Hv : QleT' 0 v) (a b : nat), NatLe a b ->
  QltT b0 (Qmult (igr_qpow k0 b) v) -> QltT b0 (Qmult (igr_qpow k0 a) v).
Proof.
  intros k0 v b0 Hq0 Hq1 Hv a b Hab Hb.
  apply Qlt_to_QltT.
  apply (Qlt_le_trans b0 (Qmult (igr_qpow k0 b) v) (Qmult (igr_qpow k0 a) v)).
  - exact (QltT_to_Qlt _ _ Hb).
  - apply (Qmult_le_compat_r _ _ v).
    + exact (QleT'_to_Qle _ _ (mixd_qpow_anti k0 Hq0 Hq1 b a Hab)).
    + exact (QleT'_to_Qle _ _ Hv).
Qed.

(* Part 2: ladder and binary weights. *)

Fixpoint mixd_two_pow (i : nat) : nat :=
  match i with
  | Datatypes.O => 1%nat
  | Datatypes.S j => 2 * mixd_two_pow j
  end.

Lemma mixd_two_pow_ge : forall i : nat, NatLe (Datatypes.S i) (mixd_two_pow i).
Proof.
  induction i as [| i IH].
  - cbn [mixd_two_pow]. apply NatLe_lift. lia.
  - cbn [mixd_two_pow].
    pose proof (NatLe_drop (Datatypes.S i) (mixd_two_pow i) IH).
    apply NatLe_lift. lia.
Qed.

(* Ladder: kappa_0^(2^i) (repeated squaring, exactly one multiplication per level). *)
Fixpoint mixd_ladder (k0 : Q) (i : nat) : Q :=
  match i with
  | Datatypes.O => k0
  | Datatypes.S j => Qmult (mixd_ladder k0 j) (mixd_ladder k0 j)
  end.

Lemma mixd_qpow_plus : forall (q : Q) (a b : nat),
  QeqT (igr_qpow q (a + b)) (igr_qpow q a * igr_qpow q b).
Proof.
  intros q a b. induction a as [| a IH].
  - cbn [igr_qpow Nat.add]. apply qeq_imp_qeqT. symmetry. apply Qmult_1_l.
  - cbn [igr_qpow Nat.add].
    apply qeq_imp_qeqT.
    apply (Qeq_trans _ (q * (igr_qpow q a * igr_qpow q b)) _).
    + exact (qeqT_imp_qeq _ _
               (mixd_qeq_mult_l (igr_qpow q (a + b))
                  (igr_qpow q a * igr_qpow q b) q IH)).
    + ring.
Qed.

(* Ladder correctness: mixd_ladder k0 i is kappa_0^(2^i), returned as a QeqT certificate. *)
Lemma mixd_ladder_spec : forall (k0 : Q) (i : nat),
  QeqT (mixd_ladder k0 i) (igr_qpow k0 (mixd_two_pow i)).
Proof.
  intros k0 i. induction i as [| i IH].
  - cbn [mixd_ladder mixd_two_pow igr_qpow].
    apply qeq_imp_qeqT. symmetry. apply Qmult_1_r.
  - apply qeq_imp_qeqT.
    cbn [mixd_ladder].
    replace (mixd_two_pow (Datatypes.S i))
      with (mixd_two_pow i + mixd_two_pow i)%nat
      by (cbn [mixd_two_pow]; lia).
    apply (Qeq_trans _ (igr_qpow k0 (mixd_two_pow i)
                          * igr_qpow k0 (mixd_two_pow i)) _).
    + apply (Qeq_trans _ (igr_qpow k0 (mixd_two_pow i)
                            * mixd_ladder k0 i) _).
      * exact (qeqT_imp_qeq _ _
                 (mixd_qeq_mult_r (mixd_ladder k0 i)
                    (igr_qpow k0 (mixd_two_pow i)) (mixd_ladder k0 i) IH)).
      * exact (qeqT_imp_qeq _ _
                 (mixd_qeq_mult_l (mixd_ladder k0 i)
                    (igr_qpow k0 (mixd_two_pow i))
                    (igr_qpow k0 (mixd_two_pow i)) IH)).
    + apply (Qeq_sym _ _
               (qeqT_imp_qeq _ _
                  (mixd_qpow_plus k0 (mixd_two_pow i) (mixd_two_pow i)))).
Qed.

(* Scan-segment runtime certificate: acc == ladder i implies QeqT (acc*v) (kappa_0^(2^i) * v). *)
Lemma mixd_acc_cert : forall (k0 v : Q) (i : nat) (acc : Q),
  QeqT acc (mixd_ladder k0 i) ->
  QeqT (Qmult acc v) (Qmult (igr_qpow k0 (mixd_two_pow i)) v).
Proof.
  intros k0 v i acc Hacc.
  apply qeq_imp_qeqT.
  transitivity (mixd_ladder k0 i * v).
  - apply (@Qmult_comp acc (mixd_ladder k0 i) (qeqT_imp_qeq _ _ Hacc)
             v v (Qeq_refl v)).
  - apply (@Qmult_comp (mixd_ladder k0 i) (igr_qpow k0 (mixd_two_pow i))
             (qeqT_imp_qeq _ _ (mixd_ladder_spec k0 i)) v v (Qeq_refl v)).
Defined.

Lemma mixd_qeqT_one_mul : forall v : Q, QeqT (1 * v) v.
Proof. intro v. apply qeq_imp_qeqT. apply Qmult_1_l. Qed.

Lemma mixd_qeqT_sym : forall a b : Q, QeqT a b -> QeqT b a.
Proof.
  intros a b H. apply qeq_imp_qeqT. symmetry.
  exact (qeqT_imp_qeq a b H).
Qed.

(* Ladder squaring self-consistency: p == kappa_0^(2^j) implies p*p == kappa_0^(2^(S j)). *)
Lemma mixd_qeq_sq : forall (k0 : Q) (j : nat) (p : Q),
  QeqT p (igr_qpow k0 (mixd_two_pow j)) ->
  QeqT (p * p) (igr_qpow k0 (mixd_two_pow (Datatypes.S j))).
Proof.
  intros k0 j p Hp.
  replace (mixd_two_pow (Datatypes.S j))
    with (mixd_two_pow j + mixd_two_pow j)%nat
    by (cbn [mixd_two_pow]; lia).
  apply qeq_imp_qeqT.
  apply (Qeq_trans _ (igr_qpow k0 (mixd_two_pow j)
                        * igr_qpow k0 (mixd_two_pow j)) _).
  - exact (@Qmult_comp p (igr_qpow k0 (mixd_two_pow j)) (qeqT_imp_qeq _ _ Hp)
             p (igr_qpow k0 (mixd_two_pow j)) (qeqT_imp_qeq _ _ Hp)).
  - apply (Qeq_sym _ _
             (qeqT_imp_qeq _ _ (mixd_qpow_plus k0 (mixd_two_pow j)
                                  (mixd_two_pow j)))).
Qed.

(* Single-step value ledger at rung S j. *)
Lemma mixd_qeq_step : forall (k0 v : Q) (j k : nat) (p val : Q),
  QeqT p (igr_qpow k0 (mixd_two_pow (Datatypes.S j))) ->
  QeqT val (igr_qpow k0 k * v) ->
  QeqT (val * p) (igr_qpow k0 (k + mixd_two_pow (Datatypes.S j)) * v).
Proof.
  intros k0 v j k p val Hp Hval.
  apply qeq_imp_qeqT.
  apply (Qeq_trans _ (igr_qpow k0 k * v * p) _).
  - exact (qeqT_imp_qeq _ _ (mixd_qeq_mult_r val (igr_qpow k0 k * v) p Hval)).
  - apply (Qeq_trans _
             (igr_qpow k0 k * v
                * igr_qpow k0 (mixd_two_pow (Datatypes.S j))) _).
    + exact (qeqT_imp_qeq _ _
               (mixd_qeq_mult_l p
                  (igr_qpow k0 (mixd_two_pow (Datatypes.S j)))
                  (igr_qpow k0 k * v) Hp)).
    + apply (Qeq_trans _
               (igr_qpow k0 k
                  * (v * igr_qpow k0 (mixd_two_pow (Datatypes.S j)))) _).
      * apply (Qeq_sym _ _ (Qmult_assoc (igr_qpow k0 k) v
                  (igr_qpow k0 (mixd_two_pow (Datatypes.S j))))).
      * apply (Qeq_trans _
                 (igr_qpow k0 k
                    * (igr_qpow k0 (mixd_two_pow (Datatypes.S j)) * v)) _).
        -- exact (qeqT_imp_qeq _ _
                    (mixd_qeq_mult_l
                       (v * igr_qpow k0 (mixd_two_pow (Datatypes.S j)))
                       (igr_qpow k0 (mixd_two_pow (Datatypes.S j)) * v)
                       (igr_qpow k0 k)
                       (qeq_imp_qeqT _ _ (Qmult_comm v
                          (igr_qpow k0 (mixd_two_pow (Datatypes.S j))))))).
        -- apply (Qeq_trans _
                     ((igr_qpow k0 k
                       * igr_qpow k0 (mixd_two_pow (Datatypes.S j)))
                      * v) _).
           ++ apply (Qmult_assoc (igr_qpow k0 k)
                       (igr_qpow k0 (mixd_two_pow (Datatypes.S j))) v).
           ++ exact (qeqT_imp_qeq _ _
                       (mixd_qeq_mult_r
                          (igr_qpow k0 k
                             * igr_qpow k0 (mixd_two_pow (Datatypes.S j)))
                          (igr_qpow k0
                             (k + mixd_two_pow (Datatypes.S j))) v
                          (mixd_qeqT_sym _ _
                             (mixd_qpow_plus k0 k
                                (mixd_two_pow (Datatypes.S j)))))).
Qed.

(* Value ledger at rung 0. *)
Lemma mixd_qeq_step0 : forall (k0 v : Q) (k : nat) (p val : Q),
  QeqT p (igr_qpow k0 (mixd_two_pow 0%nat)) ->
  QeqT val (igr_qpow k0 k * v) ->
  QeqT (val * p) (igr_qpow k0 (Datatypes.S k) * v).
Proof.
  intros k0 v k p val Hp Hval.
  cbn [mixd_two_pow] in Hp.
  replace (Datatypes.S k) with (k + 1)%nat by lia.
  apply qeq_imp_qeqT.
  apply (Qeq_trans _ (igr_qpow k0 k * v * p) _).
  - exact (qeqT_imp_qeq _ _ (mixd_qeq_mult_r val (igr_qpow k0 k * v) p Hval)).
  - apply (Qeq_trans _ (igr_qpow k0 k * v * igr_qpow k0 1) _).
    + exact (qeqT_imp_qeq _ _ (mixd_qeq_mult_l p (igr_qpow k0 1) (igr_qpow k0 k * v) Hp)).
    + apply (Qeq_trans _ (igr_qpow k0 k * (v * igr_qpow k0 1)) _).
      * apply (Qeq_sym _ _ (Qmult_assoc (igr_qpow k0 k) v (igr_qpow k0 1))).
      * apply (Qeq_trans _ (igr_qpow k0 k * (igr_qpow k0 1 * v)) _).
        -- exact (qeqT_imp_qeq _ _
                    (mixd_qeq_mult_l (v * igr_qpow k0 1) (igr_qpow k0 1 * v)
                       (igr_qpow k0 k)
                       (qeq_imp_qeqT _ _ (Qmult_comm v (igr_qpow k0 1))))).
        -- apply (Qeq_trans _ ((igr_qpow k0 k * igr_qpow k0 1) * v) _).
           ++ apply (Qmult_assoc (igr_qpow k0 k) (igr_qpow k0 1) v).
           ++ exact (qeqT_imp_qeq _ _
                       (mixd_qeq_mult_r (igr_qpow k0 k * igr_qpow k0 1)
                          (igr_qpow k0 (k + 1)) v
                          (mixd_qeqT_sym _ _ (mixd_qpow_plus k0 k 1)))).
Qed.

(* Part 3: Set-layer deciders (boolean match; dead-branch fallback is a legal value construction). *)

Definition mixd_dec_le (x y : Q)
  : sum (Id (Qle_bool x y) true) (Id (Qle_bool x y) false) :=
  match Qle_bool x y as b return
      sum (Id b true) (Id b false) with
  | true => inl id_refl
  | false => inr id_refl
  end.

Definition mixd_dec_leb (m n : nat)
  : sum (NatLe m n) (Id (Nat.leb m n) false) :=
  match Nat.leb m n as b return
      sum (Id b true) (Id b false) with
  | true => inl id_refl
  | false => inr id_refl
  end.

(* Id (Qle_bool x y) false to the strict failure face. *)
Lemma mixd_qleF_lt : forall x y : Q,
  Id (Qle_bool x y) false -> QltT y x.
Proof.
  intros x y H.
  assert (Hn : ~ (x <= y)).
  { intro Hc.
    assert (Ht : Qle_bool x y = true) by (apply Qle_bool_iff; exact Hc).
    rewrite Ht in H. inversion H. }
  exact (Qlt_to_QltT _ _ (Qnot_le_lt x y Hn)).
Qed.

(* Part 4: Q-core certificate selectors (Defined, extractable). *)

Definition mixd_rung_cert (k0 v b0 : Q) (j : nat) : Set :=
  QleT' (Qmult (igr_qpow k0 (mixd_two_pow j)) v) b0.

Definition mixd_ans_cert (k0 v b0 : Q) (k : nat) : Set :=
  QleT' (Qmult (igr_qpow k0 k) v) b0.

(* Upward scan: at most d rungs; returns the first passing rung (Set certificate),
   the previous failed rung value, and the multiplication count. The Hacc thread
   carries acc == ladder i as a QeqT data premise. *)
Fixpoint mixd_scan_up (k0 v b0 : Q) (d i : nat) (pacc acc : Q) (c : nat)
    (Hacc : QeqT acc (mixd_ladder k0 i))
  : option (sigT (fun j : nat => mixd_rung_cert k0 v b0 j) * Q * nat) :=
  match d with
  | Datatypes.O =>
      match mixd_dec_le (Qmult acc v) b0 with
      | inl Hp =>
          Some (existT _ i
                  (mixd_leT_transport (Qmult acc v)
                     (Qmult (igr_qpow k0 (mixd_two_pow i)) v) b0
                     (mixd_acc_cert k0 v i acc Hacc)
                     Hp),
                pacc, Datatypes.S c)
      | inr _ => None
      end
  | Datatypes.S d' =>
      match mixd_dec_le (Qmult acc v) b0 with
      | inl Hp =>
          Some (existT _ i
                  (mixd_leT_transport (Qmult acc v)
                     (Qmult (igr_qpow k0 (mixd_two_pow i)) v) b0
                     (mixd_acc_cert k0 v i acc Hacc)
                     Hp),
                pacc, Datatypes.S c)
      | inr _ =>
          mixd_scan_up k0 v b0 d' (Datatypes.S i) acc
            (Qmult acc acc) (Datatypes.S (Datatypes.S c))
            (qeq_imp_qeqT _ _
               (@Qmult_comp acc (mixd_ladder k0 i) (qeqT_imp_qeq _ _ Hacc)
                  acc (mixd_ladder k0 i) (qeqT_imp_qeq _ _ Hacc)))
      end
  end.

(* Binary fallback composition (greedy add-on-failure): bit j has weight 2^j;
   a failing candidate k + 2^j adds the bit. *)
Fixpoint mixd_desc (k0 v b0 : Q) (j : nat) (k : nat) (val : Q) (c : nat)
  : nat * nat :=
  match j with
  | Datatypes.O =>
      match mixd_dec_le (Qmult val (mixd_ladder k0 0)) b0 with
      | inl _ => (k, Datatypes.S c)
      | inr _ => (Datatypes.S k, Datatypes.S (Datatypes.S c))
      end
  | Datatypes.S j' =>
      match mixd_dec_le (Qmult val (mixd_ladder k0 (Datatypes.S j'))) b0 with
      | inl _ => mixd_desc k0 v b0 j' k val (Datatypes.S (Datatypes.S c))
      | inr _ =>
          mixd_desc k0 v b0 j' (k + mixd_two_pow (Datatypes.S j'))%nat
            (Qmult val (mixd_ladder k0 (Datatypes.S j')))
            (Datatypes.S (Datatypes.S (Datatypes.S c)))
      end
  end.

(* Top-level selector (Defined, certificate-returning): the k = 0 branch is tested first;
   otherwise the first passing rung of the upward scan plus the binary fallback
   composition yields the failure bit kf; the top branch guard tests S kf directly
   (inl returns the passing certificate; inr is a semantically dead branch whose
   fallback is the top rung -- a legal construction). *)
Definition mixd_k_select_log_cert (k0 v b0 : Q) (h0 : QltT 0 k0)
    (h1 : QleT' k0 1) (hv : QleT' 0 v) (d : nat)
  : option ((sum (sigT (fun k : nat => mixd_ans_cert k0 v b0 k))
                 (sigT (fun k : nat => mixd_ans_cert k0 v b0 k))) * nat) :=
  match mixd_dec_le v b0 with
  | inl Hp0 =>
      Some (inl (existT _ 0%nat
                   (mixd_leT_transport v (1 * v) b0
                      (mixd_qeqT_sym (1 * v) v (mixd_qeqT_one_mul v)) Hp0)),
            1%nat)
  | inr _ =>
      match mixd_scan_up k0 v b0 d 0%nat k0 k0 0%nat
              (qeq_imp_qeqT k0 k0 (Qeq_refl k0)) with
      | None => None
      | Some (existT _ i Htop, pacc, c1) =>
          let kfc :=
            match i with
            | Datatypes.O => (0%nat, 0%nat)
            | Datatypes.S i' => mixd_desc k0 v b0 i' 0%nat v 0%nat
            end in
          match mixd_dec_le (Qmult (igr_qpow k0 (Datatypes.S (fst kfc))) v) b0 with
          | inl Hpass =>
              Some (inl (existT _ (Datatypes.S (fst kfc)) Hpass),
                    (c1 + snd kfc)%nat)
          | inr _ =>
              Some (inr (existT _ (mixd_two_pow i) Htop),
                    (c1 + snd kfc)%nat)
          end
      end
  end.

(* Part 5: Q-Bernoulli and the window (Q layer computes its own account). *)

(* m*w <= 1 + m*w for w > 0. *)
Lemma mixd_mw_le_boost : forall (m : nat) (w : Q) (Hw : QltT 0 w),
  QleT' (Qmake (Z.of_nat m) 1 * w) (1 + Qmake (Z.of_nat m) 1 * w).
Proof.
  intros m w Hw.
  apply (mixd_qle_eq_l (Qplus 0 (Qmake (Z.of_nat m) 1 * w))
           (Qmake (Z.of_nat m) 1 * w)
           (Qplus 1 (Qmake (Z.of_nat m) 1 * w))).
  - apply qeq_imp_qeqT. apply Qplus_0_l.
  - apply Qle_to_QleT'.
    apply (Qplus_le_compat 0 1 (Qmake (Z.of_nat m) 1 * w)
             (Qmake (Z.of_nat m) 1 * w)).
    + unfold Qle. cbn [Qnum Qden]. lia.
    + apply Qle_refl.
Qed.

(* Q-Bernoulli step bridge: Qmake (Z.of_nat (S m)) 1 == 1 + Qmake (Z.of_nat m) 1. *)
Lemma mixd_qnat_succ : forall m : nat,
  QeqT (Qmake (Z.of_nat (Datatypes.S m)) 1) ((1 + Qmake (Z.of_nat m) 1)%Q).
Proof.
  intro m. apply qeq_imp_qeqT. unfold Qeq, Qplus. cbn [Qnum Qden]. lia.
Qed.

(* Q-Bernoulli: (1-w)^m * (1 + m*w) <= 1 for 0 <= w <= 1. *)
Lemma mixd_qbern : forall (w : Q) (Hw0 : QleT' 0 w) (Hw1 : QleT' w 1) (m : nat),
  QleT' (Qmult (igr_qpow (1 - w) m) (1 + Qmake (Z.of_nat m) 1 * w)) 1.
Proof.
  intros w Hw0 Hw1 m.
  pose proof (QleT'_to_Qle 0 w Hw0) as Hw0q.
  pose proof (QleT'_to_Qle _ _ (mixd_qsub_ge0 w Hw1)) as Hq0.
  pose proof (QleT'_to_Qle _ _ (mixd_qsub_le w Hw0)) as Hq1.
  induction m as [| m IH].
  - cbn [igr_qpow Z.of_nat].
    apply (mixd_qle_eq_l (1 * (1 + Qmake 0 1 * w)) (1 * (1 + 0 * w)) 1).
    + apply qeq_imp_qeqT. apply Qmult_1_l.
    + apply Qle_to_QleT'.
      rewrite Qmult_0_l. rewrite Qplus_0_r. rewrite Qmult_1_l.
      apply Qle_refl.
  - apply (mixd_qle_eq_l
             (Qplus (Qmult (1 - w)
                             (Qmult (igr_qpow (1 - w) m)
                                    (Qplus 1
                                       (Qmult (Qmake (Z.of_nat m) 1) w))))
                    (Qmult (igr_qpow (1 - w) (Datatypes.S m)) w))
             (Qmult (igr_qpow (1 - w) (Datatypes.S m))
                (Qplus 1 (Qmult (Qmake (Z.of_nat (Datatypes.S m)) 1) w)))
             1).
    + apply qeq_imp_qeqT.
      cbn [igr_qpow].
      rewrite (qeqT_imp_qeq _ _ (mixd_qnat_succ m)). ring.
    + apply Qle_to_QleT'.
      apply (Qle_trans _ (Qplus (1 - w) w) _).
      * apply Qplus_le_compat.
        -- (* (1-w)*(q^m*(1+M*w)) <= 1-w: IH right-multiplied by (1-w). *)
           assert (Hop1 : QleT' (Qmult (1 - w)
                                   (Qmult (igr_qpow (1 - w) m)
                                          (Qplus 1 (Qmult (Qmake (Z.of_nat m) 1) w))))
                           (Qmult 1 (1 - w))).
           { apply (mixd_qle_eq_l
                      (Qmult (Qmult (igr_qpow (1 - w) m)
                                    (Qplus 1 (Qmult (Qmake (Z.of_nat m) 1) w)))
                             (1 - w))
                      (Qmult (1 - w)
                              (Qmult (igr_qpow (1 - w) m)
                                     (Qplus 1 (Qmult (Qmake (Z.of_nat m) 1) w))))
                      (Qmult 1 (1 - w))
                      (qeq_imp_qeqT _ _
                         (Qmult_comm (Qmult (igr_qpow (1 - w) m)
                                        (Qplus 1 (Qmult (Qmake (Z.of_nat m) 1) w)))
                            (1 - w)))
                      (Qle_to_QleT' _ _
                         (Qmult_le_compat_r _ _ (1 - w)
                            (QleT'_to_Qle _ _ IH) Hq0))). }
           assert (Hop2 : QleT' (Qmult 1 (1 - w)) (1 - w)).
           { exact (mixd_qle_eq_r (Qmult 1 (1 - w)) (1 - w) (1 - w)
                      (qeq_imp_qeqT _ _ (Qeq_refl (1 - w)))
                      (mixd_qle_eq_l (1 - w) (Qmult 1 (1 - w)) (1 - w)
                         (qeq_imp_qeqT _ _ (Qeq_sym _ _ (Qmult_1_l (1 - w))))
                         (Qle_to_QleT' _ _ (Qle_refl (1 - w))))). }
           exact (QleT'_to_Qle _ _
                    (mixd_qleT'_trans (Qmult (1 - w)
                                         (Qmult (igr_qpow (1 - w) m)
                                                (Qplus 1 (Qmult (Qmake (Z.of_nat m) 1) w))))
                       (Qmult 1 (1 - w)) (1 - w) Hop1 Hop2)).
        -- (* q^(S m)*w <= w: mixd_qpow_le1 + compat_r double hop. *)
           assert (HX1T : QleT' (igr_qpow (1 - w) m) 1)
             by exact (mixd_qpow_le1 (1 - w) (mixd_qsub_le w Hw0) (mixd_qsub_ge0 w Hw1) m).
           assert (Hpw0 : QleT' (Qmult (Qmult (1 - w) (igr_qpow (1 - w) m)) w)
                             (Qmult 1 w)).
           { apply Qle_to_QleT'.
             apply (Qmult_le_compat_r _ _ w
                (Qle_trans (Qmult (1 - w) (igr_qpow (1 - w) m)) (1 - w) 1
                   (QleT'_to_Qle _ _
                      (mixd_qle_eq_r
                         (Qmult (1 - w) (igr_qpow (1 - w) m))
                         (Qmult (1 - w) 1) (1 - w)
                         (qeq_imp_qeqT _ _ (Qmult_1_r (1 - w)))
                         (mixd_qmult_le_compat_l
                            (igr_qpow (1 - w) m) 1 (1 - w)
                            HX1T (Qle_to_QleT' _ _ Hq0))))
                   Hq1)
                Hw0q). }
           assert (Hpw : QleT' (Qmult (Qmult (1 - w) (igr_qpow (1 - w) m)) w) w).
           { exact (mixd_qle_eq_r (Qmult (Qmult (1 - w) (igr_qpow (1 - w) m)) w)
                      (Qmult 1 w) w
                      (qeq_imp_qeqT _ _ (Qmult_1_l w)) Hpw0). }
           exact (QleT'_to_Qle _ _
                    (mixd_qle_eq_l
                       (Qmult (Qmult (1 - w) (igr_qpow (1 - w) m)) w)
                       (Qmult (igr_qpow (1 - w) (Datatypes.S m)) w)
                       w
                       (qeq_imp_qeqT (Qmult (Qmult (1 - w) (igr_qpow (1 - w) m)) w)
                          (Qmult (igr_qpow (1 - w) (Datatypes.S m)) w)
                          (Qeq_refl (Qmult (igr_qpow (1 - w) (Datatypes.S m)) w)))
                       Hpw)).
      * assert (Heqfin : QeqT (Qplus (1 - w) w) 1).
        { apply qeq_imp_qeqT. ring. }
        exact (QleT'_to_Qle _ _
                 (mixd_qle_eq_r (Qplus (1 - w) w) (Qplus (1 - w) w) 1
                    Heqfin
                    (Qle_to_QleT' _ _ (Qle_refl (Qplus (1 - w) w))))).
Qed.

(* Window item: v <= m*(w*b0) implies kappa_0^m*v <= b0 (QleT' return face). *)
Lemma mixd_window_pass : forall (k0 v b0 w : Q) (m : nat)
    (Hk0 : QltT 0 k0) (Hk1 : QleT' k0 1) (Hv : QleT' 0 v) (Hb0 : QltT 0 b0)
    (Hw : QeqT w (1 - k0)) (Hwp : QltT 0 w)
    (Hn : QleT' v (Qmult (Qmake (Z.of_nat m) 1) (Qmult w b0))),
  QleT' (Qmult (igr_qpow k0 m) v) b0.
Proof.
  intros k0 v b0 w m Hk0 Hk1 Hv Hb0 Hw Hwp Hn.
  pose proof (QltT_to_Qlt 0 b0 Hb0) as Hb0q.
  pose proof (QltT_to_Qlt 0 w Hwp) as Hwpq.
  assert (Hb0le : (0 <= b0)%Q) by exact (Qlt_le_weak 0 b0 Hb0q).
  assert (Hwb0 : (0 <= w * b0)%Q).
  { apply (Qle_trans 0 (0 * b0) (w * b0)).
    - rewrite Qmult_0_l. apply Qle_refl.
    - apply (Qmult_le_compat_r _ _ b0).
      + apply (Qlt_le_weak 0 w Hwpq).
      + exact Hb0le. }
  assert (Hk0nn : QleT' 0 (igr_qpow k0 m))
    by exact (mixd_qpow_nonneg k0 (qltT_leT' 0 k0 Hk0) m).
  assert (Hmono : QleT' (Qmult (Qmult (Qmake (Z.of_nat m) 1) w) b0)
                        (Qmult (Qplus 1 (Qmake (Z.of_nat m) 1 * w)) b0)).
  { apply Qle_to_QleT'.
    apply (Qmult_le_compat_r _ _ b0).
    - exact (QleT'_to_Qle _ _ (mixd_mw_le_boost m w Hwp)).
    - exact Hb0le. }
  assert (Hbern : QleT' (Qmult (igr_qpow (1 - w) m)
                            (Qplus 1 (Qmake (Z.of_nat m) 1 * w))) 1).
  { exact (mixd_qbern w (qltT_leT' 0 w Hwp)
             (Qle_to_QleT' _ _
                (Qle_trans w (1 - k0) 1
                   (QleT'_to_Qle _ _ (qeq_leT' w (1 - k0) Hw))
                   (QleT'_to_Qle _ _ (mixd_qsub_le k0 (qltT_leT' 0 k0 Hk0)))))
             m). }
  assert (Hpowcompat : QeqT (igr_qpow (1 - w) m) (igr_qpow k0 m)).
  { apply (mixd_qpow_eq_compat (1 - w) k0).
    apply (mixd_qeqT_trans_l (1 - w) (1 - (1 - k0)) k0).
    - apply qeq_imp_qeqT.
      exact (@Qminus_comp 1 1 (Qeq_refl 1) w (1 - k0) (qeqT_imp_qeq w (1 - k0) Hw)).
    - apply qeq_imp_qeqT. ring. }
  assert (Hbern1 : QleT' (Qmult (igr_qpow k0 m)
                             (Qplus 1 (Qmake (Z.of_nat m) 1 * w))) 1).
  { exact (mixd_qle_eq_l (Qmult (igr_qpow (1 - w) m)
                              (Qplus 1 (Qmake (Z.of_nat m) 1 * w)))
                         (Qmult (igr_qpow k0 m)
                            (Qplus 1 (Qmake (Z.of_nat m) 1 * w)))
                         1
                         (qeq_imp_qeqT _ _
                            (@Qmult_comp (igr_qpow (1 - w) m) (igr_qpow k0 m)
                               (qeqT_imp_qeq _ _ Hpowcompat)
                               (Qplus 1 (Qmake (Z.of_nat m) 1 * w))
                               (Qplus 1 (Qmake (Z.of_nat m) 1 * w))
                               (Qeq_refl _)))
                         Hbern). }
  assert (Hbig : QleT' (Qmult (Qmult (igr_qpow k0 m)
                                  (Qplus 1 (Qmake (Z.of_nat m) 1 * w))) b0)
                       (Qmult 1 b0)).
  { apply Qle_to_QleT'.
    apply (Qmult_le_compat_r _ _ b0).
    - exact (QleT'_to_Qle _ _ Hbern1).
    - exact Hb0le. }
  assert (Hchain1 : QleT' (Qmult (igr_qpow k0 m)
                              (Qmult (Qmult (Qmake (Z.of_nat m) 1) w) b0))
                         (Qmult 1 b0)).
  { apply (mixd_qleT'_trans
             (Qmult (igr_qpow k0 m) (Qmult (Qmult (Qmake (Z.of_nat m) 1) w) b0))
             (Qmult (igr_qpow k0 m)
                (Qmult (Qplus 1 (Qmake (Z.of_nat m) 1 * w)) b0))
             (Qmult 1 b0)).
    - exact (mixd_qmult_le_compat_l
               (Qmult (Qmult (Qmake (Z.of_nat m) 1) w) b0)
               (Qmult (Qplus 1 (Qmake (Z.of_nat m) 1 * w)) b0)
               (igr_qpow k0 m) Hmono Hk0nn).
    - exact (mixd_qle_eq_l
               (Qmult (Qmult (igr_qpow k0 m)
                          (Qplus 1 (Qmake (Z.of_nat m) 1 * w))) b0)
               (Qmult (igr_qpow k0 m)
                  (Qmult (Qplus 1 (Qmake (Z.of_nat m) 1 * w)) b0))
               (Qmult 1 b0)
               (qeq_imp_qeqT _ _
                  (Qeq_sym _ _
                     (Qmult_assoc (igr_qpow k0 m)
                        (Qplus 1 (Qmake (Z.of_nat m) 1 * w)) b0)))
               Hbig). }
  apply Qle_to_QleT'.
  apply (Qle_trans _ (Qmult (igr_qpow k0 m)
                        (Qmult (Qmake (Z.of_nat m) 1) (Qmult w b0))) _).
  - exact (QleT'_to_Qle _ _
             (mixd_qmult_le_compat_l _ _ (igr_qpow k0 m) Hn Hk0nn)).
  - exact (QleT'_to_Qle _ _
             (mixd_qle_eq_l
                (Qmult (igr_qpow k0 m)
                   (Qmult (Qmult (Qmake (Z.of_nat m) 1) w) b0))
                (Qmult (igr_qpow k0 m)
                   (Qmult (Qmake (Z.of_nat m) 1) (Qmult w b0)))
                b0
                (qeq_imp_qeqT _ _
                   (@Qmult_comp (igr_qpow k0 m) (igr_qpow k0 m) (Qeq_refl _)
                      (Qmult (Qmult (Qmake (Z.of_nat m) 1) w) b0)
                      (Qmult (Qmake (Z.of_nat m) 1) (Qmult w b0))
                      (Qeq_sym _ _ (Qmult_assoc (Qmake (Z.of_nat m) 1) w b0))))
                (mixd_qle_eq_r
                   (Qmult (igr_qpow k0 m)
                      (Qmult (Qmult (Qmake (Z.of_nat m) 1) w) b0))
                   (Qmult 1 b0) b0
                   (qeq_imp_qeqT _ _ (Qmult_1_l b0))
                   Hchain1))).
Qed.

(* Top-level window item: v <= N*(w*b0) and N <= 2^d imply the top rung
   kappa_0^(2^d)*v <= b0. *)
Lemma mixd_window_top_pass : forall (k0 v b0 w : Q) (N d : nat)
    (Hk0 : QltT 0 k0) (Hk1 : QleT' k0 1) (Hv : QleT' 0 v) (Hb0 : QltT 0 b0)
    (Hw : QeqT w (1 - k0)) (Hwp : QltT 0 w)
    (Hn : QleT' v (Qmult (Qmake (Z.of_nat N) 1) (Qmult w b0)))
    (HNd : NatLe N (mixd_two_pow d)),
  QleT' (Qmult (igr_qpow k0 (mixd_two_pow d)) v) b0.
Proof.
  intros k0 v b0 w N d Hk0 Hk1 Hv Hb0 Hw Hwp Hn HNd.
  pose proof (QltT_to_Qlt 0 b0 Hb0) as Hb0q.
  pose proof (QltT_to_Qlt 0 w Hwp) as Hwpq.
  pose proof (NatLe_drop N (mixd_two_pow d) HNd) as HNdq.
  assert (Hwb0 : (0 <= w * b0)%Q).
  { apply (Qle_trans 0 (0 * b0) (w * b0)).
    - rewrite Qmult_0_l. apply Qle_refl.
    - apply (Qmult_le_compat_r _ _ b0).
      + apply (Qlt_le_weak 0 w Hwpq).
      + apply (Qlt_le_weak 0 b0 Hb0q). }
  assert (Hn' : QleT' v (Qmult (Qmake (Z.of_nat (mixd_two_pow d)) 1)
                                 (Qmult w b0))).
  { apply Qle_to_QleT'.
    apply (Qle_trans _ (Qmult (Qmake (Z.of_nat N) 1) (Qmult w b0)) _).
    - exact (QleT'_to_Qle _ _ Hn).
    - apply (Qmult_le_compat_r _ _ (Qmult w b0)).
      + unfold Qle. cbn [Qnum Qden]. lia.
      + exact Hwb0. }
  exact (mixd_window_pass k0 v b0 w (mixd_two_pow d) Hk0 Hk1 Hv Hb0 Hw Hwp
           Hn').
Qed.

(* Part 6: the three selector accounts (sound / min / cost). *)

(* Some-pair injection surrogates (injection is blind to existT payloads at
   the abstract layer; f_equal projects once here). *)
Lemma mixd_some_inj_fst : forall (A : Type) (x y : A) (m n : nat),
  @Some (A * nat) (x, m) = @Some (A * nat) (y, n) -> x = y.
Proof.
  intros A x y m n H.
  exact (f_equal (fun o : option (A * nat) =>
                    match o with
                    | Some p => @fst A nat p
                    | None => x
                    end) H).
Qed.

Lemma mixd_some_inj_snd : forall (A : Type) (x y : A) (m n : nat),
  @Some (A * nat) (x, m) = @Some (A * nat) (y, n) -> m = n.
Proof.
  intros A x y m n H.
  exact (f_equal (fun o : option (A * nat) =>
                    match o with
                    | Some p => @snd A nat p
                    | None => m
                    end) H).
Qed.

Lemma mixd_some_inl_fst : forall (A B : Type) (x y : A) (m n : nat),
  @Some ((A + B) * nat) (@inl A B x, m) =
  @Some ((A + B) * nat) (@inl A B y, n) -> x = y.
Proof.
  intros A B x y m n H.
  exact (f_equal (fun o : option ((A + B) * nat) =>
                    (match o return A with
                     | Some (inl a, _) => a
                     | _ => x
                     end)) H).
Qed.

(* Upward-scan no-solution account: None implies every in-window rung fails. *)
Lemma mixd_scan_up_none : forall (k0 v b0 : Q) (d i : nat) (pacc acc : Q)
    (c : nat) (Hacc : QeqT acc (mixd_ladder k0 i)),
  mixd_scan_up k0 v b0 d i pacc acc c Hacc = None ->
  forall j : nat, NatLe i j -> NatLe j (i + d)%nat ->
  QltT b0 (Qmult (igr_qpow k0 (mixd_two_pow j)) v).
Proof.
  intros k0 v b0 d. induction d as [| d IH];
    intros i pacc acc c Hacc Hnone j Hj1 Hj2.
  - cbn [mixd_scan_up] in Hnone.
    destruct (mixd_dec_le (Qmult acc v) b0) as [Hp | Hf].
    + discriminate Hnone.
    + pose proof (NatLe_drop i j Hj1) as Hj1q.
      pose proof (NatLe_drop j (i + 0)%nat Hj2) as Hj2q.
      assert (Hji : j = i) by lia. subst j.
      apply (mixd_qlt_eq_r b0 (Qmult acc v)
               (Qmult (igr_qpow k0 (mixd_two_pow i)) v)).
      * exact (mixd_acc_cert k0 v i acc Hacc).
      * exact (mixd_qleF_lt _ _ Hf).
  - cbn [mixd_scan_up] in Hnone.
    destruct (mixd_dec_le (Qmult acc v) b0) as [Hp | Hf].
    + discriminate Hnone.
    + pose proof (NatLe_drop i j Hj1) as Hj1q.
      pose proof (NatLe_drop j (i + Datatypes.S d)%nat Hj2) as Hj2q.
      destruct (Nat.eq_dec j i) as [Hje | Hjne].
      * subst j. apply (mixd_qlt_eq_r b0 (Qmult acc v)
               (Qmult (igr_qpow k0 (mixd_two_pow i)) v)).
        -- exact (mixd_acc_cert k0 v i acc Hacc).
        -- exact (mixd_qleF_lt _ _ Hf).
      * assert (Hrec : mixd_scan_up k0 v b0 d (Datatypes.S i) acc
                         (Qmult acc acc) (Datatypes.S (Datatypes.S c))
                         (qeq_imp_qeqT _ _
                            (@Qmult_comp acc (mixd_ladder k0 i)
                               (qeqT_imp_qeq _ _ Hacc)
                               acc (mixd_ladder k0 i) (qeqT_imp_qeq _ _ Hacc)))
                         = None)
          by exact Hnone.
        apply (IH (Datatypes.S i) acc (Qmult acc acc)
                   (Datatypes.S (Datatypes.S c))
                   (qeq_imp_qeqT _ _
                      (@Qmult_comp acc (mixd_ladder k0 i)
                         (qeqT_imp_qeq _ _ Hacc)
                         acc (mixd_ladder k0 i) (qeqT_imp_qeq _ _ Hacc)))
                   Hrec).
        -- apply NatLe_lift. lia.
        -- apply NatLe_lift. lia.
Qed.

(* Upward-scan solution account: j <= i + d, cost <= 2*d + 1, and the previous
   rung value thread, all returned at Set faces. *)
Lemma mixd_scan_up_some : forall (k0 v b0 : Q) (d i : nat) (pacc acc : Q)
    (c : nat) (j : nat) (Hcert : mixd_rung_cert k0 v b0 j) (pacc' : Q)
    (c' : nat)
    (Hacc : QeqT acc (mixd_ladder k0 i)),
  QeqT pacc (mixd_ladder k0 (Nat.pred i)) ->
  mixd_scan_up k0 v b0 d i pacc acc c Hacc
    = Some (existT _ j Hcert, pacc', c') ->
  And (NatLe i j)
      (And (NatLe j (i + d)%nat)
           (And (NatLe c' (c + 2 * d + 1)%nat)
                (QeqT pacc' (mixd_ladder k0 (Nat.pred j))))).
Proof.
  intros k0 v b0 d. induction d as [| d IH];
    intros i pacc acc c j Hcert pacc' c' Hacc Hpa Hsome.
  - cbn [mixd_scan_up] in Hsome.
    revert Hsome.
    destruct (mixd_dec_le (Qmult acc v) b0) as [Hp | Hf].
    + intro Hsome. cbn [mixd_scan_up] in Hsome.
      assert (Hin1 : (existT _ i (mixd_leT_transport (Qmult acc v)
                          (Qmult (igr_qpow k0 (mixd_two_pow i)) v) b0
                          (mixd_acc_cert k0 v i acc Hacc) Hp), pacc)
                    = (existT _ j Hcert, pacc')).
      { apply (mixd_some_inj_fst _ _ _ _ _ Hsome). }
      assert (He : i = j).
      { exact (f_equal (@projT1 nat (fun j0 : nat => mixd_rung_cert k0 v b0 j0))
                 (f_equal (@fst (sigT (fun j0 : nat => mixd_rung_cert k0 v b0 j0)) Q)
                    Hin1)). }
      assert (Hpacc : pacc = pacc')
        by exact (f_equal (@snd (sigT (fun j0 : nat => mixd_rung_cert k0 v b0 j0)) Q) Hin1).
      assert (Hcnt : Datatypes.S c = c')
        by exact (mixd_some_inj_snd _ _ _ _ _ Hsome).
      subst j. subst pacc'. subst c'. repeat split.
      * apply NatLe_lift. lia.
      * apply NatLe_lift. lia.
      * apply NatLe_lift. lia.
      * exact Hpa.
    + intro Hsome. cbn [mixd_scan_up] in Hsome.
      discriminate Hsome.
  - cbn [mixd_scan_up] in Hsome.
    revert Hsome.
    destruct (mixd_dec_le (Qmult acc v) b0) as [Hp | Hf].
    + intro Hsome. cbn [mixd_scan_up] in Hsome.
      assert (Hin1 : (existT _ i (mixd_leT_transport (Qmult acc v)
                          (Qmult (igr_qpow k0 (mixd_two_pow i)) v) b0
                          (mixd_acc_cert k0 v i acc Hacc) Hp), pacc)
                    = (existT _ j Hcert, pacc')).
      { apply (mixd_some_inj_fst _ _ _ _ _ Hsome). }
      assert (He : i = j).
      { exact (f_equal (@projT1 nat (fun j0 : nat => mixd_rung_cert k0 v b0 j0))
                 (f_equal (@fst (sigT (fun j0 : nat => mixd_rung_cert k0 v b0 j0)) Q)
                    Hin1)). }
      assert (Hpacc : pacc = pacc')
        by exact (f_equal (@snd (sigT (fun j0 : nat => mixd_rung_cert k0 v b0 j0)) Q) Hin1).
      assert (Hcnt : Datatypes.S c = c')
        by exact (mixd_some_inj_snd _ _ _ _ _ Hsome).
      subst j. subst pacc'. subst c'. repeat split.
      * apply NatLe_lift. lia.
      * apply NatLe_lift. lia.
      * apply NatLe_lift. lia.
      * exact Hpa.
    + intro Hsome. cbn [mixd_scan_up] in Hsome.
      destruct (IH (Datatypes.S i) acc (Qmult acc acc)
                   (Datatypes.S (Datatypes.S c)) j Hcert pacc' c'
                   (qeq_imp_qeqT _ _
                      (@Qmult_comp acc (mixd_ladder k0 i)
                         (qeqT_imp_qeq _ _ Hacc)
                         acc (mixd_ladder k0 i) (qeqT_imp_qeq _ _ Hacc)))
                   Hacc Hsome) as [Hb1 [Hb2 [Hb3 Hb4]]].
      repeat split.
      * pose proof (NatLe_drop (Datatypes.S i) j Hb1).
        apply NatLe_lift. lia.
      * pose proof (NatLe_drop j (Datatypes.S i + d) Hb2).
        apply NatLe_lift. lia.
      * pose proof (NatLe_drop c'
                      (Datatypes.S (Datatypes.S c) + 2 * d + 1) Hb3).
        apply NatLe_lift. lia.
      * exact Hb4.
Qed.

(* Fallback composition account: entry invariants (p == kappa_0^(2^j),
   val == kappa_0^k * v, everything below k fails) imply exit (everything
   below kf fails, S kf <= k + 2^(S j), cost bound). *)
Lemma mixd_desc_spec : forall (k0 v b0 : Q) (Hq0 : QltT 0 k0) (Hq1 : QleT' k0 1)
    (Hv : QleT' 0 v) (j : nat) (k : nat) (val : Q) (c : nat)
    (Hval : QeqT val (Qmult (igr_qpow k0 k) v))
    (Hfail : forall m : nat, NatLe m k -> QltT b0 (Qmult (igr_qpow k0 m) v))
    (kf c' : nat),
  mixd_desc k0 v b0 j k val c = (kf, c') ->
  And (forall m : nat, NatLe m kf -> QltT b0 (Qmult (igr_qpow k0 m) v))
      (And (NatLe (Datatypes.S kf) (k + mixd_two_pow (Datatypes.S j))%nat)
           (NatLe c' (c + 3 * j + 2)%nat)).
Proof.
  intros k0 v b0 Hq0 Hq1 Hv j. induction j as [| j IH];
    intros k val c Hval Hfail kf c' Hrun.
  - cbn [mixd_desc] in Hrun.
    revert Hrun.
    destruct (mixd_dec_le (Qmult val (mixd_ladder k0 0)) b0)
      as [Hpass | Hfailj].
    + intro Hrun. cbn [mixd_dec_le] in Hrun.
      injection Hrun as Hkf Hcc. subst kf c'. repeat split.
      * intros m Hm. exact (Hfail m Hm).
      * cbn [mixd_two_pow]. apply NatLe_lift. lia.
      * apply NatLe_lift. lia.
    + intro Hrun. cbn [mixd_dec_le] in Hrun.
      injection Hrun as Hkf Hcc. subst kf c'. repeat split.
      * intros m Hm.
        pose proof (NatLe_drop m (Datatypes.S k) Hm) as Hmq.
        destruct (Nat.eq_dec m (Datatypes.S k)) as [Hme | Hmne].
        -- subst m.
           apply (mixd_qlt_eq_r b0
                             (Qmult val (mixd_ladder k0 0))
                             (Qmult (igr_qpow k0 (Datatypes.S k)) v)).
           ++ exact (mixd_qeq_step0 k0 v k (mixd_ladder k0 0) val
                       (mixd_ladder_spec k0 0) Hval).
           ++ exact (mixd_qleF_lt _ _ Hfailj).
        -- assert (Hmk : (m <= k)%nat) by lia.
           exact (Hfail m (NatLe_lift m k Hmk)).
      * cbn [mixd_two_pow mixd_ladder]. apply NatLe_lift. lia.
      * apply NatLe_lift. lia.
  - cbn [mixd_desc] in Hrun.
    revert Hrun.
    destruct (mixd_dec_le (Qmult val (mixd_ladder k0 (Datatypes.S j))) b0)
      as [Hpass | Hfailj].
    + intro Hrun. cbn [mixd_dec_le] in Hrun.
      destruct (IH k val (Datatypes.S (Datatypes.S c))
                  Hval Hfail kf c' Hrun) as [Ha [Hb Hc]].
      repeat split.
      * exact Ha.
      * change (mixd_two_pow (Datatypes.S (Datatypes.S j)))
          with (2 * mixd_two_pow (Datatypes.S j))%nat.
        apply NatLe_lift.
        pose proof (NatLe_drop (Datatypes.S kf)
                      (k + mixd_two_pow (Datatypes.S j)) Hb).
        lia.
      * apply NatLe_lift.
        pose proof (NatLe_drop c'
                      (Datatypes.S (Datatypes.S c) + 3 * j + 2) Hc). lia.
    + intro Hrun. cbn [mixd_dec_le] in Hrun.
      assert (Hfail' : forall m : nat,
                 NatLe m (k + mixd_two_pow (Datatypes.S j))%nat ->
                 QltT b0 (Qmult (igr_qpow k0 m) v)).
      { intros m Hm.
        destruct (mixd_dec_leb m k) as [Hmk | Hmkf].
        - exact (Hfail m Hmk).
        - apply (mixd_fail_down k0 v b0 Hq0 Hq1 Hv m
                    (k + mixd_two_pow (Datatypes.S j))).
          + exact Hm.
          + apply (mixd_qlt_eq_r b0
                     (Qmult val (mixd_ladder k0 (Datatypes.S j)))
                     (Qmult (igr_qpow k0 (k + mixd_two_pow (Datatypes.S j)))
                        v)).
            * exact (mixd_qeq_step k0 v j k
                       (mixd_ladder k0 (Datatypes.S j)) val
                       (mixd_ladder_spec k0 (Datatypes.S j)) Hval).
            * exact (mixd_qleF_lt _ _ Hfailj). }
      destruct (IH (k + mixd_two_pow (Datatypes.S j))%nat
                  (Qmult val (mixd_ladder k0 (Datatypes.S j)))
                  (Datatypes.S (Datatypes.S (Datatypes.S c)))
                  (mixd_qeq_step k0 v j k (mixd_ladder k0 (Datatypes.S j)) val
                     (mixd_ladder_spec k0 (Datatypes.S j)) Hval)
                  Hfail' kf c' Hrun) as [Ha [Hb Hc]].
      repeat split.
      * exact Ha.
      * change (mixd_two_pow (Datatypes.S (Datatypes.S j)))
          with (2 * mixd_two_pow (Datatypes.S j))%nat.
        apply NatLe_lift.
        pose proof (NatLe_drop (Datatypes.S kf)
                      (k + mixd_two_pow (Datatypes.S j) + mixd_two_pow (Datatypes.S j)) Hb).
        lia.
      * apply NatLe_lift.
        pose proof (NatLe_drop c'
                      (Datatypes.S (Datatypes.S (Datatypes.S c)) + 3 * j + 2) Hc). lia.
Qed.

(* Top-level sound account: Some (inl (k, cert), c) implies everything below k
   fails and c <= 5*d + 2. *)
Lemma mixd_k_select_log_cert_spec : forall (k0 v b0 : Q) (h0 : QltT 0 k0)
    (h1 : QleT' k0 1) (hv : QleT' 0 v) (d k c : nat)
    (Hcert : mixd_ans_cert k0 v b0 k),
  mixd_k_select_log_cert k0 v b0 h0 h1 hv d
    = Some (inl (existT _ k Hcert), c) ->
  And (forall j : nat, NatLe (Datatypes.S j) k ->
         QltT b0 (Qmult (igr_qpow k0 j) v))
      (NatLe c (5 * d + 2)%nat).
Proof.
  intros k0 v b0 h0 h1 hv d k c Hcert Hrun.
  unfold mixd_k_select_log_cert in Hrun.
  remember (mixd_dec_le v b0) as d0 eqn:Ed0.
  cbn [mixd_k_select_log_cert] in Hrun.
  destruct d0 as [Hp0 | Hf0].
  - assert (Hb : 1%nat = c) by exact (mixd_some_inj_snd _ _ _ _ _ Hrun).
    assert (Hk0 : 0%nat = k).
    { exact (f_equal (@projT1 nat (fun k1 : nat => mixd_ans_cert k0 v b0 k1))
               (mixd_some_inl_fst _ _ _ _ _ _ Hrun)). }
    subst k. subst c. split.
    + intros j Hj.
      pose proof (NatLe_drop (Datatypes.S j) 0%nat Hj).
      exfalso. lia.
    + apply NatLe_lift. lia.
  - cbn [mixd_k_select_log_cert] in Hrun.
    revert Hrun.
    destruct (mixd_scan_up k0 v b0 d 0%nat k0 k0 0%nat
              (qeq_imp_qeqT k0 k0 (Qeq_refl k0)))
      eqn:Hscan.
    + destruct p as [sq c1].
      destruct sq as [s0 pacc].
      destruct s0 as [jj Htop].
      intro Hrun. cbn [mixd_k_select_log_cert] in Hrun.
      destruct jj as [| j].
      * cbn [fst snd] in *.
        remember (mixd_dec_le (Qmult (igr_qpow k0 1) v) b0) as d1 eqn:Ed1.
        cbn [mixd_k_select_log_cert] in Hrun.
        destruct d1 as [Hp1 | Hf1].
        -- assert (Hb : (c1 + 0)%nat = c)
             by exact (mixd_some_inj_snd _ _ _ _ _ Hrun).
           assert (Hk1 : Datatypes.S 0%nat = k)
             by exact (f_equal
                        (@projT1 nat (fun k1 : nat => mixd_ans_cert k0 v b0 k1))
                        (mixd_some_inl_fst _ _ _ _ _ _ Hrun)).
           subst c. split.
           ++ intros m Hm.
              pose proof (NatLe_drop (Datatypes.S m) k Hm) as Hmq.
              assert (Hm0 : m = 0%nat) by lia. subst m.
              apply (mixd_qlt_eq_r b0 v (Qmult (igr_qpow k0 0%nat) v)).
              --- apply qeq_imp_qeqT. cbn [igr_qpow]. symmetry. apply Qmult_1_l.
              --- exact (mixd_qleF_lt _ _ Hf0).
           ++ assert (Hs : mixd_scan_up k0 v b0 d 0%nat k0 k0 0%nat
                               (qeq_imp_qeqT k0 k0 (Qeq_refl k0))
                               = Some (existT _ 0%nat Htop, pacc, c1))
                by exact Hscan.
              destruct (mixd_scan_up_some k0 v b0 d 0%nat k0 k0 0%nat
                          0%nat Htop pacc c1
                          (qeq_imp_qeqT k0 k0 (Qeq_refl k0))
                          (qeq_imp_qeqT k0 k0 (Qeq_refl k0)) Hs)
                as [_ [_ [Hc1 _]]].
              apply NatLe_lift.
              pose proof (NatLe_drop c1 (0%nat + 2 * d + 1) Hc1).
              lia.
        -- discriminate Hrun.
      * assert (Hs : mixd_scan_up k0 v b0 d 0%nat k0 k0 0%nat
                         (qeq_imp_qeqT k0 k0 (Qeq_refl k0))
                         = Some (existT _ (Datatypes.S j) Htop, pacc, c1))
          by exact Hscan.
        destruct (mixd_scan_up_some k0 v b0 d 0%nat k0 k0 0%nat
                    (Datatypes.S j) Htop pacc c1
                    (qeq_imp_qeqT k0 k0 (Qeq_refl k0))
                    (qeq_imp_qeqT k0 k0 (Qeq_refl k0))
                    Hs) as [_ [Hjle [Hc1 Hpacc]]].
        assert (Hval0 : QeqT v (Qmult (igr_qpow k0 0%nat) v)).
        { apply qeq_imp_qeqT. cbn [igr_qpow]. symmetry. apply Qmult_1_l. }
        assert (Hfail0 : forall m : nat, NatLe m 0%nat ->
                   QltT b0 (Qmult (igr_qpow k0 m) v)).
        { intros m Hm.
          pose proof (NatLe_drop m 0%nat Hm) as Hmq.
          assert (Hm0 : m = 0%nat) by lia. subst m.
          apply (mixd_qlt_eq_r b0 v (Qmult (igr_qpow k0 0%nat) v)).
          - apply qeq_imp_qeqT. cbn [igr_qpow]. symmetry. apply Qmult_1_l.
          - exact (mixd_qleF_lt _ _ Hf0). }
        revert Hrun.
        destruct (mixd_desc k0 v b0 j 0%nat v 0%nat) as [kf c2] eqn:Hdesc.
        cbn [fst snd].
        destruct (mixd_desc_spec k0 v b0 h0 h1 hv j 0%nat v 0%nat
                    Hval0 Hfail0 kf c2 Hdesc) as [HfailK [Hbnd Hcost]].
        remember (mixd_dec_le (Qmult (igr_qpow k0 (Datatypes.S kf)) v) b0)
          as d2 eqn:Ed2.
        intro Hrun. cbn [mixd_k_select_log_cert] in Hrun.
        destruct d2 as [Hpass | HfailS].
        -- assert (Hb : (c1 + c2)%nat = c)
             by exact (mixd_some_inj_snd _ _ _ _ _ Hrun).
           assert (Hk : Datatypes.S kf = k)
             by exact (f_equal
                        (@projT1 nat (fun k1 : nat => mixd_ans_cert k0 v b0 k1))
                        (mixd_some_inl_fst _ _ _ _ _ _ Hrun)).
           subst c. split.
           ++ intros m Hm.
              pose proof (NatLe_drop (Datatypes.S m) k Hm) as Hmq.
              assert (Hmk : (m <= kf)%nat) by lia.
              exact (HfailK m (NatLe_lift m kf Hmk)).
           ++ apply NatLe_lift.
              pose proof (NatLe_drop (Datatypes.S j) (0%nat + d) Hjle).
              pose proof (NatLe_drop c1 (0%nat + 2 * d + 1) Hc1).
              pose proof (NatLe_drop c2 (0%nat + 3 * j + 2) Hcost).
              lia.
        -- discriminate Hrun.
    + intro Hrun. discriminate Hrun.
Qed.

(* Magnitude theorem, machine-checkable nat-bound form: multiplication count
   <= 5*d + 2 where d is the ladder depth (rung count about log2 K). *)
Theorem mixd_k_select_log_mulcost : forall (k0 v b0 : Q) (h0 : QltT 0 k0)
    (h1 : QleT' k0 1) (hv : QleT' 0 v) (d k c : nat)
    (Hcert : mixd_ans_cert k0 v b0 k),
  mixd_k_select_log_cert k0 v b0 h0 h1 hv d
    = Some (inl (existT _ k Hcert), c) ->
  NatLe c (5 * d + 2)%nat.
Proof.
  intros k0 v b0 h0 h1 hv d k c Hcert Hrun.
  destruct (mixd_k_select_log_cert_spec k0 v b0 h0 h1 hv d k c Hcert Hrun)
    as [_ Hcost].
  exact Hcost.
Qed.

(* Top-level fallback account (semantically dead branch): Some (inr (k, cert), c)
   implies the answer certificate (the top rung passes through) and c <= 5*d + 2. *)
Lemma mixd_k_select_log_cert_fb : forall (k0 v b0 : Q) (h0 : QltT 0 k0)
    (h1 : QleT' k0 1) (hv : QleT' 0 v) (d k c : nat)
    (Hcert : mixd_ans_cert k0 v b0 k),
  mixd_k_select_log_cert k0 v b0 h0 h1 hv d
    = Some (inr (existT _ k Hcert), c) ->
  NatLe c (5 * d + 2)%nat.
Proof.
  intros k0 v b0 h0 h1 hv d k c Hcert Hrun.
  unfold mixd_k_select_log_cert in Hrun.
  remember (mixd_dec_le v b0) as d0 eqn:Ed0.
  cbn [mixd_k_select_log_cert] in Hrun.
  destruct d0 as [Hp0 | Hf0].
  - discriminate Hrun.
  - cbn [mixd_k_select_log_cert] in Hrun.
    revert Hrun.
    destruct (mixd_scan_up k0 v b0 d 0%nat k0 k0 0%nat
              (qeq_imp_qeqT k0 k0 (Qeq_refl k0)))
      eqn:Hscan.
    + destruct p as [sq c1].
      destruct sq as [s0 pacc].
      destruct s0 as [jj Htop].
      intro Hrun. cbn [mixd_k_select_log_cert] in Hrun.
      destruct jj as [| j].
      * cbn [fst snd] in *.
        remember (mixd_dec_le (Qmult (igr_qpow k0 1) v) b0) as d1 eqn:Ed1.
        cbn [mixd_k_select_log_cert] in Hrun.
        destruct d1 as [Hp1 | Hf1].
        -- discriminate Hrun.
        -- (* jj = 0 branch, kfc = (0,0): snd kfc = 0. *)
           assert (Hs : mixd_scan_up k0 v b0 d 0%nat k0 k0 0%nat
                           (qeq_imp_qeqT k0 k0 (Qeq_refl k0))
                           = Some (existT _ 0%nat Htop, pacc, c1))
             by exact Hscan.
           destruct (mixd_scan_up_some k0 v b0 d 0%nat k0 k0 0%nat
                       0%nat Htop pacc c1
                       (qeq_imp_qeqT k0 k0 (Qeq_refl k0))
                       (qeq_imp_qeqT k0 k0 (Qeq_refl k0)) Hs)
             as [_ [_ [Hc1 _]]].
           assert (Hb : (c1 + 0)%nat = c)
             by exact (mixd_some_inj_snd _ _ _ _ _ Hrun).
           subst c. apply NatLe_lift.
           pose proof (NatLe_drop c1 (0%nat + 2 * d + 1) Hc1).
           lia.
      * assert (Hs : mixd_scan_up k0 v b0 d 0%nat k0 k0 0%nat
                         (qeq_imp_qeqT k0 k0 (Qeq_refl k0))
                         = Some (existT _ (Datatypes.S j) Htop, pacc, c1))
          by exact Hscan.
        destruct (mixd_scan_up_some k0 v b0 d 0%nat k0 k0 0%nat
                    (Datatypes.S j) Htop pacc c1
                    (qeq_imp_qeqT k0 k0 (Qeq_refl k0))
                    (qeq_imp_qeqT k0 k0 (Qeq_refl k0))
                    Hs) as [_ [Hjle [Hc1 Hpacc]]].
        pose proof (NatLe_drop (Datatypes.S j) (0%nat + d) Hjle) as Hjleq.
        revert Hrun.
        destruct (mixd_desc k0 v b0 j 0%nat v 0%nat) as [kf c2] eqn:Hdesc.
        cbn [fst snd].
        remember (mixd_dec_le (Qmult (igr_qpow k0 (Datatypes.S kf)) v) b0)
          as d2 eqn:Ed2.
        intro Hrun. cbn [mixd_k_select_log_cert] in Hrun.
        destruct d2 as [Hpass | HfailS].
        -- discriminate Hrun.
        -- assert (Hb : (c1 + c2)%nat = c)
             by exact (mixd_some_inj_snd _ _ _ _ _ Hrun).
           subst c.
           assert (Hval0 : QeqT v (Qmult (igr_qpow k0 0%nat) v)).
           { apply qeq_imp_qeqT. cbn [igr_qpow]. symmetry. apply Qmult_1_l. }
           assert (Hfail0 : forall m : nat, NatLe m 0%nat ->
                      QltT b0 (Qmult (igr_qpow k0 m) v)).
           { intros m Hm.
             pose proof (NatLe_drop m 0%nat Hm) as Hmq.
             assert (Hm0 : m = 0%nat) by lia. subst m.
             apply (mixd_qlt_eq_r b0 v (Qmult (igr_qpow k0 0%nat) v)).
             - apply qeq_imp_qeqT. cbn [igr_qpow]. symmetry. apply Qmult_1_l.
             - exact (mixd_qleF_lt _ _ Hf0). }
           destruct (mixd_desc_spec k0 v b0 h0 h1 hv j 0%nat v 0%nat
                       Hval0 Hfail0 kf c2 Hdesc) as [_ [_ Hcost2]].
           apply NatLe_lift.
           pose proof (NatLe_drop c1 (0%nat + 2 * d + 1) Hc1).
           pose proof (NatLe_drop c2 (0%nat + 3 * j + 2) Hcost2).
           lia.
    + intro Hrun. discriminate Hrun.
Qed.

(* No-solution account: None implies every k <= 2^d fails (the window tightness
   is reported honestly). *)
Lemma mixd_k_select_log_cert_none : forall (k0 v b0 : Q) (h0 : QltT 0 k0)
    (h1 : QleT' k0 1) (hv : QleT' 0 v) (d : nat),
  mixd_k_select_log_cert k0 v b0 h0 h1 hv d = None ->
  forall j : nat, NatLe j (mixd_two_pow d)%nat ->
  QltT b0 (Qmult (igr_qpow k0 j) v).
Proof.
  intros k0 v b0 h0 h1 hv d Hnone j Hj.
  unfold mixd_k_select_log_cert in Hnone.
  remember (mixd_dec_le v b0) as d0 eqn:Ed0.
  cbn [mixd_k_select_log_cert] in Hnone.
  destruct d0 as [Hp0 | Hf0].
  - discriminate Hnone.
  - revert Hnone.
    destruct (mixd_scan_up k0 v b0 d 0%nat k0 k0 0%nat
              (qeq_imp_qeqT k0 k0 (Qeq_refl k0)))
      eqn:Hscan.
    + destruct p as [sq c1].
      destruct sq as [s0 pacc].
      destruct s0 as [jj Htop].
      destruct jj as [| j0].
      * cbn [fst snd].
        destruct (mixd_dec_le (Qmult (igr_qpow k0 1) v) b0)
          as [Hp1 | Hf1].
        -- intro Hnone. discriminate Hnone.
        -- intro Hnone. discriminate Hnone.
      * cbn [fst snd].
        destruct (mixd_dec_le (Qmult (igr_qpow k0
                          (Datatypes.S (fst (mixd_desc k0 v b0 j0 0%nat v
                             0%nat)))) v) b0) as [Hp2 | Hf2].
        -- intro Hnone. discriminate Hnone.
        -- intro Hnone. discriminate Hnone.
    + intro Hnone. cbn [mixd_k_select_log_cert] in Hnone.
      apply (mixd_fail_down k0 v b0 h0 h1 hv j (mixd_two_pow d) Hj).
      apply (mixd_scan_up_none k0 v b0 d 0%nat k0 k0 0%nat
               (qeq_imp_qeqT k0 k0 (Qeq_refl k0))).
      * exact Hscan.
      * apply NatLe_lift. lia.
      * apply NatLe_lift. lia.
Qed.

(* Part 7: Real shell (Q-to-Real reflection + kappa_0/b_0 extraction + power
   bridge + return chain). *)

(* real_const pointwise projection. *)
Lemma mixd_const_proj : forall (v : Q) (n : nat), QeqT (projT1 (real_const v) n) v.
Proof.
  intros v n. exact (qeq_imp_qeqT _ _ (Qeq_refl v)).
Qed.

Lemma mixd_zero_proj : forall n : nat, QeqT (projT1 real_zero n) 0.
Proof.
  intro n. exact (qeq_imp_qeqT _ _ (Qeq_refl 0)).
Qed.

Lemma mixd_one_proj : forall n : nat, QeqT (projT1 real_one n) 1.
Proof.
  intro n. exact (qeq_imp_qeqT _ _ (Qeq_refl 1)).
Qed.

(* real_lt to real_le (Or left-branch direct; real_le := Or real_lt real_eq). *)
Definition mixd_lt_to_le : forall x y : Real, real_lt x y -> real_le x y :=
  fun x y H => @inl (real_lt x y) (real_eq x y) H.

(* Q-to-Real reflection: real_lt real_zero (real_const v) implies QleT' 0 v. *)
Lemma mixd_const_le_reflect : forall v : Q,
  real_lt real_zero (real_const v) -> QleT' 0 v.
Proof.
  intros v H. destruct H as [eps [Heps [N HN]]].
  apply Qle_to_QleT'.
  apply (Qle_trans 0 eps v).
  + exact (Qlt_le_weak 0 eps (QltT_to_Qlt 0 eps Heps)).
  + assert (HNv : QltT eps (projT1 (real_const v) N - projT1 real_zero N)).
    { apply HN. apply NatLe_lift. apply Nat.le_refl. }
    apply (Qle_trans eps
             (projT1 (real_const v) N - projT1 real_zero N) v).
    * apply (Qlt_le_weak eps). exact (QltT_to_Qlt _ _ HNv).
    * assert (Heq' : QeqT v (projT1 (real_const v) N - projT1 real_zero N)).
      { apply qeq_imp_qeqT.
        change (projT1 (real_const v) N) with v.
        change (projT1 real_zero N) with 0.
        ring. }
      exact (QleT'_to_Qle _ _
               (mixd_qle_eq_l v
                  (projT1 (real_const v) N - projT1 real_zero N) v
                  Heq' (Qle_to_QleT' _ _ (Qle_refl v)))).
Qed.

(* real_const positivity. *)
Lemma mixd_const_pos : forall k0 : Q, QltT 0 k0 ->
  real_lt real_zero (real_const k0).
Proof.
  intros k0 H.
  exact (real_eq_lt_lt real_zero (real_const (0#1)) (real_const k0)
           (real_eq_sym _ _ mix_const_zero)
           (real_const_lt 0 k0 H)).
Defined.

(* const multiplication projection: real_const (a*b) == real_const a * real_const b. *)
Lemma mixd_const_mult : forall a b : Q,
  real_eq (real_const (Qmult a b)) (real_mult (real_const a) (real_const b)).
Proof.
  intros a b. apply real_eq_of_zero_diff. intro n.
  apply qeq_imp_qeqT.
  cbn [projT1 real_const real_mult].
  ring.
Qed.

(* Real power - Q power bridge: tv_rpow (real_const q) m == real_const (igr_qpow q m). *)
Lemma mixd_rpow_const : forall (q : Q) (m : nat),
  real_eq (tv_rpow (real_const q) m) (real_const (igr_qpow q m)).
Proof.
  intros q m. induction m as [| m IH].
  - apply real_eq_of_zero_diff. intro n.
    apply qeq_imp_qeqT.
    cbn [projT1 real_one real_const tv_rpow igr_qpow].
    ring.
  - cbn [tv_rpow igr_qpow].
    apply (real_eq_trans _
             (real_mult (real_const q) (real_const (igr_qpow q m)))).
    + exact (RealSetoid.real_eq_mult_compat (real_const q)
               (tv_rpow (real_const q) m)
               (real_const q) (real_const (igr_qpow q m))
               (real_eq_refl (real_const q)) IH).
    + exact (mixd_const_mult q (igr_qpow q m)).
Qed.

(* Return-chain assembly shape: the kappa_0'^k * v product projects back to Q. *)
Lemma mixd_rpow_const_eq : forall (q v : Q) (k : nat),
  real_eq (real_mult (tv_rpow (real_const q) k) (real_const v))
          (real_const (Qmult (igr_qpow q k) v)).
Proof.
  intros q v k.
  apply (real_eq_trans
           (real_mult (tv_rpow (real_const q) k) (real_const v))
           (real_mult (real_const (igr_qpow q k)) (real_const v))
           (real_const (Qmult (igr_qpow q k) v))).
  - apply (RealSetoid.real_eq_mult_compat (tv_rpow (real_const q) k)
             (real_const v) (real_const (igr_qpow q k)) (real_const v)
             (mixd_rpow_const q k) (real_eq_refl (real_const v))).
  - apply (real_eq_sym _ _ (mixd_const_mult (igr_qpow q k) v)).
Qed.

(* Base monotonicity: 0 < kappa and kappa <= kappa_0' imply kappa^m <= kappa_0'^m. *)
Lemma mixd_pow_base_mono : forall (kappa : Real) (k0 : Q) (m : nat)
    (Hk1 : real_lt real_zero kappa) (Hk0p : QltT 0 k0)
    (Hle : real_le kappa (real_const k0)),
  real_le (tv_rpow kappa m) (tv_rpow (real_const k0) m).
Proof.
  intros kappa k0 m Hk1 Hk0p Hle. induction m as [| m IH].
  - exact (klc_le_refl (tv_rpow kappa 0)).
  - apply (real_le_trans
             (real_mult kappa (tv_rpow kappa m))
             (real_mult (real_const k0) (tv_rpow kappa m))
             (real_mult (real_const k0) (tv_rpow (real_const k0) m))).
    + exact (real_le_mult_compat kappa (real_const k0) (tv_rpow kappa m)
               (mix_rpow_pos kappa m Hk1) Hle).
    + exact (real_le_mult_compat_r (real_const k0)
                 (tv_rpow kappa m) (tv_rpow (real_const k0) m)
                 (mixd_lt_to_le real_zero (real_const k0)
                    (mixd_const_pos k0 Hk0p))
                 IH).
Qed.

(* kappa_0 gap item (branch-free: the Qmax double lower bound takes the
   1 - eps/2 lower bound alone). *)
Lemma mixd_kappa0_gap : forall (e x k0 : Q),
  QltT 0 e -> QeqT k0 (mixd_qmax (1 - e * (1#2)) (1#2)) ->
  QltT e (1 - x) -> QltT (e * (1#2)) (k0 - x).
Proof.
  intros e x k0 He Hk0 Hlt.
  pose proof (QltT_to_Qlt 0 e He) as Heq.
  assert (HQ : QltT (x + e) 1).
  { apply (mixd_qlt_eq_r (x + e) (x + (1 - x)) 1).
    - apply qeq_imp_qeqT. ring.
    - apply Qlt_to_QltT.
      exact (proj2 (Qplus_lt_r e (1 - x) x) (QltT_to_Qlt _ _ Hlt)). }
  assert (Ha : QltT (e * (1#2) + x) (1 - e * (1#2))).
  { apply Qlt_to_QltT.
    apply (proj1 (Qplus_lt_r (e * (1#2) + x) (1 - e * (1#2)) (e * (1#2)))).
    assert (Heq1 : QeqT 1 (e * (1#2) + (1 - e * (1#2)))).
    { apply qeq_imp_qeqT. ring. }
    assert (Hsub : QltT (e * (1#2) + (e * (1#2) + x)) 1).
    { apply (mixd_qlt_eq_l (x + e)
               (e * (1#2) + (e * (1#2) + x)) 1).
      - apply qeq_imp_qeqT. ring.
      - exact HQ. }
    exact (QltT_to_Qlt _ _
             (mixd_qlt_eq_r (e * (1#2) + (e * (1#2) + x)) 1
                (e * (1#2) + (1 - e * (1#2))) Heq1 Hsub)). }
  assert (Hlb : QleT' (1 - e * (1#2)) k0).
  { apply (mixd_qle_eq_r (1 - e * (1#2))
               (mixd_qmax (1 - e * (1#2)) (1#2)) k0).
    - apply qeq_imp_qeqT. exact (Qeq_sym _ _ (qeqT_imp_qeq _ _ Hk0)).
    - destruct (mixd_dec_le (1 - e * (1#2)) (1#2)) as [Eb | Eb].
      + apply (mixd_qle_eq_r (1 - e * (1#2)) (1#2)
                 (mixd_qmax (1 - e * (1#2)) (1#2))).
        ** exact (mixd_qeqT_sym _ _ (mixd_qmax_eq_r _ _ Eb)).
        ** exact Eb.
      + apply (mixd_qle_eq_r (1 - e * (1#2)) (1 - e * (1#2))
                 (mixd_qmax (1 - e * (1#2)) (1#2))).
        ** exact (mixd_qeqT_sym _ _ (mixd_qmax_eq_l _ _ Eb)).
        ** apply Qle_to_QleT'. apply Qle_refl. }
  apply Qlt_to_QltT.
  apply (proj1 (Qplus_lt_r (e * (1#2)) (k0 - x) x)).
  assert (HeqA : QeqT (e * (1#2) + x) (x + e * (1#2))).
  { apply qeq_imp_qeqT. ring. }
  assert (Hmid : QltT (e * (1#2) + x) (x + (k0 - x))).
  { apply (mixd_qlt_eq_r (e * (1#2) + x) k0 (x + (k0 - x))).
    - apply qeq_imp_qeqT. ring.
    - apply Qlt_to_QltT.
      exact (Qlt_le_trans (e * (1#2) + x) (1 - e * (1#2)) k0
                (QltT_to_Qlt _ _ Ha) (QleT'_to_Qle _ _ Hlb)). }
  exact (QltT_to_Qlt _ _
           (mixd_qlt_eq_l (e * (1#2) + x) (x + e * (1#2)) (x + (k0 - x))
              HeqA Hmid)).
Qed.

(* kappa_0 extraction: real_lt kappa 1 gives kappa_0 := Qmax(1-eps/2)(1/2) in Q,
   carrying 0 < kappa_0 < 1 (QltT) and kappa < kappa_0 (real_lt -- the return
   chain's load-bearing slot). *)
Lemma mixd_kappa0_cert : forall kappa : Real, real_lt kappa real_one ->
  sigT (fun k0 : Q =>
    And (QltT 0 k0) (And (QltT k0 1) (real_lt kappa (real_const k0)))).
Proof.
  intros kappa H. destruct H as [eps [Heps [N HN]]].
  exists (mixd_qmax (1 - eps * (1#2)) (1#2)).
  pose proof (QltT_to_Qlt 0 eps Heps) as Hepos.
  assert (Hlt0 : QltT 0 (mixd_qmax (1 - eps * (1#2)) (1#2))).
  { destruct (mixd_dec_le (1 - eps * (1#2)) (1#2)) as [Eb | Eb].
    - apply (mixd_qlt_eq_r 0 (1#2) (mixd_qmax (1 - eps * (1#2)) (1#2))).
      + exact (mixd_qeqT_sym _ _ (mixd_qmax_eq_r _ _ Eb)).
      + exact mixd_half_pos.
    - apply (mixd_qlt_eq_r 0 (1 - eps * (1#2))
               (mixd_qmax (1 - eps * (1#2)) (1#2))).
      + exact (mixd_qeqT_sym _ _ (mixd_qmax_eq_l _ _ Eb)).
      + apply Qlt_to_QltT.
        apply (Qlt_trans 0 (1#2) (1 - eps * (1#2))).
        * exact (QltT_to_Qlt _ _ mixd_half_pos).
        * exact (QltT_to_Qlt _ _
                   (mixd_qle_bool_false_lt (1 - eps * (1#2)) (1#2) Eb)). }
  assert (Hlt1 : QltT (mixd_qmax (1 - eps * (1#2)) (1#2)) 1).
  { destruct (mixd_dec_le (1 - eps * (1#2)) (1#2)) as [Eb | Eb].
    - apply (mixd_qlt_eq_l (1#2) (mixd_qmax (1 - eps * (1#2)) (1#2)) 1
               (mixd_qeqT_sym _ _ (mixd_qmax_eq_r _ _ Eb))).
      exact mixd_half_lt_one.
    - apply (mixd_qlt_eq_l (1 - eps * (1#2))
               (mixd_qmax (1 - eps * (1#2)) (1#2)) 1
               (mixd_qeqT_sym _ _ (mixd_qmax_eq_l _ _ Eb))).
      apply Qlt_to_QltT.
      apply (proj1 (Qplus_lt_r (1 - eps * (1#2)) 1 (eps * (1#2)))).
      assert (Heq2 : QeqT 1 (eps * (1#2) + (1 - eps * (1#2)))).
      { apply qeq_imp_qeqT. ring. }
      assert (Hmid2 : QltT 1 (eps * (1#2) + 1)).
      { apply (mixd_qlt_eq_r 1 (1 + eps * (1#2)) (eps * (1#2) + 1)).
        - apply qeq_imp_qeqT. ring.
        - exact (mixd_qlt_add_pos 1 (eps * (1#2))
                   (mixd_qlt_eq_l (0 * (1#2)) 0 (eps * (1#2))
                      (qeq_imp_qeqT _ _ (Qmult_0_l (1#2)))
                      (Qlt_to_QltT _ _
                         (Qmult_lt_compat_r 0 eps (1#2)
                            (QltT_to_Qlt _ _ mixd_half_pos) Hepos)))). }
      exact (QltT_to_Qlt _ _
               (mixd_qlt_eq_l 1 (eps * (1#2) + (1 - eps * (1#2)))
                  (eps * (1#2) + 1) Heq2 Hmid2)). }
  split.
  - exact Hlt0.
  - split.
    + exact Hlt1.
    + exists (eps * (1#2)). split.
      * exact (mixd_qlt_eq_l (0 * (1#2)) 0 (eps * (1#2))
                 (qeq_imp_qeqT _ _ (Qmult_0_l (1#2)))
                 (Qlt_to_QltT _ _
                    (Qmult_lt_compat_r 0 eps (1#2)
                       (QltT_to_Qlt _ _ mixd_half_pos) Hepos))).
      * exists N. intros n Hn.
        assert (Hprem : QltT eps (1 - projT1 kappa n)).
        { apply (mixd_qlt_eq_r eps (projT1 real_one n - projT1 kappa n)
                   (1 - projT1 kappa n)).
          - apply qeq_imp_qeqT. change (projT1 real_one n) with 1. ring.
          - exact (HN n Hn). }
        apply Qlt_to_QltT.
        rewrite (qeqT_imp_qeq _ _
                   (mixd_const_proj (mixd_qmax (1 - eps * (1#2)) (1#2)) n)).
        exact (QltT_to_Qlt _ _
                 (mixd_kappa0_gap eps (projT1 kappa n)
                    (mixd_qmax (1 - eps * (1#2)) (1#2)) Heps
                    (qeq_imp_qeqT _ _ (Qeq_refl _)) Hprem)).
Defined.

(* b_0 extraction: real_lt 0 budget gives b_0 := eps_b/2 in Q carrying 0 < b_0
   and real_const b_0 < budget (the strict tail of the return chain). *)
Lemma mixd_b0_cert : forall budget : Real, real_lt real_zero budget ->
  sigT (fun b0 : Q => And (QltT 0 b0) (real_lt (real_const b0) budget)).
Proof.
  intros budget H. destruct H as [epsb [Heps [N HN]]].
  exists (epsb * (1#2)).
  pose proof (QltT_to_Qlt 0 epsb Heps) as Hepos.
  assert (HB0 : QltT 0 (epsb * (1#2))).
  { exact (mixd_qlt_eq_l (0 * (1#2)) 0 (epsb * (1#2))
             (qeq_imp_qeqT _ _ (Qmult_0_l (1#2)))
             (Qlt_to_QltT _ _
                (Qmult_lt_compat_r 0 epsb (1#2)
                   (QltT_to_Qlt _ _ mixd_half_pos) Hepos))). }
  split.
  - exact HB0.
  - exists (epsb * (1#2)). split.
    + exact HB0.
    + exists N. intros n Hn.
      change (projT1 (real_const (epsb * (1#2))) n)
        with (epsb * (1#2)).
      apply (mixd_qsub_lt2 (epsb * (1#2)) (projT1 budget n)).
      * apply (mixd_qlt_eq_l epsb (epsb * (1#2) + epsb * (1#2))
                 (projT1 budget n)).
        -- apply qeq_imp_qeqT. ring.
        -- apply (mixd_qlt_eq_r epsb
                      (projT1 budget n - projT1 real_zero n)
                      (projT1 budget n)).
           ++ apply qeq_imp_qeqT.
              change (projT1 real_zero n) with 0. ring.
           ++ exact (HN n Hn).
Defined.

(* Return chain: the Q certificate <= gives the Real strict < (kappa^k * TV_0
   <= kappa_0'^k * TV_0 <= kappa_0'^k * v == kappa_0^k * v <= b_0 < budget). *)
Lemma mixd_real_chain : forall (kappa TV0 budget : Real) (k0 v b0 : Q)
    (k : nat) (Hk1 : real_lt real_zero kappa) (Hk0p : QltT 0 k0)
    (Hkle : real_le kappa (real_const k0))
    (Halt : real_lt real_zero TV0)
    (Htle : real_le TV0 (real_const v))
    (Hb0 : real_lt (real_const b0) budget)
    (Hcert : mixd_ans_cert k0 v b0 k),
  real_lt (real_mult (tv_rpow kappa k) TV0) budget.
Proof.
  intros kappa TV0 budget k0 v b0 k Hk1 Hk0p Hkle Halt Htle Hb0 Hcert.
  apply (real_le_lt_trans (real_mult (tv_rpow kappa k) TV0)
           (real_const b0) budget).
  - apply (real_le_trans
             (real_mult (tv_rpow kappa k) TV0)
             (real_mult (tv_rpow (real_const k0) k) TV0)
             (real_const b0)).
    + exact (real_le_mult_compat (tv_rpow kappa k)
               (tv_rpow (real_const k0) k) TV0
               Halt (mixd_pow_base_mono kappa k0 k Hk1 Hk0p Hkle)).
    + apply (real_le_trans
               (real_mult (tv_rpow (real_const k0) k) TV0)
               (real_mult (tv_rpow (real_const k0) k) (real_const v))
               (real_const b0)).
      * exact (real_le_mult_compat_r (tv_rpow (real_const k0) k)
                   TV0 (real_const v)
                   (mixd_lt_to_le real_zero
                      (tv_rpow (real_const k0) k)
                      (mix_rpow_pos (real_const k0) k
                         (mixd_const_pos k0 Hk0p)))
                   Htle).
      * apply (real_le_trans
                 (real_mult (tv_rpow (real_const k0) k) (real_const v))
                 (real_const (Qmult (igr_qpow k0 k) v))
                 (real_const b0)).
        -- exact (lt_le_iff _ _
                     (@inr (real_lt (real_mult
                             (tv_rpow (real_const k0) k) (real_const v))
                             (real_const (Qmult (igr_qpow k0 k) v)))
                             (real_eq (real_mult
                             (tv_rpow (real_const k0) k) (real_const v))
                             (real_const (Qmult (igr_qpow k0 k) v)))
                             (mixd_rpow_const_eq k0 v k))).
        -- exact (klc_const_le (Qmult (igr_qpow k0 k) v) b0 Hcert).
  - exact Hb0.
Defined.

(* Part 8: the main Defined piece and the le-face corollary. *)

(* Positive-TV_0 branch pipeline (the TV_0 == 0 branch goes through the
   existing mix_k_select item). *)
Definition mixd_k_select_log_pos (kappa TV0 budget : Real)
    (Hk1 : real_lt real_zero kappa) (Hk2 : real_lt kappa real_one)
    (Halt : real_lt real_zero TV0) (Hbudget : real_lt real_zero budget)
    (Htv : sigT (fun v : Q => real_le TV0 (real_const v)))
    (Hwin : forall (v k0 b0 : Q),
              sigT (fun N : nat =>
                QleT' v (Qmult (Qmake (Z.of_nat N) 1)
                                 (Qmult (1 - k0) b0))))
  : sigT (fun k : nat => real_lt (real_mult (tv_rpow kappa k) TV0) budget) :=
  match Htv with
  | existT _ v Htle =>
      match mixd_kappa0_cert kappa Hk2 with
      | existT _ k0 hpay =>
          match hpay with
          | (h0, (h0lt1, Hk0lt)) =>
              match mixd_b0_cert budget Hbudget with
              | existT _ b0 bpay =>
                  match bpay with
                  | (hb0p, Hb0lt) =>
                      match Hwin v k0 b0 with
                      | existT _ N Hw =>
                          let hv :=
                            mixd_const_le_reflect v
                              (real_lt_le_trans real_zero TV0
                                 (real_const v) Halt Htle) in
                          let h1 := qltT_leT' k0 1 h0lt1 in
                          let topcert :=
                            mixd_window_top_pass k0 v b0 (1 - k0) N N
                              h0 h1 hv hb0p
                              (qeq_imp_qeqT _ _ (Qeq_refl (1 - k0)))
                              (mixd_qsub_pos k0 h0lt1)
                              Hw
                              (NatLe_lift N (mixd_two_pow N)
                                 (Nat.le_trans N (Datatypes.S N)
                                    (mixd_two_pow N)
                                    (Nat.le_succ_diag_r N)
                                    (NatLe_drop (Datatypes.S N)
                                       (mixd_two_pow N)
                                       (mixd_two_pow_ge N)))) in
                          match mixd_k_select_log_cert k0 v b0 h0 h1 hv N
                          with
                          | Some (inl (existT _ kk Hcert), cc) =>
                              existT _ kk
                                (mixd_real_chain kappa TV0 budget k0 v b0 kk
                                   Hk1 h0
                                   (mixd_lt_to_le kappa (real_const k0)
                                      Hk0lt)
                                   Halt Htle Hb0lt Hcert)
                          | Some (inr (existT _ kk Hcert), cc) =>
                              existT _ kk
                                (mixd_real_chain kappa TV0 budget k0 v b0 kk
                                   Hk1 h0
                                   (mixd_lt_to_le kappa (real_const k0)
                                      Hk0lt)
                                   Halt Htle Hb0lt Hcert)
                          | None =>
                              existT _ (mixd_two_pow N)
                                (mixd_real_chain kappa TV0 budget k0 v b0
                                   (mixd_two_pow N) Hk1 h0
                                   (mixd_lt_to_le kappa (real_const k0)
                                      Hk0lt)
                                   Halt Htle Hb0lt topcert)
                          end
                      end
                  end
              end
      end
  end
  end.

(* Main piece: the log-depth selector (sigT Set form, Defined, extractable). *)
Definition mixd_k_select_log (kappa TV0 budget : Real)
    (Hk1 : real_lt real_zero kappa) (Hk2 : real_lt kappa real_one)
    (Ha : real_le real_zero TV0) (Hbudget : real_lt real_zero budget)
    (Htv : sigT (fun v : Q => real_le TV0 (real_const v)))
    (Hwin : forall (v k0 b0 : Q),
              sigT (fun N : nat =>
                QleT' v (Qmult (Qmake (Z.of_nat N) 1)
                                 (Qmult (1 - k0) b0))))
  : sigT (fun k : nat => real_lt (real_mult (tv_rpow kappa k) TV0) budget) :=
  match Ha as Haa return real_le real_zero TV0 ->
                   sigT (fun k : nat =>
                     real_lt (real_mult (tv_rpow kappa k) TV0) budget) with
  | inl Halt =>
      fun _ =>
        mixd_k_select_log_pos kappa TV0 budget Hk1 Hk2 Halt Hbudget Htv Hwin
  | inr Haq =>
      fun _ => mix_k_select kappa TV0 budget Hk1 Hk2 Ha Hbudget
  end Ha.

(* le-face corollary (Defined). *)
Definition mixd_k_select_log_le (kappa TV0 budget : Real)
    (Hk1 : real_lt real_zero kappa) (Hk2 : real_lt kappa real_one)
    (Ha : real_le real_zero TV0) (Hbudget : real_lt real_zero budget)
    (Htv : sigT (fun v : Q => real_le TV0 (real_const v)))
    (Hwin : forall (v k0 b0 : Q),
              sigT (fun N : nat =>
                QleT' v (Qmult (Qmake (Z.of_nat N) 1)
                                 (Qmult (1 - k0) b0))))
  : sigT (fun k : nat => real_le (real_mult (tv_rpow kappa k) TV0) budget) :=
  match mixd_k_select_log kappa TV0 budget Hk1 Hk2 Ha Hbudget Htv Hwin with
  | existT _ k Hk => existT _ k (mixd_lt_to_le _ _ Hk)
  end.

(* ============================ Assumption audit ============================ *)

Print Assumptions state_value_req.
Print Assumptions advantage_req.
Print Assumptions kl_to_ref_req.
Print Assumptions rppo_pistar.
Print Assumptions rppo_pistar_pos.
Print Assumptions policy_ratio_req.
Print Assumptions rppo_opp_one_mult.
Print Assumptions rppo_sum_opp.
Print Assumptions rppo_sum_minus.
Print Assumptions rppo_KL_self_zero.
Print Assumptions rppo_constant_sum.
Print Assumptions rppo_plus_opp_plus_r.
Print Assumptions rppo_advantage_sum_ref.
Print Assumptions rppo_dpo_reward_is_implicit.
Print Assumptions rppo_advantage_expectation_zero.
Print Assumptions rppo_align_objective_decomp.
Print Assumptions rppo_exact_improvement_identity.
Print Assumptions rppo_ppo_monotonic_improvement.
Print Assumptions rppo_kl_penalty_sufficient.
Print Assumptions rppo_ppo_gap_exact.
Print Assumptions rppo_importance_ratio_self_one.
Print Assumptions rppo_ppo_surrogate_raw_is_value_improvement.
Print Assumptions rppo_rlhf_optimal_value.
Print Assumptions rppo_pi_star_objective_value.
Print Assumptions rppo_align_free_energy_explicit.
Print Assumptions rppo_free_energy_ext_gen.
Print Assumptions rppo_boltzmann_pos.
Print Assumptions rppo_align_free_energy_pi_star.
Print Assumptions rppo_b_collapse_minus.
Print Assumptions rppo_J_ref_eq_value.
Print Assumptions rppo_align_objective_advantage_decomp.
Print Assumptions mixd_qeq_mult_r.
Print Assumptions mixd_qeq_mult_l.
Print Assumptions mixd_qeqT_trans_l.
Print Assumptions mixd_leT_transport.
Print Assumptions mixd_qlt_eq_l.
Print Assumptions mixd_qlt_eq_r.
Print Assumptions mixd_qle_eq_l.
Print Assumptions mixd_qle_eq_r.
Print Assumptions mixd_qleT'_trans.
Print Assumptions mixd_qpow_eq_compat.
Print Assumptions mixd_qring_cancel_r.
Print Assumptions mixd_half_pos.
Print Assumptions mixd_half_lt_one.
Print Assumptions mixd_qlt_add_pos.
Print Assumptions mixd_qsub_lt2.
Print Assumptions mixd_qsub_le.
Print Assumptions mixd_qsub_ge0.
Print Assumptions mixd_qsub_pos.
Print Assumptions mixd_qle_bool_false_lt.
Print Assumptions mixd_qmax_eq_l.
Print Assumptions mixd_qmax_eq_r.
Print Assumptions mixd_qnatw_nonneg.
Print Assumptions mixd_qpow_nonneg.
Print Assumptions mixd_half_lt.
Print Assumptions mixd_qmult_le_compat_l.
Print Assumptions mixd_qpow_le1.
Print Assumptions mixd_qpow_anti.
Print Assumptions mixd_fail_down.
Print Assumptions mixd_two_pow_ge.
Print Assumptions mixd_qpow_plus.
Print Assumptions mixd_ladder_spec.
Print Assumptions mixd_acc_cert.
Print Assumptions mixd_qeqT_one_mul.
Print Assumptions mixd_qeqT_sym.
Print Assumptions mixd_qeq_sq.
Print Assumptions mixd_qeq_step.
Print Assumptions mixd_qeq_step0.
Print Assumptions mixd_qleF_lt.
Print Assumptions mixd_mw_le_boost.
Print Assumptions mixd_qnat_succ.
Print Assumptions mixd_qbern.
Print Assumptions mixd_window_pass.
Print Assumptions mixd_window_top_pass.
Print Assumptions mixd_some_inj_fst.
Print Assumptions mixd_some_inj_snd.
Print Assumptions mixd_some_inl_fst.
Print Assumptions mixd_scan_up.
Print Assumptions mixd_scan_up_none.
Print Assumptions mixd_scan_up_some.
Print Assumptions mixd_desc.
Print Assumptions mixd_desc_spec.
Print Assumptions mixd_k_select_log_cert.
Print Assumptions mixd_k_select_log_cert_spec.
Print Assumptions mixd_k_select_log_mulcost.
Print Assumptions mixd_k_select_log_cert_fb.
Print Assumptions mixd_k_select_log_cert_none.
Print Assumptions mixd_const_proj.
Print Assumptions mixd_zero_proj.
Print Assumptions mixd_one_proj.
Print Assumptions mixd_const_le_reflect.
Print Assumptions mixd_const_pos.
Print Assumptions mixd_const_mult.
Print Assumptions mixd_rpow_const.
Print Assumptions mixd_rpow_const_eq.
Print Assumptions mixd_pow_base_mono.
Print Assumptions mixd_kappa0_gap.
Print Assumptions mixd_kappa0_cert.
Print Assumptions mixd_b0_cert.
Print Assumptions mixd_real_chain.
Print Assumptions mixd_k_select_log_pos.
Print Assumptions mixd_k_select_log.
Print Assumptions mixd_k_select_log_le.
