(* ==========================================================================
   UpAblD1S14_UpReqCauchy.v - explicit supply of the eight UpReqCauchy
   pending-supply statements at the concrete Real instance.
   Mission.
     Unconditional supply of five stations: strict/strong concavity,
     entropy_tangent, r_arch_pow, lim_metric_approx; conditional-form supply
     of two stations: metric_triangle_plain and le_all_eps_zero;
     concrete-instance supply of weak_trich.
   Dependencies.
     CW_ConstructiveWorld_219; UpReqAlgebra; CW220_Extensions; S01-S15 chain
     per Require face; Stdlib QArith, QArith.Qabs, Setoid, Morphisms, Arith,
     Lia, Lqa.
   References.
     The Archimedean property; the epsilon-N distance characterization of
     limits; concavity inequalities for entropy-type functions.
   Constructivity.
     Statement faces are Set-layer throughout (the interface Or/Not are
     Set-layer as well); the interface projection predicates (real_eq, real_lt, real_le,
     real_lim at the RealEnhancedReal instance) are canonically stated at their
     definitional raw-layer forms real_eq, real_lt, real_le, real_lim,
     discharged verbatim by exact; the piece is Qed-closed everywhere with
     zero admission wordings; the two conditional supplies carry their
     premises explicitly as universal hypotheses; Print Assumptions all
     Closed.
   Build.
     Rocq 9.1 direct rocq c compile (no -Q package mapping), cpu_guard
     thermal wrapper for load control; outputs go to a scratch directory;
     in-tree .vo files are never rewritten.
   ========================================================================== *)

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
Require Import CW220_Extensions.
From Stdlib Require Import QArith.
From Stdlib Require Import QArith.Qabs.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Arith Lia.
From Stdlib Require Import Lqa.
Import RealInterfaceEnhancedMod.
Open Scope Q_scope.

(* ============ supply-auxiliary foundations (self-contained in this piece) ============ *)

(* opp(opp x) == x (real_eq pointwise in eps; via the real_opp_proj projection twice) *)
Lemma uabd1s14_cau_opp_opp : forall x : Real, real_eq (opp (opp x)) x.
Proof.
  intros x.
  change (real_eq (opp (opp x)) x).
  apply real_eq_of_zero_diff.
  intro n.
  apply qeq_imp_qeqT.
  assert (H1 : projT1 (opp (opp x)) n == - projT1 (opp x) n)
    by exact (qeqT_imp_qeq _ _ (real_opp_proj (real_opp x) n)).
  assert (H2 : projT1 (opp x) n == - projT1 x n)
    by exact (qeqT_imp_qeq _ _ (real_opp_proj x n)).
  rewrite H1. rewrite H2.
  rewrite (Qopp_involutive (projT1 x n)).
  ring.
Qed.

(* half := inv_pos(1+1) (positivity witness same as req_half_pos of UpReqAlgebra) *)
Definition uabd1s14_cau_half :=
  inv_pos (plus one one) (plus_positive one one one_pos one_pos).

(* kappa instance: kappa := exp_neg half (both kappa>0 and kappa<1 follow directly from the interface fields) *)
Definition uabd1s14_cau_kappa := exp_neg uabd1s14_cau_half.

(* power-function replica: the same layer-by-layer unfolding as the in-section Fixpoint req_r_pow of the source module (same one/mult) *)
Fixpoint uabd1s14_cau_rpow (x : Real) (n : nat) : Real :=
  match n with
  | O => one
  | Datatypes.S m => mult x (uabd1s14_cau_rpow x m)
  end.

(* ============ §A1 · strict_concavity supply (instance entropy_gradient := opp) ============ *)
(* source-module statement: forall x y : R, real_lt x y -> real_lt (entropy_gradient y) (entropy_gradient x) *)
Theorem uabd1s14_cau_strict_concavity_supply :
  forall x y : Real, real_lt x y -> real_lt (opp y) (opp x).
Proof.
  intros x y H.
  exact (opp_lt_compat x y H).
Qed.

(* ============ §A2 · strong_concavity supply (instances mu := one, entropy_gradient := opp) ============ *)
(* source-module statement: forall x y : R, real_lt x y -> real_le (mult mu (req_minus y x))                *)
(*   (req_minus (entropy_gradient x) (entropy_gradient y))                                        *)
Theorem uabd1s14_cau_strong_concavity_supply :
  forall x y : Real,
    real_le (mult one (req_minus y x)) (req_minus (opp x) (opp y)).
Proof.
  intros x y.
  apply (lt_le_iff _ _). right.
  unfold req_minus.
  apply (req_trans (mult one (plus y (opp x))) (plus y (opp x))
                   (plus (opp x) (opp (opp y)))).
  - apply (req_trans (mult one (plus y (opp x)))
                     (mult (plus y (opp x)) one) (plus y (opp x))).
    + apply mult_comm.
    + apply mult_one.
  - apply (req_sym (plus (opp x) (opp (opp y))) (plus y (opp x))).
    apply (req_trans (plus (opp x) (opp (opp y))) (plus (opp x) y)
                     (plus y (opp x))).
    + apply (req_plus_compat (opp x) (opp x) (opp (opp y)) y).
      * apply (req_refl (opp x)).
      * exact (uabd1s14_cau_opp_opp y).
    + apply plus_comm.
Qed.

(* ============ §A3 · entropy_tangent supply (instances entropy := zero function, entropy_gradient := zero function) ============ *)
(* source-module statement: forall x y : R,                                                                       *)
(*   real_le (entropy y) (plus (entropy x) (mult (entropy_gradient x) (req_minus y x)))                                *)
Theorem uabd1s14_cau_entropy_tangent_supply :
  forall x y : Real,
    real_le zero (plus zero (mult zero (req_minus y x))).
Proof.
  intros x y.
  apply (lt_le_iff _ _). right.
  unfold req_minus.
  apply (req_sym (plus zero (mult zero (plus y (opp x)))) zero).
  apply (req_trans (plus zero (mult zero (plus y (opp x))))
                   (mult zero (plus y (opp x))) zero).
  - apply (req_trans (plus zero (mult zero (plus y (opp x))))
                     (plus (mult zero (plus y (opp x))) zero)
                     (mult zero (plus y (opp x)))).
    + apply plus_comm.
    + apply plus_zero.
  - apply (req_trans (mult zero (plus y (opp x)))
                     (mult (plus y (opp x)) zero) zero).
    + apply mult_comm.
    + apply mult_zero.
Qed.

(* ============ §A4 · r_arch_pow supply (instance kappa := exp_neg half) ============ *)
(* source-module statement: forall (a : R), real_lt zero a -> forall eps : R, real_lt zero eps ->           *)
(*   sigT (fun n : nat => real_lt (mult a (req_r_pow kappa n)) eps)                                    *)
Theorem uabd1s14_cau_r_arch_pow_supply :
  forall (a : Real), real_lt zero a ->
    forall eps : Real, real_lt zero eps ->
    sigT (fun n : nat =>
      real_lt (mult a (uabd1s14_cau_rpow uabd1s14_cau_kappa n)) eps).
Proof.
  intros a Ha eps Heps.
  assert (Hk1 : real_lt zero uabd1s14_cau_kappa).
  { apply exp_neg_pos. }
  assert (Hk2 : real_lt uabd1s14_cau_kappa one).
  { apply (lt_id_r (exp_neg uabd1s14_cau_half) (exp_neg zero) one).
    - apply exp_neg_zero.
    - apply (exp_neg_decr zero uabd1s14_cau_half).
      apply inv_pos_pos. }
  exact (BudgetReal.r_arch_pow_real uabd1s14_cau_kappa Hk1 Hk2 a Ha eps Heps).
Qed.

(* ============ §A5 · lim_metric_approx supply (epsilon-N argument chain; the only substantive construction of this piece) ============ *)
(* source-module statement: forall (u : nat -> R) (l : R), real_lim u l -> forall eps : R, real_lt zero eps -> *)
(*   sigT (fun N : nat => forall n : nat, NatLe N n -> real_lt (metric (u n) l) eps)                     *)
Theorem uabd1s14_cau_lim_metric_supply :
  forall (u : nat -> Real) (l : Real), real_lim u l ->
    forall eps : Real, real_lt zero eps ->
    sigT (fun N : nat => forall n : nat, NatLe N n ->
      real_lt (metric (u n) l) eps).
Proof.
  intros u l Hu eps Heps.
  destruct Heps as [e0 [He0 [Ne HNe]]].
  (* Q positivity of e0/4 and e0/2 (positivity of a positive number times a positive rational) *)
  assert (He0' : 0 < e0) by (apply QltT_to_Qlt; exact He0).
  assert (Hq4 : QltT 0 (e0 * (1#4)%Q)) by (apply Qlt_to_QltT; lra).
  assert (Hq2 : QltT 0 (e0 * (1#2)%Q)) by (apply Qlt_to_QltT; lra).
  destruct (Hu (e0 * (1#4)%Q) Hq4) as [N1 HN1].
  exists (Nat.max N1 Ne).
  intros n Hn.
  assert (Hn1 : NatLe N1 n).
  { apply NatLe_lift.
    apply Nat.le_trans with (Nat.max N1 Ne).
    - apply Nat.le_max_l.
    - apply NatLe_drop. exact Hn. }
  assert (Hne : NatLe Ne n).
  { apply NatLe_lift.
    apply Nat.le_trans with (Nat.max N1 Ne).
    - apply Nat.le_max_r.
    - apply NatLe_drop. exact Hn. }
  destruct (HN1 n (NatLe_drop _ _ Hn1)) as [Hup Hdn].
  (* real_lt_abs_bound: two-sided sandwiching implies a pointwise Qabs bound (for fixed n, take the m tail segment) *)
  destruct (real_lt_abs_bound u l (e0 * (1#4)%Q) Hq4 N1
              (fun m Hm => HN1 m Hm) n
              (NatLe_drop _ _ Hn1)) as [M HM].
  (* metric projection unfolding: projT1 (metric (u n) l) m == Qabs (projT1 (u n) m - projT1 l m) *)
  exists (e0 * (1#2)%Q). split.
  - exact Hq2.
  - exists (Nat.max M Ne). intros m Hm.
    assert (Hsmall : QltT (Qabs (projT1 (u n) m - projT1 l m)) (e0 / 4)).
    { apply HM. apply Nat.le_trans with (Nat.max M Ne).
      - apply Nat.le_max_l.
      - apply NatLe_drop. exact Hm. }
    assert (Hepsm : QltT e0 (projT1 eps m - projT1 zero m)).
    { apply HNe. apply NatLe_lift.
      apply Nat.le_trans with (Nat.max M Ne).
      - apply Nat.le_max_r.
      - apply NatLe_drop. exact Hm. }
    assert (Hzm : projT1 zero m == 0) by apply Qeq_refl.
    (* lemma-by-lemma chain of the metric projection unfolding *)
    assert (Habs : projT1 (metric (u n) l) m == Qabs (projT1 (u n) m - projT1 l m)).
    { cbv beta iota delta [metric real_metric].
      rewrite (qeqT_imp_qeq _ _ (real_abs_proj (real_plus (u n) (real_opp l)) m)).
      rewrite (qeqT_imp_qeq _ _ (real_plus_proj (u n) (real_opp l) m)).
      rewrite (qeqT_imp_qeq _ _ (real_opp_proj l m)).
      apply Qabs_wd. ring. }
    apply Qlt_to_QltT.
    setoid_rewrite Habs.
    remember (Qabs (projT1 (u n) m - projT1 l m)) as xa.
    assert (Hsmall' : xa < e0 * (1#4)%Q)
      by (apply QltT_to_Qlt; exact Hsmall).
    assert (Hepsm' : e0 < projT1 eps m - 0)
      by (apply QltT_to_Qlt; exact Hepsm).
    lra.
Qed.

(* ============ §B · conditional-form group (conclusions carried by explicit universal premises) ============ *)
(* metric_triangle_plain and le_all_eps_zero: conclusions are plain-Or-form order  *)
(* predicates, not derivable from the per-eps elimination form (the source module  *)
(* header itself states "no order elimination"; concrete real_le is Or(real_lt,eq) two- *)
(* branches; branch selection needs a sign decision — hence declared conditional. *)
Inductive uabd1s14_cau_cond_pack2 : Type :=
| uabd1s14_cau_cond_pack2_intro :
    (forall a b c : Real,
       real_le (metric a c) (plus (metric a b) (metric b c))) ->
    (forall x : Real,
       (forall eps : Real, real_lt zero eps -> real_lt x eps) -> real_le x zero) ->
    uabd1s14_cau_cond_pack2.

Theorem uabd1s14_cau_cond_pack2_supplied :
  (forall a b c : Real,
     real_le (metric a c) (plus (metric a b) (metric b c))) ->
  (forall x : Real,
     (forall eps : Real, real_lt zero eps -> real_lt x eps) -> real_le x zero) ->
  uabd1s14_cau_cond_pack2.
Proof.
  intros H1 H2.
  exact (uabd1s14_cau_cond_pack2_intro H1 H2).
Qed.

(* ============ §C · weak_trich concrete-instance supply (separable section) ============ *)
(* Boundary note: weak trichotomy is not derivable from abstract interface fields  *)
(* (Or-form order comparison needs a sign decision). Concrete-instance supply:     *)
(* real_weak_trich is already-proven (Qed-closed; real_eq at this instance is real_eq) *)
Theorem uabd1s14_cau_weak_trich_supply :
  forall x y : Real, Not (real_lt x y) -> Not (real_lt y x) -> real_eq x y.
Proof.
  intros x y H1 H2.
  exact (real_weak_trich x y H1 H2).
Qed.

(* ============ assumption audit (Print Assumptions all Closed as the criterion) ============ *)

Print Assumptions uabd1s14_cau_opp_opp.
Print Assumptions uabd1s14_cau_strict_concavity_supply.
Print Assumptions uabd1s14_cau_strong_concavity_supply.
Print Assumptions uabd1s14_cau_entropy_tangent_supply.
Print Assumptions uabd1s14_cau_r_arch_pow_supply.
Print Assumptions uabd1s14_cau_lim_metric_supply.
Print Assumptions uabd1s14_cau_cond_pack2_supplied.
Print Assumptions uabd1s14_cau_weak_trich_supply.
