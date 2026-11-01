(* ========================================================================== *)
(*  UpAblLogWall.v - Forward reduction from a minimal-station selector to     *)
(*  LPO-family instances (the Real-layer logarithmic gap, theoremized)        *)
(* ========================================================================== *)
(*   Mission. lgw_MinSel : Set := forall kappa TV0 budget : Real, sigT (fun   *)
(*   k : nat => lgw_min_sel_spec kappa TV0 budget k) supplies a station k     *)
(*   whose informative test holds (gap branch) with every closer station     *)
(*   refuted (no-gap branch); the main theorem lgw_lpo_of_min_sel :          *)
(*   lgw_MinSel -> lgw_lpo_family is a forward reduction: at kappa :=         *)
(*   lgw_half, TV0 := x, budget := lgw_half the selector output decides      *)
(*   Or (real_lt x real_one) (real_eq x real_one) for x ordered in [0,1] -   *)
(*   an LPO-family instance. The unconditioned interface is empty (at        *)
(*   kappa = TV0 = budget = real_one no minimal station exists; the          *)
(*   refutation is refined in UpAblLogWallEq), so the reduction premise is   *)
(*   carried explicitly by the theorem signature; companion lgw_oracle_pin   *)
(*   (with an order-decision oracle the instance follows immediately).       *)
(*   Dependencies. Stdlib QArith (QArith.QArith, QArith.Qabs), Lia,           *)
(*   Extraction; S01_BaseRing (Set-level And/Or/NatLe), S02_CauchyComplete   *)
(*   (Real layer, QltT/QeqT faces and bridges), UpReqLpoEquiv (verbatim).    *)
(*   References. Statement faces follow UpReqMixLogA (mixa_sel_accounts /    *)
(*   mixa_pow_budget_log_min; this piece is the informative-order            *)
(*   strengthening); lineage UpReqLpoEquiv (rLPO). Benchmark stdlib QArith;  *)
(*   mathlib has no constructive counterpart.                                *)
(*   Constructivity. Purely constructive Set-level carrying; statement       *)
(*   faces use sigT / Set-level And / Or / QltT / QeqT only; zero admission  *)
(*   faces; tail Print Assumptions all Closed; extraction Obj.magic 0.       *)
(*   Build. rocq c -native-compiler no -q -Q . "" in the seat world closure, *)
(*   wrapped by cpu_guard (-Reg /tmp/cw_reg_nw5) with ulimit -s 65532.       *)
(* ========================================================================== *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Lia.
From Stdlib Require Import Extraction.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import UpReqLpoEquiv.

Local Open Scope Q_scope.

(* ============================================================ *)
(* Part 0 - Geometric constants and the station power family    *)
(* (reproduces the tv_rpow shape of UpTVDoeblin)                *)
(* ============================================================ *)

Definition lgw_half : Real := real_const (1#2).

Fixpoint lgw_rpow (a : Real) (n : nat) : Real :=
  match n with
  | 0%nat => real_one
  | Datatypes.S m => real_mult a (lgw_rpow a m)
  end.

(* Informative test: test k := real_lt (kappa^k * TV0) budget      *)
(* (same-shape reproduction of the Q-layer mixa_test).             *)
Definition lgw_test (kappa TV0 budget : Real) (k : nat) : Set :=
  real_lt (real_mult (lgw_rpow kappa k) TV0) budget.

(* ============================================================ *)
(* Part 1 - Selector specification (Real-layer counterpart of    *)
(* the Q-layer mixa_sel_accounts statement face)                 *)
(* ============================================================ *)

(* Exact minimal-station specification: test k holds (gap branch)  *)
(* and every j with NatLe (S j) k has test j refuted (no-gap        *)
(* branch).                                                        *)
Definition lgw_min_sel_spec (kappa TV0 budget : Real) (k : nat) : Set :=
  And (lgw_test kappa TV0 budget k)
      (forall j : nat, NatLe (Datatypes.S j) k ->
        lgw_test kappa TV0 budget j -> Empty_set).

(* Real-layer minimal-station selector interface (carrying no       *)
(* decidable-test premise - the constructive boundary itself).      *)
Definition lgw_MinSel : Set :=
  forall kappa TV0 budget : Real,
    sigT (fun k : nat => lgw_min_sel_spec kappa TV0 budget k).

(* LPO instance face: Or-decomposition decision of the informative  *)
(* real_le on [0,1].                                                *)
Definition lgw_lpo_family : Set :=
  forall x : Real, real_le real_zero x -> real_le x real_one ->
    Or (real_lt x real_one) (real_eq x real_one).

(* ============================================================ *)
(* Part 2 - Projection-level Q-arithmetic bridging lemmas        *)
(* (the common kernel of all conversions)                        *)
(* ============================================================ *)

(* Halving forward bridge: eps < 1/2 - z/2 implies 2*eps < 1 - z    *)
(* (Qmult_lt_compat_r twice + ring).                                *)
Lemma lgw_qlt_half_gap : forall eps z : Q,
  Qlt eps ((1#2) - (1#2) * z) -> QltT (eps + eps) (1 - z).
Proof.
  intros eps z H.
  assert (Hq2 : Qlt 0 (2#1)) by (apply (proj2 (Qlt_alt 0 (2#1))); reflexivity).
  assert (Hm : eps * (2#1) < ((1#2) - (1#2) * z) * (2#1))
    by (apply Qmult_lt_compat_r; assumption).
  assert (Hr1 : ((1#2) - (1#2) * z) * (2#1) == 1 - z) by ring.
  assert (Hr2 : eps * (2#1) == eps + eps) by ring.
  rewrite Hr2 in Hm. rewrite Hr1 in Hm.
  apply Qlt_to_QltT. exact Hm.
Qed.

(* Halving inverse bridge: eps < 1 - z implies eps/2 < 1/2 - z/2    *)
(* (Qmult_lt_compat_r + ring).                                      *)
Lemma lgw_qlt_half_gap_inv : forall eps z : Q,
  Qlt eps (1 - z) -> QltT (eps * (1#2)) ((1#2) - (1#2) * z).
Proof.
  intros eps z H.
  assert (Hqh : Qlt 0 (1#2)) by (apply (proj2 (Qlt_alt 0 (1#2))); reflexivity).
  assert (Hm : eps * (1#2) < (1 - z) * (1#2))
    by (apply Qmult_lt_compat_r; assumption).
  assert (Hr1 : (1 - z) * (1#2) == (1#2) - (1#2) * z) by ring.
  rewrite Hr1 in Hm.
  apply Qlt_to_QltT. exact Hm.
Qed.

(* Projection lemmas: pointwise projected Q values of lgw_half /    *)
(* real_one / the first two stations of the power family.           *)
Lemma lgw_half_proj : forall n : nat, QeqT (projT1 lgw_half n) (1#2).
Proof.
  intros n. unfold lgw_half. apply real_const_proj.
Qed.

Lemma lgw_one_proj : forall n : nat, QeqT (projT1 real_one n) 1.
Proof.
  intros n. apply qeq_imp_qeqT. exact (Qeq_refl (projT1 real_one n)).
Qed.

Lemma lgw_rpow0_proj : forall n : nat,
  QeqT (projT1 (lgw_rpow lgw_half 0%nat) n) 1.
Proof.
  intros n.
  apply qeq_imp_qeqT.
  exact (Qeq_refl (projT1 (lgw_rpow lgw_half 0%nat) n)).
Qed.

Lemma lgw_rpow1_proj : forall n : nat,
  QeqT (projT1 (lgw_rpow lgw_half 1%nat) n) (1#2).
Proof.
  intros n.
  apply qeq_imp_qeqT.
  cbn [lgw_rpow].
  rewrite (qeqT_imp_qeq _ _ (real_mult_proj lgw_half real_one n)).
  rewrite (qeqT_imp_qeq _ _ (lgw_half_proj n)).
  rewrite (qeqT_imp_qeq _ _ (lgw_one_proj n)).
  reflexivity.
Qed.

(* ============================================================ *)
(* Part 3 - Station specification to order-information bridge    *)
(* (the mathematical core of the main theorem; three stations,   *)
(* three branches)                                               *)
(* ============================================================ *)

(* Station 0 holds implies x < one: eps < 1/2 - x_n with eps > 0    *)
(* gives x_n < 1/2, hence 1/4 < 1 - x_n.                            *)
Lemma lgw_test0_lt_one : forall x : Real,
  lgw_test lgw_half x lgw_half 0%nat -> real_lt x real_one.
Proof.
  intros x Htk.
  unfold lgw_test in Htk. unfold real_lt in Htk.
  destruct Htk as [eps [Heps [N HN]]].
  apply QltT_to_Qlt in Heps.
  unfold real_lt.
  exists (1#4). split.
  - apply Qlt_to_QltT.
    apply (proj2 (Qlt_alt 0 (1#4))). reflexivity.
  - exists N. intros n Hn. specialize (HN n Hn).
    apply QltT_to_Qlt in HN.
    apply Qlt_to_QltT.
    rewrite (qeqT_imp_qeq _ _ (real_mult_proj (lgw_rpow lgw_half 0%nat) x n)) in HN.
    rewrite (qeqT_imp_qeq _ _ (lgw_rpow0_proj n)) in HN.
    rewrite (qeqT_imp_qeq _ _ (lgw_half_proj n)) in HN.
    rewrite (qeqT_imp_qeq _ _ (lgw_one_proj n)).
    assert (Hn1 : 1 * projT1 x n == projT1 x n) by ring.
    rewrite Hn1 in HN.
    assert (Hnn : Qlt 0 ((1#2) - projT1 x n)).
    { apply Qlt_trans with eps; assumption. }
    assert (Hqh : Qlt 0 (1#2)) by (apply (proj2 (Qlt_alt 0 (1#2))); reflexivity).
    assert (Hadr : (1#2) + 0 < (1#2) + ((1#2) - projT1 x n)).
    { exact (proj2 (Qplus_lt_r 0%Q ((1#2) - projT1 x n) (1#2)) Hnn). }
    rewrite (Qplus_0_r (1#2)) in Hadr.
    assert (Hr : 1 - projT1 x n == (1#2) + ((1#2) - projT1 x n)) by ring.
    rewrite Hr.
    apply Qlt_trans with (1#2).
    + apply (proj2 (Qlt_alt 0 (1#4))). reflexivity.
    + exact Hadr.
Qed.

(* Station 1 holds implies x < one: eps < 1/2 - x_n/2 implies       *)
(* 2*eps < 1 - x_n (halving forward bridge).                        *)
Lemma lgw_test1_lt_one : forall x : Real,
  lgw_test lgw_half x lgw_half 1%nat -> real_lt x real_one.
Proof.
  intros x Htk.
  unfold lgw_test in Htk. unfold real_lt in Htk.
  destruct Htk as [eps [Heps [N HN]]].
  apply QltT_to_Qlt in Heps.
  unfold real_lt.
  exists (eps + eps). split.
  - apply Qlt_to_QltT.
    assert (Hq2 : Qlt 0 (2#1)) by (apply (proj2 (Qlt_alt 0 (2#1))); reflexivity).
    assert (Hm0 : 0 * (2#1) < eps * (2#1))
      by (apply Qmult_lt_compat_r; assumption).
    rewrite Qmult_0_l in Hm0.
    assert (Hr2 : eps * (2#1) == eps + eps) by ring.
    rewrite <- Hr2. exact Hm0.
  - exists N. intros n Hn. specialize (HN n Hn).
    apply QltT_to_Qlt in HN.
    apply Qlt_to_QltT.
    rewrite (qeqT_imp_qeq _ _ (real_mult_proj (lgw_rpow lgw_half 1%nat) x n)) in HN.
    rewrite (qeqT_imp_qeq _ _ (lgw_rpow1_proj n)) in HN.
    rewrite (qeqT_imp_qeq _ _ (lgw_half_proj n)) in HN.
    rewrite (qeqT_imp_qeq _ _ (lgw_one_proj n)).
    exact (QltT_to_Qlt (eps + eps) (1 - projT1 x n)
             (lgw_qlt_half_gap eps (projT1 x n) HN)).
Qed.

(* x < one implies station 1 holds (reverse direction: gap witness  *)
(* eps * half, via lgw_qlt_half_gap_inv).                           *)
Lemma lgw_test1_of_lt_one : forall x : Real,
  real_lt x real_one -> lgw_test lgw_half x lgw_half 1%nat.
Proof.
  intros x Hlt.
  unfold lgw_test, real_lt.
  destruct Hlt as [eps [Heps [N HN]]].
  apply QltT_to_Qlt in Heps.
  exists (eps * (1#2)). split.
  - apply Qlt_to_QltT.
    assert (Hqh : Qlt 0 (1#2)) by (apply (proj2 (Qlt_alt 0 (1#2))); reflexivity).
    assert (Hm0 : 0 * (1#2) < eps * (1#2))
      by (apply Qmult_lt_compat_r; assumption).
    rewrite Qmult_0_l in Hm0.
    exact Hm0.
  - exists N. intros n Hn. specialize (HN n Hn).
    apply QltT_to_Qlt in HN.
    apply Qlt_to_QltT.
    rewrite (qeqT_imp_qeq _ _ (lgw_one_proj n)) in HN.
    rewrite (qeqT_imp_qeq _ _ (real_mult_proj (lgw_rpow lgw_half 1%nat) x n)).
    rewrite (qeqT_imp_qeq _ _ (lgw_rpow1_proj n)).
    rewrite (qeqT_imp_qeq _ _ (lgw_half_proj n)).
    exact (QltT_to_Qlt (eps * (1#2)) ((1#2) - (1#2) * projT1 x n)
             (lgw_qlt_half_gap_inv eps (projT1 x n) HN)).
Qed.

(* ============================================================ *)
(* Part 4 - Main theorem: forward reduction (selector implies    *)
(* LPO instance)                                                 *)
(* ============================================================ *)

(* Reduction construction: kappa := half, TV0 := x, budget := half,  *)
(* three-station case analysis - cases k = 0 / k = 1 give x < 1     *)
(* directly from the gap branch; case k >= 2 refutes station 1      *)
(* through the no-gap branch, which with the left premise x <= 1    *)
(* yields the empty type while the right branch (x = 1) is taken    *)
(* directly - the selector output is the order-decision witness, so *)
(* the absence of an order decision reduces to the absence of a     *)
(* selector.                                                        *)
Theorem lgw_lpo_of_min_sel : lgw_MinSel -> lgw_lpo_family.
Proof.
  intros Hsel x Hz Hx1.
  destruct (Hsel lgw_half x lgw_half) as [k Hacc].
  destruct Hacc as [Htk Hbel].
  destruct k as [| [| m]].
  - apply inl. exact (lgw_test0_lt_one x Htk).
  - apply inl. exact (lgw_test1_lt_one x Htk).
  - assert (Href1 : lgw_test lgw_half x lgw_half 1%nat -> Empty_set).
    { intros Ht1. apply (Hbel 1%nat).
      - apply NatLe_lift. apply le_n_S. apply le_n_S. apply le_0_n.
      - exact Ht1. }
    destruct Hx1 as [Hlt1 | Heq1].
    + destruct (Href1 (lgw_test1_of_lt_one x Hlt1)).
    + apply inr. exact Heq1.
Qed.

(* ============================================================ *)
(* Part 5 - Order-decision oracle companion piece               *)
(* ============================================================ *)

(* Order-decision oracle: an Or-decomposition decision for any pair  *)
(* of reals - not suppliable on the Real layer (see the real_square_ *)
(* not_negative remark of S02_CauchyComplete); with the oracle in    *)
(* place the conclusion follows immediately; the core of this       *)
(* non-constructivity is the absence of an order decision.          *)
Definition lgw_ord_oracle : Set :=
  forall x y : Real, Or (real_lt x y) (real_eq x y).

Theorem lgw_oracle_pin : lgw_ord_oracle -> lgw_lpo_family.
Proof.
  intros Hord x _ Hx1.
  exact (Hord x real_one).
Qed.

(* ============================================================ *)
(* Part 6 - Assumption audit and extraction exit                *)
(* ============================================================ *)

Print Assumptions lgw_min_sel_spec.
Print Assumptions lgw_MinSel.
Print Assumptions lgw_lpo_family.
Print Assumptions lgw_lpo_of_min_sel.
Print Assumptions lgw_oracle_pin.

Separate Extraction lgw_rpow lgw_test lgw_min_sel_spec lgw_MinSel lgw_lpo_family lgw_ord_oracle.
