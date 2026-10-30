(* ================================================================== *)
(* PintMono.v -- P1 integral machinery, phase two: monotonicity and    *)
(* positivity engines for rational polynomial integrals, on top of the *)
(* phase-one linear functional pint_integral over Q-coefficient lists; *)
(* preparation for the Beukers mainline.                               *)
(* ================================================================== *)
(* Mission.  Formalization of the properties stated by the theorem and *)
(* lemma declaration surface of this file.                             *)
(* Dependencies.  Stdlib QArith.QArith, QArith.Qabs, Lists.List,       *)
(* Arith.Arith, ZArith.ZArith, Lia; library modules S01_BaseRing,      *)
(* S02_CauchyComplete, PolyIntegral -- exactly the in-file Require     *)
(* list; phase-one pint_integral_* results are used, never re-proved.  *)
(* References.  Part 1 pm_qleT'_mult_r / pm_qle_wd_l / pm_qle_wd_r:    *)
(* QleT' (Set) statements, Qeq premises proof-only, Q-level monotone   *)
(* rewriting.  Part 2 pm_eval_ge0 / pm_eval_le0 / pm_pointwise_le_eval *)
(* turns coefficient-wise sign into eval sign under 0 <= x, zero Prop. *)
(* Part 3 pm_monomial_int_nonpos / pm_integral_from_nonpos /           *)
(* pm_pointwise_le_integral: integral monotonicity without an          *)
(* equal-length premise (four-branch induction, out-of-range coeff 0). *)
(* Part 4 pm_monomial_int_pos / pm_integral_from_pos_strict /          *)
(* pm_integral_pos_strict / pm_integral_from_pos / pm_integral_pos:    *)
(* strict positivity, witnesses carried by sigT (Set), zero Prop.      *)
(* Part 5 pm_scale_mono / pm_add_mono: linearity-based monotonicity,   *)
(* length premises carried as Id : Set (S01), not Prop eq.             *)
(* Constructivity.  No admission-style statements (mechanically        *)
(* audited): all six main theorems report Closed under the global      *)
(* context through the Print Assumptions block at file end;            *)
(* statements are Prop-free (Qeq / Qle appear in proofs only).         *)
(* Build.  rocq c -native-compiler no -q -Q <source-seat world_pm> ""  *)
(* PintMono.v (Rocq 9.1.0), same-world dependency .vo chain.           *)

From Stdlib Require Import QArith.QArith QArith.Qabs Lists.List Arith.Arith
               ZArith.ZArith Lia.
Import ListNotations.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import PolyIntegral.

(* ============================================================ *)
(* Part 1. QleT' operation support pieces (internal Q level,    *)
(* proof-only).                                                 *)
(* ============================================================ *)

(* QleT' multiplicative right order-preservation: a <= b, 0 <= c *)
(* imply a*c <= b*c *)
Lemma pm_qleT'_mult_r : forall a b c : Q,
  QleT' a b -> QleT' 0 c -> QleT' (a * c) (b * c).
Proof.
  intros a b c Hab Hc. apply Qle_to_QleT'.
  apply (Qmult_le_compat_r a b c).
  - apply QleT'_to_Qle. exact Hab.
  - apply QleT'_to_Qle. exact Hc.
Qed.

(* QleT' multiplicative left order-preservation: a <= b, 0 <= c *)
(* imply c*a <= c*b (bridged through Qmult_comm) *)
Lemma pm_qleT'_mult_l : forall a b c : Q,
  QleT' a b -> QleT' 0 c -> QleT' (c * a) (c * b).
Proof.
  intros a b c Hab Hc. apply Qle_to_QleT'.
  rewrite (Qmult_comm c a).
  rewrite (Qmult_comm c b).
  apply (Qmult_le_compat_r a b c).
  - apply QleT'_to_Qle. exact Hab.
  - apply QleT'_to_Qle. exact Hc.
Qed.

(* QleT' left-end reshaping under Qeq: x == y, QleT' x z imply *)
(* QleT' y z (internal piece) *)
Lemma pm_qle_wd_l : forall x y z : Q, x == y -> QleT' x z -> QleT' y z.
Proof.
  intros x y z Hxy Hxz. apply Qle_to_QleT'.
  rewrite <- Hxy. apply QleT'_to_Qle. exact Hxz.
Qed.

(* QleT' right-end reshaping under Qeq: x == y, QleT' z x imply *)
(* QleT' z y (internal piece) *)
Lemma pm_qle_wd_r : forall x y z : Q, x == y -> QleT' z x -> QleT' z y.
Proof.
  intros x y z Hxy Hzx. apply Qle_to_QleT'.
  rewrite <- Hxy. apply QleT'_to_Qle. exact Hzx.
Qed.

(* Three multiplication reshaping pieces (assembled from the Qeq *)
(* rewriting bridges + Qmult_comm, sidestepping Z-level rewrite  *)
(* matching) *)
Lemma pm_mult_r0_le : forall b c : Q,
  QleT' 0 b -> QleT' 0 c -> QleT' 0 (c * b).
Proof.
  intros b c Hb Hc.
  apply (pm_qle_wd_l (0 * c) 0 (c * b)).
  - apply Qmult_0_l.
  - apply (pm_qle_wd_r (b * c) (c * b)).
    + apply Qmult_comm.
    + apply (pm_qleT'_mult_r 0 b c).
      * exact Hb.
      * exact Hc.
Qed.

Lemma pm_mult_r0_le0 : forall a c : Q,
  QleT' a 0 -> QleT' 0 c -> QleT' (c * a) 0.
Proof.
  intros a c Ha Hc.
  apply (pm_qle_wd_l (a * c) (c * a) 0).
  - apply Qmult_comm.
  - apply (pm_qle_wd_r (0 * c) 0).
    + apply Qmult_0_l.
    + apply (pm_qleT'_mult_r a 0 c).
      * exact Ha.
      * exact Hc.
Qed.

Lemma pm_qleT'_comm_l : forall a b c : Q,
  QleT' (a * c) (b * c) -> QleT' (c * a) (c * b).
Proof.
  intros a b c H. apply (pm_qle_wd_l (a * c) (c * a) (c * b)).
  - apply Qmult_comm.
  - apply (pm_qle_wd_r (b * c) (c * b)).
    + apply Qmult_comm.
    + exact H.
Qed.

(* Bridge from Id (nat) to Prop eq (the only channel that makes the *)
(* length premises Set-valued; proof-only) *)
Lemma pm_id_nat_eq : forall n m : nat, Id n m -> n = m.
Proof.
  intros n m H. case H. reflexivity.
Qed.

(* ============================================================ *)
(* Part 2. Pointwise evaluation face: coefficient-wise sign      *)
(* implies the eval sign (nonnegative at the left endpoint of    *)
(* [0,1] suffices).                                              *)
(* ============================================================ *)

(* Nonnegative coefficients imply eval >= 0 (given 0 <= x) *)
Theorem pm_eval_ge0 : forall p : list Q,
  (forall i : nat, QleT' 0 (pint_coeff p i)) ->
  forall x : Q, QleT' 0 x -> QleT' 0 (pint_eval p x).
Proof.
  induction p as [| a p' IH]; intros Hcoeff x Hx.
  - apply qleT'_refl.
  - cbn [pint_eval pint_coeff].
    apply (qleT'_plus_compat 0 a 0 (x * pint_eval p' x)).
    + specialize (Hcoeff 0%nat). cbn [pint_coeff] in Hcoeff. exact Hcoeff.
    + apply pm_mult_r0_le.
      * apply IH.
        -- intros i. specialize (Hcoeff (Datatypes.S i)).
           cbn [pint_coeff] in Hcoeff. exact Hcoeff.
        -- exact Hx.
      * exact Hx.
Qed.

(* Nonpositive coefficients (all <= 0) imply eval <= 0 (given 0 <= x) *)
Theorem pm_eval_le0 : forall p : list Q,
  (forall i : nat, QleT' (pint_coeff p i) 0) ->
  forall x : Q, QleT' 0 x -> QleT' (pint_eval p x) 0.
Proof.
  induction p as [| a p' IH]; intros Hcoeff x Hx.
  - apply qleT'_refl.
  - cbn [pint_eval pint_coeff].
    apply (qleT'_plus_compat a 0 (x * pint_eval p' x) 0).
    + specialize (Hcoeff 0%nat). cbn [pint_coeff] in Hcoeff. exact Hcoeff.
    + apply pm_mult_r0_le0.
      * apply IH.
        -- intros i. specialize (Hcoeff (Datatypes.S i)).
           cbn [pint_coeff] in Hcoeff. exact Hcoeff.
        -- exact Hx.
      * exact Hx.
Qed.

(* Main monotonicity result (pointwise face): coefficient-wise <= *)
(* implies eval p x <= eval q x for every 0 <= x.                 *)
(* No equal-length premise: four-branch induction under the       *)
(* out-of-range coefficient = 0 semantics (stronger than the      *)
(* phase-one equal-length version). *)
Theorem pm_pointwise_le_eval : forall p q : list Q,
  (forall i : nat, QleT' (pint_coeff p i) (pint_coeff q i)) ->
  forall x : Q, QleT' 0 x -> QleT' (pint_eval p x) (pint_eval q x).
Proof.
  induction p as [| a p' IH]; intros q Hcoeff x Hx.
  - destruct q as [| b q'].
    + apply qleT'_refl.
    + cbn [pint_eval pint_coeff].
      apply (qleT'_plus_compat 0 b 0 (x * pint_eval q' x)).
      * specialize (Hcoeff 0%nat). cbn [pint_coeff] in Hcoeff. exact Hcoeff.
      * apply pm_mult_r0_le.
        -- apply pm_eval_ge0.
           ++ intros i. specialize (Hcoeff (Datatypes.S i)).
              cbn [pint_coeff] in Hcoeff. exact Hcoeff.
           ++ exact Hx.
        -- exact Hx.
  - destruct q as [| b q'].
    + cbn [pint_eval pint_coeff].
      apply (qleT'_plus_compat a 0 (x * pint_eval p' x) 0).
      * specialize (Hcoeff 0%nat). cbn [pint_coeff] in Hcoeff. exact Hcoeff.
      * apply pm_mult_r0_le0.
        -- apply pm_eval_le0.
           ++ intros i. specialize (Hcoeff (Datatypes.S i)).
              cbn [pint_coeff] in Hcoeff. exact Hcoeff.
           ++ exact Hx.
        -- exact Hx.
    + cbn [pint_eval pint_coeff].
      apply (qleT'_plus_compat a b (x * pint_eval p' x) (x * pint_eval q' x)).
      * specialize (Hcoeff 0%nat). cbn [pint_coeff] in Hcoeff. exact Hcoeff.
      * apply pm_qleT'_comm_l.
        apply (pm_qleT'_mult_r (pint_eval p' x) (pint_eval q' x) x).
        -- apply IH.
           ++ intros i. specialize (Hcoeff (Datatypes.S i)).
              cbn [pint_coeff] in Hcoeff. exact Hcoeff.
           ++ exact Hx.
        -- exact Hx.
Qed.

(* ============================================================ *)
(* Part 3. Integral monotonicity (equal-length-free form):       *)
(* coefficient-wise <= implies integral p <= integral q          *)
(* ============================================================ *)

(* Monomial nonpositive: a <= 0 implies a/(k+1) <= 0 (mirror of *)
(* the phase-one pint_monomial_int_nonneg) *)
Lemma pm_monomial_int_nonpos : forall (a : Q) (k : nat),
  QleT' a 0 -> QleT' (pint_monomial_int a k) 0.
Proof.
  intros a k Ha. apply Qle_to_QleT'.
  unfold pint_monomial_int, Qdiv.
  apply (Qle_trans (a * (1 / (Z.of_nat (Datatypes.S k) # 1)))
                   (0 * (1 / (Z.of_nat (Datatypes.S k) # 1))) 0).
  - apply (Qmult_le_compat_r a 0).
    + apply QleT'_to_Qle. exact Ha.
    + apply Qlt_le_weak. apply QltT_to_Qlt. apply pint_invS_pos.
  - rewrite Qmult_0_l. apply Qle_refl.
Qed.

(* All coefficients <= 0 imply the shifted integral <= 0 (both *)
(* induction arms) *)
Lemma pm_integral_from_nonpos : forall (p : list Q) (k : nat),
  (forall i : nat, QleT' (pint_coeff p i) 0) ->
  QleT' (pint_integral_from p k) 0.
Proof.
  induction p as [| a p' IH]; intros k Hcoeff.
  - apply qleT'_refl.
  - cbn [pint_integral_from].
    apply (qleT'_plus_compat (pint_monomial_int a k) 0
                             (pint_integral_from p' (Datatypes.S k)) 0).
    + apply pm_monomial_int_nonpos.
      specialize (Hcoeff 0%nat). cbn [pint_coeff] in Hcoeff. exact Hcoeff.
    + apply IH.
      intros i. specialize (Hcoeff (Datatypes.S i)).
      cbn [pint_coeff] in Hcoeff. exact Hcoeff.
Qed.

(* Main integral monotonicity: coefficient-wise <= (no equal-length *)
(* premise, four-branch) implies the shifted integral <= *)
Lemma pm_integral_from_mono_gen : forall (p q : list Q) (k : nat),
  (forall i : nat, QleT' (pint_coeff p i) (pint_coeff q i)) ->
  QleT' (pint_integral_from p k) (pint_integral_from q k).
Proof.
  induction p as [| a p' IH]; intros q k Hcoeff.
  - destruct q as [| b q'].
    + apply qleT'_refl.
    + cbn [pint_integral_from pint_coeff].
      apply (qleT'_plus_compat 0 (pint_monomial_int b k)
                               0 (pint_integral_from q' (Datatypes.S k))).
      * apply pint_monomial_int_nonneg.
        specialize (Hcoeff 0%nat). cbn [pint_coeff] in Hcoeff. exact Hcoeff.
      * apply pint_integral_from_nonneg.
        intros i. specialize (Hcoeff (Datatypes.S i)).
        cbn [pint_coeff] in Hcoeff. exact Hcoeff.
  - destruct q as [| b q'].
    + cbn [pint_integral_from pint_coeff].
      apply (qleT'_plus_compat (pint_monomial_int a k) 0
                               (pint_integral_from p' (Datatypes.S k)) 0).
      * apply pm_monomial_int_nonpos.
        specialize (Hcoeff 0%nat). cbn [pint_coeff] in Hcoeff. exact Hcoeff.
      * apply pm_integral_from_nonpos.
        intros i. specialize (Hcoeff (Datatypes.S i)).
        cbn [pint_coeff] in Hcoeff. exact Hcoeff.
    + cbn [pint_integral_from pint_coeff].
      apply (qleT'_plus_compat (pint_monomial_int a k) (pint_monomial_int b k)
                             (pint_integral_from p' (Datatypes.S k))
                             (pint_integral_from q' (Datatypes.S k))).
      * apply Qle_to_QleT'.
        unfold pint_monomial_int, Qdiv.
        apply (Qmult_le_compat_r a b).
        -- apply QleT'_to_Qle.
           specialize (Hcoeff 0%nat). cbn [pint_coeff] in Hcoeff. exact Hcoeff.
        -- apply Qlt_le_weak. apply QltT_to_Qlt. apply pint_invS_pos.
      * apply IH.
        -- intros i. specialize (Hcoeff (Datatypes.S i)).
           cbn [pint_coeff] in Hcoeff. exact Hcoeff.
Qed.

(* Assembly at zero offset:                                           *)
(* [pm_pointwise_le main result] coefficient-wise <= implies          *)
(* pint_integral p <= pint_integral q *)
Theorem pm_pointwise_le_integral : forall p q : list Q,
  (forall i : nat, QleT' (pint_coeff p i) (pint_coeff q i)) ->
  QleT' (pint_integral p) (pint_integral q).
Proof.
  intros p q Hcoeff. unfold pint_integral.
  exact (pm_integral_from_mono_gen p q 0 Hcoeff).
Qed.


(* ============================================================ *)
(* Part 4. Strict positivity machinery (QltT face; witnesses    *)
(* carried by sigT, zero Prop)                                  *)
(* Honest boundary: pointwise positivity on a segment with      *)
(* arbitrary coefficients needs grid/Sturm machinery and stays  *)
(* beyond this phase's window.                                  *)
(* ============================================================ *)

(* Monomial strictly positive: 0 < a implies 0 < a/(k+1)          *)
(* (Qmult_lt_compat_r + Qmult_0_l to reshape the left side) *)
Lemma pm_monomial_int_pos : forall (a : Q) (k : nat),
  QltT 0 a -> QltT 0 (pint_monomial_int a k).
Proof.
  intros a k Ha. apply Qlt_to_QltT.
  unfold pint_monomial_int, Qdiv.
  assert (H0 : 0 * (1 / (Z.of_nat (Datatypes.S k) # 1))
               < a * (1 / (Z.of_nat (Datatypes.S k) # 1))).
  { apply (Qmult_lt_compat_r 0 a (1 / (Z.of_nat (Datatypes.S k) # 1))).
    - apply QltT_to_Qlt. apply pint_invS_pos.
    - apply QltT_to_Qlt. exact Ha. }
  rewrite Qmult_0_l in H0. exact H0.
Qed.

(* All coefficients strictly positive imply the shifted integral      *)
(* strictly positive (induction; for the empty list the premise has   *)
(* the uninhabited type QltT 0 0 and the case closes by the identity  *)
(* of that same type -- the premise assumption is exactly the         *)
(* conclusion type, no explosion). *)
Lemma pm_integral_from_pos_strict : forall (p : list Q) (k : nat),
  (forall i : nat, QltT 0 (pint_coeff p i)) ->
  QltT 0 (pint_integral_from p k).
Proof.
  induction p as [| a p' IH]; intros k Hcoeff.
  - cbn [pint_integral_from]. specialize (Hcoeff 0%nat).
    cbn [pint_coeff] in Hcoeff. exact Hcoeff.
  - cbn [pint_integral_from].
    apply Qlt_to_QltT. apply (Qplus_lt_compat
      (0) (pint_monomial_int a k)
      (0) (pint_integral_from p' (Datatypes.S k))).
    + apply QltT_to_Qlt. apply pm_monomial_int_pos.
      specialize (Hcoeff 0%nat). cbn [pint_coeff] in Hcoeff. exact Hcoeff.
    + apply QltT_to_Qlt. apply IH.
      intros i. specialize (Hcoeff (Datatypes.S i)).
      cbn [pint_coeff] in Hcoeff. exact Hcoeff.
Qed.

(* Assembly: all coefficients strictly positive imply the integral *)
(* of p strictly positive *)
Theorem pm_integral_pos_strict : forall p : list Q,
  (forall i : nat, QltT 0 (pint_coeff p i)) ->
  QltT 0 (pint_integral p).
Proof.
  intros p H. unfold pint_integral.
  exact (pm_integral_from_pos_strict p 0 H).
Qed.


(* Shifted-induction main result with a strict-positivity witness:   *)
(* all coefficients nonnegative + a sigT witness (some coefficient   *)
(* strictly positive) imply the shifted integral strictly positive.  *)
(* Three-way sigT index split (0: strict head; S i': tail induction; *)
(* empty list: the witness type is uninhabited, case dismissed). *)
Lemma pm_integral_from_pos : forall (p : list Q) (k : nat),
  (forall i : nat, QleT' 0 (pint_coeff p i)) ->
  sigT (fun i => QltT 0 (pint_coeff p i)) ->
  QltT 0 (pint_integral_from p k).
Proof.
  induction p as [| a p' IH]; intros k Hcoeff Hwit.
  - destruct Hwit as [i Hi].
    cbn [pint_integral_from]. cbn [pint_coeff] in Hi. exact Hi.
  - destruct Hwit as [i Hi]. destruct i as [| i].
    + (* strict head + nonnegative tail *)
      cbn [pint_coeff] in Hi. cbn [pint_integral_from].
      apply Qlt_to_QltT.
      apply (Qplus_lt_le_compat 0 (pint_monomial_int a k)
                               0 (pint_integral_from p' (Datatypes.S k))).
      * apply QltT_to_Qlt. apply pm_monomial_int_pos. exact Hi.
      * apply QleT'_to_Qle. apply pint_integral_from_nonneg.
        intros i'. specialize (Hcoeff (Datatypes.S i')).
        cbn [pint_coeff] in Hcoeff. exact Hcoeff.
    + (* nonnegative head + strictly positive tail: the Qplus_le_lt shape is *)
(* routed through a Qplus_comm rewrite chain down to Qplus_lt_le_compat *)
(* (the stdlib has no le-then-lt variant; the right-operand order there *)
(* is fixed) *)
      cbn [pint_coeff] in Hi. cbn [pint_integral_from].
      assert (Htail : QltT 0 (pint_integral_from p' (Datatypes.S k))).
      { apply IH.
        - intros i'. specialize (Hcoeff (Datatypes.S i')).
          cbn [pint_coeff] in Hcoeff. exact Hcoeff.
        - exact (existT (fun j => QltT 0 (pint_coeff p' j)) i Hi). }
      apply Qlt_to_QltT.
      rewrite <- (Qplus_0_l 0).
      rewrite (Qplus_comm (pint_monomial_int a k)
                          (pint_integral_from p' (Datatypes.S k))).
      apply (Qplus_lt_le_compat 0 (pint_integral_from p' (Datatypes.S k))
                               0 (pint_monomial_int a k)).
      * apply QltT_to_Qlt. exact Htail.
      * apply QleT'_to_Qle. apply pint_monomial_int_nonneg.
        specialize (Hcoeff 0%nat). cbn [pint_coeff] in Hcoeff. exact Hcoeff.
Qed.

(* Assembly: [pm_pointwise_pos main result] all coefficients            *)
(* nonnegative + some coefficient strictly positive (sigT witness)      *)
(* imply the integral of p strictly positive.                           *)
(* Together with the Part 4 strict result this forms the                *)
(* coefficient-level reachable face of the nonnegative + strictly       *)
(* positive somewhere decomposition; the Taylor truncation of the        *)
(* Beukers-candidate integrand (1 - t/2)^(-(n+1)) is of                 *)
(* all-positive-coefficient shape, so the strict result applies         *)
(* directly; the arbitrary-position witness is carried by the sigT      *)
(* face of this result. *)
Theorem pm_integral_pos : forall p : list Q,
  (forall i : nat, QleT' 0 (pint_coeff p i)) ->
  sigT (fun i => QltT 0 (pint_coeff p i)) ->
  QltT 0 (pint_integral p).
Proof.
  intros p Hcoeff Hwit. unfold pint_integral.
  exact (pm_integral_from_pos p 0 Hcoeff Hwit).
Qed.


(* ============================================================ *)
(* Part 5. The two linearity results (for the Beukers identity  *)
(* chain; phase-one linearity is used, not re-proved)           *)
(* ============================================================ *)

(* Scalar-multiplication monotonicity: 0 <= a and integral p <=       *)
(* integral q imply integral (a*p) <= integral (a*q)                  *)
(* (pint_integral_scale QeqT reshaping on both ends +                 *)
(* Qmult_le_compat_r) *)
Theorem pm_scale_mono : forall (a : Q) (p q : list Q),
  QleT' 0 a ->
  QleT' (pint_integral p) (pint_integral q) ->
  QleT' (pint_integral (pint_scale a p)) (pint_integral (pint_scale a q)).
Proof.
  intros a p q Ha Hipq.
  apply (pm_qle_wd_l (a * pint_integral p) (pint_integral (pint_scale a p))).
  - apply Qeq_sym. apply qeqT_imp_qeq. apply pint_integral_scale.
  - apply (pm_qle_wd_r (a * pint_integral q) (pint_integral (pint_scale a q))).
    + apply Qeq_sym. apply qeqT_imp_qeq. apply pint_integral_scale.
    + apply pm_qleT'_mult_l.
      * exact Hipq.
      * exact Ha.
Qed.

(* Addition monotonicity: add carries internal equal lengths (Id :    *)
(* Set face, p~r and q~s paired) + integral p <= integral q and       *)
(* integral r <= integral s imply integral (p+r) <= integral (q+s)    *)
(* (pint_integral_add QeqT reshaping on both ends +                   *)
(* qleT'_plus_compat) *)
Theorem pm_add_mono : forall p q r s : list Q,
  Id (length p) (length r) -> Id (length q) (length s) ->
  QleT' (pint_integral p) (pint_integral q) ->
  QleT' (pint_integral r) (pint_integral s) ->
  QleT' (pint_integral (pint_add p r)) (pint_integral (pint_add q s)).
Proof.
  intros p q r s Hpr Hqs Hipq Hirs.
  apply (pm_qle_wd_l (pint_integral p + pint_integral r)
                     (pint_integral (pint_add p r))).
  - apply Qeq_sym. apply qeqT_imp_qeq. apply pint_integral_add.
    apply pm_id_nat_eq. exact Hpr.
  - apply (pm_qle_wd_r (pint_integral q + pint_integral s)
                       (pint_integral (pint_add q s))).
    + apply Qeq_sym. apply qeqT_imp_qeq. apply pint_integral_add.
      apply pm_id_nat_eq. exact Hqs.
    + apply (qleT'_plus_compat (pint_integral p) (pint_integral q)
                             (pint_integral r) (pint_integral s)).
      * exact Hipq.
      * exact Hirs.
Qed.

(* ============================================================ *)
(* Extraction check + assumption audit trail (compile-time      *)
(* stdout; re-checked by the verification step).                *)
(* ============================================================ *)

Extraction "pintmono_extract.ml"
  pm_eval_ge0 pm_eval_le0 pm_pointwise_le_eval
  pm_pointwise_le_integral pm_integral_pos_strict pm_integral_pos
  pm_scale_mono pm_add_mono.

Print Assumptions pm_pointwise_le_eval.
Print Assumptions pm_pointwise_le_integral.
Print Assumptions pm_integral_pos_strict.
Print Assumptions pm_integral_pos.
Print Assumptions pm_scale_mono.
Print Assumptions pm_add_mono.
