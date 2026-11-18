(* Mission. formalization of the Pinsker-type transport layer (PNSKB):
   the Bishop-order (_B) combinator family over grouped-mass coordinates,
   the filter split identities (sum over the list equals sum over the
   filter plus sum over its complement, with pointwise sign ite
   elimination on both sides), the list-shaped Gibbs nonnegativity
   (Bishop form, case-free, closed by real_gibbs_inequality_eps plus
   real_le_closure_b), and the G1 identity layer
   pnt_abs_tv_decomp: sum(p+q+|p-q|) == 2 + 2*TV (real_eq, pure algebra,
   case-free); culminating in the G2 data-processing two-point transport
   piece and the pointwise kl decomposition identity (the G2 chain rule
   core). A signed-certificate conditional main-piece slot
   (pnt_pinsker_abs_of_signcert) is declared as a registered future slot
   and is not present as a statement in this module.
   Dependencies. the library pieces listed by the in-file Require face
   (S01_BaseRing .. S15_TailFEPUp chain; Stdlib QArith, Qring, Qabs,
   Qround, List, Bool, Arith, Lia, Setoid, Morphisms, Extraction).
   References. M. S. Pinsker, On the information stability of random
   variables (two-point Pinsker inequality KL >= 2*TV^2 in the
   convention of this development); Bishop-style constructive analysis
   for the order-theoretic fragment.
   Constructivity. statement face entirely at the Set layer; purely
   constructive; all proofs closed by Qed; axiom face empty (coqchk
   "Closed under the global context" throughout, Print Assumptions audit
   at end of file); zero Obj.magic on both extraction faces.
   Build. coqc -q -native-compiler no -Q <Live tree> ""
   UpReqPinskerTransport.v *)

Set Printing Width 500.
(* ============================================================ *)

From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import QArith.Qring.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround.
From Stdlib Require Import Extraction.
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
Require Import UpRealLeB.
Require Import UpReqTVAbsEps.

(* ---- 0. Pointwise Q-ring instance resolution (an independent sibling of
        the PinskerTwoPoint p2_ring_eq family: real_eq goals resolved to pointwise
        Q identities via ring; real_inv_pos/real_abs/real_log kept opaque as ring atoms). ---- *)
Ltac pnt_ring_eq :=
  apply real_eq_of_zero_diff; intro n0;
  repeat match goal with
         | [ x : Real |- _ ] => destruct x
         end;
  cbn [projT1 real_plus real_mult real_opp real_minus_r real_one real_zero
       real_list_sum real_of_nat] in *;
  apply qeq_imp_qeqT; ring.

(* ---- 1. Carrier definitions ---- *)
Definition pnt_two : Real := real_plus real_one real_one.
Definition pnt_diff (p q : Real) : Real := real_plus p (real_opp q).
Definition pnt_one_minus (p : Real) : Real := real_plus real_one (real_opp p).
Definition pnt_sq (p : Real) : Real := real_mult p p.

(* Two-point KL over grouped-mass coordinates; an independent sibling of
   PinskerTwoPoint.p2_kl2 -- interface contract: pnt_kl2 u v = p2_kl2 u v (verbatim isomorphic, registered). *)
Definition pnt_kl2 (p q : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (Hp1 : real_lt real_zero (pnt_one_minus p))
  (Hq1 : real_lt real_zero (pnt_one_minus q)) : Real :=
  real_plus (real_kl_term p q Hp Hq)
            (real_kl_term (pnt_one_minus p) (pnt_one_minus q) Hp1 Hq1).

(* abs total variation TV := half of the pointwise sum of |p s - q s| *)
Definition pnt_tv (X : Type) (l : list X) (p q : X -> Real) : Real :=
  real_mult tv9_half
    (real_list_sum X (fun s => real_abs (pnt_diff (p s) (q s))) l).

(* ---- 2. Bishop combinator family ---- *)

(* 2a. Reflexivity *)
Lemma pnt_le_b_refl : forall x : Real, real_le_b x x.
Proof.
  intros x eps Heps.
  exact (real_lt_plus_r_zero x eps Heps).
Qed.

Lemma pnt_mult_one_l : forall x : Real, real_eq (real_mult real_one x) x.
Proof. intro x. pnt_ring_eq. Qed.

Lemma pnt_half_double : forall e : Real,
  real_eq (real_plus (real_mult tv9_half e) (real_mult tv9_half e)) e.
Proof. intro e.
  exact (tv9_double_inv tv9_half e
           (real_inv_pos_correct (real_plus real_one real_one) tv9_two_pos)).
Qed.

(* 2b. Right-side real_eq transport *)
Lemma pnt_le_b_eq_r : forall x y z : Real,
  real_eq y z -> real_le_b x y -> real_le_b x z.
Proof.
  intros x y z Hyz Hxy eps Heps.
  apply (RealSetoid.real_lt_compat x x (real_plus y eps) (real_plus z eps)).
  - apply real_eq_refl.
  - apply (RealSetoid.real_eq_plus_compat y eps z eps Hyz (real_eq_refl eps)).
  - exact (Hxy eps Heps).
Qed.

(* 2c. Left-side real_eq transport *)
Lemma pnt_le_b_eq_l : forall x y z : Real,
  real_eq x z -> real_le_b x y -> real_le_b z y.
Proof.
  intros x y z Hxz Hxy eps Heps.
  exact (RealSetoid.real_lt_compat x z (real_plus y eps) (real_plus y eps)
           Hxz (real_eq_refl (real_plus y eps)) (Hxy eps Heps)).
Qed.

(* 2d. Transitivity (tv9_half half-quantity mechanism) *)
Lemma pnt_le_b_trans : forall x y z : Real,
  real_le_b x y -> real_le_b y z -> real_le_b x z.
Proof.
  intros x y z Hxy Hyz eps Heps.
  assert (Hh : real_lt real_zero (real_mult tv9_half eps))
    by exact (real_mult_pos_compat tv9_half eps tv9_half_pos Heps).
  assert (H1 : real_lt x (real_plus y (real_mult tv9_half eps)))
    by exact (Hxy _ Hh).
  assert (H2 : real_lt (real_plus y (real_mult tv9_half eps))
                       (real_plus (real_plus z (real_mult tv9_half eps))
                                  (real_mult tv9_half eps))).
  { apply (RealSetoid.real_lt_compat
             (real_plus (real_mult tv9_half eps) y)
             (real_plus y (real_mult tv9_half eps))
             (real_plus (real_mult tv9_half eps)
                (real_plus z (real_mult tv9_half eps)))
             (real_plus (real_plus z (real_mult tv9_half eps))
                (real_mult tv9_half eps))).
    - apply real_plus_comm.
    - apply (real_eq_trans
               (real_plus (real_mult tv9_half eps)
                          (real_plus z (real_mult tv9_half eps)))
               (real_plus (real_plus (real_mult tv9_half eps) z)
                          (real_mult tv9_half eps))
               (real_plus (real_plus z (real_mult tv9_half eps))
                          (real_mult tv9_half eps))).
      + exact (real_plus_assoc (real_mult tv9_half eps) z
                 (real_mult tv9_half eps)).
      + apply (RealSetoid.real_eq_plus_compat
                 (real_plus (real_mult tv9_half eps) z)
                 (real_mult tv9_half eps)
                 (real_plus z (real_mult tv9_half eps))
                 (real_mult tv9_half eps)
                 (real_plus_comm (real_mult tv9_half eps) z)
                 (real_eq_refl (real_mult tv9_half eps))).
    - exact (real_lt_plus_translate (real_mult tv9_half eps) y
               (real_plus z (real_mult tv9_half eps)) (Hyz _ Hh)). }
  apply (RealSetoid.real_lt_compat x x
           (real_plus (real_plus z (real_mult tv9_half eps))
                      (real_mult tv9_half eps))
           (real_plus z eps)).
  - apply real_eq_refl.
  - apply (real_eq_trans (real_plus (real_plus z (real_mult tv9_half eps))
                         (real_mult tv9_half eps))
             (real_plus z (real_plus (real_mult tv9_half eps)
                        (real_mult tv9_half eps)))
             (real_plus z eps)).
    + apply real_eq_sym. exact (real_plus_assoc z (real_mult tv9_half eps)
                                  (real_mult tv9_half eps)).
    + exact (RealSetoid.real_eq_plus_compat z
               (real_plus (real_mult tv9_half eps)
                  (real_mult tv9_half eps)) z eps
               (real_eq_refl z) (pnt_half_double eps)).
  - exact (real_lt_trans x (real_plus y (real_mult tv9_half eps))
             (real_plus (real_plus z (real_mult tv9_half eps))
                        (real_mult tv9_half eps)) H1 H2).
Qed.

(* 2e. Nonneg-term elimination: 0 <=_B c implies x <=_B y implies x <=_B y+c *)
Lemma pnt_le_b_add_r : forall x y c : Real,
  real_le_b real_zero c -> real_le_b x y -> real_le_b x (real_plus y c).
Proof.
  intros x y c Hc Hxy eps Heps.
  assert (Hce : real_lt real_zero (real_plus c eps)) by exact (Hc eps Heps).
  apply (RealSetoid.real_lt_compat x x
           (real_plus y (real_plus c eps)) (real_plus (real_plus y c) eps)).
  - apply real_eq_refl.
  - pnt_ring_eq.
  - exact (Hxy _ Hce).
Qed.

(* 2f. Nonneg pairwise addition: 0 <=_B a -> 0 <=_B b -> 0 <=_B (a+b) *)
Lemma pnt_le_b_plus_zero : forall a b : Real,
  real_le_b real_zero a -> real_le_b real_zero b ->
  real_le_b real_zero (real_plus a b).
Proof.
  intros a b Ha Hb eps Heps.
  exact (RealSetoid.real_lt_compat real_zero real_zero
           (real_plus a (real_plus b eps))
           (real_plus (real_plus a b) eps)
           (real_eq_refl real_zero)
           (real_plus_assoc a b eps)
           (Ha (real_plus b eps) (Hb eps Heps))).
Qed.

Lemma pnt_plus_half_shuffle : forall y y' e : Real,
  real_eq (real_plus (real_plus y (real_mult tv9_half e))
                     (real_plus y' (real_mult tv9_half e)))
          (real_plus (real_plus y y') e).
Proof.
  intros y y' e.
  apply (real_eq_trans
           (real_plus (real_plus y (real_mult tv9_half e))
                      (real_plus y' (real_mult tv9_half e)))
           (real_plus y (real_plus (real_mult tv9_half e)
                        (real_plus y' (real_mult tv9_half e))))
           (real_plus (real_plus y y') e)).
  - apply real_eq_sym.
    exact (real_plus_assoc y (real_mult tv9_half e)
             (real_plus y' (real_mult tv9_half e))).
  - apply (real_eq_trans
             (real_plus y (real_plus (real_mult tv9_half e)
                        (real_plus y' (real_mult tv9_half e))))
             (real_plus y (real_plus (real_mult tv9_half e)
                        (real_plus (real_mult tv9_half e) y')))
             (real_plus (real_plus y y') e)).
    + apply (RealSetoid.real_eq_plus_compat y
               (real_plus (real_mult tv9_half e)
                  (real_plus y' (real_mult tv9_half e)))
               y
               (real_plus (real_mult tv9_half e)
                  (real_plus (real_mult tv9_half e) y'))
               (real_eq_refl y)
               (RealSetoid.real_eq_plus_compat (real_mult tv9_half e)
                  (real_plus y' (real_mult tv9_half e))
                  (real_mult tv9_half e)
                  (real_plus (real_mult tv9_half e) y')
                  (real_eq_refl (real_mult tv9_half e))
                  (real_plus_comm y' (real_mult tv9_half e)))).
    + apply (real_eq_trans
               (real_plus y (real_plus (real_mult tv9_half e)
                          (real_plus (real_mult tv9_half e) y')))
               (real_plus y (real_plus (real_plus (real_mult tv9_half e)
                                  (real_mult tv9_half e)) y'))
               (real_plus (real_plus y y') e)).
      * exact (RealSetoid.real_eq_plus_compat y
                  (real_plus (real_mult tv9_half e)
                     (real_plus (real_mult tv9_half e) y'))
                  y
                  (real_plus (real_plus (real_mult tv9_half e)
                     (real_mult tv9_half e)) y')
                  (real_eq_refl y)
                  (real_plus_assoc (real_mult tv9_half e)
                     (real_mult tv9_half e) y')).
      * apply (real_eq_trans
                 (real_plus y (real_plus (real_plus (real_mult tv9_half e)
                                (real_mult tv9_half e)) y'))
                 (real_plus (real_plus y y')
                            (real_plus (real_mult tv9_half e)
                                       (real_mult tv9_half e)))
                 (real_plus (real_plus y y') e)).
        -- apply (real_eq_trans
                    (real_plus y (real_plus (real_plus (real_mult tv9_half e)
                                   (real_mult tv9_half e)) y'))
                    (real_plus y (real_plus y' (real_plus
                                   (real_mult tv9_half e)
                                   (real_mult tv9_half e))))
                    (real_plus (real_plus y y')
                               (real_plus (real_mult tv9_half e)
                                          (real_mult tv9_half e)))).
           ++ apply (RealSetoid.real_eq_plus_compat y
                       (real_plus (real_plus (real_mult tv9_half e)
                          (real_mult tv9_half e)) y')
                       y
                       (real_plus y' (real_plus (real_mult tv9_half e)
                          (real_mult tv9_half e)))
                       (real_eq_refl y)
                       (real_plus_comm (real_plus (real_mult tv9_half e)
                              (real_mult tv9_half e)) y')).
           ++ exact (real_plus_assoc y y'
                       (real_plus (real_mult tv9_half e)
                                  (real_mult tv9_half e))).
        -- exact (RealSetoid.real_eq_plus_compat (real_plus y y')
                    (real_plus (real_mult tv9_half e)
                               (real_mult tv9_half e))
                    (real_plus y y') e
                    (real_eq_refl (real_plus y y'))
                    (pnt_half_double e)).
Qed.

(* 2g. Bishop-order addition monotonicity *)
Lemma pnt_le_b_plus : forall x y x' y' : Real,
  real_le_b x y -> real_le_b x' y' ->
  real_le_b (real_plus x x') (real_plus y y').
Proof.
  intros x y x' y' Hxy Hxy' eps Heps.
  assert (Hh : real_lt real_zero (real_mult tv9_half eps))
    by exact (real_mult_pos_compat tv9_half eps tv9_half_pos Heps).
  apply (RealSetoid.real_lt_compat (real_plus x x') (real_plus x x')
           (real_plus (real_plus y (real_mult tv9_half eps))
                      (real_plus y' (real_mult tv9_half eps)))
           (real_plus (real_plus y y') eps)).
  - apply real_eq_refl.
  - exact (pnt_plus_half_shuffle y y' eps).
  - apply real_lt_plus_compat.
    + exact (Hxy _ Hh).
    + exact (Hxy' _ Hh).
Qed.

Lemma pnt_mult_plus_distr_r : forall a b c : Real,
  real_eq (real_mult (real_plus a b) c)
          (real_plus (real_mult a c) (real_mult b c)).
Proof. intros a b c. pnt_ring_eq. Qed.

(* ---- 6. Auxiliary: one-sided multiplication eq transport ---- *)
Lemma pnt_mul_l_eq : forall a b t : Real,
  real_eq a b -> real_eq (real_mult a t) (real_mult b t).
Proof.
  intros a b t Hab.
  exact (RealSetoid.real_eq_mult_compat a t b t Hab (real_eq_refl t)).
Qed.

Lemma pnt_mul_r_eq : forall a b t : Real,
  real_eq a b -> real_eq (real_mult t a) (real_mult t b).
Proof.
  intros a b t Hab.
  exact (RealSetoid.real_eq_mult_compat t a t b (real_eq_refl t) Hab).
Qed.

Lemma pnt_mult_inv_r : forall (c e : Real) (Hc : real_lt real_zero c),
  real_eq (real_mult c (real_mult e (real_inv_pos c Hc))) e.
Proof.
  intros c e Hc.
  apply (real_eq_trans (real_mult c (real_mult e (real_inv_pos c Hc)))
             (real_mult (real_mult c (real_inv_pos c Hc)) e) e).
  - apply (real_eq_trans (real_mult c (real_mult e (real_inv_pos c Hc)))
             (real_mult (real_mult c e) (real_inv_pos c Hc))
             (real_mult (real_mult c (real_inv_pos c Hc)) e)).
    + exact (real_mult_assoc c e (real_inv_pos c Hc)).
    + apply (real_eq_trans (real_mult (real_mult c e) (real_inv_pos c Hc))
               (real_mult (real_mult e c) (real_inv_pos c Hc))
               (real_mult (real_mult c (real_inv_pos c Hc)) e)).
      * apply (RealSetoid.real_eq_mult_compat (real_mult c e)
                 (real_inv_pos c Hc) (real_mult e c) (real_inv_pos c Hc)
                 (real_mult_comm c e) (real_eq_refl (real_inv_pos c Hc))).
      * apply (real_eq_trans (real_mult (real_mult e c) (real_inv_pos c Hc))
                 (real_mult e (real_mult c (real_inv_pos c Hc)))
                 (real_mult (real_mult c (real_inv_pos c Hc)) e)).
        -- apply real_eq_sym.
           exact (real_mult_assoc e c (real_inv_pos c Hc)).
        -- exact (real_mult_comm e (real_mult c (real_inv_pos c Hc))).
  - apply (real_eq_trans (real_mult (real_mult c (real_inv_pos c Hc)) e)
             (real_mult real_one e) e).
    + exact (RealSetoid.real_eq_mult_compat
                 (real_mult c (real_inv_pos c Hc)) e real_one e
                 (real_inv_pos_correct c Hc) (real_eq_refl e)).
    + exact (pnt_mult_one_l e).
Qed.


(* ---- 2g'. Variable-level rearrangement arsenal (pure Q after destruct, ring-safe; zero poison in instantiation) ---- *)
Lemma pnt_opp_plus_distr : forall x y : Real,
  real_eq (real_opp (real_plus x y)) (real_plus (real_opp x) (real_opp y)).
Proof. intros x y. pnt_ring_eq. Qed.

Lemma pnt_mult_plus_distr_l : forall p x y : Real,
  real_eq (real_plus (real_mult p x) (real_mult p y))
          (real_mult p (real_plus x y)).
Proof. intros p x y. pnt_ring_eq. Qed.

Lemma pnt_rearr_swap : forall a b c : Real,
  real_eq (real_mult a (real_mult b c)) (real_mult (real_mult a c) b).
Proof. intros a b c. pnt_ring_eq. Qed.

Lemma pnt_rearr_r1 : forall u v w x y z : Real,
  real_eq (real_mult (real_mult (real_mult u v) (real_mult w x))
                      (real_mult y z))
          (real_mult (real_mult u w)
                      (real_mult (real_mult x z) (real_mult y v))).
Proof. intros u v w x y z. pnt_ring_eq. Qed.

Lemma pnt_rearr_swap4 : forall a b c d : Real,
  real_eq (real_mult (real_mult a b) (real_mult c d))
          (real_mult (real_mult a c) (real_mult b d)).
Proof. intros a b c d. pnt_ring_eq. Qed.

Lemma pnt_rearr_sum4 : forall a b c d : Real,
  real_eq (real_plus (real_plus a b) (real_plus c d))
          (real_plus (real_plus b d) (real_plus a c)).
Proof. intros a b c d. pnt_ring_eq. Qed.

Lemma pnt_rearr_sum4b : forall a b c d : Real,
  real_eq (real_plus (real_plus a b) (real_plus c d))
          (real_plus (real_plus b c) (real_plus a d)).
Proof. intros a b c d. pnt_ring_eq. Qed.

Lemma pnt_rearr_e1 : forall t1 t2 t3 t4 : Real,
  real_eq (real_mult t1 t2) real_one ->
  real_eq (real_mult t3 t4) real_one ->
  real_eq (real_mult (real_mult t1 t2) (real_mult t3 t4)) real_one.
Proof.
  intros t1 t2 t3 t4 H1 H2.
  apply (real_eq_trans (real_mult (real_mult t1 t2) (real_mult t3 t4))
             (real_mult real_one (real_mult t3 t4)) real_one).
  - apply (RealSetoid.real_eq_mult_compat (real_mult t1 t2)
             (real_mult t3 t4) real_one (real_mult t3 t4)
             H1 (real_eq_refl (real_mult t3 t4))).
  - apply (real_eq_trans (real_mult real_one (real_mult t3 t4))
             (real_mult t3 t4) real_one).
    + exact (pnt_mult_one_l (real_mult t3 t4)).
    + exact H2.
Qed.

(* 2h. Strictly-positive left-factor multiplication Bishop monotonicity: 0<c and x <=_B y imply c*x <=_B c*y *)
Lemma pnt_le_b_mult_l : forall c x y : Real,
  real_lt real_zero c -> real_le_b x y ->
  real_le_b (real_mult c x) (real_mult c y).
Proof.
  intros c x y Hc Hxy eps Heps.
  assert (Hd : real_lt real_zero (real_mult eps (real_inv_pos c Hc)))
    by exact (real_mult_positive eps (real_inv_pos c Hc) Heps
                (real_inv_pos_pos c Hc)).
  assert (H1 : real_lt x (real_plus y (real_mult eps (real_inv_pos c Hc))))
    by exact (Hxy _ Hd).
  assert (H2 : real_lt (real_mult x c)
                 (real_mult (real_plus y (real_mult eps (real_inv_pos c Hc))) c))
    by exact (real_mult_lt_compat x
                (real_plus y (real_mult eps (real_inv_pos c Hc))) c H1 Hc).
  apply (RealSetoid.real_lt_compat (real_mult x c) (real_mult c x)
           (real_mult (real_plus y (real_mult eps (real_inv_pos c Hc))) c)
           (real_plus (real_mult c y) eps)).
  - exact (real_mult_comm x c).
  - apply (real_eq_trans (real_mult (real_plus y
                          (real_mult eps (real_inv_pos c Hc))) c)
             (real_plus (real_mult y c)
                        (real_mult (real_mult eps (real_inv_pos c Hc)) c))
             (real_plus (real_mult c y) eps)).
    + exact (pnt_mult_plus_distr_r y
               (real_mult eps (real_inv_pos c Hc)) c).
    + apply (RealSetoid.real_eq_plus_compat (real_mult y c)
               (real_mult (real_mult eps (real_inv_pos c Hc)) c)
               (real_mult c y) eps
               (real_mult_comm y c)
               (real_eq_trans (real_mult (real_mult eps (real_inv_pos c Hc)) c)
                              (real_mult c
                                 (real_mult eps (real_inv_pos c Hc)))
                              eps
                              (real_mult_comm (real_mult eps (real_inv_pos c Hc)) c)
                              (pnt_mult_inv_r c eps Hc))).
  - exact H2.
Qed.

(* 2i. Strictly-positive left-factor multiplication Bishop nonneg: 0<c and 0 <=_B g imply 0 <=_B c*g *)
Lemma pnt_mult_pos_le_b : forall c g : Real,
  real_lt real_zero c -> real_le_b real_zero g ->
  real_le_b real_zero (real_mult c g).
Proof.
  intros c g Hc Hg.
  apply (pnt_le_b_eq_l (real_mult c real_zero) (real_mult c g) real_zero).
  - pnt_ring_eq.
  - exact (pnt_le_b_mult_l c real_zero g Hc Hg).
Qed.

(* 2j. Pointwise real_eq lifted to list sums *)
Lemma pnt_list_sum_eq_ext : forall (X : Type) (f g : X -> Real) (l : list X),
  (forall s : X, real_eq (f s) (g s)) ->
  real_eq (real_list_sum X f l) (real_list_sum X g l).
Proof.
  intros X f g l Hpt. induction l as [| w rest IH].
  - pnt_ring_eq.
  - cbn [real_list_sum].
    apply (RealSetoid.real_eq_plus_compat (f w) (real_list_sum X f rest)
             (g w) (real_list_sum X g rest)).
    + exact (Hpt w).
    + exact IH.
Qed.

(* 2k. Pointwise nonnegativity lifted to Bishop-order list sums *)
Lemma pnt_list_sum_nonneg_b : forall (X : Type) (f : X -> Real) (l : list X),
  (forall s : X, real_le_b real_zero (f s)) ->
  real_le_b real_zero (real_list_sum X f l).
Proof.
  intros X f l Hpt. induction l as [| w rest IH].
  - cbn [real_list_sum]. apply pnt_le_b_refl.
  - cbn [real_list_sum].
    apply pnt_le_b_plus_zero.
    + exact (Hpt w).
    + exact IH.
Qed.

(* 2l. real_abs compatible with real_eq (Q-level q_abs_abs_triangle) *)
Lemma pnt_abs_compat : forall x y : Real,
  real_eq x y -> real_eq (real_abs x) (real_abs y).
Proof.
  intros x y Hxy.
  destruct x as [u Hu]. destruct y as [v Hv].
  unfold real_abs, real_eq. simpl.
  intros eps Heps.
  destruct (Hxy eps Heps) as [N HN].
  exists N.
  intros n Hn.
  apply Qlt_to_QltT.
  apply (Qle_lt_trans _ (Qabs (u n - v n)) _).
  - apply QleT'_to_Qle. apply q_abs_abs_triangle.
  - apply QltT_to_Qlt. exact (HN n Hn).
Qed.

(* 2m. Uniqueness of reciprocals: W*Z == 1 (W>0) implies Z == inv W *)
Lemma pnt_inv_uniq : forall (W Z : Real) (HW : real_lt real_zero W),
  real_eq (real_mult W Z) real_one -> real_eq Z (real_inv_pos W HW).
Proof.
  intros W Z HW H.
  apply (real_eq_trans Z (real_mult Z (real_mult W (real_inv_pos W HW)))
           (real_inv_pos W HW)).
  - apply (real_eq_trans Z (real_mult Z real_one)
             (real_mult Z (real_mult W (real_inv_pos W HW)))).
    + apply real_eq_sym. exact (real_mult_one Z).
    + apply (RealSetoid.real_eq_mult_compat Z real_one Z
               (real_mult W (real_inv_pos W HW)) (real_eq_refl Z)).
      apply real_eq_sym.
      exact (real_inv_pos_correct W HW).
  - apply (real_eq_trans (real_mult Z (real_mult W (real_inv_pos W HW)))
             (real_mult (real_mult Z W) (real_inv_pos W HW))
             (real_inv_pos W HW)).
    + exact (real_mult_assoc Z W (real_inv_pos W HW)).
    + apply (real_eq_trans (real_mult (real_mult Z W) (real_inv_pos W HW))
               (real_mult real_one (real_inv_pos W HW))
               (real_inv_pos W HW)).
      * apply (RealSetoid.real_eq_mult_compat (real_mult Z W)
                 (real_inv_pos W HW) real_one (real_inv_pos W HW)
                 (real_eq_trans (real_mult Z W) (real_mult W Z) real_one
                    (real_mult_comm Z W) H)
                 (real_eq_refl (real_inv_pos W HW))).
      * exact (pnt_mult_one_l (real_inv_pos W HW)).
Qed.

(* 2n. real_log compatible with real_eq (real_log_le_mono plus real_le_antisym, both directions) *)
Lemma pnt_log_compat : forall (x y : Real) (Hx : real_lt real_zero x)
  (Hy : real_lt real_zero y),
  real_eq x y -> real_eq (real_log x Hx) (real_log y Hy).
Proof.
  intros x y Hx Hy Hxy.
  apply real_le_antisym.
  - apply (real_log_le_mono x y Hx Hy).
    exact (RealSetoid.real_eq_le x y Hxy).
  - apply (real_log_le_mono y x Hy Hx).
    exact (RealSetoid.real_eq_le y x (real_eq_sym x y Hxy)).
Qed.

(* 2o. kl_term two-argument real_eq transport (certificate swap) *)
Lemma pnt_kl_term_transport : forall (u u' v v' : Real)
  (Hu : real_lt real_zero u) (Hv : real_lt real_zero v)
  (Hu' : real_lt real_zero u') (Hv' : real_lt real_zero v'),
  real_eq u u' -> real_eq v v' ->
  real_eq (real_kl_term u v Hu Hv) (real_kl_term u' v' Hu' Hv').
Proof.
  intros u u' v v' Hu Hv Hu' Hv' Huu' Hvv'.
  unfold real_kl_term.
  assert (Hinv : real_eq (real_inv_pos u Hu) (real_inv_pos u' Hu')).
  { apply (pnt_inv_uniq u' (real_inv_pos u Hu) Hu').
    apply (real_eq_trans (real_mult u' (real_inv_pos u Hu))
             (real_mult u (real_inv_pos u Hu)) real_one).
    - apply (RealSetoid.real_eq_mult_compat u' (real_inv_pos u Hu)
               u (real_inv_pos u Hu) (real_eq_sym u u' Huu')
               (real_eq_refl (real_inv_pos u Hu))).
    - exact (real_inv_pos_correct u Hu). }
  apply (RealSetoid.real_eq_mult_compat u
           (real_opp (real_log (real_mult v (real_inv_pos u Hu))
             (real_mult_positive v (real_inv_pos u Hu) Hv
                (real_inv_pos_pos u Hu))))
           u'
           (real_opp (real_log (real_mult v' (real_inv_pos u' Hu'))
             (real_mult_positive v' (real_inv_pos u' Hu') Hv'
                (real_inv_pos_pos u' Hu'))))).
  - exact Huu'.
  - apply (RealSetoid.real_eq_opp_compat).
    apply (pnt_log_compat (real_mult v (real_inv_pos u Hu))
            (real_mult v' (real_inv_pos u' Hu'))).
    + apply (RealSetoid.real_eq_mult_compat v (real_inv_pos u Hu) v'
               (real_inv_pos u' Hu') Hvv' Hinv).
Qed.

(* 2p. 1-a == b (from the a+b==1 certificate) *)
Lemma pnt_one_minus_eq : forall a b : Real,
  real_eq (real_plus a b) real_one -> real_eq (pnt_one_minus a) b.
Proof.
  intros a b Hab.
  apply (real_eq_trans (pnt_one_minus a)
           (real_plus (real_plus a b) (real_opp a)) b).
  - apply (RealSetoid.real_eq_plus_compat real_one (real_opp a)
             (real_plus a b) (real_opp a) (real_eq_sym _ _ Hab)
             (real_eq_refl (real_opp a))).
  - pnt_ring_eq.
Qed.

(* ---- 3. Filter split identity family ---- *)

(* 3a. Σ_l g == Σ_(filter f l) g + Σ_(filter negb∘f l) g *)
Lemma pnt_sum_filter_split : forall (X : Type) (g : X -> Real) (l : list X)
  (f : X -> bool),
  real_eq (real_list_sum X g l)
          (real_plus (real_list_sum X g (filter f l))
                     (real_list_sum X g (filter (fun x => negb (f x)) l))).
Proof.
  intros X g l f. induction l as [| w rest IH].
  - cbn [filter real_list_sum negb]. pnt_ring_eq.
  - cbn [filter real_list_sum]. destruct (f w); cbn [filter negb real_list_sum].
    + (* f w = true: LHS == (g w + rest-sum), RHS == ((g w + Frest) + Fcrest) *)
      apply (real_eq_trans
               (real_plus (g w) (real_list_sum X g rest))
               (real_plus (g w) (real_plus (real_list_sum X g (filter f rest)) (real_list_sum X g (filter (fun x => negb (f x)) rest))))
               (real_plus (real_plus (g w) (real_list_sum X g (filter f rest))) (real_list_sum X g (filter (fun x => negb (f x)) rest)))).
      * exact (RealSetoid.real_eq_plus_compat (g w) (real_list_sum X g rest)
                 (g w) (real_plus (real_list_sum X g (filter f rest)) (real_list_sum X g (filter (fun x => negb (f x)) rest))) (real_eq_refl (g w)) IH).
      * exact (real_plus_assoc (g w) (real_list_sum X g (filter f rest)) (real_list_sum X g (filter (fun x => negb (f x)) rest))).
    + (* f w = false: LHS == (g w + rest-sum), RHS == (Frest + (g w + Fcrest)) *)
      apply (real_eq_trans
               (real_plus (g w) (real_list_sum X g rest))
               (real_plus (g w) (real_plus (real_list_sum X g (filter f rest)) (real_list_sum X g (filter (fun x => negb (f x)) rest))))
               (real_plus (real_list_sum X g (filter f rest)) (real_plus (g w) (real_list_sum X g (filter (fun x => negb (f x)) rest))))).
      * exact (RealSetoid.real_eq_plus_compat (g w) (real_list_sum X g rest)
                 (g w) (real_plus (real_list_sum X g (filter f rest)) (real_list_sum X g (filter (fun x => negb (f x)) rest))) (real_eq_refl (g w)) IH).
      * apply (real_eq_trans (real_plus (g w) (real_plus (real_list_sum X g (filter f rest)) (real_list_sum X g (filter (fun x => negb (f x)) rest))))
                 (real_plus (real_plus (g w) (real_list_sum X g (filter f rest))) (real_list_sum X g (filter (fun x => negb (f x)) rest)))
                 (real_plus (real_list_sum X g (filter f rest)) (real_plus (g w) (real_list_sum X g (filter (fun x => negb (f x)) rest))))).
        -- exact (real_plus_assoc (g w) (real_list_sum X g (filter f rest)) (real_list_sum X g (filter (fun x => negb (f x)) rest))).
        -- apply (real_eq_trans (real_plus (real_plus (g w) (real_list_sum X g (filter f rest))) (real_list_sum X g (filter (fun x => negb (f x)) rest)))
                    (real_plus (real_plus (real_list_sum X g (filter f rest)) (g w)) (real_list_sum X g (filter (fun x => negb (f x)) rest)))
                    (real_plus (real_list_sum X g (filter f rest)) (real_plus (g w) (real_list_sum X g (filter (fun x => negb (f x)) rest))))).
          ++ apply (RealSetoid.real_eq_plus_compat (real_plus (g w) (real_list_sum X g (filter f rest)))
                      (real_list_sum X g (filter (fun x => negb (f x)) rest)) (real_plus (real_list_sum X g (filter f rest)) (g w)) (real_list_sum X g (filter (fun x => negb (f x)) rest))
                      (real_plus_comm (g w) (real_list_sum X g (filter f rest))) (real_eq_refl (real_list_sum X g (filter (fun x => negb (f x)) rest)))).
          ++ apply real_eq_sym.
             exact (real_plus_assoc (real_list_sum X g (filter f rest)) (g w) (real_list_sum X g (filter (fun x => negb (f x)) rest))).
Qed.

(* 3b. Pointwise sign-function ite elimination along the filter primary side *)
Lemma pnt_sum_filter_ite_true : forall (X : Type) (f : X -> bool)
  (g h : X -> Real) (l : list X),
  real_eq (real_list_sum X (fun s => if f s then g s else h s) (filter f l))
          (real_list_sum X g (filter f l)).
Proof.
  intros X f g h l. induction l as [| w rest IH].
  - cbn [filter real_list_sum]. pnt_ring_eq.
  - cbn [filter]. destruct (f w) eqn:Hfw; cbn [filter real_list_sum]; rewrite ?Hfw; cbn [negb real_list_sum].
    + apply (RealSetoid.real_eq_plus_compat (g w)
               (real_list_sum X (fun s => if f s then g s else h s)
                  (filter f rest))
               (g w) (real_list_sum X g (filter f rest))).
      * exact (real_eq_refl (g w)).
      * exact IH.
    + exact IH.
Qed.

(* 3c. Pointwise sign-function ite elimination along the filter complement side *)
Lemma pnt_sum_filter_ite_false : forall (X : Type) (f : X -> bool)
  (g h : X -> Real) (l : list X),
  real_eq (real_list_sum X (fun s => if f s then g s else h s)
             (filter (fun x => negb (f x)) l))
          (real_list_sum X h (filter (fun x => negb (f x)) l)).
Proof.
  intros X f g h l. induction l as [| w rest IH].
  - cbn [filter real_list_sum negb]. pnt_ring_eq.
  - cbn [filter]. destruct (f w) eqn:Hfw; cbn [filter negb real_list_sum]; rewrite ?Hfw; cbn [negb real_list_sum].
    + exact IH.
    + apply (RealSetoid.real_eq_plus_compat (h w)
               (real_list_sum X (fun s => if f s then g s else h s)
                  (filter (fun x => negb (f x)) rest))
               (h w) (real_list_sum X h (filter (fun x => negb (f x)) rest))).
      * exact (real_eq_refl (h w)).
      * exact IH.
Qed.

(* ---- 4. List-shaped Gibbs nonnegativity (Bishop form, case-free) ---- *)
(* Pointwise nonnegativity plus double normalization imply 0 <=_B the
   list sum of kl_term(r,t). Route: real_gibbs_inequality_eps (eps-family
   encoding of the order) plus real_le_closure_b (D := 1 completing lemma). *)
Lemma pnt_list_gibbs_b : forall (X : Type) (m : list X) (r t : X -> Real)
  (Hr : forall s : X, real_lt real_zero (r s))
  (Ht : forall s : X, real_lt real_zero (t s))
  (Hnr : real_eq (real_list_sum X r m) real_one)
  (Hnt : real_eq (real_list_sum X t m) real_one),
  real_le_b real_zero
    (real_list_sum X
       (fun s : X => real_kl_term (r s) (t s) (Hr s) (Ht s)) m).
Proof.
  intros X m r t Hr Ht Hnr Hnt.
  apply (real_le_closure_b real_zero
           (real_list_sum X
              (fun s : X => real_kl_term (r s) (t s) (Hr s) (Ht s)) m)
           real_one real_lt_zero_one).
  intros eps Heps.
  apply (RealSetoid.real_le_id_r real_zero
           (real_plus (real_list_sum X
                         (fun s : X => real_kl_term (r s) (t s) (Hr s) (Ht s)) m)
                      eps)
           (real_plus (real_list_sum X
                         (fun s : X => real_kl_term (r s) (t s) (Hr s) (Ht s)) m)
                      (real_mult real_one eps))).
  - apply (RealSetoid.real_eq_plus_compat
             (real_list_sum X
                (fun s : X => real_kl_term (r s) (t s) (Hr s) (Ht s)) m)
             eps
             (real_list_sum X
                (fun s : X => real_kl_term (r s) (t s) (Hr s) (Ht s)) m)
             (real_mult real_one eps)).
    + apply real_eq_refl.
    + pnt_ring_eq.
  - exact (real_gibbs_inequality_eps X m r t Hr Ht Hnr Hnt eps Heps).
Qed.

(* ---- 5. G1 identity layer: sum(p+q+|p-q|) == 2 + 2*TV ---- *)
(* Pure algebraic decomposition of the termwise sum: sum p + sum q == 2 (normalization); sum |p-q| == 2*TV (halving). *)
Lemma pnt_abs_tv_decomp : forall (X : Type) (l : list X) (p q : X -> Real)
  (Hnp : real_eq (real_list_sum X p l) real_one)
  (Hnq : real_eq (real_list_sum X q l) real_one),
  real_eq
    (real_list_sum X
       (fun s : X => real_plus (real_plus (p s) (q s))
                     (real_abs (pnt_diff (p s) (q s)))) l)
    (real_plus pnt_two (real_mult pnt_two (pnt_tv X l p q))).
Proof.
  intros X l p q Hnp Hnq.
  set (S := real_list_sum X
              (fun s : X => real_abs (pnt_diff (p s) (q s))) l).
  assert (Hsum3 : real_eq
    (real_list_sum X
       (fun s : X => real_plus (real_plus (p s) (q s))
                     (real_abs (pnt_diff (p s) (q s)))) l)
    (real_plus (real_plus (real_list_sum X p l) (real_list_sum X q l)) S)).
  { apply (real_eq_trans
             (real_list_sum X
                (fun s : X => real_plus (real_plus (p s) (q s))
                      (real_abs (pnt_diff (p s) (q s)))) l)
             (real_plus (real_list_sum X (fun s : X => real_plus (p s) (q s)) l)
                        S)
             (real_plus (real_plus (real_list_sum X p l)
                         (real_list_sum X q l)) S)).
    - apply (real_eq_trans
               (real_list_sum X
                  (fun s : X => real_plus (real_plus (p s) (q s))
                        (real_abs (pnt_diff (p s) (q s)))) l)
               (real_plus
                  (real_list_sum X (fun s : X => real_plus (p s) (q s)) l)
                  (real_list_sum X
                     (fun s : X => real_abs (pnt_diff (p s) (q s))) l))
               (real_plus (real_list_sum X (fun s : X => real_plus (p s) (q s)) l)
                          S)).
      + exact (real_list_sum_add X
                  (fun s : X => real_plus (p s) (q s))
                  (fun s : X => real_abs (pnt_diff (p s) (q s))) l).
      + apply real_eq_refl.
    - apply (RealSetoid.real_eq_plus_compat
               (real_list_sum X (fun s : X => real_plus (p s) (q s)) l) S
               (real_plus (real_list_sum X p l) (real_list_sum X q l)) S).
      + exact (real_list_sum_add X p q l).
      + apply real_eq_refl. }
  apply (real_eq_trans
           (real_list_sum X (fun s : X => real_plus (real_plus (p s) (q s)) (real_abs (pnt_diff (p s) (q s)))) l)
           (real_plus (real_plus (real_list_sum X p l) (real_list_sum X q l)) S)
           (real_plus pnt_two (real_mult pnt_two (pnt_tv X l p q)))).
  - exact Hsum3.
  - apply (RealSetoid.real_eq_plus_compat
             (real_plus (real_list_sum X p l) (real_list_sum X q l)) S
             (real_plus real_one real_one)
             (real_mult pnt_two (pnt_tv X l p q))).
    + apply (RealSetoid.real_eq_plus_compat (real_list_sum X p l)
               (real_list_sum X q l) real_one real_one Hnp Hnq).
    + apply (real_eq_trans S
               (real_mult (real_plus real_one real_one)
                          (real_mult tv9_half S))
               (real_mult pnt_two (pnt_tv X l p q))).
      * apply real_eq_sym.
        apply (real_eq_trans
                 (real_mult (real_plus real_one real_one)
                            (real_mult tv9_half S))
                 (real_mult real_one S) S).
      -- apply (real_eq_trans
                    (real_mult (real_plus real_one real_one)
                               (real_mult tv9_half S))
                    (real_mult (real_mult (real_plus real_one real_one)
                                 tv9_half) S)
                    (real_mult real_one S)).
            exact (real_mult_assoc (real_plus real_one real_one) tv9_half S).
         ++ exact (pnt_mul_l_eq
                      (real_mult (real_plus real_one real_one) tv9_half)
                      real_one S
                      (real_inv_pos_correct (real_plus real_one real_one)
                         tv9_two_pos)).
      -- exact (pnt_mult_one_l S).
      * apply real_eq_refl.
Qed.



(* ---- 7. Pointwise kl decomposition identity (G2 chain-rule core) ---- *)
(* kl(p,q) == a*kl(p/a, q/b) + (p/a)*kl(a,b) (all four points positive; multiplied-out form avoids division). *)
Lemma pnt_kl_pt_split : forall (p q a b : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (Ha : real_lt real_zero a) (Hb : real_lt real_zero b),
  real_eq (real_kl_term p q Hp Hq)
    (real_plus
       (real_mult a (real_kl_term
          (real_mult p (real_inv_pos a Ha))
          (real_mult q (real_inv_pos b Hb))
          (real_mult_positive p (real_inv_pos a Ha) Hp (real_inv_pos_pos a Ha))
          (real_mult_positive q (real_inv_pos b Hb) Hq (real_inv_pos_pos b Hb))))
       (real_mult (real_mult p (real_inv_pos a Ha))
                  (real_kl_term a b Ha Hb))).
Proof.
  intros p q a b Hp Hq Ha Hb.
  unfold real_kl_term.
  set (ivp := real_inv_pos p Hp).
  set (iva := real_inv_pos a Ha).
  set (ivb := real_inv_pos b Hb).
  set (HWc := real_mult_positive p iva Hp (real_inv_pos_pos a Ha)).
  set (HWc' := real_mult_positive q ivb Hq (real_inv_pos_pos b Hb)).
  set (ivW := real_inv_pos (real_mult p iva) HWc).
  set (LWp := real_opp (real_log (real_mult q ivp)
                 (real_mult_positive q ivp Hq (real_inv_pos_pos p Hp)))).
  set (LWx := real_opp (real_log (real_mult (real_mult q ivb) ivW)
                 (real_mult_positive (real_mult q ivb) ivW HWc'
                    (real_inv_pos_pos (real_mult p (real_inv_pos a Ha)) HWc)))).
  set (LWy := real_opp (real_log (real_mult b iva)
                 (real_mult_positive b iva Hb (real_inv_pos_pos a Ha)))).
  assert (Eia : real_eq (real_mult iva a) real_one).
  { apply (real_eq_trans (real_mult iva a) (real_mult a iva) real_one).
    - exact (real_mult_comm iva a).
    - exact (real_inv_pos_correct a Ha). }
  assert (E1 : real_eq (real_mult (real_mult p iva) (real_mult ivp a)) real_one).
  { apply (real_eq_trans (real_mult (real_mult p iva) (real_mult ivp a))
             (real_mult (real_mult p ivp) real_one) real_one).
    - apply (real_eq_trans (real_mult (real_mult p iva) (real_mult ivp a))
               (real_mult (real_mult p ivp) (real_mult iva a))
               (real_mult (real_mult p ivp) real_one)).
      + exact (pnt_rearr_swap4 p iva ivp a).
      + apply (RealSetoid.real_eq_mult_compat (real_mult p ivp)
                 (real_mult iva a) (real_mult p ivp) real_one
                 (real_eq_refl (real_mult p ivp)) Eia).
    - apply (real_eq_trans (real_mult (real_mult p ivp) real_one)
               (real_mult p ivp) real_one).
      + exact (real_mult_one (real_mult p ivp)).
      + exact (real_inv_pos_correct p Hp). }
  assert (D1 : real_eq ivW (real_mult ivp a))
    by exact (real_eq_sym (real_mult ivp a)
                (real_inv_pos (real_mult p iva) HWc)
                (pnt_inv_uniq (real_mult p iva) (real_mult ivp a) HWc E1)).
  (* log-argument identity: X*Y == Z *)
  (* log-argument identity: X*Y == Z *)
  assert (Harg : real_eq (real_mult (real_mult (real_mult q ivb) ivW) (real_mult b iva)) (real_mult q ivp)).
  { apply (real_eq_trans
             (real_mult (real_mult (real_mult q ivb) ivW) (real_mult b iva))
             (real_mult (real_mult (real_mult q ivb) (real_mult ivp a))
                        (real_mult b iva))
             (real_mult q ivp)).
    - apply (RealSetoid.real_eq_mult_compat
               (real_mult (real_mult q ivb) ivW) (real_mult b iva)
               (real_mult (real_mult q ivb) (real_mult ivp a))
               (real_mult b iva)
               (pnt_mul_r_eq ivW (real_mult ivp a) (real_mult q ivb) D1)
               (real_eq_refl (real_mult b iva))).
    - apply (real_eq_trans
               (real_mult (real_mult (real_mult q ivb) (real_mult ivp a))
                          (real_mult b iva))
               (real_mult (real_mult q ivp)
                          (real_mult (real_mult a iva) (real_mult b ivb)))
               (real_mult q ivp)).
      + exact (pnt_rearr_r1 q ivb ivp a b iva).
      + apply (real_eq_trans (real_mult (real_mult q ivp)
                                (real_mult (real_mult a iva) (real_mult b ivb)))
                   (real_mult (real_mult q ivp) real_one)
                   (real_mult q ivp)).
        * apply (pnt_mul_r_eq (real_mult (real_mult a iva)
                                     (real_mult b ivb)) real_one
                    (real_mult q ivp)
                    (pnt_rearr_e1 a iva b ivb (real_inv_pos_correct a Ha)
                       (real_inv_pos_correct b Hb))).
        * exact (real_mult_one (real_mult q ivp)). }
  (* HB: LWp == LWx + LWy (real_log_mult plus log compatibility plus opp distribution) *)
  assert (HB : real_eq LWp (real_plus LWx LWy)).
  { apply (real_eq_trans (real_opp (real_log (real_mult q ivp)
                        (real_mult_positive q ivp Hq (real_inv_pos_pos p Hp))))
             (real_opp (real_log (real_mult (real_mult (real_mult q ivb) ivW) (real_mult b iva)) (real_mult_positive (real_mult (real_mult q ivb) ivW) (real_mult b iva) (real_mult_positive (real_mult q ivb) ivW HWc' (real_inv_pos_pos (real_mult p (real_inv_pos a Ha)) HWc)) (real_mult_positive b iva Hb (real_inv_pos_pos a Ha)))))
             (real_plus LWx LWy)).
    - exact (RealSetoid.real_eq_opp_compat (real_log (real_mult q ivp)
                 (real_mult_positive q ivp Hq (real_inv_pos_pos p Hp)))
                 (real_log (real_mult (real_mult (real_mult q ivb) ivW) (real_mult b iva)) (real_mult_positive (real_mult (real_mult q ivb) ivW) (real_mult b iva) (real_mult_positive (real_mult q ivb) ivW HWc' (real_inv_pos_pos (real_mult p (real_inv_pos a Ha)) HWc)) (real_mult_positive b iva Hb (real_inv_pos_pos a Ha))))
                 (pnt_log_compat (real_mult q ivp)
                   (real_mult (real_mult (real_mult q ivb) ivW) (real_mult b iva))
                   (real_mult_positive q ivp Hq (real_inv_pos_pos p Hp))
                   (real_mult_positive (real_mult (real_mult q ivb) ivW) (real_mult b iva) (real_mult_positive (real_mult q ivb) ivW HWc' (real_inv_pos_pos (real_mult p (real_inv_pos a Ha)) HWc)) (real_mult_positive b iva Hb (real_inv_pos_pos a Ha)))
                   (real_eq_sym (real_mult (real_mult (real_mult q ivb) ivW) (real_mult b iva)) (real_mult q ivp) Harg))).
    - exact (real_eq_trans (real_opp (real_log (real_mult (real_mult (real_mult q ivb) ivW) (real_mult b iva)) (real_mult_positive (real_mult (real_mult q ivb) ivW) (real_mult b iva) (real_mult_positive (real_mult q ivb) ivW HWc' (real_inv_pos_pos (real_mult p (real_inv_pos a Ha)) HWc)) (real_mult_positive b iva Hb (real_inv_pos_pos a Ha)))))
               (real_opp (real_plus (real_log (real_mult (real_mult q ivb) ivW) (real_mult_positive (real_mult q ivb) ivW HWc' (real_inv_pos_pos (real_mult p (real_inv_pos a Ha)) HWc))) (real_log (real_mult b iva) (real_mult_positive b iva Hb (real_inv_pos_pos a Ha)))))
               (real_plus LWx LWy)
          (RealSetoid.real_eq_opp_compat (real_log (real_mult (real_mult (real_mult q ivb) ivW) (real_mult b iva)) (real_mult_positive (real_mult (real_mult q ivb) ivW) (real_mult b iva) (real_mult_positive (real_mult q ivb) ivW HWc' (real_inv_pos_pos (real_mult p (real_inv_pos a Ha)) HWc)) (real_mult_positive b iva Hb (real_inv_pos_pos a Ha)))) (real_plus (real_log (real_mult (real_mult q ivb) ivW) (real_mult_positive (real_mult q ivb) ivW HWc' (real_inv_pos_pos (real_mult p (real_inv_pos a Ha)) HWc))) (real_log (real_mult b iva) (real_mult_positive b iva Hb (real_inv_pos_pos a Ha))))
             (real_log_mult (real_mult (real_mult q ivb) ivW) (real_mult b iva)
                (real_mult_positive (real_mult q ivb) ivW HWc' (real_inv_pos_pos (real_mult p (real_inv_pos a Ha)) HWc)) (real_mult_positive b iva Hb (real_inv_pos_pos a Ha))))
          (pnt_opp_plus_distr (real_log (real_mult (real_mult q ivb) ivW) (real_mult_positive (real_mult q ivb) ivW HWc' (real_inv_pos_pos (real_mult p (real_inv_pos a Ha)) HWc))) (real_log (real_mult b iva) (real_mult_positive b iva Hb (real_inv_pos_pos a Ha))))). }
  (* Factor limbs: a*(W*LWx) == p*LWp and W*(a*LWy) == p*LWp *)
  assert (EaW : real_eq (real_mult a (real_mult p iva)) p).
  { apply (real_eq_trans (real_mult a (real_mult p iva))
             (real_mult (real_mult a iva) p) p).
    - exact (pnt_rearr_swap a p iva).
    - apply (real_eq_trans (real_mult (real_mult a iva) p)
               (real_mult real_one p) p).
      + exact (pnt_mul_l_eq (real_mult a iva) real_one p
                  (real_inv_pos_correct a Ha)).
      + exact (pnt_mult_one_l p). }
  assert (EA : real_eq (real_mult a (real_mult (real_mult p iva) LWx))
                       (real_mult p LWx)).
  { apply (real_eq_trans (real_mult a (real_mult (real_mult p iva) LWx))
             (real_mult (real_mult a (real_mult p iva)) LWx)
             (real_mult p LWx)).
    - exact (real_mult_assoc a (real_mult p iva) LWx).
    - exact (pnt_mul_l_eq (real_mult a (real_mult p iva)) p LWx EaW). }
  assert (EWa : real_eq (real_mult (real_mult p iva) a) p).
  { apply (real_eq_trans (real_mult (real_mult p iva) a)
             (real_mult p (real_mult iva a)) p).
    - exact (real_eq_sym (real_mult p (real_mult iva a))
               (real_mult (real_mult p iva) a) (real_mult_assoc p iva a)).
    - apply (real_eq_trans (real_mult p (real_mult iva a))
               (real_mult p real_one) p).
      + exact (pnt_mul_r_eq (real_mult iva a) real_one p Eia).
      + exact (real_mult_one p). }
  assert (EB : real_eq (real_mult (real_mult p iva) (real_mult a LWy))
                       (real_mult p LWy)).
  { apply (real_eq_trans (real_mult (real_mult p iva) (real_mult a LWy))
             (real_mult (real_mult (real_mult p iva) a) LWy)
             (real_mult p LWy)).
    - exact (real_mult_assoc (real_mult p iva) a LWy).
    - exact (pnt_mul_l_eq (real_mult (real_mult p iva) a) p LWy EWa). }
  apply (real_eq_sym
           (real_plus (real_mult a (real_mult (real_mult p iva) LWx))
                      (real_mult (real_mult p iva) (real_mult a LWy)))
           (real_mult p LWp)).
  apply (real_eq_trans
           (real_plus (real_mult a (real_mult (real_mult p iva) LWx))
                      (real_mult (real_mult p iva) (real_mult a LWy)))
           (real_plus (real_mult p LWx) (real_mult p LWy))
           (real_mult p LWp)).
  - apply (RealSetoid.real_eq_plus_compat
             (real_mult a (real_mult (real_mult p iva) LWx))
             (real_mult (real_mult p iva) (real_mult a LWy))
             (real_mult p LWx) (real_mult p LWy) EA EB).
  - apply (real_eq_trans (real_plus (real_mult p LWx) (real_mult p LWy))
             (real_mult p (real_plus LWx LWy))
             (real_mult p LWp)).
    + exact (pnt_mult_plus_distr_l p LWx LWy).
    + exact (pnt_mul_r_eq (real_plus LWx LWy) LWp p
               (real_eq_sym LWp (real_plus LWx LWy) HB)).
Qed.

(* ---- 8. Fiber-sum lifting (pointwise decomposition lifted to list sums, with scaled sums and coordinates) ---- *)
Lemma pnt_fiber_split_sum : forall (Y : Type) (m : list Y)
  (f g : Y -> Real)
  (Hf : forall s : Y, real_lt real_zero (f s))
  (Hg : forall s : Y, real_lt real_zero (g s))
  (a b : Real) (Ha : real_lt real_zero a) (Hb : real_lt real_zero b),
  real_eq
    (real_list_sum Y (fun s => real_kl_term (f s) (g s) (Hf s) (Hg s)) m)
    (real_plus
       (real_mult a (real_list_sum Y (fun s => real_kl_term
          (real_mult (f s) (real_inv_pos a Ha))
          (real_mult (g s) (real_inv_pos b Hb))
          (real_mult_positive (f s) (real_inv_pos a Ha) (Hf s)
             (real_inv_pos_pos a Ha))
          (real_mult_positive (g s) (real_inv_pos b Hb) (Hg s)
             (real_inv_pos_pos b Hb))) m))
       (real_mult (real_kl_term a b Ha Hb)
          (real_list_sum Y (fun s => real_mult (f s) (real_inv_pos a Ha)) m))).
Proof.
  intros Y m f g Hf Hg a b Ha Hb.
  set (KL' := fun s : Y => real_kl_term
     (real_mult (f s) (real_inv_pos a Ha))
     (real_mult (g s) (real_inv_pos b Hb))
     (real_mult_positive (f s) (real_inv_pos a Ha) (Hf s)
        (real_inv_pos_pos a Ha))
     (real_mult_positive (g s) (real_inv_pos b Hb) (Hg s)
        (real_inv_pos_pos b Hb))).
  set (PA := fun s : Y => real_mult (f s) (real_inv_pos a Ha)).
  assert (EC1 : real_eq (real_list_sum Y (fun s => real_mult a (KL' s)) m)
                        (real_mult a (real_list_sum Y KL' m))).
  { apply (real_eq_trans (real_list_sum Y (fun s => real_mult a (KL' s)) m)
             (real_list_sum Y (fun s => real_mult (KL' s) a) m)
             (real_mult a (real_list_sum Y KL' m))).
    - apply pnt_list_sum_eq_ext. intro s. exact (real_mult_comm a (KL' s)).
    - exact (real_list_sum_linear_r Y a KL' m). }
  assert (EC2 : real_eq
                  (real_list_sum Y (fun s => real_mult (PA s)
                                      (real_kl_term a b Ha Hb)) m)
                  (real_mult (real_kl_term a b Ha Hb) (real_list_sum Y PA m))).
  { exact (real_list_sum_linear_r Y (real_kl_term a b Ha Hb) PA m). }
  apply (real_eq_trans
           (real_list_sum Y (fun s => real_kl_term (f s) (g s) (Hf s) (Hg s)) m)
           (real_list_sum Y (fun s => real_plus
              (real_mult a (KL' s))
              (real_mult (PA s) (real_kl_term a b Ha Hb))) m)
           (real_plus (real_mult a (real_list_sum Y KL' m))
                      (real_mult (real_kl_term a b Ha Hb)
                                 (real_list_sum Y PA m)))).
  - apply pnt_list_sum_eq_ext. intro s.
    exact (pnt_kl_pt_split (f s) (g s) a b (Hf s) (Hg s) Ha Hb).
  - apply (real_eq_trans
             (real_list_sum Y (fun s => real_plus
                (real_mult a (KL' s))
                (real_mult (PA s) (real_kl_term a b Ha Hb))) m)
             (real_plus (real_list_sum Y (fun s => real_mult a (KL' s)) m)
                        (real_list_sum Y (fun s => real_mult (PA s)
                                            (real_kl_term a b Ha Hb)) m))
             (real_plus (real_mult a (real_list_sum Y KL' m))
                        (real_mult (real_kl_term a b Ha Hb)
                                   (real_list_sum Y PA m)))).
    + exact (real_list_sum_add Y (fun s => real_mult a (KL' s))
                (fun s => real_mult (PA s) (real_kl_term a b Ha Hb)) m).
    + apply (RealSetoid.real_eq_plus_compat
                (real_list_sum Y (fun s => real_mult a (KL' s)) m)
                (real_list_sum Y (fun s => real_mult (PA s)
                                    (real_kl_term a b Ha Hb)) m)
                (real_mult a (real_list_sum Y KL' m))
                (real_mult (real_kl_term a b Ha Hb) (real_list_sum Y PA m))
                EC1 EC2).
Qed.

(* ---- 9. G2 main piece: the data-processing two-point transport piece ---- *)
Theorem pnt_dp_two_point : forall (X : Type) (l : list X) (p q : X -> Real)
  (Hp : forall s : X, real_lt real_zero (p s))
  (Hq : forall s : X, real_lt real_zero (q s))
  (Hnp : real_eq (real_list_sum X p l) real_one)
  (Hnq : real_eq (real_list_sum X q l) real_one)
  (f : X -> bool)
  (HAp : real_lt real_zero (real_list_sum X p (filter f l)))
  (HAq : real_lt real_zero (real_list_sum X q (filter f l)))
  (HBp : real_lt real_zero
           (real_list_sum X p (filter (fun x => negb (f x)) l)))
  (HBq : real_lt real_zero
           (real_list_sum X q (filter (fun x => negb (f x)) l))),
  real_le_b
    (real_plus
       (real_kl_term (real_list_sum X p (filter f l))
                     (real_list_sum X q (filter f l)) HAp HAq)
       (real_kl_term (real_list_sum X p (filter (fun x => negb (f x)) l))
                     (real_list_sum X q (filter (fun x => negb (f x)) l))
                     HBp HBq))
    (real_list_sum X
       (fun s : X => real_kl_term (p s) (q s) (Hp s) (Hq s)) l).
Proof.
  intros X l p q Hp Hq Hnp Hnq f HAp HAq HBp HBq.
  set (A := real_list_sum X p (filter f l)) in *.
  set (B := real_list_sum X q (filter f l)) in *.
  set (Bp := real_list_sum X p (filter (fun x => negb (f x)) l)) in *.
  set (Bq := real_list_sum X q (filter (fun x => negb (f x)) l)) in *.
  (* Primary fiber (f side) conditional-distribution normalization *)
  assert (Hnormr : real_eq
    (real_list_sum X (fun s => real_mult (p s) (real_inv_pos A HAp))
       (filter f l)) real_one).
  { apply (real_eq_trans
             (real_list_sum X (fun s => real_mult (p s) (real_inv_pos A HAp))
                (filter f l))
             (real_mult (real_inv_pos A HAp) A) real_one).
    - exact (real_list_sum_linear_r X (real_inv_pos A HAp) p (filter f l)).
    - apply (real_eq_trans (real_mult (real_inv_pos A HAp) A)
               (real_mult A (real_inv_pos A HAp)) real_one).
      + exact (real_mult_comm (real_inv_pos A HAp) A).
      + exact (real_inv_pos_correct A HAp). }
  assert (Hnormt : real_eq
    (real_list_sum X (fun s => real_mult (q s) (real_inv_pos B HAq))
       (filter f l)) real_one).
  { apply (real_eq_trans
             (real_list_sum X (fun s => real_mult (q s) (real_inv_pos B HAq))
                (filter f l))
             (real_mult (real_inv_pos B HAq) B) real_one).
    - exact (real_list_sum_linear_r X (real_inv_pos B HAq) q (filter f l)).
    - apply (real_eq_trans (real_mult (real_inv_pos B HAq) B)
               (real_mult B (real_inv_pos B HAq)) real_one).
      + exact (real_mult_comm (real_inv_pos B HAq) B).
      + exact (real_inv_pos_correct B HAq). }
  (* Complement fiber (negb side) normalization *)
  assert (Hnormrc : real_eq
    (real_list_sum X (fun s => real_mult (p s) (real_inv_pos Bp HBp))
       (filter (fun x => negb (f x)) l)) real_one).
  { apply (real_eq_trans
             (real_list_sum X (fun s => real_mult (p s)
                                 (real_inv_pos Bp HBp))
                (filter (fun x => negb (f x)) l))
             (real_mult (real_inv_pos Bp HBp) Bp) real_one).
    - exact (real_list_sum_linear_r X (real_inv_pos Bp HBp) p
               (filter (fun x => negb (f x)) l)).
    - apply (real_eq_trans (real_mult (real_inv_pos Bp HBp) Bp)
               (real_mult Bp (real_inv_pos Bp HBp)) real_one).
      + exact (real_mult_comm (real_inv_pos Bp HBp) Bp).
      + exact (real_inv_pos_correct Bp HBp). }
  assert (Hnormtc : real_eq
    (real_list_sum X (fun s => real_mult (q s) (real_inv_pos Bq HBq))
       (filter (fun x => negb (f x)) l)) real_one).
  { apply (real_eq_trans
             (real_list_sum X (fun s => real_mult (q s)
                                 (real_inv_pos Bq HBq))
                (filter (fun x => negb (f x)) l))
             (real_mult (real_inv_pos Bq HBq) Bq) real_one).
    - exact (real_list_sum_linear_r X (real_inv_pos Bq HBq) q
               (filter (fun x => negb (f x)) l)).
    - apply (real_eq_trans (real_mult (real_inv_pos Bq HBq) Bq)
               (real_mult Bq (real_inv_pos Bq HBq)) real_one).
      + exact (real_mult_comm (real_inv_pos Bq HBq) Bq).
      + exact (real_inv_pos_correct Bq HBq). }
  (* Conditional Gibbs nonnegativity on both fibers (Bishop) *)
  assert (Gb : real_le_b real_zero
    (real_list_sum X (fun s => real_kl_term
       (real_mult (p s) (real_inv_pos A HAp))
       (real_mult (q s) (real_inv_pos B HAq))
       (real_mult_positive (p s) (real_inv_pos A HAp) (Hp s)
          (real_inv_pos_pos A HAp))
       (real_mult_positive (q s) (real_inv_pos B HAq) (Hq s)
          (real_inv_pos_pos B HAq))) (filter f l))).
  { exact (pnt_list_gibbs_b X (filter f l)
             (fun s => real_mult (p s) (real_inv_pos A HAp))
             (fun s => real_mult (q s) (real_inv_pos B HAq))
             (fun s => real_mult_positive (p s) (real_inv_pos A HAp) (Hp s)
                (real_inv_pos_pos A HAp))
             (fun s => real_mult_positive (q s) (real_inv_pos B HAq) (Hq s)
                (real_inv_pos_pos B HAq))
             Hnormr Hnormt). }
  assert (Gc : real_le_b real_zero
    (real_list_sum X (fun s => real_kl_term
       (real_mult (p s) (real_inv_pos Bp HBp))
       (real_mult (q s) (real_inv_pos Bq HBq))
       (real_mult_positive (p s) (real_inv_pos Bp HBp) (Hp s)
          (real_inv_pos_pos Bp HBp))
       (real_mult_positive (q s) (real_inv_pos Bq HBq) (Hq s)
          (real_inv_pos_pos Bq HBq))) (filter (fun x => negb (f x)) l))).
  { exact (pnt_list_gibbs_b X (filter (fun x => negb (f x)) l)
             (fun s => real_mult (p s) (real_inv_pos Bp HBp))
             (fun s => real_mult (q s) (real_inv_pos Bq HBq))
             (fun s => real_mult_positive (p s) (real_inv_pos Bp HBp) (Hp s)
                (real_inv_pos_pos Bp HBp))
             (fun s => real_mult_positive (q s) (real_inv_pos Bq HBq) (Hq s)
                (real_inv_pos_pos Bq HBq))
             Hnormrc Hnormtc). }
  (* Primary fiber decomposition identity: sum_F kl == A*G + kl(A,B) *)
  assert (FibF : real_eq
    (real_list_sum X (fun s => real_kl_term (p s) (q s) (Hp s) (Hq s))
       (filter f l))
    (real_plus (real_mult A (real_list_sum X (fun s => real_kl_term
                  (real_mult (p s) (real_inv_pos A HAp))
                  (real_mult (q s) (real_inv_pos B HAq))
                  (real_mult_positive (p s) (real_inv_pos A HAp) (Hp s)
                     (real_inv_pos_pos A HAp))
                  (real_mult_positive (q s) (real_inv_pos B HAq) (Hq s)
                     (real_inv_pos_pos B HAq))) (filter f l)))
               (real_kl_term A B HAp HAq))).
  { apply (real_eq_trans
             (real_list_sum X (fun s => real_kl_term (p s) (q s) (Hp s) (Hq s))
                (filter f l))
             (real_plus (real_mult A (real_list_sum X (fun s => real_kl_term
                          (real_mult (p s) (real_inv_pos A HAp))
                          (real_mult (q s) (real_inv_pos B HAq))
                          (real_mult_positive (p s) (real_inv_pos A HAp) (Hp s)
                             (real_inv_pos_pos A HAp))
                          (real_mult_positive (q s) (real_inv_pos B HAq) (Hq s)
                             (real_inv_pos_pos B HAq))) (filter f l)))
                        (real_mult (real_kl_term A B HAp HAq)
                           (real_list_sum X (fun s => real_mult (p s)
                              (real_inv_pos A HAp)) (filter f l))))
             (real_plus (real_mult A (real_list_sum X (fun s => real_kl_term
                          (real_mult (p s) (real_inv_pos A HAp))
                          (real_mult (q s) (real_inv_pos B HAq))
                          (real_mult_positive (p s) (real_inv_pos A HAp) (Hp s)
                             (real_inv_pos_pos A HAp))
                          (real_mult_positive (q s) (real_inv_pos B HAq) (Hq s)
                             (real_inv_pos_pos B HAq))) (filter f l)))
                        (real_kl_term A B HAp HAq))).
    - exact (pnt_fiber_split_sum X (filter f l) p q Hp Hq A B HAp HAq).
    - apply (RealSetoid.real_eq_plus_compat
               (real_mult A (real_list_sum X (fun s => real_kl_term
                  (real_mult (p s) (real_inv_pos A HAp))
                  (real_mult (q s) (real_inv_pos B HAq))
                  (real_mult_positive (p s) (real_inv_pos A HAp) (Hp s)
                     (real_inv_pos_pos A HAp))
                  (real_mult_positive (q s) (real_inv_pos B HAq) (Hq s)
                     (real_inv_pos_pos B HAq))) (filter f l)))
               (real_mult (real_kl_term A B HAp HAq)
                  (real_list_sum X (fun s => real_mult (p s)
                     (real_inv_pos A HAp)) (filter f l)))
               (real_mult A (real_list_sum X (fun s => real_kl_term
                  (real_mult (p s) (real_inv_pos A HAp))
                  (real_mult (q s) (real_inv_pos B HAq))
                  (real_mult_positive (p s) (real_inv_pos A HAp) (Hp s)
                     (real_inv_pos_pos A HAp))
                  (real_mult_positive (q s) (real_inv_pos B HAq) (Hq s)
                     (real_inv_pos_pos B HAq))) (filter f l)))
               (real_kl_term A B HAp HAq)
               (real_eq_refl (real_mult A (real_list_sum X
                  (fun s => real_kl_term
                     (real_mult (p s) (real_inv_pos A HAp))
                     (real_mult (q s) (real_inv_pos B HAq))
                     (real_mult_positive (p s) (real_inv_pos A HAp) (Hp s)
                        (real_inv_pos_pos A HAp))
                     (real_mult_positive (q s) (real_inv_pos B HAq) (Hq s)
                        (real_inv_pos_pos B HAq))) (filter f l))))
               (real_eq_trans (real_mult (real_kl_term A B HAp HAq)
                                 (real_list_sum X (fun s => real_mult (p s)
                                    (real_inv_pos A HAp)) (filter f l)))
                              (real_mult (real_kl_term A B HAp HAq) real_one)
                              (real_kl_term A B HAp HAq)
                              (pnt_mul_r_eq (real_list_sum X (fun s =>
                                 real_mult (p s) (real_inv_pos A HAp))
                                 (filter f l)) real_one
                                 (real_kl_term A B HAp HAq) Hnormr)
                              (real_mult_one (real_kl_term A B HAp HAq)))). }
  (* Complement fiber decomposition identity: sum_Fc kl == Bp*Gc + kl(Bp,Bq) *)
  assert (FibC : real_eq
    (real_list_sum X (fun s => real_kl_term (p s) (q s) (Hp s) (Hq s))
       (filter (fun x => negb (f x)) l))
    (real_plus (real_mult Bp (real_list_sum X (fun s => real_kl_term
                  (real_mult (p s) (real_inv_pos Bp HBp))
                  (real_mult (q s) (real_inv_pos Bq HBq))
                  (real_mult_positive (p s) (real_inv_pos Bp HBp) (Hp s)
                     (real_inv_pos_pos Bp HBp))
                  (real_mult_positive (q s) (real_inv_pos Bq HBq) (Hq s)
                     (real_inv_pos_pos Bq HBq))) (filter (fun x => negb (f x)) l)))
               (real_kl_term Bp Bq HBp HBq))).
  { apply (real_eq_trans
             (real_list_sum X (fun s => real_kl_term (p s) (q s) (Hp s) (Hq s))
                (filter (fun x => negb (f x)) l))
             (real_plus (real_mult Bp (real_list_sum X (fun s => real_kl_term
                          (real_mult (p s) (real_inv_pos Bp HBp))
                          (real_mult (q s) (real_inv_pos Bq HBq))
                          (real_mult_positive (p s) (real_inv_pos Bp HBp) (Hp s)
                             (real_inv_pos_pos Bp HBp))
                          (real_mult_positive (q s) (real_inv_pos Bq HBq) (Hq s)
                             (real_inv_pos_pos Bq HBq)))
                          (filter (fun x => negb (f x)) l)))
                        (real_mult (real_kl_term Bp Bq HBp HBq)
                           (real_list_sum X (fun s => real_mult (p s)
                              (real_inv_pos Bp HBp))
                              (filter (fun x => negb (f x)) l))))
             (real_plus (real_mult Bp (real_list_sum X (fun s => real_kl_term
                          (real_mult (p s) (real_inv_pos Bp HBp))
                          (real_mult (q s) (real_inv_pos Bq HBq))
                          (real_mult_positive (p s) (real_inv_pos Bp HBp) (Hp s)
                             (real_inv_pos_pos Bp HBp))
                          (real_mult_positive (q s) (real_inv_pos Bq HBq) (Hq s)
                             (real_inv_pos_pos Bq HBq)))
                          (filter (fun x => negb (f x)) l)))
                        (real_kl_term Bp Bq HBp HBq))).
    - exact (pnt_fiber_split_sum X (filter (fun x => negb (f x)) l) p q Hp Hq
                Bp Bq HBp HBq).
    - apply (RealSetoid.real_eq_plus_compat
               (real_mult Bp (real_list_sum X (fun s => real_kl_term
                  (real_mult (p s) (real_inv_pos Bp HBp))
                  (real_mult (q s) (real_inv_pos Bq HBq))
                  (real_mult_positive (p s) (real_inv_pos Bp HBp) (Hp s)
                     (real_inv_pos_pos Bp HBp))
                  (real_mult_positive (q s) (real_inv_pos Bq HBq) (Hq s)
                     (real_inv_pos_pos Bq HBq)))
                  (filter (fun x => negb (f x)) l)))
               (real_mult (real_kl_term Bp Bq HBp HBq)
                  (real_list_sum X (fun s => real_mult (p s)
                     (real_inv_pos Bp HBp)) (filter (fun x => negb (f x)) l)))
               (real_mult Bp (real_list_sum X (fun s => real_kl_term
                  (real_mult (p s) (real_inv_pos Bp HBp))
                  (real_mult (q s) (real_inv_pos Bq HBq))
                  (real_mult_positive (p s) (real_inv_pos Bp HBp) (Hp s)
                     (real_inv_pos_pos Bp HBp))
                  (real_mult_positive (q s) (real_inv_pos Bq HBq) (Hq s)
                     (real_inv_pos_pos Bq HBq)))
                  (filter (fun x => negb (f x)) l)))
               (real_kl_term Bp Bq HBp HBq)
               (real_eq_refl (real_mult Bp (real_list_sum X
                  (fun s => real_kl_term
                     (real_mult (p s) (real_inv_pos Bp HBp))
                     (real_mult (q s) (real_inv_pos Bq HBq))
                     (real_mult_positive (p s) (real_inv_pos Bp HBp) (Hp s)
                        (real_inv_pos_pos Bp HBp))
                     (real_mult_positive (q s) (real_inv_pos Bq HBq) (Hq s)
                        (real_inv_pos_pos Bq HBq)))
                     (filter (fun x => negb (f x)) l))))
               (real_eq_trans (real_mult (real_kl_term Bp Bq HBp HBq)
                                 (real_list_sum X (fun s => real_mult (p s)
                                    (real_inv_pos Bp HBp))
                                    (filter (fun x => negb (f x)) l)))
                              (real_mult (real_kl_term Bp Bq HBp HBq) real_one)
                              (real_kl_term Bp Bq HBp HBq)
                              (pnt_mul_r_eq (real_list_sum X (fun s =>
                                 real_mult (p s) (real_inv_pos Bp HBp))
                                 (filter (fun x => negb (f x)) l)) real_one
                                 (real_kl_term Bp Bq HBp HBq) Hnormrc)
                              (real_mult_one (real_kl_term Bp Bq HBp HBq)))). }
  (* Assembly: sum_l kl == (kl(A,B)+kl(Bp,Bq)) + (A*G + Bp*Gc); the latter factor is Bishop-nonnegative *)
  set (GF := real_list_sum X (fun s => real_kl_term
             (real_mult (p s) (real_inv_pos A HAp))
             (real_mult (q s) (real_inv_pos B HAq))
             (real_mult_positive (p s) (real_inv_pos A HAp) (Hp s)
                (real_inv_pos_pos A HAp))
             (real_mult_positive (q s) (real_inv_pos B HAq) (Hq s)
                (real_inv_pos_pos B HAq))) (filter f l)) in *.
  set (GC := real_list_sum X (fun s => real_kl_term
             (real_mult (p s) (real_inv_pos Bp HBp))
             (real_mult (q s) (real_inv_pos Bq HBq))
             (real_mult_positive (p s) (real_inv_pos Bp HBp) (Hp s)
                (real_inv_pos_pos Bp HBp))
             (real_mult_positive (q s) (real_inv_pos Bq HBq) (Hq s)
                (real_inv_pos_pos Bq HBq)))
             (filter (fun x => negb (f x)) l)) in *.
  assert (Hsplit : real_eq
    (real_list_sum X (fun s => real_kl_term (p s) (q s) (Hp s) (Hq s)) l)
    (real_plus (real_list_sum X (fun s => real_kl_term (p s) (q s) (Hp s)
                                   (Hq s)) (filter f l))
               (real_list_sum X (fun s => real_kl_term (p s) (q s) (Hp s)
                                   (Hq s))
                  (filter (fun x => negb (f x)) l)))).
  { exact (pnt_sum_filter_split X (fun s => real_kl_term (p s) (q s) (Hp s)
                                     (Hq s)) l f). }
  remember (real_plus (real_kl_term A B HAp HAq)
                      (real_kl_term Bp Bq HBp HBq)) as MID.
  remember (real_plus (real_mult A GF) (real_mult Bp GC)) as NN.
  assert (Htot : real_eq
    (real_list_sum X (fun s => real_kl_term (p s) (q s) (Hp s) (Hq s)) l)
    (real_plus MID NN)).
  { apply (real_eq_trans
             (real_list_sum X (fun s => real_kl_term (p s) (q s) (Hp s) (Hq s)) l)
             (real_plus (real_plus (real_mult A GF) (real_kl_term A B HAp HAq))
                        (real_plus (real_mult Bp GC)
                                   (real_kl_term Bp Bq HBp HBq)))
             (real_plus MID NN)).
    - apply (real_eq_trans
               (real_list_sum X (fun s => real_kl_term (p s) (q s) (Hp s) (Hq s)) l)
               (real_plus (real_list_sum X (fun s => real_kl_term (p s) (q s)
                                      (Hp s) (Hq s)) (filter f l))
                          (real_list_sum X (fun s => real_kl_term (p s) (q s)
                                      (Hp s) (Hq s))
                             (filter (fun x => negb (f x)) l)))
               (real_plus (real_plus (real_mult A GF)
                          (real_kl_term A B HAp HAq))
                          (real_plus (real_mult Bp GC)
                          (real_kl_term Bp Bq HBp HBq)))).
      + exact Hsplit.
      + apply (RealSetoid.real_eq_plus_compat
                 (real_list_sum X (fun s => real_kl_term (p s) (q s) (Hp s)
                                     (Hq s)) (filter f l))
                 (real_list_sum X (fun s => real_kl_term (p s) (q s) (Hp s)
                                     (Hq s))
                    (filter (fun x => negb (f x)) l))
                 (real_plus (real_mult A GF) (real_kl_term A B HAp HAq))
                 (real_plus (real_mult Bp GC) (real_kl_term Bp Bq HBp HBq))
                 FibF FibC).
    - rewrite HeqMID. rewrite HeqNN.
      exact (pnt_rearr_sum4 (real_mult A GF) (real_kl_term A B HAp HAq)
               (real_mult Bp GC) (real_kl_term Bp Bq HBp HBq)). }
  assert (Ngc : real_le_b real_zero NN).
  { rewrite HeqNN.
    exact (pnt_le_b_plus_zero (real_mult A GF) (real_mult Bp GC)
             (pnt_mult_pos_le_b A GF HAp Gb)
             (pnt_mult_pos_le_b Bp GC HBp Gc)). }
  apply (pnt_le_b_eq_r MID (real_plus MID NN)
           (real_list_sum X (fun s => real_kl_term (p s) (q s) (Hp s) (Hq s)) l)).
  - apply real_eq_sym. exact Htot.
  - apply (pnt_le_b_add_r MID MID NN Ngc (pnt_le_b_refl MID)).
Qed.

(* ---- 10. End-of-file assumption audit and extraction check ---- *)
Print Assumptions pnt_le_b_mult_l.
Print Assumptions pnt_inv_uniq.
Print Assumptions pnt_log_compat.
Print Assumptions pnt_kl_term_transport.
Print Assumptions pnt_list_gibbs_b.
Print Assumptions pnt_kl_pt_split.
Print Assumptions pnt_fiber_split_sum.
Print Assumptions pnt_abs_tv_decomp.
Print Assumptions pnt_dp_two_point.

Extraction "pnt_ex_probe.ml" pnt_dp_two_point pnt_abs_tv_decomp
  pnt_list_gibbs_b pnt_kl_pt_split.

Print Assumptions pnt_le_b_mult_l.
Print Assumptions pnt_inv_uniq.
Print Assumptions pnt_log_compat.
Print Assumptions pnt_kl_term_transport.
Print Assumptions pnt_list_gibbs_b.
Print Assumptions pnt_kl_pt_split.
Print Assumptions pnt_fiber_split_sum.
Print Assumptions pnt_abs_tv_decomp.
Print Assumptions pnt_dp_two_point.

Extraction "pnt_ex_probe.ml" pnt_dp_two_point pnt_abs_tv_decomp
  pnt_list_gibbs_b pnt_kl_pt_split.
