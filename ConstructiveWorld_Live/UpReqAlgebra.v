(* ConstructiveWorld-Set — algebraic law library for the real_eq-faced enhanced real interface. *)

(** * UpReqAlgebra: interface algebra laws for the Set-carrier real interface.

    Mission.  Algebraic laws for the enhanced setoid real interface of
      [S07_RealSetoidExpLog] (class [RealInterfaceEnhancedSetoid], instance
      [RealEnhancedReal]): additive laws, cancellation and uniqueness
      [req_plus_cancel_l]/[req_mult_cancel_r]/[req_plus_inv_unique], inverse
      and multiplication laws, order/absolute-value compatibility, subtraction
      via [req_minus a b := plus a (opp b)], and exponential identities.

    Dependencies.  Stdlib [QArith], [Arith], [Lia], [Setoid].  Requires the
      backbone [S01_BaseRing] .. [S15_TailFEPUp] of this development.
      Statements are fixed to the global instance [RealEnhancedReal]: the
      interface class in this tree is unparameterized, carrier [Real].

    References.  This development, the same-named baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements are carried by [Set]; relations are
      the global Set-carrier relations [real_eq]/[real_lt]/[real_le].  Honest
      interface limits: log injectivity [req_log_cancel] keeps its displayed
      side hypotheses (no injectivity field for [exp_neg]); mixed strict/weak
      monotonicity keeps explicit strict premises ([ReqStrictOrderBridge]).
      Statements extract with [Obj.magic] = 0; [coqchk] reports [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" UpReqAlgebra.v] compiles
      cleanly (exit 0); the first eight bytes of the artifact are
      [436f7121 00015ff4]. *)

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
Import RealInterfaceEnhancedMod.
(* The interface class in this tree is unparameterized; its carrier is the global Real. *)
Notation R := Real.

(* Subtraction on this face (transparently the same shape as Id-carrier minus). *)
Definition req_minus (a b : R) : R :=
  plus a (opp b).

(* ============================================================ *)
(* ReqAlgebraCore: the main real_eq-faced algebra block. *)
(* ============================================================ *)
Section ReqAlgebraCore.

(* ============ A. Alias layer: SimpleAlgebra (5 lemmas) ============ *)
(* These five are direct aliases of interface fields; on this face the fields are cited directly. *)

(* plus_zero_r: a + 0 == a (field alias). *)
Lemma req_plus_zero_r : forall a : R, real_eq (plus a zero) a.
Proof. intro a. apply plus_zero. Qed.

(* Left form (the fields give the right form; via commutativity). *)
Lemma req_plus_zero_l : forall a : R, real_eq (plus zero a) a.
Proof.
  intro a.
  exact (req_trans (plus zero a) (plus a zero) a (plus_comm zero a) (plus_zero a)).
Qed.

(* plus_opp_r: a + (-a) == 0 (field alias). *)
Lemma req_plus_opp_r : forall a : R, real_eq (plus a (opp a)) zero.
Proof. intro a. apply plus_opp. Qed.

(* Left form. *)
Lemma req_plus_opp_l : forall a : R, real_eq (plus (opp a) a) zero.
Proof.
  intro a.
  exact (req_trans (plus (opp a) a) (plus a (opp a)) zero
                   (plus_comm (opp a) a) (plus_opp a)).
Qed.

(* mult_one_r: a*1 == a (field alias). *)
Lemma req_mult_one_r : forall a : R, real_eq (mult a one) a.
Proof. intro a. apply mult_one. Qed.

(* Left form. *)
Lemma req_mult_one_l : forall a : R, real_eq (mult one a) a.
Proof.
  intro a.
  exact (req_trans (mult one a) (mult a one) a (mult_comm one a) (mult_one a)).
Qed.

(* Id mult_zero_r L27906 *)
Lemma req_mult_zero_r : forall a : R, real_eq (mult a zero) zero.
Proof. intro a. apply mult_zero. Qed.

(* Id mult_comm_rewrite L27910 *)
Lemma req_mult_comm_rewrite : forall a b : R, real_eq (mult a b) (mult b a).
Proof. intros a b. apply mult_comm. Qed.

(* ============ B. Cancellation engines + opp algebra ============ *)

(* Core engine: additive left cancellation (the seven-step chain replaces destruct-based equality elimination). *)
Lemma req_add_cancel_l : forall (u v w : R),
  real_eq (plus u v) (plus w v) -> real_eq u w.
Proof.
  intros u v w H.
  apply (req_trans u (plus u zero) w).
  - apply (req_sym (plus u zero) u). apply plus_zero.
  - apply (req_trans (plus u zero) (plus u (plus v (opp v))) w).
    + apply (req_plus_compat u u zero (plus v (opp v))).
      * apply req_refl.
      * apply (req_sym (plus v (opp v)) zero). apply plus_opp.
    + apply (req_trans (plus u (plus v (opp v))) (plus (plus u v) (opp v)) w).
      * apply plus_assoc.
      * apply (req_trans (plus (plus u v) (opp v)) (plus (plus w v) (opp v)) w).
        -- apply (req_plus_compat (plus u v) (plus w v) (opp v) (opp v) H).
           apply req_refl.
        -- apply (req_trans (plus (plus w v) (opp v)) (plus w (plus v (opp v))) w).
           ++ apply (req_sym (plus w (plus v (opp v))) (plus (plus w v) (opp v))).
              apply plus_assoc.
           ++ apply (req_trans (plus w (plus v (opp v))) (plus w zero) w).
              ** apply (req_plus_compat w w (plus v (opp v)) zero).
                 --- apply req_refl.
                 --- apply plus_opp.
              ** apply plus_zero.
Qed.

(* plus_inv_unique: b and c both right inverses of a imply b == c. *)
Lemma req_plus_inv_unique : forall a b c : R,
  real_eq (plus a b) zero -> real_eq (plus a c) zero -> real_eq b c.
Proof.
  intros a b c Hab Hac.
  assert (Hbc : real_eq (plus b a) (plus c a)).
  { exact (req_trans (plus b a) (plus a b) (plus c a)
           (plus_comm b a)
           (req_trans (plus a b) (plus a c) (plus c a)
                      (req_trans (plus a b) zero (plus a c) Hab
                                 (req_sym (plus a c) zero Hac))
                      (plus_comm a c))). }
  apply (req_trans b (plus b zero) c).
  - apply (req_sym (plus b zero) b). apply plus_zero.
  - apply (req_trans (plus b zero) (plus b (plus a (opp a))) c).
    + apply (req_plus_compat b b zero (plus a (opp a))).
      * apply req_refl.
      * apply (req_sym (plus a (opp a)) zero). apply plus_opp.
    + apply (req_trans (plus b (plus a (opp a))) (plus (plus b a) (opp a)) c).
      * apply plus_assoc.
      * apply (req_trans (plus (plus b a) (opp a)) (plus (plus c a) (opp a)) c).
        -- apply (req_plus_compat (plus b a) (plus c a) (opp a) (opp a) Hbc).
           apply req_refl.
        -- apply (req_trans (plus (plus c a) (opp a)) (plus c (plus a (opp a))) c).
           ++ apply (req_sym (plus c (plus a (opp a))) (plus (plus c a) (opp a))).
              apply plus_assoc.
           ++ apply (req_trans (plus c (plus a (opp a))) (plus c zero) c).
              ** apply (req_plus_compat c c (plus a (opp a)) zero).
                 --- apply req_refl.
                 --- apply plus_opp.
              ** apply plus_zero.
Qed.

(* double_neg: -(-a) == a. *)
Lemma req_double_neg : forall a : R, real_eq (opp (opp a)) a.
Proof.
  intro a.
  apply (req_add_cancel_l (opp (opp a)) (opp a) a).
  apply (req_trans (plus (opp (opp a)) (opp a)) zero (plus a (opp a))).
  - apply (req_trans (plus (opp (opp a)) (opp a)) (plus (opp a) (opp (opp a))) zero).
    + apply plus_comm.
    + apply plus_opp.
  - apply (req_sym (plus a (opp a)) zero). apply plus_opp.
Qed.

(* opp_plus: -(a + b) == (-a) + (-b). *)
Lemma req_opp_plus : forall a b : R, real_eq (opp (plus a b)) (plus (opp a) (opp b)).
Proof.
  intros a b.
  apply (req_add_cancel_l (opp (plus a b)) (plus a b) (plus (opp a) (opp b))).
  apply (req_trans (plus (opp (plus a b)) (plus a b)) zero
                   (plus (plus (opp a) (opp b)) (plus a b))).
  - apply (req_trans (plus (opp (plus a b)) (plus a b))
                     (plus (plus a b) (opp (plus a b))) zero).
    + apply plus_comm.
    + apply plus_opp.
  - apply (req_sym (plus (plus (opp a) (opp b)) (plus a b)) zero).
    apply (req_trans (plus (plus (opp a) (opp b)) (plus a b))
                     (plus (opp a) (plus (opp b) (plus a b)))
                     zero).
    + apply (req_sym (plus (opp a) (plus (opp b) (plus a b)))
                     (plus (plus (opp a) (opp b)) (plus a b))).
      apply plus_assoc.
    + apply (req_trans (plus (opp a) (plus (opp b) (plus a b)))
                       (plus (opp a) (plus (plus (opp b) a) b))
                       zero).
      * apply (req_plus_compat (opp a) (opp a) (plus (opp b) (plus a b))
                               (plus (plus (opp b) a) b)).
        -- apply req_refl.
        -- apply plus_assoc.
      * apply (req_trans (plus (opp a) (plus (plus (opp b) a) b))
                         (plus (opp a) (plus (plus a (opp b)) b))
                         zero).
        -- apply (req_plus_compat (opp a) (opp a)
                                  (plus (plus (opp b) a) b) (plus (plus a (opp b)) b)).
           ++ apply req_refl.
           ++ apply (req_plus_compat (plus (opp b) a) (plus a (opp b)) b b).
              ** apply plus_comm.
              ** apply req_refl.
        -- apply (req_trans (plus (opp a) (plus (plus a (opp b)) b))
                            (plus (plus (opp a) a) (plus (opp b) b))
                            zero).
           ++ apply (req_trans (plus (opp a) (plus (plus a (opp b)) b))
                               (plus (opp a) (plus a (plus (opp b) b)))
                               (plus (plus (opp a) a) (plus (opp b) b))).
              ** apply (req_plus_compat (opp a) (opp a)
                                        (plus (plus a (opp b)) b) (plus a (plus (opp b) b))).
                 --- apply req_refl.
                 --- apply (req_sym (plus a (plus (opp b) b))
                                    (plus (plus a (opp b)) b)). apply plus_assoc.
              ** apply plus_assoc.
           ++ apply (req_trans (plus (plus (opp a) a) (plus (opp b) b)) (plus zero zero) zero).
              ** apply (req_plus_compat (plus (opp a) a) zero (plus (opp b) b) zero).
                 --- apply (req_trans (plus (opp a) a) (plus a (opp a)) zero).
                     +++ apply plus_comm.
                     +++ apply plus_opp.
                 --- apply (req_trans (plus (opp b) b) (plus b (opp b)) zero).
                     +++ apply plus_comm.
                     +++ apply plus_opp.
              ** apply plus_zero.
Qed.

(* opp_mult_l: a*(-b) == -(a*b). *)
Lemma req_opp_mult_l : forall a b : R, real_eq (mult a (opp b)) (opp (mult a b)).
Proof.
  intros a b.
  apply (req_add_cancel_l (mult a (opp b)) (mult a b) (opp (mult a b))).
  apply (req_trans (plus (mult a (opp b)) (mult a b)) zero
                   (plus (opp (mult a b)) (mult a b))).
  - apply (req_trans (plus (mult a (opp b)) (mult a b))
                     (plus (mult a b) (mult a (opp b))) zero).
    + apply plus_comm.
    + apply (req_trans (plus (mult a b) (mult a (opp b))) (mult a (plus b (opp b))) zero).
      * apply (req_sym (mult a (plus b (opp b))) (plus (mult a b) (mult a (opp b)))).
        apply distrib.
      * apply (req_trans (mult a (plus b (opp b))) (mult a zero) zero).
        -- apply (req_mult_compat a a (plus b (opp b)) zero).
           ++ apply req_refl.
           ++ apply plus_opp.
        -- apply mult_zero.
  - apply (req_sym (plus (opp (mult a b)) (mult a b)) zero).
    apply (req_trans (plus (opp (mult a b)) (mult a b))
                     (plus (mult a b) (opp (mult a b))) zero).
    + apply plus_comm.
    + apply plus_opp.
Qed.

(* opp_mult_r: (-a)*b == -(a*b), via commutativity. *)
Lemma req_opp_mult_r : forall a b : R, real_eq (mult (opp a) b) (opp (mult a b)).
Proof.
  intros a b.
  apply (req_trans (mult (opp a) b) (mult b (opp a)) (opp (mult a b))).
  - apply mult_comm.
  - apply (req_trans (mult b (opp a)) (opp (mult b a)) (opp (mult a b))).
    + apply req_opp_mult_l.
    + apply (req_opp_compat (mult b a) (mult a b)). apply mult_comm.
Qed.

(* ============ C. Multiplication cluster ============ *)

(* mult_plus_distr_r: right distributivity. *)
Lemma req_mult_plus_distr_r : forall a b c : R,
  real_eq (mult (plus a b) c) (plus (mult a c) (mult b c)).
Proof.
  intros a b c.
  apply (req_trans (mult (plus a b) c) (mult c (plus a b))
                   (plus (mult a c) (mult b c))).
  - apply mult_comm.
  - apply (req_trans (mult c (plus a b)) (plus (mult c a) (mult c b))
                     (plus (mult a c) (mult b c))).
    + apply distrib.
    + apply (req_plus_compat (mult c a) (mult a c) (mult c b) (mult b c)
                             (mult_comm c a) (mult_comm c b)).
Qed.

(* Id two_mult L426：2·a == a + a *)
Lemma req_two_mult : forall a : R, real_eq (mult (plus one one) a) (plus a a).
Proof.
  intro a.
  apply (req_trans (mult (plus one one) a) (mult a (plus one one)) (plus a a)).
  - apply mult_comm.
  - apply (req_trans (mult a (plus one one)) (plus (mult a one) (mult a one))
                     (plus a a)).
    + apply distrib.
    + apply (req_plus_compat (mult a one) a (mult a one) a
                             (mult_one a) (mult_one a)).
Qed.

(* one_neq_zero: [one <> zero] at the Set carrier, via the field [lt_id_r]. *)
Lemma req_one_neq_zero : Not (real_eq one zero).
Proof.
  intro H.
  apply (lt_irrefl zero).
  exact (lt_id_r zero one zero H one_pos).
Qed.

(* Id two_pos L489 *)
Lemma req_two_pos : real_lt zero (plus one one).
Proof. exact (plus_positive one one one_pos one_pos). Qed.

(* half_pos: positivity of the half (eps/2 > 0). *)
Lemma req_half_pos : forall a : R, real_lt zero a ->
  real_lt zero (mult (inv_pos (plus one one) (plus_positive one one one_pos one_pos)) a).
Proof.
  intros a Ha.
  apply mult_positive.
  - apply inv_pos_pos.
  - exact Ha.
Qed.

(* half_twice: inv2*a + inv2*a == a, with the witness 2 > 0 explicit. *)
Lemma req_half_twice : forall (a : R) (H2 : real_lt zero (plus one one)),
  real_eq (plus (mult (inv_pos (plus one one) H2) a)
            (mult (inv_pos (plus one one) H2) a)) a.
Proof.
  intros a H2.
  apply (req_trans (plus (mult (inv_pos (plus one one) H2) a)
                         (mult (inv_pos (plus one one) H2) a))
                   (mult (plus one one) (mult (inv_pos (plus one one) H2) a)) a).
  - apply (req_sym (mult (plus one one) (mult (inv_pos (plus one one) H2) a))
                   (plus (mult (inv_pos (plus one one) H2) a)
                         (mult (inv_pos (plus one one) H2) a))).
    apply req_two_mult.
  - apply (req_trans (mult (plus one one) (mult (inv_pos (plus one one) H2) a))
                     (mult (mult (plus one one) (inv_pos (plus one one) H2)) a)
                     a).
    + apply mult_assoc.
    + exact (req_trans (mult (mult (plus one one) (inv_pos (plus one one) H2)) a)
                       (mult one a) a
                       (req_mult_compat (mult (plus one one) (inv_pos (plus one one) H2)) one
                                        a a
                                        (inv_pos_correct (plus one one) H2) (req_refl a))
                       (req_mult_one_l a)).
Qed.

(* Id plus_swap_mid L520：(a+b)+(c+d) == (a+c)+(b+d) *)
Lemma req_plus_swap_mid : forall a b c d : R,
  real_eq (plus (plus a b) (plus c d)) (plus (plus a c) (plus b d)).
Proof.
  intros a b c d.
  apply (req_trans (plus (plus a b) (plus c d)) (plus a (plus b (plus c d)))
                   (plus (plus a c) (plus b d))).
  - apply (req_sym (plus a (plus b (plus c d))) (plus (plus a b) (plus c d))).
    apply plus_assoc.
  - apply (req_trans (plus a (plus b (plus c d))) (plus a (plus (plus b c) d))
                     (plus (plus a c) (plus b d))).
    + apply (req_plus_compat a a (plus b (plus c d)) (plus (plus b c) d)
                             (req_refl a) (plus_assoc b c d)).
    + apply (req_trans (plus a (plus (plus b c) d)) (plus a (plus (plus c b) d))
                       (plus (plus a c) (plus b d))).
      * apply (req_plus_compat a a (plus (plus b c) d) (plus (plus c b) d)
                               (req_refl a)
                               (req_plus_compat (plus b c) (plus c b) d d
                                                (plus_comm b c) (req_refl d))).
      * apply (req_trans (plus a (plus (plus c b) d)) (plus a (plus c (plus b d)))
                         (plus (plus a c) (plus b d))).
        -- apply (req_plus_compat a a (plus (plus c b) d) (plus c (plus b d))
                                  (req_refl a)
                                  (req_sym (plus c (plus b d)) (plus (plus c b) d)
                                           (plus_assoc c b d))).
        -- apply plus_assoc.
Qed.

(* Helper: (A + X) + (-A) == X (completion engine for product/error decompositions). *)
Lemma req_plus_cancel : forall a x : R, real_eq (plus (plus a x) (opp a)) x.
Proof.
  intros a x.
  apply (req_trans (plus (plus a x) (opp a)) (plus a (plus x (opp a))) x).
  - apply (req_sym (plus a (plus x (opp a))) (plus (plus a x) (opp a))).
    apply plus_assoc.
  - apply (req_trans (plus a (plus x (opp a))) (plus a (plus (opp a) x)) x).
    + apply (req_plus_compat a a (plus x (opp a)) (plus (opp a) x)
                             (req_refl a) (plus_comm x (opp a))).
    + apply (req_trans (plus a (plus (opp a) x)) (plus (plus a (opp a)) x) x).
      * apply plus_assoc.
      * apply (req_trans (plus (plus a (opp a)) x) (plus zero x) x).
        -- apply (req_plus_compat (plus a (opp a)) zero x x
                                  (plus_opp a) (req_refl x)).
        -- apply (req_trans (plus zero x) (plus x zero) x
                            (plus_comm zero x) (plus_zero x)).
Qed.

(* Id plus_cancel_zero L995：a + b == a ⟹ b == 0 *)
Lemma req_plus_cancel_zero : forall a b : R, real_eq (plus a b) a -> real_eq b zero.
Proof.
  intros a b Hab.
  assert (Hba : real_eq (plus (opp a) a) zero).
  { exact (req_trans (plus (opp a) a) (plus a (opp a)) zero
                     (plus_comm (opp a) a) (plus_opp a)). }
  assert (H3 : real_eq (plus (plus (opp a) a) b) b).
  { apply (req_trans (plus (plus (opp a) a) b) (plus zero b) b).
    - apply (req_plus_compat (plus (opp a) a) zero b b Hba (req_refl b)).
    - exact (req_trans (plus zero b) (plus b zero) b
                       (plus_comm zero b) (plus_zero b)). }
  apply (req_trans b (plus (opp a) (plus a b)) zero).
  - exact (req_trans b (plus (plus (opp a) a) b) (plus (opp a) (plus a b))
                     (req_sym (plus (plus (opp a) a) b) b H3)
                     (req_sym (plus (opp a) (plus a b)) (plus (plus (opp a) a) b)
                              (plus_assoc (opp a) a b))).
  - apply (req_trans (plus (opp a) (plus a b)) (plus (opp a) a) zero).
    + apply (req_plus_compat (opp a) (opp a) (plus a b) a (req_refl (opp a)) Hab).
    + exact Hba.
Qed.

(* Id plus_cancel_l L1020：a + b == a + c ⟹ b == c *)
Lemma req_plus_cancel_l : forall a b c : R, real_eq (plus a b) (plus a c) -> real_eq b c.
Proof.
  intros a b c H.
  assert (Hbc : real_eq (plus b a) (plus c a)).
  { exact (req_trans (plus b a) (plus a b) (plus c a)
                     (plus_comm b a)
                     (req_trans (plus a b) (plus a c) (plus c a)
                                H (plus_comm a c))). }
  apply (req_trans b (plus b zero) c).
  - apply (req_sym (plus b zero) b). apply plus_zero.
  - apply (req_trans (plus b zero) (plus b (plus a (opp a))) c).
    + apply (req_plus_compat b b zero (plus a (opp a))).
      * apply req_refl.
      * apply (req_sym (plus a (opp a)) zero). apply plus_opp.
    + apply (req_trans (plus b (plus a (opp a))) (plus (plus b a) (opp a)) c).
      * apply plus_assoc.
      * apply (req_trans (plus (plus b a) (opp a)) (plus (plus c a) (opp a)) c).
        -- apply (req_plus_compat (plus b a) (plus c a) (opp a) (opp a) Hbc).
           apply req_refl.
        -- apply (req_trans (plus (plus c a) (opp a)) (plus c (plus a (opp a))) c).
           ++ apply (req_sym (plus c (plus a (opp a))) (plus (plus c a) (opp a))).
              apply plus_assoc.
           ++ apply (req_trans (plus c (plus a (opp a))) (plus c zero) c).
              ** apply (req_plus_compat c c (plus a (opp a)) zero).
                 --- apply req_refl.
                 --- apply plus_opp.
              ** apply plus_zero.
Qed.

(* Id mult_cancel_l L908：a > 0 ⟹ a·b == a·c ⟹ b == c *)
Lemma req_mult_cancel_l : forall a b c : R,
  real_lt zero a -> real_eq (mult a b) (mult a c) -> real_eq b c.
Proof.
  intros a b c Ha Habc.
  assert (Hlb : real_eq (mult (inv_pos a Ha) (mult a b)) b).
  { apply (req_trans (mult (inv_pos a Ha) (mult a b))
                     (mult (mult (inv_pos a Ha) a) b) b).
    - apply mult_assoc.
    - apply (req_trans (mult (mult (inv_pos a Ha) a) b) (mult one b) b).
      + apply (req_mult_compat (mult (inv_pos a Ha) a) one b b
                               (req_trans (mult (inv_pos a Ha) a)
                                          (mult a (inv_pos a Ha)) one
                                          (mult_comm (inv_pos a Ha) a)
                                          (inv_pos_correct a Ha))
                               (req_refl b)).
      + apply req_mult_one_l. }
  assert (Hrc : real_eq (mult (inv_pos a Ha) (mult a c)) c).
  { apply (req_trans (mult (inv_pos a Ha) (mult a c))
                     (mult (mult (inv_pos a Ha) a) c) c).
    - apply mult_assoc.
    - apply (req_trans (mult (mult (inv_pos a Ha) a) c) (mult one c) c).
      + apply (req_mult_compat (mult (inv_pos a Ha) a) one c c
                               (req_trans (mult (inv_pos a Ha) a)
                                          (mult a (inv_pos a Ha)) one
                                          (mult_comm (inv_pos a Ha) a)
                                          (inv_pos_correct a Ha))
                               (req_refl c)).
      + apply req_mult_one_l. }
  apply (req_trans b (mult (inv_pos a Ha) (mult a b)) c).
  - apply (req_sym (mult (inv_pos a Ha) (mult a b)) b). exact Hlb.
  - apply (req_trans (mult (inv_pos a Ha) (mult a b))
                     (mult (inv_pos a Ha) (mult a c)) c).
    + apply (req_mult_compat (inv_pos a Ha) (inv_pos a Ha) (mult a b) (mult a c)
                             (req_refl (inv_pos a Ha)) Habc).
    + exact Hrc.
Qed.

(* mult_cancel_r: via commutativity. *)
Lemma req_mult_cancel_r : forall a b c : R,
  real_lt zero a -> real_eq (mult b a) (mult c a) -> real_eq b c.
Proof.
  intros a b c Ha Hba.
  assert (Hlb : real_eq (mult (inv_pos a Ha) (mult a b)) b).
  { apply (req_trans (mult (inv_pos a Ha) (mult a b))
                     (mult (mult (inv_pos a Ha) a) b) b).
    - apply mult_assoc.
    - apply (req_trans (mult (mult (inv_pos a Ha) a) b) (mult one b) b).
      + apply (req_mult_compat (mult (inv_pos a Ha) a) one b b
                               (req_trans (mult (inv_pos a Ha) a)
                                          (mult a (inv_pos a Ha)) one
                                          (mult_comm (inv_pos a Ha) a)
                                          (inv_pos_correct a Ha))
                               (req_refl b)).
      + apply req_mult_one_l. }
  assert (Hrc : real_eq (mult (inv_pos a Ha) (mult a c)) c).
  { apply (req_trans (mult (inv_pos a Ha) (mult a c))
                     (mult (mult (inv_pos a Ha) a) c) c).
    - apply mult_assoc.
    - apply (req_trans (mult (mult (inv_pos a Ha) a) c) (mult one c) c).
      + apply (req_mult_compat (mult (inv_pos a Ha) a) one c c
                               (req_trans (mult (inv_pos a Ha) a)
                                          (mult a (inv_pos a Ha)) one
                                          (mult_comm (inv_pos a Ha) a)
                                          (inv_pos_correct a Ha))
                               (req_refl c)).
      + apply req_mult_one_l. }
  apply (req_trans b (mult (inv_pos a Ha) (mult a b)) c).
  - apply (req_sym (mult (inv_pos a Ha) (mult a b)) b). exact Hlb.
  - apply (req_trans (mult (inv_pos a Ha) (mult a b))
                     (mult (inv_pos a Ha) (mult a c)) c).
    + apply (req_mult_compat (inv_pos a Ha) (inv_pos a Ha) (mult a b) (mult a c)
                             (req_refl (inv_pos a Ha))
                             (req_trans (mult a b) (mult b a) (mult a c)
                                        (mult_comm a b)
                                        (req_trans (mult b a) (mult c a)
                                                   (mult a c)
                                                   Hba (mult_comm c a)))).
    + exact Hrc.
Qed.

(* le_mult_compat_r: a >= 0 and b <= c imply a*b <= a*c. *)
Lemma req_le_mult_compat_r : forall a b c : R,
  real_le zero a -> real_le b c -> real_le (mult a b) (mult a c).
Proof.
  intros a b c Ha Hbc.
  apply (le_id_r (mult a b) (mult c a) (mult a c) (mult_comm c a)
                 (le_id_l (mult a b) (mult b a) (mult c a) (mult_comm a b)
                          (le_mult_compat_weak b c a Ha Hbc))).
Qed.

(* Id two_times_quarter L784：2·((1/2)·(1/2)·e)·h' == (1/2·e)·h' *)
Lemma req_two_times_quarter : forall (e h' : R) (H2 : real_lt zero (plus one one)),
  real_eq (mult (plus one one)
            (mult (mult (inv_pos (plus one one) H2)
                        (mult (inv_pos (plus one one) H2) e)) h'))
      (mult (mult (inv_pos (plus one one) H2) e) h').
Proof.
  intros e h' H2.
  apply (req_trans
    (mult (plus one one)
          (mult (mult (inv_pos (plus one one) H2) (mult (inv_pos (plus one one) H2) e)) h'))
    (mult (mult (plus one one)
                (mult (inv_pos (plus one one) H2) (mult (inv_pos (plus one one) H2) e))) h')
    (mult (mult (inv_pos (plus one one) H2) e) h')).
  - apply mult_assoc.
  - apply (req_trans
      (mult (mult (plus one one)
                  (mult (inv_pos (plus one one) H2) (mult (inv_pos (plus one one) H2) e))) h')
      (mult (mult (mult (plus one one) (inv_pos (plus one one) H2))
                  (mult (inv_pos (plus one one) H2) e)) h')
      (mult (mult (inv_pos (plus one one) H2) e) h')).
    + apply (req_mult_compat
        (mult (plus one one)
              (mult (inv_pos (plus one one) H2) (mult (inv_pos (plus one one) H2) e)))
        (mult (mult (plus one one) (inv_pos (plus one one) H2))
              (mult (inv_pos (plus one one) H2) e))
        h' h'
        (mult_assoc (plus one one) (inv_pos (plus one one) H2)
                    (mult (inv_pos (plus one one) H2) e))
        (req_refl h')).
    + apply (req_trans
        (mult (mult (mult (plus one one) (inv_pos (plus one one) H2))
                    (mult (inv_pos (plus one one) H2) e)) h')
        (mult (mult one (mult (inv_pos (plus one one) H2) e)) h')
        (mult (mult (inv_pos (plus one one) H2) e) h')).
      * apply (req_mult_compat
          (mult (mult (plus one one) (inv_pos (plus one one) H2))
                (mult (inv_pos (plus one one) H2) e))
          (mult one (mult (inv_pos (plus one one) H2) e)) h' h'
          (req_mult_compat (mult (plus one one) (inv_pos (plus one one) H2)) one
                           (mult (inv_pos (plus one one) H2) e)
                           (mult (inv_pos (plus one one) H2) e)
                           (inv_pos_correct (plus one one) H2) (req_refl _))
          (req_refl _)).
      * apply (req_mult_compat (mult one (mult (inv_pos (plus one one) H2) e))
                               (mult (inv_pos (plus one one) H2) e) h' h'
                               (req_mult_one_l (mult (inv_pos (plus one one) H2) e))
                               (req_refl _)).
Qed.

(* Id mult_minus_distr_l L837：a·(b-c) == a·b - a·c *)
Lemma req_mult_minus_distr_l : forall a b c : R,
  real_eq (mult a (req_minus b c)) (req_minus (mult a b) (mult a c)).
Proof.
  intros a b c.
  apply (req_trans (mult a (req_minus b c)) (plus (mult a b) (mult a (opp c)))
                   (req_minus (mult a b) (mult a c))).
  - apply distrib.
  - apply (req_plus_compat (mult a b) (mult a b) (mult a (opp c)) (opp (mult a c))
                           (req_refl (mult a b)) (req_opp_mult_l a c)).
Qed.

(* Helper: (A + X) - (A + Y) == X - Y (error-decomposition engine). *)
Lemma req_minus_plus_congr : forall a x y : R,
  real_eq (req_minus (plus a x) (plus a y)) (req_minus x y).
Proof.
  intros a x y.
  apply (req_trans (plus (plus a x) (opp (plus a y)))
                   (plus (plus a x) (plus (opp a) (opp y)))
                   (plus x (opp y))).
  - apply (req_plus_compat (plus a x) (plus a x) (opp (plus a y)) (plus (opp a) (opp y))
                           (req_refl (plus a x)) (req_opp_plus a y)).
  - apply (req_trans (plus (plus a x) (plus (opp a) (opp y)))
                     (plus (plus a (opp a)) (plus x (opp y)))
                     (plus x (opp y))).
    + apply req_plus_swap_mid.
    + apply (req_trans (plus (plus a (opp a)) (plus x (opp y)))
                       (plus zero (plus x (opp y)))
                       (plus x (opp y))).
      * apply (req_plus_compat (plus a (opp a)) zero (plus x (opp y)) (plus x (opp y))
                               (plus_opp a) (req_refl (plus x (opp y)))).
      * apply (req_trans (plus zero (plus x (opp y)))
                         (plus (plus x (opp y)) zero) (plus x (opp y))
                         (plus_comm zero (plus x (opp y)))
                         (plus_zero (plus x (opp y)))).
Qed.

(* ============ D. Subtraction cluster (carrier = [req_minus]) ============ *)

(* Id minus_plus_cancel L668：a + (b - a) == b *)
Lemma req_minus_plus_cancel : forall a b : R, real_eq (plus a (req_minus b a)) b.
Proof.
  intros a b. unfold req_minus.
  apply (req_trans (plus a (plus b (opp a))) (plus (plus a b) (opp a)) b).
  - apply plus_assoc.
  - apply (req_trans (plus (plus a b) (opp a)) (plus (plus b a) (opp a)) b).
    + apply (req_plus_compat (plus a b) (plus b a) (opp a) (opp a)
                             (plus_comm a b) (req_refl (opp a))).
    + apply (req_trans (plus (plus b a) (opp a)) (plus b (plus a (opp a))) b).
      * apply (req_sym (plus b (plus a (opp a))) (plus (plus b a) (opp a))).
        apply plus_assoc.
      * apply (req_trans (plus b (plus a (opp a))) (plus b zero) b).
        -- apply (req_plus_compat b b (plus a (opp a)) zero
                                  (req_refl b) (plus_opp a)).
        -- apply plus_zero.
Qed.

(* Id minus_plus_cancel_r L681：(a + b) - a == b *)
Lemma req_minus_plus_cancel_r : forall a b : R, real_eq (req_minus (plus a b) a) b.
Proof.
  intros a b. unfold req_minus.
  apply (req_trans (plus (plus a b) (opp a)) (plus a (plus b (opp a))) b).
  - apply (req_sym (plus a (plus b (opp a))) (plus (plus a b) (opp a))).
    apply plus_assoc.
  - apply (req_trans (plus a (plus b (opp a))) (plus a (plus (opp a) b)) b).
    + apply (req_plus_compat a a (plus b (opp a)) (plus (opp a) b)
                             (req_refl a) (plus_comm b (opp a))).
    + apply (req_trans (plus a (plus (opp a) b)) (plus (plus a (opp a)) b) b).
      * apply plus_assoc.
      * apply (req_trans (plus (plus a (opp a)) b) (plus zero b) b).
        -- apply (req_plus_compat (plus a (opp a)) zero b b
                                  (plus_opp a) (req_refl b)).
        -- apply (req_trans (plus zero b) (plus b zero) b
                            (plus_comm zero b) (plus_zero b)).
Qed.

(* Id minus_plus_r L695：a - (b + c) == (a - b) - c *)
Lemma req_minus_plus_r : forall a b c : R,
  real_eq (req_minus a (plus b c)) (req_minus (req_minus a b) c).
Proof.
  intros a b c. unfold req_minus.
  apply (req_trans (plus a (opp (plus b c))) (plus a (plus (opp b) (opp c)))
                   (plus (plus a (opp b)) (opp c))).
  - apply (req_plus_compat a a (opp (plus b c)) (plus (opp b) (opp c))
                           (req_refl a) (req_opp_plus b c)).
  - apply plus_assoc.
Qed.

(* Id opp_minus L706：-(a - b) == (-a) + b *)
Lemma req_opp_minus : forall a b : R, real_eq (opp (req_minus a b)) (plus (opp a) b).
Proof.
  intros a b. unfold req_minus.
  apply (req_trans (opp (plus a (opp b))) (plus (opp a) (opp (opp b)))
                   (plus (opp a) b)).
  - apply req_opp_plus.
  - apply (req_plus_compat (opp a) (opp a) (opp (opp b)) b
                           (req_refl (opp a)) (req_double_neg b)).
Qed.

(* Id minus_plus_distr L534：(a+b) - (c+d) == (a-c) + (b-d) *)
Lemma req_minus_plus_distr : forall a b c d : R,
  real_eq (req_minus (plus a b) (plus c d)) (plus (req_minus a c) (req_minus b d)).
Proof.
  intros a b c d. unfold req_minus.
  apply (req_trans (plus (plus a b) (opp (plus c d)))
                   (plus (plus a b) (plus (opp c) (opp d)))
                   (plus (plus a (opp c)) (plus b (opp d)))).
  - apply (req_plus_compat (plus a b) (plus a b) (opp (plus c d)) (plus (opp c) (opp d))
                           (req_refl (plus a b)) (req_opp_plus c d)).
  - apply req_plus_swap_mid.
Qed.

(* Id minus_plus_quad L822：(A + (B+C)) - (D+E) == (A-D) + ((B-E) + C) *)
Lemma req_minus_plus_quad : forall A B C D E : R,
  real_eq (req_minus (plus A (plus B C)) (plus D E))
      (plus (req_minus A D) (plus (req_minus B E) C)).
Proof.
  intros A B C D E. unfold req_minus.
  assert (Hswap : real_eq (plus (plus B C) (opp E)) (plus (plus B (opp E)) C)).
  { apply (req_trans (plus (plus B C) (opp E)) (plus B (plus C (opp E)))
                     (plus (plus B (opp E)) C)).
    - apply (req_sym (plus B (plus C (opp E))) (plus (plus B C) (opp E))).
      apply plus_assoc.
    - apply (req_trans (plus B (plus C (opp E))) (plus B (plus (opp E) C))
                       (plus (plus B (opp E)) C)).
      + apply (req_plus_compat B B (plus C (opp E)) (plus (opp E) C)
                               (req_refl B) (plus_comm C (opp E))).
      + apply plus_assoc. }
  apply (req_trans (plus (plus A (plus B C)) (opp (plus D E)))
                   (plus (plus A (plus B C)) (plus (opp D) (opp E)))
                   (plus (plus A (opp D)) (plus (plus B (opp E)) C))).
  - apply (req_plus_compat (plus A (plus B C)) (plus A (plus B C))
                           (opp (plus D E)) (plus (opp D) (opp E))
                           (req_refl (plus A (plus B C))) (req_opp_plus D E)).
  - apply (req_trans (plus (plus A (plus B C)) (plus (opp D) (opp E)))
                     (plus (plus A (opp D)) (plus (plus B C) (opp E)))
                     (plus (plus A (opp D)) (plus (plus B (opp E)) C))).
    + apply req_plus_swap_mid.
    + apply (req_plus_compat (plus A (opp D)) (plus A (opp D))
                             (plus (plus B C) (opp E)) (plus (plus B (opp E)) C)
                             (req_refl (plus A (opp D))) Hswap).
Qed.

(* Id minus_split L760：a - b == (a - (b + c)) + c *)
Lemma req_minus_split : forall a b c : R,
  real_eq (req_minus a b) (plus (req_minus a (plus b c)) c).
Proof.
  intros a b c.
  assert (Hob : real_eq (opp b) (plus (opp b) (plus (opp c) c))).
  { apply (req_trans (opp b) (plus (opp b) zero) (plus (opp b) (plus (opp c) c))).
    - apply (req_sym (plus (opp b) zero) (opp b)). apply plus_zero.
    - apply (req_plus_compat (opp b) (opp b) zero (plus (opp c) c)
                             (req_refl (opp b))
                             (req_sym (plus (opp c) c) zero (req_plus_opp_l c))). }
  unfold req_minus.
  apply (req_trans (plus a (opp b)) (plus a (plus (opp b) (plus (opp c) c)))
                   (plus (plus a (opp (plus b c))) c)).
  - apply (req_plus_compat a a (opp b) (plus (opp b) (plus (opp c) c))
                           (req_refl a) Hob).
  - apply (req_trans (plus a (plus (opp b) (plus (opp c) c)))
                     (plus a (plus (plus (opp b) (opp c)) c))
                     (plus (plus a (opp (plus b c))) c)).
    + apply (req_plus_compat a a (plus (opp b) (plus (opp c) c))
                             (plus (plus (opp b) (opp c)) c)
                             (req_refl a)
                             (plus_assoc (opp b) (opp c) c)).
    + apply (req_trans (plus a (plus (plus (opp b) (opp c)) c))
                       (plus (plus a (plus (opp b) (opp c))) c)
                       (plus (plus a (opp (plus b c))) c)).
      * apply plus_assoc.
      * apply (req_plus_compat (plus a (plus (opp b) (opp c)))
                               (plus a (opp (plus b c))) c c
                               (req_plus_compat a a (plus (opp b) (opp c))
                                                (opp (plus b c))
                                                (req_refl a)
                                                (req_sym (opp (plus b c))
                                                         (plus (opp b) (opp c))
                                                         (req_opp_plus b c)))
                               (req_refl c)).
Qed.

(* Id le_minus_nonneg L959：a ≤ b ⟹ 0 ≤ b - a *)
Lemma req_le_minus_nonneg : forall a b : R, real_le a b -> real_le zero (req_minus b a).
Proof.
  intros a b Hab. unfold req_minus.
  apply (le_id_l zero (plus a (opp a)) (plus b (opp a))
                 (req_sym (plus a (opp a)) zero (plus_opp a))
                 (le_plus_compat a b (opp a) (opp a) Hab (le_refl (opp a)))).
Qed.

(* Id minus_eq_cancel L971：a - b == 0 ⟹ a == b *)
Lemma req_minus_eq_cancel : forall a b : R, real_eq (req_minus a b) zero -> real_eq a b.
Proof.
  intros a b Hab. unfold req_minus in Hab.
  assert (Hpb : real_eq (opp b) (opp a)).
  { exact (req_plus_inv_unique a (opp b) (opp a) Hab (plus_opp a)). }
  apply (req_trans a (opp (opp a)) b).
  - apply (req_sym (opp (opp a)) a). apply req_double_neg.
  - apply (req_trans (opp (opp a)) (opp (opp b)) b).
    + apply (req_opp_compat (opp a) (opp b) (req_sym (opp b) (opp a) Hpb)).
    + apply req_double_neg.
Qed.

(* Id minus_self_zero L984：a == b ⟹ a - b == 0 *)
Lemma req_minus_self_zero : forall a b : R, real_eq a b -> real_eq (req_minus a b) zero.
Proof.
  intros a b Hab. unfold req_minus.
  apply (req_trans (plus a (opp b)) (plus b (opp b)) zero).
  - apply (req_plus_compat a b (opp b) (opp b) Hab (req_refl (opp b))).
  - apply plus_opp.
Qed.

(* ring_d_cancel: a*(-b) == a*(-c) + a*d with a > 0 yields c - b == d. *)
Lemma req_ring_d_cancel : forall a b c d : R,
  real_lt zero a ->
  real_eq (mult a (opp b)) (plus (mult a (opp c)) (mult a d)) ->
  real_eq (req_minus c b) d.
Proof.
  intros a b c d Ha Hmain. unfold req_minus.
  apply (req_mult_cancel_l a (plus c (opp b)) d Ha).
  apply (req_trans (mult a (plus c (opp b)))
                   (plus (mult a c) (mult a (opp b)))
                   (mult a d)).
  - apply distrib.
  - apply (req_trans (plus (mult a c) (mult a (opp b)))
                     (plus (mult a c) (plus (mult a (opp c)) (mult a d)))
                     (mult a d)).
    + apply (req_plus_compat (mult a c) (mult a c) (mult a (opp b))
                             (plus (mult a (opp c)) (mult a d))
                             (req_refl (mult a c)) Hmain).
    + apply (req_trans (plus (mult a c) (plus (mult a (opp c)) (mult a d)))
                       (plus (plus (mult a c) (mult a (opp c))) (mult a d))
                       (mult a d)).
      * apply plus_assoc.
      * apply (req_trans (plus (plus (mult a c) (mult a (opp c))) (mult a d))
                         (plus zero (mult a d)) (mult a d)).
        -- apply (req_plus_compat
                    (plus (mult a c) (mult a (opp c))) zero (mult a d) (mult a d)
                    (req_trans (plus (mult a c) (mult a (opp c)))
                               (plus (mult a c) (opp (mult a c))) zero
                               (req_plus_compat (mult a c) (mult a c)
                                                (mult a (opp c)) (opp (mult a c))
                                                (req_refl (mult a c))
                                                (req_opp_mult_l a c))
                               (plus_opp (mult a c)))
                    (req_refl (mult a d))).
        -- apply (req_trans (plus zero (mult a d))
                            (plus (mult a d) zero) (mult a d)
                            (plus_comm zero (mult a d)) (plus_zero (mult a d))).
Qed.

(* Id ring_minus_trans L1072：(a-b) == (a-c) - (b-c) *)
Lemma req_ring_minus_trans : forall a b c : R,
  real_eq (req_minus a b) (req_minus (req_minus a c) (req_minus b c)).
Proof.
  intros a b c. unfold req_minus.
  assert (HR : real_eq (plus (plus a (opp c)) (opp (plus b (opp c)))) (plus a (opp b))).
  { apply (req_trans (plus (plus a (opp c)) (opp (plus b (opp c))))
                     (plus a (plus (opp c) (opp (plus b (opp c)))))
                     (plus a (opp b))).
    - apply (req_sym (plus a (plus (opp c) (opp (plus b (opp c)))))
                     (plus (plus a (opp c)) (opp (plus b (opp c))))).
      apply plus_assoc.
    - apply (req_trans (plus a (plus (opp c) (opp (plus b (opp c)))))
                       (plus a (plus (opp c) (plus (opp b) (opp (opp c)))))
                       (plus a (opp b))).
      + apply (req_plus_compat a a
                               (plus (opp c) (opp (plus b (opp c))))
                               (plus (opp c) (plus (opp b) (opp (opp c))))
                               (req_refl a)
                               (req_plus_compat (opp c) (opp c)
                                                (opp (plus b (opp c)))
                                                (plus (opp b) (opp (opp c)))
                                                (req_refl (opp c))
                                                (req_opp_plus b (opp c)))).
      + apply (req_trans (plus a (plus (opp c) (plus (opp b) (opp (opp c)))))
                         (plus a (plus (opp c) (plus (opp b) c)))
                         (plus a (opp b))).
        * apply (req_plus_compat a a
                                 (plus (opp c) (plus (opp b) (opp (opp c))))
                                 (plus (opp c) (plus (opp b) c))
                                 (req_refl a)
                                 (req_plus_compat (opp c) (opp c)
                                                  (plus (opp b) (opp (opp c)))
                                                  (plus (opp b) c)
                                                  (req_refl (opp c))
                                                  (req_plus_compat (opp b) (opp b)
                                                                   (opp (opp c)) c
                                                                   (req_refl (opp b))
                                                                   (req_double_neg c)))).
        * apply (req_trans (plus a (plus (opp c) (plus (opp b) c)))
                           (plus a (plus (opp c) (plus c (opp b))))
                           (plus a (opp b))).
          -- apply (req_plus_compat a a (plus (opp c) (plus (opp b) c))
                                    (plus (opp c) (plus c (opp b)))
                                    (req_refl a)
                                    (req_plus_compat (opp c) (opp c)
                                                     (plus (opp b) c) (plus c (opp b))
                                                     (req_refl (opp c))
                                                     (plus_comm (opp b) c))).
          -- apply (req_trans (plus a (plus (opp c) (plus c (opp b))))
                              (plus a (plus (plus (opp c) c) (opp b)))
                              (plus a (opp b))).
             ++ apply (req_plus_compat a a (plus (opp c) (plus c (opp b)))
                                       (plus (plus (opp c) c) (opp b))
                                       (req_refl a) (plus_assoc (opp c) c (opp b))).
             ++ apply (req_trans (plus a (plus (plus (opp c) c) (opp b)))
                                 (plus a (plus zero (opp b)))
                                 (plus a (opp b))).
                ** apply (req_plus_compat a a (plus (plus (opp c) c) (opp b))
                                          (plus zero (opp b))
                                          (req_refl a)
                                          (req_plus_compat (plus (opp c) c) zero
                                                           (opp b) (opp b)
                                                           (req_trans (plus (opp c) c)
                                                                      (plus c (opp c)) zero
                                                                      (plus_comm (opp c) c)
                                                                      (plus_opp c))
                                                           (req_refl (opp b)))).
                ** apply (req_plus_compat a a (plus zero (opp b)) (opp b)
                                          (req_refl a)
                                          (req_trans (plus zero (opp b))
                                                     (plus (opp b) zero) (opp b)
                                                     (plus_comm zero (opp b))
                                                     (plus_zero (opp b)))).
  }
  exact (req_sym _ _ HR).
Qed.

(* Id minus_plus_congr_l L95663（AlgHelpers）：(a+b) - (a+c) == b - c *)
Lemma req_minus_plus_congr_l : forall a b c : R,
  real_eq (req_minus (plus a b) (plus a c)) (req_minus b c).
Proof.
  intros a b c. unfold req_minus.
  apply (req_trans (plus (plus a b) (opp (plus a c)))
                   (plus (plus a b) (plus (opp a) (opp c)))
                   (plus b (opp c))).
  - apply (req_plus_compat (plus a b) (plus a b) (opp (plus a c))
                           (plus (opp a) (opp c))
                           (req_refl (plus a b)) (req_opp_plus a c)).
  - apply (req_trans (plus (plus a b) (plus (opp a) (opp c)))
                     (plus (plus a (opp a)) (plus b (opp c)))
                     (plus b (opp c))).
    + apply req_plus_swap_mid.
    + apply (req_trans (plus (plus a (opp a)) (plus b (opp c)))
                       (plus zero (plus b (opp c)))
                       (plus b (opp c))).
      * apply (req_plus_compat (plus a (opp a)) zero (plus b (opp c))
                               (plus b (opp c))
                               (plus_opp a) (req_refl (plus b (opp c)))).
      * apply (req_trans (plus zero (plus b (opp c)))
                         (plus (plus b (opp c)) zero) (plus b (opp c))
                         (plus_comm zero (plus b (opp c)))
                         (plus_zero (plus b (opp c)))).
Qed.

(* Id minus_factor L95675（AlgHelpers）：k·x - k·y == k·(x - y) *)
Lemma req_minus_factor : forall k x y : R,
  real_eq (req_minus (mult k x) (mult k y)) (mult k (req_minus x y)).
Proof.
  intros k x y. unfold req_minus.
  apply (req_trans (plus (mult k x) (opp (mult k y)))
                   (plus (mult k x) (mult k (opp y)))
                   (mult k (plus x (opp y)))).
  - apply (req_plus_compat (mult k x) (mult k x) (opp (mult k y)) (mult k (opp y))
                           (req_refl (mult k x))
                           (req_sym (mult k (opp y)) (opp (mult k y))
                                    (req_opp_mult_l k y))).
  - apply (req_sym (mult k (plus x (opp y))) (plus (mult k x) (mult k (opp y)))).
    apply distrib.
Qed.

(* Id minus_factor_pt L95684（AlgHelpers）：x·k - y·k == (x - y)·k *)
Lemma req_minus_factor_pt : forall x y k : R,
  real_eq (req_minus (mult x k) (mult y k)) (mult (req_minus x y) k).
Proof.
  intros x y k. unfold req_minus.
  apply (req_trans (plus (mult x k) (opp (mult y k)))
                   (plus (mult x k) (mult (opp y) k))
                   (mult (plus x (opp y)) k)).
  - apply (req_plus_compat (mult x k) (mult x k) (opp (mult y k)) (mult (opp y) k)
                           (req_refl (mult x k))
                           (req_sym (mult (opp y) k) (opp (mult y k))
                                    (req_opp_mult_r y k))).
  - apply (req_sym (mult (plus x (opp y)) k) (plus (mult x k) (mult (opp y) k))).
    apply req_mult_plus_distr_r.
Qed.

(* ============ E. Order / abs / exponential side ============ *)
(* abs_plus_one_pos (|a| + 1 > 0) is NOT carried here: its Id-carrier proof    *)
(* uses the plain form [abs_nonneg : real_le zero (abs a)], while this          *)
(* interface carries the epsilon form, not derivable from it (no order          *)
(* elimination).  See the exclusions at the end of the file.                    *)

(* Id le_plus_nonneg_r L562：b ≥ 0 ⟹ a ≤ a + b *)
Lemma req_le_plus_nonneg_r : forall a b : R, real_le zero b -> real_le a (plus a b).
Proof.
  intros a b Hb.
  apply (le_trans a (plus a zero) (plus a b)
                  (le_id_r a a (plus a zero)
                           (req_sym (plus a zero) a (plus_zero a)) (le_refl a))
                  (le_plus_compat a a zero b (le_refl a) Hb)).
Qed.

(* Id abs_le_abs_plus_one L573：|a| ≤ |a| + 1 *)
Lemma req_abs_le_abs_plus_one : forall a : R, real_le (abs a) (plus (abs a) one).
Proof.
  intro a.
  apply (le_trans (abs a) (plus (abs a) zero) (plus (abs a) one)
                  (le_id_r (abs a) (abs a) (plus (abs a) zero)
                           (req_sym (plus (abs a) zero) (abs a)
                                    (plus_zero (abs a)))
                           (le_refl (abs a)))).
  apply (le_plus_compat (abs a) (abs a) zero one).
  - apply (le_refl (abs a)).
  - apply (lt_le_iff zero one). left. apply one_pos.
Qed.

(* plus_le_lt_pos: a >= 0 and b > 0 imply a + b > 0. *)
Lemma req_plus_le_lt_pos : forall a b : R, real_le zero a -> real_lt zero b -> real_lt zero (plus a b).
Proof.
  intros a b Ha Hb.
  apply (lt_le_trans zero b (plus a b) Hb
                     (le_trans b (plus zero b) (plus a b)
                               (le_id_r b b (plus zero b)
                                        (req_sym (plus zero b) b
                                                 (req_trans (plus zero b)
                                                            (plus b zero) b
                                                            (plus_comm zero b)
                                                            (plus_zero b)))
                                        (le_refl b))
                               (le_plus_compat zero a b b Ha (le_refl b)))).
Qed.

(* Id abs_minus_sym L717：|a - b| == |b - a| *)
Lemma req_abs_minus_sym : forall a b : R,
  real_eq (abs (req_minus a b)) (abs (req_minus b a)).
Proof.
  intros a b.
  assert (H1 : real_eq (req_minus a b) (opp (req_minus b a))).
  { unfold req_minus.
    apply (req_trans (plus a (opp b)) (plus (opp b) a) (opp (plus b (opp a)))).
    - apply plus_comm.
    - apply (req_trans (plus (opp b) a) (plus (opp b) (opp (opp a)))
                       (opp (plus b (opp a)))).
      + apply (req_plus_compat (opp b) (opp b) a (opp (opp a))
                               (req_refl (opp b))
                               (req_sym (opp (opp a)) a (req_double_neg a))).
      + apply (req_sym (opp (plus b (opp a))) (plus (opp b) (opp (opp a)))
                       (req_opp_plus b (opp a))). }
  apply (req_trans (abs (req_minus a b)) (abs (opp (req_minus b a)))
                   (abs (req_minus b a))).
  - apply req_abs_compat. exact H1.
  - apply abs_opp.
Qed.

(* exp_neg_opp_plus: e^{-(a+b)} == e^{-a} * e^{-b}, via the world exp_neg compatibility fact. *)
Lemma req_exp_neg_opp_plus : forall a b : R,
  real_eq (exp_neg (opp (plus a b))) (mult (exp_neg (opp a)) (exp_neg (opp b))).
Proof.
  intros a b.
  apply (req_trans (exp_neg (opp (plus a b))) (exp_neg (plus (opp a) (opp b)))
                   (mult (exp_neg (opp a)) (exp_neg (opp b)))).
  - apply exp_neg_req_compat_setoid. apply req_opp_plus.
  - apply exp_neg_plus.
Qed.

(* exp_neg_opp_log: e^{-log x} == x for x > 0; direct chain                    *)
(* [log_inv_log] + [exp_neg_log_inv], no bridge assumptions.                    *)
Lemma req_exp_neg_opp_log : forall (x : R) (Hx : real_lt zero x),
  real_eq (exp_neg (opp (log x Hx))) x.
Proof.
  intros x Hx.
  apply (req_trans (exp_neg (opp (log x Hx))) (exp_neg (log_inv x Hx)) x).
  - apply exp_neg_req_compat_setoid.
    apply (req_sym (log_inv x Hx) (opp (log x Hx))). apply log_inv_log.
  - apply exp_neg_log_inv.
Qed.

(* ============ F. Helper layer ============ *)

(* Direct use of the interface field [lt_id_r].  On the Id carrier this        *)
(* needed equality elimination; accessed as a field it is direct.               *)
Lemma req_lt_id_r_loc : forall (a b c : R), real_eq b c -> real_lt a b -> real_lt a c.
Proof. intros a b c H Hlt. exact (lt_id_r a b c H Hlt). Qed.

(* Id plus_exchange L95651：(a+c)+(b+d) == (a+b)+(c+d) *)
Lemma req_plus_exchange : forall a b c d : R,
  real_eq (plus (plus a c) (plus b d)) (plus (plus a b) (plus c d)).
Proof.
  intros a b c d.
  apply (req_trans (plus (plus a c) (plus b d)) (plus a (plus c (plus b d)))
                   (plus (plus a b) (plus c d))).
  - apply (req_sym (plus a (plus c (plus b d))) (plus (plus a c) (plus b d))).
    apply plus_assoc.
  - apply (req_trans (plus a (plus c (plus b d))) (plus a (plus (plus c b) d))
                     (plus (plus a b) (plus c d))).
    + apply (req_plus_compat a a (plus c (plus b d)) (plus (plus c b) d)
                             (req_refl a) (plus_assoc c b d)).
    + apply (req_trans (plus a (plus (plus c b) d)) (plus a (plus (plus b c) d))
                       (plus (plus a b) (plus c d))).
      * apply (req_plus_compat a a (plus (plus c b) d) (plus (plus b c) d)
                               (req_refl a)
                               (req_plus_compat (plus c b) (plus b c) d d
                                                (plus_comm c b) (req_refl d))).
      * apply (req_trans (plus a (plus (plus b c) d)) (plus a (plus b (plus c d)))
                         (plus (plus a b) (plus c d))).
        -- apply (req_plus_compat a a (plus (plus b c) d) (plus b (plus c d))
                                  (req_refl a)
                                  (req_sym (plus b (plus c d)) (plus (plus b c) d)
                                           (plus_assoc b c d))).
        -- apply plus_assoc.
Qed.

(* inv_pos_mult_distr: inv (a*b) == inv a * inv b for positive a b. *)
Lemma req_inv_pos_mult_distr : forall (a b : R) (Ha : real_lt zero a) (Hb : real_lt zero b),
  real_eq (inv_pos (mult a b) (mult_positive a b Ha Hb))
      (mult (inv_pos a Ha) (inv_pos b Hb)).
Proof.
  intros a b Ha Hb.
  assert (Hcore : real_eq (mult (mult a b) (mult (inv_pos a Ha) (inv_pos b Hb))) one).
  { apply (req_trans (mult (mult a b) (mult (inv_pos a Ha) (inv_pos b Hb)))
                     (mult a (mult b (mult (inv_pos a Ha) (inv_pos b Hb))))
                     one).
    - apply (req_sym (mult a (mult b (mult (inv_pos a Ha) (inv_pos b Hb))))
                     (mult (mult a b) (mult (inv_pos a Ha) (inv_pos b Hb)))).
      apply mult_assoc.
    - apply (req_trans (mult a (mult b (mult (inv_pos a Ha) (inv_pos b Hb))))
                       (mult a (mult (inv_pos a Ha) (mult (inv_pos b Hb) b)))
                       one).
      + apply (req_mult_compat a a (mult b (mult (inv_pos a Ha) (inv_pos b Hb)))
                               (mult (inv_pos a Ha) (mult (inv_pos b Hb) b)) (req_refl a)
        (req_trans (mult b (mult (inv_pos a Ha) (inv_pos b Hb)))
                   (mult (mult (inv_pos a Ha) (inv_pos b Hb)) b)
                   (mult (inv_pos a Ha) (mult (inv_pos b Hb) b))
                   (mult_comm b (mult (inv_pos a Ha) (inv_pos b Hb)))
                   (req_sym (mult (inv_pos a Ha) (mult (inv_pos b Hb) b))
                            (mult (mult (inv_pos a Ha) (inv_pos b Hb)) b)
                            (mult_assoc (inv_pos a Ha) (inv_pos b Hb) b)))).
      + apply (req_trans (mult a (mult (inv_pos a Ha) (mult (inv_pos b Hb) b)))
                         (mult (mult a (inv_pos a Ha)) (mult (inv_pos b Hb) b)) one).
        * apply mult_assoc.
        * apply (req_trans (mult (mult a (inv_pos a Ha)) (mult (inv_pos b Hb) b))
                           (mult one (mult (inv_pos b Hb) b)) one).
          -- apply (req_mult_compat (mult a (inv_pos a Ha)) one
                                    (mult (inv_pos b Hb) b) (mult (inv_pos b Hb) b)
                                    (inv_pos_correct a Ha)
                                    (req_refl (mult (inv_pos b Hb) b))).
          -- apply (req_trans (mult one (mult (inv_pos b Hb) b))
                              (mult (inv_pos b Hb) b) one
                              (req_mult_one_l (mult (inv_pos b Hb) b))
                              (req_trans (mult (inv_pos b Hb) b)
                                         (mult b (inv_pos b Hb)) one
                                         (mult_comm (inv_pos b Hb) b)
                                         (inv_pos_correct b Hb))). }
  apply (req_mult_cancel_l (mult a b) (inv_pos (mult a b) (mult_positive a b Ha Hb))
                          (mult (inv_pos a Ha) (inv_pos b Hb))
                          (mult_positive a b Ha Hb)).
  exact (req_trans (mult (mult a b) (inv_pos (mult a b) (mult_positive a b Ha Hb)))
                   one
                   (mult (mult a b) (mult (inv_pos a Ha) (inv_pos b Hb)))
                   (inv_pos_correct (mult a b) (mult_positive a b Ha Hb))
                   (req_sym (mult (mult a b) (mult (inv_pos a Ha) (inv_pos b Hb))) one
                            Hcore)).
Qed.

(* ============ G. Larger statements ============ *)

(* Id mult_delta_split L798：(a+da)(b+db) - ab == a·db + b·da + da·db *)
Lemma req_mult_delta_split : forall a b da db : R,
  real_eq (req_minus (mult (plus a da) (plus b db)) (mult a b))
      (plus (mult a db) (plus (mult b da) (mult da db))).
Proof.
  intros a b da db.
  assert (Hexp : real_eq (mult (plus a da) (plus b db))
                     (plus (mult a b)
                           (plus (mult da b)
                                 (plus (mult a db) (mult da db))))).
  { apply (req_trans (mult (plus a da) (plus b db))
                     (plus (mult (plus a da) b) (mult (plus a da) db))
                     (plus (mult a b)
                           (plus (mult da b) (plus (mult a db) (mult da db))))).
    - apply distrib.
    - apply (req_trans (plus (mult (plus a da) b) (mult (plus a da) db))
                       (plus (plus (mult a b) (mult da b))
                             (plus (mult a db) (mult da db)))
                       (plus (mult a b)
                             (plus (mult da b) (plus (mult a db) (mult da db))))).
      + apply (req_plus_compat
                 (mult (plus a da) b) (plus (mult a b) (mult da b))
                 (mult (plus a da) db) (plus (mult a db) (mult da db))
                 (req_mult_plus_distr_r a da b)
                 (req_mult_plus_distr_r a da db)).
      + apply (req_sym (plus (mult a b)
                             (plus (mult da b) (plus (mult a db) (mult da db))))
                       (plus (plus (mult a b) (mult da b))
                             (plus (mult a db) (mult da db)))
                       (plus_assoc (mult a b) (mult da b)
                                   (plus (mult a db) (mult da db)))). }
  assert (Hreord : real_eq (plus (mult da b) (plus (mult a db) (mult da db)))
                       (plus (mult a db) (plus (mult b da) (mult da db)))).
  { apply (req_trans (plus (mult da b) (plus (mult a db) (mult da db)))
                     (plus (plus (mult a db) (mult da db)) (mult da b))
                     (plus (mult a db) (plus (mult b da) (mult da db)))).
    - apply plus_comm.
    - apply (req_trans (plus (plus (mult a db) (mult da db)) (mult da b))
                       (plus (mult a db) (plus (mult da db) (mult da b)))
                       (plus (mult a db) (plus (mult b da) (mult da db)))).
      + apply (req_sym (plus (mult a db) (plus (mult da db) (mult da b)))
                       (plus (plus (mult a db) (mult da db)) (mult da b))).
        apply plus_assoc.
      + apply (req_plus_compat (mult a db) (mult a db)
                               (plus (mult da db) (mult da b))
                               (plus (mult b da) (mult da db))
                               (req_refl (mult a db))
                               (req_trans (plus (mult da db) (mult da b))
                                          (plus (mult da b) (mult da db))
                                          (plus (mult b da) (mult da db))
                                          (plus_comm (mult da db) (mult da b))
                                          (req_plus_compat (mult da b) (mult b da)
                                                           (mult da db) (mult da db)
                                                           (mult_comm da b)
                                                           (req_refl (mult da db))))). }
  unfold req_minus.
  apply (req_trans (plus (mult (plus a da) (plus b db)) (opp (mult a b)))
                   (plus (plus (mult a b)
                               (plus (mult da b)
                                     (plus (mult a db) (mult da db))))
                         (opp (mult a b)))
                   (plus (mult a db) (plus (mult b da) (mult da db)))).
  - apply (req_plus_compat _ _ (opp (mult a b)) (opp (mult a b)) Hexp (req_refl _)).
  - apply (req_trans (plus (plus (mult a b)
                                 (plus (mult da b)
                                       (plus (mult a db) (mult da db))))
                          (opp (mult a b)))
                     (plus (mult da b) (plus (mult a db) (mult da db)))
                     (plus (mult a db) (plus (mult b da) (mult da db)))).
    + apply req_plus_cancel.
    + exact Hreord.
Qed.

(* Product error decomposition, with f1 := f x, f2 := f (x+h), g1 := g x,      *)
(* g2 := g (x+h), u := f2 - f1, v := g2 - g1.  The real_eq version rebuilds    *)
(* the factors via Hcf/Hcg, expands Hfg, shifts HP and regroups four terms     *)
(* with [real_eq_minus_plus_quad] — a substantial adaptation.         *)
Lemma req_mult_diff_decomp :
  forall (f g : R -> R) (df dg : R -> R) (x h : R),
  real_eq (req_minus (mult (f (plus x h)) (g (plus x h)))
            (plus (mult (f x) (g x))
                  (mult (plus (mult (df x) (g x)) (mult (f x) (dg x))) h)))
      (plus (mult (f x) (req_minus (g (plus x h)) (plus (g x) (mult (dg x) h))))
            (plus (mult (g x) (req_minus (f (plus x h)) (plus (f x) (mult (df x) h))))
                  (mult (req_minus (f (plus x h)) (f x))
                        (req_minus (g (plus x h)) (g x))))).
Proof.
  intros f g df dg x h.
  set (f1 := f x).
  set (f2 := f (plus x h)).
  set (g1 := g x).
  set (g2 := g (plus x h)).
  set (dfx := df x).
  set (dgx := dg x).
  set (u := req_minus f2 f1).
  set (v := req_minus g2 g1).
  assert (Hcf : real_eq (plus f1 u) f2) by apply req_minus_plus_cancel.
  assert (Hcg : real_eq (plus g1 v) g2) by apply req_minus_plus_cancel.
  assert (Hfg : real_eq (mult f2 g2)
                    (plus (mult f1 g1)
                          (plus (mult f1 v) (plus (mult g1 u) (mult u v))))).
  { apply (req_trans (mult f2 g2) (mult (plus f1 u) g2)
                     (plus (mult f1 g1)
                           (plus (mult f1 v) (plus (mult g1 u) (mult u v))))).
    - apply (req_mult_compat f2 (plus f1 u) g2 g2
                             (req_sym (plus f1 u) f2 Hcf) (req_refl g2)).
    - apply (req_trans (mult (plus f1 u) g2)
                       (plus (mult f1 g2) (mult u g2))
                       (plus (mult f1 g1)
                             (plus (mult f1 v) (plus (mult g1 u) (mult u v))))).
      + apply req_mult_plus_distr_r.
      + apply (req_trans (plus (mult f1 g2) (mult u g2))
                         (plus (mult f1 (plus g1 v)) (mult u (plus g1 v)))
                         (plus (mult f1 g1)
                               (plus (mult f1 v) (plus (mult g1 u) (mult u v))))).
        * apply (req_plus_compat (mult f1 g2) (mult f1 (plus g1 v))
                                 (mult u g2) (mult u (plus g1 v))
                                 (req_mult_compat f1 f1 g2 (plus g1 v) (req_refl f1)
                                                  (req_sym (plus g1 v) g2 Hcg))
                                 (req_mult_compat u u g2 (plus g1 v) (req_refl u)
                                                  (req_sym (plus g1 v) g2 Hcg))).
        * apply (req_trans (plus (mult f1 (plus g1 v)) (mult u (plus g1 v)))
                           (plus (plus (mult f1 g1) (mult f1 v))
                                 (plus (mult u g1) (mult u v)))
                           (plus (mult f1 g1)
                                 (plus (mult f1 v) (plus (mult g1 u) (mult u v))))).
          -- apply (req_plus_compat (mult f1 (plus g1 v)) (plus (mult f1 g1) (mult f1 v))
                                    (mult u (plus g1 v)) (plus (mult u g1) (mult u v))
                                    (distrib f1 g1 v) (distrib u g1 v)).
          -- apply (req_trans (plus (plus (mult f1 g1) (mult f1 v))
                                    (plus (mult u g1) (mult u v)))
                              (plus (plus (mult f1 g1) (mult f1 v))
                                    (plus (mult g1 u) (mult u v)))
                              (plus (mult f1 g1)
                                    (plus (mult f1 v) (plus (mult g1 u) (mult u v))))).
             ++ apply (req_plus_compat (plus (mult f1 g1) (mult f1 v))
                                       (plus (mult f1 g1) (mult f1 v))
                                       (plus (mult u g1) (mult u v))
                                       (plus (mult g1 u) (mult u v))
                                       (req_refl (plus (mult f1 g1) (mult f1 v)))
                                       (req_plus_compat (mult u g1) (mult g1 u)
                                                        (mult u v) (mult u v)
                                                        (mult_comm u g1)
                                                        (req_refl (mult u v)))).
             ++ apply (req_sym (plus (mult f1 g1)
                                     (plus (mult f1 v) (plus (mult g1 u) (mult u v))))
                               (plus (plus (mult f1 g1) (mult f1 v))
                                     (plus (mult g1 u) (mult u v)))).
                apply plus_assoc. }
  assert (HP : real_eq (mult (plus (mult dfx g1) (mult f1 dgx)) h)
                   (plus (mult f1 (mult dgx h)) (mult g1 (mult dfx h)))).
  { apply (req_trans (mult (plus (mult dfx g1) (mult f1 dgx)) h)
                     (plus (mult (mult dfx g1) h) (mult (mult f1 dgx) h))
                     (plus (mult f1 (mult dgx h)) (mult g1 (mult dfx h)))).
    - apply req_mult_plus_distr_r.
    - apply (req_trans (plus (mult (mult dfx g1) h) (mult (mult f1 dgx) h))
                       (plus (mult g1 (mult dfx h)) (mult f1 (mult dgx h)))
                       (plus (mult f1 (mult dgx h)) (mult g1 (mult dfx h)))).
      + apply (req_plus_compat (mult (mult dfx g1) h) (mult g1 (mult dfx h))
                               (mult (mult f1 dgx) h) (mult f1 (mult dgx h))
                               (req_trans (mult (mult dfx g1) h)
                                          (mult (mult g1 dfx) h)
                                          (mult g1 (mult dfx h))
                                          (req_mult_compat (mult dfx g1) (mult g1 dfx) h h
                                                           (mult_comm dfx g1) (req_refl h))
                                          (req_sym (mult g1 (mult dfx h))
                                                   (mult (mult g1 dfx) h)
                                                   (mult_assoc g1 dfx h)))
                               (req_sym (mult f1 (mult dgx h)) (mult (mult f1 dgx) h)
                                        (mult_assoc f1 dgx h))).
      + apply plus_comm. }
  assert (HT1 : real_eq (mult f1 (req_minus g2 (plus g1 (mult dgx h))))
                    (req_minus (mult f1 v) (mult f1 (mult dgx h)))).
  { exact (req_trans (mult f1 (req_minus g2 (plus g1 (mult dgx h))))
                     (mult f1 (req_minus (req_minus g2 g1) (mult dgx h)))
                     (req_minus (mult f1 v) (mult f1 (mult dgx h)))
                     (req_mult_compat f1 f1
                                      (req_minus g2 (plus g1 (mult dgx h)))
                                      (req_minus (req_minus g2 g1) (mult dgx h))
                                      (req_refl f1)
                                      (req_minus_plus_r g2 g1 (mult dgx h)))
                     (req_mult_minus_distr_l f1 v (mult dgx h))). }
  assert (HT2 : real_eq (mult g1 (req_minus f2 (plus f1 (mult dfx h))))
                    (req_minus (mult g1 u) (mult g1 (mult dfx h)))).
  { exact (req_trans (mult g1 (req_minus f2 (plus f1 (mult dfx h))))
                     (mult g1 (req_minus (req_minus f2 f1) (mult dfx h)))
                     (req_minus (mult g1 u) (mult g1 (mult dfx h)))
                     (req_mult_compat g1 g1
                                      (req_minus f2 (plus f1 (mult dfx h)))
                                      (req_minus (req_minus f2 f1) (mult dfx h))
                                      (req_refl g1)
                                      (req_minus_plus_r f2 f1 (mult dfx h)))
                     (req_mult_minus_distr_l g1 u (mult dfx h))). }
  apply (req_trans (req_minus (mult f2 g2)
                              (plus (mult f1 g1)
                                    (mult (plus (mult dfx g1) (mult f1 dgx)) h)))
                   (req_minus (plus (mult f1 g1)
                                    (plus (mult f1 v) (plus (mult g1 u) (mult u v))))
                              (plus (mult f1 g1)
                                    (mult (plus (mult dfx g1) (mult f1 dgx)) h)))
                   (plus (mult f1 (req_minus g2 (plus g1 (mult dgx h))))
                         (plus (mult g1 (req_minus f2 (plus f1 (mult dfx h))))
                               (mult u v)))).
  - exact (req_plus_compat (mult f2 g2)
                           (plus (mult f1 g1)
                                 (plus (mult f1 v) (plus (mult g1 u) (mult u v))))
                           (opp (plus (mult f1 g1)
                                      (mult (plus (mult dfx g1) (mult f1 dgx)) h)))
                           (opp (plus (mult f1 g1)
                                      (mult (plus (mult dfx g1) (mult f1 dgx)) h)))
                           Hfg (req_refl _)).
  - apply (req_trans (req_minus (plus (mult f1 g1)
                                      (plus (mult f1 v) (plus (mult g1 u) (mult u v))))
                                 (plus (mult f1 g1)
                                       (mult (plus (mult dfx g1) (mult f1 dgx)) h)))
                     (req_minus (plus (mult f1 v) (plus (mult g1 u) (mult u v)))
                                (mult (plus (mult dfx g1) (mult f1 dgx)) h))
                     (plus (mult f1 (req_minus g2 (plus g1 (mult dgx h))))
                           (plus (mult g1 (req_minus f2 (plus f1 (mult dfx h))))
                                 (mult u v)))).
    + exact (req_minus_plus_congr (mult f1 g1)
                                  (plus (mult f1 v) (plus (mult g1 u) (mult u v)))
                                  (mult (plus (mult dfx g1) (mult f1 dgx)) h)).
    + exact (req_trans (req_minus (plus (mult f1 v) (plus (mult g1 u) (mult u v)))
                                  (mult (plus (mult dfx g1) (mult f1 dgx)) h))
                       (req_minus (plus (mult f1 v) (plus (mult g1 u) (mult u v)))
                                  (plus (mult f1 (mult dgx h)) (mult g1 (mult dfx h))))
                       (plus (mult f1 (req_minus g2 (plus g1 (mult dgx h))))
                             (plus (mult g1 (req_minus f2 (plus f1 (mult dfx h))))
                                   (mult u v)))
                       (req_plus_compat (plus (mult f1 v) (plus (mult g1 u) (mult u v)))
                                        (plus (mult f1 v) (plus (mult g1 u) (mult u v)))
                                        (opp (mult (plus (mult dfx g1) (mult f1 dgx)) h))
                                        (opp (plus (mult f1 (mult dgx h))
                                                   (mult g1 (mult dfx h))))
                                        (req_refl (plus (mult f1 v)
                                                        (plus (mult g1 u) (mult u v))))
                                        (req_opp_compat
                                           (mult (plus (mult dfx g1) (mult f1 dgx)) h)
                                           (plus (mult f1 (mult dgx h))
                                                 (mult g1 (mult dfx h)))
                                           HP))
                       (req_trans (req_minus (plus (mult f1 v) (plus (mult g1 u) (mult u v)))
                                             (plus (mult f1 (mult dgx h))
                                                   (mult g1 (mult dfx h))))
                                  (plus (req_minus (mult f1 v) (mult f1 (mult dgx h)))
                                        (plus (req_minus (mult g1 u)
                                                         (mult g1 (mult dfx h)))
                                              (mult u v)))
                                  (plus (mult f1 (req_minus g2 (plus g1 (mult dgx h))))
                                        (plus (mult g1 (req_minus f2
                                                              (plus f1 (mult dfx h))))
                                              (mult u v)))
                                  (req_minus_plus_quad (mult f1 v) (mult g1 u)
                                                       (mult u v)
                                                       (mult f1 (mult dgx h))
                                                       (mult g1 (mult dfx h)))
                                  (req_plus_compat
                                     (req_minus (mult f1 v) (mult f1 (mult dgx h)))
                                     (mult f1 (req_minus g2 (plus g1 (mult dgx h))))
                                     (plus (req_minus (mult g1 u) (mult g1 (mult dfx h)))
                                           (mult u v))
                                     (plus (mult g1 (req_minus f2
                                                           (plus f1 (mult dfx h))))
                                           (mult u v))
                                     (req_sym
                                        (mult f1 (req_minus g2 (plus g1 (mult dgx h))))
                                        (req_minus (mult f1 v) (mult f1 (mult dgx h)))
                                        HT1)
                                     (req_plus_compat
                                        (req_minus (mult g1 u) (mult g1 (mult dfx h)))
                                        (mult g1 (req_minus f2 (plus f1 (mult dfx h))))
                                        (mult u v) (mult u v)
                                        (req_sym
                                           (mult g1 (req_minus f2
                                                          (plus f1 (mult dfx h))))
                                           (req_minus (mult g1 u) (mult g1 (mult dfx h)))
                                           HT2)
                                        (req_refl (mult u v)))))).
Qed.

(* APPEND-POINT *)
End ReqAlgebraCore.

(* ============================================================ *)
(* ReqCancelMachines: cancellation engines.  The Id-carrier uniqueness          *)
(* arguments (destruct + eq_ind elimination) are unavailable on the real_eq     *)
(* face; these two lemmas rebuild them by pure algebra, after which the whole   *)
(* cancellation cluster reduces to direct field application.                    *)
(* ============================================================ *)
Section ReqCancelMachines.

(* Machine 1: injectivity of [inv_pos] (inverse of the Id-carrier              *)
(* [inv_pos_ext], used backwards); pure algebra with two-sided cancellation.    *)
Lemma req_inv_pos_cancel : forall (a b : R) (Ha : real_lt zero a) (Hb : real_lt zero b),
  real_eq (inv_pos a Ha) (inv_pos b Hb) -> real_eq a b.
Proof.
  intros a b Ha Hb Hinv.
  assert (Ha1 : real_eq a (mult (inv_pos b Hb) (mult a b))).
  { apply (req_trans a (mult one a) (mult (inv_pos b Hb) (mult a b))).
    - apply (req_sym (mult one a) a). apply req_mult_one_l.
    - apply (req_trans (mult one a) (mult (mult (inv_pos b Hb) b) a)
                       (mult (inv_pos b Hb) (mult a b))).
      + apply (req_mult_compat one (mult (inv_pos b Hb) b) a a
                               (req_trans one (mult b (inv_pos b Hb))
                                          (mult (inv_pos b Hb) b)
                                          (req_sym (mult b (inv_pos b Hb)) one
                                                   (inv_pos_correct b Hb))
                                          (mult_comm b (inv_pos b Hb)))
                               (req_refl a)).
      + apply (req_trans (mult (mult (inv_pos b Hb) b) a)
                         (mult (inv_pos b Hb) (mult b a))
                         (mult (inv_pos b Hb) (mult a b))).
        * apply (req_sym (mult (inv_pos b Hb) (mult b a))
                         (mult (mult (inv_pos b Hb) b) a)). apply mult_assoc.
        * apply (req_mult_compat (inv_pos b Hb) (inv_pos b Hb) (mult b a) (mult a b)
                                 (req_refl (inv_pos b Hb)) (mult_comm b a)). }
  assert (Hb1 : real_eq b (mult (inv_pos a Ha) (mult b a))).
  { apply (req_trans b (mult one b) (mult (inv_pos a Ha) (mult b a))).
    - apply (req_sym (mult one b) b). apply req_mult_one_l.
    - apply (req_trans (mult one b) (mult (mult (inv_pos a Ha) a) b)
                       (mult (inv_pos a Ha) (mult b a))).
      + apply (req_mult_compat one (mult (inv_pos a Ha) a) b b
                               (req_trans one (mult a (inv_pos a Ha))
                                          (mult (inv_pos a Ha) a)
                                          (req_sym (mult a (inv_pos a Ha)) one
                                                   (inv_pos_correct a Ha))
                                          (mult_comm a (inv_pos a Ha)))
                               (req_refl b)).
      + apply (req_trans (mult (mult (inv_pos a Ha) a) b)
                         (mult (inv_pos a Ha) (mult a b))
                         (mult (inv_pos a Ha) (mult b a))).
        * apply (req_sym (mult (inv_pos a Ha) (mult a b))
                         (mult (mult (inv_pos a Ha) a) b)). apply mult_assoc.
        * apply (req_mult_compat (inv_pos a Ha) (inv_pos a Ha) (mult a b) (mult b a)
                                 (req_refl (inv_pos a Ha)) (mult_comm a b)). }
  assert (Hba : real_eq b a).
  { apply (req_trans b (mult (inv_pos a Ha) (mult b a)) a).
    - exact Hb1.
    - apply (req_trans (mult (inv_pos a Ha) (mult b a))
                       (mult (inv_pos b Hb) (mult b a)) a).
      + apply (req_mult_compat (inv_pos a Ha) (inv_pos b Hb) (mult b a) (mult b a)
                               Hinv (req_refl (mult b a))).
      + apply (req_trans (mult (inv_pos b Hb) (mult b a))
                         (mult (inv_pos b Hb) (mult a b)) a).
        * apply (req_mult_compat (inv_pos b Hb) (inv_pos b Hb) (mult b a) (mult a b)
                                 (req_refl (inv_pos b Hb)) (mult_comm b a)).
        * exact (req_sym a (mult (inv_pos b Hb) (mult a b)) Ha1). }
  exact (req_sym b a Hba).
Qed.

(* Machine 2: injectivity of [log] on positives — via [log_inv_log],           *)
(* [exp_neg_log_inv] and the exp_neg compatibility fact of the world module;    *)
(* no interface assumptions beyond the displayed ones.                          *)
Lemma req_log_cancel : forall (a b : R) (Ha : real_lt zero a) (Hb : real_lt zero b),
  real_eq (log a Ha) (log b Hb) -> real_eq a b.
Proof.
  intros a b Ha Hb Hlog.
  apply (req_trans a (exp_neg (log_inv a Ha)) b).
  - apply (req_sym (exp_neg (log_inv a Ha)) a). apply exp_neg_log_inv.
  - apply (req_trans (exp_neg (log_inv a Ha)) (exp_neg (opp (log a Ha))) b).
    + apply exp_neg_req_compat_setoid.
      apply log_inv_log.
    + apply (req_trans (exp_neg (opp (log a Ha))) (exp_neg (opp (log b Hb))) b).
      * apply exp_neg_req_compat_setoid.
        apply (req_opp_compat (log a Ha) (log b Hb)). exact Hlog.
      * apply (req_trans (exp_neg (opp (log b Hb))) (exp_neg (log_inv b Hb)) b).
        -- apply exp_neg_req_compat_setoid.
           exact (req_sym (log_inv b Hb) (opp (log b Hb)) (log_inv_log b Hb)).
        -- apply exp_neg_log_inv.
Qed.

End ReqCancelMachines.

(* ============================================================ *)
(* ReqStrictOrderBridge: mixed strict/weak additive monotonicity.              *)
(* The interface fields cover strict-strict [real_lt_plus_compat] and          *)
(* weak-weak [real_le_plus_compat] only; mixed shapes carry their strict       *)
(* premises as explicit hypotheses.  The weak-conclusion variant is derived    *)
(* from the strict-strict shape by commutativity and [real_lt_compat]          *)
(* transport, adding no new assumptions.                                        *)
(* ============================================================ *)
Section ReqStrictOrderBridge.

(* Honest interface note: the interface provides only strict-strict            *)
(* [real_lt_plus_compat] and weak-weak [real_le_plus_compat] additive           *)
(* monotonicity.  The mixed strict-premise forms below keep their strict        *)
(* premises as explicit hypotheses (a constructive order admits no one-sided    *)
(* cancellation); a concrete-layer supply for one mixed shape lives in the      *)
(* world module [S07_RealSetoidExpLog].                                         *)
Hypothesis req_lt_plus_compat_lt_le :
  forall a b c d : R, real_lt a b -> real_le c d -> real_lt (plus a c) (plus b d).

(* Weak-conclusion variant: derived from the strict-strict shape by commutativity and [real_lt_compat] transport. *)
Lemma req_lt_plus_compat_le_lt :
  forall a b c d : R, real_le a b -> real_lt c d -> real_lt (plus a c) (plus b d).
Proof.
  intros a b c d Hab Hcd.
  apply (req_lt_compat (plus c a) (plus a c) (plus d b) (plus b d)
                       (plus_comm c a) (plus_comm d b)).
  exact (req_lt_plus_compat_lt_le c d a b Hcd Hab).
Qed.

End ReqStrictOrderBridge.

(* ============================================================ *)

(* Both bridges transport facts whose Id-carrier proofs use equality           *)
(* elimination (destruct / eq_ind) plus the interface field [log_inv_exp_neg];  *)
(* this interface exports no injectivity field for [exp_neg], so the general    *)
(* statements carry their displayed side hypotheses.  The Real instance         *)
(* satisfies them; a general interface extension is future work.                *)
(* ============================================================ *)
Section ReqLogBridge.

Hypothesis log_req_compat :
  forall (x y : R) (Hx : real_lt zero x) (Hy : real_lt zero y),
    real_eq x y -> real_eq (log x Hx) (log y Hy).

Hypothesis log_inv_exp_neg_req :
  forall x : R, real_eq (log_inv (exp_neg x) (exp_neg_pos x)) x.


Lemma req_log_exp_neg : forall x : R,
  real_eq (log (exp_neg x) (exp_neg_pos x)) (opp x).
Proof.
  intro x.
  apply (req_trans (log (exp_neg x) (exp_neg_pos x))
                   (opp (opp (log (exp_neg x) (exp_neg_pos x)))) (opp x)).
  - apply (req_sym (opp (opp (log (exp_neg x) (exp_neg_pos x))))
                   (log (exp_neg x) (exp_neg_pos x))). apply req_double_neg.
  - apply (req_trans (opp (opp (log (exp_neg x) (exp_neg_pos x))))
                     (opp (log_inv (exp_neg x) (exp_neg_pos x))) (opp x)).
    + apply (req_opp_compat (opp (log (exp_neg x) (exp_neg_pos x)))
                            (log_inv (exp_neg x) (exp_neg_pos x))).
      apply (req_sym (log_inv (exp_neg x) (exp_neg_pos x))
                     (opp (log (exp_neg x) (exp_neg_pos x)))). apply log_inv_log.
    + apply (req_opp_compat (log_inv (exp_neg x) (exp_neg_pos x)) x).
      apply log_inv_exp_neg_req.
Qed.


Lemma req_log_inv_one_inv : forall (x : R) (Hx : real_lt zero x),
  real_eq (log (inv_pos x Hx) (inv_pos_pos x Hx)) (opp (log x Hx)).
Proof.
  intros x Hx.
  assert (Hprod : real_eq (mult (inv_pos x Hx) x) one).
  { exact (req_trans (mult (inv_pos x Hx) x) (mult x (inv_pos x Hx)) one
                     (mult_comm (inv_pos x Hx) x) (inv_pos_correct x Hx)). }
  assert (Hl1 : real_eq (log (mult (inv_pos x Hx) x)
                         (mult_positive (inv_pos x Hx) x (inv_pos_pos x Hx) Hx))
                    zero).
  { apply (req_trans (log (mult (inv_pos x Hx) x)
                          (mult_positive (inv_pos x Hx) x (inv_pos_pos x Hx) Hx))
                     (log one one_pos) zero).
    - apply log_req_compat. exact Hprod.
    - exact (log_one one_pos). }
  apply (req_add_cancel_l (log (inv_pos x Hx) (inv_pos_pos x Hx)) (log x Hx)
                          (opp (log x Hx))).
  apply (req_trans (plus (log (inv_pos x Hx) (inv_pos_pos x Hx)) (log x Hx))
                   zero
                   (plus (opp (log x Hx)) (log x Hx))).
  - apply (req_trans (plus (log (inv_pos x Hx) (inv_pos_pos x Hx)) (log x Hx))
                     (log (mult (inv_pos x Hx) x)
                          (mult_positive (inv_pos x Hx) x (inv_pos_pos x Hx) Hx))
                     zero).
    + apply (req_sym (log (mult (inv_pos x Hx) x)
                          (mult_positive (inv_pos x Hx) x (inv_pos_pos x Hx) Hx))
                     (plus (log (inv_pos x Hx) (inv_pos_pos x Hx)) (log x Hx))).
      apply log_mult.
    + exact Hl1.
  - apply (req_sym (plus (opp (log x Hx)) (log x Hx)) zero).
    apply (req_trans (plus (opp (log x Hx)) (log x Hx))
                     (plus (log x Hx) (opp (log x Hx))) zero).
    + apply plus_comm.
    + apply plus_opp.
Qed.


Lemma req_log_div : forall (a b : R) (Ha : real_lt zero a) (Hb : real_lt zero b),
  real_eq (log (mult a (inv_pos b Hb))
           (mult_positive a (inv_pos b Hb) Ha (inv_pos_pos b Hb)))
      (req_minus (log a Ha) (log b Hb)).
Proof.
  intros a b Ha Hb. unfold req_minus.
  apply (req_trans (log (mult a (inv_pos b Hb))
                        (mult_positive a (inv_pos b Hb) Ha (inv_pos_pos b Hb)))
                   (plus (log a Ha) (log (inv_pos b Hb) (inv_pos_pos b Hb)))
                   (plus (log a Ha) (opp (log b Hb)))).
  - apply log_mult.
  - apply (req_plus_compat (log a Ha) (log a Ha)
                           (log (inv_pos b Hb) (inv_pos_pos b Hb)) (opp (log b Hb))
                           (req_refl (log a Ha)) (req_log_inv_one_inv b Hb)).
Qed.


Lemma req_log_div_neg : forall (a b : R) (Ha : real_lt zero a) (Hb : real_lt zero b),
  real_eq (log (mult a (inv_pos b Hb))
           (mult_positive a (inv_pos b Hb) Ha (inv_pos_pos b Hb)))
      (opp (log (mult b (inv_pos a Ha))
                (mult_positive b (inv_pos a Ha) Hb (inv_pos_pos a Ha)))).
Proof.
  intros a b Ha Hb.
  apply (req_trans (log (mult a (inv_pos b Hb))
                        (mult_positive a (inv_pos b Hb) Ha (inv_pos_pos b Hb)))
                   (req_minus (log a Ha) (log b Hb))
                   (opp (log (mult b (inv_pos a Ha))
                             (mult_positive b (inv_pos a Ha) Hb (inv_pos_pos a Ha))))).
  - apply req_log_div.
  - unfold req_minus.
    exact (req_trans (plus (log a Ha) (opp (log b Hb)))
                     (opp (plus (log b Hb) (opp (log a Ha))))
                     (opp (log (mult b (inv_pos a Ha))
                               (mult_positive b (inv_pos a Ha) Hb (inv_pos_pos a Ha))))
                     (req_trans (plus (log a Ha) (opp (log b Hb)))
                                (plus (opp (log b Hb)) (log a Ha))
                                (opp (plus (log b Hb) (opp (log a Ha))))
                                (plus_comm (log a Ha) (opp (log b Hb)))
                                (req_trans (plus (opp (log b Hb)) (log a Ha))
                                           (plus (opp (log b Hb))
                                                 (opp (opp (log a Ha))))
                                           (opp (plus (log b Hb) (opp (log a Ha))))
                                           (req_plus_compat (opp (log b Hb))
                                                            (opp (log b Hb))
                                                            (log a Ha)
                                                            (opp (opp (log a Ha)))
                                                            (req_refl (opp (log b Hb)))
                                                            (req_sym (opp (opp (log a Ha)))
                                                                     (log a Ha)
                                                                     (req_double_neg
                                                                        (log a Ha))))
                                           (req_sym (opp (plus (log b Hb)
                                                               (opp (log a Ha))))
                                                    (plus (opp (log b Hb))
                                                          (opp (opp (log a Ha))))
                                                    (req_opp_plus (log b Hb)
                                                                  (opp (log a Ha))))))
                     (req_opp_compat (req_minus (log b Hb) (log a Ha))
                                     (log (mult b (inv_pos a Ha))
                                          (mult_positive b (inv_pos a Ha) Hb
                                                         (inv_pos_pos a Ha)))
                                     (req_sym (log (mult b (inv_pos a Ha))
                                                   (mult_positive b (inv_pos a Ha) Hb
                                                                  (inv_pos_pos a Ha)))
                                              (req_minus (log b Hb) (log a Ha))
                                              (req_log_div b a Hb Ha)))).
Qed.

End ReqLogBridge.

(* ============================================================ *)
(* ---- Honest exclusions (statements deliberately not carried here) ---- *)
(* 1. attn_nat_to_R_pos: a nat-recursion fact about a nat -> Real embedding;    *)
(*    it does not transfer across carrier faces (the Real families differ) and  *)
(*    has no consumer in this development.                                      *)
(* 2. id_ring_demo_*: demonstration lemmas whose statements coincide exactly    *)
(*    with interface fields (real_eq_double_neg / real_eq_plus_opp_r /          *)
(*    real_eq_mult_one_r proved above); no transfer content.                    *)
(* 3. abs_plus_one_pos (|a| + 1 > 0): signature-face exclusion — its proof      *)
(*    needs the plain form [abs_nonneg : real_le zero (abs a)], while this      *)
(*    interface carries the epsilon form only, and the plain form is not        *)
(*    derivable from it (a constructive order admits no elimination).           *)
(* ============================================================ *)

Print Assumptions req_plus_inv_unique.
Print Assumptions req_plus_cancel_l.
Print Assumptions req_mult_cancel_r.
Print Assumptions req_abs_le_abs_plus_one.
