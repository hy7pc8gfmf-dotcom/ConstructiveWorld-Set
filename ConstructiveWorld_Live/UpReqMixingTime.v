(* ConstructiveWorld-Set -- explicit mixing-time constructions for contraction kernels. *)

(** * UpReqMixingTime: explicit mixing time with explicit k selection.

    Mission.  Explicit construction of the mixing-time step count k of a
      contraction kernel: given the spectral-gap ratio kappa (0 < kappa < 1),
      the deviation TV0 and an accuracy budget, a nat k with
      [tv_rpow kappa k * TV0 < budget] is built as a computable [sigT]
      witness; main statements [mix_pow_budget], [mix_k_select],
      [mix_k_compute], [mix_k_spec], [mix_bernoulli_upper], [mix_le_inv].

    Dependencies.  Stdlib [QArith.Qring], [ZArith], [Lia].  Requires
      [S01_BaseRing], [S02_CauchyComplete], [S03_QExp], [S04_RealExpLogConv],
      [S05_AlignmentGRPO], [S06_DiffSamplingGibbs], [S07_RealSetoidExpLog],
      [S08_RealMainlineDPO], [S09_EntropyReal], [S10_KVQuantTrig],
      [S11_TP3B5], [S12_B5RecycleSF], [S13_NLiveAudit], [S14_B5BatchBlock],
      [S15_TailFEPUp], [UpTVDoeblin], [UpReqIterGeomRate] of this development.

    References.  This development, UpReqMixingTime.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" UpReqMixingTime.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 000160bc]. *)
From Stdlib Require Import QArith.Qring.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
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
Require Import UpTVDoeblin.
Require Import UpReqIterGeomRate.

Local Open Scope Q_scope.

(* ============================================================ *)
(* Part 0. Ring tactic (following the [tvd_rring] pattern of UpTVDoeblin) and nat-scale sums *)
(* ============================================================ *)


(* the nat-scale iterated sum k*w: mix_scale 0 w = 0 and mix_scale (Datatypes.S k) w = w + mix_scale k w. *)
Fixpoint mix_scale (k : nat) (w : Real) : Real :=
  match k with
  | Datatypes.O => real_zero
  | Datatypes.S m => real_plus w (mix_scale m w)
  end.

Ltac mix_rring :=
  apply real_eq_of_zero_diff; intro n0;
  repeat match goal with
         | [ x : Real |- _ ] => destruct x
         end;
  cbn [projT1 real_plus real_mult real_opp real_minus_r real_one real_zero
       real_const real_of_nat mix_scale tv_omd] in *;
  (* real_eq_of_zero_diff leaves a QeqT goal; ring (Qring) expects Qeq --
     bridge first, per the real_plus_comm pattern in S02_CauchyComplete *)
  apply qeq_imp_qeqT; ring.

(* 1*x == x, the left-factor form of [real_mult_one]. *)
Lemma mix_mult_one_l : forall x : Real, real_eq (real_mult real_one x) x.
Proof.
  intro x.
  apply (real_eq_trans (real_mult real_one x) (real_mult x real_one) x).
  - exact (real_mult_comm real_one x).
  - exact (real_mult_one x).
Qed.

(* nat-scale nonnegativity: 0 <= w gives 0 <= k*w. *)
Lemma mix_scale_nonneg : forall (w : Real) (k : nat),
  real_le real_zero w -> real_le real_zero (mix_scale k w).
Proof.
  intros w k Hw. induction k as [| k IH].
  - apply (RealSetoid.real_eq_le). exact (real_eq_refl real_zero).
  - apply (real_le_trans real_zero (real_plus real_zero real_zero)
             (real_plus w (mix_scale k w))).
    + apply (RealSetoid.real_eq_le).
      exact (real_eq_sym _ _ (real_plus_zero real_zero)).
    + exact (real_le_plus_compat real_zero w real_zero
               (mix_scale k w) Hw IH).
Qed.

(* nat-scale strict positivity: 0 < w gives 0 < (Datatypes.S k)*w, since w + k*w >= w > 0. *)
Lemma mix_scale_S_pos : forall (w : Real) (k : nat),
  real_lt real_zero w -> real_lt real_zero (mix_scale (Datatypes.S k) w).
Proof.
  intros w k Hwp.
  assert (Hnn : real_le real_zero w).
  { apply (RealSetoid.real_lt_le_iff_req real_zero w). left. exact Hwp. }
  apply (RealSetoid.real_lt_id_l real_zero
           (real_plus real_zero real_zero)
           (real_plus w (mix_scale k w))).
  - apply (real_eq_sym _ _ (real_plus_zero real_zero)).
  - exact (real_lt_plus_compat_lt_le real_zero w real_zero
             (mix_scale k w) Hwp (mix_scale_nonneg w k Hnn)).
Qed.

(* ============================================================ *)
(* Part 1. Const-scale bridge: the real_arch output face (k#1) against the nat scale *)
(* ============================================================ *)

(* const zero: (0#1) == 0. *)
Lemma mix_const_zero : real_eq (real_const (Z.of_nat 0 # 1)) real_zero.
Proof. mix_rring. Qed.

(* const successor: (Datatypes.S k)#1 == (k#1) + 1, by Nat2Z.inj_succ and Q ring computation. *)
Lemma mix_const_succ : forall k : nat,
  real_eq (real_const (Z.of_nat (Datatypes.S k) # 1))
          (real_plus (real_const (Z.of_nat k # 1)) real_one).
Proof.
  intro k. apply real_eq_of_zero_diff. intro n0.
  cbn [projT1 real_const real_plus real_one real_zero] in *.
  replace (Z.of_nat (Datatypes.S k)) with ((Z.of_nat k) + 1)%Z by lia.
  (* real_eq_of_zero_diff leaves a QeqT goal; bridge to Qeq first (ring
     expects Qeq), then the 9.1-era unfold chain does the Qmake
     cross-product reduction ring needs *)
  apply qeq_imp_qeqT.
  unfold Qminus, Qeq, Qplus, Qmult, Qopp. simpl. ring.
Qed.

(* main bridge: k*w == (k#1)*w, the nat scale and the const scale agree as Real values. *)
Lemma mix_scale_eq_const : forall (k : nat) (w : Real),
  real_eq (mix_scale k w) (real_mult (real_const (Z.of_nat k # 1)) w).
Proof.
  intros k. induction k as [| k IH].
  - intro w.
    apply (real_eq_trans real_zero (real_mult real_zero w)
             (real_mult (real_const (Z.of_nat 0 # 1)) w)).
    + apply (real_eq_trans real_zero (real_mult w real_zero)
               (real_mult real_zero w)).
      * exact (real_eq_sym _ _ (real_mult_zero w)).
      * exact (real_eq_sym _ _ (real_mult_comm real_zero w)).
    + apply (RealSetoid.real_eq_mult_compat real_zero w
               (real_const (Z.of_nat 0 # 1)) w
               mix_const_zero (real_eq_refl w)).
  - intro w.
    apply (real_eq_trans (real_plus w (mix_scale k w))
             (real_plus w (real_mult (real_const (Z.of_nat k # 1)) w))).
    + apply (RealSetoid.real_eq_plus_compat w (mix_scale k w) w
               (real_mult (real_const (Z.of_nat k # 1)) w)
               (real_eq_refl w) (IH w)).
    + apply (real_eq_trans
               (real_plus w (real_mult (real_const (Z.of_nat k # 1)) w))
               (real_plus (real_mult real_one w)
                          (real_mult (real_const (Z.of_nat k # 1)) w))).
      * apply (RealSetoid.real_eq_plus_compat w
                 (real_mult (real_const (Z.of_nat k # 1)) w)
                 (real_mult real_one w)
                 (real_mult (real_const (Z.of_nat k # 1)) w)
                 (real_eq_sym _ _ (mix_mult_one_l w))
                 (real_eq_refl (real_mult (real_const (Z.of_nat k # 1)) w))).
      * apply (real_eq_trans
                 (real_plus (real_mult real_one w)
                    (real_mult (real_const (Z.of_nat k # 1)) w))
                 (real_mult (real_plus real_one
                               (real_const (Z.of_nat k # 1))) w)).
        -- exact (real_distrib_r real_one
                     (real_const (Z.of_nat k # 1)) w).
        -- apply (RealSetoid.real_eq_mult_compat
                     (real_plus real_one (real_const (Z.of_nat k # 1))) w
                     (real_const (Z.of_nat (Datatypes.S k) # 1)) w
                     (real_eq_trans
                        (real_plus real_one (real_const (Z.of_nat k # 1)))
                        (real_plus (real_const (Z.of_nat k # 1)) real_one)
                        (real_const (Z.of_nat (Datatypes.S k) # 1))
                        (real_plus_comm real_one
                           (real_const (Z.of_nat k # 1)))
                        (real_eq_sym _ _ (mix_const_succ k)))
                     (real_eq_refl w)).
Qed.

(* the nat scale distributes over the right factor: (k*x)*z == k*(x*z). *)
Lemma mix_scale_mult_distrib : forall (k : nat) (x z : Real),
  real_eq (real_mult (mix_scale k x) z) (mix_scale k (real_mult x z)).
Proof.
  intro k. induction k as [| k IH]; intros x z.
  - apply (real_eq_trans (real_mult real_zero z)
             (real_mult z real_zero) real_zero).
    + exact (real_mult_comm real_zero z).
    + exact (real_mult_zero z).
  - apply (real_eq_trans (real_mult (real_plus x (mix_scale k x)) z)
             (real_plus (real_mult x z) (real_mult (mix_scale k x) z))).
    + apply (real_eq_sym _ _ (real_distrib_r x (mix_scale k x) z)).
    + apply (RealSetoid.real_eq_plus_compat (real_mult x z)
               (real_mult (mix_scale k x) z) (real_mult x z)
               (mix_scale k (real_mult x z))
               (real_eq_refl (real_mult x z)) (IH x z)).
Qed.

(* ============================================================ *)
(* Part 2. Rate-certificate lemmas and powers *)
(* ============================================================ *)

(* delta > 0 gives 1 - delta < 1, the upper bound on [tv_omd]; dual to [tv_omd_pos_of_lt]. *)
Lemma mix_omd_lt_one : forall delta : Real,
  real_lt real_zero delta -> real_lt (tv_omd delta) real_one.
Proof.
  intros delta Hdelta.
  apply (real_lt_eq_lt (tv_omd delta)
           (real_plus (tv_omd delta) delta) real_one).
  - exact (igr_lt_plus_r (tv_omd delta) delta Hdelta).
  - mix_rring.
Qed.

(* power extensionality: equal bases give equal powers. *)
Lemma mix_rpow_eq_compat : forall (x y : Real) (k : nat),
  real_eq x y -> real_eq (tv_rpow x k) (tv_rpow y k).
Proof.
  intros x y k Hxy. induction k as [| k IH].
  - exact (real_eq_refl real_one).
  - apply (RealSetoid.real_eq_mult_compat x (tv_rpow x k) y (tv_rpow y k)
             Hxy IH).
Qed.

(* power one: a^1 == a. *)
Lemma mix_rpow_one : forall a : Real, real_eq (tv_rpow a 1) a.
Proof.
  intro a.
  exact (real_eq_trans (tv_rpow a 1) (real_mult a real_one) a           (real_eq_refl (real_mult a real_one)) (real_mult_one a)).
Qed.

(* power positivity: 0 < a gives 0 < a^k. *)
Lemma mix_rpow_pos : forall (a : Real) (k : nat),
  real_lt real_zero a -> real_lt real_zero (tv_rpow a k).
Proof.
  intros a k Ha. induction k as [| k IH].
  - exact real_lt_zero_one.
  - exact (real_mult_pos_compat a (tv_rpow a k) Ha IH).
Qed.

(* power nonnegativity: 0 <= a gives 0 <= a^k, branchwise on the Or coding. *)
Lemma mix_rpow_nonneg : forall (a : Real) (k : nat),
  real_le real_zero a -> real_le real_zero (tv_rpow a k).
Proof.
  intros a k Ha. induction k as [| k IH].
  - apply (RealSetoid.real_lt_le_iff_req real_zero real_one). left.
    exact real_lt_zero_one.
  - destruct Ha as [Halt | Haq].
    + destruct IH as [IPlt | IPeq].
      * apply (RealSetoid.real_lt_le_iff_req real_zero
                 (real_mult a (tv_rpow a k))). left.
        exact (real_mult_pos_compat a (tv_rpow a k) Halt IPlt).
      * apply (RealSetoid.real_eq_le).
        apply (real_eq_sym _ _).
        apply (real_eq_trans (real_mult a (tv_rpow a k))
                 (real_mult a real_zero) real_zero).
        -- exact (RealSetoid.real_eq_mult_compat a (tv_rpow a k) a
                    real_zero (real_eq_refl a) (real_eq_sym _ _ IPeq)).
        -- exact (real_mult_zero a).
    + apply (RealSetoid.real_eq_le).
      apply (real_eq_sym _ _).
      apply (real_eq_trans (real_mult a (tv_rpow a k))
               (real_mult real_zero (tv_rpow a k)) real_zero).
      * exact (RealSetoid.real_eq_mult_compat a (tv_rpow a k)
                 real_zero (tv_rpow a k) (real_eq_sym _ _ Haq)
                 (real_eq_refl (tv_rpow a k))).
      * apply (real_eq_trans (real_mult real_zero (tv_rpow a k))
                 (real_mult (tv_rpow a k) real_zero) real_zero).
        -- exact (real_mult_comm real_zero (tv_rpow a k)).
        -- exact (real_mult_zero (tv_rpow a k)).
Qed.

(* boost positivity: 1 + k*w > 0; 0 <= w suffices, by cases on k. *)
Lemma mix_boost_pos : forall (w : Real) (k : nat),
  real_le real_zero w ->
  real_lt real_zero (real_plus real_one (mix_scale k w)).
Proof.
  intros w k Hw. destruct k as [| k'].
  - (* case k = 0: 1 + 0 == 1 > 0. *)
    apply (real_lt_eq_lt real_zero (real_plus real_one
              (mix_scale 0 w)) real_one).
    + exact real_lt_zero_one.
    + mix_rring.
  - (* case k >= 1: 0 + 0 < 1 + (w + k'*w), from 0 < 1 and 0 <= w. *)
    apply (RealSetoid.real_lt_id_l real_zero
             (real_plus real_zero real_zero)
             (real_plus real_one (mix_scale (Datatypes.S k') w))).
    + apply (real_eq_sym _ _ (real_plus_zero real_zero)).
    + exact (real_lt_plus_compat_lt_le real_zero real_one real_zero
               (mix_scale (Datatypes.S k') w) real_lt_zero_one
               (mix_scale_nonneg w (Datatypes.S k') Hw)).
Qed.

(* generic atomic ring lemmas in the igr style: destruct all Reals, then
   simpl and ring; the unreducible variable-stalling fixpoints are bypassed by taking mix_scale k w as one atom. *)
(* multiplicative swap: (a*b)*c == b*(a*c), by a chain of eq combinators without ring. *)
Lemma mix_mult_swap : forall a b c : Real,
  real_eq (real_mult (real_mult a b) c) (real_mult b (real_mult a c)).
Proof.
  intros a b c.
  apply (real_eq_trans _ (real_mult (real_mult b a) c)).
  - apply (RealSetoid.real_eq_mult_compat (real_mult a b) c
             (real_mult b a) c (real_mult_comm a b) (real_eq_refl c)).
  - apply (real_eq_sym _ _ (real_mult_assoc b a c)).
Qed.

Lemma mix_ring_cancel : forall A C : Real,
  real_eq (real_plus (real_minus_r A C) C) A.
Proof.
  intros A C. destruct A as [a Ha]. destruct C as [c Hc].
  apply real_eq_of_zero_diff. intro n. apply qeq_imp_qeqT. simpl. ring.
Qed.

Lemma mix_ring_sc : forall u a : Real,
  real_eq
    (real_mult (real_minus_r real_one u)
       (real_plus real_one (real_plus u a)))
    (real_minus_r (real_plus real_one a)
       (real_mult (real_plus u a) u)).
Proof.
  intros u a. destruct u as [p Hp]. destruct a as [q Hq].
  apply real_eq_of_zero_diff. intro n. apply qeq_imp_qeqT. simpl. ring.
Qed.

(* double complement for omd: x == 1 - (1 - x). *)
Lemma mix_omd_id : forall x : Real,
  real_eq x (real_minus_r real_one (real_minus_r real_one x)).
Proof.
  intro x. destruct x as [r Hr].
  apply real_eq_of_zero_diff. intro n. apply qeq_imp_qeqT. simpl. ring.
Qed.

(* ============================================================ *)
(* Part 3. Bernoulli upper form without exp or log, the power-contraction kernel: *)
(*   (1-w)^k * (1 + k*w) <= 1 for 0 < w < 1 *)
(* ============================================================ *)

Lemma mix_bernoulli_upper : forall (w : Real) (k : nat),
  real_le real_zero w -> real_lt real_zero w -> real_le w real_one ->
  real_lt w real_one ->
  real_le (real_mult (tv_rpow (real_minus_r real_one w) k)
                     (real_plus real_one (mix_scale k w)))
          real_one.
Proof.
  intros w k Hw0 Hwp Hw1 Hwlt. induction k as [| k IH].
  - (* case k = 0: 1 * (1 + 0) == 1. *)
    apply (RealSetoid.real_eq_le).
    apply (real_eq_trans
             (real_mult real_one (real_plus real_one (mix_scale 0 w)))
             (real_mult real_one real_one)).
    + apply (RealSetoid.real_eq_mult_compat real_one
               (real_plus real_one (mix_scale 0 w)) real_one real_one
               (real_eq_refl real_one) (real_plus_zero real_one)).
    + exact (real_mult_one real_one).
  - (* inductive step: ring computation rewrites (1-w)*(1+(k+1)*w) as
       (1+k*w) - ((k+1)*w)*w; the subclaim bounds it by 1+k*w, and the positive power Pk connects the estimate to IH. *)
    assert (Hbpos : real_lt real_zero (real_minus_r real_one w))
      by exact (tv_omd_pos_of_lt w Hwlt).
    assert (HPk : real_lt real_zero (tv_rpow (real_minus_r real_one w) k))
      by exact (mix_rpow_pos (real_minus_r real_one w) k Hbpos).
    assert (HC : real_lt real_zero (real_mult (mix_scale (Datatypes.S k) w) w))
      by exact (real_mult_pos_compat (mix_scale (Datatypes.S k) w) w
                 (mix_scale_S_pos w k Hwp) Hwp).
    assert (HeqSC : real_eq
              (real_mult (real_minus_r real_one w)
                 (real_plus real_one (mix_scale (Datatypes.S k) w)))
              (real_minus_r (real_plus real_one (mix_scale k w))
                 (real_mult (mix_scale (Datatypes.S k) w) w)))
      by exact (mix_ring_sc w (mix_scale k w)).
    assert (HSC : real_le
              (real_mult (real_minus_r real_one w)
                 (real_plus real_one (mix_scale (Datatypes.S k) w)))
              (real_plus real_one (mix_scale k w))).
    { apply (real_le_trans _
               (real_minus_r (real_plus real_one (mix_scale k w))
                  (real_mult (mix_scale (Datatypes.S k) w) w))).
      - apply (RealSetoid.real_eq_le). exact HeqSC.
      - apply (real_le_trans _
                 (real_plus (real_minus_r (real_plus real_one (mix_scale k w))
                               (real_mult (mix_scale (Datatypes.S k) w) w))
                            (real_mult (mix_scale (Datatypes.S k) w) w))).
        + exact (igr_le_plus_r _ _ HC).
        + apply (RealSetoid.real_eq_le).
          exact (mix_ring_cancel _ _). }
    assert (HeqR : real_eq
              (real_mult (real_mult (real_minus_r real_one w)
                           (tv_rpow (real_minus_r real_one w) k))
                        (real_plus real_one (mix_scale (Datatypes.S k) w)))
              (real_mult (real_mult (real_minus_r real_one w)
                              (real_plus real_one (mix_scale (Datatypes.S k) w)))
                         (tv_rpow (real_minus_r real_one w) k)))
      by exact (real_eq_trans
                  (real_mult (real_mult (real_minus_r real_one w)
                               (tv_rpow (real_minus_r real_one w) k))
                        (real_plus real_one (mix_scale (Datatypes.S k) w)))
                  (real_mult (tv_rpow (real_minus_r real_one w) k)
                     (real_mult (real_minus_r real_one w)
                        (real_plus real_one (mix_scale (Datatypes.S k) w))))
                  (real_mult (real_mult (real_minus_r real_one w)
                               (real_plus real_one
                                  (mix_scale (Datatypes.S k) w)))
                        (tv_rpow (real_minus_r real_one w) k))
                  (mix_mult_swap (real_minus_r real_one w)
                     (tv_rpow (real_minus_r real_one w) k)
                     (real_plus real_one (mix_scale (Datatypes.S k) w)))
                  (real_mult_comm (tv_rpow (real_minus_r real_one w) k)
                     (real_mult (real_minus_r real_one w)
                        (real_plus real_one (mix_scale (Datatypes.S k) w))))).
    assert (IH' : real_le
              (real_mult (real_plus real_one (mix_scale k w))
                         (tv_rpow (real_minus_r real_one w) k))
              real_one).
    { apply (real_le_trans _
               (real_mult (tv_rpow (real_minus_r real_one w) k)
                          (real_plus real_one (mix_scale k w)))).
      - apply (RealSetoid.real_eq_le). exact (real_mult_comm _ _).
      - exact IH. }
    apply (real_le_trans
             (real_mult (real_mult (real_minus_r real_one w)
                          (tv_rpow (real_minus_r real_one w) k))
                   (real_plus real_one (mix_scale (Datatypes.S k) w)))
             (real_mult (real_plus real_one (mix_scale k w))
                (tv_rpow (real_minus_r real_one w) k))
             real_one).
    + apply (real_le_trans _
               (real_mult (real_mult (real_minus_r real_one w)
                              (real_plus real_one (mix_scale (Datatypes.S k) w)))
                          (tv_rpow (real_minus_r real_one w) k))).
      * apply (RealSetoid.real_eq_le). exact HeqR.
      * exact (real_le_mult_compat
                 (real_mult (real_minus_r real_one w)
                    (real_plus real_one (mix_scale (Datatypes.S k) w)))
                 (real_plus real_one (mix_scale k w))
                 (tv_rpow (real_minus_r real_one w) k) HPk HSC).
    + exact IH'.
Qed.

(* ============================================================ *)
(* Part 4. Inverse branch: A*B <= 1 and 0 < B give A <= 1/B *)
(* ============================================================ *)

Lemma mix_le_inv : forall (A B : Real) (HB : real_lt real_zero B),
  real_le (real_mult A B) real_one -> real_le A (real_inv_pos B HB).
Proof.
  intros A B HB HAB.
  assert (HBp : real_lt real_zero (real_inv_pos B HB))
    by exact (real_inv_pos_pos B HB).
  assert (HeqA : real_eq A
              (real_mult (real_mult A B) (real_inv_pos B HB))).
  { apply (real_eq_trans A (real_mult A real_one)).
    - apply (real_eq_sym _ _ (real_mult_one A)).
    - apply (real_eq_trans (real_mult A real_one)
               (real_mult A (real_mult B (real_inv_pos B HB)))).
      + apply (RealSetoid.real_eq_mult_compat A real_one A
                 (real_mult B (real_inv_pos B HB)) (real_eq_refl A)
                 (real_eq_sym _ _ (real_inv_pos_correct B HB))).
      + exact (real_mult_assoc A B (real_inv_pos B HB)). }
  apply (real_le_trans A
           (real_mult (real_mult A B) (real_inv_pos B HB))
           (real_inv_pos B HB)).
  - apply (RealSetoid.real_eq_le). exact HeqA.
  - apply (real_le_trans _ (real_mult real_one (real_inv_pos B HB))).
    + exact (real_le_mult_compat (real_mult A B) real_one
               (real_inv_pos B HB) HBp HAB).
    + apply (RealSetoid.real_eq_le).
      apply (real_eq_trans (real_mult real_one (real_inv_pos B HB))
               (real_mult (real_inv_pos B HB) real_one)).
      * exact (real_mult_comm real_one (real_inv_pos B HB)).
      * exact (real_mult_one (real_inv_pos B HB)).
Qed.

(* ============================================================ *)
(* Part 5. The k-selection main theorem mix_pow_budget *)
(* ============================================================ *)

Theorem mix_pow_budget : forall (kappa TV0 budget : Real),
  real_lt real_zero kappa -> real_lt kappa real_one ->
  real_lt real_zero TV0 -> real_lt real_zero budget ->
  sigT (fun k : nat => real_lt (real_mult (tv_rpow kappa k) TV0) budget).
Proof.
  intros kappa TV0 budget Hk1 Hk2 Ha Hbudget.
  assert (hwp : real_lt real_zero (real_minus_r real_one kappa))
    by exact (tv_omd_pos_of_lt kappa Hk2).
  assert (hw1 : real_le kappa real_one).
  { apply (RealSetoid.real_lt_le_iff_req kappa real_one). left.
    exact Hk2. }
  assert (hw0 : real_le real_zero (real_minus_r real_one kappa))
    by exact (tv_omd_nonneg kappa hw1).
  assert (hwlt : real_lt (real_minus_r real_one kappa) real_one)
    by exact (mix_omd_lt_one kappa Hk1).
  assert (Heqk : real_eq kappa
              (real_minus_r real_one (real_minus_r real_one kappa)))
    by exact (mix_omd_id kappa).
  assert (Hwb : real_lt real_zero
              (real_mult (real_minus_r real_one kappa) budget))
    by exact (real_mult_pos_compat (real_minus_r real_one kappa) budget
                hwp Hbudget).
  destruct (real_arch (real_mult TV0
             (real_inv_pos (real_mult (real_minus_r real_one kappa) budget)
                Hwb))) as [N [Hge2 HN]].
  destruct N as [| N'].
  (* NatLe is the Set carrier face; lia reads only nat arithmetic --
     drop the carrier to its nat face per the NatLe_drop read face in S01 *)
  - exfalso. assert (Hge : (2 <= 0)%nat) by exact (NatLe_drop 2 0 Hge2). lia.
  - set (w := real_minus_r real_one kappa) in *.
    set (wb := real_mult w budget) in *.
    set (Ms := mix_scale (Datatypes.S N') w) in *.
    set (boost := real_plus real_one Ms) in *.
    set (invwb := real_inv_pos wb Hwb).
    set (mR := real_const (Z.of_nat (Datatypes.S N') # 1)).
    assert (HMs : real_lt real_zero Ms)
      by exact (mix_scale_S_pos w N' hwp).
    assert (HMsnn : real_le real_zero Ms).
    { apply (RealSetoid.real_lt_le_iff_req real_zero Ms). left.
      exact HMs. }
    assert (Hboost0 : real_lt real_zero boost)
      by exact (mix_boost_pos w (Datatypes.S N') hw0).
    assert (HinvB : real_lt real_zero (real_inv_pos boost Hboost0))
      by exact (real_inv_pos_pos boost Hboost0).
    (* budget branch: TV0 < budget*boost. *)
    assert (Hstep : real_lt (real_mult (real_mult TV0 invwb) wb)
                         (real_mult mR wb))
      by exact (real_mult_lt_compat _ _ _ HN Hwb).
    assert (HeqL : real_eq (real_mult (real_mult TV0 invwb) wb) TV0).
    { apply (real_eq_trans _ (real_mult wb (real_mult TV0 invwb))).
      - exact (real_mult_comm _ _).
      - exact (real_mult_div wb TV0 Hwb). }
    assert (HeqR : real_eq (real_mult mR wb) (real_mult Ms budget)).
    { apply (real_eq_trans _ (mix_scale (Datatypes.S N') wb)).
      - apply (real_eq_sym _ _ (mix_scale_eq_const (Datatypes.S N') wb)).
      - apply (real_eq_sym _ _ (mix_scale_mult_distrib (Datatypes.S N') w budget)). }
    assert (Hb0 : real_lt TV0 (real_mult Ms budget)).
    { exact (real_lt_eq_lt TV0 (real_mult mR wb) (real_mult Ms budget)
               (real_eq_lt_lt TV0 (real_mult (real_mult TV0 invwb) wb)
                  (real_mult mR wb) (real_eq_sym _ _ HeqL) Hstep)
               HeqR). }
    assert (HeqBud : real_eq (real_mult budget boost)
                         (real_plus budget (real_mult Ms budget))).
    { apply (real_eq_trans _
               (real_plus (real_mult budget real_one)
                  (real_mult budget Ms))).
      - exact (real_distrib budget real_one Ms).
      - apply (RealSetoid.real_eq_plus_compat (real_mult budget real_one)
                 (real_mult budget Ms) budget (real_mult Ms budget)
                 (real_mult_one budget) (real_mult_comm budget Ms)). }
    assert (Hbud : real_lt TV0 (real_mult budget boost)).
    { apply (real_lt_eq_lt TV0 (real_plus (real_mult Ms budget) budget)
               (real_mult budget boost)).
      - exact (real_lt_le_trans TV0 (real_mult Ms budget)
                 (real_plus (real_mult Ms budget) budget) Hb0
                 (igr_le_plus_r (real_mult Ms budget) budget Hbudget)).
      - exact (real_eq_trans (real_plus (real_mult Ms budget) budget)
                 (real_plus budget (real_mult Ms budget))
                 (real_mult budget boost)
                 (real_plus_comm (real_mult Ms budget) budget)
                 (real_eq_sym _ _ HeqBud)).
    }
    exists (Datatypes.S N').
    (* main chain: kappa^(Datatypes.S N') * TV0 < budget. *)
    assert (Heqp : real_eq (tv_rpow kappa (Datatypes.S N'))
              (tv_rpow (real_minus_r real_one w) (Datatypes.S N')))
      by exact (mix_rpow_eq_compat kappa (real_minus_r real_one w)
                  (Datatypes.S N') Heqk).
    assert (hw1w : real_le w real_one).
    { apply (RealSetoid.real_lt_le_iff_req w real_one). left.
      exact hwlt. }
    assert (Hbern : real_le
              (real_mult (tv_rpow (real_minus_r real_one w) (Datatypes.S N')) boost)
              real_one)
      by exact (mix_bernoulli_upper w (Datatypes.S N') hw0 hwp hw1w hwlt).
    assert (Hinvleg : real_le
              (tv_rpow (real_minus_r real_one w) (Datatypes.S N'))
              (real_inv_pos boost Hboost0))
      by exact (mix_le_inv _ _ Hboost0 Hbern).
    apply (real_le_lt_trans _ (real_mult (real_inv_pos boost Hboost0) TV0)
             budget).
    + apply (real_le_trans _
               (real_mult (tv_rpow (real_minus_r real_one w) (Datatypes.S N')) TV0)).
        * apply (RealSetoid.real_eq_le).
          exact (RealSetoid.real_eq_mult_compat
                   (tv_rpow kappa (Datatypes.S N')) TV0
                   (tv_rpow (real_minus_r real_one w) (Datatypes.S N'))
                   TV0 Heqp (real_eq_refl TV0)).
        * exact (real_le_mult_compat
                   (tv_rpow (real_minus_r real_one w) (Datatypes.S N'))
                   (real_inv_pos boost Hboost0) TV0 Ha Hinvleg).
    + apply (real_eq_lt_lt _ _ _ (real_mult_comm _ _)).
      apply (real_lt_eq_lt _
               (real_mult (real_mult budget boost)
                  (real_inv_pos boost Hboost0))).
        * exact (real_mult_lt_compat TV0 (real_mult budget boost)
                  (real_inv_pos boost Hboost0) Hbud HinvB).
        * apply (real_eq_trans _
                 (real_mult (real_mult boost budget)
                            (real_inv_pos boost Hboost0))).
          -- apply (RealSetoid.real_eq_mult_compat
                   (real_mult budget boost) (real_inv_pos boost Hboost0)
                   (real_mult boost budget) (real_inv_pos boost Hboost0)
                   (real_mult_comm budget boost) (real_eq_refl _)).
          -- apply (real_eq_trans (real_mult (real_mult boost budget)
                              (real_inv_pos boost Hboost0))
                   (real_mult boost (real_mult budget
                        (real_inv_pos boost Hboost0)))).
            ++ apply (real_eq_sym _ _ (real_mult_assoc boost budget
                          (real_inv_pos boost Hboost0))).
            ++ exact (real_mult_div boost budget Hboost0).
Defined.

(* ============================================================ *)
(* Part 6. The nonnegative-TV0 relaxation mix_k_select and its le form *)
(* ============================================================ *)

Theorem mix_k_select : forall (kappa TV0 budget : Real),
  real_lt real_zero kappa -> real_lt kappa real_one ->
  real_le real_zero TV0 -> real_lt real_zero budget ->
  sigT (fun k : nat => real_lt (real_mult (tv_rpow kappa k) TV0) budget).
Proof.
  intros kappa TV0 budget Hk1 Hk2 Ha Hbudget.
  unfold real_le in Ha.
  destruct Ha as [Ha | Haq].
  - exact (mix_pow_budget kappa TV0 budget Hk1 Hk2 Ha Hbudget).
  - exists 0%nat.
    apply (real_eq_lt_lt (real_mult (tv_rpow kappa 0) TV0) real_zero budget).
    + apply (real_eq_trans (real_mult (tv_rpow kappa 0) TV0)
               (real_mult real_one TV0) real_zero).
      * exact (RealSetoid.real_eq_mult_compat (tv_rpow kappa 0) TV0
                 real_one TV0 (real_eq_refl real_one) (real_eq_refl TV0)).
      * exact (real_eq_trans (real_mult real_one TV0) TV0 real_zero
                 (mix_mult_one_l TV0) (real_eq_sym _ _ Haq)).
    + exact Hbudget.
Defined.

Corollary mix_k_select_le : forall (kappa TV0 budget : Real),
  real_lt real_zero kappa -> real_lt kappa real_one ->
  real_le real_zero TV0 -> real_lt real_zero budget ->
  sigT (fun k : nat => real_le (real_mult (tv_rpow kappa k) TV0) budget).
Proof.
  intros kappa TV0 budget Hk1 Hk2 Ha Hbudget.
  destruct (mix_k_select kappa TV0 budget Hk1 Hk2 Ha Hbudget) as [k Hk].
  exists k.   apply (RealSetoid.real_lt_le_iff_req). left. exact Hk.
Defined.

(* ============================================================ *)
(* Part 6.5. Witness/certificate separation for extraction efficiency: with *)
(*   mix_pow_budget and mix_k_select closed by Defined, extraction would *)
(*   force the mix_bernoulli_upper inductive certificate chain (Set-level *)
(*   real_le of length k, binding the Real constructions of tv_rpow *)
(*   through the cauchy modulus) at run time, with blowup.  The witness *)
(*   (a purely computational k) is separated from the opaque Qed *)
(*   certificate; no new axioms: *)
(*   - mix_k_compute, a transparent Definition, runs only the real_arch *)
(*     enumeration (cheap at the Q layer): no tv_rpow, no mix_bernoulli_upper, *)
(*     so the extracted program pays only real_arch plus the basic Real *)
(*     operations real_minus_r, real_mult, real_inv_pos; *)
(*   - mix_k_spec, an opaque Qed proof, carries the full kappa^k * TV0 < budget *)
(*     certificate via mix_pow_budget; mix_k_select_r1 packages the pair as *)
(*     existT, with mix_k_select_r1_projT1 fixing the projT1 reduction. *)
(* ============================================================ *)

Definition mix_k_compute (kappa TV0 budget : Real)
  (Hk1 : real_lt real_zero kappa) (Hk2 : real_lt kappa real_one)
  (Hbudget : real_lt real_zero budget) : nat :=
  let w := real_minus_r real_one kappa in
  let wb := real_mult w budget in
  let Hwb := real_mult_pos_compat w budget (tv_omd_pos_of_lt kappa Hk2) Hbudget in
  let (n, _) := real_arch (real_mult TV0 (real_inv_pos wb Hwb)) in n.

(* witness-coherence lemma: the k computed by mix_k_compute and the k certified
   by mix_pow_budget both originate from the first projection of the same
   real_arch sigT; after the dead branch of destruct N is discharged, the
   survivor has successor shape and coincides with the bare arch witness
   (the 0 branch is excluded by the dead 2 <= n premise); real_arch is opaque
   under Qed, so the two are not definitionally equal and mix_k_spec reuses
   the certificate through this lemma. *)
Theorem mix_k_compute_eq_pow_budget (kappa TV0 budget : Real)
  (Hk1 : real_lt real_zero kappa) (Hk2 : real_lt kappa real_one)
  (Ha : real_lt real_zero TV0) (Hbudget : real_lt real_zero budget) :
  mix_k_compute kappa TV0 budget Hk1 Hk2 Hbudget
  = projT1 (mix_pow_budget kappa TV0 budget Hk1 Hk2 Ha Hbudget).
Proof.
  unfold mix_k_compute, mix_pow_budget.
  cbv zeta.
  destruct (real_arch (real_mult TV0
             (real_inv_pos (real_mult (real_minus_r real_one kappa) budget)
                (real_mult_pos_compat (real_minus_r real_one kappa) budget
                   (tv_omd_pos_of_lt kappa Hk2) Hbudget)))) as [n [Hge2 Hn]].
  destruct n as [| m].
  (* NatLe is the Set carrier face; lia reads only nat arithmetic --
     drop the carrier to its nat face per the NatLe_drop read face in S01 *)
  - exfalso. assert (Hge : (2 <= 0)%nat) by exact (NatLe_drop 2 0 Hge2). lia.
  - reflexivity.
Qed.

Theorem mix_k_spec (kappa TV0 budget : Real)
  (Hk1 : real_lt real_zero kappa) (Hk2 : real_lt kappa real_one)
  (Ha : real_lt real_zero TV0) (Hbudget : real_lt real_zero budget) :
  real_lt (real_mult (tv_rpow kappa (mix_k_compute kappa TV0 budget Hk1 Hk2 Hbudget)) TV0) budget.
Proof.
  rewrite (mix_k_compute_eq_pow_budget kappa TV0 budget Hk1 Hk2 Ha Hbudget).
  exact (projT2 (mix_pow_budget kappa TV0 budget Hk1 Hk2 Ha Hbudget)).
Qed.

Definition mix_k_select_r1 (kappa TV0 budget : Real)
  (Hk1 : real_lt real_zero kappa) (Hk2 : real_lt kappa real_one)
  (Ha : real_lt real_zero TV0) (Hbudget : real_lt real_zero budget) :
  sigT (fun k : nat => real_lt (real_mult (tv_rpow kappa k) TV0) budget) :=
  existT _ (mix_k_compute kappa TV0 budget Hk1 Hk2 Hbudget)
         (mix_k_spec kappa TV0 budget Hk1 Hk2 Ha Hbudget).

(* reduction fix: projT1 of mix_k_select_r1 equals mix_k_compute; the
   opaque second component does not affect the projT1 reduction. *)
Theorem mix_k_select_r1_projT1 (kappa TV0 budget : Real)
  (Hk1 : real_lt real_zero kappa) (Hk2 : real_lt kappa real_one)
  (Ha : real_lt real_zero TV0) (Hbudget : real_lt real_zero budget) :
  projT1 (mix_k_select_r1 kappa TV0 budget Hk1 Hk2 Ha Hbudget)
  = mix_k_compute kappa TV0 budget Hk1 Hk2 Hbudget.
Proof. reflexivity. Qed.

Print Assumptions mix_k_compute.
Print Assumptions mix_k_spec.
Print Assumptions mix_k_select_r1.

(* ============================================================ *)
(* Part 7-8 (mix_time_explicit / mix_k_calc), pending items.  The sign case
   split of mix_time_explicit needs an inhabitant of the Or-Set
   real_le real_zero TV0, which the base layer cannot decide constructively;
   it must be carried explicitly by the interface or recast in B-form.  The
   full draft (a Section MixingTV over 9+1 variables, assembled from
   tv_doeblin_iter and mix_pow_budget, with the delta = 1 and TV0 = 0
   branches closed by k := 1 and a Defined mix_k_calc calculator) is
   deferred until the interface is extended. *)
(* ============================================================ *)

(* ============================================================ *)
(* Audit: Print Assumptions trail, all expected Closed *)
(* ============================================================ *)

Print Assumptions mix_pow_budget.
Print Assumptions mix_k_select.
Print Assumptions mix_k_select_le.

Print Assumptions mix_rpow_one.
