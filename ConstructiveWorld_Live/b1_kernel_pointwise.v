(* ConstructiveWorld-Set — pointwise decay bounds for the arctan kernel
   with rational short certificates. *)

(** * b1_kernel_pointwise: rational pointwise bounds for the arctan kernel.

    Mission. The Beukers-arctan kernel [x * (1 - x) / (1 + x * x)] is
    dominated pointwise by [1/4] and by [5/24] via completed-square
    certificates [(5 * x - 2)^2 + 1 >= 1] and [(29 * x - 12)^2 + 1 >= 1],
    with the power lift [b1_kernel_pow_le24], the positivity lemma
    [b1_kernel_pos], and anchors at [x = 1/2], [x = 2/5] and
    [5/24 - 6/29 = 1/696].

    Dependencies. Stdlib [QArith.QArith], [QArith.Qabs], [ZArith.ZArith],
    [Setoid], [Morphisms], [Qfield]; requires [S01_BaseRing],
    [S02_CauchyComplete], [S03_QExp] of this development.

    References. ConstructiveWorld-Main ConstructiveWorld_Live/
    b1_kernel_pointwise.v, whose statement names are carried over here
    verbatim (statement-face Set-carrier completion).

    Constructivity. All statements are carried by [Set] ([QltT], [QleT'],
    [QeqT]); equality certificates close by [ring] and anchors by
    computation; [Obj.magic] = 0 and a [coqchk] run reports a closed
    global context.

    Build. [rocq c -native-compiler no -q -Q . "" b1_kernel_pointwise.v]
    compiles cleanly (exit 0); artifact magic [436f7121 00015ff4]. *)

From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith Arith.Arith.
From Stdlib Require Import Setoid Morphisms Qfield.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.

Open Scope Q_scope.

(* ========== Section 0. Micro toolkit: bridges from Stdlib and S02 ========== *)

(* Weaken [QleT] to [QleT']; [QleT] is [Or QltT (Id x y)] and no direct
   weakening bridge exists in S02, so this one is local. *)
Lemma b1_qleT_imp_qle : forall x y : Q, QleT x y -> QleT' x y.
Proof.
  intros x y H. destruct H as [Hlt | Heq].
  - exact (qltT_leT' _ _ Hlt).
  - rewrite Heq. apply qleT'_refl.
Qed.

(* [x <= 1] implies [0 <= 1 - x]. *)
Lemma b1_sub_ge0 : forall x : Q, QleT' x 1 -> QleT' 0 (1 - x).
Proof.
  intros x Hx1. apply Qle_to_QleT'.
  setoid_replace (1 - x)%Q with ((- x) + 1)%Q by ring.
  replace 0%Q with ((-1) + 1)%Q by reflexivity.
  apply (Qplus_le_compat (-1) (- x) 1 1).
  - exact (Qopp_le_compat x 1 (QleT'_to_Qle _ _ Hx1)).
  - apply Qle_refl.
Qed.

(* [0 < 1] holds by computation. *)
Lemma b1_0lt1 : QltT 0 1.
Proof. apply Qlt_to_QltT. unfold Qlt. reflexivity. Qed.

(* The inverse of a positive number is positive. *)
Lemma b1_inv_pos : forall D : Q, Qlt 0 D -> QltT 0 (/ D).
Proof. intros D HD. apply Qlt_to_QltT. apply Qinv_lt_0_compat. exact HD. Qed.

(* Squares are nonnegative at the [Z] layer, the load-bearing step for the
   [Q]-level statement. *)
Lemma b1_zsq_nonneg : forall z : Z, Id (Z.leb 0 (z * z)) true.
Proof.
  intro z. destruct z as [| p | p]; vm_compute; apply id_refl.
Qed.

(* Squares are nonnegative at the [Q] layer, shared by both certificates;
   [Qle] unfolds to a [Z] cross-product comparison read off directly. *)
Lemma b1_qsq_nonneg : forall z : Q, QleT' 0 (z * z).
Proof.
  intro z. apply Qle_to_QleT'.
  unfold Qle, Qmult, Qnum, Qden, Qinv, Qminus. simpl.
  destruct z as [zn zd]. cbn.
  rewrite Z.mul_1_r.
  destruct zn as [| p | p]; cbn;
    [ apply Z.le_refl | apply Zle_0_pos | apply Zle_0_pos ].
Qed.

(* [1 + x * x > 0] holds unconditionally. *)
Lemma b1_den_pos : forall x : Q, QltT 0 (1 + x * x).
Proof.
  intro x. apply Qlt_to_QltT. apply (Qlt_le_trans 0 1 (1 + x * x)).
  - exact (QltT_to_Qlt _ _ b1_0lt1).
  - assert (H1 : Qle (1 + 0) (1 + x * x))
      by (apply (proj2 (Qplus_le_r 0 (x * x) 1));
          exact (QleT'_to_Qle _ _ (b1_qsq_nonneg x))).
    replace (1 + 0)%Q with 1%Q in H1 by reflexivity.
    exact H1.
Qed.

(* [z * z + 1 > 0] and [1 <= z * z + 1]. *)
Lemma b1_qsq_plus1_pos : forall z : Q, QltT 0 (z * z + 1).
Proof.
  intro z. apply Qlt_to_QltT. apply (Qle_lt_trans 0 (z * z) (z * z + 1)).
  - exact (QleT'_to_Qle _ _ (b1_qsq_nonneg z)).
  - assert (H2 : Qlt (z * z + 0) (z * z + 1))
      by (apply (proj2 (Qplus_lt_r 0 1 (z * z)));
          exact (QltT_to_Qlt _ _ b1_0lt1)).
    setoid_replace (z * z + 0)%Q with (z * z)%Q in H2 by ring.
    exact H2.
Qed.

Lemma b1_qsq_plus1_ge1 : forall z : Q, QleT' 1 (z * z + 1).
Proof.
  intro z. apply Qle_to_QleT'.
  assert (H1 : Qle (1 + 0) (1 + z * z))
    by (apply (proj2 (Qplus_le_r 0 (z * z) 1));
        exact (QleT'_to_Qle _ _ (b1_qsq_nonneg z))).
  replace (1 + 0)%Q with 1%Q in H1 by reflexivity.
  setoid_replace (1 + z * z)%Q with (z * z + 1)%Q in H1 by ring.
  exact H1.
Qed.

(* [A - B > 0] implies [B < A]. *)
Lemma b1_pos_diff_lt : forall A B : Q, Qlt 0 (A - B) -> QltT B A.
Proof.
  intros A B H. apply Qlt_to_QltT. apply (proj2 (Qlt_minus_iff B A)).
  setoid_replace (A + - B)%Q with (A - B)%Q by (unfold Qminus; ring).
  exact H.
Qed.

(* Kernel numerator nonnegative: [0 <= x <= 1] implies
   [0 <= x * (1 - x)]. *)
Lemma b1_kernel_num_nonneg : forall x : Q,
  QleT 0 x -> QleT' x 1 -> QleT' 0 (x * (1 - x)).
Proof.
  intros x Hx0 Hx1. apply Qle_to_QleT'.
  apply (Qmult_le_0_compat x (1 - x)).
  - exact (QleT'_to_Qle _ _ (b1_qleT_imp_qle _ _ Hx0)).
  - exact (QleT'_to_Qle _ _ (b1_sub_ge0 x Hx1)).
Qed.

(* Kernel numerator strictly positive on the open interval. *)
Lemma b1_kernel_num_pos : forall x : Q,
  QltT 0 x -> QltT x 1 -> QltT 0 (x * (1 - x)).
Proof.
  intros x Hx0 Hx1. apply Qlt_to_QltT.
  apply Qmult_lt_0_compat.
  - exact (QltT_to_Qlt _ _ Hx0).
  - assert (Hn : Qlt 0 (1 - x)).
    { apply (proj1 (Qlt_minus_iff x 1)). exact (QltT_to_Qlt _ _ Hx1). }
    exact Hn.
Qed.

(* ========== Section 1. First certificate: [1/4] by completed square ========== *)

(* Denominator-clearing identity
   [5 * ((1 + x^2) - 4 * x * (1 - x)) = (5 * x - 2)^2 + 1]
   (a [ring] equality certificate). *)
Lemma b1_kernel_margin_eq4 : forall x : Q,
  QeqT (5 * ((1 + x * x) - 4 * (x * (1 - x))))%Q
       ((5 * x - 2) * (5 * x - 2) + 1)%Q.
Proof.
  intro x. apply qeq_imp_qeqT. ring.
Qed.

(* Pointwise strict domination [4 * x * (1 - x) < 1 + x^2], unconditional
   in [x]. *)
Theorem b1_kernel_pointwise_lt4 : forall x : Q,
  QltT (4 * (x * (1 - x))) (1 + x * x).
Proof.
  intro x.
  set (D := ((1 + x * x) - 4 * (x * (1 - x)))%Q).
  set (S := ((5 * x - 2) * (5 * x - 2) + 1)%Q).
  assert (Hme : 5 * D == S) by (apply (qeqT_imp_qeq _ _ (b1_kernel_margin_eq4 x))).
  assert (Hge : Qle 1 S) by exact (QleT'_to_Qle _ _ (b1_qsq_plus1_ge1 (5 * x - 2))).
  (* Multiply [1 <= S] by [1/5] and fold: [5 * D * (1/5) == D]. *)
  assert (H21 : Qle (1 * (1 # 5)) (S * (1 # 5))).
  { apply (Qmult_le_compat_r 1 S (1 # 5)).
    - exact Hge.
    - apply Qlt_le_weak. exact (QltT_to_Qlt _ _ b1_0lt1). }
  setoid_replace (1 * (1 # 5))%Q with (1 # 5)%Q in H21 by ring.
  rewrite <- Hme in H21.
  setoid_replace (5 * D * (1 # 5))%Q with D%Q in H21 by ring.
  assert (HD : Qlt 0 D).
  { apply (Qlt_le_trans 0 (1 # 5) D).
    - exact (QltT_to_Qlt _ _ b1_0lt1). - exact H21. }
  exact (b1_pos_diff_lt (1 + x * x) (4 * (x * (1 - x))) HD).
Qed.

(* Ratio face of the first certificate:
   [x * (1 - x) / (1 + x^2) <= 1/4] on [0 <= x <= 1]. *)
Theorem b1_kernel_ratio_le4 : forall x : Q,
  QleT 0 x -> QleT' x 1 ->
  QleT' ((x * (1 - x)) / (1 + x * x)) (1 # 4).
Proof.
  intros x Hx0 Hx1.
  pose proof (b1_den_pos x) as Hden.
  pose proof (QltT_to_Qlt _ _ (b1_kernel_pointwise_lt4 x)) as Hpt.
  (* From [4 * num < den] conclude [num <= den * (1/4)]. *)
  assert (Hstep1 : Qle (x * (1 - x)) ((1 + x * x) * (1 # 4))).
  { pose proof (Qmult_le_compat_r (4 * (x * (1 - x))) (1 + x * x) (1 # 4)
                  (Qlt_le_weak _ _ Hpt) (Qlt_le_weak _ _ (QltT_to_Qlt _ _ b1_0lt1))) as H1.
    setoid_replace ((4 * (x * (1 - x))) * (1 # 4))%Q with (x * (1 - x))%Q in H1 by ring.
    exact H1. }
  (* Cancel the denominator: [(den * (1/4)) * (/den) == 1/4] once the
   inverse is atomic. *)
  assert (Hcol : ((1 + x * x) * (1 # 4)) * (/ (1 + x * x)) == (1 # 4)).
  { remember (/ (1 + x * x)) as u eqn:Eu.
    assert (Hid : (1 + x * x) * u == 1).
    { subst u. apply Qmult_inv_r.
      intro Hc. apply (Qlt_not_eq 0 (1 + x * x) (QltT_to_Qlt _ _ Hden)).
      apply (Qeq_sym (1 + x * x) 0). exact Hc. }
    setoid_replace (((1 + x * x) * (1 # 4)) * u)%Q
      with ((1 # 4) * ((1 + x * x) * u))%Q by ring.
    rewrite Hid. apply Qmult_1_r. }
  apply Qle_to_QleT'.
  setoid_replace ((x * (1 - x)) / (1 + x * x))%Q
    with ((x * (1 - x)) * (/ (1 + x * x)))%Q by reflexivity.
  rewrite <- Hcol.
  apply (Qmult_le_compat_r (x * (1 - x)) ((1 + x * x) * (1 # 4)) (/ (1 + x * x)) Hstep1).
  apply Qlt_le_weak. apply QltT_to_Qlt. apply (b1_inv_pos (1 + x * x)).
  exact (QltT_to_Qlt _ _ Hden).
Qed.

(* ========== Section 2. Second certificate: [5/24], sharpened ========== *)

Lemma b1_kernel_margin_eq24 : forall x : Q,
  QeqT (29 * ((5 * (1 + x * x)) - 24 * (x * (1 - x))))%Q
       ((29 * x - 12) * (29 * x - 12) + 1)%Q.
Proof.
  intro x. apply qeq_imp_qeqT. ring.
Qed.

Theorem b1_kernel_pointwise_lt24 : forall x : Q,
  QltT (24 * (x * (1 - x))) (5 * (1 + x * x)).
Proof.
  intro x.
  set (D := ((5 * (1 + x * x)) - 24 * (x * (1 - x)))%Q).
  set (S := ((29 * x - 12) * (29 * x - 12) + 1)%Q).
  assert (Hme : 29 * D == S) by (apply (qeqT_imp_qeq _ _ (b1_kernel_margin_eq24 x))).
  assert (Hge : Qle 1 S) by exact (QleT'_to_Qle _ _ (b1_qsq_plus1_ge1 (29 * x - 12))).
  assert (H21 : Qle (1 * (1 # 29)) (S * (1 # 29))).
  { apply (Qmult_le_compat_r 1 S (1 # 29)).
    - exact Hge.
    - apply Qlt_le_weak. exact (QltT_to_Qlt _ _ b1_0lt1). }
  setoid_replace (1 * (1 # 29))%Q with (1 # 29)%Q in H21 by ring.
  rewrite <- Hme in H21.
  setoid_replace (29 * D * (1 # 29))%Q with D%Q in H21 by ring.
  assert (HD : Qlt 0 D).
  { apply (Qlt_le_trans 0 (1 # 29) D).
    - exact (QltT_to_Qlt _ _ b1_0lt1). - exact H21. }
  exact (b1_pos_diff_lt (5 * (1 + x * x)) (24 * (x * (1 - x))) HD).
Qed.

(* Ratio face of the second certificate: the kernel ratio is at most
   [5/24]. *)
Theorem b1_kernel_ratio_le24 : forall x : Q,
  QleT 0 x -> QleT' x 1 ->
  QleT' ((x * (1 - x)) / (1 + x * x)) (5 # 24).
Proof.
  intros x Hx0 Hx1.
  pose proof (b1_den_pos x) as Hden.
  pose proof (QltT_to_Qlt _ _ (b1_kernel_pointwise_lt24 x)) as Hpt.
  (* From [24 * num < 5 * den] conclude [num <= den * (5/24)]. *)
  assert (Hstep1 : Qle (x * (1 - x)) ((1 + x * x) * (5 # 24))).
  { pose proof (Qmult_le_compat_r (24 * (x * (1 - x))) (5 * (1 + x * x)) (1 # 24)
                  (Qlt_le_weak _ _ Hpt) (Qlt_le_weak _ _ (QltT_to_Qlt _ _ b1_0lt1))) as H1.
    setoid_replace ((24 * (x * (1 - x))) * (1 # 24))%Q with (x * (1 - x))%Q in H1 by ring.
    setoid_replace ((5 * (1 + x * x)) * (1 # 24))%Q with ((1 + x * x) * (5 # 24))%Q in H1 by ring.
    exact H1. }
  assert (Hcol : ((1 + x * x) * (5 # 24)) * (/ (1 + x * x)) == (5 # 24)).
  { remember (/ (1 + x * x)) as u eqn:Eu.
    assert (Hid : (1 + x * x) * u == 1).
    { subst u. apply Qmult_inv_r.
      intro Hc. apply (Qlt_not_eq 0 (1 + x * x) (QltT_to_Qlt _ _ Hden)).
      apply (Qeq_sym (1 + x * x) 0). exact Hc. }
    setoid_replace (((1 + x * x) * (5 # 24)) * u)%Q
      with ((5 # 24) * ((1 + x * x) * u))%Q by ring.
    rewrite Hid. apply Qmult_1_r. }
  apply Qle_to_QleT'.
  setoid_replace ((x * (1 - x)) / (1 + x * x))%Q
    with ((x * (1 - x)) * (/ (1 + x * x)))%Q by reflexivity.
  rewrite <- Hcol.
  apply (Qmult_le_compat_r (x * (1 - x)) ((1 + x * x) * (5 # 24)) (/ (1 + x * x)) Hstep1).
  apply Qlt_le_weak. apply QltT_to_Qlt. apply (b1_inv_pos (1 + x * x)).
  exact (QltT_to_Qlt _ _ Hden).
Qed.

(* ========== Section 3. Power lift through the monotone [q_pow] ========== *)

Theorem b1_kernel_pow_le24 : forall (n : nat) (x : Q),
  QleT 0 x -> QleT' x 1 ->
  QleT' (q_pow ((x * (1 - x)) / (1 + x * x)) n) (q_pow (5 # 24) n).
Proof.
  intros n x Hx0 Hx1.
  apply (q_pow_mono _ _ n).
  - apply Qle_to_QleT'.
    replace ((x * (1 - x)) / (1 + x * x))%Q
      with ((x * (1 - x)) * (/ (1 + x * x)))%Q by reflexivity.
    apply (Qmult_le_0_compat (x * (1 - x)) (/ (1 + x * x))).
    + exact (QleT'_to_Qle _ _ (b1_kernel_num_nonneg x Hx0 Hx1)).
    + apply Qlt_le_weak. apply QltT_to_Qlt. apply (b1_inv_pos (1 + x * x)).
      exact (QltT_to_Qlt _ _ (b1_den_pos x)).
  - exact (b1_kernel_ratio_le24 x Hx0 Hx1).
Qed.

(* ========== Section 4. Positivity of the kernel on the open interval ========== *)

Theorem b1_kernel_pos : forall x : Q,
  QltT 0 x -> QltT x 1 -> QltT 0 ((x * (1 - x)) / (1 + x * x)).
Proof.
  intros x Hx0 Hx1.
  apply Qlt_to_QltT.
  setoid_replace ((x * (1 - x)) / (1 + x * x))%Q
    with ((x * (1 - x)) * (/ (1 + x * x)))%Q by reflexivity.
  apply Qmult_lt_0_compat.
  - exact (QltT_to_Qlt _ _ (b1_kernel_num_pos x Hx0 Hx1)).
  - apply QltT_to_Qlt. apply (b1_inv_pos (1 + x * x)).
    exact (QltT_to_Qlt _ _ (b1_den_pos x)).
Qed.

(* ========== Section 5. Numeric anchors (independent recomputation points) ========== *)

(* Anchor at [x = 1/2]: the kernel ratio equals [1/5]
   (exactly [1/4] divided by [5/4]). *)
Lemma b1_kernel_anchor_half :
  QeqT (((1 # 2) * (1 - (1 # 2))) / (1 + (1 # 2) * (1 # 2))) (1 # 5).
Proof. apply qeq_imp_qeqT. reflexivity. Qed.

(* Anchor at [x = 2/5] (the true supremum point): the kernel ratio equals
   [6/29], about 0.2069, below [5/24] which is about 0.2083. *)
Lemma b1_kernel_anchor_twofifth :
  QeqT (((2 # 5) * (1 - (2 # 5))) / (1 + (2 # 5) * (2 # 5))) (6 # 29).
Proof. apply qeq_imp_qeqT. reflexivity. Qed.

(* Anchor for the slack: [5/24 - 6/29 = 1/696 > 0], a mechanical witness
   that the second certificate is not tight. *)
Lemma b1_kernel_anchor_gap :
  QeqT ((5 # 24) - (6 # 29)) (1 # 696).
Proof. apply qeq_imp_qeqT. reflexivity. Qed.

Lemma b1_kernel_anchor_gap_pos : QltT 0 ((5 # 24) - (6 # 29)).
Proof. apply Qlt_to_QltT. unfold Qlt. reflexivity. Qed.

(* ========== Section 6. Statement checks and assumption audit ========== *)

Check b1_kernel_pointwise_lt4.
Check b1_kernel_ratio_le4.
Check b1_kernel_pointwise_lt24.
Check b1_kernel_ratio_le24.
Check b1_kernel_pow_le24.
Check b1_kernel_pos.
Check b1_kernel_num_nonneg.
Check b1_kernel_num_pos.
Check b1_kernel_anchor_half.
Check b1_kernel_anchor_twofifth.
Check b1_kernel_anchor_gap.

Print Assumptions b1_kernel_pointwise_lt4.
Print Assumptions b1_kernel_ratio_le4.
Print Assumptions b1_kernel_pointwise_lt24.
Print Assumptions b1_kernel_ratio_le24.
Print Assumptions b1_kernel_pow_le24.
Print Assumptions b1_kernel_pos.
