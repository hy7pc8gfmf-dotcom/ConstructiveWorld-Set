(* ConstructiveWorld-Set — Partial exponential over the rationals: definitions,
   geometric decay, Cauchy completeness, and the real exponential field. *)

(** * S03_QExp: The partial exponential over the rationals and the real exponential.

    Mission.  Formalizes the partial exponential of a rational argument: powers
      [q_pow], factorials [q_fact], the partial sums [exp_partial] and tail sums
      [exp_tail]/[exp_tail_abs], the geometric decay estimates for [q_pow A m / q_fact m],
      the Cauchy property of the partial sums [exp_partial_cauchy], the real exponential
      [cauchy_real_exp] with its positivity [cauchy_real_exp_pos], the alternating identity
      [esq_eq_corr] (E_m^2 - O_m^2 == 1 + corr m a), and the Real-layer [real_abs],
      [real_metric] and positive reciprocal [real_inv_pos].

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs], [QArith.Qround], [Lists.List],
      [Bool.Bool], [Arith.Arith], [Setoid], [Morphisms], [Lia], [QArith.Qminmax].
      Requires [S01_BaseRing], [S02_CauchyComplete] of this development.

    References.  The baseline module [CW_ConstructiveWorld_219] of ConstructiveWorld-Main,
      whose statement names are carried over here verbatim (statement-face Set-carrier
      completion; this module is the split of that baseline covering source range
      [L6983]-[L13800]).  Only the proof bodies of [Q2_nonneg] and [Qhalf_nonneg] are
      rewritten (statements unchanged), unfolding [Qle] to the cross-product [Z.le] and
      closing by linear arithmetic.

    Constructivity.  All named statements and fields are carried by [Set] (decidable
      Q-carriers [QltT]/[QleT']/[QeqT], [Id], [NatLe]); statements extract with
      [Obj.magic] = 0 and no erasure; [coqchk] reports [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" S03_QExp.v] compiles cleanly (exit 0);
      the first eight bytes of the artifact are [436f7121 00015ff4]. *)
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               Lists.List Bool.Bool Arith.Arith.
Import ListNotations.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax.

Section QExpPartial.
(* positive_nat_Z: [Z.of_nat (Pos.to_nat p) == Z.pos p] holds by definitional [simpl] reduction plus [lia]. *)
Lemma positive_nat_Z : forall p : positive, QeqT (Z.of_nat (Pos.to_nat p) # 1) (Z.pos p # 1).
Proof.
  intro p. apply qeq_imp_qeqT.
  assert (Hz : Z.of_nat (Pos.to_nat p) = Z.pos p) by lia.
  rewrite Hz. apply Qeq_refl.
Qed.

Fixpoint q_pow (x : Q) (n : nat) : Q :=
  match n with
  | 0%nat => 1%Q
  | Datatypes.S m => x * q_pow x m
  end.

Fixpoint q_fact (n : nat) : Q :=
  match n with
  | 0%nat => 1%Q
  | Datatypes.S m => (Z.of_nat (Datatypes.S m) # 1) * q_fact m
  end.

Fixpoint exp_partial (n : nat) (x : Q) : Q :=
  match n with
  | 0%nat => 1%Q
  | Datatypes.S m => exp_partial m x + q_pow x (Datatypes.S m) / q_fact (Datatypes.S m)
  end.

Lemma q_pow_abs : forall (x : Q) (n : nat),QeqT ( Qabs (q_pow x n) ) ( q_pow (Qabs x) n).
Proof.
  intros x n. induction n as [| m IH]; simpl.
  - apply qeq_imp_qeqT.
    assert (H1 : Qabs (1%Q) == 1%Q) by (unfold Qabs; simpl; reflexivity).
    exact H1.
  - apply qeq_imp_qeqT.
    change (Qabs (x * q_pow x m) == Qabs x * q_pow (Qabs x) m).
    rewrite Qabs_Qmult.
    rewrite (qeqT_imp_qeq _ _ IH). reflexivity.
Qed.

Lemma q_pow_succ : forall x n,QeqT ( q_pow x (Datatypes.S n) ) ( x * q_pow x n).
Proof. intros. apply qeq_imp_qeqT. reflexivity. Qed.

Lemma q_fact_succ : forall k : nat,QeqT ( q_fact (Datatypes.S k) ) ( (Z.of_nat (Datatypes.S k) # 1) * q_fact k).
Proof. intro k. apply qeq_imp_qeqT. reflexivity. Qed.

Lemma q_fact_pos : forall n : nat, QltT 0 (q_fact n).
Proof.
  induction n as [| m IH]; simpl.
  - apply Qlt_to_QltT. unfold Qlt; simpl; lia.
  - apply Qlt_to_QltT.
    apply Qmult_lt_0_compat; [unfold Qlt; simpl; lia | apply QltT_to_Qlt; exact IH].
Qed.

Lemma q_pow_nonneg : forall (x : Q) (n : nat), QleT' 0 x -> QleT' 0 (q_pow x n).
Proof.
  intros x n Hx. induction n as [| m IH]; simpl.
  - apply Qle_to_QleT'. unfold Qle; simpl; lia.
  - apply Qle_to_QleT'.
    apply Qmult_le_0_compat; [apply QleT'_to_Qle; exact Hx | apply QleT'_to_Qle; exact IH].
Qed.

Lemma q_neq_of_lt : forall x : Q, QltT 0 x -> Not (QeqT x 0).
Proof.
  intros x Hx H.
  destruct (Qlt_not_eq 0 x (QltT_to_Qlt 0 x Hx) (Qeq_sym x 0 (qeqT_imp_qeq x 0 H))).
Qed.

(* ===== Monotonicity ([pow_fact_mono]) ===== *)
Lemma pow_fact_mono_int : forall (A : Q) (k : nat),
  QleT' 0 A -> QleT' A (Z.of_nat (k + 1) # 1) ->
  QleT' (q_pow A (Datatypes.S k) * q_fact k) (q_pow A k * q_fact (Datatypes.S k)).
Proof.
  intros A k HA Hle.
  apply Qle_to_QleT'.
  rewrite (qeqT_imp_qeq _ _ (q_pow_succ A k)).
  rewrite (qeqT_imp_qeq _ _ (q_fact_succ k)).
  setoid_replace (Z.of_nat (Datatypes.S k) # 1) with (Z.of_nat (k + 1) # 1).
  2: { unfold Qeq. simpl. lia. }
  apply (Qle_trans _ (A * (q_pow A k * q_fact k)) _).
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
  - apply (Qle_trans _ ((Z.of_nat (k + 1) # 1) * (q_pow A k * q_fact k)) _).
    + apply (Qmult_le_compat_r A (Z.of_nat (k + 1) # 1) (q_pow A k * q_fact k)).
      * apply QleT'_to_Qle. exact Hle.
      * apply Qmult_le_0_compat.
        -- apply QleT'_to_Qle. apply q_pow_nonneg. exact HA.
        -- apply (Qlt_le_weak 0 (q_fact k)). apply QltT_to_Qlt. apply q_fact_pos.
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
Qed.

Lemma Qle_div_same_denom : forall a b e : Q,
  QltT 0 e -> QleT' a b -> QleT' (a / e) (b / e).
Proof.
  intros a b e He Hab.
  apply Qle_to_QleT'.
  unfold Qdiv.
  exact (Qmult_le_compat_r a b (/ e) (QleT'_to_Qle _ _ Hab)
    (Qinv_le_0_compat e (Qlt_le_weak 0 e (QltT_to_Qlt _ _ He)))).
Qed.

Lemma q_le_div_le : forall a b c d : Q,
  QltT 0 b -> QltT 0 d -> QleT' (a * d) (c * b) -> QleT' (a / b) (c / d).
Proof.
  intros a b c d Hb Hd Hle.
  apply Qle_to_QleT'.
  apply (Qle_trans _ ((a * d) / (b * d)) _).
  - apply QleT'_to_Qle. apply qeq_le.
  apply qeq_imp_qeqT.
    field; split;
      try (intro Hz0; assert (Hlt0 : QltT 0 b) by exact Hb;
           destruct (q_neq_of_lt b Hlt0 (qeq_imp_qeqT _ _ Hz0)));
      try (intro Hz0; assert (Hlt0 : QltT 0 d) by exact Hd;
           destruct (q_neq_of_lt d Hlt0 (qeq_imp_qeqT _ _ Hz0))).
  - apply (Qle_trans _ ((c * b) / (b * d)) _).
    + apply QleT'_to_Qle.
      apply (Qle_div_same_denom (a * d) (c * b) (b * d)).
      * apply Qlt_to_QltT.
        apply Qmult_lt_0_compat; [apply QltT_to_Qlt; exact Hb | apply QltT_to_Qlt; exact Hd].
      * exact Hle.
    + apply QleT'_to_Qle. apply qeq_le.
    apply qeq_imp_qeqT.
      field; split;
        try (intro Hz0; assert (Hlt0 : QltT 0 b) by exact Hb;
             destruct (q_neq_of_lt b Hlt0 (qeq_imp_qeqT _ _ Hz0)));
        try (intro Hz0; assert (Hlt0 : QltT 0 d) by exact Hd;
             destruct (q_neq_of_lt d Hlt0 (qeq_imp_qeqT _ _ Hz0))).
Qed.

Lemma pow_fact_mono : forall (A : Q) (k : nat),
  QleT' 0 A -> QltT (Qmult (1 + 1)%Q A) (Qmake (Z.of_nat (k + 1)) 1) ->
  QleT' (q_pow A (Datatypes.S k) / q_fact (Datatypes.S k)) (q_pow A k / q_fact k).
Proof.
  intros A k HA Hlt.
  assert (HleA : QleT' A (Qmake (Z.of_nat (k + 1)) 1)).
  {
    apply Qle_to_QleT'.
    apply (Qle_trans _ (Qmult (1 + 1)%Q A) _).
    - apply Qle_minus_iff.
      setoid_replace (Qmult (1 + 1)%Q A + - A) with A by ring.
      apply QleT'_to_Qle. exact HA.
    - apply Qlt_le_weak. apply QltT_to_Qlt. exact Hlt.
  }
  apply (q_le_div_le (q_pow A (Datatypes.S k)) (q_fact (Datatypes.S k)) (q_pow A k) (q_fact k)).
  - apply q_fact_pos.
  - apply q_fact_pos.
  - apply (pow_fact_mono_int A k HA HleA).
Qed.

(* ===== Geometric decay ([pow_fact_geom_step]) ===== *)
Lemma pow_fact_geom_int : forall (A : Q) (k : nat),
  QleT' 0 A -> QleT' (Qmult (1 + 1)%Q A) (Z.of_nat (k + 1) # 1) ->
  QleT' (q_pow A (Datatypes.S k) * q_fact k * (1 + 1)) (q_pow A k * q_fact (Datatypes.S k)).
Proof.
  intros A k HA Hle.
  apply Qle_to_QleT'.
  rewrite (qeqT_imp_qeq _ _ (q_pow_succ A k)).
  rewrite (qeqT_imp_qeq _ _ (q_fact_succ k)).
  setoid_replace (Z.of_nat (Datatypes.S k) # 1) with (Z.of_nat (k + 1) # 1).
  2: { unfold Qeq. simpl. lia. }
  apply (Qle_trans _ ((Qmult (1 + 1)%Q A) * (q_pow A k * q_fact k)) _).
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
  - apply (Qle_trans _ ((Z.of_nat (k + 1) # 1) * (q_pow A k * q_fact k)) _).
    + apply (Qmult_le_compat_r (Qmult (1 + 1)%Q A) (Z.of_nat (k + 1) # 1) (q_pow A k * q_fact k)).
      * apply QleT'_to_Qle. exact Hle.
      * apply Qmult_le_0_compat.
        -- apply QleT'_to_Qle. apply q_pow_nonneg. exact HA.
        -- apply (Qlt_le_weak 0 (q_fact k)). apply QltT_to_Qlt. apply q_fact_pos.
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
Qed.

Lemma div_form_lhs : forall (A : Q) (k : nat),QeqT (
  q_pow A (Datatypes.S k) * q_fact k ) ( (q_pow A (Datatypes.S k) * q_fact k * (1 + 1)) * (1 / 2)).
Proof. intros. apply qeq_imp_qeqT. field. Qed.

Lemma pow_fact_geom_step : forall (A : Q) (k : nat),
  QleT' 0 A -> QleT' (Qmult (1 + 1)%Q A) (Z.of_nat (k + 1) # 1) ->
  QleT' (q_pow A (Datatypes.S k) / q_fact (Datatypes.S k)) ((q_pow A k / q_fact k) * (1 / 2)).
Proof.
  intros A k HA Hle.
  apply Qle_to_QleT'.
  apply (Qle_trans _ ((q_pow A k * (1 / 2)) / q_fact k) _).
  - apply QleT'_to_Qle.
    apply (q_le_div_le (q_pow A (Datatypes.S k)) (q_fact (Datatypes.S k))
                       (q_pow A k * (1 / 2)) (q_fact k)).
    + apply q_fact_pos.
    + apply q_fact_pos.
    + apply Qle_to_QleT'.
      apply (Qle_trans _ ((q_pow A k * q_fact (Datatypes.S k)) * (1 / 2)) _).
      * apply (Qle_trans _ ((q_pow A (Datatypes.S k) * q_fact k * (1 + 1)) * (1 / 2)) _).
        -- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. exact (qeqT_imp_qeq _ _ (div_form_lhs A k)).
        -- apply (Qmult_le_compat_r (q_pow A (Datatypes.S k) * q_fact k * (1 + 1))
                                   (q_pow A k * q_fact (Datatypes.S k)) (1 / 2)).
           ++ apply QleT'_to_Qle. apply (pow_fact_geom_int A k HA Hle).
           ++ apply Qlt_le_weak. unfold Qlt; simpl; lia.
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. field.
  - apply QleT'_to_Qle. apply qeq_le.
  apply qeq_imp_qeqT.
    field.
    intro Hz. destruct (q_neq_of_lt (q_fact k) (q_fact_pos k) (qeq_imp_qeqT _ _ Hz)).
Qed.

(* ===== Geometric series (the recursive [geo_sum]) ===== *)
Fixpoint geo_sum (n : nat) : Q :=
  match n with
  | 0%nat => 0
  | Datatypes.S m => geo_sum m + q_pow (1 / 2) m
  end.

Lemma geo_sum_closed : forall n : nat,QeqT (
  geo_sum n ) ( (1 + 1) * (1 - q_pow (1 / 2) n)).
Proof.
  intro n. apply qeq_imp_qeqT.
  induction n as [| n IH]; simpl.
  - ring.
  - rewrite IH.
    change ((1 + 1) * (1 - q_pow (1 / 2) n) + q_pow (1 / 2) n ==
            (1 + 1) * (1 - (1 / 2) * q_pow (1 / 2) n)).
    field.
Qed.

Lemma geo_sum_le_two : forall n : nat, QleT' (geo_sum n) (1 + 1).
Proof.
  intro n. apply Qle_to_QleT'.
  rewrite (qeqT_imp_qeq _ _ (geo_sum_closed n)).
  apply Qle_minus_iff.
  setoid_replace ((1 + 1) - (1 + 1) * (1 - q_pow (1 / 2) n))
    with ((1 + 1) * q_pow (1 / 2) n).
  2: { ring. }
  apply Qmult_le_0_compat.
  - unfold Qle; simpl; lia.
  - apply QleT'_to_Qle. apply q_pow_nonneg. apply Qle_to_QleT'. unfold Qle; simpl; lia.
Qed.

(* ===== Iterated geometric decay =====
   For all j >= 0, A^(m+Datatypes.S j)/(m+Datatypes.S j)! <= (A^m/m!) * (1/2)^(Datatypes.S j).
   By induction on [j]: one step of [pow_fact_geom_step] at index [m+j] combined with the
   IH multiplied by [1/2]. *)
Lemma pow_fact_geom_iter : forall (A : Q) (m j : nat),
  QleT' 0 A ->
  (forall t : nat, NatLe m t -> QleT' (Qmult (1 + 1)%Q A) (Z.of_nat (t + 1) # 1)) ->
  QleT' (q_pow A (m + Datatypes.S j) / q_fact (m + Datatypes.S j))
      ((q_pow A m / q_fact m) * q_pow (1 / 2) (Datatypes.S j)).
Proof.
  intros A m j HA Hgeom.
  apply Qle_to_QleT'.
  revert m Hgeom. induction j as [| j IH]; intros m Hgeom.
  - (* Case [j = 0]: the claim is A^(m+1)/(m+1)! <= (A^m/m!) * (1/2)^1.
       After rewriting [m+1 == Datatypes.S m] (by [lia]) and [q_pow (1/2) 1 == (1/2)],
       this is exactly [pow_fact_geom_step] at [m]. *)
    replace (m + 1)%nat with (Datatypes.S m) by lia.
    setoid_replace (q_pow (1 / 2) 1) with (1 / 2).
    2: { change ((1 / 2) * 1 == 1 / 2). field. }
    apply QleT'_to_Qle.
    apply (pow_fact_geom_step A m HA).
    apply Hgeom. apply NatLe_lift. lia.
  - (* Case [j = Datatypes.S j']: the claim is
       A^(m+S(Datatypes.S j'))/(m+S(Datatypes.S j'))! <= (A^m/m!) * (1/2)^(Datatypes.S(Datatypes.S j')).
       Write k := m + Datatypes.S j', so the left side is A^(Datatypes.S k)/(Datatypes.S k)!.
       One step at [k]: A^(Datatypes.S k)/(Datatypes.S k)! <= (A^k/k!) * (1/2).
       The IH at [m] (with [j := Datatypes.S j']) gives
       A^k/k! <= (A^m/m!) * (1/2)^(Datatypes.S j').
       Combining: <= (A^m/m!) * (1/2)^(Datatypes.S j') * (1/2) == (A^m/m!) * (1/2)^(Datatypes.S(Datatypes.S j')). *)
    (* Rewriting the right side: (1/2)^(Datatypes.S(Datatypes.S j)) == (1/2)^(Datatypes.S j) * (1/2), by [q_pow_succ] and commutativity. *)
    setoid_replace (q_pow (1 / 2) (Datatypes.S (Datatypes.S j))) with (q_pow (1 / 2) (Datatypes.S j) * (1 / 2)).
    2: { rewrite (qeqT_imp_qeq _ _ (q_pow_succ (1 / 2) (Datatypes.S j))). ring. }
    (* Rewriting the left side: [m + Datatypes.S (Datatypes.S j)] equals [Datatypes.S (m + Datatypes.S j)] in [nat] (asserted first, then used to rewrite). *)
    assert (Hm : (m + Datatypes.S (Datatypes.S j))%nat = Datatypes.S (m + Datatypes.S j)) by lia.
    setoid_replace (q_pow A (m + Datatypes.S (Datatypes.S j)) / q_fact (m + Datatypes.S (Datatypes.S j)))
      with (q_pow A (Datatypes.S (m + Datatypes.S j)) / q_fact (Datatypes.S (m + Datatypes.S j))).
    2: { rewrite Hm. reflexivity. }
    (* Goal: A^(S(m+Datatypes.S j))/(S(m+Datatypes.S j))! <= (A^m/m!) * (1/2)^(Datatypes.S j) * (1/2),
       following from one step at [m+Datatypes.S j] and the IH
       (A^(m+Datatypes.S j)/(m+Datatypes.S j)! <= (A^m/m!) * (1/2)^(Datatypes.S j)). *)
    apply (Qle_trans _ ((q_pow A (m + Datatypes.S j) / q_fact (m + Datatypes.S j)) * (1 / 2)) _).
    { (* A^(S(m+Datatypes.S j))/(S(m+Datatypes.S j))! <= (A^(m+Datatypes.S j)/(m+Datatypes.S j)!) * (1/2), by one step at [m+Datatypes.S j]. *)
      apply QleT'_to_Qle.
      apply (pow_fact_geom_step A (m + Datatypes.S j) HA).
      apply (Hgeom (m + Datatypes.S j)%nat). apply NatLe_lift. lia. }
    { (* (A^(m+Datatypes.S j)/(m+Datatypes.S j)!) * (1/2) <= (A^m/m!) * (1/2)^(Datatypes.S j) * (1/2):
         the IH at [m] multiplied by [1/2] ([Qmult_le_compat_r]); the goal's
         right side is reassociated with [Qmult_assoc]. *)
      setoid_replace ((q_pow A m / q_fact m) * (q_pow (1 / 2) (Datatypes.S j) * (1 / 2)))
        with ((q_pow A m / q_fact m) * q_pow (1 / 2) (Datatypes.S j) * (1 / 2)).
      2: { apply Qmult_assoc. }
      apply (Qmult_le_compat_r (q_pow A (m + Datatypes.S j) / q_fact (m + Datatypes.S j))
                               ((q_pow A m / q_fact m) * q_pow (1 / 2) (Datatypes.S j))
                               (1 / 2)).
      - exact (IH m Hgeom).
      - apply Qlt_le_weak. unfold Qlt; simpl; lia. }
Qed.

(* ============================================================ *)
(* The main theorem [exp_partial_cauchy].                                       *)
(* Route: take A = |x|, pick an Archimedean bound N0 with 2A <= (t+1)#1, then   *)
(*   bound the tail with the triangle inequality:                               *)
(*   |tail| <= the sum of A^(Datatypes.S k)/(Datatypes.S k)! <= (A^m/m!) * geo_sum <= (A^m/m!) * 2. *)
(*   Finally choose m >= N0 with (A^m/m!) * 2 < eps (decay of (1/2)^t plus the Archimedean bound). *)
(* The statement lives in [Set]: equality via [Id] and order via [QltT].        *)
(* No classical axioms; the [sigT] conclusion is informative and extractable to OCaml. *)
(* ============================================================ *)

Lemma Q2_pos : QltT 0 (1 + 1)%Q.
Proof. apply Qlt_to_QltT. unfold Qlt; simpl; lia. Qed.

Lemma Q2_nonneg : QleT' 0 (1 + 1)%Q.
Proof.
  apply Qle_to_QleT'.
  (* The comparison is built directly at the integer level: unfolding [Qle] yields the
     cross-product [Z.le], which closes by linear arithmetic after literal reduction,
     without forwarding through [Qlt_le_weak]. *)
  unfold Qle.
  simpl.
  lia.
Qed.

Lemma Qhalf_pos : QltT 0 (1 / 2)%Q.
Proof. apply Qlt_to_QltT. unfold Qlt; simpl; lia. Qed.

Lemma Qhalf_nonneg : QleT' 0 (1 / 2)%Q.
Proof.
  apply Qle_to_QleT'.
  (* The comparison is built directly at the integer level: unfolding [Qle] yields the
     cross-product [Z.le], which closes by linear arithmetic after literal reduction,
     without forwarding through [Qlt_le_weak]. *)
  unfold Qle.
  simpl.
  lia.
Qed.

Lemma Qle_of_nat : forall a b : nat, (a <= b)%nat ->
  QleT' (Z.of_nat a # 1) (Z.of_nat b # 1).
Proof.
  intros a b Hab.
  apply Qle_to_QleT'.
  unfold Qle; simpl; lia.
Qed.

Lemma Qlt_of_nat_lt : forall a b : nat, (a < b)%nat ->
  QltT (Z.of_nat a # 1) (Z.of_nat b # 1).
Proof.
  intros a b Hab.
  apply Qlt_to_QltT.
  unfold Qlt; simpl; lia.
Qed.

Lemma q_pow_wd : forall x y n,QeqT ( x ) ( y )->QeqT ( q_pow x n ) ( q_pow y n).
Proof.
  intros x y n Hxy. apply qeq_imp_qeqT.
  induction n as [| n IH]; simpl.
  - reflexivity.
  - rewrite IH. rewrite (qeqT_imp_qeq _ _ Hxy). reflexivity.
Qed.

Lemma q_pow_add : forall (x : Q) (a b : nat),QeqT ( q_pow x (a + b) ) ( q_pow x a * q_pow x b).
Proof.
  intros x a b. apply qeq_imp_qeqT.
  induction a as [| a IH]; simpl.
  - ring.
  - rewrite IH. ring.
Qed.

Lemma q_half_pow_le_one : forall k : nat, QleT' (q_pow (1 / 2)%Q k) 1.
Proof.
  intros k. apply Qle_to_QleT'.
  induction k as [| k IH]; simpl.
  - apply Qle_refl.
  - apply (Qle_trans _ (Qmult (1 / 2)%Q 1) _).
    + apply (Qmult_le_compat_nonneg (1 / 2)%Q (1 / 2)%Q (q_pow (1 / 2)%Q k) 1).
      * split; [apply QleT'_to_Qle; exact Qhalf_nonneg | apply Qle_refl].
      * split; [apply QleT'_to_Qle; apply (q_pow_nonneg (1 / 2)%Q k Qhalf_nonneg) | exact IH].
    + unfold Qle; simpl; lia.
Qed.

(* The identity (1/2) * (1/(n+1)#1) == 1/(2 * (n+1)#1), as a standalone [field] lemma. *)
Lemma half_inv_shift : forall n : nat,QeqT (
  (1 / 2)%Q * (1 / (Z.of_nat (n + 1) # 1)) ) (
  1 / ((1 + 1)%Q * (Z.of_nat (n + 1) # 1))).
Proof.
  intro n. apply qeq_imp_qeqT.
  field.
  all: try (intro Hz0;
            assert (Hlt0 : QltT 0 (Z.of_nat (n + 1) # 1))
              by (apply (Qlt_of_nat_lt 0 (n + 1)); lia);
            destruct (q_neq_of_lt _ Hlt0 (qeq_imp_qeqT _ _ Hz0))).
  all: try (intro Hz0;
            assert (Hlt0 : QltT 0 ((1 + 1)%Q * (Z.of_nat (n + 1) # 1)))
              by (apply Qlt_to_QltT;
                  apply (Qmult_lt_0_compat (1 + 1)%Q (Z.of_nat (n + 1) # 1));
                  [ apply QltT_to_Qlt; exact Q2_pos
                  | apply QltT_to_Qlt; apply (Qlt_of_nat_lt 0 (n + 1)); lia ]);
            destruct (q_neq_of_lt _ Hlt0 (qeq_imp_qeqT _ _ Hz0))).
Qed.

(* The identity (1+1)%Q * (n+1)#1 == (2(n+1))#1, computed directly on [Qmake] plus [lia]; this avoids unreduced [match] residue from [Z] multiplication. *)
Lemma Q2_mul_nat : forall n : nat,QeqT (
  (1 + 1)%Q * (Z.of_nat (n + 1) # 1) ) ( Z.of_nat (2 * (n + 1)) # 1).
Proof.
  intro n.
  apply qeq_imp_qeqT.
  change ((1 + 1)%Q) with (Qmake 2 1).
  unfold Qeq. cbn [Qnum Qden Qmult]. lia.
Qed.

(* (1/2)^n <= 1/(n+1)#1, by induction sandwiching the middle term between the multiplicative bounds. *)
Lemma q_half_pow_le_inv : forall n : nat,
  QleT' (q_pow (1 / 2)%Q n) (1 / (Z.of_nat (n + 1) # 1)).
Proof.
  intro n. induction n as [| n IH].
  - simpl. apply Qle_to_QleT'. unfold Qle; simpl; lia.
  - assert (Hn : (Datatypes.S n + 1)%nat = (n + 2)%nat) by lia. rewrite Hn.
    simpl. apply Qle_to_QleT'.
    change ((1 / 2)%Q * q_pow (1 / 2)%Q n <= 1 / (Z.of_nat (n + 2) # 1)).
    apply (Qle_trans _ ((1 / 2)%Q * (1 / (Z.of_nat (n + 1) # 1))) _).
    + apply (Qmult_le_compat_nonneg (1 / 2)%Q (1 / 2)%Q (q_pow (1 / 2)%Q n)
                                    (1 / (Z.of_nat (n + 1) # 1))).
      * split; [exact (QleT'_to_Qle _ _ Qhalf_nonneg) | apply Qle_refl].
      * split; [exact (QleT'_to_Qle _ _ (q_pow_nonneg (1 / 2)%Q n Qhalf_nonneg))
               | exact (QleT'_to_Qle _ _ IH)].
    + apply (Qle_trans _ (1 / ((1 + 1)%Q * (Z.of_nat (n + 1) # 1))) _).
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply (qeqT_imp_qeq _ _ (half_inv_shift n)).
      * apply QleT'_to_Qle.
        apply (q_le_div_le 1 ((1 + 1)%Q * (Z.of_nat (n + 1) # 1))
                            1 (Z.of_nat (n + 2) # 1)).
        -- apply Qlt_to_QltT.
           apply (Qmult_lt_0_compat (1 + 1)%Q (Z.of_nat (n + 1) # 1)).
           ++ apply QltT_to_Qlt. apply Q2_pos.
           ++ apply QltT_to_Qlt. apply (Qlt_of_nat_lt 0 (n + 1)). lia.
        -- apply (Qlt_of_nat_lt 0 (n + 2)). lia.
        -- (* The claim 1 * (n+2)#1 <= 1 * ((1+1) * (n+1)#1) reduces by cancelling the unit factors with [setoid_rewrite], then closes via [Qle_of_nat]. *)
           apply Qle_to_QleT'.
           setoid_rewrite (Qmult_1_l (Z.of_nat (n + 2) # 1)).
           setoid_rewrite (Qmult_1_l ((1 + 1)%Q * (Z.of_nat (n + 1) # 1))).
           apply (Qle_trans _ (Z.of_nat (2 * (n + 1)) # 1) _).
           ++ apply QleT'_to_Qle. apply Qle_of_nat. lia.
           ++ apply QleT'_to_Qle. apply qeq_le.
           apply qeq_imp_qeqT.
              apply Qeq_sym. apply qeqT_imp_qeq. apply Q2_mul_nat.
Qed.

(* The Archimedean property at the [Set] level: there is N with 2A <=T (t+1)#1 for all t >= N, derived from [Qarchimedean] and [positive_nat_Z], with all quantifiers recast in [NatLe]/[QleT'] form. *)
Lemma q_arch_geom : forall A : Q,
  sigT (fun N : nat => forall t : nat, NatLe N t ->
    QleT' (Qmult (1 + 1)%Q A) (Z.of_nat (t + 1) # 1)).
Proof.
  intro A.
  destruct (Qarchimedean (Qmult (1 + 1)%Q A)) as [p Hp].
  exists (Pos.to_nat p).
  intros t Ht.
  apply Qle_to_QleT'.
  apply Qlt_le_weak.
  apply (Qlt_trans _ (Z.pos p # 1) _).
  - exact Hp.
  - setoid_rewrite <- (qeqT_imp_qeq _ _ (positive_nat_Z p)).
    apply QltT_to_Qlt. apply (Qlt_of_nat_lt (Pos.to_nat p) (t + 1)).
    apply NatLe_drop in Ht. lia.
Qed.

(* Decay: for every C >= 0 and eps > 0 there is t with C * (1/2)^(S t) < eps. *)
(* Decay at the [Set] level: for all C >=T 0 and eps >T 0 there is t with C * (1/2)^(S t) <T eps, with the whole argument recast in [QleT']/[QltT] form. *)
Lemma arch_decay : forall (C eps : Q), QleT' 0 C -> QltT 0 eps ->
  sigT (fun t : nat => QltT (C * q_pow (1 / 2)%Q (Datatypes.S t)) eps).
Proof.
  intros C eps HC Hep.
  destruct (Qarchimedean (C / eps)) as [p Hp].
  exists (Pos.to_nat p).
  apply Qlt_to_QltT.
  apply (Qle_lt_trans _ (C * (1 / (Z.of_nat (Datatypes.S (Pos.to_nat p) + 1) # 1))) _).
  - apply (Qle_trans _ (q_pow (1 / 2)%Q (Datatypes.S (Pos.to_nat p)) * C) _).
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
    + apply (Qle_trans _ ((1 / (Z.of_nat (Datatypes.S (Pos.to_nat p) + 1) # 1)) * C) _).
      * apply (Qmult_le_compat_r (q_pow (1 / 2)%Q (Datatypes.S (Pos.to_nat p)))
                                 (1 / (Z.of_nat (Datatypes.S (Pos.to_nat p) + 1) # 1)) C).
        -- apply QleT'_to_Qle. apply (q_half_pow_le_inv (Datatypes.S (Pos.to_nat p))).
        -- exact (QleT'_to_Qle _ _ HC).
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
  - apply (Qlt_shift_div_r C (Z.of_nat (Datatypes.S (Pos.to_nat p) + 1) # 1) eps).
    + apply QltT_to_Qlt. apply (Qlt_of_nat_lt 0 (Datatypes.S (Pos.to_nat p) + 1)); lia.
    + apply (Qlt_le_trans _ (eps * (Z.pos p # 1)) _).
      * pose proof (Qmult_lt_compat_r (C / eps) (Z.pos p # 1) eps (QltT_to_Qlt _ _ Hep) Hp) as Hm.
        assert (Hf : (C / eps) * eps == C) by (field; intro Hz0; destruct (q_neq_of_lt eps Hep (qeq_imp_qeqT _ _ Hz0))).
        setoid_rewrite Hf in Hm.
        setoid_rewrite (Qmult_comm (Z.pos p # 1) eps) in Hm.
        exact Hm.
      * apply (Qle_trans _ ((Z.pos p # 1) * eps) _).
        -- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
        -- apply (Qle_trans _ ((Z.of_nat (Datatypes.S (Pos.to_nat p) + 1) # 1) * eps) _).
           ++ apply (Qmult_le_compat_r (Z.pos p # 1)
                                      (Z.of_nat (Datatypes.S (Pos.to_nat p) + 1) # 1) eps).
              ** setoid_rewrite <- (qeqT_imp_qeq _ _ (positive_nat_Z p)).
                 apply QleT'_to_Qle. apply (Qle_of_nat (Pos.to_nat p) (Datatypes.S (Pos.to_nat p) + 1)). lia.
              ** apply Qlt_le_weak. exact (QltT_to_Qlt _ _ Hep).
           ++ apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
Qed.
(* The multiplicative decomposition of [Qabs] under division. *)
Lemma q_abs_div : forall a b : Q,QeqT ( Qabs (a / b) ) ( Qabs a / Qabs b).
Proof.
  intros a b. apply qeq_imp_qeqT. unfold Qdiv.
  rewrite Qabs_Qmult. rewrite Qabs_Qinv. reflexivity.
Qed.

(* With A := |x|: |x^(Datatypes.S n)/(Datatypes.S n)!| == A^(Datatypes.S n)/(Datatypes.S n)!. *)
Lemma q_abs_pow_fact : forall x n,QeqT (
  Qabs (q_pow x (Datatypes.S n) / q_fact (Datatypes.S n)) ) ( q_pow (Qabs x) (Datatypes.S n) / q_fact (Datatypes.S n)).
Proof.
  intros x n. apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (q_abs_div _ _)).
  rewrite (qeqT_imp_qeq _ _ (q_pow_abs _ _)).
  rewrite (Qabs_pos (q_fact (Datatypes.S n))
                    (Qlt_le_weak 0 (q_fact (Datatypes.S n))
                       (QltT_to_Qlt 0 (q_fact (Datatypes.S n)) (q_fact_pos (Datatypes.S n))))).
  reflexivity.
Qed.

(* 0 <= A^m/m!. *)
Lemma q_pow_fact_nonneg : forall A m, QleT' 0 A -> QleT' 0 (q_pow A m / q_fact m).
Proof.
  intros A m HA.
  apply Qle_to_QleT'.
  apply QleT'_to_Qle. apply (q_le_div_le 0 1 (q_pow A m) (q_fact m)).
  - vm_compute. reflexivity.
  - apply q_fact_pos.
  - apply Qle_to_QleT'.
    apply (Qle_trans _ 0 _).
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
    + apply (Qle_trans _ (q_pow A m) _).
      * apply QleT'_to_Qle. apply q_pow_nonneg. exact HA.
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
Qed.

(* 0 <= (A^m/m!) * 2. *)
Lemma q_pow_fact2_nonneg : forall A m, QleT' 0 A -> QleT' 0 ((q_pow A m / q_fact m) * (1 + 1)%Q).
Proof.
  intros A m HA.
  apply Qle_to_QleT'.
  exact (Qmult_le_compat_r 0 (q_pow A m / q_fact m) (1 + 1)%Q
  (QleT'_to_Qle _ _ (q_pow_fact_nonneg A m HA)) (QleT'_to_Qle _ _ Q2_nonneg)).
Qed.

(* (1/2)^a <= (1/2)^b whenever a >= b. *)
Lemma q_half_pow_mono : forall a b : nat, (b <= a)%nat ->
  QleT' (q_pow (1 / 2)%Q a) (q_pow (1 / 2)%Q b).
Proof.
  intros a b H.
  apply Qle_to_QleT'.
  assert (Ha : (a = b + (a - b))%nat) by lia.
  rewrite Ha. rewrite (qeqT_imp_qeq _ _ (q_pow_add (1 / 2)%Q b (a - b))).
  apply (Qle_trans _ (q_pow (1 / 2)%Q (a - b) * q_pow (1 / 2)%Q b) _).
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
  - apply (Qle_trans _ (1 * q_pow (1 / 2)%Q b) _).
    + apply (Qmult_le_compat_r (q_pow (1 / 2)%Q (a - b)) 1 (q_pow (1 / 2)%Q b)).
      * apply QleT'_to_Qle. apply q_half_pow_le_one.
      * apply QleT'_to_Qle. apply (q_pow_nonneg (1 / 2)%Q b Qhalf_nonneg).
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
Qed.

(* ===== [exp_tail]: the tail sum of x^(Datatypes.S k)/(Datatypes.S k)! for m <= k < n (guarded version) ===== *)
Fixpoint exp_tail (m : nat) (n : nat) (x : Q) : Q :=
  match n with
  | 0%nat => 0
  | Datatypes.S n' => exp_tail m n' x + (if Nat.leb m n' then q_pow x (Datatypes.S n') / q_fact (Datatypes.S n') else 0)
  end.

Fixpoint exp_tail_abs (m : nat) (n : nat) (A : Q) : Q :=
  match n with
  | 0%nat => 0
  | Datatypes.S n' => exp_tail_abs m n' A + (if Nat.leb m n' then q_pow A (Datatypes.S n') / q_fact (Datatypes.S n') else 0)
  end.

Lemma q_div_wd : forall a b c : Q,QeqT ( a ) ( b )->QeqT ( a / c ) ( b / c).
Proof.
  intros a b c H. apply qeq_imp_qeqT. unfold Qdiv.
  apply qeqT_imp_qeq in H. rewrite H. reflexivity.
Qed.

Lemma exp_tail_abs_wd : forall (m n : nat) (A B : Q),QeqT ( A ) ( B )->QeqT ( exp_tail_abs m n A ) ( exp_tail_abs m n B).
Proof.
  intros m n A B HAB. apply qeq_imp_qeqT. induction n as [| n IH]; simpl.
  - reflexivity.
  - destruct (Nat.leb m n) eqn:E; rewrite IH.
    + rewrite (qeqT_imp_qeq _ _ (q_pow_wd A B (Datatypes.S n) HAB)). reflexivity.
    + reflexivity.
Qed.

(* If n <= m the tail sum vanishes. *)
Lemma exp_tail_le_m : forall m n x, (n <= m)%nat ->QeqT ( exp_tail m n x ) ( 0).
Proof.
  intros m n x Hn. apply qeq_imp_qeqT. induction n as [| n IH]; simpl.
  - reflexivity.
  - destruct (Nat.leb m n) eqn:E.
    + exfalso. apply Nat.leb_le in E. lia.
    + assert (Hn' : (n <= m)%nat) by lia.
      rewrite (IH Hn'). ring.
Qed.

Lemma exp_tail_abs_le_m : forall m n A, (n <= m)%nat ->QeqT ( exp_tail_abs m n A ) ( 0).
Proof.
  intros m n A Hn. apply qeq_imp_qeqT. induction n as [| n IH]; simpl.
  - reflexivity.
  - destruct (Nat.leb m n) eqn:E.
    + exfalso. apply Nat.leb_le in E. lia.
    + assert (Hn' : (n <= m)%nat) by lia.
      rewrite (IH Hn'). ring.
Qed.

(* Difference identity: for m <= n, [ep n - ep m == tail m n x], assembled by induction. *)
Lemma exp_partial_diff_tail : forall m n x, (m <= n)%nat ->QeqT (
  exp_partial n x - exp_partial m x ) ( exp_tail m n x).
Proof.
  intros m n x Hmn.
  revert Hmn.
  induction n as [| n IH]; intros Hmn.
  - apply qeq_imp_qeqT. assert (Hm0 : (m = 0)%nat) by lia. subst m. reflexivity.
  - apply qeq_imp_qeqT. simpl.
    destruct (Nat.leb m n) eqn:E.
    + apply Nat.leb_le in E.
      assert (Hring : exp_partial n x + q_pow x (Datatypes.S n) / q_fact (Datatypes.S n) - exp_partial m x ==
                      (exp_partial n x - exp_partial m x) + q_pow x (Datatypes.S n) / q_fact (Datatypes.S n)).
      { ring. }
      rewrite Hring. rewrite (qeqT_imp_qeq _ _ (IH E)). reflexivity.
    + apply Nat.leb_gt in E.
      assert (Hm : (m = Datatypes.S n)%nat) by lia. subst m.
      simpl.
      assert (Hle : (n <= Datatypes.S n)%nat) by lia.
      rewrite (qeqT_imp_qeq _ _ (exp_tail_le_m (Datatypes.S n) n x Hle)).
      ring.
Qed.

(* Triangle inequality: |tail| <= tail_abs. *)
Lemma exp_tail_abs_le : forall m n x,
  QleT' (Qabs (exp_tail m n x)) (exp_tail_abs m n (Qabs x)).
Proof.
  intros m n x. apply Qle_to_QleT'. induction n as [| n IH]; simpl.
  - unfold Qle; simpl; lia.
  - destruct (Nat.leb m n) eqn:E.
    + apply (Qle_trans _ (Qabs (exp_tail m n x) + Qabs (q_pow x (Datatypes.S n) / q_fact (Datatypes.S n))) _).
      * apply Qabs_triangle.
      * apply Qplus_le_compat;
          [ exact IH
          | (apply QleT'_to_Qle; apply qeq_le; apply qeq_imp_qeqT; apply (qeqT_imp_qeq _ _ (q_abs_pow_fact x n))) ].
    + setoid_rewrite (Qplus_0_r (exp_tail_abs m n (Qabs x))).
      apply (Qle_trans _ (Qabs (exp_tail m n x)) _).
      * apply QleT'_to_Qle. apply qeq_le.
      apply qeq_imp_qeqT.
        apply (Qabs_wd (exp_tail m n x + 0) (exp_tail m n x)). ring.
      * exact IH.
Qed.

(* The tail sum is at most (A^m/m!) * geo_sum (Datatypes.S (n-m)), by induction on [n] with [geo_sum] as the intermediate bound. *)
Lemma exp_tail_abs_geom : forall (A : Q) (m n : nat),
  QleT' 0 A ->
  (forall t : nat, NatLe m t -> QleT' (Qmult (1 + 1)%Q A) (Z.of_nat (t + 1) # 1)) ->
  (m <= n)%nat ->
  QleT' (exp_tail_abs m n A) ((q_pow A m / q_fact m) * geo_sum (Datatypes.S (n - m))).
Proof.
  intros A m n HA Hgeom Hmn.
  revert Hmn.
  induction n as [| n IH]; intros Hmn.
  - apply Qle_to_QleT'. assert (Hm0 : (m = 0)%nat) by lia. subst m.
    simpl. unfold Qle; simpl; lia.
  - (* Only [exp_tail_abs] is unfolded here; [simpl] on the whole goal would distort the [geo_sum] index. *)
    apply Qle_to_QleT'.
    change (exp_tail_abs m (Datatypes.S n) A)
      with (exp_tail_abs m n A + (if Nat.leb m n then q_pow A (Datatypes.S n) / q_fact (Datatypes.S n) else 0)).
    destruct (Nat.leb m n) eqn:Emn.
    + apply Nat.leb_le in Emn.
      apply (Qle_trans _ ((q_pow A m / q_fact m) * geo_sum (Datatypes.S (n - m))
                          + (q_pow A m / q_fact m) * q_pow (1 / 2)%Q (Datatypes.S (n - m))) _).
      * apply Qplus_le_compat.
        -- exact (QleT'_to_Qle _ _ (IH Emn)).
        -- apply (Qle_trans _ (q_pow A (m + Datatypes.S (n - m)) / q_fact (m + Datatypes.S (n - m))) _).
           ++ apply QleT'_to_Qle. apply qeq_le.
           apply qeq_imp_qeqT.
              assert (Hn : (Datatypes.S n = m + Datatypes.S (n - m))%nat) by lia.
              rewrite Hn. reflexivity.
           ++ exact (QleT'_to_Qle _ _ (pow_fact_geom_iter A m (n - m) HA Hgeom)).
      * replace (Datatypes.S ((Datatypes.S n) - m))%nat with (Datatypes.S (Datatypes.S (n - m)))%nat by lia.
        apply QleT'_to_Qle. apply qeq_le.
        apply qeq_imp_qeqT.
        change (geo_sum (Datatypes.S (Datatypes.S (n - m))))
          with (geo_sum (Datatypes.S (n - m)) + q_pow (1 / 2)%Q (Datatypes.S (n - m))).
        ring.
    + apply Nat.leb_gt in Emn.
      assert (Hle : (n <= m)%nat) by lia.
      rewrite (qeqT_imp_qeq _ _ (exp_tail_abs_le_m m n A Hle)).
      replace (Datatypes.S ((Datatypes.S n) - m))%nat with (Datatypes.S 0)%nat by lia.
      simpl.
      apply (Qle_trans _ (q_pow A m / q_fact m) _).
      * apply QleT'_to_Qle. apply q_pow_fact_nonneg. exact HA.
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
Qed.

(* The tail sum is at most (A^m/m!) * 2, finishing with geo_sum <= 2. *)
Lemma exp_tail_abs_geom2 : forall (A : Q) (m n : nat),
  QleT' 0 A ->
  (forall t : nat, NatLe m t -> QleT' (Qmult (1 + 1)%Q A) (Z.of_nat (t + 1) # 1)) ->
  (m <= n)%nat ->
  QleT' (exp_tail_abs m n A) ((q_pow A m / q_fact m) * (1 + 1)%Q).
Proof.
  intros A m n HA Hgeom Hmn.
  apply Qle_to_QleT'.
  apply (Qle_trans _ ((q_pow A m / q_fact m) * geo_sum (Datatypes.S (n - m))) _).
  - apply QleT'_to_Qle. apply exp_tail_abs_geom; assumption.
  - apply (Qle_trans _ (geo_sum (Datatypes.S (n - m)) * (q_pow A m / q_fact m)) _).
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
    + apply (Qle_trans _ ((1 + 1)%Q * (q_pow A m / q_fact m)) _).
      * apply (Qmult_le_compat_r (geo_sum (Datatypes.S (n - m))) (1 + 1)%Q (q_pow A m / q_fact m)).
        -- apply QleT'_to_Qle. apply geo_sum_le_two.
        -- apply QleT'_to_Qle. apply q_pow_fact_nonneg. exact HA.
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
Qed.

(* A^b/b! <= (A^(N0)/N0!) * (1/2)^(b-N0) for b >= N0, by one application of the iterated decay. *)
Lemma pow_fact_decay : forall (A : Q) (N0 b : nat),
  QleT' 0 A ->
  (forall t : nat, NatLe N0 t -> QleT' (Qmult (1 + 1)%Q A) (Z.of_nat (t + 1) # 1)) ->
  (N0 <= b)%nat ->
  QleT' (q_pow A b / q_fact b) ((q_pow A N0 / q_fact N0) * q_pow (1 / 2)%Q (b - N0)).
Proof.
  intros A N0 b HA Hgeom HNb.
  apply Qle_to_QleT'.
  destruct (Nat.sub b N0) as [| j] eqn:E.
  - assert (Hb : (b = N0)%nat) by lia. subst b.
    apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. simpl. ring.
  - assert (Hb : (b = N0 + Datatypes.S j)%nat) by lia. subst b.
    exact (QleT'_to_Qle _ _ (pow_fact_geom_iter A N0 j HA Hgeom)).
Qed.

(* Final decay: (A^b/b!) * 2 < eps for b >= N0 + S t, given C * (1/2)^(S t) < eps. *)
Lemma exp_tail_arch : forall (A : Q) (N0 t b : nat) (eps : Q),
  QleT' 0 A ->
  (forall u : nat, NatLe N0 u -> QleT' (Qmult (1 + 1)%Q A) (Z.of_nat (u + 1) # 1)) ->
  QltT 0 eps ->
  QltT (((q_pow A N0 / q_fact N0) * (1 + 1)%Q) * q_pow (1 / 2)%Q (Datatypes.S t)) eps ->
  (N0 + Datatypes.S t <= b)%nat ->
  QltT ((q_pow A b / q_fact b) * (1 + 1)%Q) eps.
Proof.
  intros A N0 t b eps HA Hgeom Hep Hdec Hb.
  apply Qlt_to_QltT.
  apply (Qle_lt_trans _ (((q_pow A N0 / q_fact N0) * q_pow (1 / 2)%Q (b - N0)) * (1 + 1)%Q) _).
  - apply (Qmult_le_compat_r (q_pow A b / q_fact b)
                             ((q_pow A N0 / q_fact N0) * q_pow (1 / 2)%Q (b - N0))
                             (1 + 1)%Q).
    + apply QleT'_to_Qle. apply pow_fact_decay; [exact HA | exact Hgeom | lia].
    + apply QleT'_to_Qle. apply Q2_nonneg.
  - apply (Qle_lt_trans _ (((q_pow A N0 / q_fact N0) * (1 + 1)%Q) * q_pow (1 / 2)%Q (Datatypes.S t)) _).
    + apply (Qle_trans _ (((q_pow A N0 / q_fact N0) * (1 + 1)%Q) * q_pow (1 / 2)%Q (b - N0)) _).
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
      * apply (Qle_trans _ (q_pow (1 / 2)%Q (b - N0) * ((q_pow A N0 / q_fact N0) * (1 + 1)%Q)) _).
        -- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
        -- apply (Qle_trans _ (q_pow (1 / 2)%Q (Datatypes.S t) * ((q_pow A N0 / q_fact N0) * (1 + 1)%Q)) _).
           ++ apply (Qmult_le_compat_r (q_pow (1 / 2)%Q (b - N0)) (q_pow (1 / 2)%Q (Datatypes.S t))
                                      ((q_pow A N0 / q_fact N0) * (1 + 1)%Q)).
              ** apply QleT'_to_Qle. apply (q_half_pow_mono (b - N0) (Datatypes.S t)). lia.
              ** apply QleT'_to_Qle. apply (q_pow_fact2_nonneg A N0 HA).
           ++ apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
    + exact (QltT_to_Qlt _ _ Hdec).
Qed.

(* Main bound: for m <= n, |ep n - ep m| <= (A^m/m!) * 2. *)
Lemma exp_partial_diff_bound : forall (x A : Q) (m n : nat),QeqT (
  A ) ( Qabs x )->
  QleT' 0 A ->
  (forall t : nat, NatLe m t -> QleT' (Qmult (1 + 1)%Q A) (Z.of_nat (t + 1) # 1)) ->
  (m <= n)%nat ->
  QleT' (Qabs (exp_partial n x - exp_partial m x)) ((q_pow A m / q_fact m) * (1 + 1)%Q).
Proof.
  intros x A m n HxA HAp Hgeom Hmn.
  apply Qle_to_QleT'.
  assert (Hsym : QeqT (Qabs x) A)
    by (apply qeq_imp_qeqT; apply Qeq_sym; apply qeqT_imp_qeq; exact HxA).
  apply (Qle_trans _ (exp_tail_abs m n A) _).
  - apply (Qle_trans _ (exp_tail_abs m n (Qabs x)) _).
    + apply (Qle_trans _ (Qabs (exp_tail m n x)) _).
      * apply QleT'_to_Qle. apply qeq_le.
      apply qeq_imp_qeqT.
        apply (Qabs_wd (exp_partial n x - exp_partial m x) (exp_tail m n x)).
        apply qeqT_imp_qeq. apply exp_partial_diff_tail. exact Hmn.
      * apply QleT'_to_Qle. apply exp_tail_abs_le.
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply (qeqT_imp_qeq _ _ (exp_tail_abs_wd _ _ _ _ Hsym)).
  - apply QleT'_to_Qle. apply exp_tail_abs_geom2; assumption.
Qed.

(* ===== Main theorem: the partial sums of exp form a Cauchy sequence (Set level, no global assumptions) ===== *)
Lemma exp_partial_cauchy : forall (x : Q) (eps : Q), QltT 0 eps ->
  sigT (fun N : nat => forall m n : nat, NatLe N m -> NatLe N n ->
    QltT (Qabs (exp_partial m x - exp_partial n x)) eps).
Proof.
  intros x eps Hep.
  set (A := Qabs x).
  assert (HA : Qle 0 A) by (unfold A; apply Qabs_nonneg).
  destruct (q_arch_geom A) as [N0 HN0].
  set (C := (q_pow A N0 / q_fact N0) * (1 + 1)%Q).
  assert (HC : QleT' 0 C) by (unfold C; apply q_pow_fact2_nonneg; exact (Qle_to_QleT' _ _ HA)).
  destruct (arch_decay C eps HC Hep) as [t Hdec].
  exists (N0 + Datatypes.S t)%nat.
  intros m n Hm Hn.
  apply NatLe_drop in Hm. apply NatLe_drop in Hn.
  destruct (Nat.leb m n) eqn:Emn.
  - (* Case m <= n: bound through the base point m. *)
    assert (Hmn : (m <= n)%nat) by (apply Nat.leb_le; exact Emn).
    assert (Hbound : Qle (Qabs (exp_partial n x - exp_partial m x))
                         ((q_pow A m / q_fact m) * (1 + 1)%Q)).
    { apply (QleT'_to_Qle _ _). apply (exp_partial_diff_bound x A m n).
      - apply qeq_imp_qeqT. reflexivity.
      - exact (Qle_to_QleT' _ _ HA).
      - intros u Hu. apply NatLe_drop in Hu. apply (HN0 u). apply NatLe_lift. lia.
      - exact Hmn. }
    assert (Hlt : Qlt ((q_pow A m / q_fact m) * (1 + 1)%Q) eps).
    { apply (QltT_to_Qlt _ _). apply (exp_tail_arch A N0 t m eps (Qle_to_QleT' _ _ HA) (fun u Hu => HN0 u Hu) Hep Hdec). lia. }
    apply Qlt_to_QltT.
    apply (Qle_lt_trans _ (Qabs (exp_partial n x - exp_partial m x)) _).
    + apply QleT'_to_Qle. apply qeq_le.
    apply qeq_imp_qeqT.
      rewrite (Qabs_Qminus (exp_partial m x) (exp_partial n x)). reflexivity.
    + exact (Qle_lt_trans _ ((q_pow A m / q_fact m) * (1 + 1)%Q) _ Hbound Hlt).
  - (* Case n < m: bound through the base point n; the conclusion then has exactly the shape of the bound. *)
    assert (Hnm : (n <= m)%nat) by (apply Nat.leb_gt in Emn; lia).
    assert (Hbound : Qle (Qabs (exp_partial m x - exp_partial n x))
                         ((q_pow A n / q_fact n) * (1 + 1)%Q)).
    { apply (QleT'_to_Qle _ _). apply (exp_partial_diff_bound x A n m).
      - apply qeq_imp_qeqT. reflexivity.
      - exact (Qle_to_QleT' _ _ HA).
      - intros u Hu. apply NatLe_drop in Hu. apply (HN0 u). apply NatLe_lift. lia.
      - exact Hnm. }
    assert (Hlt : Qlt ((q_pow A n / q_fact n) * (1 + 1)%Q) eps).
    { apply (QltT_to_Qlt _ _). apply (exp_tail_arch A N0 t n eps (Qle_to_QleT' _ _ HA) (fun u Hu => HN0 u Hu) Hep Hdec). lia. }
    apply Qlt_to_QltT.
    apply (Qle_lt_trans _ ((q_pow A n / q_fact n) * (1 + 1)%Q) _ Hbound Hlt).
Qed.

End QExpPartial.
(* ============================================================ *)
(* Missing Q-layer links together with the Real-layer exponential. *)
(* ============================================================ *)
(* ================= Missing Q-layer links ================= *)

(* 1. Monotonicity of powers: 0 <= A <= B implies A^n <= B^n. *)
Lemma q_pow_mono : forall (A B : Q) (n : nat),
  QleT' 0 A -> QleT' A B -> QleT' (q_pow A n) (q_pow B n).
Proof.
  intros A B n HA HAB. apply Qle_to_QleT'. induction n as [| m IH]; simpl.
  - exact (Qle_refl 1).
  - exact (Qmult_le_compat_nonneg A B (q_pow A m) (q_pow B m)
  (conj (QleT'_to_Qle _ _ HA) (QleT'_to_Qle _ _ HAB))
  (conj (QleT'_to_Qle _ _ (q_pow_nonneg A m HA)) IH)).
Qed.

(* 2. The exp series: exp_series n B = the sum of B^j / j! for j <= n, definitionally isomorphic to [exp_partial n x]. *)
Fixpoint exp_series (n : nat) (B : Q) : Q :=
  match n with
  | 0%nat => 1%Q
  | Datatypes.S m => exp_series m B + q_pow B (Datatypes.S m) / q_fact (Datatypes.S m)
  end.

(* 3. One-step monotonicity: 0 <= B implies exp_series n B <= exp_series (S n) B (nonnegative summands). *)
Lemma exp_series_step_mono : forall (B : Q) (n : nat), QleT' 0 B ->
  QleT' (exp_series n B) (exp_series (Datatypes.S n) B).
Proof.
  intros B n HB. apply Qle_to_QleT'. simpl.
  exact (Qle_plus_nonneg_r (exp_series n B)
  (q_pow B (Datatypes.S n) / q_fact (Datatypes.S n))
  (QleT'_to_Qle _ _ (q_pow_fact_nonneg B (Datatypes.S n) HB))).
Qed.

(* 4. Chained monotonicity: n <= m implies exp_series n B <= exp_series m B. *)
Lemma exp_series_mono : forall (B : Q) (n m : nat), QleT' 0 B -> (n <= m)%nat ->
  QleT' (exp_series n B) (exp_series m B).
Proof.
  intros B n m HB Hnm. apply Qle_to_QleT'. induction Hnm as [| m' _ IHIH].
  - exact (Qle_refl (exp_series n B)).
  - exact (Qle_trans (exp_series n B) (exp_series m' B)
  (exp_series (Datatypes.S m') B) IHIH (QleT'_to_Qle _ _ (exp_series_step_mono B m' HB))).
Qed.

(* 5. Nonnegativity of the tail: 0 <= A implies 0 <= exp_tail_abs m n A. *)
Lemma exp_tail_abs_nonneg : forall (m n : nat) (A : Q), QleT' 0 A -> QleT' 0 (exp_tail_abs m n A).
Proof.
  intros m n A HA. apply Qle_to_QleT'. induction n as [| n IH]; simpl.
  - exact (Qle_refl 0).
  - destruct (Nat.leb m n) eqn:E.
  + exact (Qle_trans 0 (exp_tail_abs m n A)
  (exp_tail_abs m n A + (q_pow A (Datatypes.S n) / q_fact (Datatypes.S n)))
  IH (Qle_plus_nonneg_r (exp_tail_abs m n A)
  (q_pow A (Datatypes.S n) / q_fact (Datatypes.S n))
  (QleT'_to_Qle _ _ (q_pow_fact_nonneg A (Datatypes.S n) HA)))).
  + exact (Qle_trans 0 (exp_tail_abs m n A) (exp_tail_abs m n A + 0) IH
  (Qle_plus_nonneg_r (exp_tail_abs m n A) 0 (Qle_refl 0))).
Qed.

(* 6. Tail monotonicity in the second argument: 0 <= A <= B implies exp_tail_abs m n A <= exp_tail_abs m n B. *)
Lemma exp_tail_abs_mono : forall (m n : nat) (A B : Q), QleT' 0 A -> QleT' A B ->
  QleT' (exp_tail_abs m n A) (exp_tail_abs m n B).
Proof.
  intros m n A B HA HAB. apply Qle_to_QleT'. induction n as [| n IH]; simpl.
  - exact (Qle_refl 0).
  - destruct (Nat.leb m n) eqn:E.
  + exact (Qplus_le_compat (exp_tail_abs m n A) (exp_tail_abs m n B)
  (q_pow A (Datatypes.S n) / q_fact (Datatypes.S n))
  (q_pow B (Datatypes.S n) / q_fact (Datatypes.S n)) IH
  (QleT'_to_Qle _ _ (Qle_div_same_denom (q_pow A (Datatypes.S n)) (q_pow B (Datatypes.S n))
  (q_fact (Datatypes.S n)) (q_fact_pos (Datatypes.S n))
  (q_pow_mono A B (Datatypes.S n) HA HAB)))).
  + exact (Qle_trans (exp_tail_abs m n A + 0) (exp_tail_abs m n A)
  (exp_tail_abs m n B + 0)
  (QleT'_to_Qle _ _ (qeq_imp_qle (exp_tail_abs m n A + 0) (exp_tail_abs m n A)
  (qeq_imp_qeqT (exp_tail_abs m n A + 0) (exp_tail_abs m n A)
   (Qplus_0_r (exp_tail_abs m n A)))))
  (Qle_trans (exp_tail_abs m n A) (exp_tail_abs m n B)
  (exp_tail_abs m n B + 0) IH
  (Qle_plus_nonneg_r (exp_tail_abs m n B) 0 (Qle_refl 0)))).
Qed.

(* 7b. Identity of [nat] successor literals: (S k)#1 + 1 == (S(S k))#1. *)
Lemma q_succ_add : forall (k : nat),QeqT (
  Qplus (Z.of_nat (Datatypes.S k) # 1) 1 ) ( Z.of_nat (Datatypes.S (Datatypes.S k)) # 1).
Proof.
  intros k.
  apply qeq_imp_qeqT.
  assert (Hn : Z.add (Z.of_nat (Datatypes.S k)) 1 = Z.of_nat (Datatypes.S (Datatypes.S k))) by lia.
  unfold Qeq, Qplus, Qred. simpl.
  rewrite (Pos.mul_1_r (PosDef.Pos.of_succ_nat k)).
  rewrite (Pos.mul_1_r (PosDef.Pos.add (PosDef.Pos.of_succ_nat k) 1)).
  rewrite (Pos.mul_1_r (PosDef.Pos.succ (PosDef.Pos.of_succ_nat k))).
  apply f_equal. apply Pos.add_1_r.
Qed.

(* 7. Power difference bound (in the form with [S n], no underflow): |x^(S n) - y^(S n)| <= |x-y| * ((S n)#1 * B^n). *)
Lemma q_pow_diff_bound : forall (x y B : Q) (n : nat),
  QleT' 0 B -> QleT' (Qabs x) B -> QleT' (Qabs y) B ->
  QleT' (Qabs (q_pow x (Datatypes.S n) - q_pow y (Datatypes.S n)))
      (Qmult (Qabs (x - y)) (Qmult (Z.of_nat (Datatypes.S n) # 1) (q_pow B n))).
Proof.
  intros x y B n HB Hx Hy.
  assert (HB' : Qle 0 B) by (apply QleT'_to_Qle; exact HB).
  assert (Hx' : Qle (Qabs x) B) by (apply QleT'_to_Qle; exact Hx).
  apply Qle_to_QleT'.
  induction n as [| m IH].
  - (* Case n = 0: |x^1 - y^1| = |x-y| <= |x-y| * (1#1 * B^0). *)
    rewrite (qeqT_imp_qeq _ _ (q_pow_succ x 0)), (qeqT_imp_qeq _ _ (q_pow_succ y 0)).
    setoid_replace (q_pow x 0) with 1 by reflexivity.
    assert (Hxy : Qmult x 1 - Qmult y 1 == x - y) by ring.
    apply (Qle_trans _ (Qabs (x - y)) _).
    { apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply (Qabs_wd (Qmult x 1 - Qmult y 1) (x - y)). exact Hxy. }
    { apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qeq_sym. apply Qmult_1_r. }
  - (* Case n = S m: split x * x^(S m) - y * y^(S m) into the two triangle terms and apply the IH. *)
    assert (Halg : q_pow x (Datatypes.S (Datatypes.S m)) - q_pow y (Datatypes.S (Datatypes.S m)) ==
                   x * (q_pow x (Datatypes.S m) - q_pow y (Datatypes.S m)) + (x - y) * q_pow y (Datatypes.S m)).
    { simpl. ring. }
    setoid_rewrite Halg.
    apply (Qle_trans _ (Qabs (Qmult x (q_pow x (Datatypes.S m) - q_pow y (Datatypes.S m))) +
                        Qabs (Qmult (x - y) (q_pow y (Datatypes.S m)))) _).
    + apply Qabs_triangle.
    + apply (Qle_trans _ (Qplus (Qmult (Qabs x) (Qabs (q_pow x (Datatypes.S m) - q_pow y (Datatypes.S m))))
                                (Qmult (Qabs (x - y)) (q_pow B (Datatypes.S m)))) _).
      * apply Qplus_le_compat.
        -- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qabs_Qmult.
        -- apply (Qle_trans _ (Qmult (Qabs (x - y)) (Qabs (q_pow y (Datatypes.S m)))) _).
           ++ apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qabs_Qmult.
           ++ apply (Qmult_le_compat_nonneg (Qabs (x - y)) (Qabs (x - y))
                                            (Qabs (q_pow y (Datatypes.S m))) (q_pow B (Datatypes.S m))).
              ** split; [apply Qabs_nonneg | apply Qle_refl].
              ** split; [apply Qabs_nonneg | (rewrite (qeqT_imp_qeq _ _ (q_pow_abs _ _)); apply (QleT'_to_Qle _ _); apply q_pow_mono; [apply Qle_to_QleT'; apply Qabs_nonneg | exact Hy])].
      * apply (Qle_trans _ (Qplus (Qmult B (Qmult (Qabs (x - y)) (Qmult (Z.of_nat (Datatypes.S m) # 1) (q_pow B m))))
                                  (Qmult (Qabs (x - y)) (q_pow B (Datatypes.S m)))) _).
        -- apply Qplus_le_compat.
           ++ apply (Qle_trans _ (Qmult B (Qabs (q_pow x (Datatypes.S m) - q_pow y (Datatypes.S m)))) _).
              ** apply (Qmult_le_compat_r (Qabs x) B (Qabs (q_pow x (Datatypes.S m) - q_pow y (Datatypes.S m)))).
                 ---- exact Hx'.
                 ---- apply Qabs_nonneg.
              ** apply (Qmult_le_compat_nonneg B B
                                            (Qabs (q_pow x (Datatypes.S m) - q_pow y (Datatypes.S m)))
                                            (Qmult (Qabs (x - y)) (Qmult (Z.of_nat (Datatypes.S m) # 1) (q_pow B m)))).
                 ---- split; [exact HB' | apply Qle_refl].
                 ---- split; [apply Qabs_nonneg | exact IH].
           ++ (* The second summand |x-y| * B^(S m) <= |x-y| * B^(S m) is reflexive (the goal has already been rewritten above). *)
              apply Qle_refl.
        -- (* Algebraic step: B * (|x-y| * (Sm#1 * B^m)) + |x-y| * B^(S m) == |x-y| * ((S(S m))#1 * B^(S m)). *)
           setoid_replace (Qmult B (Qmult (Qabs (x - y)) (Qmult (Z.of_nat (Datatypes.S m) # 1) (q_pow B m))))
             with (Qmult (Qabs (x - y)) (Qmult (Z.of_nat (Datatypes.S m) # 1) (q_pow B (Datatypes.S m)))).
           2: { assert (Hbs : q_pow B (Datatypes.S m) == B * q_pow B m) by (apply qeqT_imp_qeq; apply q_pow_succ).
                setoid_rewrite Hbs. ring. }
           setoid_replace (Qplus (Qmult (Qabs (x - y)) (Qmult (Z.of_nat (Datatypes.S m) # 1) (q_pow B (Datatypes.S m))))
                                 (Qmult (Qabs (x - y)) (q_pow B (Datatypes.S m))))
             with (Qmult (Qabs (x - y)) (Qmult (Qplus (Z.of_nat (Datatypes.S m) # 1) 1) (q_pow B (Datatypes.S m)))).
           2: ring.
           setoid_replace (Qmult (Qabs (x - y)) (Qmult (Qplus (Z.of_nat (Datatypes.S m) # 1) 1) (q_pow B (Datatypes.S m))))
             with (Qmult (Qabs (x - y)) (Qmult (Z.of_nat (Datatypes.S (Datatypes.S m)) # 1) (q_pow B (Datatypes.S m)))).
           2: { setoid_rewrite (qeqT_imp_qeq _ _ (q_succ_add m)). reflexivity. }
           apply Qle_refl.
Qed.

(* 8. Ratio cancellation: ((S k)#1 * B^k) / (S k)! == B^k / k!. *)
Lemma q_ratio_cancel_succ : forall (B : Q) (k : nat),QeqT (
  Qmult (Qmult (Z.of_nat (Datatypes.S k) # 1) (q_pow B k))
        (Qinv (q_fact (Datatypes.S k)))
  ) ( q_pow B k * Qinv (q_fact k)).
Proof.
  intros B k.
  apply qeq_imp_qeqT.
  setoid_rewrite (qeqT_imp_qeq _ _ (q_fact_succ k)).
  setoid_rewrite (Qinv_mult_distr (Z.of_nat (Datatypes.S k) # 1) (q_fact k)).
  setoid_replace (Qmult (Qmult (Z.of_nat (Datatypes.S k) # 1) (q_pow B k))
                        (Qmult (Qinv (Z.of_nat (Datatypes.S k) # 1)) (Qinv (q_fact k))))
    with (Qmult (Qmult (Qmult (Z.of_nat (Datatypes.S k) # 1) (Qinv (Z.of_nat (Datatypes.S k) # 1))) (q_pow B k)) (Qinv (q_fact k))).
  2: ring.
  rewrite (Qmult_inv_r (Z.of_nat (Datatypes.S k) # 1)).
  - ring.
  - unfold Qeq. simpl. lia.
Qed.

(* 9. Series difference bounded by the tail: n <= k implies exp_series k B - exp_series n B <= exp_tail_abs n k B. *)
Lemma exp_series_tail_le : forall (B : Q) (n k : nat), QleT' 0 B -> (n <= k)%nat ->
  QleT' (exp_series k B - exp_series n B) (exp_tail_abs n k B).
Proof.
  intros B n k HB Hnk.
  apply Qle_to_QleT'.
  revert n Hnk.
  induction k as [| k IH]; intros n Hnk.
  - (* Case k = 0: then n = 0. *)
    assert (Hn0 : n = 0%nat) by lia. subst n. simpl.
    apply Qle_refl.
  - simpl.
    destruct (Nat.leb n k) eqn:E.
    + apply Nat.leb_le in E.
      setoid_replace (exp_series k B + q_pow B (Datatypes.S k) / q_fact (Datatypes.S k) - exp_series n B)
        with (exp_series k B - exp_series n B + q_pow B (Datatypes.S k) / q_fact (Datatypes.S k)) by ring.
      apply (Qplus_le_compat (exp_series k B - exp_series n B) (exp_tail_abs n k B)
                             (q_pow B (Datatypes.S k) / q_fact (Datatypes.S k))
                             (q_pow B (Datatypes.S k) / q_fact (Datatypes.S k))).
      { apply IH. lia. }
      { apply Qle_refl. }
    + apply Nat.leb_gt in E.
      (* Case k < n: the difference is at most 0, and the tail sum is nonnegative. *)
      apply (Qle_trans _ 0 _).
      * (* exp_series (S k) B - exp_series n B <= 0 by monotonicity, since S k <= n. *)
        apply Qle_minus_iff.
        setoid_replace (0 + - (exp_series (Datatypes.S k) B - exp_series n B))
          with (exp_series n B - exp_series (Datatypes.S k) B) by ring.
        setoid_replace (exp_series n B - exp_series (Datatypes.S k) B)
          with (exp_series n B + - exp_series (Datatypes.S k) B) by ring.
        apply (proj1 (Qle_minus_iff (exp_series (Datatypes.S k) B) (exp_series n B))).
        apply (QleT'_to_Qle _ _). apply exp_series_mono; [exact HB | lia].
      * (* 0 <= exp_tail_abs n k B + 0. *)
        setoid_replace (exp_tail_abs n k B + 0) with (exp_tail_abs n k B) by ring.
        apply (QleT'_to_Qle _ _). apply exp_tail_abs_nonneg. exact HB.
Qed.

(* 10. Lipschitz property of the partial sums (in the form with [S n]):
       |x|, |y| <= B implies |ep_(S n) x - ep_(S n) y| <= |x-y| * exp_series n B. *)
Lemma exp_partial_lipschitz_succ : forall (x y B : Q) (n : nat),
  QleT' 0 B -> QleT' (Qabs x) B -> QleT' (Qabs y) B ->
  QleT' (Qabs (exp_partial (Datatypes.S n) x - exp_partial (Datatypes.S n) y))
      (Qmult (Qabs (x - y)) (exp_series n B)).
Proof.
  intros x y B n HB Hx Hy.
  apply Qle_to_QleT'.
  induction n as [| m IH].
  - (* Case n = 0: |ep_1 x - ep_1 y| = |x - y| <= |x-y| * exp_series 0 B = |x-y| * 1. *)
    setoid_replace (exp_series 0 B) with 1.
    2: reflexivity.
    assert (H1 : exp_partial 1 x - exp_partial 1 y == x - y).
    { simpl. unfold Qdiv. simpl. field. }
    apply (Qle_trans _ (Qabs (x - y)) _).
    { apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply (Qabs_wd (exp_partial 1 x - exp_partial 1 y) (x - y)). exact H1. }
    { apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qeq_sym. apply Qmult_1_r. }
  - (* Case n = S m. *)
    assert (Hstep1 : exp_partial (Datatypes.S (Datatypes.S m)) x ==
                     exp_partial (Datatypes.S m) x + q_pow x (Datatypes.S (Datatypes.S m)) / q_fact (Datatypes.S (Datatypes.S m))).
    { reflexivity. }
    assert (Hstep2 : exp_partial (Datatypes.S (Datatypes.S m)) y ==
                     exp_partial (Datatypes.S m) y + q_pow y (Datatypes.S (Datatypes.S m)) / q_fact (Datatypes.S (Datatypes.S m))).
    { reflexivity. }
    assert (Hsplit : exp_partial (Datatypes.S (Datatypes.S m)) x - exp_partial (Datatypes.S (Datatypes.S m)) y ==
                     (exp_partial (Datatypes.S m) x - exp_partial (Datatypes.S m) y) +
                     (q_pow x (Datatypes.S (Datatypes.S m)) - q_pow y (Datatypes.S (Datatypes.S m))) * Qinv (q_fact (Datatypes.S (Datatypes.S m)))).
    { setoid_rewrite Hstep1. setoid_rewrite Hstep2. unfold Qdiv. ring. }
    setoid_rewrite Hsplit.
    apply (Qle_trans _ (Qabs (exp_partial (Datatypes.S m) x - exp_partial (Datatypes.S m) y) +
                        Qabs (Qmult (q_pow x (Datatypes.S (Datatypes.S m)) - q_pow y (Datatypes.S (Datatypes.S m)))
                                   (Qinv (q_fact (Datatypes.S (Datatypes.S m)))))) _).
    + apply Qabs_triangle.
    + (* Bound by |x-y| * (exp_series m B + B^(S m)/(S m)!), which equals |x-y| * exp_series (S m) B. *)
      apply (Qle_trans _ (Qplus (Qmult (Qabs (x - y)) (exp_series m B))
                                (Qmult (Qabs (x - y)) (q_pow B (Datatypes.S m) * Qinv (q_fact (Datatypes.S m))))) _).
      * apply Qplus_le_compat.
        -- exact IH.
        -- (* |(x^(S(S m)) - y^(S(S m))) / (S(S m)!)| <= |x-y| * (B^(S m) / (S m)!). *)
           apply (Qle_trans _ (Qmult (Qabs (q_pow x (Datatypes.S (Datatypes.S m)) - q_pow y (Datatypes.S (Datatypes.S m))))
                                     (Qinv (q_fact (Datatypes.S (Datatypes.S m))))) _).
           ++ (* |a / f| <= |a| * |1/f| == |a| / f, since f > 0 forces 1/f > 0. *)
              apply (Qle_trans _ (Qmult (Qabs (q_pow x (Datatypes.S (Datatypes.S m)) - q_pow y (Datatypes.S (Datatypes.S m))))
                                        (Qabs (Qinv (q_fact (Datatypes.S (Datatypes.S m)))))) _).
              ** apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qabs_Qmult.
              ** apply (Qmult_le_compat_nonneg (Qabs (q_pow x (Datatypes.S (Datatypes.S m)) - q_pow y (Datatypes.S (Datatypes.S m))))
                                                (Qabs (q_pow x (Datatypes.S (Datatypes.S m)) - q_pow y (Datatypes.S (Datatypes.S m))))
                                                (Qabs (Qinv (q_fact (Datatypes.S (Datatypes.S m)))))
                                                (Qinv (q_fact (Datatypes.S (Datatypes.S m))))).
                 --- split; [apply Qabs_nonneg | apply Qle_refl].
                 --- split.
                     ---- apply Qabs_nonneg.
                     ---- assert (Hinvpos : Qlt 0 (Qinv (q_fact (Datatypes.S (Datatypes.S m))))).
                          { apply Qinv_lt_0_compat. apply (QltT_to_Qlt _ _). apply q_fact_pos. }
                          apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply (Qabs_pos (Qinv (q_fact (Datatypes.S (Datatypes.S m)))) (Qlt_le_weak 0 (Qinv (q_fact (Datatypes.S (Datatypes.S m)))) Hinvpos)).
           ++ (* |x^(S(S m)) - y^(S(S m))| / (S(S m)!) <= |x-y| * (B^(S m) / (S m)!). *)
              apply (Qle_trans _ (Qmult (Qmult (Qabs (x - y)) (Qmult (Z.of_nat (Datatypes.S (Datatypes.S m)) # 1) (q_pow B (Datatypes.S m))))
                                        (Qinv (q_fact (Datatypes.S (Datatypes.S m))))) _).
              ** apply (Qmult_le_compat_r (Qabs (q_pow x (Datatypes.S (Datatypes.S m)) - q_pow y (Datatypes.S (Datatypes.S m))))
                                          (Qmult (Qabs (x - y)) (Qmult (Z.of_nat (Datatypes.S (Datatypes.S m)) # 1) (q_pow B (Datatypes.S m))))
                                          (Qinv (q_fact (Datatypes.S (Datatypes.S m))))).
                  --- apply (QleT'_to_Qle _ _). apply (q_pow_diff_bound x y B (Datatypes.S m)); assumption.
                  --- apply (Qlt_le_weak 0 (Qinv (q_fact (Datatypes.S (Datatypes.S m))))).
                    apply Qinv_lt_0_compat. apply (QltT_to_Qlt _ _). apply q_fact_pos.
              ** (* (|x-y| * ((S(S m))#1 * B^(S m))) / (S(S m)!) <= |x-y| * (B^(S m) / (S m)!). *)
                 setoid_replace (Qmult (Qmult (Qabs (x - y)) (Qmult (Z.of_nat (Datatypes.S (Datatypes.S m)) # 1) (q_pow B (Datatypes.S m))))
                                       (Qinv (q_fact (Datatypes.S (Datatypes.S m)))))
                   with (Qmult (Qabs (x - y)) (Qmult (Qmult (Z.of_nat (Datatypes.S (Datatypes.S m)) # 1) (q_pow B (Datatypes.S m)))
                                                     (Qinv (q_fact (Datatypes.S (Datatypes.S m)))))).
                 2: ring.
                  apply (Qmult_le_compat_nonneg (Qabs (x - y)) (Qabs (x - y))
                                            (Qmult (Qmult (Z.of_nat (Datatypes.S (Datatypes.S m)) # 1) (q_pow B (Datatypes.S m)))
                                                   (Qinv (q_fact (Datatypes.S (Datatypes.S m)))))
                                            (Qmult (q_pow B (Datatypes.S m)) (Qinv (q_fact (Datatypes.S m))))).
                  --- split; [apply Qabs_nonneg | apply Qle_refl].
                  --- split.
                      ---- apply (Qmult_le_0_compat (Qmult (Z.of_nat (Datatypes.S (Datatypes.S m)) # 1) (q_pow B (Datatypes.S m)))
                                                    (Qinv (q_fact (Datatypes.S (Datatypes.S m))))).
                           { apply (Qmult_le_0_compat (Z.of_nat (Datatypes.S (Datatypes.S m)) # 1) (q_pow B (Datatypes.S m))).
                             - apply (Qlt_le_weak 0 (Z.of_nat (Datatypes.S (Datatypes.S m)) # 1)). unfold Qlt; simpl; lia.
                              - apply (QleT'_to_Qle _ _). apply q_pow_nonneg. exact HB. }
                            { apply (Qlt_le_weak 0 (Qinv (q_fact (Datatypes.S (Datatypes.S m))))). apply Qinv_lt_0_compat. apply (QltT_to_Qlt _ _). apply q_fact_pos. }
                      ---- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply (qeqT_imp_qeq _ _ (q_ratio_cancel_succ B (Datatypes.S m))).
      * (* Recombination: |x-y| * (exp_series m B + B^(S m)/(S m)!) == |x-y| * exp_series (S m) B. *)
        setoid_replace (Qplus (Qmult (Qabs (x - y)) (exp_series m B))
                              (Qmult (Qabs (x - y)) (q_pow B (Datatypes.S m) * Qinv (q_fact (Datatypes.S m)))))
          with (Qmult (Qabs (x - y)) (exp_series m B + q_pow B (Datatypes.S m) * Qinv (q_fact (Datatypes.S m)))).
        2: ring.
        apply QleT'_to_Qle. apply qeq_le.
        apply qeq_imp_qeqT.
        change (exp_series (Datatypes.S m) B) with (exp_series m B + q_pow B (Datatypes.S m) * Qinv (q_fact (Datatypes.S m))).
        reflexivity.
Qed.

(* 11. Bounded difference (the <= form): |y| <= B and m <= n imply |ep_n y - ep_m y| <= (B^m/m!) * 2. *)
Lemma exp_partial_diff_bound_le : forall (x B : Q) (m n : nat),
  QleT' 0 B -> QleT' (Qabs x) B ->
  (forall t : nat, NatLe m t -> QleT' (Qmult (1 + 1)%Q B) (Z.of_nat (t + 1) # 1)) ->
  (m <= n)%nat ->
  QleT' (Qabs (exp_partial n x - exp_partial m x)) ((q_pow B m / q_fact m) * (1 + 1)%Q).
Proof.
  intros x B m n HB Hx Hgeom Hmn.
  apply Qle_to_QleT'.
  apply (Qle_trans _ (exp_tail_abs m n B) _).
  - apply (Qle_trans _ (exp_tail_abs m n (Qabs x)) _).
    + apply (Qle_trans _ (Qabs (exp_tail m n x)) _).
      * apply QleT'_to_Qle. apply qeq_le.
      apply qeq_imp_qeqT.
        apply (Qabs_wd (exp_partial n x - exp_partial m x) (exp_tail m n x)).
        apply (qeqT_imp_qeq _ _ (exp_partial_diff_tail m n x Hmn)).
      * apply (QleT'_to_Qle _ _). apply exp_tail_abs_le.
    + apply (QleT'_to_Qle _ _). apply exp_tail_abs_mono; [apply Qle_to_QleT'; apply Qabs_nonneg | exact Hx].
  - apply (QleT'_to_Qle _ _). apply exp_tail_abs_geom2; assumption.
Qed.

(* 12. Uniform Cauchy modulus: for |y| <= B, the differences |ep_m y - ep_n y| have a modulus uniform in y (m, n >= N). *)
Lemma exp_partial_cauchy_bounded : forall (B : Q) (eps : Q),
  QleT' 0 B -> QltT 0 eps ->
  sigT (fun N : nat => forall m n : nat, NatLe N m -> NatLe N n ->
    forall y : Q, QleT' (Qabs y) B ->
      QltT (Qabs (exp_partial m y - exp_partial n y)) eps).
Proof.
  intros B eps HB Hep.
  destruct (q_arch_geom B) as [N0 HN0].
  set (C := (q_pow B N0 / q_fact N0) * (1 + 1)%Q).
  assert (HC : Qle 0 C) by (unfold C; apply (QleT'_to_Qle _ _); apply q_pow_fact2_nonneg; exact HB).
  destruct (arch_decay C eps (Qle_to_QleT' _ _ HC) Hep) as [t Hdec].
  exists (N0 + Datatypes.S t)%nat.
  intros m n Hm Hn y Hy.
  apply NatLe_drop in Hm. apply NatLe_drop in Hn.
  destruct (Nat.leb m n) eqn:Emn.
  - assert (Hmn : (m <= n)%nat) by (apply Nat.leb_le; exact Emn).
    assert (Hbound : Qle (Qabs (exp_partial n y - exp_partial m y))
                         ((q_pow B m / q_fact m) * (1 + 1)%Q)).
    { apply (QleT'_to_Qle _ _). apply (exp_partial_diff_bound_le y B m n); try exact HB; try exact Hy.
      - intros u Hu. apply NatLe_drop in Hu. apply (HN0 u). apply NatLe_lift. lia.
      - exact Hmn. }
    assert (Hlt : Qlt ((q_pow B m / q_fact m) * (1 + 1)%Q) eps).
    { apply (QltT_to_Qlt _ _). apply (exp_tail_arch B N0 t m eps HB (fun u Hu => HN0 u Hu) Hep Hdec). lia. }
    apply Qlt_to_QltT.
  apply (Qle_lt_trans _ (Qabs (exp_partial n y - exp_partial m y)) _).
  + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. rewrite (Qabs_Qminus (exp_partial m y) (exp_partial n y)). reflexivity.
  + exact (Qle_lt_trans _ ((q_pow B m / q_fact m) * (1 + 1)%Q) _ Hbound Hlt).
  - assert (Hnm : (n <= m)%nat) by (apply Nat.leb_gt in Emn; lia).
    assert (Hbound : Qle (Qabs (exp_partial m y - exp_partial n y))
                         ((q_pow B n / q_fact n) * (1 + 1)%Q)).
    { apply (QleT'_to_Qle _ _). apply (exp_partial_diff_bound_le y B n m); try exact HB; try exact Hy.
      - intros u Hu. apply NatLe_drop in Hu. apply (HN0 u). apply NatLe_lift. lia.
      - exact Hnm. }
    assert (Hlt : Qlt ((q_pow B n / q_fact n) * (1 + 1)%Q) eps).
    { apply (QltT_to_Qlt _ _). apply (exp_tail_arch B N0 t n eps HB (fun u Hu => HN0 u Hu) Hep Hdec). lia. }
    apply Qlt_to_QltT.
    apply (Qle_lt_trans _ ((q_pow B n / q_fact n) * (1 + 1)%Q) _ Hbound Hlt).
Qed.

(* 13. Uniform bound for the exp series: 0 <= B implies there is C >= 1 with exp_series n B <= C for all n. *)
Lemma exp_series_arch : forall (B : Q), QleT' 0 B ->
  sigT (fun C : Q => And (QleT' 1 C) (forall n : nat, QleT' (exp_series n B) C)).
Proof.
  intros B HB.
  destruct (q_arch_geom B) as [N0 HN0].
  set (C := exp_series N0 B + (q_pow B N0 / q_fact N0) * (1 + 1)%Q).
  exists C.
  split.
  - (* The bound 1 <= C. *)
    apply Qle_to_QleT'.
    unfold C.
    apply (Qle_trans _ (exp_series N0 B) _).
    + setoid_replace 1 with (exp_series 0 B).
      2: reflexivity.
      apply (QleT'_to_Qle _ _). apply exp_series_mono; [exact HB | lia].
    + apply (Qle_plus_nonneg_r (exp_series N0 B) ((q_pow B N0 / q_fact N0) * (1 + 1)%Q)).
      apply (QleT'_to_Qle _ _). apply q_pow_fact2_nonneg. exact HB.
  - (* The bound exp_series n B <= C for every n. *)
    intro n.
    apply Qle_to_QleT'.
    destruct (Nat.leb n N0) eqn:En.
    + apply Nat.leb_le in En.
      apply (Qle_trans _ (exp_series N0 B) _).
      * apply (QleT'_to_Qle _ _). apply exp_series_mono; [exact HB | exact En].
      * unfold C. apply (Qle_plus_nonneg_r (exp_series N0 B) ((q_pow B N0 / q_fact N0) * (1 + 1)%Q)).
        apply (QleT'_to_Qle _ _). apply q_pow_fact2_nonneg. exact HB.
    + apply Nat.leb_gt in En.
      apply (Qle_trans _ (exp_series N0 B + (q_pow B N0 / q_fact N0) * (1 + 1)%Q) _).
      * apply (Qle_trans _ (exp_series N0 B + exp_tail_abs N0 n B) _).
        -- (* exp_series n B <= exp_series N0 B + exp_tail_abs N0 n B, equivalently the difference is at most the tail. *)
           apply Qle_minus_iff.
           setoid_replace (exp_series N0 B + exp_tail_abs N0 n B + - exp_series n B)
             with (exp_tail_abs N0 n B - (exp_series n B - exp_series N0 B)) by ring.
           setoid_replace (exp_tail_abs N0 n B - (exp_series n B - exp_series N0 B))
             with (exp_tail_abs N0 n B + - (exp_series n B - exp_series N0 B)) by ring.
           apply (proj1 (Qle_minus_iff (exp_series n B - exp_series N0 B) (exp_tail_abs N0 n B))).
            apply (QleT'_to_Qle _ _). apply (exp_series_tail_le B N0 n HB). lia.
        -- apply (Qplus_le_compat _ _ _ _); [apply Qle_refl | apply (QleT'_to_Qle _ _); apply (exp_tail_abs_geom2 B N0 n HB)].
           { intros u Hu. apply NatLe_drop in Hu. apply (HN0 u). apply NatLe_lift. lia. }
           { lia. }
      * unfold C. apply Qle_refl.
Qed.

(* 14. Lipschitz property in general (including m = 0): |x|, |y| <= B implies |ep_m x - ep_m y| <= |x-y| * exp_series m B. *)

(* 14. The Lipschitz property in general (including m = 0): |x|, |y| <= B implies |ep_m x - ep_m y| <= |x-y| * exp_series m B. *)
Lemma exp_partial_lipschitz : forall (x y B : Q) (m : nat),
  QleT' 0 B -> QleT' (Qabs x) B -> QleT' (Qabs y) B ->
  QleT' (Qabs (exp_partial m x - exp_partial m y))
      (Qmult (Qabs (x - y)) (exp_series m B)).
Proof.
  intros x y B m HB Hx Hy.
  apply Qle_to_QleT'.
  destruct m as [| m'].
  - (* Case m = 0: |1 - 1| = 0 <= |x-y| * 1. *)
    assert (Hz : Qabs (exp_partial 0 x - exp_partial 0 y) == 0).
    { change (Qabs (1%Q - 1%Q) == 0). assert (Hm : 1%Q - 1%Q == 0) by reflexivity. rewrite Hm. reflexivity. }
    rewrite Hz.
    apply (Qmult_le_0_compat (Qabs (x - y)) 1).
    + apply Qabs_nonneg.
    + apply QleT'_to_Qle. apply Qle_0_1.
  - (* Case m = S m': the successor Lipschitz bound plus monotonicity of [exp_series] (exp_series m' B <= exp_series (S m') B). *)
    apply (Qle_trans _ (Qmult (Qabs (x - y)) (exp_series m' B)) _).
    + apply (QleT'_to_Qle _ _). exact (exp_partial_lipschitz_succ x y B m' HB Hx Hy).
    + apply (Qmult_le_compat_nonneg (Qabs (x - y)) (Qabs (x - y))
                                    (exp_series m' B) (exp_series (Datatypes.S m') B)).
      * split; [apply Qabs_nonneg | apply Qle_refl].
      * split.
        -- assert (Hpos : Qlt 0 (exp_series m' B)).
           { apply (Qlt_le_trans _ 1 _); [reflexivity | (setoid_replace 1 with (exp_series 0 B) by reflexivity; apply (QleT'_to_Qle _ _); apply exp_series_mono; [exact HB | lia])]. }
           apply (Qlt_le_weak 0 (exp_series m' B)). exact Hpos.
        -- apply (QleT'_to_Qle _ _). apply exp_series_step_mono. exact HB.
Qed.

(* 15. Definition of the real exponential: the diagonal sequence of the exp partial sums, proved Cauchy constructively with no global assumptions. *)
Definition cauchy_real_exp (x : Real) : Real.
Proof.
  destruct x as [u Hu].
  exists (fun n : nat => exp_partial n (u n)).
  intros eps Heps.
  destruct (real_norm_bounded (existT (fun s : Qseq => cauchy s) u Hu)) as [M [HMpos HM]].
  (* [exp_series_arch] consumes [Set] input, weakened through [qltT_leT'] without any erasure. *)
  destruct (exp_series_arch M (qltT_leT' 0 M HMpos)) as [C [HC1 HC]].
  assert (HCposT : QltT 0 C).
  { apply (qltT_leT'_ltT 0 1 C). exact qltT_0_1. exact HC1. }
  (* N1: the modulus given by [Hu (eps / (2*C))] through the positivity chain in [Set]. *)
  destruct (Hu (eps / (2 * C))%Q) as [N1 HN1].
  { apply (qltT_div_pos eps (2 * C)).
    - exact Heps.
    - apply (qmult_ltT_0_compat 2 C). exact qltT_0_2. exact HCposT. }
  (* N2: the modulus from [exp_partial_cauchy_bounded] (Set input). *)
  assert (Heps2 : QltT 0 (eps / 2)).
  { apply (qltT_div_pos eps 2). exact Heps. exact qltT_0_2. }
  destruct (exp_partial_cauchy_bounded M (eps / 2)%Q (qltT_leT' 0 M HMpos) Heps2) as [N2 HN2].
  exists (Nat.max N1 N2).
  intros m n Hm Hn.
  (* The splitting equality (by [ring]) rewrites the left side of the Set goal. *)
  apply (qltT_eq_compat_l (Qabs (exp_partial m (u m) - exp_partial m (u n) +
                                 (exp_partial m (u n) - exp_partial n (u n))))
                          (Qabs (exp_partial m (u m) - exp_partial n (u n)))
                          eps).
  - apply qeq_imp_qeqT. apply Qabs_wd. ring.
  - (* The Set-level chain: triangle inequality, term 1 <=T |Δu| * C, term 2 <T eps/2, and the sum <T eps/2 + eps/2 == eps. *)
    assert (HtriT : QleT' (Qabs (exp_partial m (u m) - exp_partial m (u n) +
                                 (exp_partial m (u n) - exp_partial n (u n))))
                          (Qabs (exp_partial m (u m) - exp_partial m (u n)) +
                           Qabs (exp_partial m (u n) - exp_partial n (u n)))).
    { apply Qle_to_QleT'. apply Qabs_triangle. }
    assert (Ht1T : QleT' (Qabs (exp_partial m (u m) - exp_partial m (u n)))
                         (Qabs (u m - u n) * C)).
    { apply (qleT'_trans (Qabs (exp_partial m (u m) - exp_partial m (u n)))
                         (Qabs (u m - u n) * exp_series m M)
                         (Qabs (u m - u n) * C)).
      - apply (exp_partial_lipschitz (u m) (u n) M m (qltT_leT' 0 M HMpos) (HM m) (HM n)).
      - apply (qleT'_mult_compat_l (exp_series m M) C (Qabs (u m - u n))).
        + apply qabs_nonnegT.
        + apply HC. }
    assert (Ht2T : QltT (Qabs (exp_partial m (u n) - exp_partial n (u n))) (eps / 2)).
    { apply (HN2 m n).
      - apply NatLe_lift. apply (Nat.le_trans _ (Nat.max N1 N2) _); [lia | exact (NatLe_drop _ _ Hm)].
      - apply NatLe_lift. apply (Nat.le_trans _ (Nat.max N1 N2) _); [lia | exact (NatLe_drop _ _ Hn)].
      - exact (HM n). }
    (* |Δu| * C <T eps/2: from |Δu| <T eps/(2C) with C >T 0, multiplying on the right and rewriting gives eps/2. *)
    assert (Ht3T : QltT (Qabs (u m - u n) * C) (eps / 2)).
    { apply (qltT_leT'_ltT (Qabs (u m - u n) * C) ((eps / (2 * C)) * C) (eps / 2)).
      - apply (qltT_mult_ltT_compat_r (Qabs (u m - u n)) (eps / (2 * C)) C).
        + exact HCposT.
        + apply (HN1 m n).
          * apply NatLe_lift. apply (Nat.le_trans _ (Nat.max N1 N2) _); [lia | exact (NatLe_drop _ _ Hm)].
          * apply NatLe_lift. apply (Nat.le_trans _ (Nat.max N1 N2) _); [lia | exact (NatLe_drop _ _ Hn)].
      - apply qeq_leT'.
        assert (Hf : (eps / (2 * C)) * C == eps / 2).
        { field.
          intro Hz.
          exact (Qlt_not_eq 0 C (QltT_to_Qlt 0 C HCposT) (Qeq_sym C 0 Hz)). }
        apply qeq_imp_qeqT. exact Hf. }
    (* Conclusion: the triangle sum = term 1 + term 2 <T |Δu| * C + eps/2 <T eps/2 + eps/2 ==T eps. *)
    apply (qleT'_ltT_ltT (Qabs (exp_partial m (u m) - exp_partial m (u n) +
                                (exp_partial m (u n) - exp_partial n (u n))))
                         (Qabs (exp_partial m (u m) - exp_partial m (u n)) +
                          Qabs (exp_partial m (u n) - exp_partial n (u n)))
                         eps);
      [ exact HtriT
      | apply (qltT_leT'_ltT _ (eps / 2 + eps / 2) eps);
        [ apply (qltT_leT'_ltT _ (Qabs (u m - u n) * C + eps / 2) _);
          [ apply (qleT'_plus_ltT_ltT (Qabs (exp_partial m (u m) - exp_partial m (u n)))
                                      (Qabs (u m - u n) * C)
                                      (Qabs (exp_partial m (u n) - exp_partial n (u n)))
                                      (eps / 2));
            [ exact Ht1T | exact Ht2T ]
          | apply qltT_leT';
            apply (qltT_plus_leT'_ltT (Qabs (u m - u n) * C) (eps / 2) (eps / 2) (eps / 2));
            [ exact Ht3T | apply qleT'_refl ] ]
        | apply qeq_leT'; apply qeq_imp_qeqT;
          assert (Hf3 : eps / 2 + eps / 2 == eps) by field;
          exact Hf3 ] ].
Defined.

(* ===== The exponential field ([cauchy_real_exp] and its properties) ===== *)

(* The partial exponential at 0 is identically 1: ep_n 0 == 1 (since 0^k = 0 for k >= 1). *)
Lemma exp_partial_zero : forall n,QeqT ( exp_partial n 0 ) ( 1).
Proof.
  intros.
  apply qeq_imp_qeqT.
  induction n as [| m IH]; simpl.
  - reflexivity.
  - rewrite IH.
    assert (Hpow : q_pow 0 (Datatypes.S m) == 0).
    { rewrite (qeqT_imp_qeq _ _ (q_pow_succ 0 m)). ring. }
    rewrite Hpow.
    unfold Qdiv.
    rewrite (Qmult_0_l (Qinv (q_fact (Datatypes.S m)))).
    ring.
Qed.

(* ===== Positivity of [cauchy_real_exp]: the partial sums of exp are eventually positive ===== *)

(* The paired sum: 1 + the sum of [(−a)^(2k−1)/(2k−1)! + (−a)^(2k)/(2k)!] for 1 <= k <= m. *)
Fixpoint exp_pair_alt (m : nat) (a : Q) : Q :=
  match m with
  | 0%nat => 1%Q
  | Datatypes.S m' => exp_pair_alt m' a +
                      (q_pow (- a) (Datatypes.S (2 * m')) / q_fact (Datatypes.S (2 * m')) +
                       q_pow (- a) (Datatypes.S (Datatypes.S (2 * m'))) / q_fact (Datatypes.S (Datatypes.S (2 * m'))))
  end.

(* The even truncation equals the paired sum: exp_partial (2m) (-a) == exp_pair_alt m a. *)
Lemma exp_even_pair : forall (a : Q) (m : nat),QeqT (
  exp_partial (2 * m) (- a) ) ( exp_pair_alt m a).
Proof.
  intros a m.
  apply qeq_imp_qeqT.
  induction m as [| m IH].
  - simpl. reflexivity.
  - assert (Hidx : (2 * Datatypes.S m)%nat = Datatypes.S (Datatypes.S (2 * m))) by lia.
    rewrite Hidx.
    simpl.
    setoid_rewrite IH.
    unfold Qdiv.
    ring.
Qed.

(* Even powers: (−a)^(2k) == a^(2k) (the sign disappears). *)
Lemma q_pow_neg_even : forall a k,QeqT ( q_pow (- a) (2 * k) ) ( q_pow a (2 * k)).
Proof.
  intros a k.
  apply qeq_imp_qeqT.
  induction k as [| k IH].
  - simpl. reflexivity.
  - assert (Hidx : (2 * Datatypes.S k)%nat = Datatypes.S (Datatypes.S (2 * k))) by lia.
    rewrite Hidx.
    setoid_rewrite (qeqT_imp_qeq _ _ (q_pow_succ (- a) (Datatypes.S (2 * k)))).
    setoid_rewrite (qeqT_imp_qeq _ _ (q_pow_succ a (Datatypes.S (2 * k)))).
    setoid_rewrite (qeqT_imp_qeq _ _ (q_pow_succ (- a) (2 * k))).
    setoid_rewrite (qeqT_imp_qeq _ _ (q_pow_succ a (2 * k))).
    setoid_rewrite IH.
    ring.
Qed.

(* Odd powers: (−a)^(2k+1) == −a^(2k+1). *)
Lemma q_pow_neg_odd : forall a k,QeqT (
  q_pow (- a) (Datatypes.S (2 * k)) ) ( - q_pow a (Datatypes.S (2 * k))).
Proof.
  intros a k.
  apply qeq_imp_qeqT.
  transitivity ((- a) * q_pow (- a) (2 * k)%nat).
  - apply (qeqT_imp_qeq _ _ (q_pow_succ (- a) (2 * k)%nat)).
  - transitivity ((- a) * q_pow a (2 * k)%nat).
    + setoid_rewrite (qeqT_imp_qeq _ _ (q_pow_neg_even a k)). reflexivity.
    + transitivity (- (a * q_pow a (2 * k)%nat)).
      * ring.
      * setoid_rewrite <- (qeqT_imp_qeq _ _ (q_pow_succ a (2 * k)%nat)). reflexivity.
Qed.

(* Nonnegativity of the paired term (positive tail): a >= 2k implies (−a)^(2k−1)/(2k−1)! + (−a)^(2k)/(2k)! >= 0. *)
Lemma exp_pair_term_nonneg : forall (a : Q) (k : nat),
  QleT' 0 a -> QleT' (Z.of_nat (2 * Datatypes.S k) # 1) a ->
  QleT' 0 (q_pow (- a) (Datatypes.S (2 * k)) / q_fact (Datatypes.S (2 * k)) +
         q_pow (- a) (Datatypes.S (Datatypes.S (2 * k))) / q_fact (Datatypes.S (Datatypes.S (2 * k)))).
Proof.
  intros a k Ha Hk.
  apply Qle_to_QleT'.
  (* The odd term is negative and the even term is positive; rewriting on the [Qeq] side, with [Qle_trans] bridging the [Qle] side. *)
  apply (Qle_trans _ (q_pow a (2 * Datatypes.S k) / q_fact (2 * Datatypes.S k) +
                     - (q_pow a (Datatypes.S (2 * k)) / q_fact (Datatypes.S (2 * k)))) _).
  - (* 0 <= C/D - (A/B) exactly when A/B <= C/D (A := a^(2k+1), B := (2k+1)!, C := a^(2k+2), D := (2k+2)!). *)
    apply (proj1 (Qle_minus_iff (q_pow a (Datatypes.S (2 * k)) / q_fact (Datatypes.S (2 * k)))
                                (q_pow a (2 * Datatypes.S k) / q_fact (2 * Datatypes.S k)))).
    apply (QleT'_to_Qle _ _).
    apply (q_le_div_le (q_pow a (Datatypes.S (2 * k))) (q_fact (Datatypes.S (2 * k)))
                       (q_pow a (2 * Datatypes.S k)) (q_fact (2 * Datatypes.S k))).
    + apply q_fact_pos.
    + apply q_fact_pos.
    + (* A*D <= C*B: D == (2*S k)#1 * B and C == a*A; after cancelling the nonnegative A*B factor, this follows from [Hk]. *)
      apply Qle_to_QleT'.
      assert (Hidx : (2 * Datatypes.S k)%nat = Datatypes.S (Datatypes.S (2 * k))) by lia.
      rewrite Hidx.
      setoid_replace (q_pow a (Datatypes.S (Datatypes.S (2 * k))))
        with (a * q_pow a (Datatypes.S (2 * k))).
      2: { apply (qeqT_imp_qeq _ _ (q_pow_succ a (Datatypes.S (2 * k)))). }
      setoid_replace (q_fact (Datatypes.S (Datatypes.S (2 * k))))
        with ((Z.of_nat (Datatypes.S (Datatypes.S (2 * k))) # 1) * q_fact (Datatypes.S (2 * k))).
      2: { apply (qeqT_imp_qeq _ _ (q_fact_succ (Datatypes.S (2 * k)))). }
      setoid_replace (q_pow a (Datatypes.S (2 * k)) *
                      ((Z.of_nat (Datatypes.S (Datatypes.S (2 * k))) # 1) * q_fact (Datatypes.S (2 * k))))
        with ((Z.of_nat (Datatypes.S (Datatypes.S (2 * k))) # 1) *
              (q_pow a (Datatypes.S (2 * k)) * q_fact (Datatypes.S (2 * k)))).
      2: ring.
      setoid_replace (a * q_pow a (Datatypes.S (2 * k)) * q_fact (Datatypes.S (2 * k)))
        with (a * (q_pow a (Datatypes.S (2 * k)) * q_fact (Datatypes.S (2 * k)))).
      2: ring.
      apply (Qmult_le_compat_r (Z.of_nat (Datatypes.S (Datatypes.S (2 * k))) # 1) a
                               (q_pow a (Datatypes.S (2 * k)) * q_fact (Datatypes.S (2 * k)))).
      * apply (Qle_trans _ (Z.of_nat (2 * Datatypes.S k) # 1) _).
        -- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. change ((Z.of_nat (Datatypes.S (Datatypes.S (2 * k))) # 1) == (Z.of_nat (2 * Datatypes.S k) # 1)). unfold Qeq. simpl. lia.
        -- exact (QleT'_to_Qle _ _ Hk).
      * apply Qmult_le_0_compat.
        -- apply (QleT'_to_Qle _ _). apply q_pow_nonneg. exact Ha.
        -- apply (Qlt_le_weak 0 (q_fact (Datatypes.S (2 * k)))). apply (QltT_to_Qlt _ _). apply q_fact_pos.
  - (* The rewritten form is equivalent to the original, P' == P, via [qeq_le]. *)
    apply QleT'_to_Qle. apply qeq_le.
    apply qeq_imp_qeqT.
    setoid_rewrite (qeqT_imp_qeq _ _ (q_pow_neg_odd a k)).
    assert (Hidx2 : (2 * Datatypes.S k)%nat = Datatypes.S (Datatypes.S (2 * k))) by lia.
    rewrite <- Hidx2.
    setoid_rewrite (qeqT_imp_qeq _ _ (q_pow_neg_even a (Datatypes.S k))).
    unfold Qdiv.
    ring.
Qed.

(* [cauchy_real_exp 0 == 1]: pointwise equality (ep_n 0 == 1 matches the constant-one sequence). *)
Lemma cauchy_real_exp_zero : real_eq (cauchy_real_exp real_zero) real_one.
Proof.
  intro eps. intro Heps.
  exists 0%nat.
  intros n Hn.
  simpl.
  (* Goal: QltT (Qabs (exp_partial n 0 - 1)) eps. *)
  assert (H1 : exp_partial n 0 - 1 == 0).
  { rewrite (qeqT_imp_qeq _ _ (exp_partial_zero n)). ring. }
  apply Qlt_to_QltT.
  apply (Qle_lt_trans _ 0 _).
  - apply QleT'_to_Qle. apply qeq_le.
  apply qeq_imp_qeqT.
    apply (Qabs_wd (exp_partial n 0 - 1) 0). exact H1.
  - apply QltT_to_Qlt. exact Heps.
Qed.

(* ============================================================ *)
(* The even/odd split, the [corr] correction structure, and the alternating sum [altf]. *)
(* Goal chain: esq_eq_corr (E_m^2 - O_m^2 == 1 + corr m a) -> exp_even_neg_nonneg *)
(*   -> exp_partial_tail_pos -> cauchy_real_exp_pos (the exp_neg_pos field of the Real layer). *)
(* Purely constructive at the [Set] level, with no global assumptions. *)
Section QExpEOSplit.
#[export] Instance Qinv_comp_proper : Proper (Qeq ==> Qeq) Qinv := Qinv_comp.

(* Registers the setoid form of [q_pow] (since [q_pow_wd] is a [Lemma], not an [Instance]). *)
#[export] Instance q_pow_comp_proper : Proper (Qeq ==> eq ==> Qeq) q_pow :=
  fun x y Hxy n m Hnm =>
    match Hnm with eq_refl =>
      qeqT_imp_qeq (q_pow x n) (q_pow y n) (q_pow_wd x y n (qeq_imp_qeqT x y Hxy)) end.

(* ============ Infrastructure: the even/odd split ============ *)

(* The even part: E_m(a) = the sum of a^(2k)/(2k)! for 0 <= k <= m. *)
Fixpoint e_sum (m : nat) (a : Q) : Q :=
  match m with
  | 0%nat => 1%Q
  | Datatypes.S m' => e_sum m' a + q_pow a (2 * Datatypes.S m') / q_fact (2 * Datatypes.S m')
  end.

(* The odd part: O_m(a) = the sum of a^(2k+1)/(2k+1)! for 0 <= k <= m-1. *)
Fixpoint o_sum (m : nat) (a : Q) : Q :=
  match m with
  | 0%nat => 0%Q
  | Datatypes.S m' => o_sum m' a + q_pow a (Datatypes.S (2 * m')) / q_fact (Datatypes.S (2 * m'))
  end.

(* The even/odd recurrences. *)
Lemma e_sum_succ : forall (a : Q) (m : nat),QeqT (
  e_sum (Datatypes.S m) a ) ( e_sum m a + q_pow a (2 * Datatypes.S m) / q_fact (2 * Datatypes.S m)).
Proof. intros. apply qeq_imp_qeqT. reflexivity. Qed.

Lemma o_sum_succ : forall (a : Q) (m : nat),QeqT (
  o_sum (Datatypes.S m) a ) ( o_sum m a + q_pow a (Datatypes.S (2 * m)) / q_fact (Datatypes.S (2 * m))).
Proof. intros. apply qeq_imp_qeqT. reflexivity. Qed.

(* The even truncation is E - O: S_(2m)(−a) == e_sum m a - o_sum m a. *)
Lemma e_o_split_even : forall (a : Q) (m : nat),QeqT (
  exp_partial (2 * m) (- a) ) ( e_sum m a - o_sum m a).
Proof.
  intros a m.
  apply qeq_imp_qeqT.
  induction m as [| m IH].
  - reflexivity.
  - (* S_(2m+2)(−a) = S_(2m)(−a) + (−a)^(2m+1)/(2m+1)! + (−a)^(2m+2)/(2m+2)!. *)
    assert (Hidx : (2 * Datatypes.S m)%nat = Datatypes.S (Datatypes.S (2 * m))) by lia.
    rewrite Hidx.
    assert (Hstep : exp_partial (Datatypes.S (Datatypes.S (2 * m))) (- a) ==
            exp_partial (2 * m) (- a) +
            q_pow (- a) (Datatypes.S (2 * m)) / q_fact (Datatypes.S (2 * m)) +
            q_pow (- a) (Datatypes.S (Datatypes.S (2 * m))) / q_fact (Datatypes.S (Datatypes.S (2 * m)))).
    { reflexivity. }
    rewrite Hstep.
    setoid_rewrite IH.
    (* On the e_sum/o_sum side: unfold with the successor lemmas to keep the literal 2 * S m form, then rewrite [Hidx]. *)
    setoid_rewrite (qeqT_imp_qeq _ _ (e_sum_succ a m)).
    setoid_rewrite (qeqT_imp_qeq _ _ (o_sum_succ a m)).
    rewrite Hidx.
    (* Sign of the odd power: (−a)^(S(2m)) == −a^(S(2m)). *)
    setoid_rewrite (qeqT_imp_qeq _ _ (q_pow_neg_odd a m)).
    (* Sign of the even power: (−a)^(S(S(2m))) == a^(S(S(2m))); first restore the index to the literal 2 * S m form. *)
    rewrite <- Hidx.
    setoid_rewrite (qeqT_imp_qeq _ _ (q_pow_neg_even a (Datatypes.S m))).
    unfold Qdiv. ring.
Qed.

(* The even truncation of a positive argument is E + O: S_(2m)(a) == e_sum m a + o_sum m a. *)
Lemma e_o_split_pos : forall (a : Q) (m : nat),QeqT (
  exp_partial (2 * m) a ) ( e_sum m a + o_sum m a).
Proof.
  intros a m.
  apply qeq_imp_qeqT.
  induction m as [| m IH].
  - reflexivity.
  - assert (Hidx : (2 * Datatypes.S m)%nat = Datatypes.S (Datatypes.S (2 * m))) by lia.
    rewrite Hidx.
    assert (Hstep : exp_partial (Datatypes.S (Datatypes.S (2 * m))) a ==
            exp_partial (2 * m) a +
            q_pow a (Datatypes.S (2 * m)) / q_fact (Datatypes.S (2 * m)) +
            q_pow a (Datatypes.S (Datatypes.S (2 * m))) / q_fact (Datatypes.S (Datatypes.S (2 * m)))).
    { reflexivity. }
    rewrite Hstep.
    setoid_rewrite IH.
    setoid_rewrite (qeqT_imp_qeq _ _ (e_sum_succ a m)).
    setoid_rewrite (qeqT_imp_qeq _ _ (o_sum_succ a m)).
    rewrite Hidx.
    unfold Qdiv. ring.
Qed.

(* ============ Core: discrete convexity and extremal lemmas ============ *)

(* Squares are nonnegative: 0 <= x * x, proved directly by unfolding at the Q level (the product n * n is nonlinear and needs [nia]). *)
Lemma q_square_nonneg : forall x : Q, QleT' 0 (x * x).
Proof.
  intro x. apply Qle_to_QleT'. unfold Qle, Qmult. destruct x as [n d]. simpl. nia.
Qed.

(* The bracketed term (for j >= 1): brk2 k j a := 2 * a^(2k+2j) * [1/((2k+1)!(2j−1)!) - 1/((2k+2)!(2j−2)!)]. *)
Definition brk2 (k j : nat) (a : Q) : Q :=
  2 * q_pow a (2 * k + 2 * j) /
    (q_fact (2 * k + 1) * q_fact (2 * j - 1)) -
  2 * q_pow a (2 * k + 2 * j) /
    (q_fact (2 * k + 2) * q_fact (2 * j - 2)).

(* The inner sum: inner2 k J a := the sum of brk2 k j a for 1 <= j <= J. *)
Fixpoint inner2 (k J : nat) (a : Q) : Q :=
  match J with
  | 0%nat => 0
  | Datatypes.S J' => inner2 k J' a + brk2 k (Datatypes.S J') a
  end.

(* kloop m k a := the sum of inner2 k' (2m−k') a for k' from k to 2m−1, recursing with k decreasing (the outer argument m is not the recursion variable). *)
Fixpoint kloop (m k : nat) (a : Q) : Q :=
  match k with
  | 0%nat => 0
  | Datatypes.S k' => if Nat.leb m k then inner2 k (2 * m - k) a + kloop m k' a else 0
  end.

(* The correction sum: corr m a := kloop m (2m−1) a = the double sum of brk2 k j a over m <= k <= 2m−1 and 1 <= j <= 2m−k. *)
Definition corr (m : nat) (a : Q) : Q := kloop m (2 * m - 1) a.

(* Structure: the one-step equation for [inner2]. *)
Lemma inner2_succ : forall (k J : nat) (a : Q),QeqT (
  inner2 k (Datatypes.S J) a ) ( inner2 k J a + brk2 k (Datatypes.S J) a).
Proof. intros. apply qeq_imp_qeqT. reflexivity. Qed.

(* Structure: the one-step equation for [kloop] (a term is added once S k >= m; the branch condition of [kloop] tests the outer index k = S k'). *)
Lemma kloop_succ : forall (m k : nat) (a : Q),
  (m <= Datatypes.S k)%nat ->QeqT (
  kloop m (Datatypes.S k) a ) ( inner2 (Datatypes.S k) (2 * m - Datatypes.S k) a + kloop m k a).
Proof.
  intros m k a Hmk. simpl.
  apply qeq_imp_qeqT.
  assert (Hleb : Nat.leb m (Datatypes.S k) = true)
    by (apply (proj2 (Nat.leb_le m (Datatypes.S k))); exact Hmk).
  rewrite Hleb. reflexivity.
Qed.

(* The reciprocal is antitone: for 0 < x, 0 < y and y <= x one has [inv x <= inv y] (constructive: case analysis by [Qle_lt_or_eq]). *)
Lemma q_inv_le_contravar : forall (x y : Q),
  QltT 0 x -> QltT 0 y -> QleT' y x -> QleT' (Qinv x) (Qinv y).
Proof.
  intros x y Hx Hy Hyx.
  apply Qle_to_QleT'.
  assert (Hx' : Qlt 0 x) by (apply QltT_to_Qlt; exact Hx).
  assert (Hy' : Qlt 0 y) by (apply QltT_to_Qlt; exact Hy).
  assert (Hyx' : Qle y x) by (apply QleT'_to_Qle; exact Hyx).
  destruct (Qle_lt_or_eq y x Hyx') as [Hlt | Heq].
  - exact (Qlt_le_weak (Qinv x) (Qinv y)
    (proj1 (Qinv_lt_contravar y x Hy' Hx') Hlt)).
  - exact (QleT'_to_Qle (Qinv x) (Qinv y) (qeq_le (Qinv x) (Qinv y)
    (qeq_imp_qeqT (Qinv x) (Qinv y)
    (Qeq_sym (Qinv y) (Qinv x) (Qinv_comp y x Heq))))).
Qed.

(* Comparison of factorial pairs: for 1 <= j and 2j−1 <= 2k+2, (2k+1)!(2j−1)! <= (2k+2)!(2j−2)!. *)
Lemma q_fact_pair_le : forall (k j : nat), (1 <= j)%nat -> (2 * j <= 2 * k + 3)%nat ->
  QleT' (q_fact (2 * k + 1) * q_fact (2 * j - 1))
      (q_fact (2 * k + 2) * q_fact (2 * j - 2)).
Proof.
  intros k j Hj1 Hkj.
  apply Qle_to_QleT'.
  assert (Hidx1 : Datatypes.S (2 * k + 1) = (2 * k + 2)%nat) by lia.
  assert (Hidx2 : Datatypes.S (2 * j - 2) = (2 * j - 1)%nat) by lia.
  assert (Hf1 : q_fact (2 * k + 2) ==
          (Z.of_nat (2 * k + 2) # 1) * q_fact (2 * k + 1)).
  { rewrite <- Hidx1. apply (qeqT_imp_qeq _ _ (q_fact_succ (2 * k + 1))). }
  assert (Hf2 : q_fact (2 * j - 1) ==
          (Z.of_nat (2 * j - 1) # 1) * q_fact (2 * j - 2)).
  { rewrite <- Hidx2. apply (qeqT_imp_qeq _ _ (q_fact_succ (2 * j - 2))). }
  setoid_replace (q_fact (2 * k + 1) * q_fact (2 * j - 1)) with
    ((Z.of_nat (2 * j - 1) # 1) * (q_fact (2 * k + 1) * q_fact (2 * j - 2))).
  2: { setoid_rewrite Hf2. ring. }
  setoid_replace (q_fact (2 * k + 2) * q_fact (2 * j - 2)) with
    ((Z.of_nat (2 * k + 2) # 1) * (q_fact (2 * k + 1) * q_fact (2 * j - 2))).
  2: { setoid_rewrite Hf1. ring. }
  apply (Qmult_le_compat_r (Z.of_nat (2 * j - 1) # 1) (Z.of_nat (2 * k + 2) # 1)
                           (q_fact (2 * k + 1) * q_fact (2 * j - 2))).
  - unfold Qle. simpl. lia.
  - apply (Qmult_le_0_compat (q_fact (2 * k + 1)) (q_fact (2 * j - 2)));
      apply (Qlt_le_weak 0 (q_fact _)); apply (QltT_to_Qlt _ _); apply q_fact_pos.
Qed.

(* Nonnegativity of the bracketed term: 0 <= a, 1 <= j and 2j <= 2k+3 imply 0 <= brk2 k j a. *)
Lemma brk2_nonneg : forall (a : Q) (k j : nat),
  QleT' 0 a -> (1 <= j)%nat -> (2 * j <= 2 * k + 3)%nat -> QleT' 0 (brk2 k j a).
Proof.
  intros a k j Ha Hj1 Hkj.
  apply Qle_to_QleT'.
  unfold brk2.
  (* Factor as 2 * a^(2k+2j) * [1/((2k+1)!(2j−1)!) - 1/((2k+2)!(2j−2)!)]; the bracket is nonnegative. *)
  apply (Qle_trans _ (2 * q_pow a (2 * k + 2 * j) *
      (Qinv (q_fact (2 * k + 1) * q_fact (2 * j - 1)) -
       Qinv (q_fact (2 * k + 2) * q_fact (2 * j - 2)))) _).
  - (* 0 <= M: both factors are nonnegative. *)
    apply (Qmult_le_0_compat (2 * q_pow a (2 * k + 2 * j))
             (Qinv (q_fact (2 * k + 1) * q_fact (2 * j - 1)) -
              Qinv (q_fact (2 * k + 2) * q_fact (2 * j - 2)))).
    + apply (Qmult_le_0_compat 2 (q_pow a (2 * k + 2 * j))).
      * apply (Qlt_le_weak 0 2). unfold Qlt; simpl; lia.
      * apply (QleT'_to_Qle _ _). apply q_pow_nonneg. exact Ha.
    + (* The bracket: inv B - inv D >= 0 exactly when inv D <= inv B, by antitonicity of the reciprocal applied to B <= D. *)
      assert (HBD := q_fact_pair_le k j Hj1 Hkj).
      apply (proj1 (Qle_minus_iff (Qinv (q_fact (2 * k + 2) * q_fact (2 * j - 2)))
                                  (Qinv (q_fact (2 * k + 1) * q_fact (2 * j - 1))))).
      apply (QleT'_to_Qle _ _).
      apply (q_inv_le_contravar (q_fact (2 * k + 2) * q_fact (2 * j - 2))
                                (q_fact (2 * k + 1) * q_fact (2 * j - 1))).
      * apply Qlt_to_QltT. apply (Qmult_lt_0_compat (q_fact (2 * k + 2)) (q_fact (2 * j - 2)));
          apply QltT_to_Qlt; apply q_fact_pos.
      * apply Qlt_to_QltT. apply (Qmult_lt_0_compat (q_fact (2 * k + 1)) (q_fact (2 * j - 1)));
          apply QltT_to_Qlt; apply q_fact_pos.
      * exact HBD.
  - (* M <= brk2 is an equality of rewritten forms: unfold [Qdiv] and close by [ring]. *)
    apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qdiv. ring.
Qed.

(* Nonnegativity of the inner sum: 0 <= a and 2J <= 2k+3 imply 0 <= inner2 k J a. *)
Lemma inner2_nonneg : forall (a : Q) (k J : nat),
  QleT' 0 a -> (2 * J <= 2 * k + 3)%nat -> QleT' 0 (inner2 k J a).
Proof.
  intros a k J Ha HJ.
  apply Qle_to_QleT'.
  induction J as [| J IH]; simpl.
  - apply Qle_refl.
  - apply (Qle_trans _ (inner2 k J a) _).
    + apply IH. lia.
    + apply (Qle_plus_nonneg_r (inner2 k J a) (brk2 k (Datatypes.S J) a)).
      apply (QleT'_to_Qle _ _). apply brk2_nonneg; try exact Ha.
      * lia.  (* 1 <= S J *)
      * assert (Hj : (2 * Datatypes.S J <= 2 * k + 3)%nat) by lia.
        exact Hj.
Qed.

(* [kloop] is nonnegative unconditionally: 0 <= a implies 0 <= kloop m k a (terms with k < m contribute 0, terms with k >= m are nonnegative). *)
Lemma kloop_nonneg : forall (a : Q) (m k : nat), QleT' 0 a -> QleT' 0 (kloop m k a).
Proof.
  intros a m k Ha.
  apply Qle_to_QleT'.
  induction k as [| k' IH]; simpl.
  - apply Qle_refl.
  - destruct (Nat.leb m (Datatypes.S k')) eqn:E.
    + apply (Qle_trans _ (kloop m k' a) _).
      * exact IH.
      * setoid_replace (inner2 (Datatypes.S k') (2 * m - Datatypes.S k') a + kloop m k' a)
          with (kloop m k' a + inner2 (Datatypes.S k') (2 * m - Datatypes.S k') a) by ring.
        apply (Qle_plus_nonneg_r (kloop m k' a) (inner2 (Datatypes.S k') (2 * m - Datatypes.S k') a)).
        apply (QleT'_to_Qle _ _). apply inner2_nonneg; try exact Ha.
        apply Nat.leb_le in E.
        (* 2(2m - S k') <= 2(S k') + 3 follows from S k' >= m. *)
        assert (Hmid : (2 * (2 * m - Datatypes.S k') <= 2 * Datatypes.S k' + 3)%nat) by lia.
        exact Hmid.
    + apply Qle_refl.
Qed.

(* Nonnegativity of the correction sum: 0 <= a implies 0 <= corr m a. *)
Lemma corr_nonneg : forall (a : Q) (m : nat), QleT' 0 a -> QleT' 0 (corr m a).
Proof.
  intros a m Ha. unfold corr. exact (kloop_nonneg a m (2 * m - 1) Ha).
Qed.

(* ============ Main identity: E_m^2 - O_m^2 == 1 + corr m a (the core) ============ *)

(* The alternating factorial sum: altf N := the sum of (−1)^u/(u!(N−u)!) for 0 <= u <= N, the coefficients in the expansion of (1−1)^N. *)
Fixpoint altf_aux (N u : nat) : Q :=
  match u with
  | 0%nat => Qinv (q_fact N)
  | Datatypes.S u' => altf_aux N u' +
      q_pow (-1) (Datatypes.S u') / (q_fact (Datatypes.S u') * q_fact (N - Datatypes.S u'))
  end.
Definition altf (N : nat) : Q := altf_aux N N.

(* Factorial predecessor: 1 <= u implies u! == u#1 * (u−1)!. *)
Lemma q_fact_pred : forall u, (1 <= u)%nat ->QeqT (
  q_fact u ) ( (Z.of_nat u # 1) * q_fact (u - 1)).
Proof.
  intros u Hu.
  apply qeq_imp_qeqT.
  destruct u as [| u']; [lia | ].
  replace (Datatypes.S u' - 1)%nat with u' by lia.
  apply (qeqT_imp_qeq _ _ (q_fact_succ u')).
Qed.

(* Pascal-type splitting for [altf]: for u >= 1 and u <= N-1,
   N/(u!(N−u)!) == 1/((u−1)!(N−u)!) + 1/(u!(N−u−1)!). *)
Lemma pascal_split : forall (N u : nat),
  (1 <= u)%nat -> (u <= N - 1)%nat ->QeqT (
  (Z.of_nat N # 1) * Qinv (q_fact u * q_fact (N - u)) ) (
  Qinv (q_fact (u - 1) * q_fact (N - u)) + Qinv (q_fact u * q_fact (N - u - 1))).
Proof.
  intros N u Hu1 HuN.
  apply qeq_imp_qeqT.
  assert (Hf1 : q_fact u == (Z.of_nat u # 1) * q_fact (u - 1)) by (apply qeqT_imp_qeq; apply q_fact_pred; exact Hu1).
  assert (HNu : (1 <= N - u)%nat) by lia.
  assert (Hf2 : q_fact (N - u) == (Z.of_nat (N - u) # 1) * q_fact (N - u - 1))
    by (apply qeqT_imp_qeq; apply q_fact_pred; exact HNu).
  assert (Hsum : (Z.of_nat N # 1) == (Z.of_nat u # 1) + (Z.of_nat (N - u) # 1)).
  { unfold Qeq. simpl. lia. }
  assert (Hn1 : ~ (Z.of_nat u # 1) == 0) by (intro Hz0; assert (Hlt0 : QltT 0 (Z.of_nat u # 1)) by (apply Qlt_to_QltT; unfold Qlt; simpl; lia); destruct (q_neq_of_lt _ Hlt0 (qeq_imp_qeqT _ _ Hz0))).
  assert (Hn2 : ~ (Z.of_nat (N - u) # 1) == 0) by (intro Hz0; assert (Hlt0 : QltT 0 (Z.of_nat (N - u) # 1)) by (apply Qlt_to_QltT; unfold Qlt; simpl; lia); destruct (q_neq_of_lt _ Hlt0 (qeq_imp_qeqT _ _ Hz0))).
  assert (Hn3 : ~ q_fact (u - 1) == 0) by (intro Hz0; destruct (q_neq_of_lt _ (q_fact_pos (u - 1)) (qeq_imp_qeqT _ _ Hz0))).
  assert (Hn4 : ~ q_fact (N - u - 1) == 0) by (intro Hz0; destruct (q_neq_of_lt _ (q_fact_pos (N - u - 1)) (qeq_imp_qeqT _ _ Hz0))).
  (* Rewriting ([Qinv_comp_proper] is registered, so rewrites reach inside [Qinv]). *)
  setoid_rewrite Hf1.
  setoid_rewrite Hf2.
  (* Expanding [Qinv] over products, matching the original syntactic shape (the # literals must be parenthesized). *)
  setoid_rewrite (Qinv_mult_distr ((Z.of_nat u # 1) * q_fact (u - 1))
                                  ((Z.of_nat (N - u) # 1) * q_fact (N - u - 1))).
  setoid_rewrite (Qinv_mult_distr (Z.of_nat u # 1) (q_fact (u - 1))).
  setoid_rewrite (Qinv_mult_distr (Z.of_nat (N - u) # 1) (q_fact (N - u - 1))).
  setoid_rewrite (Qinv_mult_distr (q_fact (u - 1))
                                  ((Z.of_nat (N - u) # 1) * q_fact (N - u - 1))).
  setoid_rewrite (Qinv_mult_distr (Z.of_nat (N - u) # 1) (q_fact (N - u - 1))).
  setoid_rewrite (Qinv_mult_distr ((Z.of_nat u # 1) * q_fact (u - 1)) (q_fact (N - u - 1))).
  setoid_rewrite (Qinv_mult_distr (Z.of_nat u # 1) (q_fact (u - 1))).
  (* N == A + B; after atomizing, [field] finishes the identity (it recognizes [Qinv], with nonvanishing given by [HnA]/[HnB]). *)
  setoid_replace (Z.of_nat N # 1) with ((Z.of_nat u # 1) + (Z.of_nat (N - u) # 1))
    by exact Hsum.
  set (A := Z.of_nat u # 1).
  set (B := Z.of_nat (N - u) # 1).
  set (I3 := Qinv (q_fact (u - 1))).
  set (I4 := Qinv (q_fact (N - u - 1))).
  assert (HnA : ~ A == 0) by (unfold A; exact Hn1).
  assert (HnB : ~ B == 0) by (unfold B; exact Hn2).
  field.
  split; [exact HnA | exact HnB].
Qed.

(* The alternating sum vanishes: N >= 1 implies the sum of (−1)^u/(u!(N−u)!) over 0 <= u <= N is 0,
   by Pascal-type induction. Route: first prove altf_scal ((N#1) * altf N == 0) term by term with
   [pascal_split_mul], then regroup (the first sum equals -altf_aux (N-1) (N-1) and the second
   equals altf_aux (N-1) (N-1) - 1/(N-1)!); the boundary terms (N#1/N! at u = 0, the second sum's
   boundary 1/(N-1)!, and (−1)^N/(N−1)! at u = N) cancel through (−1)^(N−1) + (−1)^N = 0;
   [Qmult_integral] (with N#1 ≠ 0) then concludes altf N == 0. *)

(* The version of [pascal_split] multiplied through by c on both sides (used in the term-by-term decomposition of [altf]). *)
Lemma pascal_split_mul : forall (N u : nat) (c : Q),
  (1 <= u)%nat -> (u <= N - 1)%nat ->QeqT (
  c * ((Z.of_nat N # 1) * Qinv (q_fact u * q_fact (N - u))) ) (
  c * (Qinv (q_fact (u - 1) * q_fact (N - u)) + Qinv (q_fact u * q_fact (N - u - 1)))).
Proof.
  intros N u c Hu1 HuN.
  apply qeq_imp_qeqT.
  setoid_rewrite (qeqT_imp_qeq _ _ (pascal_split N u Hu1 HuN)).
  ring.
Qed.

(* Adjacent signs cancel: (−1)^N + (−1)^(S N) == 0. *)
Lemma q_pow_neg_alt : forall N,QeqT ( q_pow (-1) N + q_pow (-1) (Datatypes.S N) ) ( 0).
Proof.
  intro N.
  apply qeq_imp_qeqT.
  induction N as [| N IH].
  - simpl. ring.
  - simpl.
    setoid_replace ((-1) * q_pow (-1) N + (-1) * q_pow (-1) (Datatypes.S N))
      with ((q_pow (-1) N + q_pow (-1) (Datatypes.S N)) * (-1)) by ring.
    setoid_rewrite IH.
    ring.
Qed.

(* N#1/N! == 1/(N−1)!, cancelling through [q_fact_pred]. *)
Lemma q_fact_div_pred : forall N, (1 <= N)%nat ->QeqT (
  (Z.of_nat N # 1) * Qinv (q_fact N) ) ( Qinv (q_fact (N - 1))).
Proof.
  intros N HN.
  apply qeq_imp_qeqT.
  assert (Hf := qeqT_imp_qeq _ _ (q_fact_pred N HN)).
  assert (Hn : ~ (Z.of_nat N # 1) == 0) by (intro Hz0; assert (Hlt0 : QltT 0 (Z.of_nat N # 1)) by (apply Qlt_to_QltT; unfold Qlt; simpl; lia); destruct (q_neq_of_lt _ Hlt0 (qeq_imp_qeqT _ _ Hz0))).
  assert (Hfq : ~ q_fact (N - 1) == 0) by (intro Hz0; destruct (q_neq_of_lt _ (q_fact_pos (N - 1)) (qeq_imp_qeqT _ _ Hz0))).
  setoid_rewrite Hf.
  setoid_rewrite (Qinv_mult_distr (Z.of_nat N # 1) (q_fact (N - 1))).
  set (A := Z.of_nat N # 1).
  set (I := Qinv (q_fact (N - 1))).
  assert (HnA : ~ A == 0) by (unfold A; exact Hn).
  field.
  exact HnA.
Qed.

(* The first sum: s1 N u := the sum of (−1)^{u'} * Qinv(q_fact (u'−1) * q_fact (N−u')) for 1 <= u' <= u. *)
Fixpoint s1 (N u : nat) : Q :=
  match u with
  | 0%nat => 0
  | Datatypes.S u' => s1 N u' +
      q_pow (-1) (Datatypes.S u') * Qinv (q_fact (Datatypes.S u' - 1) * q_fact (N - Datatypes.S u'))
  end.

(* The second sum: s2 N u := the sum of (−1)^{u'} * Qinv(q_fact u' * q_fact (N−u'−1)) for 1 <= u' <= u. *)
Fixpoint s2 (N u : nat) : Q :=
  match u with
  | 0%nat => 0
  | Datatypes.S u' => s2 N u' +
      q_pow (-1) (Datatypes.S u') * Qinv (q_fact (Datatypes.S u') * q_fact (N - Datatypes.S u' - 1))
  end.

(* The recurrence for [altf_aux]: u <= N-1 implies altf_aux N (S u) == altf_aux N u + the next term. *)
Lemma altf_aux_succ : forall N u,QeqT (
  altf_aux N (Datatypes.S u) ) ( altf_aux N u +
  q_pow (-1) (Datatypes.S u) * Qinv (q_fact (Datatypes.S u) * q_fact (N - Datatypes.S u))).
Proof. intros. apply qeq_imp_qeqT. reflexivity. Qed.

(* Rearrangement of the first sum: 1 <= u <= N implies s1 N u == -altf_aux (N−1) (u−1). *)
Lemma s1_eq : forall N u, (1 <= u)%nat -> (u <= N)%nat ->QeqT (
  s1 N u ) ( - altf_aux (N - 1) (u - 1)).
Proof.
  intros N u Hu1 HuN.
  apply qeq_imp_qeqT.
  induction u as [| u' IHu].
  - lia.  (* u = 0 contradicts Hu1. *)
  - destruct u' as [| u''].
    + (* Case u = 1: s1 N 1 == -altf_aux (N−1) 0. *)
      simpl.
      setoid_rewrite (Qmult_1_l (q_fact (N - 1))).
      set (I := Qinv (q_fact (N - 1))).
      ring.
    + (* Case u = S (S u''): step along the recurrence. *)
      assert (Hidx1 : (Datatypes.S (Datatypes.S u'') - 1)%nat = Datatypes.S u'') by lia.
      assert (Hidx2 : (N - Datatypes.S (Datatypes.S u'') = (N - 1) - Datatypes.S u'')%nat) by lia.
      assert (Hs1 : s1 N (Datatypes.S (Datatypes.S u'')) ==
              s1 N (Datatypes.S u'') +
              q_pow (-1) (Datatypes.S (Datatypes.S u'')) *
                Qinv (q_fact (Datatypes.S (Datatypes.S u'') - 1) * q_fact (N - Datatypes.S (Datatypes.S u'')))).
      { reflexivity. }
      rewrite Hs1.
      rewrite Hidx1.
      rewrite Hidx2.
      assert (IHu' : s1 N (Datatypes.S u'') == - altf_aux (N - 1) (Datatypes.S u'' - 1)).
      { apply IHu; lia. }
      setoid_rewrite IHu'.
      assert (Haux := qeqT_imp_qeq _ _ (altf_aux_succ (N - 1)%nat u'')).
      setoid_rewrite Haux.
      assert (Hidx3 : (Datatypes.S u'' - 1)%nat = u'') by lia.
      rewrite Hidx3.
      setoid_rewrite (qeqT_imp_qeq _ _ (q_pow_succ (-1) (Datatypes.S u''))).
      set (J := Qinv (q_fact (Datatypes.S u'') * q_fact ((N - 1) - Datatypes.S u''))).
      set (K := altf_aux (N - 1) u'').
      ring.
Qed.
(* Rearrangement of the second sum: 1 <= u <= N-1 implies s2 N u == altf_aux (N−1) u - Qinv (q_fact (N−1)). *)
Lemma s2_eq : forall N u, (1 <= u)%nat -> (u <= N - 1)%nat ->QeqT (
  s2 N u ) ( altf_aux (N - 1) u - Qinv (q_fact (N - 1))).
Proof.
  intros N u Hu1 HuN.
  apply qeq_imp_qeqT.
  induction u as [| u' IHu].
  - lia.  (* u = 0 contradicts Hu1. *)
  - destruct u' as [| u''].
    + (* Case u = 1. *)
      simpl.
      assert (Hn2 : ((N - 1) - 1 = N - 2)%nat) by lia.
      rewrite Hn2.
      field.
      split; intro Hz0; destruct (q_neq_of_lt _ (q_fact_pos _) (qeq_imp_qeqT _ _ Hz0)).
    + (* Case u = S (S u''): step along the recurrence. *)
      assert (Hidx2 : (N - Datatypes.S (Datatypes.S u'') - 1 = (N - 1) - Datatypes.S (Datatypes.S u''))%nat) by lia.
      assert (Hs2 : s2 N (Datatypes.S (Datatypes.S u'')) ==
              s2 N (Datatypes.S u'') +
              q_pow (-1) (Datatypes.S (Datatypes.S u'')) *
                Qinv (q_fact (Datatypes.S (Datatypes.S u'')) * q_fact (N - Datatypes.S (Datatypes.S u'') - 1))).
      { reflexivity. }
      rewrite Hs2.
      rewrite Hidx2.
      assert (IHu' : s2 N (Datatypes.S u'') == altf_aux (N - 1) (Datatypes.S u'') - Qinv (q_fact (N - 1))).
      { apply IHu; lia. }
      setoid_rewrite IHu'.
      assert (Haux := qeqT_imp_qeq _ _ (altf_aux_succ (N - 1)%nat (Datatypes.S u''))).
      setoid_rewrite Haux.
      set (I2 := Qinv (q_fact (N - 1))).
      set (K := altf_aux (N - 1) (Datatypes.S u'')).
      set (J := Qinv (q_fact (Datatypes.S (Datatypes.S u'')) * q_fact ((N - 1) - Datatypes.S (Datatypes.S u'')))).
      ring.
Qed.

(* Specialization of [pascal_split] at u = 1 (normalized form: q_fact 0 -> 1, q_fact 1 -> 1, N−1−1 -> N−2; needs N >= 2). *)
Lemma pascal_split_one : forall N, (2 <= N)%nat ->QeqT (
  (Z.of_nat N # 1) * Qinv (q_fact 1 * q_fact (N - 1)) ) (
  Qinv (1 * q_fact (N - 1)) + Qinv (1 * q_fact (N - 2))).
Proof.
  intros N HN.
  apply qeq_imp_qeqT.
  assert (Hps := qeqT_imp_qeq _ _ (pascal_split N 1 ltac:(lia) ltac:(lia))).
  assert (Hf12 : (N - 1 - 1 = N - 2)%nat) by lia.
  setoid_replace (Qinv (1 * q_fact (N - 2))) with (Qinv (1 * q_fact (N - 1 - 1))).
  2: { rewrite <- Hf12. reflexivity. }
  exact Hps.
Qed.

(* Term-by-term decomposition of (N#1) * altf_aux N u: 1 <= u <= N-1 implies
   (N#1) * altf_aux N u == (N#1) * Qinv(q_fact N) + s1 N u + s2 N u. *)
Lemma altf_scal_aux : forall N u, (1 <= u)%nat -> (u <= N - 1)%nat ->QeqT (
  (Z.of_nat N # 1) * altf_aux N u ) (
  (Z.of_nat N # 1) * Qinv (q_fact N) + s1 N u + s2 N u).
Proof.
  intros N u Hu1 HuN.
  apply qeq_imp_qeqT.
  induction u as [| u' IHu].
  - lia.  (* u = 0 contradicts Hu1. *)
  - destruct u' as [| u''].
    + (* Case u = 1. *)
      simpl (altf_aux N 1).
      assert (Hps1 := qeqT_imp_qeq _ _ (pascal_split_one N ltac:(lia))).
      assert (Hs1' : s1 N 1 == q_pow (-1) 1 * Qinv (q_fact (1 - 1) * q_fact (N - 1))).
      { change (0 + q_pow (-1) 1 * Qinv (q_fact (1 - 1) * q_fact (N - 1)) ==
                q_pow (-1) 1 * Qinv (q_fact (1 - 1) * q_fact (N - 1))).
        set (I := Qinv (q_fact (1 - 1) * q_fact (N - 1))).
        ring. }
      assert (Hs2' : s2 N 1 == q_pow (-1) 1 * Qinv (q_fact 1 * q_fact (N - 1 - 1))).
      { change (0 + q_pow (-1) 1 * Qinv (q_fact 1 * q_fact (N - 1 - 1)) ==
                q_pow (-1) 1 * Qinv (q_fact 1 * q_fact (N - 1 - 1))).
        set (I := Qinv (q_fact 1 * q_fact (N - 1 - 1))).
        ring. }
      setoid_rewrite Hs1'. setoid_rewrite Hs2'.
      setoid_replace (q_pow (-1) 1) with (-1) by reflexivity.
      assert (Hf11 : (1 - 1 = 0)%nat) by lia.
      assert (Hf12 : (N - 1 - 1 = N - 2)%nat) by lia.
      rewrite Hf11. rewrite Hf12.
      assert (Hq0 : q_fact 0 == 1) by reflexivity.
      setoid_rewrite Hq0.
      setoid_replace ((Z.of_nat N # 1) * (Qinv (q_fact N) + (-1) * Qinv (q_fact 1 * q_fact (N - 1))))
        with ((Z.of_nat N # 1) * Qinv (q_fact N) + (-1) * ((Z.of_nat N # 1) * Qinv (q_fact 1 * q_fact (N - 1)))).
      2: { set (A := Z.of_nat N # 1). set (I0 := Qinv (q_fact N)). set (I1 := Qinv (q_fact 1 * q_fact (N - 1))). ring. }
      setoid_rewrite Hps1.
      set (A := Z.of_nat N # 1).
      set (I0 := Qinv (q_fact N)).
      set (I1 := Qinv (1 * q_fact (N - 1))).
      set (I2 := Qinv (1 * q_fact (N - 2))).
      ring.
    + (* Case u = S (S u''): step along the recurrence. *)
      assert (Hsucc := qeqT_imp_qeq _ _ (altf_aux_succ N (Datatypes.S u''))).
      setoid_rewrite Hsucc.
      assert (Hps := qeqT_imp_qeq _ _ (pascal_split_mul N (Datatypes.S (Datatypes.S u'')) (q_pow (-1) (Datatypes.S (Datatypes.S u''))) ltac:(lia) ltac:(lia))).
      setoid_replace ((Z.of_nat N # 1) * (altf_aux N (Datatypes.S u'') +
          q_pow (-1) (Datatypes.S (Datatypes.S u'')) * Qinv (q_fact (Datatypes.S (Datatypes.S u'')) * q_fact (N - Datatypes.S (Datatypes.S u'')))))
        with ((Z.of_nat N # 1) * altf_aux N (Datatypes.S u'') +
             q_pow (-1) (Datatypes.S (Datatypes.S u'')) * ((Z.of_nat N # 1) * Qinv (q_fact (Datatypes.S (Datatypes.S u'')) * q_fact (N - Datatypes.S (Datatypes.S u''))))).
      2: { set (I3 := Qinv (q_fact (Datatypes.S (Datatypes.S u'')) * q_fact (N - Datatypes.S (Datatypes.S u'')))). ring. }
      setoid_rewrite Hps.
      setoid_rewrite (IHu ltac:(lia) ltac:(lia)).
      assert (Hs1' : s1 N (Datatypes.S (Datatypes.S u'')) ==
              s1 N (Datatypes.S u'') + q_pow (-1) (Datatypes.S (Datatypes.S u'')) * Qinv (q_fact (Datatypes.S (Datatypes.S u'') - 1) * q_fact (N - Datatypes.S (Datatypes.S u'')))).
      { reflexivity. }
      assert (Hs2' : s2 N (Datatypes.S (Datatypes.S u'')) ==
              s2 N (Datatypes.S u'') + q_pow (-1) (Datatypes.S (Datatypes.S u'')) * Qinv (q_fact (Datatypes.S (Datatypes.S u'')) * q_fact (N - Datatypes.S (Datatypes.S u'') - 1))).
      { reflexivity. }
      setoid_rewrite Hs1'. setoid_rewrite Hs2'.
      set (I0 := Qinv (q_fact N)).
      set (J := Qinv (q_fact (Datatypes.S (Datatypes.S u'')) * q_fact (N - Datatypes.S (Datatypes.S u'')))).
      set (K := Qinv (q_fact (Datatypes.S (Datatypes.S u'') - 1) * q_fact (N - Datatypes.S (Datatypes.S u'')))).
      set (L := Qinv (q_fact (Datatypes.S (Datatypes.S u'')) * q_fact (N - Datatypes.S (Datatypes.S u'') - 1))).
      ring.
Qed.

(* Difference form of [altf_aux]: 1 <= u <= N implies altf_aux N u == altf_aux N (u−1) + (−1)^u * Qinv(q_fact u * q_fact (N−u)). *)
Lemma altf_aux_diff : forall N u, (1 <= u)%nat -> (u <= N)%nat ->QeqT (
  altf_aux N u ) ( altf_aux N (u - 1) + q_pow (-1) u * Qinv (q_fact u * q_fact (N - u))).
Proof.
  intros N u Hu1 HuN.
  apply qeq_imp_qeqT.
  destruct u as [| u']; [lia | ].
  change (altf_aux N u' + q_pow (-1) (Datatypes.S u') * Qinv (q_fact (Datatypes.S u') * q_fact (N - Datatypes.S u')) ==
          altf_aux N (Datatypes.S u' - 1) + q_pow (-1) (Datatypes.S u') * Qinv (q_fact (Datatypes.S u') * q_fact (N - Datatypes.S u'))).
  assert (Hsu : (Datatypes.S u' - 1 = u')%nat) by lia.
  rewrite Hsu.
  reflexivity.
Qed.

(* (N#1) * altf N == 0 for N >= 1 (Pascal decomposition, regrouping, and boundary cancellation). *)
Lemma altf_scal : forall N, (1 <= N)%nat ->QeqT (
  (Z.of_nat N # 1) * altf N ) ( 0).
Proof.
  intros N HN.
  apply qeq_imp_qeqT.
  unfold altf.
  destruct N as [| N'].
  - lia.
  - destruct N' as [| N''].
    + (* Case N = 1: compute directly. *)
      simpl. field.
      all: try (intro Hz0; destruct (q_neq_of_lt _ (q_fact_pos _) (qeq_imp_qeqT _ _ Hz0))).
      all: try (match goal with |- ~ (?X == 0) =>
                  intro Hz0;
                  assert (Hlt0 : QltT 0 X) by (apply Qlt_to_QltT; unfold Qlt; simpl; lia);
                  destruct (q_neq_of_lt X Hlt0 (qeq_imp_qeqT _ _ Hz0)) end).
    + (* Case N = S (S N''): assemble the pieces (after [destruct] the name [N] is no longer available, so it is restored with [set]). *)
      set (N := Datatypes.S (Datatypes.S N'')).
      (* altf_aux N N == altf_aux N (N−1) + (−1)^N * Qinv(q_fact N * q_fact (N−N)). *)
      assert (Hstep : altf_aux N N == altf_aux N (N - 1) + q_pow (-1) N * Qinv (q_fact N * q_fact (N - N))).
      { change (altf_aux N (N - 1) + q_pow (-1) N * Qinv (q_fact N * q_fact (N - N)) ==
                altf_aux N (N - 1) + q_pow (-1) N * Qinv (q_fact N * q_fact (N - N))).
        reflexivity. }
      setoid_rewrite Hstep.
      (* Distribute (N#1) over altf_aux N (N−1) plus the tail term. *)
      setoid_replace ((Z.of_nat N # 1) * (altf_aux N (N - 1) +
          q_pow (-1) N * Qinv (q_fact N * q_fact (N - N))))
        with ((Z.of_nat N # 1) * altf_aux N (N - 1) +
             (Z.of_nat N # 1) * (q_pow (-1) N * Qinv (q_fact N * q_fact (N - N)))) by ring.
      assert (Hdec := qeqT_imp_qeq _ _ (altf_scal_aux N (N - 1)%nat ltac:(lia) ltac:(lia))).
      setoid_rewrite Hdec.
      (* The middle sum equals s1 N (N−1) + s2 N (N−1); regroup with [s1_eq]/[s2_eq]. *)
      assert (Hs1' := qeqT_imp_qeq _ _ (s1_eq N (N - 1)%nat ltac:(lia) ltac:(lia))).
      assert (Hs2' := qeqT_imp_qeq _ _ (s2_eq N (N - 1)%nat ltac:(lia) ltac:(lia))).
      setoid_rewrite Hs1'. setoid_rewrite Hs2'.
      (* (N#1) * Qinv(q_fact N) == Qinv(q_fact (N−1)). *)
      setoid_rewrite (qeqT_imp_qeq _ _ (q_fact_div_pred N HN)).
      (* Tail term: (N#1) * ((−1)^N * Qinv(q_fact N * q_fact (N−N))); here N−N = 0. *)
      assert (Hnn : (N - N = 0)%nat) by lia.
      rewrite Hnn.
      (* (N#1) * ((−1)^N * Qinv(q_fact N * q_fact 0)) == (−1)^N * Qinv(q_fact (N−1)), by [q_fact_div_pred] and q_fact 0 == 1. *)
      setoid_replace ((Z.of_nat N # 1) * (q_pow (-1) N * Qinv (q_fact N * q_fact 0)))
        with (q_pow (-1) N * ((Z.of_nat N # 1) * Qinv (q_fact N * q_fact 0))) by ring.
      assert (Hq0 : q_fact 0 == 1) by reflexivity.
      setoid_rewrite Hq0.
      setoid_rewrite (Qmult_1_r (q_fact N)).
      setoid_rewrite (qeqT_imp_qeq _ _ (q_fact_div_pred N HN)).
      (* Expand altf_aux (N−1) (N−1) by its difference form ([altf_aux_diff], unifying the N−1 shapes). *)
      assert (Hdiff := qeqT_imp_qeq _ _ (altf_aux_diff (N - 1)%nat (N - 1)%nat ltac:(lia) ltac:(lia))).
      setoid_replace (altf_aux (N - 1) (N - 1)) with
        (altf_aux (N - 1) (N - 1 - 1) + q_pow (-1) (N - 1) * Qinv (q_fact (N - 1) * q_fact (N - 1 - (N - 1)))) by exact Hdiff.
      assert (Hnn2 : ((N - 1) - (N - 1) = 0)%nat) by lia.
      rewrite Hnn2.
      setoid_rewrite Hq0.
      setoid_rewrite (Qmult_1_r (q_fact (N - 1))).
      (* Sign cancellation: (q_pow (−1) (N−1) + q_pow (−1) N) * I == 0. *)
      set (I := Qinv (q_fact (N - 1))).
      assert (Hneg : (q_pow (-1) (N - 1) + q_pow (-1) N) * I == 0).
      { assert (Hsucc : (N = Datatypes.S (N - 1))%nat) by lia.
        (* Rewrite only the index shape of q_pow (-1) N exactly; a global rewrite would also replace the N occurring inside N-1. *)
        setoid_replace (q_pow (-1) N) with (q_pow (-1) (Datatypes.S (N - 1))) by
          (apply (q_pow_comp_proper (-1) (-1) (Qeq_refl (-1)) N (Datatypes.S (N - 1)) Hsucc)).
        setoid_rewrite (qeqT_imp_qeq _ _ (q_pow_neg_alt (N - 1))).
        ring. }
      transitivity ((q_pow (-1) (N - 1) + q_pow (-1) N) * I).
      * ring.
      * exact Hneg.
Qed.
Lemma altf_zero : forall N, (1 <= N)%nat ->QeqT ( altf N ) ( 0).
Proof.
  intros N HN.
  apply qeq_imp_qeqT.
  (* From (N#1) * altf N == 0 together with N#1 ≠ 0. *)
  assert (Hmul := qeqT_imp_qeq _ _ (altf_scal N HN)).
  destruct (Qmult_integral (Z.of_nat N # 1) (altf N) Hmul) as [Hz | Ha].
  - exfalso.
    assert (Hlt0 : QltT 0 (Z.of_nat N # 1)) by (apply Qlt_to_QltT; unfold Qlt; simpl; lia).
    destruct (q_neq_of_lt (Z.of_nat N # 1) Hlt0 (qeq_imp_qeqT _ _ Hz)).
  - exact Ha.
Qed.

Lemma esq_succ : forall (a : Q) (m : nat),QeqT (
  e_sum (Datatypes.S m) a * e_sum (Datatypes.S m) a -
  o_sum (Datatypes.S m) a * o_sum (Datatypes.S m) a ) (
  (e_sum m a * e_sum m a - o_sum m a * o_sum m a) +
  (2 * e_sum m a * (q_pow a (2 * Datatypes.S m) / q_fact (2 * Datatypes.S m)) +
   (q_pow a (2 * Datatypes.S m) / q_fact (2 * Datatypes.S m)) *
   (q_pow a (2 * Datatypes.S m) / q_fact (2 * Datatypes.S m)) -
   2 * o_sum m a * (q_pow a (Datatypes.S (2 * m)) / q_fact (Datatypes.S (2 * m))) -
   (q_pow a (Datatypes.S (2 * m)) / q_fact (Datatypes.S (2 * m))) *
   (q_pow a (Datatypes.S (2 * m)) / q_fact (Datatypes.S (2 * m))))).
Proof.
  intros a m.
  apply qeq_imp_qeqT.
  setoid_rewrite (qeqT_imp_qeq _ _ (e_sum_succ a m)).
  setoid_rewrite (qeqT_imp_qeq _ _ (o_sum_succ a m)).
  unfold Qdiv. ring.
Qed.

(* One-step form of [corr]: corr (S m) == corr m + Δ', where Δ' matches the increment in [esq_succ] (the coefficients are matched in the pairing argument below). *)

(* ============ Route A: expansion into double sums ([esq_sum]/[osq_sum]) ============ *)

(* Additivity of exponents for [q_pow]: q_pow x (m+n) == q_pow x m * q_pow x n. *)

(* A row of the even double sum: esq_row N i a := the sum of a^(2N+2j)/((2N)!(2j)!) for 0 <= j <= i (fixed row N, columns up to i). *)
Fixpoint esq_row (N i : nat) (a : Q) : Q :=
  match i with
  | 0%nat => q_pow a (2 * N) / (q_fact (2 * N) * q_fact 0)
  | Datatypes.S i' => esq_row N i' a +
      q_pow a (2 * N + 2 * Datatypes.S i') / (q_fact (2 * N) * q_fact (2 * Datatypes.S i'))
  end.

(* The even double sum: esq_sum m a := the sum over 0 <= i, j <= m of a^(2i+2j)/((2i)!(2j)!). *)
Fixpoint esq_sum (m : nat) (a : Q) : Q :=
  match m with
  | 0%nat => 1%Q
  | Datatypes.S m' => esq_sum m' a +
      2 * esq_row (Datatypes.S m') m' a +
      q_pow a (2 * Datatypes.S m' + 2 * Datatypes.S m') /
        (q_fact (2 * Datatypes.S m') * q_fact (2 * Datatypes.S m'))
  end.

(* A row of the odd double sum: osq_row N i a := the sum of a^(2N+2j+2)/((2N+1)!(2j+1)!) for 0 <= j <= i. *)
Fixpoint osq_row (N i : nat) (a : Q) : Q :=
  match i with
  | 0%nat => q_pow a (2 * N + 2) / (q_fact (2 * N + 1) * q_fact 1)
  | Datatypes.S i' => osq_row N i' a +
      q_pow a (2 * N + 2 * Datatypes.S i' + 2) / (q_fact (2 * N + 1) * q_fact (2 * Datatypes.S i' + 1))
  end.

(* The odd double sum: osq_sum m a := the sum over 0 <= i, j <= m-1 of a^(2i+2j+2)/((2i+1)!(2j+1)!). *)
Fixpoint osq_sum (m : nat) (a : Q) : Q :=
  match m with
  | 0%nat => 0%Q
  | Datatypes.S m' => osq_sum m' a +
      (* The newly added row and column (i = m' or j = m', symmetric) contribute 2 * osq_row m' m' minus the diagonal, which would otherwise be counted twice. *)
      2 * osq_row m' m' a -
      q_pow a (2 * m' + 2 * m' + 2) / (q_fact (2 * m' + 1) * q_fact (2 * m' + 1))
  end.

(* A partial sum times a single term equals a row sum: E_m(a) * a^(2N)/(2N)! == esq_row N m a. *)
Lemma e_mul_term : forall (a : Q) (m N : nat),QeqT (
  e_sum m a * (q_pow a (2 * N) / q_fact (2 * N)) ) ( esq_row N m a).
Proof.
  intros a m N.
  apply qeq_imp_qeqT.
  induction m as [| m IH]; simpl.
  - (* Case m = 0: E_0 = 1, so 1 * T == esq_row N 0 = T. *)
    field.
    all: intro Hz0; destruct (q_neq_of_lt _ (q_fact_pos _) (qeq_imp_qeqT _ _ Hz0)).
  - (* [simpl] has already unfolded e_sum (S m) and esq_row N (S m); rewrite directly. *)
    setoid_replace ((e_sum m a + q_pow a (2 * Datatypes.S m) / q_fact (2 * Datatypes.S m)) *
        (q_pow a (2 * N) / q_fact (2 * N)))
      with (e_sum m a * (q_pow a (2 * N) / q_fact (2 * N)) +
            (q_pow a (2 * Datatypes.S m) / q_fact (2 * Datatypes.S m)) * (q_pow a (2 * N) / q_fact (2 * N))) by ring.
    setoid_rewrite IH.
    (* Identity for the tail term: accumulate the [q_pow] products ([Hmul]) and expand the [Qinv] denominator, in separate [transitivity] steps. *)
    assert (Hmul : q_pow a (2 * Datatypes.S m) * q_pow a (2 * N) == q_pow a (2 * N + 2 * Datatypes.S m)).
    { assert (Hc : (2 * Datatypes.S m + 2 * N = 2 * N + 2 * Datatypes.S m)%nat) by lia.
      apply Qeq_sym.
      rewrite <- Hc.
      apply qeqT_imp_qeq. apply (q_pow_add a (2 * Datatypes.S m) (2 * N)). }
    setoid_replace (q_pow a (2 * Datatypes.S m) / q_fact (2 * Datatypes.S m) *
        (q_pow a (2 * N) / q_fact (2 * N)))
      with (q_pow a (2 * N + 2 * Datatypes.S m) / (q_fact (2 * N) * q_fact (2 * Datatypes.S m))).
    2: { unfold Qdiv.
         transitivity ((q_pow a (2 * Datatypes.S m) * q_pow a (2 * N)) *
                       (Qinv (q_fact (2 * Datatypes.S m)) * Qinv (q_fact (2 * N)))).
         - ring.
         - setoid_replace (q_pow a (2 * Datatypes.S m) * q_pow a (2 * N))
             with (q_pow a (2 * N + 2 * Datatypes.S m)) by exact Hmul.
           setoid_rewrite (Qinv_mult_distr (q_fact (2 * N)) (q_fact (2 * Datatypes.S m))).
           ring. }
    (* Both sides of the main goal are definitionally equal (the [simpl]-unfolded shape versus the literal shape), so [reflexivity] closes. *)
    reflexivity.
Qed.

(* The square of the even partial sum equals the even double sum: E_m^2 == esq_sum m a. *)
Lemma e_sq_expand : forall (a : Q) (m : nat),QeqT (
  e_sum m a * e_sum m a ) ( esq_sum m a).
Proof.
  intros a m.
  apply qeq_imp_qeqT.
  induction m as [| m IH]; simpl.
  - ring.
  - setoid_rewrite (qeqT_imp_qeq _ _ (e_sum_succ a m)).
    (* (E_m + t)^2 == esq_sum m + 2 * esq_row (S m) m + the diagonal term. *)
    setoid_replace ((e_sum m a + q_pow a (2 * Datatypes.S m) / q_fact (2 * Datatypes.S m)) *
        (e_sum m a + q_pow a (2 * Datatypes.S m) / q_fact (2 * Datatypes.S m)))
      with (e_sum m a * e_sum m a +
            2 * (e_sum m a * (q_pow a (2 * Datatypes.S m) / q_fact (2 * Datatypes.S m))) +
            (q_pow a (2 * Datatypes.S m) / q_fact (2 * Datatypes.S m)) *
            (q_pow a (2 * Datatypes.S m) / q_fact (2 * Datatypes.S m))) by ring.
    setoid_rewrite IH.
    setoid_rewrite (qeqT_imp_qeq _ _ (e_mul_term a m (Datatypes.S m))).
    (* Aligning the diagonal term: a^(2(S m)) * a^(2(S m)) == a^(2(S m)+2(S m)). *)
    assert (Hdiag : q_pow a (2 * Datatypes.S m) * q_pow a (2 * Datatypes.S m) ==
                    q_pow a (2 * Datatypes.S m + 2 * Datatypes.S m)).
    { apply Qeq_sym. apply qeqT_imp_qeq. apply (q_pow_add a (2 * Datatypes.S m) (2 * Datatypes.S m)). }
    setoid_replace ((q_pow a (2 * Datatypes.S m) / q_fact (2 * Datatypes.S m)) *
        (q_pow a (2 * Datatypes.S m) / q_fact (2 * Datatypes.S m)))
      with (q_pow a (2 * Datatypes.S m + 2 * Datatypes.S m) /
            (q_fact (2 * Datatypes.S m) * q_fact (2 * Datatypes.S m))).
    2: { unfold Qdiv.
         transitivity ((q_pow a (2 * Datatypes.S m) * q_pow a (2 * Datatypes.S m)) *
                       (Qinv (q_fact (2 * Datatypes.S m)) * Qinv (q_fact (2 * Datatypes.S m)))).
         - ring.
         - setoid_replace (q_pow a (2 * Datatypes.S m) * q_pow a (2 * Datatypes.S m))
             with (q_pow a (2 * Datatypes.S m + 2 * Datatypes.S m)) by exact Hdiag.
           setoid_rewrite (Qinv_mult_distr (q_fact (2 * Datatypes.S m)) (q_fact (2 * Datatypes.S m))).
           ring. }
    reflexivity.
Qed.

(* ===== Odd-side double-sum expansion ([o_sq_expand], symmetric to [e_sq_expand]) ===== *)

(* One-step equation for the odd row: osq_row N (S i) == osq_row N i + the tail term at j = S i. *)
Lemma osq_row_succ : forall (N i : nat) (a : Q),QeqT (
  osq_row N (Datatypes.S i) a ) ( osq_row N i a +
    q_pow a (2 * N + 2 * Datatypes.S i + 2) / (q_fact (2 * N + 1) * q_fact (2 * Datatypes.S i + 1))).
Proof. intros. apply qeq_imp_qeqT. reflexivity. Qed.

(* One-step equation for the even row: esq_row N (S i) == esq_row N i + the tail term at j = S i, symmetric to [osq_row_succ]. *)
Lemma esq_row_succ : forall (N i : nat) (a : Q),QeqT (
  esq_row N (Datatypes.S i) a ) ( esq_row N i a +
    q_pow a (2 * N + 2 * Datatypes.S i) / (q_fact (2 * N) * q_fact (2 * Datatypes.S i))).
Proof. intros. apply qeq_imp_qeqT. reflexivity. Qed.

(* An odd partial sum times a single term equals an odd row sum:
   O_(S m)(a) * a^(2N+1)/(2N+1)! == osq_row N m a.
   (Since O_(S m) = the sum of a^(2k+1)/(2k+1)! for 0 <= k <= m, multiplying each term by
   a^(2N+1)/(2N+1)! gives a^(2k+1+2N+1)/((2k+1)!(2N+1)!) == a^(2N+2k+2)/((2N+1)!(2k+1)!),
   and the range k = 0..m reproduces osq_row N m; a numeric check at m = 0: O_1 = a and
   a * a^(2N+1)/(2N+1)! == a^(2N+2)/(2N+1)! == osq_row N 0.) *)
Lemma o_mul_term : forall (a : Q) (m N : nat),QeqT (
  o_sum (Datatypes.S m) a * (q_pow a (2 * N + 1) / q_fact (2 * N + 1)) ) ( osq_row N m a).
Proof.
  intros a m N.
  apply qeq_imp_qeqT.
  induction m as [| m'' IH].
  - (* Case m = 0: O_1 = a, so a * a^(2N+1)/(2N+1)! == osq_row N 0 = a^(2N+2)/((2N+1)! * 1!). *)
    simpl.
    setoid_replace (0 + a * 1 / (1 * 1)) with a.
    2: { unfold Qdiv. field. all: intro Hz0; destruct (q_neq_of_lt _ (q_fact_pos _) (qeq_imp_qeqT _ _ Hz0)). }
    setoid_replace (q_pow a (N + (N + 0) + 2)) with (a * q_pow a (N + (N + 0) + 1)).
    2: { change (q_pow a (N + (N + 0) + 2) == a * q_pow a (N + (N + 0) + 1)).
         assert (Hidx : (N + (N + 0) + 2 = Datatypes.S (N + (N + 0) + 1))%nat) by lia.
         rewrite Hidx. apply qeqT_imp_qeq. apply (q_pow_succ a (N + (N + 0) + 1)). }
    field.
    all: intro Hz0; destruct (q_neq_of_lt _ (q_fact_pos _) (qeq_imp_qeqT _ _ Hz0)).
  - setoid_rewrite (qeqT_imp_qeq _ _ (o_sum_succ a (Datatypes.S m''))).
    setoid_replace ((o_sum (Datatypes.S m'') a + q_pow a (Datatypes.S (2 * Datatypes.S m'')) / q_fact (Datatypes.S (2 * Datatypes.S m''))) *
        (q_pow a (2 * N + 1) / q_fact (2 * N + 1)))
      with (o_sum (Datatypes.S m'') a * (q_pow a (2 * N + 1) / q_fact (2 * N + 1)) +
            (q_pow a (Datatypes.S (2 * Datatypes.S m'')) / q_fact (Datatypes.S (2 * Datatypes.S m''))) *
            (q_pow a (2 * N + 1) / q_fact (2 * N + 1))) by ring.
    setoid_rewrite IH.
    assert (Hadd : q_pow a (Datatypes.S (2 * Datatypes.S m'')) * q_pow a (2 * N + 1) ==
                   q_pow a (2 * N + 1 + Datatypes.S (2 * Datatypes.S m''))).
    { apply Qeq_sym.
      assert (Hc : (Datatypes.S (2 * Datatypes.S m'') + (2 * N + 1) =
                    2 * N + 1 + Datatypes.S (2 * Datatypes.S m''))%nat) by lia.
      rewrite <- Hc. apply qeqT_imp_qeq. apply (q_pow_add a (Datatypes.S (2 * Datatypes.S m'')) (2 * N + 1)). }
    setoid_replace (q_pow a (Datatypes.S (2 * Datatypes.S m'')) / q_fact (Datatypes.S (2 * Datatypes.S m'')) *
        (q_pow a (2 * N + 1) / q_fact (2 * N + 1)))
      with (q_pow a (2 * N + 1 + Datatypes.S (2 * Datatypes.S m'')) /
            (q_fact (2 * N + 1) * q_fact (Datatypes.S (2 * Datatypes.S m'')))).
    2: { unfold Qdiv.
         transitivity ((q_pow a (Datatypes.S (2 * Datatypes.S m'')) * q_pow a (2 * N + 1)) *
                       (Qinv (q_fact (Datatypes.S (2 * Datatypes.S m''))) * Qinv (q_fact (2 * N + 1)))).
         - ring.
         - setoid_replace (q_pow a (Datatypes.S (2 * Datatypes.S m'')) * q_pow a (2 * N + 1))
             with (q_pow a (2 * N + 1 + Datatypes.S (2 * Datatypes.S m''))) by exact Hadd.
           setoid_rewrite (Qinv_mult_distr (q_fact (2 * N + 1)) (q_fact (Datatypes.S (2 * Datatypes.S m'')))).
           ring. }
    (* On the goal side, osq_row N (S m'') == osq_row N m'' + the tail term; the index shapes do not coincide after Fixpoint reduction, so they are realigned. *)
    assert (Hidx1 : (2 * N + 1 + Datatypes.S (2 * Datatypes.S m'') =
                     2 * N + 2 * Datatypes.S m'' + 2)%nat) by lia.
    assert (Hidx2 : (Datatypes.S (2 * Datatypes.S m'') =
                     2 * Datatypes.S m'' + 1)%nat) by lia.
    setoid_replace (q_pow a (2 * N + 1 + Datatypes.S (2 * Datatypes.S m'')))
      with (q_pow a (2 * N + 2 * Datatypes.S m'' + 2)).
    2: { change (q_pow a (2 * N + 1 + Datatypes.S (2 * Datatypes.S m'')) ==
                   q_pow a (2 * N + 2 * Datatypes.S m'' + 2)).
         exact (q_pow_comp_proper a a (Qeq_refl a)
                 (2 * N + 1 + Datatypes.S (2 * Datatypes.S m''))%nat
                 (2 * N + 2 * Datatypes.S m'' + 2)%nat Hidx1). }
    rewrite Hidx2.
    reflexivity.
Qed.

(* The square of the odd partial sum equals the odd double sum: O_m^2 == osq_sum m a. *)
Lemma o_sq_expand : forall (a : Q) (m : nat),QeqT (
  o_sum m a * o_sum m a ) ( osq_sum m a).
Proof.
  intros a m.
  apply qeq_imp_qeqT.
  induction m as [| m' IH].
  - simpl. ring.
  - setoid_rewrite (qeqT_imp_qeq _ _ (o_sum_succ a m')).
    setoid_replace ((o_sum m' a + q_pow a (Datatypes.S (2 * m')) / q_fact (Datatypes.S (2 * m'))) *
        (o_sum m' a + q_pow a (Datatypes.S (2 * m')) / q_fact (Datatypes.S (2 * m'))))
      with (o_sum m' a * o_sum m' a +
            2 * (o_sum m' a * (q_pow a (Datatypes.S (2 * m')) / q_fact (Datatypes.S (2 * m')))) +
            (q_pow a (Datatypes.S (2 * m')) / q_fact (Datatypes.S (2 * m'))) *
            (q_pow a (Datatypes.S (2 * m')) / q_fact (Datatypes.S (2 * m')))) by ring.
    setoid_rewrite IH.
    assert (Ht : q_pow a (Datatypes.S (2 * m')) / q_fact (Datatypes.S (2 * m')) ==
                 q_pow a (2 * m' + 1) / q_fact (2 * m' + 1)).
    { assert (Hidx : (Datatypes.S (2 * m') = 2 * m' + 1)%nat) by lia.
      setoid_replace (q_pow a (Datatypes.S (2 * m')))
        with (q_pow a (2 * m' + 1)).
      2: { exact (q_pow_comp_proper a a (Qeq_refl a)
                   (Datatypes.S (2 * m'))%nat (2 * m' + 1)%nat Hidx). }
      rewrite Hidx.
      reflexivity. }
    setoid_rewrite Ht.
    destruct m' as [| m''].
    + simpl.
      field.
      all: intro Hz0; destruct (q_neq_of_lt _ (q_fact_pos _) (qeq_imp_qeqT _ _ Hz0)).
    + setoid_replace (o_sum (Datatypes.S m'') a * (q_pow a (2 * Datatypes.S m'' + 1) / q_fact (2 * Datatypes.S m'' + 1)))
        with (osq_row (Datatypes.S m'') (Datatypes.S m'') a -
              q_pow a (2 * Datatypes.S m'' + 2 * Datatypes.S m'' + 2) /
              (q_fact (2 * Datatypes.S m'' + 1) * q_fact (2 * Datatypes.S m'' + 1))).
      2: { setoid_rewrite (qeqT_imp_qeq _ _ (o_mul_term a m'' (Datatypes.S m''))).
           apply Qeq_sym.
           setoid_rewrite (qeqT_imp_qeq _ _ (osq_row_succ (Datatypes.S m'') m'' a)).
           ring. }
      assert (Ht2 : (q_pow a (2 * Datatypes.S m'' + 1) / q_fact (2 * Datatypes.S m'' + 1)) *
                    (q_pow a (2 * Datatypes.S m'' + 1) / q_fact (2 * Datatypes.S m'' + 1)) ==
                    q_pow a (2 * Datatypes.S m'' + 2 * Datatypes.S m'' + 2) /
                    (q_fact (2 * Datatypes.S m'' + 1) * q_fact (2 * Datatypes.S m'' + 1))).
      { assert (Hadd : q_pow a (2 * Datatypes.S m'' + 1) * q_pow a (2 * Datatypes.S m'' + 1) ==
                       q_pow a ((2 * Datatypes.S m'' + 1) + (2 * Datatypes.S m'' + 1))).
        { apply Qeq_sym. apply qeqT_imp_qeq. apply (q_pow_add a (2 * Datatypes.S m'' + 1) (2 * Datatypes.S m'' + 1)). }
        assert (Hidx : (2 * Datatypes.S m'' + 1 + 2 * Datatypes.S m'' + 1 =
                        2 * Datatypes.S m'' + 2 * Datatypes.S m'' + 2)%nat) by lia.
        unfold Qdiv.
        transitivity ((q_pow a (2 * Datatypes.S m'' + 1) * q_pow a (2 * Datatypes.S m'' + 1)) *
                      (Qinv (q_fact (2 * Datatypes.S m'' + 1)) * Qinv (q_fact (2 * Datatypes.S m'' + 1)))).
        - ring.
        - setoid_replace (q_pow a (2 * Datatypes.S m'' + 1) * q_pow a (2 * Datatypes.S m'' + 1))
            with (q_pow a (2 * Datatypes.S m'' + 2 * Datatypes.S m'' + 2)).
          2: { assert (Hadd2 : q_pow a (2 * Datatypes.S m'' + 1) * q_pow a (2 * Datatypes.S m'' + 1) ==
                               q_pow a (2 * Datatypes.S m'' + 2 * Datatypes.S m'' + 2)).
               { apply Qeq_sym.
                 transitivity (q_pow a ((2 * Datatypes.S m'' + 1) + (2 * Datatypes.S m'' + 1))).
                 - assert (Hc : ((2 * Datatypes.S m'' + 1) + (2 * Datatypes.S m'' + 1) =
                                 2 * Datatypes.S m'' + 2 * Datatypes.S m'' + 2)%nat) by lia.
                   change (q_pow a (2 * Datatypes.S m'' + 2 * Datatypes.S m'' + 2) ==
                           q_pow a ((2 * Datatypes.S m'' + 1) + (2 * Datatypes.S m'' + 1))).
                   apply (q_pow_comp_proper a a (Qeq_refl a)
                           (2 * Datatypes.S m'' + 2 * Datatypes.S m'' + 2)%nat
                           ((2 * Datatypes.S m'' + 1) + (2 * Datatypes.S m'' + 1))%nat
                           (eq_sym Hc)).
                 - apply qeqT_imp_qeq. apply (q_pow_add a (2 * Datatypes.S m'' + 1) (2 * Datatypes.S m'' + 1)). }
               exact Hadd2. }
          setoid_rewrite (Qinv_mult_distr (q_fact (2 * Datatypes.S m'' + 1)) (q_fact (2 * Datatypes.S m'' + 1))).
          ring. }
      setoid_rewrite Ht2.
      set (D := q_pow a (2 * Datatypes.S m'' + 2 * Datatypes.S m'' + 2) *
                 Qinv (q_fact (2 * Datatypes.S m'' + 1) * q_fact (2 * Datatypes.S m'' + 1))).
      change (osq_sum (Datatypes.S m'') a +
              2 * (osq_row (Datatypes.S m'') (Datatypes.S m'') a - D) + D ==
              osq_sum (Datatypes.S m'') a +
              2 * osq_row (Datatypes.S m'') (Datatypes.S m'') a -
              q_pow a (2 * Datatypes.S m'' + 2 * Datatypes.S m'' + 2) *
              Qinv (q_fact (2 * Datatypes.S m'' + 1) * q_fact (2 * Datatypes.S m'' + 1))).
      subst D.
      ring.
Qed.

(* ============ Closed sums for [corr] (the [kloop_ksum] chain): the sigma form of corr ============ *)
(* The unfolding depth of kloop (S m) (2m+1) and kloop m (2m−1) depends on m, so [simpl]
   cannot reduce them layer by layer; the running sum [ksum] (the closed form of [kloop])
   makes the difference of [corr] computable. *)

(* The running-sum form of [kloop]: ksum m k a := the sum of inner2 (m+i) (2m−(m+i)) for 0 <= i <= k−1. *)
Fixpoint ksum (m k : nat) (a : Q) : Q :=
  match k with
  | 0%nat => 0
  | Datatypes.S k' => ksum m k' a + inner2 (m + k') (2 * m - (m + k')) a
  end.

(* One-step equation for [ksum] (forward direction). *)
Lemma ksum_succ : forall (m k : nat) (a : Q),QeqT (
  ksum m (Datatypes.S k) a ) ( ksum m k a + inner2 (m + k) (2 * m - (m + k)) a).
Proof. intros. apply qeq_imp_qeqT. reflexivity. Qed.

(* Helper: the tail of kloop m k vanishes for k < m — the converse condition to [kloop_succ]. *)
Lemma kloop_below : forall (m k : nat) (a : Q),
  (k < m)%nat ->QeqT ( kloop m k a ) ( 0).
Proof.
  intros m k a Hkm.
  apply qeq_imp_qeqT.
  destruct k as [| k']; [reflexivity |].
  (* For k = S k' < m, Nat.leb m (S k') = false, hence kloop = 0. *)
  simpl.
  assert (Hleb : Nat.leb m (Datatypes.S k') = false).
  { apply Nat.leb_gt. lia. }
  rewrite Hleb. reflexivity.
Qed.

(* kloop m (m+k') == ksum m (k'+1): accumulating [kloop] from m+k' down to m matches the running sum [ksum] growing upward. *)
Lemma kloop_ksum : forall (m k' : nat) (a : Q),QeqT (
  kloop m (m + k') a ) ( ksum m (k' + 1) a).
Proof.
  intros m k' a.
  apply qeq_imp_qeqT.
  induction k' as [| k' IH].
  - (* Case k' = 0: kloop m m == ksum m 1 == inner2 m (2m−m) == inner2 m m. *)
    simpl.
    destruct m as [| m'].
    + simpl. reflexivity.  (* for m = 0: kloop 0 0 = 0 and ksum 0 1 = inner2 0 0 = 0 *)
    + (* Case m = S m': kloop (S m') (S m') == inner2 (S m') (2(S m') - S m') + kloop (S m') m',
         where kloop (S m') m' == 0 (since m' < S m') and 2(S m') - S m' == S m'. *)
      assert (Hk : kloop (Datatypes.S m') (Datatypes.S m') a ==
                   inner2 (Datatypes.S m') (2 * Datatypes.S m' - Datatypes.S m') a +
                   kloop (Datatypes.S m') m' a).
      { apply qeqT_imp_qeq. apply kloop_succ. lia. }
      (* First reduce S m' + 0 == S m', then apply [Hk]. *)
      assert (Hadd0 : (Datatypes.S m' + 0 = Datatypes.S m')%nat) by lia.
      rewrite Hadd0.
      setoid_rewrite Hk.
      setoid_rewrite (qeqT_imp_qeq _ _ (kloop_below (Datatypes.S m') m' a ltac:(lia))).
      assert (Hidx : (2 * Datatypes.S m' - Datatypes.S m' = Datatypes.S m')%nat) by lia.
      rewrite Hidx.
      (* Goal: inner2 (S m') (S m') + 0 == 0 + inner2 (S m') (S m' + S m' − S m');
         after reducing S m' + S m' − S m' == S m', [ring] closes. *)
      assert (Hsub : (Datatypes.S m' + Datatypes.S m' - Datatypes.S m' = Datatypes.S m')%nat) by lia.
      rewrite Hsub.
      ring.
  - (* Case k' = S k': kloop m (m + S k') == kloop m (S (m+k')). *)
    assert (Hadd : (m + Datatypes.S k' = Datatypes.S (m + k'))%nat) by lia.
    rewrite Hadd.
    assert (Hk : kloop m (Datatypes.S (m + k')) a ==
                 inner2 (Datatypes.S (m + k')) (2 * m - Datatypes.S (m + k')) a +
                 kloop m (m + k') a).
    { apply qeqT_imp_qeq. apply kloop_succ. lia. }
    setoid_rewrite Hk.
    setoid_rewrite IH.
    (* ksum m (S k' + 1) == ksum m (k'+1) + inner2 (m + (k'+1)) (2m − (m+(k'+1))). *)
    assert (Hks : ksum m (Datatypes.S (k' + 1)) a ==
                  ksum m (k' + 1) a + inner2 (m + (k' + 1)) (2 * m - (m + (k' + 1))) a).
    { apply qeqT_imp_qeq. apply ksum_succ. }
    setoid_rewrite <- Hks.
    (* Index shapes of the tail term: S(m+k') == m + (k'+1) and 2m - S(m+k') == 2m - (m+(k'+1)). *)
    assert (Hidx1 : (Datatypes.S (m + k') = m + (k' + 1))%nat) by lia.
    assert (Hidx2 : (2 * m - Datatypes.S (m + k') = 2 * m - (m + (k' + 1)))%nat) by lia.
    setoid_replace (inner2 (Datatypes.S (m + k')) (2 * m - Datatypes.S (m + k')) a)
      with (inner2 (m + (k' + 1)) (2 * m - (m + (k' + 1))) a).
    2: { change (inner2 (Datatypes.S (m + k')) (2 * m - Datatypes.S (m + k')) a ==
                 inner2 (m + (k' + 1)) (2 * m - (m + (k' + 1))) a).
         rewrite Hidx1. reflexivity. }
    (* On the right, ksum (S(k'+1)) unfolds to ksum (k'+1) + inner2 ([Hks]); commutativity finishes. *)
    setoid_rewrite Hks.
    ring.
Qed.

(* corr m == ksum m m: for m >= 1, corr m = kloop m (2m−1) = kloop m (m + (m−1)) = ksum m m. *)
Lemma corr_ksum : forall (a : Q) (m : nat),
  (1 <= m)%nat ->QeqT ( corr m a ) ( ksum m m a).
Proof.
  intros a m Hm.
  apply qeq_imp_qeqT.
  unfold corr.
  (* For kloop m (2m−1): 2m−1 == m + (m−1). *)
  assert (Hidx : (2 * m - 1 = m + (m - 1))%nat) by lia.
  rewrite Hidx.
  assert (Hk : kloop m (m + (m - 1)) a == ksum m (m - 1 + 1) a).
  { apply qeqT_imp_qeq. apply kloop_ksum. }
  setoid_rewrite Hk.
  assert (Hsub : (m - 1 + 1 = m)%nat) by lia.
  rewrite Hsub.
  reflexivity.
Qed.

(* corr (S m) == ksum (S m) (S m): corr (S m) = kloop (S m) (2(S m)−1), and
   2(S m) − 1 == S m + (S m − 1) == S m + m, giving ksum (S m) (m+1). *)
Lemma corr_succ_ksum : forall (a : Q) (m : nat),QeqT (
  corr (Datatypes.S m) a ) ( ksum (Datatypes.S m) (Datatypes.S m) a).
Proof.
  intros a m.
  apply qeq_imp_qeqT.
  unfold corr.
  (* For kloop (S m) (2(S m) − 1): 2(S m)−1 == S m + S m − 1 == S m + m. *)
  assert (Hidx : (2 * Datatypes.S m - 1 = Datatypes.S m + m)%nat) by lia.
  rewrite Hidx.
  assert (Hk : kloop (Datatypes.S m) (Datatypes.S m + m) a == ksum (Datatypes.S m) (m + 1) a).
  { apply qeqT_imp_qeq. apply kloop_ksum. }
  setoid_rewrite Hk.
  assert (Hsub : (m + 1 = Datatypes.S m)%nat) by lia.
  rewrite Hsub.
  reflexivity.
Qed.

(* ============ The successor step: decomposing the difference of [corr] via [ksum_diff] ============ *)

(* Difference accumulation for [ksum]: ksum (S m) k == ksum m k + ksum_diff m k. *)
Fixpoint ksum_diff (m k : nat) (a : Q) : Q :=
  match k with
  | 0%nat => 0
  | Datatypes.S k' => ksum_diff m k' a +
      (inner2 (Datatypes.S m + k') (2 * Datatypes.S m - (Datatypes.S m + k')) a -
       inner2 (m + k') (2 * m - (m + k')) a)
  end.

Lemma ksum_diff_correct : forall (m k : nat) (a : Q),QeqT (
  ksum (Datatypes.S m) k a ) ( ksum m k a + ksum_diff m k a).
Proof.
  intros m k a.
  apply qeq_imp_qeqT.
  induction k as [| k' IH].
  - simpl. ring.
  - (* Unfold ksum_diff (S k'): definitionally it equals ksum_diff k' + (inner2 (S m + k') (2 * S m - (S m + k')) - inner2 (m + k') (2 * m - (m + k'))). *)
    change (ksum (Datatypes.S m) (Datatypes.S k') a ==
            ksum m (Datatypes.S k') a +
            (ksum_diff m k' a +
             (inner2 (Datatypes.S m + k') (2 * Datatypes.S m - (Datatypes.S m + k')) a -
              inner2 (m + k') (2 * m - (m + k')) a))).
    assert (H1 : ksum (Datatypes.S m) (Datatypes.S k') a ==
                 ksum (Datatypes.S m) k' a + inner2 (Datatypes.S m + k') (2 * Datatypes.S m - (Datatypes.S m + k')) a).
    { apply qeqT_imp_qeq. apply ksum_succ. }
    assert (H2 : ksum m (Datatypes.S k') a ==
                 ksum m k' a + inner2 (m + k') (2 * m - (m + k')) a).
    { apply qeqT_imp_qeq. apply ksum_succ. }
    setoid_rewrite H1. setoid_rewrite H2. setoid_rewrite IH.
    ring.
Qed.

(* For m >= 1: corr (S m) - corr m == ksum_diff m m + inner2 (2m+1) (2(S m)−(2m+1)). *)
Lemma corr_succ_decomp : forall (a : Q) (m : nat),
  (1 <= m)%nat ->QeqT (
  corr (Datatypes.S m) a - corr m a ) (
  ksum_diff m m a + inner2 (2 * m + 1) (2 * Datatypes.S m - (2 * m + 1)) a).
Proof.
  intros a m Hm.
  apply qeq_imp_qeqT.
  setoid_rewrite (qeqT_imp_qeq _ _ (corr_succ_ksum a m)).
  setoid_rewrite (qeqT_imp_qeq _ _ (corr_ksum a m Hm)).
  assert (H1 : ksum (Datatypes.S m) (Datatypes.S m) a ==
               ksum (Datatypes.S m) m a + inner2 (Datatypes.S m + m) (2 * Datatypes.S m - (Datatypes.S m + m)) a).
  { apply qeqT_imp_qeq. apply ksum_succ. }
  setoid_rewrite H1.
  assert (H2 : ksum (Datatypes.S m) m a == ksum m m a + ksum_diff m m a).
  { apply qeqT_imp_qeq. apply ksum_diff_correct. }
  setoid_rewrite H2.
  (* First reduce the inner2 indices (S m + m == 2m+1 and 2*S m - (2m+1) == 1), then close by [ring]. *)
  assert (Hidx : (Datatypes.S m + m = 2 * m + 1)%nat) by lia.
  assert (Hj : (2 * Datatypes.S m - (2 * m + 1) = 1)%nat) by lia.
  (* Realign the LHS inner2 indices: S m + m -> 2m+1 and 2*S m - (S m + m) -> 1. *)
  setoid_replace (inner2 (Datatypes.S m + m) (2 * Datatypes.S m - (Datatypes.S m + m)) a)
    with (inner2 (2 * m + 1) (2 * Datatypes.S m - (2 * m + 1)) a).
  2: { change (inner2 (Datatypes.S m + m) (2 * Datatypes.S m - (Datatypes.S m + m)) a ==
               inner2 (2 * m + 1) (2 * Datatypes.S m - (2 * m + 1)) a).
       rewrite Hidx. reflexivity. }
  ring.
Qed.

(* ============ Infrastructure for the [corr] argument: bounded sums and row matching ============ *)

(* The bounded sum: sum_upto n f = the sum of f i for 0 <= i <= n−1 (infrastructure for sums over skew diagonals). *)
Fixpoint sum_upto (n : nat) (f : nat -> Q) : Q :=
  match n with
  | 0%nat => 0
  | Datatypes.S n' => sum_upto n' f + f n'
  end.

(* Realigning the argument of [q_fact] (a [nat] identity transported to [Qeq]; the shapes 2*S N and 2N+2 are not definitionally equal). *)
Lemma q_fact_nat_eq : forall (n m : nat), n = m ->QeqT ( q_fact n ) ( q_fact m).
Proof. intros. subst. apply qeq_imp_qeqT. reflexivity. Qed.

(* inner2 k J == the sum of brk2 k j for 1 <= j <= J == sum_upto J (fun j => brk2 k (S j)), by induction on [J] with [k] fixed. *)
Lemma inner2_sum_upto : forall (k J : nat) (a : Q),QeqT (
  inner2 k J a ) ( sum_upto J (fun j : nat => brk2 k (Datatypes.S j) a)).
Proof.
  intros k J a.
  apply qeq_imp_qeqT.
  induction J as [| J' IH].
  - reflexivity.
  - change (inner2 k (Datatypes.S J') a ==
            sum_upto J' (fun j : nat => brk2 k (Datatypes.S j) a) + brk2 k (Datatypes.S J') a).
    setoid_rewrite <- IH.
    setoid_rewrite (qeqT_imp_qeq _ _ (inner2_succ k J' a)).
    ring.
Qed.

(* ksum_diff (S m) k == the sum over 0 <= k' <= k−1 of (inner2 (m+2+k') (m+2−k') - inner2 (m+1+k') (m+1−k')),
   by induction on [k] with [m] fixed: the closed-sum representation of the skew-diagonal accumulation. *)
Lemma ksum_diff_sum_upto : forall (m k : nat) (a : Q),QeqT (
  ksum_diff (Datatypes.S m) k a ) (
  sum_upto k (fun k' : nat =>
    inner2 (m + 2 + k') (m + 2 - k') a -
    inner2 (m + 1 + k') (m + 1 - k') a)).
Proof.
  intros m k a.
  apply qeq_imp_qeqT.
  induction k as [| k' IH].
  - reflexivity.
  - change (ksum_diff (Datatypes.S m) (Datatypes.S k') a ==
            sum_upto k' (fun k0 : nat =>
              inner2 (m + 2 + k0) (m + 2 - k0) a -
              inner2 (m + 1 + k0) (m + 1 - k0) a) +
            (inner2 (m + 2 + k') (m + 2 - k') a -
             inner2 (m + 1 + k') (m + 1 - k') a)).
    setoid_rewrite <- IH.
    change (ksum_diff (Datatypes.S m) (Datatypes.S k') a) with
      (ksum_diff (Datatypes.S m) k' a +
       (inner2 (Datatypes.S (Datatypes.S m) + k') (2 * Datatypes.S (Datatypes.S m) - (Datatypes.S (Datatypes.S m) + k')) a -
        inner2 (Datatypes.S m + k') (2 * Datatypes.S m - (Datatypes.S m + k')) a)).
    assert (H1 : (Datatypes.S (Datatypes.S m) + k' = m + 2 + k')%nat) by lia.
    assert (H2 : (2 * Datatypes.S (Datatypes.S m) - (Datatypes.S (Datatypes.S m) + k') = m + 2 - k')%nat) by lia.
    assert (H3 : (Datatypes.S m + k' = m + 1 + k')%nat) by lia.
    assert (H4 : (2 * Datatypes.S m - (Datatypes.S m + k') = m + 1 - k')%nat) by lia.
    setoid_replace (inner2 (Datatypes.S (Datatypes.S m) + k') (2 * Datatypes.S (Datatypes.S m) - (Datatypes.S (Datatypes.S m) + k')) a)
      with (inner2 (m + 2 + k') (m + 2 - k') a).
    2: { change (inner2 (Datatypes.S (Datatypes.S m) + k') (2 * Datatypes.S (Datatypes.S m) - (Datatypes.S (Datatypes.S m) + k')) a ==
                 inner2 (m + 2 + k') (m + 2 - k') a).
         rewrite H2. rewrite H1. reflexivity. }
    setoid_replace (inner2 (Datatypes.S m + k') (2 * Datatypes.S m - (Datatypes.S m + k')) a)
      with (inner2 (m + 1 + k') (m + 1 - k') a).
    2: { change (inner2 (Datatypes.S m + k') (2 * Datatypes.S m - (Datatypes.S m + k')) a ==
                 inner2 (m + 1 + k') (m + 1 - k') a).
         rewrite H4. rewrite H3. reflexivity. }
    ring.
Qed.

(* Row matching: -inner2 N i == 2 * esq_row (S N) i - 2 * osq_row N (i−1) - 2T,
   by induction on [i] with the row N fixed; this decomposes the first block of the induction
   step of [ksum_diff_row]. *)
Lemma rows_vs_inner_i : forall (a : Q) (N i : nat),
  (1 <= i)%nat ->QeqT (
  - inner2 N i a ) (
    2 * esq_row (Datatypes.S N) i a -
    2 * osq_row N (i - 1) a -
    2 * q_pow a (2 * N + 2 * i + 2) / (q_fact (2 * N + 2) * q_fact (2 * i))).
Proof.
  intros a N i Hi.
  apply qeq_imp_qeqT.
  destruct i as [| i'].
  - lia.
  - induction i' as [| i'' IH2].
    + setoid_rewrite (qeqT_imp_qeq _ _ (inner2_succ N 0 a)).
      setoid_rewrite (qeqT_imp_qeq _ _ (esq_row_succ (Datatypes.S N) 0 a)).
      change (inner2 N 0 a) with 0.
      change (esq_row (Datatypes.S N) 0 a) with
        (q_pow a (2 * Datatypes.S N) / (q_fact (2 * Datatypes.S N) * q_fact 0)).
      change (brk2 N 1 a) with
        (2 * q_pow a (2 * N + 2 * 1) / (q_fact (2 * N + 1) * q_fact (2 * 1 - 1)) -
         2 * q_pow a (2 * N + 2 * 1) / (q_fact (2 * N + 2) * q_fact (2 * 1 - 2))).
      change (osq_row N (1 - 1) a) with
        (q_pow a (2 * N + 2) / (q_fact (2 * N + 1) * q_fact 1)).
      assert (H2 : (2 * Datatypes.S N = 2 * N + 2)%nat) by lia.
      assert (H4 : (2 * Datatypes.S N + 2 = 2 * N + 4)%nat) by lia.
      assert (Hb : (2 * N + 2 * 1 = 2 * N + 2)%nat) by lia.
      assert (Ht : (2 * N + 2 * 1 + 2 = 2 * N + 4)%nat) by lia.
      setoid_replace (q_pow a (2 * Datatypes.S N)) with (q_pow a (2 * N + 2)).
      2: { apply (q_pow_comp_proper a a (Qeq_refl a)
                   (2 * Datatypes.S N)%nat (2 * N + 2)%nat H2). }
      setoid_replace (q_pow a (2 * Datatypes.S N + 2)) with (q_pow a (2 * N + 4)).
      2: { apply (q_pow_comp_proper a a (Qeq_refl a)
                   (2 * Datatypes.S N + 2)%nat (2 * N + 4)%nat H4). }
      setoid_replace (q_pow a (2 * N + 2 * 1)) with (q_pow a (2 * N + 2)).
      2: { apply (q_pow_comp_proper a a (Qeq_refl a)
                   (2 * N + 2 * 1)%nat (2 * N + 2)%nat Hb). }
      setoid_replace (q_pow a (2 * N + 2 * 1 + 2)) with (q_pow a (2 * N + 4)).
      2: { apply (q_pow_comp_proper a a (Qeq_refl a)
                   (2 * N + 2 * 1 + 2)%nat (2 * N + 4)%nat Ht). }
      setoid_replace (q_fact (2 * Datatypes.S N)) with (q_fact (2 * N + 2)).
      2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. lia. }
      setoid_replace (q_fact (2 * 1 - 1)) with (q_fact 1).
      2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. lia. }
      setoid_replace (q_fact (2 * 1 - 2)) with (q_fact 0).
      2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. lia. }
      setoid_replace (q_fact (2 * 1)) with (q_fact 2).
      2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. lia. }
      change (q_fact 0) with 1.
      change (q_fact 1) with 1.
      change (q_fact 2) with 2.
      unfold Qdiv.
      ring.
    + assert (Hi' : (1 <= Datatypes.S i'')%nat) by lia.
      setoid_rewrite (qeqT_imp_qeq _ _ (inner2_succ N (Datatypes.S i'') a)).
      setoid_replace (- (inner2 N (Datatypes.S i'') a + brk2 N (Datatypes.S (Datatypes.S i'')) a))
        with (- inner2 N (Datatypes.S i'') a - brk2 N (Datatypes.S (Datatypes.S i'')) a) by ring.
      unfold brk2.
      setoid_rewrite (qeqT_imp_qeq _ _ (esq_row_succ (Datatypes.S N) (Datatypes.S i'') a)).
      setoid_rewrite (qeqT_imp_qeq _ _ (osq_row_succ N i'' a)).
      setoid_rewrite (IH2 Hi').
      assert (H6 : (2 * Datatypes.S N + 2 * Datatypes.S (Datatypes.S i'') =
                    2 * N + 2 * i'' + 6)%nat) by lia.
      assert (H6b : (2 * N + 2 * Datatypes.S (Datatypes.S i'') + 2 =
                     2 * N + 2 * i'' + 6)%nat) by lia.
      assert (H4 : (2 * N + 2 * Datatypes.S (Datatypes.S i'') =
                    2 * N + 2 * i'' + 4)%nat) by lia.
      assert (H4b : (2 * N + 2 * Datatypes.S i'' + 2 =
                     2 * N + 2 * i'' + 4)%nat) by lia.
      setoid_replace (q_pow a (2 * Datatypes.S N + 2 * Datatypes.S (Datatypes.S i'')))
        with (q_pow a (2 * N + 2 * i'' + 6)).
      2: { apply (q_pow_comp_proper a a (Qeq_refl a)
                   (2 * Datatypes.S N + 2 * Datatypes.S (Datatypes.S i''))%nat
                   (2 * N + 2 * i'' + 6)%nat H6). }
      setoid_replace (q_pow a (2 * N + 2 * Datatypes.S (Datatypes.S i'')))
        with (q_pow a (2 * N + 2 * i'' + 4)).
      2: { apply (q_pow_comp_proper a a (Qeq_refl a)
                   (2 * N + 2 * Datatypes.S (Datatypes.S i''))%nat
                   (2 * N + 2 * i'' + 4)%nat H4). }
      setoid_replace (q_pow a (2 * N + 2 * Datatypes.S i'' + 2))
        with (q_pow a (2 * N + 2 * i'' + 4)).
      2: { apply (q_pow_comp_proper a a (Qeq_refl a)
                   (2 * N + 2 * Datatypes.S i'' + 2)%nat
                   (2 * N + 2 * i'' + 4)%nat H4b). }
      setoid_replace (q_pow a (2 * N + 2 * Datatypes.S (Datatypes.S i'') + 2))
        with (q_pow a (2 * N + 2 * i'' + 6)).
      2: { apply (q_pow_comp_proper a a (Qeq_refl a)
                   (2 * N + 2 * Datatypes.S (Datatypes.S i'') + 2)%nat
                   (2 * N + 2 * i'' + 6)%nat H6b). }
      setoid_replace (q_fact (2 * Datatypes.S N)) with (q_fact (2 * N + 2)).
      2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. lia. }
      setoid_replace (q_fact (2 * Datatypes.S (Datatypes.S i'') - 1))
        with (q_fact (2 * Datatypes.S i'' + 1)).
      2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. lia. }
      setoid_replace (q_fact (2 * Datatypes.S (Datatypes.S i'') - 2))
        with (q_fact (2 * Datatypes.S i'')).
      2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. lia. }
      assert (Hsub : (Datatypes.S i'' - 1 = i'')%nat) by lia.
      setoid_replace (osq_row N (Datatypes.S i'' - 1) a) with (osq_row N i'' a).
      2: { change (osq_row N (Datatypes.S i'' - 1) a == osq_row N i'' a).
           rewrite Hsub. reflexivity. }
      unfold Qdiv.
      ring.
Qed.

(* ============ Change-of-variables family for bounded sums ============ *)

(* Linearity: the sum of (f+g) equals the sum of f plus the sum of g, by induction on [n]. *)
Lemma sum_upto_plus : forall (n : nat) (f g : nat -> Q),QeqT (
  sum_upto n (fun i => f i + g i) ) ( sum_upto n f + sum_upto n g).
Proof.
  intros n f g.
  apply qeq_imp_qeqT.
  induction n as [| n' IH].
  - reflexivity.
  - change (sum_upto n' (fun i => f i + g i) + (f n' + g n') ==
            sum_upto n' f + f n' + (sum_upto n' g + g n')).
    setoid_rewrite IH.
    ring.
Qed.

Lemma sum_upto_zero : forall (n : nat),QeqT ( sum_upto n (fun _ => 0) ) ( 0).
Proof.
  intros n.
  apply qeq_imp_qeqT.
  induction n as [| n' IH].
  - reflexivity.
  - simpl. rewrite IH. ring.
Qed.

(* Extensionality: pointwise equality of summands gives equality of sums. *)
Lemma sum_upto_ext : forall (n : nat) (f g : nat -> Q),
  (forall i,QeqT ( f i ) ( g i)) ->QeqT ( sum_upto n f ) ( sum_upto n g).
Proof.
  intros n f g H.
  apply qeq_imp_qeqT.
  induction n as [| n' IH].
  - reflexivity.
  - simpl. setoid_rewrite IH. setoid_rewrite (qeqT_imp_qeq _ _ (H n')). reflexivity.
Qed.

(* Peeling off the first term: the sum of h i over 0 <= i <= n equals h 0 plus the sum of h (i+1) over 0 <= i <= n−1, by induction on [n] (the basis for index shifts). *)
Lemma sum_upto_rot : forall (n : nat) (h : nat -> Q),QeqT (
  sum_upto (Datatypes.S n) h ) ( h 0%nat + sum_upto n (fun i => h (Datatypes.S i))).
Proof.
  intros n h.
  apply qeq_imp_qeqT.
  induction n as [| n' IH].
  - simpl. ring.
  - change (sum_upto (Datatypes.S n') h + h (Datatypes.S n') ==
            h 0%nat + sum_upto (Datatypes.S n') (fun i => h (Datatypes.S i))).
    setoid_rewrite IH.
    change (sum_upto (Datatypes.S n') (fun i => h (Datatypes.S i))) with
      (sum_upto n' (fun i => h (Datatypes.S i)) + h (Datatypes.S n')).
    ring.
Qed.

(* Reversed shift: the sum of h (n−i) equals the sum of h (i+1), with [sum_upto_rot] in the induction step. *)
Lemma sum_upto_shift_rev : forall (n : nat) (h : nat -> Q),QeqT (
  sum_upto n (fun i => h (n - i)%nat) ) ( sum_upto n (fun i => h (Datatypes.S i))).
Proof.
  intros n h.
  apply qeq_imp_qeqT.
  induction n as [| n' IH].
  - reflexivity.
  - rewrite (qeqT_imp_qeq _ _ (sum_upto_rot n' (fun i => h (Datatypes.S n' - i)%nat))).
    rewrite (fun Hprm => qeqT_imp_qeq _ _ (sum_upto_ext n' (fun i => h (Datatypes.S n' - Datatypes.S i)%nat) (fun i => h (n' - i)%nat) Hprm)).
    2: { intro i. apply qeq_imp_qeqT. assert (Hnat : (Datatypes.S n' - Datatypes.S i = n' - i)%nat) by lia.
         rewrite Hnat. reflexivity. }
    setoid_rewrite IH.
    change (h (Datatypes.S n' - 0)%nat) with (h (Datatypes.S n')).
    change (sum_upto (Datatypes.S n') (fun i => h (Datatypes.S i))) with
      (sum_upto n' (fun i => h (Datatypes.S i)) + h (Datatypes.S n')).
    ring.
Qed.

(* Reversed sum: the sum of h (n−1−i) equals the sum of h i. *)
Lemma sum_upto_rev : forall (n : nat) (h : nat -> Q),QeqT (
  sum_upto n (fun i => h (n - 1 - i)%nat) ) ( sum_upto n h).
Proof.
  intros n h.
  apply qeq_imp_qeqT.
  induction n as [| n' IH].
  - reflexivity.
  - rewrite (qeqT_imp_qeq _ _ (sum_upto_rot n' (fun i => h (Datatypes.S n' - 1 - i)%nat))).
    rewrite (fun Hprm => qeqT_imp_qeq _ _ (sum_upto_ext n' (fun i => h (Datatypes.S n' - 1 - Datatypes.S i)%nat) (fun i => h (n' - 1 - i)%nat) Hprm)).
    2: { intro i. apply qeq_imp_qeqT. assert (Hnat : (Datatypes.S n' - 1 - Datatypes.S i = n' - 1 - i)%nat) by lia.
         rewrite Hnat. reflexivity. }
    assert (Hn : (Datatypes.S n' - 1 = n')%nat) by lia.
    rewrite Hn.
    setoid_rewrite IH.
    assert (Hz : (n' - 0 = n')%nat) by lia.
    rewrite Hz.
    change (sum_upto (Datatypes.S n') h) with (sum_upto n' h + h n').
    ring.
Qed.

(* Swapping rectangular sums: the double sum over i and j of f i j is symmetric, by induction on [m] with [n] fixed. *)
Lemma sum_upto_rect_swap : forall (m n : nat) (f : nat -> nat -> Q),QeqT (
  sum_upto m (fun i => sum_upto n (fun j => f i j)) ) (
  sum_upto n (fun j => sum_upto m (fun i => f i j))).
Proof.
  intros m n f.
  apply qeq_imp_qeqT.
  induction m as [| m' IH].
  - simpl. apply Qeq_sym. apply qeqT_imp_qeq. apply sum_upto_zero.
  - change (sum_upto m' (fun i => sum_upto n (fun j => f i j)) + sum_upto n (fun j => f m' j) ==
            sum_upto n (fun j => sum_upto (Datatypes.S m') (fun i => f i j))).
    setoid_rewrite IH.
    rewrite (fun Hprm => qeqT_imp_qeq _ _ (sum_upto_ext n (fun j => sum_upto (Datatypes.S m') (fun i => f i j)) (fun j => sum_upto m' (fun i => f i j) + f m' j) Hprm)).
    2: { intro j. apply qeq_imp_qeqT. reflexivity. }
    rewrite (qeqT_imp_qeq _ _ (sum_upto_plus n (fun j => sum_upto m' (fun i => f i j)) (fun j => f m' j))).
    ring.
Qed.

(* ============ Swapping family for double sums ============ *)

(* Extensionality over the index range: pointwise equality is only needed for i < n (identities such as S m'−i == S(m'−i) hold only for i <= m'). *)
Lemma sum_upto_ext_below : forall (n : nat) (f g : nat -> Q),
  (forall i : nat, NatLe (Datatypes.S i) n ->QeqT ( f i ) ( g i)) ->QeqT ( sum_upto n f ) ( sum_upto n g).
Proof.
  intros n f g H.
  apply qeq_imp_qeqT.
  induction n as [| n' IH].
  - reflexivity.
  - simpl.
    setoid_rewrite (IH (fun i : nat => fun Hi =>
                        H i (NatLe_lift _ _ (Nat.le_le_succ_r (Datatypes.S i) n' (NatLe_drop (Datatypes.S i) n' Hi))))).
    setoid_rewrite (qeqT_imp_qeq _ _ (H n' (NatLe_lift _ _ (Nat.lt_succ_diag_r n')))).
    reflexivity.
Qed.

(* ============ The [ksum_diff_row] argument: the difference of [corr] equals the row difference ============ *)

(* ===== Direct proof of [ksum_diff_row] (without induction): the difference of [corr] equals the row difference =====
   First step: apply [corr_succ_decomp] in reverse, then chain [ksum_succ]/[ksum_diff_correct]
   to expose the goal shape. *)
Lemma ksum_diff_row_step1 : forall (a : Q) (m : nat),
  (1 <= m)%nat ->QeqT (
  ksum_diff m m a + inner2 (2 * m + 1) (2 * Datatypes.S m - (2 * m + 1)) a ) (
  corr (Datatypes.S m) a - corr m a).
Proof.
  intros a m Hm. exact (qeq_imp_qeqT _ _ (Qeq_sym _ _ (qeqT_imp_qeq _ _ (corr_succ_decomp a m Hm)))).
Qed.

(* Second step: the left side equals the difference of [corr], which equals ksum (S m) (S m) - ksum m m,
   via [corr_succ_ksum]/[corr_ksum] chained with [ksum_succ] and [ksum_diff_correct]. *)
Lemma ksum_diff_row_step2 : forall (a : Q) (m : nat),
  (1 <= m)%nat ->QeqT (
  ksum_diff m m a + inner2 (2 * m + 1) (2 * Datatypes.S m - (2 * m + 1)) a ) (
  ksum (Datatypes.S m) (Datatypes.S m) a - ksum m m a).
Proof.
  intros a m Hm.
  apply qeq_imp_qeqT.
  (* [corr_succ_decomp]: LHS == corr (S m) - corr m. *)
  setoid_rewrite <- (qeqT_imp_qeq _ _ (corr_succ_decomp a m Hm)).
  (* corr (S m) == ksum (S m) (S m)、corr m == ksum m m *)
  setoid_rewrite (qeqT_imp_qeq _ _ (corr_succ_ksum a m)).
  setoid_rewrite (qeqT_imp_qeq _ _ (corr_ksum a m Hm)).
  reflexivity.
Qed.

(* Third step: ksum (S m) (S m) unfolds to ksum (S m) m + inner2 (2m+1) 1 ([ksum_succ] plus index reduction),
   reducing the goal to ksum_diff m m + inner2 (2m+1) 1 == ksum (S m) m + inner2 (2m+1) 1 - ksum m m. *)
Lemma ksum_diff_row_step3 : forall (a : Q) (m : nat),
  (1 <= m)%nat ->QeqT (
  ksum_diff m m a + inner2 (2 * m + 1) 1 a ) (
  ksum (Datatypes.S m) (Datatypes.S m) a - ksum m m a).
Proof.
  intros a m Hm.
  apply qeq_imp_qeqT.
  (* ksum (S m) (S m) == ksum (S m) m + inner2 (S m + m) (2*S m − (S m + m)). *)
  assert (Hk : ksum (Datatypes.S m) (Datatypes.S m) a ==
               ksum (Datatypes.S m) m a + inner2 (Datatypes.S m + m) (2 * Datatypes.S m - (Datatypes.S m + m)) a).
  { apply qeqT_imp_qeq. apply ksum_succ. }
  setoid_rewrite Hk.
  (* Reduce the inner2 indices: S m + m == 2m+1 and 2*S m − (S m + m) == 1; apply [Hj] before [Hidx], since a global rewrite by [Hidx] would also hit the subterm inside [Hj]. *)
  assert (Hidx : (Datatypes.S m + m = 2 * m + 1)%nat) by lia.
  assert (Hj : (2 * Datatypes.S m - (Datatypes.S m + m) = 1)%nat) by lia.
  setoid_replace (inner2 (Datatypes.S m + m) (2 * Datatypes.S m - (Datatypes.S m + m)) a)
    with (inner2 (2 * m + 1) 1 a).
  2: { change (inner2 (Datatypes.S m + m) (2 * Datatypes.S m - (Datatypes.S m + m)) a ==
               inner2 (2 * m + 1) 1 a).
       rewrite Hj. rewrite Hidx. reflexivity. }
  (* ksum (S m) m == ksum m m + ksum_diff m m, by [ksum_diff_correct]. *)
  assert (Hd : ksum (Datatypes.S m) m a == ksum m m a + ksum_diff m m a).
  { apply qeqT_imp_qeq. apply ksum_diff_correct. }
  setoid_rewrite Hd.
  ring.
Qed.

(* Leibniz transport in the first argument of [ksum_diff] (only [k] recurs; when m1 == m2 the substitution is definitional). *)
Lemma ksum_diff_nat_eq : forall (m1 m2 k : nat) (a : Q),
  m1 = m2 ->QeqT ( ksum_diff m1 k a ) ( ksum_diff m2 k a).
Proof. intros. subst. apply qeq_imp_qeqT. reflexivity. Qed.

(* Step 4: the left side of [ksum_diff_row] unfolds via [ksum_diff_sum_upto] (with m−1),
   giving ksum_diff m m == sum_upto m (inner2 (m+1+k') (m+1−k') - inner2 (m+k') (m−k')). *)
Lemma ksum_diff_row_step4 : forall (a : Q) (m : nat),
  (1 <= m)%nat ->QeqT (
  ksum_diff m m a ) (
  sum_upto m (fun k' => inner2 (m + 1 + k') (m + 1 - k') a - inner2 (m + k') (m - k') a)).
Proof.
  intros a m Hm.
  apply qeq_imp_qeqT.
  (* Replace the first argument of [ksum_diff]: m == S(m−1), via [ksum_diff_nat_eq] (the second argument stays [m]). *)
  assert (Hsm : (m = Datatypes.S (m - 1))%nat) by lia.
  assert (Hbr : ksum_diff m m a == ksum_diff (Datatypes.S (m - 1)) m a).
  { apply qeqT_imp_qeq. apply (ksum_diff_nat_eq m (Datatypes.S (m - 1)) m a Hsm). }
  setoid_rewrite Hbr.
  (* [ksum_diff_sum_upto] at N=m−1 and k=m: ksum_diff (S(m−1)) m ==
     sum_upto m (inner2 (m+1+k') (m+1−k') - inner2 (m+k') (m−k')). *)
  rewrite (qeqT_imp_qeq _ _ (ksum_diff_sum_upto (m - 1) m a)).
  (* [sum_upto_ext_below] realigns the summand arguments (m−1+2+k' == m+1+k' and so on). *)
  rewrite (fun Hprm => qeqT_imp_qeq _ _ (sum_upto_ext_below m (fun k' => inner2 (m - 1 + 2 + k') (m - 1 + 2 - k') a - inner2 (m - 1 + 1 + k') (m - 1 + 1 - k') a) (fun k' => inner2 (m + 1 + k') (m + 1 - k') a - inner2 (m + k') (m - k') a) Hprm)).
  2: { intros k' Hk'. apply NatLe_drop in Hk'. apply qeq_imp_qeqT.
       assert (H1 : (m - 1 + 2 + k' = m + 1 + k')%nat) by lia.
       assert (H2 : (m - 1 + 2 - k' = m + 1 - k')%nat) by lia.
       assert (H3 : (m - 1 + 1 + k' = m + k')%nat) by lia.
       assert (H4 : (m - 1 + 1 - k' = m - k')%nat) by lia.
       setoid_rewrite H1. setoid_rewrite H2. setoid_rewrite H3. setoid_rewrite H4.
       reflexivity. }
  reflexivity.
Qed.

(* Leibniz transport in the second argument of [osq_row] (bridging S(m−1) == m). *)
Lemma osq_row_nat_eq2 : forall (N i1 i2 : nat) (a : Q),
  i1 = i2 ->QeqT ( osq_row N i1 a ) ( osq_row N i2 a).
Proof. intros. subst. apply qeq_imp_qeqT. reflexivity. Qed.

(* Closing the right side: the row difference == [esq_sum (S m) - esq_sum m] - [osq_sum (S m) - osq_sum m],
   that is 2*esq_row (S m) m + Te^2 - 2*osq_row m (m−1) - To^2, with Te^2 = a^(4m+4)/((2m+2)!)^2 and
   To^2 = a^(4m+2)/((2m+1)!)^2;
   the one-step equations for [esq_sum]/[osq_sum] are definitional, and [osq_row_succ] gives
   osq_row m m == osq_row m (m−1) + To^2. *)
Lemma row_diff_closed : forall (a : Q) (m : nat), (1 <= m)%nat ->QeqT (
  2 * esq_row (Datatypes.S m) m a +
  (q_pow a (4 * m + 4) / (q_fact (2 * m + 2) * q_fact (2 * m + 2))) -
  2 * osq_row m (m - 1) a -
  (q_pow a (4 * m + 2) / (q_fact (2 * m + 1) * q_fact (2 * m + 1))) ) (
  (esq_sum (Datatypes.S m) a - esq_sum m a) -
  (osq_sum (Datatypes.S m) a - osq_sum m a)).
Proof.
  intros a m Hm.
  apply qeq_imp_qeqT.
  (* esq_sum (S m) == esq_sum m + 2*esq_row (S m) m + q_pow a (2*S m+2*S m)/((2*S m)!(2*S m)!), the definitional one-step equation. *)
  change (esq_sum (Datatypes.S m) a) with
    (esq_sum m a + 2 * esq_row (Datatypes.S m) m a +
     q_pow a (2 * Datatypes.S m + 2 * Datatypes.S m) /
       (q_fact (2 * Datatypes.S m) * q_fact (2 * Datatypes.S m))).
  (* osq_sum (S m) == osq_sum m + 2*osq_row m m - q_pow a (2m+2m+2)/((2m+1)!(2m+1)!), the definitional one-step equation. *)
  change (osq_sum (Datatypes.S m) a) with
    (osq_sum m a + 2 * osq_row m m a -
     q_pow a (2 * m + 2 * m + 2) / (q_fact (2 * m + 1) * q_fact (2 * m + 1))).
  (* osq_row m m == osq_row m (S(m−1)) by a [nat] identity in the second argument, then unfold with [osq_row_succ]. *)
  assert (Hsm : (m = Datatypes.S (m - 1))%nat) by lia.
  setoid_replace (osq_row m m a) with (osq_row m (Datatypes.S (m - 1)) a).
  2: { apply qeqT_imp_qeq. apply (osq_row_nat_eq2 m m (Datatypes.S (m - 1)) a Hsm). }
  setoid_rewrite (qeqT_imp_qeq _ _ (osq_row_succ m (m - 1) a)).
  (* Reduce the tail term of [osq_row_succ]: 2m+2*S(m−1)+2 == 4m+2 and 2*S(m−1)+1 == 2m+1. *)
  assert (Hp3 : (2 * m + 2 * Datatypes.S (m - 1) + 2 = 4 * m + 2)%nat) by lia.
  assert (Hf3 : (2 * Datatypes.S (m - 1) + 1 = 2 * m + 1)%nat) by lia.
  setoid_replace (q_pow a (2 * m + 2 * Datatypes.S (m - 1) + 2))
    with (q_pow a (4 * m + 2)).
  2: { apply (q_pow_comp_proper a a (Qeq_refl a)
               (2 * m + 2 * Datatypes.S (m - 1) + 2)%nat (4 * m + 2)%nat Hp3). }
  setoid_replace (q_fact (2 * Datatypes.S (m - 1) + 1)) with (q_fact (2 * m + 1)).
  2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. lia. }
  (* Reduce the tail term of [esq_sum]: 2*S m+2*S m == 4m+4 and 2*S m == 2m+2. *)
  assert (Hp1 : (2 * Datatypes.S m + 2 * Datatypes.S m = 4 * m + 4)%nat) by lia.
  assert (Hf1 : (2 * Datatypes.S m = 2 * m + 2)%nat) by lia.
  setoid_replace (q_pow a (2 * Datatypes.S m + 2 * Datatypes.S m))
    with (q_pow a (4 * m + 4)).
  2: { apply (q_pow_comp_proper a a (Qeq_refl a)
               (2 * Datatypes.S m + 2 * Datatypes.S m)%nat (4 * m + 4)%nat Hp1). }
  setoid_replace (q_fact (2 * Datatypes.S m)) with (q_fact (2 * m + 2)).
  2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. lia. }
  (* Reduce the tail term of [osq_sum]: 2m+2m+2 == 4m+2. *)
  assert (Hp2 : (2 * m + 2 * m + 2 = 4 * m + 2)%nat) by lia.
  setoid_replace (q_pow a (2 * m + 2 * m + 2))
    with (q_pow a (4 * m + 2)).
  2: { apply (q_pow_comp_proper a a (Qeq_refl a)
               (2 * m + 2 * m + 2)%nat (4 * m + 2)%nat Hp2). }
  ring.
Qed.

(* Main frame of [ksum_diff_row]: the difference of [corr] equals the row difference, mediated by [esq_sum]/[osq_sum].
   LHS = corr (S m) − corr m (by [corr_succ_decomp] in reverse)
       = ksum (S m) (S m) − ksum m m (by [corr_succ_ksum]/[corr_ksum]).
   RHS = the row difference ([row_diff_closed])
        == [esq_sum(S m)−esq_sum m] − [osq_sum(S m)−osq_sum m]
        == (E_(S m)^2−O_(S m)^2) − (E_m^2−O_m^2) (by [e_sq_expand]/[o_sq_expand]).
   The remaining bridge (the difference of [corr] equals this difference of squares) is supplied by the
   pairing argument; this lemma closes the right side first. *)
Lemma ksum_diff_row_rhs : forall (a : Q) (m : nat), (1 <= m)%nat ->QeqT (
  2 * esq_row (Datatypes.S m) m a +
  (q_pow a (4 * m + 4) / (q_fact (2 * m + 2) * q_fact (2 * m + 2))) -
  2 * osq_row m (m - 1) a -
  (q_pow a (4 * m + 2) / (q_fact (2 * m + 1) * q_fact (2 * m + 1))) ) (
  (e_sum (Datatypes.S m) a * e_sum (Datatypes.S m) a -
   o_sum (Datatypes.S m) a * o_sum (Datatypes.S m) a) -
  (e_sum m a * e_sum m a - o_sum m a * o_sum m a)).
Proof.
  intros a m Hm.
  apply qeq_imp_qeqT.
  (* By [e_sq_expand]/[o_sq_expand]: the goal contains e_sum^2 - o_sum^2 terms, so rewrite esq_sum/osq_sum in the forward (LHS==RHS) direction. *)
  setoid_rewrite (qeqT_imp_qeq _ _ (e_sq_expand a m)).
  setoid_rewrite (qeqT_imp_qeq _ _ (o_sq_expand a m)).
  setoid_rewrite (qeqT_imp_qeq _ _ (e_sq_expand a (Datatypes.S m))).
  setoid_rewrite (qeqT_imp_qeq _ _ (o_sq_expand a (Datatypes.S m))).
  (* Regroup the goal: esq_sum(S m) - osq_sum(S m) - (esq_sum m - osq_sum m)
     == (esq_sum(S m)−esq_sum m) - (osq_sum(S m)−osq_sum m), by [setoid_replace] plus [ring] (purely atomic). *)
  setoid_replace (esq_sum (Datatypes.S m) a - osq_sum (Datatypes.S m) a -
                  (esq_sum m a - osq_sum m a))
    with ((esq_sum (Datatypes.S m) a - esq_sum m a) -
          (osq_sum (Datatypes.S m) a - osq_sum m a)) by ring.
  (* Goal: the row difference == [esq_sum(S m)−esq_sum m] − [osq_sum(S m)−osq_sum m], by [row_diff_closed] in reverse. *)
  setoid_rewrite <- (qeqT_imp_qeq _ _ (row_diff_closed a m Hm)).
  reflexivity.
Qed.

(* Shift plus boundary correction (in two dimensions): the sum of g (S i) (n−i) equals
   the sum of g i (n+1−i) + g n 1 - g 0 (n+1),
   by induction on [n] (the IH is stated for all g, and the step applies it
   to g' = g∘S to absorb the double-successor misalignment). *)
Lemma sum_upto_shift_boundary : forall (n : nat) (g : nat -> nat -> Q),QeqT (
  sum_upto n (fun i => g (Datatypes.S i) (n - i)%nat) ) (
  sum_upto n (fun i => g i (n + 1 - i)%nat) + g n 1%nat - g 0%nat (n + 1)%nat).
Proof.
  intros n.
  induction n as [| n' IH].
  - intros g. apply qeq_imp_qeqT. simpl. ring.
  - intros g. apply qeq_imp_qeqT.
    rewrite (qeqT_imp_qeq _ _ (sum_upto_rot n' (fun i => g (Datatypes.S i) (Datatypes.S n' - i)%nat))).
    rewrite (fun Hprm => qeqT_imp_qeq _ _ (sum_upto_ext n' (fun i => g (Datatypes.S (Datatypes.S i)) (Datatypes.S n' - Datatypes.S i)%nat) (fun i => g (Datatypes.S (Datatypes.S i)) (n' - i)%nat) Hprm)).
    2: { intro i. apply qeq_imp_qeqT. assert (Hnat : (Datatypes.S n' - Datatypes.S i = n' - i)%nat) by lia.
         rewrite Hnat. reflexivity. }
    rewrite (qeqT_imp_qeq _ _ (sum_upto_rot n' (fun i => g i (Datatypes.S n' + 1 - i)%nat))).
    rewrite (fun Hprm => qeqT_imp_qeq _ _ (sum_upto_ext n' (fun i => g (Datatypes.S i) (Datatypes.S n' + 1 - Datatypes.S i)%nat) (fun i => g (Datatypes.S i) (n' + 1 - i)%nat) Hprm)).
    2: { intro i. apply qeq_imp_qeqT. assert (Hnat2 : (Datatypes.S n' + 1 - Datatypes.S i = n' + 1 - i)%nat) by lia.
         rewrite Hnat2. reflexivity. }
    setoid_rewrite (qeqT_imp_qeq _ _ (IH (fun i j => g (Datatypes.S i) j))).
    assert (Hn1 : (Datatypes.S n' = n' + 1)%nat) by lia.
    rewrite Hn1.
    assert (Hz1 : (n' + 1 - 0 = n' + 1)%nat) by lia.
    rewrite Hz1.
    assert (Hz2 : (n' + 1 + 1 - 0 = n' + 1 + 1)%nat) by lia.
    rewrite Hz2.
    ring.
Qed.

(* Row decomposition: the sum over i <= S m' and 1 <= j <= S m'−i of g(i,j) equals LHS(m') plus the sum of g i (m'+1−i). *)
Lemma sum_upto_row_succ : forall (m' : nat) (g : nat -> nat -> Q),QeqT (
  sum_upto (Datatypes.S m') (fun i => sum_upto (Datatypes.S m' - i) (fun j => g i (Datatypes.S j))) ) (
  sum_upto m' (fun i => sum_upto (m' - i) (fun j => g i (Datatypes.S j))) +
  sum_upto (Datatypes.S m') (fun i => g i (m' + 1 - i)%nat)).
Proof.
  intros m' g.
  apply qeq_imp_qeqT.
  rewrite (fun Hprm => qeqT_imp_qeq _ _ (sum_upto_ext_below (Datatypes.S m') (fun i => sum_upto (Datatypes.S m' - i) (fun j => g i (Datatypes.S j))) (fun i => sum_upto (m' - i) (fun j => g i (Datatypes.S j)) + g i (m' + 1 - i)%nat) Hprm)).
  2: { intros i Hi. apply NatLe_drop in Hi. apply qeq_imp_qeqT.
       assert (Hnat : (Datatypes.S m' - i = Datatypes.S (m' - i))%nat) by lia.
       rewrite Hnat.
       change (sum_upto (m' - i) (fun j : nat => g i (Datatypes.S j)) +
               g i (Datatypes.S (m' - i)) ==
               sum_upto (m' - i) (fun j : nat => g i (Datatypes.S j)) + g i (m' + 1 - i)%nat).
       assert (Hnat2 : (Datatypes.S (m' - i) = m' + 1 - i)%nat) by lia.
       rewrite Hnat2.
       reflexivity. }
  rewrite (qeqT_imp_qeq _ _ (sum_upto_plus (Datatypes.S m')
           (fun i => sum_upto (m' - i) (fun j => g i (Datatypes.S j)))
           (fun i => g i (m' + 1 - i)%nat))).
  assert (Hm : (m' - m' = 0)%nat) by lia.
  change (sum_upto (Datatypes.S m') (fun i => sum_upto (m' - i) (fun j => g i (Datatypes.S j)))) with
    (sum_upto m' (fun i => sum_upto (m' - i) (fun j => g i (Datatypes.S j))) +
     sum_upto (m' - m') (fun j => g m' (Datatypes.S j))).
  rewrite Hm.
  simpl. ring.
Qed.

(* Column decomposition: the sum over j <= S m' and 0 <= i <= S m'−S j of g(i,j) equals RHS(m') plus the sum of g i (m'+1−i). *)
Lemma sum_upto_col_succ : forall (m' : nat) (g : nat -> nat -> Q),QeqT (
  sum_upto (Datatypes.S m') (fun j => sum_upto (Datatypes.S m' - Datatypes.S j + 1) (fun i => g i (Datatypes.S j))) ) (
  sum_upto m' (fun j => sum_upto (m' - Datatypes.S j + 1) (fun i => g i (Datatypes.S j))) +
  sum_upto (Datatypes.S m') (fun i => g i (m' + 1 - i)%nat)).
Proof.
  intros m' g.
  apply qeq_imp_qeqT.
  change (sum_upto (Datatypes.S m') (fun j => sum_upto (Datatypes.S m' - Datatypes.S j + 1) (fun i => g i (Datatypes.S j)))) with
    (sum_upto m' (fun j => sum_upto (Datatypes.S m' - Datatypes.S j + 1) (fun i => g i (Datatypes.S j))) +
     sum_upto (Datatypes.S m' - Datatypes.S m' + 1) (fun i => g i (Datatypes.S m'))).
  assert (Hlast : (Datatypes.S m' - Datatypes.S m' + 1 = 1)%nat) by lia.
  rewrite Hlast.
  rewrite (fun Hprm => qeqT_imp_qeq _ _ (sum_upto_ext_below m' (fun j => sum_upto (Datatypes.S m' - Datatypes.S j + 1) (fun i => g i (Datatypes.S j))) (fun j => sum_upto (m' - Datatypes.S j + 1) (fun i => g i (Datatypes.S j)) + g (m' - j)%nat (Datatypes.S j)) Hprm)).
  2: { intros j Hj. apply NatLe_drop in Hj. apply qeq_imp_qeqT.
       assert (Hnat : (Datatypes.S m' - Datatypes.S j + 1 = Datatypes.S (m' - j))%nat) by lia.
       rewrite Hnat.
       change (sum_upto (m' - j) (fun i : nat => g i (Datatypes.S j)) + g (m' - j)%nat (Datatypes.S j) ==
               sum_upto (m' - Datatypes.S j + 1) (fun i : nat => g i (Datatypes.S j)) + g (m' - j)%nat (Datatypes.S j)).
       assert (Hnat2 : (m' - j = m' - Datatypes.S j + 1)%nat) by lia.
       rewrite Hnat2.
       reflexivity. }
  rewrite (qeqT_imp_qeq _ _ (sum_upto_plus m'
           (fun j => sum_upto (m' - Datatypes.S j + 1) (fun i => g i (Datatypes.S j)))
           (fun j => g (m' - j)%nat (Datatypes.S j)))).
  setoid_rewrite <- (qeqT_imp_qeq _ _ (sum_upto_rev m' (fun j => g (m' - j)%nat (Datatypes.S j)))).
  rewrite (fun Hprm => qeqT_imp_qeq _ _ (sum_upto_ext_below m' (fun k => g (m' - (m' - 1 - k))%nat (Datatypes.S (m' - 1 - k))) (fun k => g (Datatypes.S k) (m' - k)%nat) Hprm)).
  2: { intros k Hk. apply NatLe_drop in Hk. apply qeq_imp_qeqT.
       assert (Hx : (m' - (m' - 1 - k) = Datatypes.S k)%nat) by lia.
       rewrite Hx.
       assert (Hy : (Datatypes.S (m' - 1 - k) = m' - k)%nat) by lia.
       rewrite Hy.
       reflexivity. }
  rewrite (qeqT_imp_qeq _ _ (sum_upto_shift_boundary m' g)).
  change (sum_upto (Datatypes.S m') (fun i => g i (m' + 1 - i)%nat)) with
    (sum_upto m' (fun i => g i (m' + 1 - i)%nat) + g m' (m' + 1 - m')%nat).
  assert (H1 : (m' + 1 - m' = 1)%nat) by lia.
  rewrite H1.
  simpl.
  assert (Hsm : (Datatypes.S m' = m' + 1)%nat) by lia.
  rewrite Hsm.
  ring.
Qed.

(* Standard triangular swap: the sum over 0 <= i <= m−1, 1 <= j <= m−i of g(i,j) equals
   the sum over 1 <= j <= m, 0 <= i <= m−j of g(i,j).
   By induction on [m]: decompose the left side with [sum_upto_row_succ] and the right with
   [sum_upto_col_succ] (the identical correction terms cancel). *)
Lemma sum_upto_tri_swap_std : forall (m : nat) (g : nat -> nat -> Q),QeqT (
  sum_upto m (fun i => sum_upto (m - i) (fun j => g i (Datatypes.S j))) ) (
  sum_upto m (fun j => sum_upto (m - Datatypes.S j + 1) (fun i => g i (Datatypes.S j)))).
Proof.
  intros m.
  induction m as [| m' IH].
  - intros g. apply qeq_imp_qeqT. reflexivity.
  - intros g. apply qeq_imp_qeqT.
    rewrite (qeqT_imp_qeq _ _ (sum_upto_row_succ m' g)).
    rewrite (qeqT_imp_qeq _ _ (sum_upto_col_succ m' g)).
    specialize (IH g).
    setoid_rewrite (qeqT_imp_qeq _ _ IH).
    ring.
Qed.

(* ============ Splitting lemmas for bounded sums ============ *)
(* One-dimensional shift plus boundary: the sum of f (S a + i) over i < b equals
   the sum of f (a + i) over i < b - f a + f (a+b),
   by induction on [b] (the basis for [sum_upto_add]). *)
Lemma sum_upto_shift1 : forall (a b : nat) (f : nat -> Q),QeqT (
  sum_upto b (fun i => f (Datatypes.S a + i)%nat) ) (
  sum_upto b (fun i => f (a + i)%nat) - f a + f (a + b)%nat).
Proof.
  intros a b f.
  apply qeq_imp_qeqT.
  induction b as [| b' IH].
  - (* Case b = 0: 0 == 0 - f a + f (a+0), with a+0 == a by [lia]. *)
    assert (Hz : (a + 0 = a)%nat) by lia.
    rewrite Hz.
    change (sum_upto 0 (fun i : nat => f (Datatypes.S a + i)%nat)) with 0.
    change (sum_upto 0 (fun i : nat => f (a + i)%nat)) with 0.
    ring.
  - (* Case b = S b': sum_upto (S b') (fun i => f (S a + i)) = sum_upto b' (fun i => f (S a + i)) + f (S a + b'). *)
    change (sum_upto b' (fun i => f (Datatypes.S a + i)%nat) + f (Datatypes.S a + b')%nat ==
            sum_upto (Datatypes.S b') (fun i => f (a + i)%nat) - f a + f (a + Datatypes.S b')%nat).
    setoid_rewrite IH.
    (* sum_upto (S b') (fun i => f (a+i)) = sum_upto b' (fun i => f (a+i)) + f (a + b')%nat *)
    change (sum_upto (Datatypes.S b') (fun i => f (a + i)%nat)) with
      (sum_upto b' (fun i => f (a + i)%nat) + f (a + b')%nat).
    (* Reduce the index shapes: S a + b' == S (a + b') and a + S b' == S (a + b'). *)
    assert (H1 : (Datatypes.S a + b' = Datatypes.S (a + b'))%nat) by lia.
    rewrite H1.
    assert (H2 : (a + Datatypes.S b' = Datatypes.S (a + b'))%nat) by lia.
    rewrite H2.
    ring.
Qed.

(* Splitting at a: the sum over i < a+b of f i equals the sum over i < a of f i plus the sum over i < b of f (a + i), by induction on [a]. *)
Lemma sum_upto_add : forall (a b : nat) (f : nat -> Q),QeqT (
  sum_upto (a + b) f ) ( sum_upto a f + sum_upto b (fun i => f (a + i)%nat)).
Proof.
  intros a b f.
  apply qeq_imp_qeqT.
  induction a as [| a' IH].
  - simpl. change (sum_upto b (fun i : nat => f i)) with (sum_upto b f). ring.
  - (* Case a = S a': S a' + b == S (a' + b). *)
    assert (Had : (Datatypes.S a' + b = Datatypes.S (a' + b))%nat) by lia.
    rewrite Had.
    change (sum_upto (Datatypes.S (a' + b)) f ==
            sum_upto (Datatypes.S a') f + sum_upto b (fun i => f (Datatypes.S a' + i)%nat)).
    change (sum_upto (a' + b) f + f (a' + b)%nat ==
            sum_upto a' f + f a'%nat + sum_upto b (fun i => f (Datatypes.S a' + i)%nat)).
    setoid_rewrite IH.
    setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_shift1 a' b f)).
    ring.
Qed.

(* ============ Triangular swap family with [min]-bounded ranges ============ *)

(* Leibniz rewriting of the [sum_upto] bound plus splitting along j (N == (N−m+1)+(m−1); safe because f is an argument). *)
Lemma sum_upto_nat_eq : forall (n m : nat) (f : nat -> Q), n = m ->QeqT ( sum_upto n f ) ( sum_upto m f).
Proof. intros. subst. apply qeq_imp_qeqT. reflexivity. Qed.

(* ============ The pairing argument: row expansion of the difference of [corr] ============ *)

Lemma esq_row_sum_upto : forall (N i : nat) (a : Q),QeqT (
  esq_row N i a ) (
  sum_upto (i + 1) (fun j => q_pow a (2 * N + 2 * j) / (q_fact (2 * N) * q_fact (2 * j)))).
Proof.
  intros N i a.
  apply qeq_imp_qeqT.
  induction i as [| i' IH].
  - (* Case i = 0: esq_row N 0 == q_pow a (2N)/((2N)! * 0!), and sum_upto 1 f == f 0. *)
    change (esq_row N 0 a) with (q_pow a (2 * N) / (q_fact (2 * N) * q_fact 0)).
    (* sum_upto (0+1) f == sum_upto 0 f + f 0 == 0 + f 0: unfold with [simpl] and close by [ring]. *)
    assert (Hs : sum_upto (0 + 1) (fun j : nat => q_pow a (2 * N + 2 * j) / (q_fact (2 * N) * q_fact (2 * j))) ==
                 q_pow a (2 * N + 2 * 0) / (q_fact (2 * N) * q_fact (2 * 0))).
    { simpl. ring. }
    rewrite Hs.
    assert (Hz : (2 * N + 2 * 0 = 2 * N)%nat) by lia.
    setoid_replace (q_pow a (2 * N + 2 * 0)) with (q_pow a (2 * N)).
    2: { apply (q_pow_comp_proper a a (Qeq_refl a) (2 * N + 2 * 0)%nat (2 * N)%nat Hz). }
    change (q_fact (2 * 0)) with (q_fact 0).
    reflexivity.
  - (* Case i = S i': esq_row N (S i') == esq_row N i' + q_pow a (2N+2*S i')/((2N)! * (2*S i')!). *)
    change (esq_row N (Datatypes.S i') a) with
      (esq_row N i' a + q_pow a (2 * N + 2 * Datatypes.S i') / (q_fact (2 * N) * q_fact (2 * Datatypes.S i'))).
    (* sum_upto (S i' + 1) f == sum_upto (i' + 1) f + f (i' + 1) *)
    assert (Hsu : (Datatypes.S i' + 1 = Datatypes.S (i' + 1))%nat) by lia.
    rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq (Datatypes.S i' + 1) (Datatypes.S (i' + 1))
              (fun j => q_pow a (2 * N + 2 * j) / (q_fact (2 * N) * q_fact (2 * j))) Hsu)).
    change (sum_upto (Datatypes.S (i' + 1)) (fun j => q_pow a (2 * N + 2 * j) / (q_fact (2 * N) * q_fact (2 * j)))) with
      (sum_upto (i' + 1) (fun j => q_pow a (2 * N + 2 * j) / (q_fact (2 * N) * q_fact (2 * j))) +
       q_pow a (2 * N + 2 * (i' + 1)) / (q_fact (2 * N) * q_fact (2 * (i' + 1)))).
    setoid_rewrite IH.
    (* Reduce the tail-term indices: 2*S i' == 2*(i'+1) for both [q_pow] and [q_fact]; assert the tail equality first, then rewrite. *)
    assert (Hp : (2 * Datatypes.S i' = 2 * (i' + 1))%nat) by lia.
    assert (Htail : q_pow a (2 * N + 2 * Datatypes.S i') / (q_fact (2 * N) * q_fact (2 * Datatypes.S i')) ==
                    q_pow a (2 * N + 2 * (i' + 1)) / (q_fact (2 * N) * q_fact (2 * (i' + 1)))).
    { assert (Hp1 : (2 * N + 2 * Datatypes.S i' = 2 * N + 2 * (i' + 1))%nat) by lia.
      setoid_rewrite (q_pow_comp_proper a a (Qeq_refl a)
                        (2 * N + 2 * Datatypes.S i')%nat (2 * N + 2 * (i' + 1))%nat Hp1).
      setoid_rewrite (qeqT_imp_qeq _ _ (q_fact_nat_eq (2 * Datatypes.S i') (2 * (i' + 1)) Hp)).
      reflexivity. }
    setoid_rewrite Htail.
    reflexivity.
Qed.

Lemma osq_row_sum_upto : forall (N i : nat) (a : Q),QeqT (
  osq_row N i a ) (
  sum_upto (i + 1) (fun j => q_pow a (2 * N + 2 * j + 2) / (q_fact (2 * N + 1) * q_fact (2 * j + 1)))).
Proof.
  intros N i a.
  apply qeq_imp_qeqT.
  induction i as [| i' IH].
  - (* Case i = 0: osq_row N 0 == q_pow a (2N+2)/((2N+1)! * 1!), and sum_upto 1 f == f 0. *)
    change (osq_row N 0 a) with (q_pow a (2 * N + 2) / (q_fact (2 * N + 1) * q_fact 1)).
    assert (Hs : sum_upto (0 + 1) (fun j : nat => q_pow a (2 * N + 2 * j + 2) / (q_fact (2 * N + 1) * q_fact (2 * j + 1))) ==
                 q_pow a (2 * N + 2 * 0 + 2) / (q_fact (2 * N + 1) * q_fact (2 * 0 + 1))).
    { simpl. ring. }
    rewrite Hs.
    assert (Hz : (2 * N + 2 * 0 + 2 = 2 * N + 2)%nat) by lia.
    setoid_replace (q_pow a (2 * N + 2 * 0 + 2)) with (q_pow a (2 * N + 2)).
    2: { apply (q_pow_comp_proper a a (Qeq_refl a) (2 * N + 2 * 0 + 2)%nat (2 * N + 2)%nat Hz). }
    assert (Hf : (2 * 0 + 1 = 1)%nat) by lia.
    setoid_replace (q_fact (2 * 0 + 1)) with (q_fact 1).
    2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. lia. }
    reflexivity.
  - change (osq_row N (Datatypes.S i') a) with
      (osq_row N i' a + q_pow a (2 * N + 2 * Datatypes.S i' + 2) / (q_fact (2 * N + 1) * q_fact (2 * Datatypes.S i' + 1))).
    assert (Hsu : (Datatypes.S i' + 1 = Datatypes.S (i' + 1))%nat) by lia.
    rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq (Datatypes.S i' + 1) (Datatypes.S (i' + 1))
              (fun j => q_pow a (2 * N + 2 * j + 2) / (q_fact (2 * N + 1) * q_fact (2 * j + 1))) Hsu)).
    change (sum_upto (Datatypes.S (i' + 1)) (fun j => q_pow a (2 * N + 2 * j + 2) / (q_fact (2 * N + 1) * q_fact (2 * j + 1)))) with
      (sum_upto (i' + 1) (fun j => q_pow a (2 * N + 2 * j + 2) / (q_fact (2 * N + 1) * q_fact (2 * j + 1))) +
       q_pow a (2 * N + 2 * (i' + 1) + 2) / (q_fact (2 * N + 1) * q_fact (2 * (i' + 1) + 1))).
    setoid_rewrite IH.
    assert (Hp : (2 * N + 2 * Datatypes.S i' + 2 = 2 * N + 2 * (i' + 1) + 2)%nat) by lia.
    setoid_replace (q_pow a (2 * N + 2 * Datatypes.S i' + 2))
      with (q_pow a (2 * N + 2 * (i' + 1) + 2)).
    2: { apply (q_pow_comp_proper a a (Qeq_refl a)
                 (2 * N + 2 * Datatypes.S i' + 2)%nat (2 * N + 2 * (i' + 1) + 2)%nat Hp). }
    assert (Hf : (2 * Datatypes.S i' + 1 = 2 * (i' + 1) + 1)%nat) by lia.
    setoid_replace (q_fact (2 * Datatypes.S i' + 1)) with (q_fact (2 * (i' + 1) + 1)).
    2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. lia. }
    reflexivity.
Qed.

Lemma inner2_expand : forall (a : Q) (N i : nat), (1 <= i)%nat ->QeqT (
  inner2 N i a ) (
  - 2 * esq_row (Datatypes.S N) i a
  + 2 * osq_row N (i - 1) a
  + 2 * q_pow a (2 * N + 2 * i + 2) / (q_fact (2 * N + 2) * q_fact (2 * i))).
Proof.
  intros a N i Hi.
  apply qeq_imp_qeqT.
  assert (Hr := qeqT_imp_qeq _ _ (rows_vs_inner_i a N i Hi)).
  (* [Hr] states -inner2 == 2*esq - 2*osq - 2T, while the goal is inner2 == -2*esq + 2*osq + 2T.
     Negating both sides: inner2 == -(2*esq - 2*osq - 2T); transport through [Qeq_sym] applied to
     [Hr] and then close by [ring]. *)
  assert (Hopp : - (2 * esq_row (Datatypes.S N) i a
                    - 2 * osq_row N (i - 1) a
                    - 2 * q_pow a (2 * N + 2 * i + 2) / (q_fact (2 * N + 2) * q_fact (2 * i))) ==
                 inner2 N i a).
  { apply Qeq_sym.
    (* Goal: inner2 N i a == -(2*esq - 2*osq - 2T), that is inner2 == -X; rewrite X backwards using [Hr]. *)
    setoid_rewrite <- Hr.  (* the goal is inner2 == -X, so rewriting <- [Hr] matches its negated right side *)
    ring. }
  setoid_rewrite <- Hopp.
  ring.
Qed.

Lemma corr_diff_expand : forall (a : Q) (m : nat), (1 <= m)%nat ->QeqT (
  corr (Datatypes.S m) a - corr m a ) (
  sum_upto m
    (fun k' =>
       - 2 * esq_row (m + 2 + k') (m + 1 - k') a
       + 2 * esq_row (m + 1 + k') (m - k') a
       + 2 * osq_row (m + 1 + k') (m - k') a
       - 2 * osq_row (m + k') (m - k' - 1) a
       + 2 * q_pow a (4 * m + 6) / (q_fact (2 * m + 2 * k' + 4) * q_fact (2 * m + 2 - 2 * k'))
       - 2 * q_pow a (4 * m + 2) / (q_fact (2 * m + 2 * k' + 2) * q_fact (2 * m - 2 * k')))
  - 2 * esq_row (2 * m + 2) 1 a
  + 2 * osq_row (2 * m + 1) 0 a
  + 2 * q_pow a (4 * m + 6) / (q_fact (4 * m + 4) * q_fact 2)).
Proof.
  intros a m Hm.
  apply qeq_imp_qeqT.
  (* The difference of [corr] equals ksum_diff m m + inner2 (2m+1) 1, by [corr_succ_decomp] in reverse plus index reduction. *)
  assert (Hdec : corr (Datatypes.S m) a - corr m a ==
                 ksum_diff m m a + inner2 (2 * m + 1) 1 a).
  { assert (Hd2 : corr (Datatypes.S m) a - corr m a ==
                  ksum_diff m m a + inner2 (2 * m + 1) (2 * Datatypes.S m - (2 * m + 1)) a).
    { apply qeqT_imp_qeq. apply (corr_succ_decomp a m Hm). }
    assert (Hj : (2 * Datatypes.S m - (2 * m + 1) = 1)%nat) by lia.
    setoid_replace (inner2 (2 * m + 1) (2 * Datatypes.S m - (2 * m + 1)) a)
      with (inner2 (2 * m + 1) 1 a) in Hd2.
    2: { change (inner2 (2 * m + 1) (2 * Datatypes.S m - (2 * m + 1)) a ==
                 inner2 (2 * m + 1) 1 a).
         rewrite Hj. reflexivity. }
    exact Hd2. }
  rewrite Hdec.
  (* ksum_diff m m == sum_upto m (inner2 (m+1+k') (m+1−k') - inner2 (m+k') (m−k')) (step 4). *)
  rewrite (qeqT_imp_qeq _ _ (ksum_diff_row_step4 a m Hm)).
  (* ksum_diff m m == sum_upto m (inner2 (m+1+k') (m+1−k') - inner2 (m+k') (m−k')), by [ksum_diff_row_step4]. *)
  rewrite (fun Hprm => qeqT_imp_qeq _ _ (sum_upto_ext_below m (fun k' => inner2 (m + 1 + k') (m + 1 - k') a - inner2 (m + k') (m - k') a) (fun k' => - 2 * esq_row (m + 2 + k') (m + 1 - k') a + 2 * esq_row (m + 1 + k') (m - k') a + 2 * osq_row (m + 1 + k') (m - k') a - 2 * osq_row (m + k') (m - k' - 1) a + 2 * q_pow a (4 * m + 6) / (q_fact (2 * m + 2 * k' + 4) * q_fact (2 * m + 2 - 2 * k')) - 2 * q_pow a (4 * m + 2) / (q_fact (2 * m + 2 * k' + 2) * q_fact (2 * m - 2 * k'))) Hprm)).
  2: {
    intros k' Hk'. apply NatLe_drop in Hk'.
    apply qeq_imp_qeqT.
    (* [rows_vs_inner_i]: -inner2 N i == 2*esq_row (S N) i - 2*osq_row N (i−1) - 2T; negated,
       inner2 N i == -2*esq_row (S N) i + 2*osq_row N (i−1) + 2T. *)
    (* For inner2 (m+1+k') (m+1−k'): N = m+1+k' and i = m+1−k'. *)
    assert (Hr1 : inner2 (m + 1 + k') (m + 1 - k') a ==
                  - 2 * esq_row (m + 2 + k') (m + 1 - k') a
                  + 2 * osq_row (m + 1 + k') (m - k') a
                  + 2 * q_pow a (4 * m + 6) / (q_fact (2 * m + 2 * k' + 4) * q_fact (2 * m + 2 - 2 * k'))).
    { (* [inner2_expand] at N=m+1+k' and i=m+1−k', applied in the forward (LHS==RHS) direction with [setoid_rewrite]. *)
      assert (Hi1 : (1 <= m + 1 - k')%nat) by lia.
      setoid_rewrite (qeqT_imp_qeq _ _ (inner2_expand a (m + 1 + k') (m + 1 - k') Hi1)).
      (* Reduce the first argument of [esq_row]: S (m+1+k') == m+2+k'; and the second argument of [osq_row]: m+1−k'−1 == m−k'. *)
      assert (Hse : (Datatypes.S (m + 1 + k') = m + 2 + k')%nat) by lia.
      setoid_replace (esq_row (Datatypes.S (m + 1 + k')) (m + 1 - k') a)
        with (esq_row (m + 2 + k') (m + 1 - k') a).
      2: { change (esq_row (Datatypes.S (m + 1 + k')) (m + 1 - k') a ==
                   esq_row (m + 2 + k') (m + 1 - k') a).
           rewrite Hse. reflexivity. }
      assert (Hso : (m + 1 - k' - 1 = m - k')%nat) by lia.
      setoid_replace (osq_row (m + 1 + k') (m + 1 - k' - 1) a)
        with (osq_row (m + 1 + k') (m - k') a).
      2: { change (osq_row (m + 1 + k') (m + 1 - k' - 1) a ==
                   osq_row (m + 1 + k') (m - k') a).
           rewrite Hso. reflexivity. }
      (* For [q_pow]: the exponent 2N+2i+2 == 4m+6, and the denominator (2N+2)!(2i)! == (2m+2k'+4)!(2m+2−2k')!. *)
      assert (Hp : (2 * (m + 1 + k') + 2 * (m + 1 - k') + 2 = 4 * m + 6)%nat) by lia.
      setoid_replace (q_pow a (2 * (m + 1 + k') + 2 * (m + 1 - k') + 2))
        with (q_pow a (4 * m + 6)).
      2: { apply (q_pow_comp_proper a a (Qeq_refl a)
                   (2 * (m + 1 + k') + 2 * (m + 1 - k') + 2)%nat (4 * m + 6)%nat Hp). }
      assert (Hf1 : (2 * (m + 1 + k') + 2 = 2 * m + 2 * k' + 4)%nat) by lia.
      assert (Hf2 : (2 * (m + 1 - k') = 2 * m + 2 - 2 * k')%nat) by lia.
      setoid_replace (q_fact (2 * (m + 1 + k') + 2)) with (q_fact (2 * m + 2 * k' + 4)).
      2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. lia. }
      setoid_replace (q_fact (2 * (m + 1 - k'))) with (q_fact (2 * m + 2 - 2 * k')).
      2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. lia. }
      ring. }
    (* For inner2 (m+k') (m−k'): N = m+k' and i = m−k'. *)
    assert (Hr2 : inner2 (m + k') (m - k') a ==
                  - 2 * esq_row (m + 1 + k') (m - k') a
                  + 2 * osq_row (m + k') (m - k' - 1) a
                  + 2 * q_pow a (4 * m + 2) / (q_fact (2 * m + 2 * k' + 2) * q_fact (2 * m - 2 * k'))).
    { assert (Hi2 : (1 <= m - k')%nat) by lia.
      setoid_rewrite (qeqT_imp_qeq _ _ (inner2_expand a (m + k') (m - k') Hi2)).
      assert (Hse : (Datatypes.S (m + k') = m + 1 + k')%nat) by lia.
      setoid_replace (esq_row (Datatypes.S (m + k')) (m - k') a)
        with (esq_row (m + 1 + k') (m - k') a).
      2: { change (esq_row (Datatypes.S (m + k')) (m - k') a ==
                   esq_row (m + 1 + k') (m - k') a).
           rewrite Hse. reflexivity. }
      assert (Hp : (2 * (m + k') + 2 * (m - k') + 2 = 4 * m + 2)%nat) by lia.
      setoid_replace (q_pow a (2 * (m + k') + 2 * (m - k') + 2))
        with (q_pow a (4 * m + 2)).
      2: { apply (q_pow_comp_proper a a (Qeq_refl a)
                   (2 * (m + k') + 2 * (m - k') + 2)%nat (4 * m + 2)%nat Hp). }
      assert (Hf1 : (2 * (m + k') + 2 = 2 * m + 2 * k' + 2)%nat) by lia.
      assert (Hf2 : (2 * (m - k') = 2 * m - 2 * k')%nat) by lia.
      setoid_replace (q_fact (2 * (m + k') + 2)) with (q_fact (2 * m + 2 * k' + 2)).
      2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. lia. }
      setoid_replace (q_fact (2 * (m - k'))) with (q_fact (2 * m - 2 * k')).
      2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. lia. }
      ring. }
    (* Goal: inner2 A - inner2 B == the row difference at k'; rewrite with [Hr1] and [Hr2], then close by [ring]. *)
    setoid_rewrite Hr1. setoid_rewrite Hr2.
    ring. }
  (* Tail term: expand inner2 (2m+1) 1 with [rows_vs_inner_i]. *)
  assert (Htail : inner2 (2 * m + 1) 1 a ==
                  - 2 * esq_row (2 * m + 2) 1 a
                  + 2 * osq_row (2 * m + 1) 0 a
                  + 2 * q_pow a (4 * m + 6) / (q_fact (4 * m + 4) * q_fact 2)).
  { assert (Hi3 : (1 <= 1)%nat) by lia.
    setoid_rewrite (qeqT_imp_qeq _ _ (inner2_expand a (2 * m + 1) 1 Hi3)).
    assert (Hse : (Datatypes.S (2 * m + 1) = 2 * m + 2)%nat) by lia.
    setoid_replace (esq_row (Datatypes.S (2 * m + 1)) 1 a)
      with (esq_row (2 * m + 2) 1 a).
    2: { change (esq_row (Datatypes.S (2 * m + 1)) 1 a == esq_row (2 * m + 2) 1 a).
         rewrite Hse. reflexivity. }
    setoid_replace (osq_row (2 * m + 1) (1 - 1) a)
      with (osq_row (2 * m + 1) 0 a).
    2: { change (osq_row (2 * m + 1) (1 - 1) a == osq_row (2 * m + 1) 0 a).
         simpl. reflexivity. }
    assert (Hp : (2 * (2 * m + 1) + 2 * 1 + 2 = 4 * m + 6)%nat) by lia.
    setoid_replace (q_pow a (2 * (2 * m + 1) + 2 * 1 + 2))
      with (q_pow a (4 * m + 6)).
    2: { apply (q_pow_comp_proper a a (Qeq_refl a)
                 (2 * (2 * m + 1) + 2 * 1 + 2)%nat (4 * m + 6)%nat Hp). }
    assert (Hf1 : (2 * (2 * m + 1) + 2 = 4 * m + 4)%nat) by lia.
    assert (Hf2 : (2 * 1 = 2)%nat) by lia.
    setoid_replace (q_fact (2 * (2 * m + 1) + 2)) with (q_fact (4 * m + 4)).
    2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. lia. }
    setoid_replace (q_fact (2 * 1)) with (q_fact 2).
    2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. lia. }
    ring. }
  (* By transitivity: the left side (the sum_upto part plus the inner2 tail) equals sum_upto + RHS_tail, which equals the goal's right side. *)
  transitivity (sum_upto m
    (fun k' =>
       - 2 * esq_row (m + 2 + k') (m + 1 - k') a
       + 2 * esq_row (m + 1 + k') (m - k') a
       + 2 * osq_row (m + 1 + k') (m - k') a
       - 2 * osq_row (m + k') (m - k' - 1) a
       + 2 * q_pow a (4 * m + 6) / (q_fact (2 * m + 2 * k' + 4) * q_fact (2 * m + 2 - 2 * k'))
       - 2 * q_pow a (4 * m + 2) / (q_fact (2 * m + 2 * k' + 2) * q_fact (2 * m - 2 * k')))
    - 2 * esq_row (2 * m + 2) 1 a
    + 2 * osq_row (2 * m + 1) 0 a
    + 2 * q_pow a (4 * m + 6) / (q_fact (4 * m + 4) * q_fact 2)).
  - (* Left side == intermediate form: rewrite the inner2 tail with [Htail] and close by [ring] (reassociation). *)
    setoid_rewrite Htail.
    ring.
  - reflexivity.
Qed.

Lemma sum_upto_split : forall (m N : nat) (f : nat -> Q),
  (1 <= m)%nat -> (m <= N)%nat ->QeqT (
  sum_upto N f ) ( sum_upto (N - m + 1) f + sum_upto (m - 1) (fun j => f (N - m + 1 + j)%nat)).
Proof.
  intros m N f Hm Hmn.
  apply qeq_imp_qeqT.
  assert (Hadd : ((N - m + 1) + (m - 1) = N)%nat) by lia.
  rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq N ((N - m + 1) + (m - 1)) f (eq_sym Hadd))).
  setoid_rewrite <- (qeqT_imp_qeq _ _ (sum_upto_add (N - m + 1) (m - 1) f)).
  reflexivity.
Qed.

(* Reduction of the minimum: for j <= N−m, min(m−1, N−S j) = m−1; for j > N−m it equals N−S j. *)
Lemma min_lower : forall (m N j : nat), (1 <= m)%nat -> (m <= N)%nat -> (j <= N - m)%nat ->
  Id (Nat.min (m - 1)%nat (N - Datatypes.S j)%nat) (m - 1)%nat.
Proof.
  intros m N j Hm Hmn Hj.
  assert (Hle : ((m - 1) <= (N - Datatypes.S j))%nat) by lia.
  exact (eq_rect (Nat.min (m - 1)%nat (N - Datatypes.S j)%nat)
                 (fun z : nat => Id (Nat.min (m - 1)%nat (N - Datatypes.S j)%nat) z)
                 (@id_refl nat (Nat.min (m - 1)%nat (N - Datatypes.S j)%nat))
                 (m - 1)%nat
                 (Nat.min_l _ _ Hle)).
Qed.

Lemma min_upper : forall (m N j : nat), (1 <= m)%nat -> (m <= N)%nat -> (N - m < j)%nat ->
  Id (Nat.min (m - 1)%nat (N - Datatypes.S j)%nat) (N - Datatypes.S j)%nat.
Proof.
  intros m N j Hm Hmn Hj.
  assert (Hle : ((N - Datatypes.S j) <= (m - 1))%nat) by lia.
  exact (eq_rect (Nat.min (m - 1)%nat (N - Datatypes.S j)%nat)
                 (fun z : nat => Id (Nat.min (m - 1)%nat (N - Datatypes.S j)%nat) z)
                 (@id_refl nat (Nat.min (m - 1)%nat (N - Datatypes.S j)%nat))
                 (N - Datatypes.S j)%nat
                 (Nat.min_r _ _ Hle)).
Qed.

(* Padding each column: the full column equals the min-bounded column plus the padded remainder ([sum_upto_add] plus the [min] identities, with no case analysis). *)
Lemma sum_upto_min_pad : forall (m N j : nat) (f : nat -> Q),
  (j < N)%nat -> (1 <= m)%nat ->QeqT (
  sum_upto (N - Datatypes.S j + 1) f ) (
  sum_upto (Nat.min (m - 1)%nat (N - Datatypes.S j)%nat + 1) f +
  sum_upto (N - Datatypes.S j - Nat.min (m - 1)%nat (N - Datatypes.S j)%nat)%nat
           (fun i => f ((Nat.min (m - 1)%nat (N - Datatypes.S j)%nat + 1) + i)%nat)).
Proof.
  intros m N j f Hj Hm.
  apply qeq_imp_qeqT.
  assert (Hsum : (N - Datatypes.S j + 1 =
                  Nat.min (m - 1)%nat (N - Datatypes.S j)%nat + 1 +
                  (N - Datatypes.S j - Nat.min (m - 1)%nat (N - Datatypes.S j)%nat))%nat) by lia.
  rewrite Hsum.
  setoid_rewrite <- (qeqT_imp_qeq _ _ (sum_upto_add (Nat.min (m - 1)%nat (N - Datatypes.S j)%nat + 1)                     (N - Datatypes.S j - Nat.min (m - 1)%nat (N - Datatypes.S j)%nat) f)).
  reflexivity.
Qed.

(* The per-column excess equals the tail rows: the sum over j of the padded remainders equals
   the sum over 0 <= i <= N−m−1 and 1 <= j <= N−m−i of f (m+i) j.
   Split with [sum_upto_split] (j <= N−m versus j > N−m), reduce the minima, then apply
   [sum_upto_tri_swap_std] with n = N−m (in reverse). *)
Lemma excess_col_tail : forall (m N : nat) (f : nat -> nat -> Q),
  (1 <= m)%nat -> (m <= N)%nat ->QeqT (
  sum_upto N (fun j => sum_upto (N - Datatypes.S j - Nat.min (m - 1)%nat (N - Datatypes.S j)%nat)%nat
                               (fun i => f (Nat.min (m - 1)%nat (N - Datatypes.S j)%nat + 1 + i)%nat (Datatypes.S j))) ) (
  sum_upto (N - m)%nat (fun i => sum_upto (N - m - i)%nat (fun j => f (m + i)%nat (Datatypes.S j)))).
Proof.
  intros m N f Hm Hmn.
  apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (sum_upto_split m N           (fun j => sum_upto (N - Datatypes.S j - Nat.min (m - 1)%nat (N - Datatypes.S j)%nat)%nat
                              (fun i => f (Nat.min (m - 1)%nat (N - Datatypes.S j)%nat + 1 + i)%nat (Datatypes.S j)))           Hm Hmn)).
  assert (Hpre1538_47 : (forall i : nat, NatLe (Datatypes.S i) (N - m + 1) ->QeqT ( (fun j => sum_upto (N - Datatypes.S j - Nat.min (m - 1)%nat (N - Datatypes.S j)%nat)%nat (fun i => f (Nat.min (m - 1)%nat (N - Datatypes.S j)%nat + 1 + i)%nat (Datatypes.S j))) i ) ( (fun j => sum_upto (N - Datatypes.S j - (m - 1))%nat                              (fun i => f (m + i)%nat (Datatypes.S j))) i))).
  {  intros j Hj.
     apply NatLe_drop in Hj.
       apply qeq_imp_qeqT.
       assert (Hjle : (j <= N - m)%nat) by lia.
       destruct (id_sym (min_lower m N j Hm Hmn Hjle)).
       apply qeqT_imp_qeq.
       apply (sum_upto_ext (N - Datatypes.S j - (m - 1))%nat
              (fun i => f (m - 1 + 1 + i)%nat (Datatypes.S j)) (fun i => f (m + i)%nat (Datatypes.S j))).
       intro i. apply qeq_imp_qeqT. assert (Hx : (m - 1 + 1 + i = m + i)%nat) by lia. rewrite Hx. reflexivity. }
  rewrite (qeqT_imp_qeq _ _ (sum_upto_ext_below (N - m + 1)           (fun j => sum_upto (N - Datatypes.S j - Nat.min (m - 1)%nat (N - Datatypes.S j)%nat)%nat
                              (fun i => f (Nat.min (m - 1)%nat (N - Datatypes.S j)%nat + 1 + i)%nat (Datatypes.S j)))
           (fun j => sum_upto (N - Datatypes.S j - (m - 1))%nat                              (fun i => f (m + i)%nat (Datatypes.S j))) Hpre1538_47)).
  assert (Hpre1538_46 : (forall i,QeqT ( (fun j => sum_upto (N - Datatypes.S (N - m + 1 + j) - Nat.min (m - 1)%nat (N - Datatypes.S (N - m + 1 + j))%nat)%nat (fun i => f (Nat.min (m - 1)%nat (N - Datatypes.S (N - m + 1 + j))%nat + 1 + i)%nat (Datatypes.S (N - m + 1 + j)))) i ) ( (fun _ => 0) i))).
  {  intro j.
       apply qeq_imp_qeqT.
       assert (Hjg : (N - m < N - m + 1 + j)%nat) by lia.
       destruct (id_sym (min_upper m N (N - m + 1 + j) Hm Hmn Hjg)).
       assert (Hz : (N - Datatypes.S (N - m + 1 + j) - (N - Datatypes.S (N - m + 1 + j)) = 0)%nat) by lia.
       rewrite Hz.
       simpl. ring. }
  rewrite (qeqT_imp_qeq _ _ (sum_upto_ext (m - 1)           (fun j => sum_upto (N - Datatypes.S (N - m + 1 + j) - Nat.min (m - 1)%nat (N - Datatypes.S (N - m + 1 + j))%nat)%nat
                             (fun i => f (Nat.min (m - 1)%nat (N - Datatypes.S (N - m + 1 + j))%nat + 1 + i)%nat (Datatypes.S (N - m + 1 + j))))           (fun _ => 0) Hpre1538_46)).
  rewrite (qeqT_imp_qeq _ _ (sum_upto_zero _)).
  assert (Hsm : (N - m + 1 = Datatypes.S (N - m))%nat) by lia.
  rewrite Hsm.
  change (sum_upto (Datatypes.S (N - m)) (fun j => sum_upto (N - Datatypes.S j - (m - 1))%nat
                                                        (fun i => f (m + i)%nat (Datatypes.S j)))) with
    (sum_upto (N - m) (fun j => sum_upto (N - Datatypes.S j - (m - 1))%nat
                                          (fun i => f (m + i)%nat (Datatypes.S j))) +
     sum_upto (N - Datatypes.S (N - m) - (m - 1))%nat (fun i => f (m + i)%nat (Datatypes.S (N - m)))).
  assert (Hz : (N - Datatypes.S (N - m) - (m - 1) = 0)%nat) by lia.
  rewrite Hz.
  simpl.
  assert (Hpre1538_102 : (forall i : nat, NatLe (Datatypes.S i) (N - m) ->QeqT ( (fun j => sum_upto (N - Datatypes.S j - (m - 1))%nat (fun i => f (m + i)%nat (Datatypes.S j))) i ) ( (fun j => sum_upto (N - m - Datatypes.S j + 1) (fun i => f (m + i)%nat (Datatypes.S j))) i))).
  {  intros j Hj. apply NatLe_drop in Hj. apply qeq_imp_qeqT. assert (Hx : (N - Datatypes.S j - (m - 1) = N - m - Datatypes.S j + 1)%nat) by lia.
       rewrite Hx. reflexivity. }
  rewrite (qeqT_imp_qeq _ _ (sum_upto_ext_below (N - m) (fun j => sum_upto (N - Datatypes.S j - (m - 1))%nat (fun i => f (m + i)%nat (Datatypes.S j))) (fun j => sum_upto (N - m - Datatypes.S j + 1) (fun i => f (m + i)%nat (Datatypes.S j))) Hpre1538_102)).
  setoid_rewrite <- (qeqT_imp_qeq _ _ (sum_upto_tri_swap_std (N - m) (fun i j => f (m + i)%nat j))).
  change (sum_upto (N - m)
            (fun i => sum_upto (N - m - i) (fun j => f (m + i)%nat (Datatypes.S j))) + 0 + 0 ==
          sum_upto (N - m) (fun i => sum_upto (N - m - i) (fun j => f (m + i)%nat (Datatypes.S j)))).
  ring.
Qed.

(* Triangular swap with min-bounded ranges (completion method): the truncated left side equals the min-bounded right side.
   Truncated plus tail rows == the full left side ([sum_upto_add]); apply [sum_upto_tri_swap_std] at n = N;
   the full right side == the min-bounded right side plus the padded columns ([sum_upto_ext_below] columnwise
   plus [sum_upto_min_pad]); and the padded columns equal the tail rows ([excess_col_tail]). *)
Lemma sum_upto_tri_swap_min : forall (m N : nat) (f : nat -> nat -> Q),
  (1 <= m)%nat -> (m <= N)%nat ->QeqT (
  sum_upto m (fun i => sum_upto (N - i)%nat (fun j => f i (Datatypes.S j))) ) (
  sum_upto N (fun j => sum_upto (Nat.min (m - 1)%nat (N - Datatypes.S j)%nat + 1)%nat (fun i => f i (Datatypes.S j)))).
Proof.
  intros m N f Hm Hmn.
  apply qeq_imp_qeqT.
  setoid_replace (sum_upto m (fun i => sum_upto (N - i)%nat (fun j => f i (Datatypes.S j))))
    with (sum_upto N (fun i => sum_upto (N - i)%nat (fun j => f i (Datatypes.S j))) -
          sum_upto (N - m)%nat (fun i => sum_upto (N - m - i)%nat (fun j => f (m + i)%nat (Datatypes.S j)))).
  2: { assert (Hadd : (m + (N - m) = N)%nat) by lia.
       rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq N (m + (N - m)) (fun i => sum_upto (N - i)%nat (fun j => f i (Datatypes.S j))) (eq_sym Hadd))).
       setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_add m (N - m) (fun i => sum_upto (N - i)%nat (fun j => f i (Datatypes.S j))))).
       assert (Hpre1538_101 : (forall i : nat, NatLe (Datatypes.S i) (N - m) ->QeqT ( (fun i => sum_upto (N - (m + i))%nat (fun j => f (m + i)%nat (Datatypes.S j))) i ) ( (fun i => sum_upto (N - m - i)%nat (fun j => f (m + i)%nat (Datatypes.S j))) i))).
       {  intros i Hi. apply NatLe_drop in Hi. apply qeq_imp_qeqT. assert (Hx : (N - (m + i) = N - m - i)%nat) by lia.
            rewrite Hx. reflexivity. }
       rewrite (qeqT_imp_qeq _ _ (sum_upto_ext_below (N - m) (fun i => sum_upto (N - (m + i))%nat (fun j => f (m + i)%nat (Datatypes.S j))) (fun i => sum_upto (N - m - i)%nat (fun j => f (m + i)%nat (Datatypes.S j))) Hpre1538_101)).
       ring. }
  setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_tri_swap_std N f)).
  assert (Hpre1538_45 : (forall i : nat, NatLe (Datatypes.S i) N ->QeqT ( (fun j => sum_upto (N - Datatypes.S j + 1)%nat (fun i => f i (Datatypes.S j))) i ) ( (fun j => sum_upto (Nat.min (m - 1)%nat (N - Datatypes.S j)%nat + 1)%nat (fun i => f i (Datatypes.S j)) + sum_upto (N - Datatypes.S j - Nat.min (m - 1)%nat (N - Datatypes.S j)%nat)%nat                              (fun i => f (Nat.min (m - 1)%nat (N - Datatypes.S j)%nat + 1 + i)%nat (Datatypes.S j))) i))).
  {  intros j Hj.
       apply qeq_imp_qeqT.
       apply qeqT_imp_qeq.
       apply (sum_upto_min_pad m N j (fun i => f i (Datatypes.S j))).
       - exact (NatLe_drop (Datatypes.S j) N Hj). - exact Hm. }
  rewrite (qeqT_imp_qeq _ _ (sum_upto_ext_below N           (fun j => sum_upto (N - Datatypes.S j + 1)%nat (fun i => f i (Datatypes.S j)))
           (fun j => sum_upto (Nat.min (m - 1)%nat (N - Datatypes.S j)%nat + 1)%nat (fun i => f i (Datatypes.S j)) +
                     sum_upto (N - Datatypes.S j - Nat.min (m - 1)%nat (N - Datatypes.S j)%nat)%nat                              (fun i => f (Nat.min (m - 1)%nat (N - Datatypes.S j)%nat + 1 + i)%nat (Datatypes.S j))) Hpre1538_45)).
  rewrite (qeqT_imp_qeq _ _ (sum_upto_plus N           (fun j => sum_upto (Nat.min (m - 1)%nat (N - Datatypes.S j)%nat + 1)%nat (fun i => f i (Datatypes.S j)))
           (fun j => sum_upto (N - Datatypes.S j - Nat.min (m - 1)%nat (N - Datatypes.S j)%nat)%nat                              (fun i => f (Nat.min (m - 1)%nat (N - Datatypes.S j)%nat + 1 + i)%nat (Datatypes.S j))))).
  setoid_replace (sum_upto N (fun j => sum_upto (N - Datatypes.S j - Nat.min (m - 1)%nat (N - Datatypes.S j)%nat)%nat
                                            (fun i => f (Nat.min (m - 1)%nat (N - Datatypes.S j)%nat + 1 + i)%nat (Datatypes.S j))))
    with (sum_upto (N - m)%nat (fun i => sum_upto (N - m - i)%nat (fun j => f (m + i)%nat (Datatypes.S j)))).
  2: { apply qeqT_imp_qeq. apply (excess_col_tail m N f Hm Hmn). }
  ring.
Qed.

(* ============ The columnwise pairing family behind [c1] = ksum_diff (S m) m expanded and paired ============ *)

(* Linearity under negation and differences of [sum_upto] (needed to split the left side of [c1] into the first and second sums). *)
Lemma sum_upto_neg : forall (n : nat) (f : nat -> Q),QeqT (
  sum_upto n (fun i => - f i) ) ( - sum_upto n f).
Proof.
  intros n f.
  apply qeq_imp_qeqT.
  induction n as [| n' IH].
  - reflexivity.
  - simpl. setoid_rewrite IH. ring.
Qed.

Lemma sum_upto_minus : forall (n : nat) (f g : nat -> Q),QeqT (
  sum_upto n (fun i => f i - g i) ) ( sum_upto n f - sum_upto n g).
Proof.
  intros n f g.
  apply qeq_imp_qeqT.
  change (sum_upto n (fun i => f i + - g i) == sum_upto n f - sum_upto n g).
  rewrite (qeqT_imp_qeq _ _ (sum_upto_plus n f (fun i => - g i))).
  rewrite (qeqT_imp_qeq _ _ (sum_upto_neg n g)).
  ring.
Qed.

(* Shifting a column to the right: the sum of brk2 (k+1+i) j over i < ub equals the sum of brk2 (k+i) j over i <= ub minus brk2 k j (the core of the columnwise pairing in [c1]). *)
Lemma col_shift_right : forall (k j ub : nat) (a : Q),QeqT (
  sum_upto ub (fun i => brk2 (k + 1 + i) j a) ) (
  sum_upto (ub + 1) (fun i => brk2 (k + i) j a) - brk2 k j a).
Proof.
  intros k j ub a.
  apply qeq_imp_qeqT.
  assert (Hadd : (1 + ub = ub + 1)%nat) by lia.
  rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq (ub + 1) (1 + ub) (fun i => brk2 (k + i) j a) (eq_sym Hadd))).
  setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_add 1 ub (fun i => brk2 (k + i) j a))).
  simpl.
  assert (Hpre1538_44 : (forall i : nat, NatLe (Datatypes.S i) ub ->QeqT ( (fun i => brk2 (k + (1 + i)) j a) i ) ( (fun i => brk2 (k + 1 + i) j a) i))).
  {  intros i Hi. apply NatLe_drop in Hi. apply qeq_imp_qeqT. assert (Hx : (k + (1 + i) = k + 1 + i)%nat) by lia. rewrite Hx. reflexivity. }
  rewrite (qeqT_imp_qeq _ _ (sum_upto_ext_below ub           (fun i => brk2 (k + (1 + i)) j a) (fun i => brk2 (k + 1 + i) j a) Hpre1538_44)).
  assert (Hz : (k + 0 = k)%nat) by lia.
  rewrite Hz.
  ring.
Qed.

(* Shifting a column to the left (the converse of [col_shift_right]): the sum of brk2 (k+i) j over i <= ub equals brk2 k j plus the sum of brk2 (k+1+i) j over i < ub. *)
Lemma col_shift_left : forall (k j ub : nat) (a : Q),QeqT (
  sum_upto (ub + 1) (fun i => brk2 (k + i) j a) ) (
  brk2 k j a + sum_upto ub (fun i => brk2 (k + 1 + i) j a)).
Proof.
  intros k j ub a.
  apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (col_shift_right k j ub a)).
  ring.
Qed.

(* Generic Q-ring rearrangement lemmas ([ring] applied to variables; they work around the unreliability of [by ring] on Fixpoint atoms in [c1_col_mid]). *)
Lemma q_ring_reorder : forall (X A B C : Q),QeqT ( X + A - B + C ) ( A + C - B + X).
Proof. intros. apply qeq_imp_qeqT. ring. Qed.

Lemma q_ring_reorder2 : forall (X A B C : Q),QeqT ( A + C - B + X ) ( X + A + C - B).
Proof. intros. apply qeq_imp_qeqT. ring. Qed.

Lemma q_ring_reorder3 : forall (X B C : Q),QeqT ( X - B + C ) ( X + C - B).
Proof. intros. apply qeq_imp_qeqT. ring. Qed.

(* Columnwise pairing for [c1] (segment 1a, j <= 1, where both minima equal m−1): the first column == the second column + brk2 (2m+1) (S j) - brk2 (m+1) (S j). *)
Lemma c1_col_lo_shift : forall (m j : nat) (a : Q), (j <= 1)%nat -> (1 <= m)%nat ->QeqT (
  sum_upto (Nat.min (m - 1) (m + 2 - Datatypes.S j) + 1) (fun i => brk2 (m + 2 + i) (Datatypes.S j) a)
  ) ( sum_upto (Nat.min (m - 1) (m + 1 - Datatypes.S j) + 1) (fun i => brk2 (m + 1 + i) (Datatypes.S j) a)
     + brk2 (2 * m + 1) (Datatypes.S j) a - brk2 (m + 1) (Datatypes.S j) a).
Proof.
  intros m j a Hj1 Hm.
  apply qeq_imp_qeqT.
  assert (Hmin1 : (Nat.min (m - 1) (m + 2 - Datatypes.S j) = m - 1)%nat) by (apply Nat.min_l; lia).
  assert (Hmin2 : (Nat.min (m - 1) (m + 1 - Datatypes.S j) = m - 1)%nat) by (apply Nat.min_l; lia).
  rewrite Hmin1. rewrite Hmin2.
  (* The first column is sum_upto m (since m−1+1 == m); peel off the tail term brk2 (2m+1) (S j). *)
  assert (Hup1 : (m - 1 + 1 = m)%nat) by lia.
  rewrite Hup1.
  (* sum_upto m == sum_upto (m−1) + the tail term (m = S(m−1), valid since m >= 1, by [lia]). *)
  assert (Hm1 : (m = Datatypes.S (m - 1))%nat) by lia.
  rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq m (Datatypes.S (m - 1)) (fun i => brk2 (m + 2 + i) (Datatypes.S j) a) Hm1)).
  change (sum_upto (Datatypes.S (m - 1)) (fun i => brk2 (m + 2 + i) (Datatypes.S j) a)) with
    (sum_upto (m - 1) (fun i => brk2 (m + 2 + i) (Datatypes.S j) a) +
     brk2 (m + 2 + (m - 1)) (Datatypes.S j) a).
  assert (Hk : (m + 2 + (m - 1) = 2 * m + 1)%nat) by lia.
  rewrite Hk.
  (* Apply [col_shift_right] at k=m+1 and ub=m−1 (first realign the summand arguments with [sum_upto_ext_below]: m+2+i == m+1+1+i). *)
  assert (Hpre1538_43 : (forall i : nat, NatLe (Datatypes.S i) (m - 1) ->QeqT ( (fun i => brk2 (m + 2 + i) (Datatypes.S j) a) i ) ( (fun i => brk2 (m + 1 + 1 + i) (Datatypes.S j) a) i))).
  {  intros i Hi. apply NatLe_drop in Hi. apply qeq_imp_qeqT. assert (Hnat : (m + 2 + i = m + 1 + 1 + i)%nat) by lia. rewrite Hnat. reflexivity. }
  rewrite (qeqT_imp_qeq _ _ (sum_upto_ext_below (m - 1)           (fun i => brk2 (m + 2 + i) (Datatypes.S j) a)           (fun i => brk2 (m + 1 + 1 + i) (Datatypes.S j) a) Hpre1538_43)).
  setoid_rewrite (qeqT_imp_qeq _ _ (col_shift_right (m + 1) (Datatypes.S j) (m - 1) a)).
  (* Reduce the second column's bound: m−1+1 == m. *)
  assert (Hup2 : (m - 1 + 1 = m)%nat) by lia.
  rewrite Hup2.
  apply (qeqT_imp_qeq _ _ (q_ring_reorder3 (sum_upto m (fun i => brk2 (m + 1 + i) (Datatypes.S j) a))           (brk2 (m + 1) (Datatypes.S j) a)           (brk2 (2 * m + 1) (Datatypes.S j) a))).
Qed.

(* Columnwise pairing for [c1] (segment 2, j = m+1): the first column collapses to the supplementary term brk2 (m+2) (m+2). *)
Lemma c1_col_hi : forall (m : nat) (a : Q), (1 <= m)%nat ->QeqT (
  sum_upto (Nat.min (m - 1) (m + 2 - Datatypes.S (m + 1)) + 1) (fun i => brk2 (m + 2 + i) (Datatypes.S (m + 1)) a)
  ) ( brk2 (m + 2) (m + 2) a).
Proof.
  intros m a Hm.
  apply qeq_imp_qeqT.
  (* S(m+1) == m+2, reduced by [lia] (a [sum_upto] bound). *)
  assert (Hsm : (Datatypes.S (m + 1) = m + 2)%nat) by lia.
  (* min(m−1, m+2−(m+2)) = 0 *)
  assert (Hmin : (Nat.min (m - 1) (m + 2 - Datatypes.S (m + 1)) = 0)%nat).
  { rewrite Hsm. lia. }
  (* Rewrite with [Hmin] in the [sum_upto] bound: the min subterm becomes 0 and the bound becomes 0+1. *)
  rewrite Hmin.
  (* [simpl] unfolds sum_upto (0+1) to brk2 (m+2+0) (S(m+1)). *)
  simpl.
  (* The second argument of brk2: S(m+1) -> m+2. *)
  rewrite Hsm.
  (* The first argument of brk2: m+2+0 -> m+2. *)
  assert (Hz : (m + 2 + 0 = m + 2)%nat) by lia.
  rewrite Hz.
  ring.
Qed.

(* Columnwise pairing for [c1] (segment 1b, 2 <= j <= m): the first column == the second column
   + the supplementary column - brk2 (m+1) (S j).
   Reduce the minima and apply [col_shift_right] (the peeled tail term equals the supplementary column). *)
Lemma c1_col_mid : forall (m j : nat) (a : Q), (2 <= j)%nat -> (j <= m)%nat -> (1 <= m)%nat ->QeqT (
  sum_upto (Nat.min (m - 1) (m + 2 - Datatypes.S j) + 1) (fun i => brk2 (m + 2 + i) (Datatypes.S j) a)
  ) ( sum_upto (Nat.min (m - 1) (m + 1 - Datatypes.S j) + 1) (fun i => brk2 (m + 1 + i) (Datatypes.S j) a)
     + brk2 (2 * m + 3 - Datatypes.S j) (Datatypes.S j) a
     + brk2 (2 * m + 4 - Datatypes.S j) (Datatypes.S j) a
     - brk2 (m + 1) (Datatypes.S j) a).
Proof.
  intros m j a Hj2 Hjm Hm.
  apply qeq_imp_qeqT.
  assert (Hmin1 : (Nat.min (m - 1) (m + 2 - Datatypes.S j) = m + 2 - Datatypes.S j)%nat) by (apply Nat.min_r; lia).
  assert (Hmin2 : (Nat.min (m - 1) (m + 1 - Datatypes.S j) = m + 1 - Datatypes.S j)%nat) by (apply Nat.min_r; lia).
  rewrite Hmin1. rewrite Hmin2.
  (* The first column is sum_upto (m+2−S j+1); peel off the tail term brk2 (2m+4−S j).
     The bounds m+2−S j+1 and S(m+2−S j) are equal, reduced by [lia]. *)
  assert (Hsucc : (m + 2 - Datatypes.S j + 1 = Datatypes.S (m + 2 - Datatypes.S j))%nat) by lia.
  rewrite Hsucc.
  change (sum_upto (Datatypes.S (m + 2 - Datatypes.S j)) (fun i => brk2 (m + 2 + i) (Datatypes.S j) a)) with
    (sum_upto (m + 2 - Datatypes.S j) (fun i => brk2 (m + 2 + i) (Datatypes.S j) a) +
     brk2 (m + 2 + (m + 2 - Datatypes.S j)) (Datatypes.S j) a).
  (* The tail term has k = m+2+m+2−S j = 2m+4−S j, reduced by [lia]. *)
  assert (Hk : (m + 2 + (m + 2 - Datatypes.S j) = 2 * m + 4 - Datatypes.S j)%nat) by lia.
  rewrite Hk.
  (* Apply [col_shift_right] at k=m+1 and ub=m+2−S j. *)
  assert (Hpre1538_42 : (forall i : nat, NatLe (Datatypes.S i) (m + 2 - Datatypes.S j) ->QeqT ( (fun i => brk2 (m + 2 + i) (Datatypes.S j) a) i ) ( (fun i => brk2 (m + 1 + 1 + i) (Datatypes.S j) a) i))).
  {  intros i Hi. apply NatLe_drop in Hi. apply qeq_imp_qeqT. assert (Hnat : (m + 2 + i = m + 1 + 1 + i)%nat) by lia. rewrite Hnat. reflexivity. }
  rewrite (qeqT_imp_qeq _ _ (sum_upto_ext_below (m + 2 - Datatypes.S j)           (fun i => brk2 (m + 2 + i) (Datatypes.S j) a)           (fun i => brk2 (m + 1 + 1 + i) (Datatypes.S j) a) Hpre1538_42)).
  setoid_rewrite (qeqT_imp_qeq _ _ (col_shift_right (m + 1) (Datatypes.S j) (m + 2 - Datatypes.S j) a)).
  (* sum_upto (m+3−S j) (fun i => brk2 (m+1+i) (S j)) == the second column + brk2 (2m+3−S j); peel off the tail term. *)
  setoid_replace (sum_upto (m + 2 - Datatypes.S j + 1) (fun i => brk2 (m + 1 + i) (Datatypes.S j) a))
    with (sum_upto (m + 2 - Datatypes.S j) (fun i => brk2 (m + 1 + i) (Datatypes.S j) a) +
          brk2 (m + 1 + (m + 2 - Datatypes.S j)) (Datatypes.S j) a).
  2: { assert (Hsucc2 : (m + 2 - Datatypes.S j + 1 = Datatypes.S (m + 2 - Datatypes.S j))%nat) by lia.
       rewrite Hsucc2. reflexivity. }
  assert (Hk2 : (m + 1 + (m + 2 - Datatypes.S j) = 2 * m + 3 - Datatypes.S j)%nat) by lia.
  rewrite Hk2.
  (* The second column: sum_upto (m+1−S j+1), with m+1−S j+1 == m+2−S j by [lia]. *)
  assert (Hup : (m + 1 - Datatypes.S j + 1 = m + 2 - Datatypes.S j)%nat) by lia.
  rewrite Hup.
  setoid_replace (sum_upto (m + 2 - Datatypes.S j) (fun i => brk2 (m + 1 + i) (Datatypes.S j) a) +
                  brk2 (2 * m + 3 - Datatypes.S j) (Datatypes.S j) a - brk2 (m + 1) (Datatypes.S j) a +
                  brk2 (2 * m + 4 - Datatypes.S j) (Datatypes.S j) a)
    with (brk2 (2 * m + 3 - Datatypes.S j) (Datatypes.S j) a + brk2 (2 * m + 4 - Datatypes.S j) (Datatypes.S j) a -
          brk2 (m + 1) (Datatypes.S j) a + sum_upto (m + 2 - Datatypes.S j) (fun i => brk2 (m + 1 + i) (Datatypes.S j) a))
    by (apply (qeqT_imp_qeq _ _ (q_ring_reorder (sum_upto (m + 2 - Datatypes.S j) (fun i => brk2 (m + 1 + i) (Datatypes.S j) a))                (brk2 (2 * m + 3 - Datatypes.S j) (Datatypes.S j) a)
                (brk2 (m + 1) (Datatypes.S j) a)
                (brk2 (2 * m + 4 - Datatypes.S j) (Datatypes.S j) a)))).
  apply qeqT_imp_qeq.
  apply (q_ring_reorder2 (sum_upto (m + 2 - Datatypes.S j) (fun i => brk2 (m + 1 + i) (Datatypes.S j) a)) (brk2 (2 * m + 3 - Datatypes.S j) (Datatypes.S j) a) (brk2 (m + 1) (Datatypes.S j) a) (brk2 (2 * m + 4 - Datatypes.S j) (Datatypes.S j) a)).
Qed.

(* Supplementary rows become columns ([supp_col]): the sum over 0 <= i <= m−1 of
   [brk2 (m+2+i)(m+1−i) + brk2 (m+2+i)(m+2−i)]
   == the sum over 2 <= S <= m+1 of brk2 (2m+3−S)(S) + the sum over 3 <= S <= m+2 of brk2 (2m+4−S)(S).
   Reverse the index by the substitution of [sum_upto_rev]: i' = m−1−i, with S = i'+2 for the first
   family and S = i'+3 for the second. *)
Lemma supp_col : forall (m : nat) (a : Q),QeqT (
  sum_upto m (fun i => brk2 (m + 2 + i) (m + 1 - i) a + brk2 (m + 2 + i) (m + 2 - i) a) ) (
  sum_upto m (fun i => brk2 (2 * m + 1 - i) (i + 2) a) +
  sum_upto m (fun i => brk2 (2 * m + 1 - i) (i + 3) a)).
Proof.
  intros m a.
  apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (sum_upto_plus m (fun i => brk2 (m + 2 + i) (m + 1 - i) a) (fun i => brk2 (m + 2 + i) (m + 2 - i) a))).
  (* First family: the sum over i of brk2 (m+2+i)(m+1−i) == the sum over i of brk2 (2m+1−i)(i+2).
     For h of [sum_upto_rev m], h(m−1−i) = brk2 (2m+1−(m−1−i))((m−1−i)+2) == brk2 (m+2+i)(m+1−i). *)
  (* First-family identity: the sum over i of brk2 (m+2+i)(m+1−i) == the sum over i of brk2 (2m+1−i)(i+2).
     [sum_upto_ext_below] transports to the reversed form (2m+1−(m−1−i) == m+2+i for i < m),
     and [sum_upto_rev] restores the range. *)
  assert (Htmp1 : sum_upto m (fun i => brk2 (m + 2 + i) (m + 1 - i) a) ==
                  sum_upto m (fun i => brk2 (2 * m + 1 - (m - 1 - i)) ((m - 1 - i) + 2) a)).
  { apply qeqT_imp_qeq.
    apply (sum_upto_ext_below m
             (fun i => brk2 (m + 2 + i) (m + 1 - i) a)
             (fun i => brk2 (2 * m + 1 - (m - 1 - i)) ((m - 1 - i) + 2) a)).
    intros i Hi. apply NatLe_drop in Hi.
    apply qeq_imp_qeqT.
    assert (Ha : (2 * m + 1 - (m - 1 - i) = m + 2 + i)%nat) by lia.
    assert (Hb : ((m - 1 - i) + 2 = m + 1 - i)%nat) by lia.
    rewrite Ha, Hb. reflexivity. }
  assert (H1 : sum_upto m (fun i => brk2 (m + 2 + i) (m + 1 - i) a) ==
               sum_upto m (fun i => brk2 (2 * m + 1 - i) (i + 2) a)).
  { rewrite (qeqT_imp_qeq _ _ (sum_upto_rev m (fun i => brk2 (2 * m + 1 - i) (i + 2) a))) in Htmp1.
    exact Htmp1. }
  (* Second-family identity: the sum over i of brk2 (m+2+i)(m+2−i) == the sum over i of brk2 (2m+1−i)(i+3). *)
  assert (Htmp2 : sum_upto m (fun i => brk2 (m + 2 + i) (m + 2 - i) a) ==
                  sum_upto m (fun i => brk2 (2 * m + 1 - (m - 1 - i)) ((m - 1 - i) + 3) a)).
  { apply qeqT_imp_qeq.
  apply (sum_upto_ext_below m             (fun i => brk2 (m + 2 + i) (m + 2 - i) a)             (fun i => brk2 (2 * m + 1 - (m - 1 - i)) ((m - 1 - i) + 3) a)).
    intros i Hi. apply NatLe_drop in Hi.
    apply qeq_imp_qeqT.
    assert (Ha : (2 * m + 1 - (m - 1 - i) = m + 2 + i)%nat) by lia.
    assert (Hb : ((m - 1 - i) + 3 = m + 2 - i)%nat) by lia.
    rewrite Ha, Hb. reflexivity. }
  assert (H2 : sum_upto m (fun i => brk2 (m + 2 + i) (m + 2 - i) a) ==
               sum_upto m (fun i => brk2 (2 * m + 1 - i) (i + 3) a)).
  { rewrite (qeqT_imp_qeq _ _ (sum_upto_rev m (fun i => brk2 (2 * m + 1 - i) (i + 3) a))) in Htmp2.
    exact Htmp2. }
  (* Recombine: the left side is already in the split form of [sum_upto_plus], so rewrite directly with [H1] and [H2]. *)
  rewrite H1. rewrite H2.
  reflexivity.
Qed.

(* Unified pairing for [c1]: the first column (indexed by j, i.e. the S j column) == the second column
   + C(j) - brk2 (m+1) (S j).
   For j <= 1 use [c1_col_lo_shift] (C = brk2 (2m+1) (S j)); for 2 <= j <= m use [c1_col_mid]
   (C = the two supplementary terms). *)
Lemma c1_col_uni : forall (m j : nat) (a : Q), (1 <= m)%nat -> (j <= m)%nat ->QeqT (
  sum_upto (Nat.min (m - 1) (m + 2 - Datatypes.S j) + 1) (fun i => brk2 (m + 2 + i) (Datatypes.S j) a) ) (
  sum_upto (Nat.min (m - 1) (m + 1 - Datatypes.S j) + 1) (fun i => brk2 (m + 1 + i) (Datatypes.S j) a) +
  (if Nat.leb j 1 then brk2 (2 * m + 1) (Datatypes.S j) a
   else brk2 (2 * m + 3 - Datatypes.S j) (Datatypes.S j) a + brk2 (2 * m + 4 - Datatypes.S j) (Datatypes.S j) a) -
  brk2 (m + 1) (Datatypes.S j) a).
Proof.
  intros m j a Hm Hjm.
  apply qeq_imp_qeqT.
  assert (Hle1 : (j <= 1)%nat \/ (2 <= j)%nat) by lia.
  destruct Hle1 as [Hj1 | Hj2].
  - (* Case j <= 1: apply [c1_col_lo_shift]; the if-branch is true ([Nat.leb_le]). *)
    assert (Hleb : Nat.leb j 1 = true) by (apply Nat.leb_le; exact Hj1).
    rewrite Hleb.
    apply qeqT_imp_qeq.
    apply (c1_col_lo_shift m j a Hj1 Hm).
  - (* Case 2 <= j: apply [c1_col_mid]; the if-branch is false ([Nat.leb_gt]). The goal is
        G + (b1+b2) - b3 while [c1_col_mid] delivers (G+b1)+b2−b3, so reassociate with
        [Qplus_assoc] (addition on Q is not definitionally associative, so this is explicit). *)
    assert (Hleb : Nat.leb j 1 = false) by (apply Nat.leb_gt; lia).
    rewrite Hleb.
    setoid_rewrite (Qplus_assoc
             (sum_upto (Nat.min (m - 1) (m + 1 - Datatypes.S j) + 1)
                       (fun i => brk2 (m + 1 + i) (Datatypes.S j) a))
             (brk2 (2 * m + 3 - Datatypes.S j) (Datatypes.S j) a)
             (brk2 (2 * m + 4 - Datatypes.S j) (Datatypes.S j) a)).
    apply qeqT_imp_qeq.
    apply (c1_col_mid m j a Hj2 Hjm Hm).
Qed.

(* Assembling the supplementary part of [c1]: the segment-1b supplementary sum over 2 <= j <= m,
   together with brk2 (2m+1) 2 (segment 1a at j = 1) and brk2 (m+2) (m+2) (segment 2),
   equals the supplementary row. Under the substitution S = j+1 this matches the right side
   of [supp_col] (the sums over 2 <= S <= m+1 and 3 <= S <= m+2). *)
Lemma c1_assembly : forall (m : nat) (a : Q), (1 <= m)%nat ->QeqT (
  sum_upto (m - 1) (fun i => brk2 (2 * m - i) (i + 3) a + brk2 (2 * m + 1 - i) (i + 3) a) +
  brk2 (2 * m + 1) 2 a + brk2 (m + 2) (m + 2) a ) (
  sum_upto m (fun i => brk2 (m + 2 + i) (m + 1 - i) a + brk2 (m + 2 + i) (m + 2 - i) a)).
Proof.
  intros m a Hm.
  apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (supp_col m a)).
  (* Goal: S0 + brk2(2m+1) 2 + brk2(m+2)(m+2) == S1 + S2.
     Peel the head term off S1: brk2(2m+1) 2 + the sum of brk2(2m−i)(i+3) for i < m−1
     (by [sum_upto_add 1 (m−1)]); peel the tail term off S2: the sum of brk2(2m+1−i)(i+3)
     for i < m−1 + brk2(m+2)(m+2) (by the definition at S(m−1)). *)
  assert (H1 : sum_upto m (fun i => brk2 (2 * m + 1 - i) (i + 2) a) ==
               brk2 (2 * m + 1) 2 a +
               sum_upto (m - 1) (fun i => brk2 (2 * m - i) (i + 3) a)).
  { assert (Hup : (1 + (m - 1) = m)%nat) by lia.
    rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq m (1 + (m - 1))                 (fun i => brk2 (2 * m + 1 - i) (i + 2) a) (eq_sym Hup))).
    setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_add 1 (m - 1)                 (fun i => brk2 (2 * m + 1 - i) (i + 2) a))).
    assert (Hpre1538_41 : (forall i : nat, NatLe (Datatypes.S i) (m - 1) ->QeqT ( (fun i => brk2 (2 * m + 1 - (1 + i)) (1 + i + 2) a) i ) ( (fun i => brk2 (2 * m - i) (i + 3) a) i))).
    {  intros i Hi. apply NatLe_drop in Hi.
         apply qeq_imp_qeqT.
         assert (Ha : (2 * m + 1 - (1 + i) = 2 * m - i)%nat) by lia.
         assert (Hb : (1 + i + 2 = i + 3)%nat) by lia.
         rewrite Ha, Hb. reflexivity. }
    rewrite (qeqT_imp_qeq _ _ (sum_upto_ext_below (m - 1)               (fun i => brk2 (2 * m + 1 - (1 + i)) (1 + i + 2) a)               (fun i => brk2 (2 * m - i) (i + 3) a) Hpre1538_41)).
    assert (Hsu : sum_upto 1 (fun i : nat => brk2 (2 * m + 1 - i) (i + 2) a) ==
                 brk2 (2 * m + 1) 2 a).
    { change (sum_upto 1 (fun i : nat => brk2 (2 * m + 1 - i) (i + 2) a)) with
        (sum_upto 0 (fun i : nat => brk2 (2 * m + 1 - i) (i + 2) a) +
         brk2 (2 * m + 1 - 0) (0 + 2) a).
      assert (Hnat1 : (2 * m + 1 - 0 = 2 * m + 1)%nat) by lia.
      assert (Hnat2 : (0 + 2 = 2)%nat) by lia.
      setoid_rewrite Hnat1. setoid_rewrite Hnat2.
      simpl. ring. }
    rewrite Hsu. reflexivity. }
  assert (H2 : sum_upto m (fun i => brk2 (2 * m + 1 - i) (i + 3) a) ==
               sum_upto (m - 1) (fun i => brk2 (2 * m + 1 - i) (i + 3) a) +
               brk2 (m + 2) (m + 2) a).
  { assert (Hsm : (m = Datatypes.S (m - 1))%nat) by lia.
    rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq m (Datatypes.S (m - 1))               (fun i => brk2 (2 * m + 1 - i) (i + 3) a) Hsm)).
    change (sum_upto (Datatypes.S (m - 1)) (fun i => brk2 (2 * m + 1 - i) (i + 3) a)) with
      (sum_upto (m - 1) (fun i => brk2 (2 * m + 1 - i) (i + 3) a) +
       brk2 (2 * m + 1 - (m - 1)) ((m - 1) + 3) a).
    assert (Hk : (2 * m + 1 - (m - 1) = m + 2)%nat) by lia.
    assert (Hj : ((m - 1) + 3 = m + 2)%nat) by lia.
    rewrite Hk, Hj.
    reflexivity. }
  rewrite H1. rewrite H2.
  (* Goal: S0 + brk2(2m+1) 2 + brk2(m+2)(m+2) ==
           [brk2(2m+1) 2 + S0a] + [S0b + brk2(m+2)(m+2)]; close by [ring]
           (S0 = S0a + S0b via [sum_upto_plus]). *)
  setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_plus (m - 1)                   (fun i => brk2 (2 * m - i) (i + 3) a)                   (fun i => brk2 (2 * m + 1 - i) (i + 3) a))).
  ring.
Qed.

(* Final rearrangement for [c1]: X + (B1+B2+S0) - Q + B3 - X == B1 + (B2 + (S0 + B3)) - Q (pure variable [ring]). *)
Lemma c1_final : forall (X B1 B2 S0 B3 Q : Q),QeqT (
  X + (B1 + B2 + S0) - Q + B3 - X ) ( B1 + (B2 + (S0 + B3)) - Q).
Proof. intros. apply qeq_imp_qeqT. ring. Qed.

(* Simplified final rearrangement: X + A - Q + C - X == A + C - Q (A is an atomic argument and the two occurrences of X cancel). *)
Lemma c1_final2 : forall (X A Q C : Q),QeqT (
  X + A - Q + C - X ) ( A + C - Q).
Proof. intros. apply qeq_imp_qeqT. ring. Qed.

(* Fully expanded final rearrangement: X + B1 + B2 + S0 - Q + C - X == B1 + B2 + S0 + C - Q.
   The goal's left side is a left-associative chain (X + B1 + B2 + S0), not of the form X + (A),
   so each term must be listed. *)
Lemma c1_final3 : forall (X B1 B2 S0 Q C : Q),QeqT (
  X + B1 + B2 + S0 - Q + C - X ) ( B1 + B2 + S0 + C - Q).
Proof. intros. apply qeq_imp_qeqT. ring. Qed.

(* Associative final rearrangement: B1 + B2 + S0 + B3 - Q == B1 + (B2 + (S0 + B3)) - Q (matching the shape consumed by [c1_assembly2]). *)
Lemma c1_assoc3 : forall (B1 B2 S0 B3 Q : Q),QeqT (
  B1 + B2 + S0 + B3 - Q ) ( B1 + (B2 + (S0 + B3)) - Q).
Proof. intros. apply qeq_imp_qeqT. ring. Qed.

(* Associative variant of [c1_assembly]: B2 + (S0 + B3) == the supplementary row (matched by [setoid_rewrite]). *)
Lemma c1_assembly2 : forall (m : nat) (a : Q), (1 <= m)%nat ->QeqT (
  brk2 (2 * m + 1) 2 a +
  (sum_upto (m - 1) (fun i => brk2 (2 * m - i) (i + 3) a + brk2 (2 * m + 1 - i) (i + 3) a) +
   brk2 (m + 2) (m + 2) a) ) (
  sum_upto m (fun i => brk2 (m + 2 + i) (m + 1 - i) a + brk2 (m + 2 + i) (m + 2 - i) a)).
Proof.
  intros m a Hm.
  apply qeq_imp_qeqT.
  (* Turn B2 + (S0 + B3) into (S0 + B2) + B3 ([Qplus_assoc] plus [Qplus_comm]), then rewrite with [c1_assembly]. *)
  setoid_rewrite (Qplus_assoc (brk2 (2 * m + 1) 2 a)
                     (sum_upto (m - 1) (fun i => brk2 (2 * m - i) (i + 3) a + brk2 (2 * m + 1 - i) (i + 3) a))
                     (brk2 (m + 2) (m + 2) a)).
  setoid_rewrite (Qplus_comm (brk2 (2 * m + 1) 2 a)
                     (sum_upto (m - 1) (fun i => brk2 (2 * m - i) (i + 3) a + brk2 (2 * m + 1 - i) (i + 3) a))).
  rewrite (qeqT_imp_qeq _ _ (c1_assembly m a Hm)).
  ring.
Qed.

(* The key identity [c1]: ksum_diff (S m) m == the supplementary sum - inner2 (m+1)(m+1) + inner2 (2m+1) 1 (the core of the induction step of [ksum_diff_row]). *)
Lemma c1 : forall (a : Q) (m : nat),
  (1 <= m)%nat ->QeqT (
  ksum_diff (Datatypes.S m) m a ) (
  sum_upto m (fun i => brk2 (m + 2 + i) (m + 1 - i) a + brk2 (m + 2 + i) (m + 2 - i) a) -
  inner2 (m + 1) (m + 1) a + inner2 (2 * m + 1) 1 a).
Proof.
  intros a m Hm.
  apply qeq_imp_qeqT.
  (* Left side: [ksum_diff_sum_upto] turns the skew-diagonal accumulation into a bounded sum. *)
  rewrite (qeqT_imp_qeq _ _ (ksum_diff_sum_upto m m a)).
  (* Expand the inner sums with [inner2_sum_upto], transported pointwise by [sum_upto_ext_below]. *)
  assert (Hpre1538_40 : (forall i : nat, NatLe (Datatypes.S i) m ->QeqT ( (fun k' => inner2 (m + 2 + k') (m + 2 - k') a - inner2 (m + 1 + k') (m + 1 - k') a) i ) ( (fun k' => sum_upto (m + 2 - k') (fun j => brk2 (m + 2 + k') (Datatypes.S j) a) -                      sum_upto (m + 1 - k') (fun j => brk2 (m + 1 + k') (Datatypes.S j) a)) i))).
  {  intros k' Hk'. apply NatLe_drop in Hk'.
       apply qeq_imp_qeqT.
       setoid_rewrite (qeqT_imp_qeq _ _ (inner2_sum_upto (m + 2 + k') (m + 2 - k') a)).
       setoid_rewrite (qeqT_imp_qeq _ _ (inner2_sum_upto (m + 1 + k') (m + 1 - k') a)).
       reflexivity. }
  rewrite (qeqT_imp_qeq _ _ (sum_upto_ext_below m           (fun k' => inner2 (m + 2 + k') (m + 2 - k') a - inner2 (m + 1 + k') (m + 1 - k') a)
           (fun k' => sum_upto (m + 2 - k') (fun j => brk2 (m + 2 + k') (Datatypes.S j) a) -                      sum_upto (m + 1 - k') (fun j => brk2 (m + 1 + k') (Datatypes.S j) a)) Hpre1538_40)).
  rewrite (qeqT_imp_qeq _ _ (sum_upto_minus m           (fun k' => sum_upto (m + 2 - k') (fun j => brk2 (m + 2 + k') (Datatypes.S j) a))           (fun k' => sum_upto (m + 1 - k') (fun j => brk2 (m + 1 + k') (Datatypes.S j) a)))).
  assert (Hle2 : (m <= m + 2)%nat) by lia.
  assert (Hle1 : (m <= m + 1)%nat) by lia.
  rewrite (qeqT_imp_qeq _ _ (sum_upto_tri_swap_min m (m + 2) (fun i j => brk2 (m + 2 + i) j a) Hm Hle2)).
  rewrite (qeqT_imp_qeq _ _ (sum_upto_tri_swap_min m (m + 1) (fun i j => brk2 (m + 1 + i) j a) Hm Hle1)).
  setoid_rewrite (qeqT_imp_qeq _ _ (inner2_sum_upto (m + 1) (m + 1) a)).
  setoid_rewrite (qeqT_imp_qeq _ _ (inner2_sum_upto (2 * m + 1) 1 a)).
  (* Goal after the swaps:
     the sum of F1 j over 0 <= j <= m+1 minus the sum of F2 j over 0 <= j <= m ==
     the supplementary row - the sum of brk2 (m+1)(S j) over 0 <= j <= m + brk2 (2m+1) 1,
     where F1 j = sum_upto (min (m−1)(m+2−S j)+1) (brk2 (m+2+i)(S j)) and
     F2 j = sum_upto (min (m−1)(m+1−S j)+1) (brk2 (m+1+i)(S j)). *)
  (* Split sum_upto (m+2) F1 = sum_upto (m+1) F1 + F1 (m+1) (since m+2 == S (m+1)). *)
  assert (Hsu : (m + 2 = Datatypes.S (m + 1))%nat) by lia.
  rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq (m + 2) (Datatypes.S (m + 1))            (fun j => sum_upto (Nat.min (m - 1) (m + 2 - Datatypes.S j) + 1)                              (fun i => brk2 (m + 2 + i) (Datatypes.S j) a)) Hsu)).
  change (sum_upto (Datatypes.S (m + 1))
            (fun j => sum_upto (Nat.min (m - 1) (m + 2 - Datatypes.S j) + 1)
                              (fun i => brk2 (m + 2 + i) (Datatypes.S j) a))) with
    (sum_upto (m + 1)
       (fun j => sum_upto (Nat.min (m - 1) (m + 2 - Datatypes.S j) + 1)
                         (fun i => brk2 (m + 2 + i) (Datatypes.S j) a)) +
     sum_upto (Nat.min (m - 1) (m + 2 - Datatypes.S (m + 1)) + 1)
              (fun i => brk2 (m + 2 + i) (Datatypes.S (m + 1)) a)).
  (* Tail term at j = m+1: [c1_col_hi] gives the first column == brk2 (m+2)(m+2). *)
  setoid_rewrite (qeqT_imp_qeq _ _ (c1_col_hi m a Hm)).
  (* For the sum of F1 j over j < m+1: apply [c1_col_uni] pointwise (j <= m follows from j < m+1), transported by [sum_upto_ext_below]. *)
  assert (Hpre1538_39 : (forall i : nat, NatLe (Datatypes.S i) (m + 1) ->QeqT ( (fun j => sum_upto (Nat.min (m - 1) (m + 2 - Datatypes.S j) + 1) (fun i => brk2 (m + 2 + i) (Datatypes.S j) a)) i ) ( (fun j => sum_upto (Nat.min (m - 1) (m + 1 - Datatypes.S j) + 1) (fun i => brk2 (m + 1 + i) (Datatypes.S j) a) + (if Nat.leb j 1 then brk2 (2 * m + 1) (Datatypes.S j) a else brk2 (2 * m + 3 - Datatypes.S j) (Datatypes.S j) a + brk2 (2 * m + 4 - Datatypes.S j) (Datatypes.S j) a) -               brk2 (m + 1) (Datatypes.S j) a) i))).
  {  intros j Hj. apply NatLe_drop in Hj. apply qeq_imp_qeqT. apply qeqT_imp_qeq. apply (c1_col_uni m j a Hm). lia. }
  rewrite (qeqT_imp_qeq _ _ (sum_upto_ext_below (m + 1)            (fun j => sum_upto (Nat.min (m - 1) (m + 2 - Datatypes.S j) + 1)
                              (fun i => brk2 (m + 2 + i) (Datatypes.S j) a))
            (fun j =>
               sum_upto (Nat.min (m - 1) (m + 1 - Datatypes.S j) + 1)
                        (fun i => brk2 (m + 1 + i) (Datatypes.S j) a) +
               (if Nat.leb j 1 then brk2 (2 * m + 1) (Datatypes.S j) a
                else brk2 (2 * m + 3 - Datatypes.S j) (Datatypes.S j) a +
                     brk2 (2 * m + 4 - Datatypes.S j) (Datatypes.S j) a) -               brk2 (m + 1) (Datatypes.S j) a) Hpre1538_39)).
  (* Split the sum of (F2 + C - Q) with [sum_upto_minus] and [sum_upto_plus]. *)
  rewrite (qeqT_imp_qeq _ _ (sum_upto_minus (m + 1)            (fun j =>
               sum_upto (Nat.min (m - 1) (m + 1 - Datatypes.S j) + 1)
                        (fun i => brk2 (m + 1 + i) (Datatypes.S j) a) +
               (if Nat.leb j 1 then brk2 (2 * m + 1) (Datatypes.S j) a
                else brk2 (2 * m + 3 - Datatypes.S j) (Datatypes.S j) a +
                     brk2 (2 * m + 4 - Datatypes.S j) (Datatypes.S j) a))            (fun j => brk2 (m + 1) (Datatypes.S j) a))).
  rewrite (qeqT_imp_qeq _ _ (sum_upto_plus (m + 1)            (fun j => sum_upto (Nat.min (m - 1) (m + 1 - Datatypes.S j) + 1)
                              (fun i => brk2 (m + 1 + i) (Datatypes.S j) a))
            (fun j => if Nat.leb j 1 then brk2 (2 * m + 1) (Datatypes.S j) a
                      else brk2 (2 * m + 3 - Datatypes.S j) (Datatypes.S j) a +                           brk2 (2 * m + 4 - Datatypes.S j) (Datatypes.S j) a))).
  (* Goal: the sum of F2 + the sum of C - the sum of Q + brk2 (m+2)(m+2) - the sum of F2 ==
     the supplementary row - the sum of Q + brk2 (2m+1) 1.
     Split the sum of C into sum_upto 2 + sum_upto (m−1) (since 2+(m−1) = m+1). *)
  assert (HaddC : (2 + (m - 1) = m + 1)%nat) by lia.
  rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq (m + 1) (2 + (m - 1))            (fun j => if Nat.leb j 1 then brk2 (2 * m + 1) (Datatypes.S j) a
                      else brk2 (2 * m + 3 - Datatypes.S j) (Datatypes.S j) a +                           brk2 (2 * m + 4 - Datatypes.S j) (Datatypes.S j) a) (eq_sym HaddC))).
  setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_add 2 (m - 1)            (fun j => if Nat.leb j 1 then brk2 (2 * m + 1) (Datatypes.S j) a
                      else brk2 (2 * m + 3 - Datatypes.S j) (Datatypes.S j) a +                           brk2 (2 * m + 4 - Datatypes.S j) (Datatypes.S j) a))).
  (* sum_upto 2 C == brk2 (2m+1) 1 + brk2 (2m+1) 2 *)
  assert (Hc2 : sum_upto 2
                  (fun j => if Nat.leb j 1 then brk2 (2 * m + 1) (Datatypes.S j) a
                            else brk2 (2 * m + 3 - Datatypes.S j) (Datatypes.S j) a +
                                 brk2 (2 * m + 4 - Datatypes.S j) (Datatypes.S j) a) ==
               brk2 (2 * m + 1) 1 a + brk2 (2 * m + 1) 2 a).
  { simpl. ring. }
  rewrite Hc2.
  (* For the sum of C (2+j) over j < m−1: reduce with [sum_upto_ext_below] (leb (2+j) 1 = false, S(2+j) = 3+j, 2m+3−S(2+j) = 2m−j). *)
  assert (Hpre1538_100 : (forall i : nat, NatLe (Datatypes.S i) (m - 1) ->QeqT ( (fun j => if Nat.leb (2 + j) 1 then brk2 (2 * m + 1) (Datatypes.S (2 + j)) a else brk2 (2 * m + 3 - Datatypes.S (2 + j)) (Datatypes.S (2 + j)) a + brk2 (2 * m + 4 - Datatypes.S (2 + j)) (Datatypes.S (2 + j)) a) i ) ( (fun j => brk2 (2 * m - j) (j + 3) a + brk2 (2 * m + 1 - j) (j + 3) a) i))).
  {  intros j Hj. apply NatLe_drop in Hj.
  apply qeq_imp_qeqT.
       assert (Hleb : Nat.leb (2 + j) 1 = false) by (apply Nat.leb_gt; lia).
       rewrite Hleb.
       assert (Hs1 : (Datatypes.S (2 + j) = 3 + j)%nat) by lia.
        rewrite Hs1.
        assert (Hsw : (3 + j = j + 3)%nat) by lia.
        rewrite Hsw.
        assert (Ha : (2 * m + 3 - (j + 3) = 2 * m - j)%nat) by lia.
       assert (Hb : (2 * m + 4 - (j + 3) = 2 * m + 1 - j)%nat) by lia.
       rewrite Ha, Hb. reflexivity. }
  rewrite (qeqT_imp_qeq _ _ (sum_upto_ext_below (m - 1) (fun j => if Nat.leb (2 + j) 1 then brk2 (2 * m + 1) (Datatypes.S (2 + j)) a else brk2 (2 * m + 3 - Datatypes.S (2 + j)) (Datatypes.S (2 + j)) a + brk2 (2 * m + 4 - Datatypes.S (2 + j)) (Datatypes.S (2 + j)) a) (fun j => brk2 (2 * m - j) (j + 3) a + brk2 (2 * m + 1 - j) (j + 3) a) Hpre1538_100)).
  (* Goal: the sum of F2 + [brk2(2m+1) 1 + brk2(2m+1) 2 + S0] - the sum of Q + brk2 (m+2)(m+2) - the sum of F2 ==
     the supplementary row - the sum of Q + the one-term sum of brk2(2m+1)(S j).
     Rearrange with [c1_final] (the sums of F2 and Q cancel), then [c1_assembly2]
     (B2+(S0+B3) == the supplementary row) and [ring]. *)
  assert (Hone : sum_upto 1 (fun j => brk2 (2 * m + 1) (Datatypes.S j) a) ==
                 brk2 (2 * m + 1) 1 a).
  { change (sum_upto 1 (fun j => brk2 (2 * m + 1) (Datatypes.S j) a)) with
      (sum_upto 0 (fun j => brk2 (2 * m + 1) (Datatypes.S j) a) +
       brk2 (2 * m + 1) (Datatypes.S 0) a).
    change (brk2 (2 * m + 1) (Datatypes.S 0) a) with (brk2 (2 * m + 1) 1 a).
    simpl. ring. }
  setoid_rewrite Hone.
  (* Goal: the sum of F2 + (B1+B2+S0) - the sum of Q + B3 - the sum of F2 == the supplementary row - the sum of Q + B1.
     Assert the intermediate equality (cancelling the sum of F2 with [c1_final2]), then rewrite. *)
  assert (Hx : (sum_upto (m + 1)
                  (fun j => sum_upto (Nat.min (m - 1) (m + 1 - Datatypes.S j) + 1)
                                    (fun i => brk2 (m + 1 + i) (Datatypes.S j) a)) +
                (brk2 (2 * m + 1) 1 a + brk2 (2 * m + 1) 2 a +
                 sum_upto (m - 1) (fun j => brk2 (2 * m - j) (j + 3) a + brk2 (2 * m + 1 - j) (j + 3) a)) -
                sum_upto (m + 1) (fun j => brk2 (m + 1) (Datatypes.S j) a) +
                brk2 (m + 2) (m + 2) a -
                sum_upto (m + 1)
                  (fun j => sum_upto (Nat.min (m - 1) (m + 1 - Datatypes.S j) + 1)
                                    (fun i => brk2 (m + 1 + i) (Datatypes.S j) a))) ==
              (brk2 (2 * m + 1) 1 a + brk2 (2 * m + 1) 2 a +
               sum_upto (m - 1) (fun j => brk2 (2 * m - j) (j + 3) a + brk2 (2 * m + 1 - j) (j + 3) a)) +
              brk2 (m + 2) (m + 2) a -
              sum_upto (m + 1) (fun j => brk2 (m + 1) (Datatypes.S j) a)).
  { apply (qeqT_imp_qeq _ _ (c1_final2             (sum_upto (m + 1)
                (fun j => sum_upto (Nat.min (m - 1) (m + 1 - Datatypes.S j) + 1)
                                  (fun i => brk2 (m + 1 + i) (Datatypes.S j) a)))
             (brk2 (2 * m + 1) 1 a + brk2 (2 * m + 1) 2 a +
              sum_upto (m - 1) (fun j => brk2 (2 * m - j) (j + 3) a + brk2 (2 * m + 1 - j) (j + 3) a))
             (sum_upto (m + 1) (fun j => brk2 (m + 1) (Datatypes.S j) a))             (brk2 (m + 2) (m + 2) a))). }
  (* Intermediate form for transitivity: the left side == (B1+B2+S0) + B3 - the sum of Q (by [Hx]) == the supplementary row - the sum of Q + B1. *)
  transitivity ((brk2 (2 * m + 1) 1 a + brk2 (2 * m + 1) 2 a +
                 sum_upto (m - 1) (fun j => brk2 (2 * m - j) (j + 3) a + brk2 (2 * m + 1 - j) (j + 3) a)) +
                brk2 (m + 2) (m + 2) a -
                sum_upto (m + 1) (fun j => brk2 (m + 1) (Datatypes.S j) a)).
  - (* Left side == intermediate form: exactly [Hx]. *)
    exact Hx.
  - (* Intermediate form == right side: B1 + (B2+(S0+B3)) - the sum of Q == the supplementary row - the sum of Q + B1,
       by rearranging with [c1_assoc3] in reverse, then [c1_assembly2] and [ring]. *)
    setoid_rewrite (qeqT_imp_qeq _ _ (c1_assoc3              (brk2 (2 * m + 1) 1 a)
              (brk2 (2 * m + 1) 2 a)
              (sum_upto (m - 1) (fun j => brk2 (2 * m - j) (j + 3) a + brk2 (2 * m + 1 - j) (j + 3) a))
              (brk2 (m + 2) (m + 2) a)              (sum_upto (m + 1) (fun j => brk2 (m + 1) (Datatypes.S j) a)))).
    setoid_rewrite (qeqT_imp_qeq _ _ (c1_assembly2 m a Hm)).
    ring.
Qed.

(* ============ The main identity [esq_eq_corr] ============
   esq_eq_corr : forall (a : Q) (m : nat),
     e_sum m a * e_sum m a - o_sum m a * o_sum m a == 1 + corr m a.

   Numeric verification at a = 1: for m = 2, E = 37/24, O = 7/6, E^2−O^2 = 65/64, corr = 1/64;
   for m = 3, E^2−O^2 = 103721/103680 = 1 + corr.

   Equivalent form (via [e_o_split_even]/[e_o_split_pos]):
     S_(2m)(−a) * S_(2m)(a) == 1 + corr m a   (because E−O = S(−a) and E+O = S(a)),
   so corr >= 0 ([corr_nonneg]) gives S_(2m)(−a) * S_(2m)(a) >= 1 > 0,
   hence S_(2m)(−a) >= 0 ([exp_even_neg_nonneg], chaining to [exp_partial_tail_pos]
   and [cauchy_real_exp_pos]).

   Proof routes:
   Route A, diagonal coefficient matching: E^2 == the double sum over i, j <= m of
     a^(2i+2j)/((2i)!(2j)!), O^2 == the double sum over i, j <= m−1 of a^(2i+2j+2)/((2i+1)!(2j+1)!)
     (via the Fixpoint double sums [esq_sum]/[osq_sum] and their expansion lemmas);
     the coefficient of a^(2n) is 0 for n <= m — exactly the even/odd split of [altf_zero (2n)]
     (altf (2n) == the even sum minus the odd sum == 0), while for n >= m+1 it is
     2 * the sum over m <= k <= n−1 of [1/((2k+1)!(2n−2k−1)!) - 1/((2k+2)!(2n−2k−2)!)], matching the
     brk2 structure of [corr] term by term (the k+j = n diagonal regrouping of [kloop]);
     the (k,j) -> n = k+j diagonal rearrangement of [corr] is the same sum, so the two sides agree.
     The key point: [altf_zero] is exactly the expansion of (1−1)^N == 0, and its even/odd split
     directly yields the equality of the even and odd sums — the binomial core needed here,
     with no additional binomial theorem.
   Route B, successor recurrence: corr (S m) == corr m + Δ' with
     Δ' = 2*E_m*T_e + T_e^2 - 2*O_m*T_o - T_o^2 (T_e = a^(2m+2)/(2m+2)!,
     T_o = a^(2m+1)/(2m+1)!), matching the increment of [esq_succ]; then
     corr (S m) − corr m = the difference of the two inner2 sums, expanded term by term
     ([inner2_succ] plus the brk2 expansion) and matched against Δ'.
     Route A is taken (with [altf_zero] already available and a cleaner structure). *)

(* All prerequisites are proved above: the infrastructure, the [corr] structure, its
   nonnegativity, [altf_zero] and [esq_succ]; the main identity [esq_eq_corr] follows by
   route A, diagonal coefficient matching. *)

(* ===== Supporting lemmas of the Vandermonde layer of the pairing argument ===== *)
(* At the Q level, 2 * (1/x) == 2/x ([Qdiv] unfolding plus [ring]); used to cancel the E_0/O_0 terms. *)
Lemma q_div_scale2 : forall (x : Q),QeqT ( 2 * (1 / x) ) ( 2 / x).
Proof.
  intro x. apply qeq_imp_qeqT. unfold Qdiv. ring.
Qed.

(* Generic transposition for [Qeq]: SE + Em - SO - Om == 0 implies SO - SE == Em - Om.
   (Negate with [Qopp_comp], then transitivity plus [ring]; this avoids syntactic matching of Hz.) *)
Lemma qeq_moved : forall (SE SO Em Om : Q),QeqT (
  SE + Em - SO - Om ) ( 0 )->QeqT ( SO - SE ) ( Em - Om).
Proof.
  intros SE SO Em Om H.
  apply qeq_imp_qeqT.
  assert (Hdiff : (SO - SE) - (Em - Om) == 0).
  { transitivity (- (SE + Em - SO - Om)).
    - ring.
    - assert (Hopp : - (SE + Em - SO - Om) == - 0).
      { apply (Qopp_comp (SE + Em - SO - Om) 0 (qeqT_imp_qeq _ _ H)). }
      rewrite <- Hopp.
      ring. }
  transitivity ((SO - SE) - (Em - Om) + (Em - Om)).
  - ring.
  - rewrite Hdiff. ring.
Qed.

(* Transposition variant: A + B + (-C) == 0 implies C - A == B (matching the shape 2*ΣE + Em + 2*(-ΣO) == 0 of Hz). *)
Lemma qeq_moved_neg : forall (A B C : Q),QeqT (
  A + B + (- C) ) ( 0 )->QeqT ( C - A ) ( B).
Proof.
  intros A B C H.
  apply qeq_imp_qeqT.
  (* From H : A + B + (-C) == 0, negation gives -(A + B + (-C)) == 0 by [Qopp_comp];
     and C - A - B == -(A + B + (-C)) is a [ring] identity. *)
  assert (Hdiff : (C - A) - B == 0).
  { transitivity (- (A + B + (- C))).
    - ring.
    - assert (Hopp : - (A + B + (- C)) == - 0).
      { apply (Qopp_comp (A + B + (- C)) 0 (qeqT_imp_qeq _ _ H)). }
      rewrite <- Hopp.
      ring. }
(* From (C-A) - B == 0, adding B to both sides gives C - A == B. *)
  transitivity ((C - A) - B + B).
  - ring.
  - rewrite Hdiff. ring.
Qed.

(* Transposition variant 2: A + B + 2*(-C) == 0 implies 2C - A == B (matching the shape
   2*ΣE + Em + 2*(-ΣO) == 0 of Hz). Apply [qeq_moved_neg] to (A, B, 2C): the premise
   A + B + (-(2C)) == 0 follows from the assumed premise by [ring] (2*(-C) == -(2*C)). *)
Lemma qeq_moved_neg2 : forall (A B C : Q),QeqT (
  A + B + 2 * (- C) ) ( 0 )->QeqT ( 2 * C - A ) ( B).
Proof.
  intros A B C H.
  apply (qeq_moved_neg A B (2 * C)).
  apply qeq_imp_qeqT.
  (* It remains to show A + B + (-(2*C)) == 0, which follows from H (A + B + 2*(-C) == 0) by [ring]. *)
  rewrite <- (qeqT_imp_qeq _ _ H).
  ring.
Qed.

(* Shift for [sum_upto]: the sum of f (j+1) over j < n == the sum of f j over j <= n - f 0
   (first term peeled off, the converse direction of [sum_upto_rot]).
   Since sum_upto (S n) f == f 0 + sum_upto n (fun j => f (S j)) by [sum_upto_rot],
   transposing gives the claim. *)
Lemma sum_upto_shift : forall (n : nat) (f : nat -> Q),QeqT (
  sum_upto n (fun j => f (j + 1)%nat) ) ( sum_upto (n + 1) f - f 0%nat).
Proof.
  intros n f.
  apply qeq_imp_qeqT.
  assert (Hn : (n + 1 = Datatypes.S n)%nat) by lia.
  rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq (n + 1)%nat (Datatypes.S n) f Hn)).
  rewrite (qeqT_imp_qeq _ _ (sum_upto_rot n f)).
  assert (Hpre1538_38 : (forall i,QeqT ( (fun j => f (j + 1)%nat) i ) ( (fun j => f (Datatypes.S j)) i))).
  {  intro j. apply qeq_imp_qeqT. assert (Hj : (j + 1 = Datatypes.S j)%nat) by lia. rewrite Hj. reflexivity. }
  rewrite (qeqT_imp_qeq _ _ (sum_upto_ext n (fun j => f (j + 1)%nat) (fun j => f (Datatypes.S j)) Hpre1538_38)).
  unfold Qminus. ring.
Qed.

(* Scalar linearity of [sum_upto]: the sum of (c*f) == c * the sum of f, by induction with [simpl] plus [ring]. *)
Lemma sum_upto_scale : forall (n : nat) (c : Q) (f : nat -> Q),QeqT (
  sum_upto n (fun j => c * f j) ) ( c * sum_upto n f).
Proof.
  intros n. induction n as [| n' IH]; intros c f; simpl.
  - apply qeq_imp_qeqT. ring.
  - apply qeq_imp_qeqT. setoid_rewrite (qeqT_imp_qeq _ _ (IH c f)). ring.
Qed.

(* Scalar linearity with the coefficient -2: the sum of (-2*f) == -2 * the sum of f. *)
Lemma sum_upto_scale_neg2 : forall (n : nat) (f : nat -> Q),QeqT (
  sum_upto n (fun j => - 2 * f j) ) ( - 2 * sum_upto n f).
Proof.
  intros n f.
  apply qeq_imp_qeqT.
  setoid_rewrite <- (qeqT_imp_qeq _ _ (sum_upto_scale n (- 2) f)).
  reflexivity.
Qed.

(* ============ Third step of the pairing argument: the Vandermonde identities ([vander_4m2] / [vander_4m4]) ============ *)
(* Any power of 1 is 1: q_pow 1 n == 1. *)
Lemma q_pow_one : forall n,QeqT ( q_pow 1 n ) ( 1).
Proof.
  intro n. apply qeq_imp_qeqT. induction n as [| n' IH]; simpl.
  - reflexivity.
  - rewrite IH. ring.
Qed.

(* (−1)^(2n) == 1. *)
Lemma q_pow_neg1_even : forall n,QeqT ( q_pow (-1) (2 * n) ) ( 1).
Proof.
  intro n. apply qeq_imp_qeqT.
  exact (Qeq_trans _ _ _ (qeqT_imp_qeq _ _ (q_pow_neg_even 1 n)) (qeqT_imp_qeq _ _ (q_pow_one (2 * n)))).
Qed.

(* (−1)^(2n+1) == −1. *)
Lemma q_pow_neg1_odd : forall n,QeqT ( q_pow (-1) (2 * n + 1) ) ( -1).
Proof.
  intro n.
  apply qeq_imp_qeqT.
  assert (Hidx : (2 * n + 1 = Datatypes.S (2 * n))%nat) by lia.
  setoid_replace (q_pow (-1) (2 * n + 1)) with (q_pow (-1) (Datatypes.S (2 * n))).
  2: { apply (q_pow_comp_proper (-1) (-1) (Qeq_refl (-1)) (2 * n + 1)%nat (Datatypes.S (2 * n))%nat Hidx). }
  setoid_rewrite (qeqT_imp_qeq _ _ (q_pow_neg_odd 1 n)).
  setoid_rewrite (qeqT_imp_qeq _ _ (q_pow_one (Datatypes.S (2 * n)))).
  ring.
Qed.

(* Transporting [altf] to a bounded sum: altf N == the sum of q_pow (−1) u / (u!(N−u)!) for 0 <= u <= N. *)
Lemma altf_as_sum_upto : forall N,QeqT ( altf N ) (
  sum_upto (N + 1) (fun u => q_pow (-1) u / (q_fact u * q_fact (N - u)))).
Proof.
  intro N.
  apply qeq_imp_qeqT.
  (* First prove the general form: altf_aux N u == sum_upto (u+1) (fun t => q_pow (−1) t / (t!(N−t)!)), by induction on [u]. *)
  assert (Haux : forall u, altf_aux N u ==
                 sum_upto (u + 1) (fun t => q_pow (-1) t / (q_fact t * q_fact (N - t)))).
  { intro u. induction u as [| u' IH]; simpl.
    - (* Case u = 0: altf_aux N 0 == Qinv(q_fact N), and sum_upto 1 f == f 0 == 1/(0!(N−0)!). *)
      assert (Hs : sum_upto (0 + 1) (fun t : nat => q_pow (-1) t / (q_fact t * q_fact (N - t))) ==
                   q_pow (-1) 0 / (q_fact 0 * q_fact (N - 0))).
      { simpl. ring. }
      rewrite Hs.
      assert (H0 : (N - 0 = N)%nat) by lia.
      rewrite H0.
      simpl.
      unfold Qdiv.
      setoid_rewrite (Qmult_1_l (q_fact N)).
      ring.
    - (* Case u = S u': altf_aux N (S u') == altf_aux N u' + q_pow (−1) (S u')/((S u')!(N−S u')!). *)
      change (altf_aux N u' + q_pow (-1) (Datatypes.S u') / (q_fact (Datatypes.S u') * q_fact (N - Datatypes.S u')) ==
              sum_upto (Datatypes.S u' + 1) (fun t => q_pow (-1) t / (q_fact t * q_fact (N - t)))).
      assert (Hsu : (Datatypes.S u' + 1 = Datatypes.S (u' + 1))%nat) by lia.
      rewrite Hsu.
      change (sum_upto (Datatypes.S (u' + 1)) (fun t => q_pow (-1) t / (q_fact t * q_fact (N - t)))) with
        (sum_upto (u' + 1) (fun t => q_pow (-1) t / (q_fact t * q_fact (N - t))) +
         q_pow (-1) (u' + 1) / (q_fact (u' + 1) * q_fact (N - (u' + 1)))).
      setoid_rewrite IH.
      (* Tail term: q_pow (−1) (S u') versus q_pow (−1) (u'+1) — the shapes S u' and u'+1 are not definitionally equal, so align them with [lia]. *)
      assert (Hp : (u' + 1 = Datatypes.S u')%nat) by lia.
      setoid_replace (q_pow (-1) (u' + 1)) with (q_pow (-1) (Datatypes.S u')).
      2: { apply (q_pow_comp_proper (-1) (-1) (Qeq_refl (-1)) (u' + 1)%nat (Datatypes.S u')%nat Hp). }
      assert (Hf : (N - (u' + 1) = N - Datatypes.S u')%nat) by lia.
      setoid_replace (q_fact (N - (u' + 1))) with (q_fact (N - Datatypes.S u')).
      2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. lia. }
      assert (Hq : (u' + 1 = Datatypes.S u')%nat) by lia.
      setoid_replace (q_fact (u' + 1)) with (q_fact (Datatypes.S u')).
      2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. exact Hq. }
      ring. }
  (* altf N == altf_aux N N; the bound sum_upto (N+1) matches the shape at u = N. *)
  unfold altf.
  setoid_rewrite (Haux N).
  assert (Hn : (N + 1 = N + 1)%nat) by lia.
  reflexivity.
Qed.

(* Even/odd split of [sum_upto] (an even number of terms): the sum of f i over i < 2n == the sum of f (2j) plus the sum of f (2j+1), both over j < n. *)
Lemma sum_upto_even_split : forall (n : nat) (f : nat -> Q),QeqT (
  sum_upto (2 * n)%nat f ) (
  sum_upto n (fun j => f (2 * j)%nat) + sum_upto n (fun j => f (2 * j + 1)%nat)).
Proof.
  intros n. induction n as [| n' IH]; intros f.
  - (* Case n = 0: sum_upto 0 f == 0 + 0. *)
    apply qeq_imp_qeqT.
    simpl. ring.
  - (* 2*S n' == S(S(2n')), transported with [sum_upto_nat_eq] ([simpl] cannot reduce 2*S n' with the variable n'). *)
    apply qeq_imp_qeqT.
    assert (Hidx : (2 * Datatypes.S n' = Datatypes.S (Datatypes.S (2 * n')))%nat) by lia.
    rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq (2 * Datatypes.S n')%nat (Datatypes.S (Datatypes.S (2 * n'))) f Hidx)).
    (* Peel the left side layer by layer: sum_upto (S(S(2n'))) f == sum_upto (2n') f + f (2n') + f (S(2n')). *)
    change (sum_upto (Datatypes.S (Datatypes.S (2 * n'))) f) with
      (sum_upto (Datatypes.S (2 * n')) f + f (Datatypes.S (2 * n'))).
    change (sum_upto (Datatypes.S (2 * n')) f) with
      (sum_upto (2 * n')%nat f + f (2 * n')%nat).
    setoid_rewrite (qeqT_imp_qeq _ _ (IH f)).
    (* Right side: peel the tail terms off sum_upto (S n') with per-term [change]s (a single [change] on the large term is unreliable). *)
    change (sum_upto (Datatypes.S n') (fun j => f (2 * j)%nat)) with
      (sum_upto n' (fun j => f (2 * j)%nat) + f (2 * n')%nat).
    change (sum_upto (Datatypes.S n') (fun j => f (2 * j + 1)%nat)) with
      (sum_upto n' (fun j => f (2 * j + 1)%nat) + f (2 * n' + 1)%nat).
    (* Realign the tail term: f (S(2n')) == f (2n'+1) is not definitional, so rewrite explicitly via [lia]. *)
    assert (Ht : (Datatypes.S (2 * n') = 2 * n' + 1)%nat) by lia.
    rewrite Ht.
    ring.
Qed.

(* Even/odd split of [sum_upto] (an odd number of terms): the sum of f i over i <= 2n == the sum of f (2j) over j <= n plus the sum of f (2j+1) over j < n. *)
Lemma sum_upto_even_split_odd : forall (n : nat) (f : nat -> Q),QeqT (
  sum_upto (2 * n + 1)%nat f ) (
  sum_upto (n + 1)%nat (fun j => f (2 * j)%nat) + sum_upto n (fun j => f (2 * j + 1)%nat)).
Proof.
  intros n. induction n as [| n' IH]; intros f.
  - (* Case n = 0: sum_upto 1 f == f 0 == f 0 + 0. *)
    apply qeq_imp_qeqT.
    simpl. ring.
  - (* 2*S n'+1 == S(S(S(2n'))), transported with [sum_upto_nat_eq]. *)
    apply qeq_imp_qeqT.
    assert (Hidx : (2 * Datatypes.S n' + 1 = Datatypes.S (Datatypes.S (Datatypes.S (2 * n'))))%nat) by lia.
    rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq (2 * Datatypes.S n' + 1)%nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * n')))) f Hidx)).
    (* Peel the left side layer by layer: sum_upto (2n'+3) f == sum_upto (2n'+1) f + f (2n'+1) + f (2n'+2). *)
    change (sum_upto (Datatypes.S (Datatypes.S (Datatypes.S (2 * n')))) f) with
      (sum_upto (Datatypes.S (Datatypes.S (2 * n'))) f + f (Datatypes.S (Datatypes.S (2 * n')))).
    change (sum_upto (Datatypes.S (Datatypes.S (2 * n'))) f) with
      (sum_upto (Datatypes.S (2 * n')) f + f (Datatypes.S (2 * n'))).
    (* Align sum_upto (S(2n')) f with the IH's sum_upto (2n'+1) f (not definitional; [lia] bridges). *)
    assert (Hsn : (2 * n' + 1 = Datatypes.S (2 * n'))%nat) by lia.
    rewrite <- (qeqT_imp_qeq _ _ (sum_upto_nat_eq (2 * n' + 1)%nat (Datatypes.S (2 * n')) f Hsn)).
    (* Apply the IH to sum_upto (2n'+1) f. *)
    setoid_rewrite (qeqT_imp_qeq _ _ (IH f)).
    (* Right side: peel tail terms one at a time; first unify S n'+1 == S(n'+1) by a [nat] identity, then [change] term by term. *)
    assert (Hsr : (Datatypes.S n' + 1 = Datatypes.S (n' + 1))%nat) by lia.
    rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq (Datatypes.S n' + 1)%nat (Datatypes.S (n' + 1)) (fun j => f (2 * j)%nat) Hsr)).
    change (sum_upto (Datatypes.S (n' + 1)) (fun j => f (2 * j)%nat)) with
      (sum_upto (n' + 1)%nat (fun j => f (2 * j)%nat) + f (2 * (n' + 1))%nat).
    change (sum_upto (Datatypes.S n') (fun j => f (2 * j + 1)%nat)) with
      (sum_upto n' (fun j => f (2 * j + 1)%nat) + f (2 * n' + 1)%nat).
    (* Unify the tail terms: f (2(n'+1)) == f (S(S(2n'))) ([H6]) and f (S(2n')) == f (2n'+1) ([Ht1]). *)
    assert (H6 : (2 * (n' + 1) = Datatypes.S (Datatypes.S (2 * n')))%nat) by lia.
    rewrite H6.
    assert (Ht1 : (Datatypes.S (2 * n') = 2 * n' + 1)%nat) by lia.
    rewrite Ht1.
    ring.
Qed.

(* Splitting a sum (general version, no range premises): the sum of f i over i < a+b ==
   the sum of f i over i < a + the sum of f (a+i) over i < b.
   By induction on [a]; in the step, peel the first term f 0 from both sides with [sum_upto_rot]
   and apply the IH to g = f∘S. *)
Lemma sum_upto_split_gen : forall (a b : nat) (f : nat -> Q),QeqT (
  sum_upto (a + b)%nat f ) ( sum_upto a f + sum_upto b (fun i => f (a + i)%nat)).
Proof.
  intros a. induction a as [| a' IH]; intros b f.
  - (* Case a = 0: sum_upto b f == 0 + sum_upto b (fun i => f (0+i)). *)
    apply qeq_imp_qeqT.
    change (sum_upto (0 + b) f) with (sum_upto b f).
    change (sum_upto 0 f) with 0.
    assert (Hpre1538_37 : (forall i,QeqT ( (fun i => f (0 + i)%nat) i ) ( f i))).
    {  intro i. apply qeq_imp_qeqT. change (f (0 + i)%nat) with (f i). reflexivity. }
    rewrite (qeqT_imp_qeq _ _ (sum_upto_ext b (fun i => f (0 + i)%nat) f Hpre1538_37)).
    ring.
  - (* Case a = S a': peel the first term f 0 from both sides with [sum_upto_rot], then apply the IH to g = f∘S. *)
    apply qeq_imp_qeqT.
    assert (Hadd : (Datatypes.S a' + b = Datatypes.S (a' + b))%nat) by lia.
    rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq (Datatypes.S a' + b) (Datatypes.S (a' + b)) f Hadd)).
    rewrite (qeqT_imp_qeq _ _ (sum_upto_rot (a' + b) f)).
    setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_rot a' f)).
    setoid_rewrite (qeqT_imp_qeq _ _ (IH b (fun i => f (Datatypes.S i)))).
    assert (Hpre1538_36 : (forall i,QeqT ( (fun i => f (Datatypes.S (a' + i))%nat) i ) ( (fun i => f (Datatypes.S a' + i)%nat) i))).
    {  intro i. apply qeq_imp_qeqT. assert (Hnat : (Datatypes.S (a' + i) = Datatypes.S a' + i)%nat) by lia.
         rewrite Hnat. reflexivity. }
    rewrite (qeqT_imp_qeq _ _ (sum_upto_ext b (fun i => f (Datatypes.S (a' + i))%nat) (fun i => f (Datatypes.S a' + i)%nat) Hpre1538_36)).
    ring.
Qed.

(* Mirror symmetry (an even number of terms): if f j == f (2n+1−j) for j <= n, then the sum of f j over j <= 2n+1 == 2 * the sum of f j over j <= n. *)
Lemma sum_upto_mirror_even : forall (n : nat) (f : nat -> Q),
  (forall j, NatLe j n ->QeqT ( f j ) ( f (2 * n + 1 - j)%nat)) ->QeqT (
  sum_upto (2 * n + 2)%nat f ) ( 2 * sum_upto (n + 1) f).
Proof.
  intros n f Hmir.
  apply qeq_imp_qeqT.
  (* 2n+2 == (n+1)+(n+1); split the sum there. *)
  assert (Hadd : (2 * n + 2 = (n + 1) + (n + 1))%nat) by lia.
  rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq (2 * n + 2)%nat ((n + 1) + (n + 1)) f Hadd)).
  setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_split_gen (n + 1) (n + 1) f)).
  (* Second sum: the sum of f (n+1+i) over i <= n == the sum of f i (mirrored, since f (2n+1−i) == f i). *)
  assert (Hsec : sum_upto (n + 1) (fun i => f (n + 1 + i)%nat) == sum_upto (n + 1) f).
  { (* Reverse with [sum_upto_rev]: sum_upto (n+1) h == sum_upto (n+1) (fun i => h (n−i)) for h i = f (n+1+i). *)
    setoid_rewrite <- (qeqT_imp_qeq _ _ (sum_upto_rev (n + 1) (fun i => f (n + 1 + i)%nat))).
    (* The identity n+1+(n−i) == 2n+1−i holds only for i <= n, so transport with [sum_upto_ext_below] over i < n+1. *)
    assert (Hpre1538_35 : (forall i : nat, NatLe (Datatypes.S i) (n + 1) ->QeqT ( (fun i => f (n + 1 + (n + 1 - 1 - i))%nat) i ) ( (fun i => f (2 * n + 1 - i)%nat) i))).
    {  intros i Hi. apply NatLe_drop in Hi. assert (Hnat : (n + 1 + (n + 1 - 1 - i) = 2 * n + 1 - i)%nat) by lia.
         apply qeq_imp_qeqT.
         rewrite Hnat. reflexivity. }
    rewrite (qeqT_imp_qeq _ _ (sum_upto_ext_below (n + 1) (fun i => f (n + 1 + (n + 1 - 1 - i))%nat) (fun i => f (2 * n + 1 - i)%nat) Hpre1538_35)).
    assert (Hpre1538_34 : (forall i : nat, NatLe (Datatypes.S i) (n + 1) ->QeqT ( (fun i => f (2 * n + 1 - i)%nat) i ) ( f i))).
    {  intros i Hi. apply NatLe_drop in Hi. apply qeq_imp_qeqT. apply Qeq_sym. apply qeqT_imp_qeq. apply (Hmir i). apply NatLe_lift. lia. }
    rewrite (qeqT_imp_qeq _ _ (sum_upto_ext_below (n + 1) (fun i => f (2 * n + 1 - i)%nat) f Hpre1538_34)).
    reflexivity. }
  setoid_rewrite Hsec.
  ring.
Qed.

(* Mirror symmetry (an odd number of terms): if f j == f (2n−j) for j <= n, then the sum of f j over j <= 2n == 2 * the sum of f j over j < n + f n. *)
Lemma sum_upto_mirror_odd : forall (n : nat) (f : nat -> Q),
  (forall j, NatLe j n ->QeqT ( f j ) ( f (2 * n - j)%nat)) ->QeqT (
  sum_upto (2 * n + 1)%nat f ) ( 2 * sum_upto n f + f n).
Proof.
  intros n f Hmir.
  apply qeq_imp_qeqT.
  (* 2n+1 == n+(n+1); split the sum there. *)
  assert (Hadd : (2 * n + 1 = n + (n + 1))%nat) by lia.
  rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq (2 * n + 1)%nat (n + (n + 1)) f Hadd)).
  setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_split_gen n (n + 1) f)).
  (* Second sum: the sum of f (n+i) == the sum of f (2n−i) == the sum of f i (mirrored). *)
  assert (Hsec : sum_upto (n + 1) (fun i => f (n + i)%nat) == sum_upto (n + 1) f).
  { setoid_rewrite <- (qeqT_imp_qeq _ _ (sum_upto_rev (n + 1) (fun i => f (n + i)%nat))).
    assert (Hpre1538_33 : (forall i : nat, NatLe (Datatypes.S i) (n + 1) ->QeqT ( (fun i => f (n + (n + 1 - 1 - i))%nat) i ) ( (fun i => f (2 * n - i)%nat) i))).
    {  intros i Hi. apply NatLe_drop in Hi. assert (Hnat : (n + (n + 1 - 1 - i) = 2 * n - i)%nat) by lia.
         apply qeq_imp_qeqT.
         rewrite Hnat. reflexivity. }
    rewrite (qeqT_imp_qeq _ _ (sum_upto_ext_below (n + 1) (fun i => f (n + (n + 1 - 1 - i))%nat) (fun i => f (2 * n - i)%nat) Hpre1538_33)).
    assert (Hpre1538_32 : (forall i : nat, NatLe (Datatypes.S i) (n + 1) ->QeqT ( (fun i => f (2 * n - i)%nat) i ) ( f i))).
    {  intros i Hi. apply NatLe_drop in Hi. apply qeq_imp_qeqT. apply Qeq_sym. apply qeqT_imp_qeq. apply (Hmir i). apply NatLe_lift. lia. }
    rewrite (qeqT_imp_qeq _ _ (sum_upto_ext_below (n + 1) (fun i => f (2 * n - i)%nat) f Hpre1538_32)).
    reflexivity. }
  setoid_rewrite Hsec.
  (* sum_upto (n+1) f == sum_upto n f + f n (the bound n+1 is not syntactically S n, so bridge with a [nat] identity). *)
  assert (Hs : (n + 1 = Datatypes.S n)%nat) by lia.
  rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq (n + 1)%nat (Datatypes.S n) f Hs)).
  change (sum_upto (Datatypes.S n) f) with (sum_upto n f + f n).
  ring.
Qed.

(* ===== [vander_4m2]: the Vandermonde identity at the a^(4m+2) layer =====
   The sum over 0 <= j <= m−1 of [-2/((4m+2−2j)!(2j)!) + 2/((4m+1−2j)!(2j+1)!)]
   == 2/((2m+2)!(2m)!) − 1/((2m+1)!(2m+1)!).
   Route: [altf_zero (4m+2)] (== 0), transport with [altf_as_sum_upto], the even/odd split,
   reduction of the (−1)-powers, mirror symmetry (the even part times 2; the odd part times 2
   plus the middle term), then algebra.
   Core: 0 == 2*Σ_{j=0}^{m} E_j − (2*Σ_{j=0}^{m−1} O_j + O_m)
        ⟹ 2*Σ_{j=0}^{m−1}(O_j−E_j) == 2*E_m − O_m == the right side (with denominators swapped); hence the claim. *)
Lemma vander_4m2 : forall (m : nat),
  (1 <= m)%nat ->QeqT (
  sum_upto m
    (fun j =>
       - 2 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j))
       + 2 / (q_fact (4 * m + 1 - 2 * j) * q_fact (2 * j + 1))) ) (
  2 / (q_fact (2 * m + 2) * q_fact (2 * m)) -
  1 / (q_fact (2 * m + 1) * q_fact (2 * m + 1))).
Proof.
  intros m Hm.
  apply qeq_imp_qeqT.
  (* 1. [altf_zero (4m+2)]: altf (4m+2) == 0; transport with [altf_as_sum_upto]. *)
  assert (Hz : altf (4 * m + 2) == 0).
  { apply qeqT_imp_qeq. apply altf_zero. lia. }
  setoid_rewrite (qeqT_imp_qeq _ _ (altf_as_sum_upto (4 * m + 2))) in Hz.
  (* 2. Even/odd split: sum_upto (4m+3) g == the sum of g (2j) over j <= 2m+1 plus the sum of g (2j+1) over j <= 2m.
     First transport the bound of Hz with a [nat] identity, from sum_upto (4m+2+1) to
     sum_upto (2(2m+1)+1) (not definitional). *)
  assert (Hn1 : (4 * m + 2 + 1 = 2 * (2 * m + 1) + 1)%nat) by lia.
  rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq (4 * m + 2 + 1)%nat (2 * (2 * m + 1) + 1)%nat            (fun u => q_pow (-1) u / (q_fact u * q_fact (4 * m + 2 - u))) Hn1)) in Hz.
  rewrite (qeqT_imp_qeq _ _ (sum_upto_even_split_odd (2 * m + 1)            (fun u => q_pow (-1) u / (q_fact u * q_fact (4 * m + 2 - u))))) in Hz.
  (* On the right, sum_upto (2m+1+1) == sum_upto (2m+2) (not definitional; a [nat] identity). *)
  assert (Hn2 : (2 * m + 1 + 1 = 2 * m + 2)%nat) by lia.
  rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq (2 * m + 1 + 1)%nat (2 * m + 2)%nat            (fun j => q_pow (-1) (2 * j) / (q_fact (2 * j) * q_fact (4 * m + 2 - 2 * j))) Hn2)) in Hz.
  (* 3. Pointwise reduction: g (2j) == 1/((2j)!(4m+2−2j)!) and g (2j+1) == −1/((2j+1)!(4m+1−2j)!). *)
  assert (Hpre1538_31 : (forall i,QeqT ( (fun j => q_pow (-1) (2 * j) / (q_fact (2 * j) * q_fact (4 * m + 2 - 2 * j))) i ) ( (fun j => 1 / (q_fact (2 * j) * q_fact (4 * m + 2 - 2 * j))) i))).
  {  intro j. apply qeq_imp_qeqT. setoid_rewrite (qeqT_imp_qeq _ _ (q_pow_neg1_even j)). ring. }
  rewrite (qeqT_imp_qeq _ _ (sum_upto_ext (2 * m + 2)            (fun j => q_pow (-1) (2 * j) / (q_fact (2 * j) * q_fact (4 * m + 2 - 2 * j)))            (fun j => 1 / (q_fact (2 * j) * q_fact (4 * m + 2 - 2 * j))) Hpre1538_31)) in Hz.
  assert (Hpre1538_30 : (forall i,QeqT ( (fun j => q_pow (-1) (2 * j + 1) / (q_fact (2 * j + 1) * q_fact (4 * m + 2 - (2 * j + 1)))) i ) ( (fun j => - 1 / (q_fact (2 * j + 1) * q_fact (4 * m + 1 - 2 * j))) i))).
  {  intro j. apply qeq_imp_qeqT. setoid_rewrite (qeqT_imp_qeq _ _ (q_pow_neg1_odd j)).
       assert (Hn : (4 * m + 2 - (2 * j + 1) = 4 * m + 1 - 2 * j)%nat) by lia.
       setoid_replace (q_fact (4 * m + 2 - (2 * j + 1))) with (q_fact (4 * m + 1 - 2 * j)).
       2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. lia. }
       ring. }
  rewrite (qeqT_imp_qeq _ _ (sum_upto_ext (2 * m + 1)            (fun j => q_pow (-1) (2 * j + 1) / (q_fact (2 * j + 1) * q_fact (4 * m + 2 - (2 * j + 1))))            (fun j => - 1 / (q_fact (2 * j + 1) * q_fact (4 * m + 1 - 2 * j))) Hpre1538_30)) in Hz.
  (* 4. Mirror symmetry: the even part, the sum of E_j over j <= 2m+1, equals 2 * the sum of E_j over j <= m. *)
  assert (HmirE : sum_upto (2 * m + 2)
             (fun j => 1 / (q_fact (2 * j) * q_fact (4 * m + 2 - 2 * j))) ==
           2 * sum_upto (m + 1)
             (fun j => 1 / (q_fact (2 * j) * q_fact (4 * m + 2 - 2 * j)))).
  { apply qeqT_imp_qeq.
  apply (sum_upto_mirror_even m             (fun j => 1 / (q_fact (2 * j) * q_fact (4 * m + 2 - 2 * j)))).
    intros j Hj. apply NatLe_drop in Hj.
    apply qeq_imp_qeqT.
    assert (H1 : (2 * (2 * m + 1 - j) = 4 * m + 2 - 2 * j)%nat) by lia.
    assert (H2 : (4 * m + 2 - 2 * (2 * m + 1 - j) = 2 * j)%nat) by lia.
    setoid_replace (q_fact (2 * (2 * m + 1 - j))) with (q_fact (4 * m + 2 - 2 * j)).
    2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. exact H1. }
    setoid_replace (q_fact (4 * m + 2 - 2 * (2 * m + 1 - j))) with (q_fact (2 * j)).
    2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. exact H2. }
    field.
    all: split; intro Hz1545; destruct (q_neq_of_lt _ (q_fact_pos _) (qeq_imp_qeqT _ _ Hz1545)). }
  (* 5. Mirror symmetry: the odd part, the sum of O_j over j <= 2m, equals 2 * the sum of O_j over j < m + O_m (with O_m = −1/((2m+1)!(2m+1)!)). *)
  assert (HmirO : sum_upto (2 * m + 1)
             (fun j => - 1 / (q_fact (2 * j + 1) * q_fact (4 * m + 1 - 2 * j))) ==
           2 * sum_upto m
             (fun j => - 1 / (q_fact (2 * j + 1) * q_fact (4 * m + 1 - 2 * j))) +
           (- 1) / (q_fact (2 * m + 1) * q_fact (2 * m + 1))).
  { (* Apply [sum_upto_mirror_odd] to f, where f j = -1/((2j+1)!(4m+1−2j)!), producing the f m term;
       first reduce the second [q_fact] argument of f m (4m+1−2m == 2m+1) and rewrite before applying. *)
    assert (Hmid : (4 * m + 1 - 2 * m = 2 * m + 1)%nat) by lia.
    assert (Hfmid : - 1 / (q_fact (2 * m + 1) * q_fact (4 * m + 1 - 2 * m)) ==
                    - 1 / (q_fact (2 * m + 1) * q_fact (2 * m + 1))).
    { setoid_replace (q_fact (4 * m + 1 - 2 * m)) with (q_fact (2 * m + 1)).
      2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. exact Hmid. }
      reflexivity. }
    (* The goal is 2 * the sum of f + (-1)/((2m+1)!(2m+1)!); and f m = (-1)/((2m+1)!(4m+1−2m)!) == the final term of the goal. *)
    setoid_rewrite <- Hfmid.
    apply qeqT_imp_qeq.
    apply (sum_upto_mirror_odd m             (fun j => - 1 / (q_fact (2 * j + 1) * q_fact (4 * m + 1 - 2 * j)))).
    intros j Hj. apply NatLe_drop in Hj.
    apply qeq_imp_qeqT.
    assert (H1 : (2 * (2 * m - j) + 1 = 4 * m + 1 - 2 * j)%nat) by lia.
    assert (H2 : (4 * m + 1 - 2 * (2 * m - j) = 2 * j + 1)%nat) by lia.
    setoid_replace (q_fact (2 * (2 * m - j) + 1)) with (q_fact (4 * m + 1 - 2 * j)).
    2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. exact H1. }
    setoid_replace (q_fact (4 * m + 1 - 2 * (2 * m - j))) with (q_fact (2 * j + 1)).
    2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. exact H2. }
    field.
    all: split; intro Hz1545; destruct (q_neq_of_lt _ (q_fact_pos _) (qeq_imp_qeqT _ _ Hz1545)). }
  (* 6. Substitute the mirrored forms into Hz: Hz == 2*Σ_{j=0}^{m} E_j − (2*Σ_{j=0}^{m−1} O_j + O_m) == 0. *)
  setoid_rewrite HmirE in Hz.
  setoid_rewrite HmirO in Hz.
  (* 7. Split the E sum: Σ_{j=0}^{m} E_j == Σ_{j=0}^{m−1} E_j + E_m, with E_m = 1/((2m)!(2m+2)!). *)
  assert (HsplitE : sum_upto (m + 1)
             (fun j => 1 / (q_fact (2 * j) * q_fact (4 * m + 2 - 2 * j))) ==
            sum_upto m
             (fun j => 1 / (q_fact (2 * j) * q_fact (4 * m + 2 - 2 * j))) +
           1 / (q_fact (2 * m) * q_fact (2 * m + 2))).
  { assert (Hs : (m + 1 = Datatypes.S m)%nat) by lia.
    rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq (m + 1)%nat (Datatypes.S m)              (fun j => 1 / (q_fact (2 * j) * q_fact (4 * m + 2 - 2 * j))) Hs)).
    change (sum_upto (Datatypes.S m)
              (fun j => 1 / (q_fact (2 * j) * q_fact (4 * m + 2 - 2 * j)))) with
      (sum_upto m (fun j => 1 / (q_fact (2 * j) * q_fact (4 * m + 2 - 2 * j))) +
       1 / (q_fact (2 * m) * q_fact (4 * m + 2 - 2 * m))).
    setoid_replace (q_fact (4 * m + 2 - 2 * m)) with (q_fact (2 * m + 2)).
    2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. lia. }
    reflexivity. }
  setoid_rewrite HsplitE in Hz.
  (* 8. Algebra on Hz: Hz == 2*ΣE' + 2*Em − 2*ΣO'' − Om == 0 (with O'' = 1/((2j+1)!(4m+1−2j)!)).
     First turn the Σ(−1/X) in Hz into −Σ(1/X) via [HzO] ([sum_upto_neg] plus pointwise
     extensionality). *)
  assert (HzO : sum_upto m (fun j => (- 1) / (q_fact (2 * j + 1) * q_fact (4 * m + 1 - 2 * j))) ==
                - sum_upto m (fun j => 1 / (q_fact (2 * j + 1) * q_fact (4 * m + 1 - 2 * j)))).
  { setoid_rewrite <- (qeqT_imp_qeq _ _ (sum_upto_neg m             (fun j => 1 / (q_fact (2 * j + 1) * q_fact (4 * m + 1 - 2 * j))))).
    apply qeqT_imp_qeq.
    apply (sum_upto_ext m             (fun j => (- 1) / (q_fact (2 * j + 1) * q_fact (4 * m + 1 - 2 * j)))             (fun j => - (1 / (q_fact (2 * j + 1) * q_fact (4 * m + 1 - 2 * j))))).
    intro j. apply qeq_imp_qeqT. unfold Qdiv. ring. }
  rewrite HzO in Hz.
  (* 9. Transpose Hz (the [qeq_moved] pattern): 2*ΣO'' − 2*ΣE' == 2*Em − Om.
     Negate Hz with [Qopp_comp] (avoiding syntactic matching), then transitivity plus [ring]. *)
  assert (Hmoved : 2 * sum_upto m
                     (fun j => 1 / (q_fact (2 * j + 1) * q_fact (4 * m + 1 - 2 * j))) -
                    2 * sum_upto m
                      (fun j => 1 / (q_fact (2 * j) * q_fact (4 * m + 2 - 2 * j))) ==
                   2 * (1 / (q_fact (2 * m) * q_fact (2 * m + 2))) -
                   1 / (q_fact (2 * m + 1) * q_fact (2 * m + 1))).
  { (* [Hdiff] : LHS - RHS == 0; LHS - RHS == -(Hz LHS) by [ring], and -(Hz LHS) == 0 by negating Hz. *)
    assert (Hdiff : (2 * sum_upto m
                       (fun j => 1 / (q_fact (2 * j + 1) * q_fact (4 * m + 1 - 2 * j))) -
                      2 * sum_upto m
                        (fun j => 1 / (q_fact (2 * j) * q_fact (4 * m + 2 - 2 * j)))) -
                     (2 * (1 / (q_fact (2 * m) * q_fact (2 * m + 2))) -
                      1 / (q_fact (2 * m + 1) * q_fact (2 * m + 1))) == 0).
    { (* The left side of [Hdiff] == -A by [ring], and -A == 0 by negating Hz; A is extracted from Hz with [set] (avoiding syntactic matching). *)
      set (A := 2 * (sum_upto m
                       (fun j => 1 / (q_fact (2 * j) * q_fact (4 * m + 2 - 2 * j))) +
                      1 / (q_fact (2 * m) * q_fact (2 * m + 2))) +
                  (2 * (- sum_upto m
                          (fun j => 1 / (q_fact (2 * j + 1) * q_fact (4 * m + 1 - 2 * j)))) +
                   (- 1) / (q_fact (2 * m + 1) * q_fact (2 * m + 1)))).
      change (A == 0) in Hz.
      transitivity (- A).
      - unfold A. unfold Qdiv. ring.
      - (* -A == 0: [Qopp_comp] applied to Hz gives -A == -0; -0 == 0 by [ring]. *)
        assert (Hopp : - A == - 0).
        { apply (Qopp_comp A 0 Hz). }
        rewrite <- Hopp. unfold Qdiv. ring. }
    (* From [Hdiff] : LHS - RHS == 0, add RHS to both sides to conclude LHS == RHS. *)
    transitivity ((2 * sum_upto m
                     (fun j => 1 / (q_fact (2 * j + 1) * q_fact (4 * m + 1 - 2 * j))) -
                    2 * sum_upto m
                      (fun j => 1 / (q_fact (2 * j) * q_fact (4 * m + 2 - 2 * j)))) -
                   (2 * (1 / (q_fact (2 * m) * q_fact (2 * m + 2))) -
                    1 / (q_fact (2 * m + 1) * q_fact (2 * m + 1))) +
                   (2 * (1 / (q_fact (2 * m) * q_fact (2 * m + 2))) -
                    1 / (q_fact (2 * m + 1) * q_fact (2 * m + 1)))).
    - unfold Qdiv. ring.
    - rewrite Hdiff. ring. }
  (* 10. The goal of [vander_4m2] is stated as the sum of (-2E + 2O); linearity of [sum_upto]
     converts it into -2ΣE' + 2ΣO''. *)
  (* Goal: sum_upto m (fun j => -2/X_j + 2/Y_j) == 2/((2m+2)!(2m)!) - 1/((2m+1)!(2m+1)!).
     Linearity on the left: Σ(-2E+2O) == -2ΣE' + 2ΣO'' (pointwise [sum_upto_ext] plus
     the inductive linearity lemmas). *)
  assert (Hlin : sum_upto m
                   (fun j => - 2 * (1 / (q_fact (2 * j) * q_fact (4 * m + 2 - 2 * j))) +
                             2 * (1 / (q_fact (2 * j + 1) * q_fact (4 * m + 1 - 2 * j)))) ==
                 - 2 * sum_upto m (fun j => 1 / (q_fact (2 * j) * q_fact (4 * m + 2 - 2 * j))) +
                 2 * sum_upto m (fun j => 1 / (q_fact (2 * j + 1) * q_fact (4 * m + 1 - 2 * j)))).
  { rewrite (qeqT_imp_qeq _ _ (sum_upto_plus m              (fun j => - 2 * (1 / (q_fact (2 * j) * q_fact (4 * m + 2 - 2 * j))))              (fun j => 2 * (1 / (q_fact (2 * j + 1) * q_fact (4 * m + 1 - 2 * j)))))).
    assert (Hsc1 : sum_upto m (fun j => - 2 * (1 / (q_fact (2 * j) * q_fact (4 * m + 2 - 2 * j)))) ==
                  - 2 * sum_upto m (fun j => 1 / (q_fact (2 * j) * q_fact (4 * m + 2 - 2 * j)))).
    { exact (qeqT_imp_qeq _ _ (sum_upto_scale_neg2 m (fun j => 1 / (q_fact (2 * j) * q_fact (4 * m + 2 - 2 * j))))). }
    assert (Hsc2 : sum_upto m (fun j => 2 * (1 / (q_fact (2 * j + 1) * q_fact (4 * m + 1 - 2 * j)))) ==
                  2 * sum_upto m (fun j => 1 / (q_fact (2 * j + 1) * q_fact (4 * m + 1 - 2 * j)))).
    { exact (qeqT_imp_qeq _ _ (sum_upto_scale m 2 (fun j => 1 / (q_fact (2 * j + 1) * q_fact (4 * m + 1 - 2 * j))))). }
    setoid_rewrite Hsc1. setoid_rewrite Hsc2. reflexivity. }
  (* Normalize the left side of [vander_4m2] pointwise to -2*(1/X') + 2*(1/Y') (with denominators swapped). *)
  assert (Hpre1538_29 : (forall i,QeqT ( (fun j => - 2 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j)) + 2 / (q_fact (4 * m + 1 - 2 * j) * q_fact (2 * j + 1))) i ) ( (fun j => - 2 * (1 / (q_fact (2 * j) * q_fact (4 * m + 2 - 2 * j))) +                      2 * (1 / (q_fact (2 * j + 1) * q_fact (4 * m + 1 - 2 * j)))) i))).
  {  intro j. apply qeq_imp_qeqT. unfold Qdiv. field.
       all: repeat (split; [intro Hz1545; destruct (q_neq_of_lt _ (q_fact_pos _) (qeq_imp_qeqT _ _ Hz1545)) | idtac]);
            intro Hz1545; destruct (q_neq_of_lt _ (q_fact_pos _) (qeq_imp_qeqT _ _ Hz1545)). }
  rewrite (qeqT_imp_qeq _ _ (sum_upto_ext m            (fun j => - 2 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j)) +
                      2 / (q_fact (4 * m + 1 - 2 * j) * q_fact (2 * j + 1)))
            (fun j => - 2 * (1 / (q_fact (2 * j) * q_fact (4 * m + 2 - 2 * j))) +                      2 * (1 / (q_fact (2 * j + 1) * q_fact (4 * m + 1 - 2 * j)))) Hpre1538_29)).
  setoid_rewrite Hlin.
  (* Goal: -2ΣE' + 2ΣO'' == 2/((2m+2)!(2m)!) - 1/((2m+1)!(2m+1)!).
     [Hmoved] : 2ΣO'' - 2ΣE' == 2Em' - Om'.
     Right side: 2Em' - Om' == 2/((2m+2)!(2m)!) - 1/((2m+1)!(2m+1)!) (denominators swapped, by [ring]). *)
  setoid_replace (2 / (q_fact (2 * m + 2) * q_fact (2 * m)))
    with (2 * (1 / (q_fact (2 * m) * q_fact (2 * m + 2)))).
  2: { unfold Qdiv. field.
       all: repeat (split; [intro Hz1545; destruct (q_neq_of_lt _ (q_fact_pos _) (qeq_imp_qeqT _ _ Hz1545)) | idtac]);
            intro Hz1545; destruct (q_neq_of_lt _ (q_fact_pos _) (qeq_imp_qeqT _ _ Hz1545)). }
  (* Goal: -2ΣE' + 2ΣO'' == 2Em' - Om'; conclude with [Hmoved] (a [ring]-equivalent left side). *)
  transitivity (2 * sum_upto m
                  (fun j => 1 / (q_fact (2 * j + 1) * q_fact (4 * m + 1 - 2 * j))) -
                2 * sum_upto m
                  (fun j => 1 / (q_fact (2 * j) * q_fact (4 * m + 2 - 2 * j)))).
  - unfold Qdiv. ring.
  - exact Hmoved.
Qed.

(* ===== [vander_4m4]: the Vandermonde identity at the a^(4m+4) layer =====
   The sum over 0 <= j <= m−1 of [-2/((4m+2−2j)!(2j+2)!) + 2/((4m+1−2j)!(2j+3)!)]
   + [-2/((4m+4)!(0)!) + 2/((4m+3)!(1)!)] == 1/((2m+2)!(2m+2)!).
   Route (parallel to [vander_4m2]): [altf_zero (4m+4)], transport with [altf_as_sum_upto],
   the even/odd split (sum_upto (4m+5) = sum_upto (2(2m+2)+1)), reduction of the (−1)-powers,
   mirror symmetry (both parts times 2, no middle term), then transposition of [Qeq]
   (the [Qopp_comp] pattern).
   The tail term [-2/((4m+4)!(0)!) + 2/((4m+3)!(1)!)] merges with the j = 0 summand; at j = 0 the
   bracket is -2/((4m+2)!(2)!) + 2/((4m+1)!(3)!) plus the tail, so the pairing must be done globally. *)
Lemma vander_4m4 : forall (m : nat),
  (1 <= m)%nat ->QeqT (
  sum_upto m
    (fun j =>
       - 2 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 2))
       + 2 / (q_fact (4 * m + 1 - 2 * j) * q_fact (2 * j + 3)))
  - 2 / (q_fact (4 * m + 4) * q_fact 0)
  + 2 / (q_fact (4 * m + 3) * q_fact 1) ) (
  1 / (q_fact (2 * m + 2) * q_fact (2 * m + 2))).
Proof.
  intros m Hm.
  apply qeq_imp_qeqT.
  (* 1. [altf_zero (4m+4)]: altf (4m+4) == 0; transport with [altf_as_sum_upto]. *)
  assert (Hz : altf (4 * m + 4) == 0).
  { apply qeqT_imp_qeq. apply altf_zero. lia. }
  setoid_rewrite (qeqT_imp_qeq _ _ (altf_as_sum_upto (4 * m + 4))) in Hz.
  (* 2. Even/odd split: sum_upto (4m+5) g == the sum of g (2j) over j <= 2m+2 plus the sum of g (2j+1) over j <= 2m+1.
     First transport the bound of Hz with a [nat] identity, from sum_upto (4m+4+1) to sum_upto (2(2m+2)+1). *)
  assert (Hn1 : (4 * m + 4 + 1 = 2 * (2 * m + 2) + 1)%nat) by lia.
  rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq (4 * m + 4 + 1)%nat (2 * (2 * m + 2) + 1)%nat            (fun u => q_pow (-1) u / (q_fact u * q_fact (4 * m + 4 - u))) Hn1)) in Hz.
  rewrite (qeqT_imp_qeq _ _ (sum_upto_even_split_odd (2 * m + 2)            (fun u => q_pow (-1) u / (q_fact u * q_fact (4 * m + 4 - u))))) in Hz.
  assert (Hn2 : (2 * m + 2 + 1 = 2 * m + 3)%nat) by lia.
  rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq (2 * m + 2 + 1)%nat (2 * m + 3)%nat            (fun j => q_pow (-1) (2 * j) / (q_fact (2 * j) * q_fact (4 * m + 4 - 2 * j))) Hn2)) in Hz.
  (* 3. Pointwise reduction: g (2j) == 1/((2j)!(4m+4−2j)!) and g (2j+1) == −1/((2j+1)!(4m+3−2j)!). *)
  assert (Hpre1538_28 : (forall i,QeqT ( (fun j => q_pow (-1) (2 * j) / (q_fact (2 * j) * q_fact (4 * m + 4 - 2 * j))) i ) ( (fun j => 1 / (q_fact (2 * j) * q_fact (4 * m + 4 - 2 * j))) i))).
  {  intro j. apply qeq_imp_qeqT. setoid_rewrite (qeqT_imp_qeq _ _ (q_pow_neg1_even j)). ring. }
  rewrite (qeqT_imp_qeq _ _ (sum_upto_ext (2 * m + 3)            (fun j => q_pow (-1) (2 * j) / (q_fact (2 * j) * q_fact (4 * m + 4 - 2 * j)))            (fun j => 1 / (q_fact (2 * j) * q_fact (4 * m + 4 - 2 * j))) Hpre1538_28)) in Hz.
  assert (Hpre1538_27 : (forall i,QeqT ( (fun j => q_pow (-1) (2 * j + 1) / (q_fact (2 * j + 1) * q_fact (4 * m + 4 - (2 * j + 1)))) i ) ( (fun j => - 1 / (q_fact (2 * j + 1) * q_fact (4 * m + 3 - 2 * j))) i))).
  {  intro j. apply qeq_imp_qeqT. setoid_rewrite (qeqT_imp_qeq _ _ (q_pow_neg1_odd j)).
       assert (Hn : (4 * m + 4 - (2 * j + 1) = 4 * m + 3 - 2 * j)%nat) by lia.
       setoid_replace (q_fact (4 * m + 4 - (2 * j + 1))) with (q_fact (4 * m + 3 - 2 * j)).
       2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. lia. }
       ring. }
  rewrite (qeqT_imp_qeq _ _ (sum_upto_ext (2 * m + 2)            (fun j => q_pow (-1) (2 * j + 1) / (q_fact (2 * j + 1) * q_fact (4 * m + 4 - (2 * j + 1))))            (fun j => - 1 / (q_fact (2 * j + 1) * q_fact (4 * m + 3 - 2 * j))) Hpre1538_27)) in Hz.
  (* 4. Mirror symmetry:
       the even part, sum_upto (2m+3) E (2m+3 terms, j = 0..2m+2): [sum_upto_mirror_odd] at n = m+1
         gives 2*Σ_{j=0}^{m} E_j + E_{m+1};
       the odd part, sum_upto (2m+2) O (2m+2 terms, j = 0..2m+1): [sum_upto_mirror_even] at n = m
         gives 2*Σ_{j=0}^{m} O_j. *)
  assert (HmirE : sum_upto (2 * m + 3)
             (fun j => 1 / (q_fact (2 * j) * q_fact (4 * m + 4 - 2 * j))) ==
           2 * sum_upto (m + 1)
             (fun j => 1 / (q_fact (2 * j) * q_fact (4 * m + 4 - 2 * j))) +
           1 / (q_fact (2 * (m + 1)) * q_fact (4 * m + 4 - 2 * (m + 1)))).
  { (* The conclusion of [sum_upto_mirror_odd] at (m+1): sum_upto (2(m+1)+1) f == 2*sum_upto (m+1) f + f (m+1).
       Since 2(m+1)+1 == 2m+3 is not syntactically identical, first transport the goal's left side
       with a [nat] identity, then apply. *)
    assert (Hidx : (2 * (m + 1) + 1 = 2 * m + 3)%nat) by lia.
    rewrite <- (qeqT_imp_qeq _ _ (sum_upto_nat_eq (2 * (m + 1) + 1)%nat (2 * m + 3)%nat              (fun j => 1 / (q_fact (2 * j) * q_fact (4 * m + 4 - 2 * j))) Hidx)).
    apply qeqT_imp_qeq.
    apply (sum_upto_mirror_odd (m + 1)             (fun j => 1 / (q_fact (2 * j) * q_fact (4 * m + 4 - 2 * j)))).
    intros j Hj. apply NatLe_drop in Hj.
    apply qeq_imp_qeqT.
    assert (H1 : (2 * (2 * (m + 1) - j) = 4 * m + 4 - 2 * j)%nat) by lia.
    assert (H2 : (4 * m + 4 - 2 * (2 * (m + 1) - j) = 2 * j)%nat) by lia.
    setoid_replace (q_fact (2 * (2 * (m + 1) - j))) with (q_fact (4 * m + 4 - 2 * j)).
    2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. exact H1. }
    setoid_replace (q_fact (4 * m + 4 - 2 * (2 * (m + 1) - j))) with (q_fact (2 * j)).
    2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. exact H2. }
    field.
    all: repeat (split; [intro Hz1545; destruct (q_neq_of_lt _ (q_fact_pos _) (qeq_imp_qeqT _ _ Hz1545)) | idtac]);
         intro Hz1545; destruct (q_neq_of_lt _ (q_fact_pos _) (qeq_imp_qeqT _ _ Hz1545)). }
  assert (HmirO : sum_upto (2 * m + 2)
             (fun j => - 1 / (q_fact (2 * j + 1) * q_fact (4 * m + 3 - 2 * j))) ==
           2 * sum_upto (m + 1)
             (fun j => - 1 / (q_fact (2 * j + 1) * q_fact (4 * m + 3 - 2 * j)))).
  { apply qeqT_imp_qeq.
  apply (sum_upto_mirror_even m             (fun j => - 1 / (q_fact (2 * j + 1) * q_fact (4 * m + 3 - 2 * j)))).
    intros j Hj. apply NatLe_drop in Hj.
    apply qeq_imp_qeqT.
    assert (H1 : (2 * (2 * m + 1 - j) + 1 = 4 * m + 3 - 2 * j)%nat) by lia.
    assert (H2 : (4 * m + 3 - 2 * (2 * m + 1 - j) = 2 * j + 1)%nat) by lia.
    setoid_replace (q_fact (2 * (2 * m + 1 - j) + 1)) with (q_fact (4 * m + 3 - 2 * j)).
    2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. exact H1. }
    setoid_replace (q_fact (4 * m + 3 - 2 * (2 * m + 1 - j))) with (q_fact (2 * j + 1)).
    2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. exact H2. }
    field.
    all: repeat (split; [intro Hz1545; destruct (q_neq_of_lt _ (q_fact_pos _) (qeq_imp_qeqT _ _ Hz1545)) | idtac]);
         intro Hz1545; destruct (q_neq_of_lt _ (q_fact_pos _) (qeq_imp_qeqT _ _ Hz1545)). }
  (* 5. Substitute the mirrored forms into Hz: Hz == the even part + the odd part == 0
       (after reducing the (−1)-powers, even − odd == 0), with
       even == 2*Σ_{j=0}^{m} E_j + E_{m+1} and odd == 2*Σ_{j=0}^{m} O_j.
       Hence (2Σ_{j=0}^{m} E_j + E_{m+1}) − 2Σ_{j=0}^{m} O_j == 0,
       so 2Σ_{j=0}^{m} O_j − 2Σ_{j=0}^{m} E_j == E_{m+1} == 1/((2m+2)!(2m+2)!). *)
  (* In Hz the odd part carries a minus sign: (2ΣE + E_{m+1}) + (2ΣO') == 0 with O' = -1/X. *)
  setoid_rewrite HmirE in Hz.
  setoid_rewrite HmirO in Hz.
  (* In Hz the odd part is 2*Σ(-1/X); first normalize the minus sign with the [HzO] pattern. *)
  assert (HzO : sum_upto (m + 1) (fun j => (- 1) / (q_fact (2 * j + 1) * q_fact (4 * m + 3 - 2 * j))) ==
                - sum_upto (m + 1) (fun j => 1 / (q_fact (2 * j + 1) * q_fact (4 * m + 3 - 2 * j)))).
  { setoid_rewrite <- (qeqT_imp_qeq _ _ (sum_upto_neg (m + 1)             (fun j => 1 / (q_fact (2 * j + 1) * q_fact (4 * m + 3 - 2 * j))))).
    apply qeqT_imp_qeq.
    apply (sum_upto_ext (m + 1)             (fun j => (- 1) / (q_fact (2 * j + 1) * q_fact (4 * m + 3 - 2 * j)))             (fun j => - (1 / (q_fact (2 * j + 1) * q_fact (4 * m + 3 - 2 * j))))).
    intro j. apply qeq_imp_qeqT. unfold Qdiv. ring. }
  rewrite HzO in Hz.
  (* With E_{m+1} reduced, Hz reads: 2*Σ_{j=0}^{m} E_j + E_{m+1} − 2*Σ_{j=0}^{m} O_j == 0. *)
  (* E_{m+1} = 1/((2m+2)!(2m+2)!); extract with [set] and transpose the [Qeq]. *)
  set (A := 2 * (sum_upto m
                    (fun j => 1 / (q_fact (2 * j) * q_fact (4 * m + 4 - 2 * j))) +
                   1 / (q_fact (2 * (m + 1)) * q_fact (4 * m + 4 - 2 * (m + 1)))) +
             (2 * (- sum_upto m
                     (fun j => 1 / (q_fact (2 * j + 1) * q_fact (4 * m + 3 - 2 * j)))))).
  (* Check whether the left side of Hz matches A by [change]. *)
  (* After [HzO], the O part of Hz is 2*(-ΣO_j) and the E part is 2*(ΣE_j + E_{m+1}). *)
  (* Since the structure of Hz may differ syntactically, verify with [change] before use. *)
  (* Construct [Hmoved] directly: 2ΣO − 2ΣE == E_{m+1} (the Qeq transposition pattern). *)
  assert (Hmoved : 2 * sum_upto (m + 1)
                     (fun j => 1 / (q_fact (2 * j + 1) * q_fact (4 * m + 3 - 2 * j))) -
                    2 * sum_upto (m + 1)
                      (fun j => 1 / (q_fact (2 * j) * q_fact (4 * m + 4 - 2 * j))) ==
                   1 / (q_fact (2 * (m + 1)) * q_fact (4 * m + 4 - 2 * (m + 1)))).
  { (* Hz : 2*ΣE + E_{m+1} + 2*(-ΣO) == 0 (after [HzO]); [Hmoved] : 2ΣO - 2ΣE == E_{m+1}.
       Apply [qeq_moved_neg2] with (A = 2ΣE, B = E_{m+1}, C = ΣO):
       A + B + 2*(-C) == 0 implies 2C - A == B, and the premise is exactly Hz
       ([ring]-equivalent: Hz states 2ΣE + E_{m+1} + 2*(-ΣO) == 0). *)
    apply qeqT_imp_qeq.
    apply (qeq_moved_neg2
             (2 * sum_upto (m + 1) (fun j => 1 / (q_fact (2 * j) * q_fact (4 * m + 4 - 2 * j))))
             (1 / (q_fact (2 * (m + 1)) * q_fact (4 * m + 4 - 2 * (m + 1))))
             (sum_upto (m + 1) (fun j => 1 / (q_fact (2 * j + 1) * q_fact (4 * m + 3 - 2 * j))))).
    apply qeq_imp_qeqT.
    (* It remains to show 2ΣE + E_{m+1} + 2*(-ΣO) == 0, a [ring]-equivalent form of Hz (transitivity against Hz's left side). *)
    transitivity (2 * sum_upto (m + 1)
                    (fun j => 1 / (q_fact (2 * j) * q_fact (4 * m + 4 - 2 * j))) +
                   1 / (q_fact (2 * (m + 1)) * q_fact (4 * m + 4 - 2 * (m + 1))) +
                   2 * (- sum_upto (m + 1)
                          (fun j => 1 / (q_fact (2 * j + 1) * q_fact (4 * m + 3 - 2 * j))))).
    - unfold Qdiv. ring.
    - exact Hz. }
  (* 6. The left side of [vander_4m4] == -2*Σ_{k=0}^{m} E_k + 2*Σ_{k=0}^{m} O_k
       (reindexing E''_j = E_{j+1} and merging the tail term):
       the goal's left side, sum_upto m (fun j => -2/((4m+2−2j)!(2j+2)!) + 2/((4m+1−2j)!(2j+3)!))
       − 2/((4m+4)!(0)!) + 2/((4m+3)!(1)!),
       == -2*Σ_{k=1}^{m} E_k + 2*Σ_{k=1}^{m} O_k − 2*E_0 + 2*O_0
       == -2*Σ_{k=0}^{m} E_k + 2*Σ_{k=0}^{m} O_k,
       while [Hmoved] : 2Σ_{0}^{m} O − 2Σ_{0}^{m} E == E_{m+1}
       and E_{m+1} == 1/((2m+2)!(2m+2)!) (denominators swapped). *)
  (* Reindex the left side of [vander_4m4] with [sum_upto_ext] over j, rewriting E''_j into the E_{j+1} shape (denominators written in matching form first). *)
  assert (Hlin : sum_upto m
                   (fun j => - 2 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 2)) +
                             2 / (q_fact (4 * m + 1 - 2 * j) * q_fact (2 * j + 3))) ==
                 - 2 * sum_upto m (fun j => 1 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 2))) +
                 2 * sum_upto m (fun j => 1 / (q_fact (4 * m + 1 - 2 * j) * q_fact (2 * j + 3)))).
  { rewrite (qeqT_imp_qeq _ _ (sum_upto_plus m              (fun j => - 2 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 2)))              (fun j => 2 / (q_fact (4 * m + 1 - 2 * j) * q_fact (2 * j + 3))))).
    assert (Hsc1 : sum_upto m (fun j => - 2 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 2))) ==
                   - 2 * sum_upto m (fun j => 1 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 2)))).
    assert (Hpre1538_26 : (forall i,QeqT ( (fun j => - 2 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 2))) i ) ( (fun j => - 2 * (1 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 2)))) i))).
      {  intro j. apply qeq_imp_qeqT. unfold Qdiv. ring. }
    { rewrite (qeqT_imp_qeq _ _ (sum_upto_ext m                (fun j => - 2 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 2)))                (fun j => - 2 * (1 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 2)))) Hpre1538_26)).
      apply (qeqT_imp_qeq _ _ (sum_upto_scale_neg2 m (fun j => 1 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 2))))). }
    assert (Hsc2 : sum_upto m (fun j => 2 / (q_fact (4 * m + 1 - 2 * j) * q_fact (2 * j + 3))) ==
                   2 * sum_upto m (fun j => 1 / (q_fact (4 * m + 1 - 2 * j) * q_fact (2 * j + 3)))).
    assert (Hpre1538_25 : (forall i,QeqT ( (fun j => 2 / (q_fact (4 * m + 1 - 2 * j) * q_fact (2 * j + 3))) i ) ( (fun j => 2 * (1 / (q_fact (4 * m + 1 - 2 * j) * q_fact (2 * j + 3)))) i))).
      {  intro j. apply qeq_imp_qeqT. unfold Qdiv. ring. }
    { rewrite (qeqT_imp_qeq _ _ (sum_upto_ext m                (fun j => 2 / (q_fact (4 * m + 1 - 2 * j) * q_fact (2 * j + 3)))                (fun j => 2 * (1 / (q_fact (4 * m + 1 - 2 * j) * q_fact (2 * j + 3)))) Hpre1538_25)).
      apply (qeqT_imp_qeq _ _ (sum_upto_scale m 2 (fun j => 1 / (q_fact (4 * m + 1 - 2 * j) * q_fact (2 * j + 3))))). }
    setoid_rewrite Hsc1. setoid_rewrite Hsc2.
    reflexivity. }
  (* Reindex the right-side terms of [Hlin] to E/O with k = j+1: 1/((2j+2)!(4m+2−2j)!) == E_{j+1} and similarly, via [sum_upto_ext]. *)
  (* Final goal: -2Σ_{j=0}^{m}E_{j+1} + 2Σ_{j=0}^{m}O_{j+1} - 2E_0 + 2O_0 == 1/((2m+2)!(2m+2)!),
     while [Hmoved] : 2Σ_{0}^{m}O_j - 2Σ_{0}^{m}E_j == E_{m+1}.
     E_{j+1} and E_j differ by one index, so reindex with [sum_upto_ext] over j. *)
  (* Index bookkeeping: the left side of [vander_4m4] sums over j = 0..m−1 (m terms) while
     [Hmoved] sums over j = 0..m (m+1 terms).
     Still, the left side = -2Σ_{j=0}^{m-1}E''_j + 2Σ_{j=0}^{m-1}O''_j + tail
                = -2Σ_{k=1}^{m}E_k + 2Σ_{k=1}^{m}O_k - 2E_0 + 2O_0
                = -2Σ_{k=0}^{m}E_k + 2Σ_{k=0}^{m}O_k,
     which aligns with [Hmoved] exactly. *)
  (* Conclusion: the left side == -2Σ_{k=0}^{m}E_k + 2Σ_{k=0}^{m}O_k == the left side of [Hmoved] == E_{m+1} == the right side. *)
  setoid_rewrite Hlin.
  (* Goal: -2*Σ_{j=0}^{m-1}(E''_j) + 2*Σ_{j=0}^{m-1}(O''_j) - 2/((4m+4)!0!) + 2/((4m+3)!1!) == the right side,
     with E''_j = 1/((4m+2-2j)!(2j+2)!) and O''_j = 1/((4m+1-2j)!(2j+3)!). *)
  (* Reindex: E''_j == E_{j+1} (with E_k = 1/((4m+4-2k)!(2k)!)), applying [sum_upto_shift] to the E part. *)
  assert (HshiftE : sum_upto m (fun j => 1 / (q_fact (4 * m + 4 - 2 * (j + 1)) * q_fact (2 * (j + 1)))) ==
                    sum_upto (m + 1) (fun k => 1 / (q_fact (4 * m + 4 - 2 * k) * q_fact (2 * k))) -
                    1 / (q_fact (4 * m + 4 - 2 * 0) * q_fact (2 * 0))).
  { apply (qeqT_imp_qeq _ _ (sum_upto_shift m (fun k => 1 / (q_fact (4 * m + 4 - 2 * k) * q_fact (2 * k))))). }
  (* The E part of the goal's left side is -2*Σ(E''_j) (the sign sits outside the sum), so reindex inside the sum with [sum_upto_ext]: E''_j -> E_{j+1}. *)
  assert (Hpre1538_24 : (forall i,QeqT ( (fun j => 1 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 2))) i ) ( (fun j => 1 / (q_fact (4 * m + 4 - 2 * (j + 1)) * q_fact (2 * (j + 1)))) i))).
  {  intro j. apply qeq_imp_qeqT. assert (H1 : (4 * m + 4 - 2 * (j + 1) = 4 * m + 2 - 2 * j)%nat) by lia.
       assert (H2 : (2 * (j + 1) = 2 * j + 2)%nat) by lia.
       setoid_replace (q_fact (4 * m + 4 - 2 * (j + 1))) with (q_fact (4 * m + 2 - 2 * j)).
       2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. exact H1. }
       setoid_replace (q_fact (2 * (j + 1))) with (q_fact (2 * j + 2)).
       2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. exact H2. }
       reflexivity. }
  rewrite (qeqT_imp_qeq _ _ (sum_upto_ext m            (fun j => 1 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 2)))            (fun j => 1 / (q_fact (4 * m + 4 - 2 * (j + 1)) * q_fact (2 * (j + 1)))) Hpre1538_24)).
  assert (Hpre1538_23 : (forall i,QeqT ( (fun j => 1 / (q_fact (4 * m + 1 - 2 * j) * q_fact (2 * j + 3))) i ) ( (fun j => 1 / (q_fact (4 * m + 3 - 2 * (j + 1)) * q_fact (2 * (j + 1) + 1))) i))).
  {  intro j. apply qeq_imp_qeqT. assert (H1 : (4 * m + 3 - 2 * (j + 1) = 4 * m + 1 - 2 * j)%nat) by lia.
       assert (H2 : (2 * (j + 1) + 1 = 2 * j + 3)%nat) by lia.
       setoid_replace (q_fact (4 * m + 3 - 2 * (j + 1))) with (q_fact (4 * m + 1 - 2 * j)).
       2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. exact H1. }
       setoid_replace (q_fact (2 * (j + 1) + 1)) with (q_fact (2 * j + 3)).
       2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. exact H2. }
       reflexivity. }
  rewrite (qeqT_imp_qeq _ _ (sum_upto_ext m            (fun j => 1 / (q_fact (4 * m + 1 - 2 * j) * q_fact (2 * j + 3)))            (fun j => 1 / (q_fact (4 * m + 3 - 2 * (j + 1)) * q_fact (2 * (j + 1) + 1))) Hpre1538_23)).
  (* Merge the tail terms: -2/((4m+4)! * 0!) == -2*E_0 and 2/((4m+3)! * 1!) == 2*O_0.
     Goal: -2*Σ_{j=0}^{m-1}(E_{j+1}) + 2*Σ_{j=0}^{m-1}(O_{j+1}) - 2*E_0 + 2*O_0 == the right side.
     By [HshiftE]: Σ_{j=0}^{m-1}(E_{j+1}) == Σ_{k=0}^{m}(E_k) - E_0 (with E_0 = 1/((4m+4)! * 0!)). *)
  setoid_replace (sum_upto m (fun j => 1 / (q_fact (4 * m + 4 - 2 * (j + 1)) * q_fact (2 * (j + 1)))))
    with (sum_upto (m + 1) (fun k => 1 / (q_fact (4 * m + 4 - 2 * k) * q_fact (2 * k))) -
           1 / (q_fact (4 * m + 4 - 2 * 0) * q_fact (2 * 0))).
  2: { exact HshiftE. }
  (* Goal: -2*(Σ_{k=0}^{m}(E_k) - E_0) + 2*Σ_{j=0}^{m-1}(O_{j+1}) - 2*E_0 + 2*O_0 == the right side.
     Shift the O part likewise: Σ_{j=0}^{m-1}(O_{j+1}) == Σ_{k=0}^{m}(O_k) - O_0. *)
  assert (HshiftO : sum_upto m (fun j => 1 / (q_fact (4 * m + 3 - 2 * (j + 1)) * q_fact (2 * (j + 1) + 1))) ==
                    sum_upto (m + 1) (fun k => 1 / (q_fact (4 * m + 3 - 2 * k) * q_fact (2 * k + 1))) -
                    1 / (q_fact (4 * m + 3 - 2 * 0) * q_fact (2 * 0 + 1))).
  { apply (qeqT_imp_qeq _ _ (sum_upto_shift m (fun k => 1 / (q_fact (4 * m + 3 - 2 * k) * q_fact (2 * k + 1))))). }
  setoid_replace (sum_upto m (fun j => 1 / (q_fact (4 * m + 3 - 2 * (j + 1)) * q_fact (2 * (j + 1) + 1))))
    with (sum_upto (m + 1) (fun k => 1 / (q_fact (4 * m + 3 - 2 * k) * q_fact (2 * k + 1))) -
           1 / (q_fact (4 * m + 3 - 2 * 0) * q_fact (2 * 0 + 1))).
  2: { exact HshiftO. }
  (* Goal: -2*(ΣE_k - E_0) + 2*(ΣO_k - O_0) - 2*E_0 + 2*O_0 == the right side,
     which expands to -2*ΣE_k + 2*E_0 + 2*ΣO_k - 2*O_0 - 2*E_0 + 2*O_0 == -2*ΣE_k + 2*ΣO_k
     == the right side (E_0/O_0 cancel by [ring]). *)
  (* Reduce the literals E_0 = 1/((4m+4)!*0!) and O_0 = 1/((4m+3)!*1!), which coincide with the tail terms (by [ring]). *)
  (* The goal is now -2*(Σ_{k=0}^{m}(E_k) - E_0) + 2*(Σ_{k=0}^{m}(O_k) - O_0) - 2/((4m+4)!*0!) + 2/((4m+3)!*1!) == the right side;
     expanding by [ring]: -2ΣE + 2E_0 + 2ΣO - 2O_0 - 2E_0 + 2O_0 == -2ΣE + 2ΣO (E_0/O_0 cancel). *)
  (* Conclude with [Hmoved]: 2ΣO - 2ΣE == E_{m+1}, and E_{m+1} == 1/((2m+2)!(2m+2)!) (denominators swapped). *)
  transitivity (2 * sum_upto (m + 1)
                  (fun k => 1 / (q_fact (4 * m + 3 - 2 * k) * q_fact (2 * k + 1))) -
                2 * sum_upto (m + 1)
                  (fun k => 1 / (q_fact (4 * m + 4 - 2 * k) * q_fact (2 * k)))).
  - (* The goal's left side == 2ΣO - 2ΣE (the E_0/O_0 terms cancel); assert the intermediate equality, then close by [exact]. *)
    assert (Htmp : - 2 * (sum_upto (m + 1) (fun k => 1 / (q_fact (4 * m + 4 - 2 * k) * q_fact (2 * k))) +
                          - (1 / (q_fact (4 * m + 4) * q_fact 0))) +
                   2 * (sum_upto (m + 1) (fun k => 1 / (q_fact (4 * m + 3 - 2 * k) * q_fact (2 * k + 1))) -
                          (1 / (q_fact (4 * m + 3 - 2 * 0) * q_fact (2 * 0 + 1)))) -
                   2 / (q_fact (4 * m + 4) * q_fact 0) +
                   2 / (q_fact (4 * m + 3) * q_fact 1) ==
                   2 * sum_upto (m + 1) (fun k => 1 / (q_fact (4 * m + 3 - 2 * k) * q_fact (2 * k + 1))) -
                   2 * sum_upto (m + 1) (fun k => 1 / (q_fact (4 * m + 4 - 2 * k) * q_fact (2 * k)))).
    { unfold Qminus. unfold Qdiv.
      (* Reduce the O_0 literal with [change] on the whole 1/(...) term (convertible: 4m+3-2*0 == 4m+3 and 2*0+1 == 1). *)
      change (1 / (q_fact (4 * m + 3 - 2 * 0) * q_fact (2 * 0 + 1)))
        with (1 / (q_fact (4 * m + 3) * q_fact 1)).
      (* [ring_simplify] distributes -2*(Σ + ...) and normalizes the 1*x factors; [ring] then cancels E_0/O_0. *)
      ring_simplify.
      (* After [ring_simplify] the O_0 term remains as 2 * Qinv (q_fact (4m+3-2*0) * q_fact (2*0+1)), so reduce it with [change]. *)
      (* The O_0 term, -2 * / (q_fact (4m+3-2*0) * q_fact (2*0+1)), is reduced as a whole with [setoid_replace] ([Qinv] is Proper). *)
      setoid_replace (- 2 * / (q_fact (4 * m + 3 - 2 * 0) * q_fact (2 * 0 + 1)))
        with (- 2 * / (q_fact (4 * m + 3) * q_fact 1)).
      2: { setoid_replace (q_fact (4 * m + 3 - 2 * 0)) with (q_fact (4 * m + 3)).
           2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. lia. }
           setoid_replace (q_fact (2 * 0 + 1)) with (q_fact 1).
           2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. lia. }
           reflexivity. }
      ring. }
    (* The E_0/O_0 literals in the goal of [vander_4m4] (1/(q_fact (4m+4-2*0) * q_fact (2*0)) and friends) are not yet reduced; reduce them before [exact Htmp]. *)
    setoid_replace (1 / (q_fact (4 * m + 4 - 2 * 0) * q_fact (2 * 0)))
      with (1 / (q_fact (4 * m + 4) * q_fact 0)).
    2: { setoid_replace (q_fact (4 * m + 4 - 2 * 0)) with (q_fact (4 * m + 4)).
         2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. lia. }
         setoid_replace (q_fact (2 * 0)) with (q_fact 0).
         2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. lia. }
         reflexivity. }
    setoid_replace (1 / (q_fact (4 * m + 3 - 2 * 0) * q_fact (2 * 0 + 1)))
      with (1 / (q_fact (4 * m + 3) * q_fact 1)).
    2: { setoid_replace (q_fact (4 * m + 3 - 2 * 0)) with (q_fact (4 * m + 3)).
         2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. lia. }
         setoid_replace (q_fact (2 * 0 + 1)) with (q_fact 1).
         2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. lia. }
         reflexivity. }
    unfold Qminus. unfold Qdiv.
    ring_simplify.
    ring.
  - (* 2ΣO - 2ΣE == E_{m+1}, by [Hmoved]. *)
    transitivity (1 / (q_fact (2 * (m + 1)) * q_fact (4 * m + 4 - 2 * (m + 1)))).
    + (* Reorder the factors of the O part of the goal's left side ((4m+3-2k)!(2k+1)! -> (2k+1)!(4m+3-2k)!) to match [Hmoved]. *)
      assert (Hpre1538_22 : (forall i,QeqT ( (fun k => 1 / (q_fact (4 * m + 3 - 2 * k) * q_fact (2 * k + 1))) i ) ( (fun k => 1 / (q_fact (2 * k + 1) * q_fact (4 * m + 3 - 2 * k))) i))).
        {  intro k. apply qeq_imp_qeqT. field.
             all: repeat (split; [intro Hz1545; destruct (q_neq_of_lt _ (q_fact_pos _) (qeq_imp_qeqT _ _ Hz1545)) | idtac]);
                  intro Hz1545; destruct (q_neq_of_lt _ (q_fact_pos _) (qeq_imp_qeqT _ _ Hz1545)). }
      { rewrite (qeqT_imp_qeq _ _ (sum_upto_ext (m + 1)                  (fun k => 1 / (q_fact (4 * m + 3 - 2 * k) * q_fact (2 * k + 1)))                  (fun k => 1 / (q_fact (2 * k + 1) * q_fact (4 * m + 3 - 2 * k))) Hpre1538_22)).
        assert (Hpre1538_21 : (forall i,QeqT ( (fun k => 1 / (q_fact (4 * m + 4 - 2 * k) * q_fact (2 * k))) i ) ( (fun k => 1 / (q_fact (2 * k) * q_fact (4 * m + 4 - 2 * k))) i))).
        {  intro k. apply qeq_imp_qeqT. field.
             all: repeat (split; [intro Hz1545; destruct (q_neq_of_lt _ (q_fact_pos _) (qeq_imp_qeqT _ _ Hz1545)) | idtac]);
                  intro Hz1545; destruct (q_neq_of_lt _ (q_fact_pos _) (qeq_imp_qeqT _ _ Hz1545)). }
        rewrite (qeqT_imp_qeq _ _ (sum_upto_ext (m + 1)                  (fun k => 1 / (q_fact (4 * m + 4 - 2 * k) * q_fact (2 * k)))                  (fun k => 1 / (q_fact (2 * k) * q_fact (4 * m + 4 - 2 * k))) Hpre1538_21)).
        exact Hmoved. }
    + (* E_{m+1} == the right side: swap denominators, 1/((2m+2)!(2m+2)!) == 1/((2(m+1))!(4m+4−2(m+1))!). *)
      { assert (Hmid : (2 * (m + 1) = 2 * m + 2)%nat) by lia.
        assert (Hmid2 : (4 * m + 4 - 2 * (m + 1) = 2 * m + 2)%nat) by lia.
        setoid_replace (q_fact (2 * (m + 1))) with (q_fact (2 * m + 2)).
        2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. exact Hmid. }
        setoid_replace (q_fact (4 * m + 4 - 2 * (m + 1))) with (q_fact (2 * m + 2)).
        2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. exact Hmid2. }
        reflexivity. }
Qed.

End QExpEOSplit.
(* ============ The pairing argument ============
   [row_pair_main]: closing the row difference (assembled in layers: the a^(4m+6) terms cancel,
   then [vander_4m2]/[vander_4m4], with the low layers closed by reflexivity).
   [ksum_diff_row]: the difference of [corr] == the right side ([corr_diff_expand] plus reindexing
   plus [row_pair_main]) — this completes the pairing argument. *)
Lemma esq_row_nat_eq2 : forall (N i1 i2 : nat) (a : Q),
  i1 = i2 ->QeqT ( esq_row N i1 a ) ( esq_row N i2 a).
Proof. intros. subst. apply qeq_imp_qeqT. reflexivity. Qed.

Lemma sum_upto_opp2 : forall (n : nat) (f : nat -> Q),QeqT (
  sum_upto n (fun j => - (2 * f j)) ) ( - (2 * sum_upto n f)).
Proof.
  intros n f.
  apply qeq_imp_qeqT.
  induction n as [| n' IH]; simpl.
  - ring.
  - setoid_rewrite IH. ring.
Qed.

Lemma esq_pair : forall (m j : nat) (a : Q), (j < m)%nat ->QeqT (
  - 2 * esq_row (2 * m + 1 - (j + 1)) (j + 1 + 2) a
  + 2 * esq_row (2 * m - j) (j + 1) a ) (
  - 2 * q_pow a (4 * m + 4) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 4))
  - 2 * q_pow a (4 * m + 6) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 6))).
Proof.
  intros m j a Hj.
  apply qeq_imp_qeqT.
  assert (Ha : (2 * m + 1 - (j + 1) = 2 * m - j)%nat) by lia.
  assert (Hb : (j + 1 + 2 = j + 3)%nat) by lia.
  rewrite Ha. rewrite Hb.
  (* esq_row (2m−j) (j+3) == esq_row (2m−j) (j+1) + T_{j+2} + T_{j+3}, by two applications of [esq_row_succ]. *)
  assert (Hexp : esq_row (2 * m - j) (j + 3) a ==
          esq_row (2 * m - j) (j + 1) a +
          q_pow a (2 * (2 * m - j) + 2 * Datatypes.S (j + 1)) / (q_fact (2 * (2 * m - j)) * q_fact (2 * Datatypes.S (j + 1))) +
          q_pow a (2 * (2 * m - j) + 2 * Datatypes.S (j + 2)) / (q_fact (2 * (2 * m - j)) * q_fact (2 * Datatypes.S (j + 2)))).
  { assert (Hn : (j + 3 = Datatypes.S (j + 2))%nat) by lia.
    rewrite Hn.
    rewrite (qeqT_imp_qeq _ _ (esq_row_succ (2 * m - j) (j + 2) a)).
    setoid_replace (esq_row (2 * m - j) (j + 2) a) with (esq_row (2 * m - j) (Datatypes.S (j + 1)) a).
    2: { apply qeqT_imp_qeq. apply esq_row_nat_eq2. lia. }
    rewrite (qeqT_imp_qeq _ _ (esq_row_succ (2 * m - j) (j + 1) a)).
    reflexivity. }
  rewrite Hexp.
  (* T_{j+2} == q_pow a (4m+4)/((4m−2j)!(2j+4)!), after reducing the [q_pow]/[q_fact] arguments. *)
  assert (Ht2 : q_pow a (2 * (2 * m - j) + 2 * Datatypes.S (j + 1)) / (q_fact (2 * (2 * m - j)) * q_fact (2 * Datatypes.S (j + 1))) ==
                q_pow a (4 * m + 4) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 4))).
  { setoid_replace (q_pow a (2 * (2 * m - j) + 2 * Datatypes.S (j + 1))) with (q_pow a (4 * m + 4)).
    2: { apply (q_pow_comp_proper a a (Qeq_refl a) (2 * (2 * m - j) + 2 * Datatypes.S (j + 1))%nat (4 * m + 4)%nat). lia. }
    setoid_replace (q_fact (2 * (2 * m - j))) with (q_fact (4 * m - 2 * j)).
    2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. lia. }
    setoid_replace (q_fact (2 * Datatypes.S (j + 1))) with (q_fact (2 * j + 4)).
    2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. lia. }
    reflexivity. }
  (* T_{j+3} == q_pow a (4m+6)/((4m−2j)!(2j+6)!). *)
  assert (Ht3 : q_pow a (2 * (2 * m - j) + 2 * Datatypes.S (j + 2)) / (q_fact (2 * (2 * m - j)) * q_fact (2 * Datatypes.S (j + 2))) ==
                q_pow a (4 * m + 6) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 6))).
  { setoid_replace (q_pow a (2 * (2 * m - j) + 2 * Datatypes.S (j + 2))) with (q_pow a (4 * m + 6)).
    2: { apply (q_pow_comp_proper a a (Qeq_refl a) (2 * (2 * m - j) + 2 * Datatypes.S (j + 2))%nat (4 * m + 6)%nat). lia. }
    setoid_replace (q_fact (2 * (2 * m - j))) with (q_fact (4 * m - 2 * j)).
    2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. lia. }
    setoid_replace (q_fact (2 * Datatypes.S (j + 2))) with (q_fact (2 * j + 6)).
    2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. lia. }
    reflexivity. }
  setoid_rewrite Ht2.
  setoid_rewrite Ht3.
  unfold Qdiv in *. ring.
Qed.

Lemma osq_pair : forall (m j : nat) (a : Q), (j < m)%nat ->QeqT (
  2 * osq_row (2 * m - (j + 1)) (j + 1 + 1) a
  - 2 * osq_row (2 * m - 1 - j) j a ) (
  2 * q_pow a (4 * m + 2) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 3))
  + 2 * q_pow a (4 * m + 4) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 5))).
Proof.
  intros m j a Hj.
  apply qeq_imp_qeqT.
  assert (Ha : (2 * m - (j + 1) = 2 * m - 1 - j)%nat) by lia.
  assert (Hb : (j + 1 + 1 = j + 2)%nat) by lia.
  rewrite Ha. rewrite Hb.
  (* osq_row (2m−1−j) (j+2) == osq_row (2m−1−j) j + T'_{j+1} + T'_{j+2}, by two applications of [osq_row_succ]. *)
  assert (Hexp : osq_row (2 * m - 1 - j) (j + 2) a ==
          osq_row (2 * m - 1 - j) j a +
          q_pow a (2 * (2 * m - 1 - j) + 2 * Datatypes.S j + 2) / (q_fact (2 * (2 * m - 1 - j) + 1) * q_fact (2 * Datatypes.S j + 1)) +
          q_pow a (2 * (2 * m - 1 - j) + 2 * Datatypes.S (j + 1) + 2) / (q_fact (2 * (2 * m - 1 - j) + 1) * q_fact (2 * Datatypes.S (j + 1) + 1))).
  { assert (Hn : (j + 2 = Datatypes.S (j + 1))%nat) by lia.
    rewrite Hn.
    rewrite (qeqT_imp_qeq _ _ (osq_row_succ (2 * m - 1 - j) (j + 1) a)).
    setoid_replace (osq_row (2 * m - 1 - j) (j + 1) a) with (osq_row (2 * m - 1 - j) (Datatypes.S j) a).
    2: { apply qeqT_imp_qeq. apply osq_row_nat_eq2. lia. }
    rewrite (qeqT_imp_qeq _ _ (osq_row_succ (2 * m - 1 - j) j a)).
    reflexivity. }
  rewrite Hexp.
  (* T'_{j+1} == q_pow a (4m+2)/((4m−1−2j)!(2j+3)!). *)
  assert (Ht2 : q_pow a (2 * (2 * m - 1 - j) + 2 * Datatypes.S j + 2) / (q_fact (2 * (2 * m - 1 - j) + 1) * q_fact (2 * Datatypes.S j + 1)) ==
                q_pow a (4 * m + 2) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 3))).
  { setoid_replace (q_pow a (2 * (2 * m - 1 - j) + 2 * Datatypes.S j + 2)) with (q_pow a (4 * m + 2)).
    2: { apply (q_pow_comp_proper a a (Qeq_refl a) (2 * (2 * m - 1 - j) + 2 * Datatypes.S j + 2)%nat (4 * m + 2)%nat). lia. }
    setoid_replace (q_fact (2 * (2 * m - 1 - j) + 1)) with (q_fact (4 * m - 1 - 2 * j)).
    2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. lia. }
    setoid_replace (q_fact (2 * Datatypes.S j + 1)) with (q_fact (2 * j + 3)).
    2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. lia. }
    reflexivity. }
  (* T'_{j+2} == q_pow a (4m+4)/((4m−1−2j)!(2j+5)!). *)
  assert (Ht3 : q_pow a (2 * (2 * m - 1 - j) + 2 * Datatypes.S (j + 1) + 2) / (q_fact (2 * (2 * m - 1 - j) + 1) * q_fact (2 * Datatypes.S (j + 1) + 1)) ==
                q_pow a (4 * m + 4) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 5))).
  { setoid_replace (q_pow a (2 * (2 * m - 1 - j) + 2 * Datatypes.S (j + 1) + 2)) with (q_pow a (4 * m + 4)).
    2: { apply (q_pow_comp_proper a a (Qeq_refl a) (2 * (2 * m - 1 - j) + 2 * Datatypes.S (j + 1) + 2)%nat (4 * m + 4)%nat). lia. }
    setoid_replace (q_fact (2 * (2 * m - 1 - j) + 1)) with (q_fact (4 * m - 1 - 2 * j)).
    2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. lia. }
    setoid_replace (q_fact (2 * Datatypes.S (j + 1) + 1)) with (q_fact (2 * j + 5)).
    2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. lia. }
    reflexivity. }
  setoid_rewrite Ht2.
  setoid_rewrite Ht3.
  unfold Qdiv in *. ring.
Qed.

Lemma esq_row_diff_closed : forall (m : nat) (a : Q), (1 <= m)%nat ->QeqT (
  sum_upto m (fun j => - 2 * esq_row (2 * m + 1 - j) (j + 2) a
                      + 2 * esq_row (2 * m - j) (j + 1) a) ) (
  2 * esq_row (m + 1) m a - 2 * esq_row (2 * m + 1) 2 a
  - 2 * sum_upto (m - 1) (fun j => q_pow a (4 * m + 4) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 4)))
  - 2 * sum_upto (m - 1) (fun j => q_pow a (4 * m + 6) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 6)))).
Proof.
  intros m a Hm.
  apply qeq_imp_qeqT.
  assert (Hm1 : ((m - 1) + 1 = m)%nat) by lia.
  assert (Hms : (m = Datatypes.S (m - 1))%nat) by lia.
  (* 1. Split f into the esq- and esq+ parts. *)
  rewrite (qeqT_imp_qeq _ _ (sum_upto_plus m            (fun j => - 2 * esq_row (2 * m + 1 - j) (j + 2) a)            (fun j => 2 * esq_row (2 * m - j) (j + 1) a))).
  (* 2. The sum of esq- == esq-@0 + the sum of esq-@(j+1) over j < m−1 (peel the first term with [sum_upto_shift]). *)
  assert (Hsh : sum_upto m (fun j => - 2 * esq_row (2 * m + 1 - j) (j + 2) a) ==
                (- 2 * esq_row (2 * m + 1) 2 a) +
                sum_upto (m - 1) (fun j => - 2 * esq_row (2 * m + 1 - (j + 1)) ((j + 1) + 2) a)).
  { rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq m ((m - 1) + 1)              (fun j => - 2 * esq_row (2 * m + 1 - j) (j + 2) a) (eq_sym Hm1))).
    setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_shift (m - 1)                      (fun j => - 2 * esq_row (2 * m + 1 - j) (j + 2) a))).
    assert (Hf0 : (fun k : nat => - 2 * esq_row (2 * m + 1 - k) (k + 2) a) 0%nat ==
                  - 2 * esq_row (2 * m + 1) 2 a).
    { change ((fun k : nat => - 2 * esq_row (2 * m + 1 - k) (k + 2) a) 0%nat) with
        (- 2 * esq_row (2 * m + 1 - 0) (0 + 2) a).
      assert (Hn1 : (2 * m + 1 - 0 = 2 * m + 1)%nat) by lia.
      assert (Hn2 : (0 + 2 = 2)%nat) by lia.
      rewrite Hn1. rewrite Hn2.
      reflexivity. }
    setoid_rewrite Hf0.
    unfold Qminus. ring. }
  (* 3. The sum of esq+ == the sum of esq+@j over j < m−1 + esq+@(m−1) (peel the last term). *)
  assert (Hsl : sum_upto m (fun j => 2 * esq_row (2 * m - j) (j + 1) a) ==
                sum_upto (m - 1) (fun j => 2 * esq_row (2 * m - j) (j + 1) a) +
                2 * esq_row (2 * m - (m - 1)) (m - 1 + 1) a).
  { rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq m (Datatypes.S (m - 1))              (fun j => 2 * esq_row (2 * m - j) (j + 1) a) Hms)).
    reflexivity. }
  (* 4. Substitute and regroup (prove [Hre] by [ring], pulling the sums together). *)
  setoid_rewrite Hsh.
  setoid_rewrite Hsl.
  assert (Hre : ((- 2 * esq_row (2 * m + 1) 2 a) +
                 sum_upto (m - 1) (fun j => - 2 * esq_row (2 * m + 1 - (j + 1)) ((j + 1) + 2) a)) +
                (sum_upto (m - 1) (fun j => 2 * esq_row (2 * m - j) (j + 1) a) +
                 2 * esq_row (2 * m - (m - 1)) (m - 1 + 1) a) ==
                (- 2 * esq_row (2 * m + 1) 2 a) +
                (2 * esq_row (2 * m - (m - 1)) (m - 1 + 1) a) +
                (sum_upto (m - 1) (fun j => - 2 * esq_row (2 * m + 1 - (j + 1)) ((j + 1) + 2) a) +
                 sum_upto (m - 1) (fun j => 2 * esq_row (2 * m - j) (j + 1) a))).
  { ring. }
  setoid_rewrite Hre.
  setoid_rewrite <- (qeqT_imp_qeq _ _ (sum_upto_plus (m - 1)                      (fun j => - 2 * esq_row (2 * m + 1 - (j + 1)) ((j + 1) + 2) a)                      (fun j => 2 * esq_row (2 * m - j) (j + 1) a))).
  (* 5. Apply [esq_pair] pointwise (each paired summand becomes -2*T4 - 2*T6). *)
  assert (Hpre1538_20 : (forall i : nat, NatLe (Datatypes.S i) (m - 1) ->QeqT ( (fun j => - 2 * esq_row (2 * m + 1 - (j + 1)) ((j + 1) + 2) a + 2 * esq_row (2 * m - j) (j + 1) a) i ) ( (fun j => - 2 * q_pow a (4 * m + 4) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 4))                            - 2 * q_pow a (4 * m + 6) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 6))) i))).
  {  intros j Hj. apply NatLe_drop in Hj. apply qeq_imp_qeqT. apply qeqT_imp_qeq. apply (esq_pair m j a). lia. }
  setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_ext_below (m - 1)                    (fun j => - 2 * esq_row (2 * m + 1 - (j + 1)) ((j + 1) + 2) a
                            + 2 * esq_row (2 * m - j) (j + 1) a)
                    (fun j => - 2 * q_pow a (4 * m + 4) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 4))                            - 2 * q_pow a (4 * m + 6) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 6))) Hpre1538_20)).
  (* 6. Factor out -2 (pointwise (-2*a)/D == -2*(a/D), then [sum_upto_plus]/[sum_upto_scale]). *)
  assert (Hstep4 : forall j, - 2 * q_pow a (4 * m + 4) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 4)) ==
                            - 2 * (q_pow a (4 * m + 4) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 4)))).
  { intro j. unfold Qdiv. ring. }
  assert (Hstep6 : forall j, - 2 * q_pow a (4 * m + 6) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 6)) ==
                            - 2 * (q_pow a (4 * m + 6) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 6)))).
  { intro j. unfold Qdiv. ring. }
  assert (Hsum : sum_upto (m - 1) (fun j =>
                    - 2 * q_pow a (4 * m + 4) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 4))
                    - 2 * q_pow a (4 * m + 6) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 6))) ==
                  - 2 * sum_upto (m - 1) (fun j => q_pow a (4 * m + 4) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 4)))
                  - 2 * sum_upto (m - 1) (fun j => q_pow a (4 * m + 6) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 6)))).
  assert (Hpre1538_19 : (forall i : nat, NatLe (Datatypes.S i) (m - 1) ->QeqT ( (fun j => - 2 * q_pow a (4 * m + 4) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 4)) - 2 * q_pow a (4 * m + 6) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 6))) i ) ( (fun j => - 2 * (q_pow a (4 * m + 4) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 4)))                              - 2 * (q_pow a (4 * m + 6) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 6)))) i))).
    {  intros j Hj. apply NatLe_drop in Hj. apply qeq_imp_qeqT. unfold Qdiv. ring. }
  { setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_ext_below (m - 1)                      (fun j => - 2 * q_pow a (4 * m + 4) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 4))
                              - 2 * q_pow a (4 * m + 6) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 6)))
                      (fun j => - 2 * (q_pow a (4 * m + 4) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 4)))                              - 2 * (q_pow a (4 * m + 6) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 6)))) Hpre1538_19)).
    setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_plus (m - 1)                      (fun j => - 2 * (q_pow a (4 * m + 4) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 4))))                      (fun j => - (2 * (q_pow a (4 * m + 6) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 6))))))).
    setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_scale_neg2 (m - 1) (fun j => q_pow a (4 * m + 4) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 4))))).
    setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_opp2 (m - 1) (fun j => q_pow a (4 * m + 6) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 6))))).
    ring. }
  setoid_rewrite Hsum.
  (* 7. Reduce the last term: esq+@(m−1) == 2*esq_row (m+1) m. *)
  assert (Hma : (2 * m - (m - 1) = m + 1)%nat) by lia.
  assert (Hmb : (m - 1 + 1 = m)%nat) by lia.
  rewrite Hma. rewrite Hmb.
  (* 8. Assemble with [ring]. *)
  unfold Qdiv in *. ring.
Qed.

Lemma osq_row_diff_closed : forall (m : nat) (a : Q), (1 <= m)%nat ->QeqT (
  sum_upto m (fun j => 2 * osq_row (2 * m - j) (j + 1) a
                      - 2 * osq_row (2 * m - 1 - j) j a) ) (
  - 2 * osq_row m (m - 1) a + 2 * osq_row (2 * m) 1 a
  + 2 * sum_upto (m - 1) (fun j => q_pow a (4 * m + 2) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 3)))
  + 2 * sum_upto (m - 1) (fun j => q_pow a (4 * m + 4) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 5)))).
Proof.
  intros m a Hm.
  apply qeq_imp_qeqT.
  assert (Hm1 : ((m - 1) + 1 = m)%nat) by lia.
  assert (Hms : (m = Datatypes.S (m - 1))%nat) by lia.
  (* 1. Split f into the osq+ and osq- parts (the goal writes A - B, i.e. A + Qopp B, so the second summand is used in [Qopp] form). *)
  rewrite (qeqT_imp_qeq _ _ (sum_upto_plus m            (fun j => 2 * osq_row (2 * m - j) (j + 1) a)            (fun j => - (2 * osq_row (2 * m - 1 - j) j a)))).
  (* 2. The sum of osq+ == osq+@0 + the sum of osq+@(j+1) over j < m−1 (peel the first term with [sum_upto_shift]). *)
  assert (Hsh : sum_upto m (fun j => 2 * osq_row (2 * m - j) (j + 1) a) ==
                (2 * osq_row (2 * m) 1 a) +
                sum_upto (m - 1) (fun j => 2 * osq_row (2 * m - (j + 1)) ((j + 1) + 1) a)).
  { rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq m ((m - 1) + 1)              (fun j => 2 * osq_row (2 * m - j) (j + 1) a) (eq_sym Hm1))).
    setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_shift (m - 1)                      (fun j => 2 * osq_row (2 * m - j) (j + 1) a))).
    assert (Hf0 : (fun k : nat => 2 * osq_row (2 * m - k) (k + 1) a) 0%nat ==
                  2 * osq_row (2 * m) 1 a).
    { change ((fun k : nat => 2 * osq_row (2 * m - k) (k + 1) a) 0%nat) with
        (2 * osq_row (2 * m - 0) (0 + 1) a).
      assert (Hn1 : (2 * m - 0 = 2 * m)%nat) by lia.
      assert (Hn2 : (0 + 1 = 1)%nat) by lia.
      rewrite Hn1. rewrite Hn2.
      reflexivity. }
    setoid_rewrite Hf0.
    unfold Qminus. ring. }
  (* 3. The sum of osq- == the sum of osq-@j over j < m−1 + osq-@(m−1) (peel the last term). *)
  assert (Hsl : sum_upto m (fun j => - (2 * osq_row (2 * m - 1 - j) j a)) ==
                sum_upto (m - 1) (fun j => - (2 * osq_row (2 * m - 1 - j) j a)) +
                (- (2 * osq_row (2 * m - 1 - (m - 1)) (m - 1) a))).
  { rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq m (Datatypes.S (m - 1))              (fun j => - (2 * osq_row (2 * m - 1 - j) j a)) Hms)).
    reflexivity. }
  (* 4. Substitute and regroup. *)
  setoid_rewrite Hsh.
  setoid_rewrite Hsl.
  assert (Hre : ((2 * osq_row (2 * m) 1 a) +
                 sum_upto (m - 1) (fun j => 2 * osq_row (2 * m - (j + 1)) ((j + 1) + 1) a)) +
                (sum_upto (m - 1) (fun j => - (2 * osq_row (2 * m - 1 - j) j a)) +
                 (- (2 * osq_row (2 * m - 1 - (m - 1)) (m - 1) a))) ==
                (2 * osq_row (2 * m) 1 a) +
                (- (2 * osq_row (2 * m - 1 - (m - 1)) (m - 1) a)) +
                (sum_upto (m - 1) (fun j => 2 * osq_row (2 * m - (j + 1)) ((j + 1) + 1) a) +
                 sum_upto (m - 1) (fun j => - (2 * osq_row (2 * m - 1 - j) j a)))).
  { ring. }
  setoid_rewrite Hre.
  setoid_rewrite <- (qeqT_imp_qeq _ _ (sum_upto_plus (m - 1)                      (fun j => 2 * osq_row (2 * m - (j + 1)) ((j + 1) + 1) a)                      (fun j => - (2 * osq_row (2 * m - 1 - j) j a)))).
  (* 5. Apply [osq_pair] pointwise (each paired summand becomes 2*T'_{4m+2} + 2*T'_{4m+4}). *)
  assert (Hpre1538_18 : (forall i : nat, NatLe (Datatypes.S i) (m - 1) ->QeqT ( (fun j => 2 * osq_row (2 * m - (j + 1)) ((j + 1) + 1) a - 2 * osq_row (2 * m - 1 - j) j a) i ) ( (fun j => 2 * q_pow a (4 * m + 2) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 3))                            + 2 * q_pow a (4 * m + 4) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 5))) i))).
  {  intros j Hj. apply NatLe_drop in Hj. apply qeq_imp_qeqT. apply qeqT_imp_qeq. apply (osq_pair m j a). lia. }
  setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_ext_below (m - 1)                    (fun j => 2 * osq_row (2 * m - (j + 1)) ((j + 1) + 1) a
                            - 2 * osq_row (2 * m - 1 - j) j a)
                    (fun j => 2 * q_pow a (4 * m + 2) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 3))                            + 2 * q_pow a (4 * m + 4) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 5))) Hpre1538_18)).
  (* 6. Factor out 2 (pointwise (2*a)/D == 2*(a/D), then [sum_upto_plus]/[sum_upto_scale]). *)
  assert (Hstep2 : forall j, 2 * q_pow a (4 * m + 2) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 3)) ==
                            2 * (q_pow a (4 * m + 2) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 3)))).
  { intro j. unfold Qdiv. ring. }
  assert (Hstep4 : forall j, 2 * q_pow a (4 * m + 4) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 5)) ==
                            2 * (q_pow a (4 * m + 4) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 5)))).
  { intro j. unfold Qdiv. ring. }
  assert (Hsum : sum_upto (m - 1) (fun j =>
                    2 * q_pow a (4 * m + 2) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 3))
                    + 2 * q_pow a (4 * m + 4) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 5))) ==
                  2 * sum_upto (m - 1) (fun j => q_pow a (4 * m + 2) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 3)))
                  + 2 * sum_upto (m - 1) (fun j => q_pow a (4 * m + 4) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 5)))).
  assert (Hpre1538_17 : (forall i : nat, NatLe (Datatypes.S i) (m - 1) ->QeqT ( (fun j => 2 * q_pow a (4 * m + 2) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 3)) + 2 * q_pow a (4 * m + 4) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 5))) i ) ( (fun j => 2 * (q_pow a (4 * m + 2) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 3)))                              + 2 * (q_pow a (4 * m + 4) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 5)))) i))).
    {  intros j Hj. apply NatLe_drop in Hj. apply qeq_imp_qeqT. unfold Qdiv. ring. }
  { setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_ext_below (m - 1)                      (fun j => 2 * q_pow a (4 * m + 2) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 3))
                              + 2 * q_pow a (4 * m + 4) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 5)))
                      (fun j => 2 * (q_pow a (4 * m + 2) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 3)))                              + 2 * (q_pow a (4 * m + 4) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 5)))) Hpre1538_17)).
    setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_plus (m - 1)                      (fun j => 2 * (q_pow a (4 * m + 2) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 3))))                      (fun j => 2 * (q_pow a (4 * m + 4) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 5)))))).
    setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_scale (m - 1) 2 (fun j => q_pow a (4 * m + 2) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 3))))).
    setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_scale (m - 1) 2 (fun j => q_pow a (4 * m + 4) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 5))))).
    ring. }
  setoid_rewrite Hsum.
  (* 7. Reduce the last term: osq-@(m−1) == -2*osq_row m (m−1). *)
  assert (Hma : (2 * m - 1 - (m - 1) = m)%nat) by lia.
  rewrite Hma.
  (* 8. Assemble with [ring]. *)
  unfold Qdiv in *. ring.
Qed.

Lemma row_pair_esq2_expand : forall (m : nat) (a : Q),QeqT (
  esq_row (2 * m + 1) 2 a ) (
  q_pow a (4 * m + 2) / (q_fact (4 * m + 2) * q_fact 0) +
  q_pow a (4 * m + 4) / (q_fact (4 * m + 2) * q_fact 2) +
  q_pow a (4 * m + 6) / (q_fact (4 * m + 2) * q_fact 4)).
Proof.
  intros m a.
  apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (esq_row_succ (2 * m + 1) 1 a)).
  rewrite (qeqT_imp_qeq _ _ (esq_row_succ (2 * m + 1) 0 a)).
  change (esq_row (2 * m + 1) 0 a) with
    (q_pow a (2 * (2 * m + 1)) / (q_fact (2 * (2 * m + 1)) * q_fact 0)).
  assert (Hn0 : (2 * (2 * m + 1) = 4 * m + 2)%nat) by lia.
  assert (Hn1 : (2 * (2 * m + 1) + 2 * Datatypes.S 0 = 4 * m + 4)%nat) by lia.
  assert (Hn2 : (2 * (2 * m + 1) + 2 * Datatypes.S 1 = 4 * m + 6)%nat) by lia.
  assert (Hf1 : (2 * Datatypes.S 0 = 2)%nat) by lia.
  assert (Hf2 : (2 * Datatypes.S 1 = 4)%nat) by lia.
  setoid_replace (q_pow a (2 * (2 * m + 1))) with (q_pow a (4 * m + 2)).
  2: { apply (q_pow_comp_proper a a (Qeq_refl a) (2 * (2 * m + 1))%nat (4 * m + 2)%nat). exact Hn0. }
  setoid_replace (q_pow a (2 * (2 * m + 1) + 2 * Datatypes.S 0)) with (q_pow a (4 * m + 4)).
  2: { apply (q_pow_comp_proper a a (Qeq_refl a) (2 * (2 * m + 1) + 2 * Datatypes.S 0)%nat (4 * m + 4)%nat). exact Hn1. }
  setoid_replace (q_pow a (2 * (2 * m + 1) + 2 * Datatypes.S 1)) with (q_pow a (4 * m + 6)).
  2: { apply (q_pow_comp_proper a a (Qeq_refl a) (2 * (2 * m + 1) + 2 * Datatypes.S 1)%nat (4 * m + 6)%nat). exact Hn2. }
  setoid_replace (q_fact (2 * (2 * m + 1))) with (q_fact (4 * m + 2)).
  2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. exact Hn0. }
  setoid_replace (q_fact (2 * Datatypes.S 0)) with (q_fact 2).
  2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. exact Hf1. }
  setoid_replace (q_fact (2 * Datatypes.S 1)) with (q_fact 4).
  2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. exact Hf2. }
  reflexivity.
Qed.

Lemma row_pair_osq1_expand : forall (m : nat) (a : Q),QeqT (
  osq_row (2 * m) 1 a ) (
  q_pow a (4 * m + 2) / (q_fact (4 * m + 1) * q_fact 1) +
  q_pow a (4 * m + 4) / (q_fact (4 * m + 1) * q_fact 3)).
Proof.
  intros m a.
  apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (osq_row_succ (2 * m) 0 a)).
  change (osq_row (2 * m) 0 a) with
    (q_pow a (2 * (2 * m) + 2) / (q_fact (2 * (2 * m) + 1) * q_fact 1)).
  assert (Hn0 : (2 * (2 * m) + 2 = 4 * m + 2)%nat) by lia.
  assert (Hn1 : (2 * (2 * m) + 2 * Datatypes.S 0 + 2 = 4 * m + 4)%nat) by lia.
  assert (Hf1 : (2 * (2 * m) + 1 = 4 * m + 1)%nat) by lia.
  assert (Hf2 : (2 * Datatypes.S 0 + 1 = 3)%nat) by lia.
  setoid_replace (q_pow a (2 * (2 * m) + 2)) with (q_pow a (4 * m + 2)).
  2: { apply (q_pow_comp_proper a a (Qeq_refl a) (2 * (2 * m) + 2)%nat (4 * m + 2)%nat). exact Hn0. }
  setoid_replace (q_pow a (2 * (2 * m) + 2 * Datatypes.S 0 + 2)) with (q_pow a (4 * m + 4)).
  2: { apply (q_pow_comp_proper a a (Qeq_refl a) (2 * (2 * m) + 2 * Datatypes.S 0 + 2)%nat (4 * m + 4)%nat). exact Hn1. }
  setoid_replace (q_fact (2 * (2 * m) + 1)) with (q_fact (4 * m + 1)).
  2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. exact Hf1. }
  setoid_replace (q_fact (2 * Datatypes.S 0 + 1)) with (q_fact 3).
  2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. exact Hf2. }
  reflexivity.
Qed.

Lemma row_pair_tail_expand : forall (m : nat) (a : Q),QeqT (
  - 2 * esq_row (2 * m + 2) 1 a + 2 * osq_row (2 * m + 1) 0 a +
  2 * q_pow a (4 * m + 6) / (q_fact (4 * m + 4) * q_fact 2) ) (
  - 2 * q_pow a (4 * m + 4) / (q_fact (4 * m + 4) * q_fact 0) +
  2 * q_pow a (4 * m + 4) / (q_fact (4 * m + 3) * q_fact 1)).
Proof.
  intros m a.
  apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (esq_row_succ (2 * m + 2) 0 a)).
  change (esq_row (2 * m + 2) 0 a) with
    (q_pow a (2 * (2 * m + 2)) / (q_fact (2 * (2 * m + 2)) * q_fact 0)).
  change (osq_row (2 * m + 1) 0 a) with
    (q_pow a (2 * (2 * m + 1) + 2) / (q_fact (2 * (2 * m + 1) + 1) * q_fact 1)).
  assert (Hn1 : (2 * (2 * m + 2) = 4 * m + 4)%nat) by lia.
  assert (Hn2 : (2 * (2 * m + 2) + 2 * Datatypes.S 0 = 4 * m + 6)%nat) by lia.
  assert (Hn3 : (2 * (2 * m + 1) + 2 = 4 * m + 4)%nat) by lia.
  assert (Hf2 : (2 * Datatypes.S 0 = 2)%nat) by lia.
  assert (Hf3 : (2 * (2 * m + 1) + 1 = 4 * m + 3)%nat) by lia.
  (* Replace the arguments with Leibniz [rewrite]: the conversion-based matching of [setoid_replace] would also rewrite the Q numeral 2, since 2 ≡ q_fact 2. *)
  rewrite Hn2. rewrite Hf2. rewrite Hn1. rewrite Hn3. rewrite Hf3.
  unfold Qdiv in *. ring.
Qed.

Lemma row_pair_high6 : forall (m : nat), (1 <= m)%nat ->QeqT (
  - 2 / (q_fact (4 * m + 2) * q_fact 4)
  - 2 * sum_upto (m - 1) (fun j => 1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 6)))
  + 2 * sum_upto m (fun j => 1 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 4)))
  ) ( 0).
Proof.
  intros m Hm.
  apply qeq_imp_qeqT.
  assert (Hm1 : ((m - 1) + 1 = m)%nat) by lia.
  set (f' := fun j : nat => 1 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 4))).
  assert (Hf0 : f' 0%nat == 1 / (q_fact (4 * m + 2) * q_fact 4)).
  { unfold f'. change (1 / (q_fact (4 * m + 2 - 2 * 0) * q_fact (2 * 0 + 4)) ==
                       1 / (q_fact (4 * m + 2) * q_fact 4)).
    assert (Ha : (4 * m + 2 - 2 * 0 = 4 * m + 2)%nat) by lia.
    assert (Hb : (2 * 0 + 4 = 4)%nat) by lia.
    setoid_replace (q_fact (4 * m + 2 - 2 * 0)) with (q_fact (4 * m + 2)).
    2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. exact Ha. }
    setoid_replace (q_fact (2 * 0 + 4)) with (q_fact 4).
    2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. exact Hb. }
    reflexivity. }
  assert (Hfs : forall j, f' (j + 1)%nat ==
                          1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 6))).
  { intro j. unfold f'.
    change (1 / (q_fact (4 * m + 2 - 2 * (j + 1)) * q_fact (2 * (j + 1) + 4)) ==
            1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 6))).
    assert (Ha : (4 * m + 2 - 2 * (j + 1) = 4 * m - 2 * j)%nat) by lia.
    assert (Hb : (2 * (j + 1) + 4 = 2 * j + 6)%nat) by lia.
    setoid_replace (q_fact (4 * m + 2 - 2 * (j + 1))) with (q_fact (4 * m - 2 * j)).
    2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. exact Ha. }
    setoid_replace (q_fact (2 * (j + 1) + 4)) with (q_fact (2 * j + 6)).
    2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. exact Hb. }
    reflexivity. }
  assert (Hsplit : sum_upto m f' == f' 0%nat + sum_upto (m - 1) (fun j => f' (j + 1)%nat)).
  { rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq m ((m - 1) + 1) f' (eq_sym Hm1))).
    assert (Hshift : sum_upto (m - 1) (fun j => f' (j + 1)%nat) ==
                     sum_upto ((m - 1) + 1) f' - f' 0%nat).
    { apply (qeqT_imp_qeq _ _ (sum_upto_shift (m - 1) f')). }
    setoid_rewrite Hshift.
    unfold Qminus. ring. }
  setoid_rewrite Hsplit.
  assert (Hpre1538_16 : (forall i : nat, NatLe (Datatypes.S i) (m - 1) ->QeqT ( (fun j => f' (j + 1)%nat) i ) ( (fun j => 1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 6))) i))).
  {  intros j Hj. apply NatLe_drop in Hj. apply qeq_imp_qeqT. apply (Hfs j). }
  setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_ext_below (m - 1) (fun j => f' (j + 1)%nat)                   (fun j => 1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 6))) Hpre1538_16)).
  setoid_rewrite Hf0.
  unfold Qdiv in *. unfold Qminus. ring.
Qed.

Lemma row_pair_mid4 : forall (m : nat), (1 <= m)%nat ->QeqT (
  - 2 / (q_fact (4 * m + 2) * q_fact 2)
  - 2 * sum_upto (m - 1) (fun j => 1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 4)))
  + 2 * sum_upto (m - 1) (fun j => 1 / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 5)))
  + 2 / (q_fact (4 * m + 1) * q_fact 3)
  - 2 / (q_fact (4 * m + 4) * q_fact 0)
  + 2 / (q_fact (4 * m + 3) * q_fact 1)
  ) ( 1 / (q_fact (2 * m + 2) * q_fact (2 * m + 2))).
Proof.
  intros m Hm.
  apply qeq_imp_qeqT.
  assert (Hms : (m = Datatypes.S (m - 1))%nat) by lia.
  (* [H1]: the first two terms become the sum of -2/((4m+2−2j)!(2j+2)!) over j < m. *)
  assert (H1 : - 2 / (q_fact (4 * m + 2) * q_fact 2)
               - 2 * sum_upto (m - 1) (fun j => 1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 4))) ==
               sum_upto m (fun j => - 2 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 2)))).
  { rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq m (Datatypes.S (m - 1))              (fun j => - 2 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 2))) Hms)).
    rewrite (qeqT_imp_qeq _ _ (sum_upto_rot (m - 1) (fun j => - 2 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 2))))).
    assert (Hg0 : - 2 / (q_fact (4 * m + 2 - 2 * 0) * q_fact (2 * 0 + 2)) ==
                  - 2 / (q_fact (4 * m + 2) * q_fact 2)).
    { assert (Ha : (4 * m + 2 - 2 * 0 = 4 * m + 2)%nat) by lia.
      assert (Hb : (2 * 0 + 2 = 2)%nat) by lia.
      rewrite Ha. rewrite Hb. reflexivity. }
    assert (Hgs : forall j, - 2 / (q_fact (4 * m + 2 - 2 * Datatypes.S j) * q_fact (2 * Datatypes.S j + 2)) ==
                           - 2 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 4))).
    { intro j. assert (Ha : (4 * m + 2 - 2 * Datatypes.S j = 4 * m - 2 * j)%nat) by lia.
      assert (Hb : (2 * Datatypes.S j + 2 = 2 * j + 4)%nat) by lia.
      rewrite Ha. rewrite Hb. reflexivity. }
    assert (Hpre1538_15 : (forall i : nat, NatLe (Datatypes.S i) (m - 1) ->QeqT ( (fun j => - 2 / (q_fact (4 * m + 2 - 2 * Datatypes.S j) * q_fact (2 * Datatypes.S j + 2))) i ) ( (fun j => - 2 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 4))) i))).
    {  intros j Hj. apply NatLe_drop in Hj. apply qeq_imp_qeqT. apply (Hgs j). }
    setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_ext_below (m - 1)       (fun j => - 2 / (q_fact (4 * m + 2 - 2 * Datatypes.S j) * q_fact (2 * Datatypes.S j + 2)))       (fun j => - 2 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 4))) Hpre1538_15)).
    setoid_rewrite Hg0.
    assert (Hpre1538_14 : (forall i : nat, NatLe (Datatypes.S i) (m - 1) ->QeqT ( (fun j => - 2 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 4))) i ) ( (fun j => - 2 * (1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 4)))) i))).
    {  intros j Hj. apply NatLe_drop in Hj. apply qeq_imp_qeqT. unfold Qdiv. ring. }
    setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_ext_below (m - 1)       (fun j => - 2 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 4)))       (fun j => - 2 * (1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 4)))) Hpre1538_14)).
    setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_scale_neg2 (m - 1) (fun j => 1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 4))))).
    unfold Qdiv in *. unfold Qminus. ring. }
  (* [H2]: 2*Σ_{j<m−1} 1/((4m−1−2j)!(2j+5)!) + 2/((4m+1)!(3)!) becomes the sum of 2/((4m+1−2j)!(2j+3)!) over j < m. *)
  assert (H2 : 2 * sum_upto (m - 1) (fun j => 1 / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 5)))
               + 2 / (q_fact (4 * m + 1) * q_fact 3) ==
               sum_upto m (fun j => 2 / (q_fact (4 * m + 1 - 2 * j) * q_fact (2 * j + 3)))).
  { rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq m (Datatypes.S (m - 1))              (fun j => 2 / (q_fact (4 * m + 1 - 2 * j) * q_fact (2 * j + 3))) Hms)).
    rewrite (qeqT_imp_qeq _ _ (sum_upto_rot (m - 1) (fun j => 2 / (q_fact (4 * m + 1 - 2 * j) * q_fact (2 * j + 3))))).
    assert (Hg0 : 2 / (q_fact (4 * m + 1 - 2 * 0) * q_fact (2 * 0 + 3)) ==
                  2 / (q_fact (4 * m + 1) * q_fact 3)).
    { assert (Ha : (4 * m + 1 - 2 * 0 = 4 * m + 1)%nat) by lia.
      assert (Hb : (2 * 0 + 3 = 3)%nat) by lia.
      rewrite Ha. rewrite Hb. reflexivity. }
    assert (Hgs : forall j, 2 / (q_fact (4 * m + 1 - 2 * Datatypes.S j) * q_fact (2 * Datatypes.S j + 3)) ==
                           2 / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 5))).
    { intro j. assert (Ha : (4 * m + 1 - 2 * Datatypes.S j = 4 * m - 1 - 2 * j)%nat) by lia.
      assert (Hb : (2 * Datatypes.S j + 3 = 2 * j + 5)%nat) by lia.
      rewrite Ha. rewrite Hb. reflexivity. }
    assert (Hpre1538_13 : (forall i : nat, NatLe (Datatypes.S i) (m - 1) ->QeqT ( (fun j => 2 / (q_fact (4 * m + 1 - 2 * Datatypes.S j) * q_fact (2 * Datatypes.S j + 3))) i ) ( (fun j => 2 / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 5))) i))).
    {  intros j Hj. apply NatLe_drop in Hj. apply qeq_imp_qeqT. apply (Hgs j). }
    setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_ext_below (m - 1)       (fun j => 2 / (q_fact (4 * m + 1 - 2 * Datatypes.S j) * q_fact (2 * Datatypes.S j + 3)))       (fun j => 2 / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 5))) Hpre1538_13)).
    setoid_rewrite Hg0.
    assert (Hpre1538_12 : (forall i : nat, NatLe (Datatypes.S i) (m - 1) ->QeqT ( (fun j => 2 / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 5))) i ) ( (fun j => 2 * (1 / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 5)))) i))).
    {  intros j Hj. apply NatLe_drop in Hj. apply qeq_imp_qeqT. unfold Qdiv. ring. }
    setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_ext_below (m - 1)       (fun j => 2 / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 5)))       (fun j => 2 * (1 / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 5)))) Hpre1538_12)).
    setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_scale (m - 1) 2 (fun j => 1 / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 5))))).
    unfold Qdiv in *. unfold Qminus. ring. }
  (* Assembly: first regroup ([Hre] by [ring], pulling the left sides of [H1]/[H2] into contiguous subterms), then rewrite and apply [vander_4m4]. *)
  assert (Hre : - 2 / (q_fact (4 * m + 2) * q_fact 2)
                - 2 * sum_upto (m - 1) (fun j => 1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 4)))
                + 2 * sum_upto (m - 1) (fun j => 1 / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 5)))
                + 2 / (q_fact (4 * m + 1) * q_fact 3)
                - 2 / (q_fact (4 * m + 4) * q_fact 0)
                + 2 / (q_fact (4 * m + 3) * q_fact 1) ==
                (- 2 / (q_fact (4 * m + 2) * q_fact 2)
                 - 2 * sum_upto (m - 1) (fun j => 1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 4))))
                + (2 * sum_upto (m - 1) (fun j => 1 / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 5)))
                   + 2 / (q_fact (4 * m + 1) * q_fact 3))
                - 2 / (q_fact (4 * m + 4) * q_fact 0)
                + 2 / (q_fact (4 * m + 3) * q_fact 1)).
  { unfold Qminus. ring. }
  setoid_rewrite Hre.
  setoid_rewrite H1.
  setoid_rewrite H2.
  setoid_rewrite <- (qeqT_imp_qeq _ _ (sum_upto_plus m                      (fun j => - 2 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 2)))                      (fun j => 2 / (q_fact (4 * m + 1 - 2 * j) * q_fact (2 * j + 3))))).
  apply qeqT_imp_qeq.
  apply (vander_4m4 m Hm).
Qed.

Lemma row_pair_mid2 : forall (m : nat), (1 <= m)%nat ->QeqT (
  - 2 / (q_fact (4 * m + 2) * q_fact 0)
  + 2 * sum_upto (m - 1) (fun j => 1 / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 3)))
  + 2 / (q_fact (4 * m + 1) * q_fact 1)
  - 2 * sum_upto m (fun j => 1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2)))
  ) ( - 1 / (q_fact (2 * m + 1) * q_fact (2 * m + 1))).
Proof.
  intros m Hm.
  apply qeq_imp_qeqT.
  assert (Hms : (m = Datatypes.S (m - 1))%nat) by lia.
  (* [H1]: the middle two terms become the sum of 2/((4m+1−2j)!(2j+1)!) over j < m. *)
  assert (H1 : 2 * sum_upto (m - 1) (fun j => 1 / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 3)))
               + 2 / (q_fact (4 * m + 1) * q_fact 1) ==
               sum_upto m (fun j => 2 / (q_fact (4 * m + 1 - 2 * j) * q_fact (2 * j + 1)))).
  { rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq m (Datatypes.S (m - 1))              (fun j => 2 / (q_fact (4 * m + 1 - 2 * j) * q_fact (2 * j + 1))) Hms)).
    rewrite (qeqT_imp_qeq _ _ (sum_upto_rot (m - 1) (fun j => 2 / (q_fact (4 * m + 1 - 2 * j) * q_fact (2 * j + 1))))).
    assert (Hg0 : 2 / (q_fact (4 * m + 1 - 2 * 0) * q_fact (2 * 0 + 1)) ==
                  2 / (q_fact (4 * m + 1) * q_fact 1)).
    { assert (Ha : (4 * m + 1 - 2 * 0 = 4 * m + 1)%nat) by lia.
      assert (Hb : (2 * 0 + 1 = 1)%nat) by lia.
      rewrite Ha. rewrite Hb. reflexivity. }
    assert (Hgs : forall j, 2 / (q_fact (4 * m + 1 - 2 * Datatypes.S j) * q_fact (2 * Datatypes.S j + 1)) ==
                           2 / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 3))).
    { intro j. assert (Ha : (4 * m + 1 - 2 * Datatypes.S j = 4 * m - 1 - 2 * j)%nat) by lia.
      assert (Hb : (2 * Datatypes.S j + 1 = 2 * j + 3)%nat) by lia.
      rewrite Ha. rewrite Hb. reflexivity. }
    assert (Hpre1538_11 : (forall i : nat, NatLe (Datatypes.S i) (m - 1) ->QeqT ( (fun j => 2 / (q_fact (4 * m + 1 - 2 * Datatypes.S j) * q_fact (2 * Datatypes.S j + 1))) i ) ( (fun j => 2 / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 3))) i))).
    {  intros j Hj. apply NatLe_drop in Hj. apply qeq_imp_qeqT. apply (Hgs j). }
    setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_ext_below (m - 1)       (fun j => 2 / (q_fact (4 * m + 1 - 2 * Datatypes.S j) * q_fact (2 * Datatypes.S j + 1)))       (fun j => 2 / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 3))) Hpre1538_11)).
    setoid_rewrite Hg0.
    assert (Hpre1538_10 : (forall i : nat, NatLe (Datatypes.S i) (m - 1) ->QeqT ( (fun j => 2 / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 3))) i ) ( (fun j => 2 * (1 / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 3)))) i))).
    {  intros j Hj. apply NatLe_drop in Hj. apply qeq_imp_qeqT. unfold Qdiv. ring. }
    setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_ext_below (m - 1)       (fun j => 2 / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 3)))       (fun j => 2 * (1 / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 3)))) Hpre1538_10)).
    setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_scale (m - 1) 2 (fun j => 1 / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 3))))).
    unfold Qdiv in *. unfold Qminus. ring. }
  (* [H2]: the first term plus -2 times the tail sum becomes the sum of -2/((4m+2−2j)!(2j)!) over j < m minus 2/((2m+2)!(2m)!). *)
  assert (Htail : sum_upto m (fun j => 1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2))) ==
                  sum_upto (m - 1) (fun j => 1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2))) +
                  1 / (q_fact (2 * m + 2) * q_fact (2 * m))).
  { rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq m (Datatypes.S (m - 1))              (fun j => 1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2))) Hms)).
    change (sum_upto (m - 1) (fun j => 1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2))) +
            1 / (q_fact (4 * m - 2 * (m - 1)) * q_fact (2 * (m - 1) + 2)) ==
            sum_upto (m - 1) (fun j => 1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2))) +
            1 / (q_fact (2 * m + 2) * q_fact (2 * m))).
    assert (Htm : 1 / (q_fact (4 * m - 2 * (m - 1)) * q_fact (2 * (m - 1) + 2)) ==
                  1 / (q_fact (2 * m + 2) * q_fact (2 * m))).
    { assert (Ha : (4 * m - 2 * (m - 1) = 2 * m + 2)%nat) by lia.
      assert (Hb : (2 * (m - 1) + 2 = 2 * m)%nat) by lia.
      rewrite Ha. rewrite Hb. reflexivity. }
    setoid_rewrite Htm. reflexivity. }
  assert (H2 : - 2 / (q_fact (4 * m + 2) * q_fact 0)
               - 2 * sum_upto m (fun j => 1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2))) ==
               sum_upto m (fun j => - 2 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j))) -
               2 / (q_fact (2 * m + 2) * q_fact (2 * m))).
  { setoid_rewrite Htail.
    assert (Hpre : - 2 / (q_fact (4 * m + 2) * q_fact 0)
                   - 2 * sum_upto (m - 1) (fun j => 1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2))) ==
                   sum_upto m (fun j => - 2 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j)))).
    { rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq m (Datatypes.S (m - 1))                (fun j => - 2 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j))) Hms)).
      rewrite (qeqT_imp_qeq _ _ (sum_upto_rot (m - 1) (fun j => - 2 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j))))).
      assert (Hg0 : - 2 / (q_fact (4 * m + 2 - 2 * 0) * q_fact (2 * 0)) ==
                    - 2 / (q_fact (4 * m + 2) * q_fact 0)).
      { assert (Ha : (4 * m + 2 - 2 * 0 = 4 * m + 2)%nat) by lia.
        assert (Hb : (2 * 0 = 0)%nat) by lia.
        rewrite Ha. rewrite Hb. reflexivity. }
      assert (Hgs : forall j, - 2 / (q_fact (4 * m + 2 - 2 * Datatypes.S j) * q_fact (2 * Datatypes.S j)) ==
                             - 2 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2))).
      { intro j. assert (Ha : (4 * m + 2 - 2 * Datatypes.S j = 4 * m - 2 * j)%nat) by lia.
        assert (Hb : (2 * Datatypes.S j = 2 * j + 2)%nat) by lia.
        rewrite Ha. rewrite Hb. reflexivity. }
      assert (Hpre1538_9 : (forall i : nat, NatLe (Datatypes.S i) (m - 1) ->QeqT ( (fun j => - 2 / (q_fact (4 * m + 2 - 2 * Datatypes.S j) * q_fact (2 * Datatypes.S j))) i ) ( (fun j => - 2 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2))) i))).
      {  intros j Hj. apply NatLe_drop in Hj. apply qeq_imp_qeqT. apply (Hgs j). }
      setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_ext_below (m - 1)         (fun j => - 2 / (q_fact (4 * m + 2 - 2 * Datatypes.S j) * q_fact (2 * Datatypes.S j)))         (fun j => - 2 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2))) Hpre1538_9)).
      setoid_rewrite Hg0.
      assert (Hpre1538_8 : (forall i : nat, NatLe (Datatypes.S i) (m - 1) ->QeqT ( (fun j => - 2 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2))) i ) ( (fun j => - 2 * (1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2)))) i))).
      {  intros j Hj. apply NatLe_drop in Hj. apply qeq_imp_qeqT. unfold Qdiv. ring. }
      setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_ext_below (m - 1)         (fun j => - 2 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2)))         (fun j => - 2 * (1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2)))) Hpre1538_8)).
      setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_scale_neg2 (m - 1) (fun j => 1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2))))).
      unfold Qdiv in *. unfold Qminus. ring. }
    assert (Hdist : - 2 / (q_fact (4 * m + 2) * q_fact 0)
                    - 2 * (sum_upto (m - 1) (fun j => 1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2))) +
                           1 / (q_fact (2 * m + 2) * q_fact (2 * m))) ==
                    (- 2 / (q_fact (4 * m + 2) * q_fact 0)
                     - 2 * sum_upto (m - 1) (fun j => 1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2))))
                    - 2 / (q_fact (2 * m + 2) * q_fact (2 * m))).
    { unfold Qdiv in *. unfold Qminus. ring. }
    setoid_rewrite Hdist.
    setoid_rewrite Hpre.
    unfold Qdiv in *. unfold Qminus. ring. }
  (* Assembly: after rewriting with [H1]/[H2] this equals the left side of [vander_4m2] - 2/((2m+2)!(2m)!), i.e. -1/((2m+1)!(2m+1)!). *)
  assert (Hre : - 2 / (q_fact (4 * m + 2) * q_fact 0)
                + 2 * sum_upto (m - 1) (fun j => 1 / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 3)))
                + 2 / (q_fact (4 * m + 1) * q_fact 1)
                - 2 * sum_upto m (fun j => 1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2))) ==
                (- 2 / (q_fact (4 * m + 2) * q_fact 0)
                 - 2 * sum_upto m (fun j => 1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2))))
                + (2 * sum_upto (m - 1) (fun j => 1 / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 3)))
                   + 2 / (q_fact (4 * m + 1) * q_fact 1))).
  { unfold Qdiv in *. unfold Qminus. ring. }
  setoid_rewrite Hre.
  setoid_rewrite H2.
  setoid_rewrite H1.
  assert (Hre2 : (sum_upto m (fun j => - 2 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j))) -
                  2 / (q_fact (2 * m + 2) * q_fact (2 * m))) +
                 sum_upto m (fun j => 2 / (q_fact (4 * m + 1 - 2 * j) * q_fact (2 * j + 1))) ==
                 (sum_upto m (fun j => - 2 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j))) +
                  sum_upto m (fun j => 2 / (q_fact (4 * m + 1 - 2 * j) * q_fact (2 * j + 1))))
                 - 2 / (q_fact (2 * m + 2) * q_fact (2 * m))).
  { unfold Qdiv in *. unfold Qminus. ring. }
  setoid_rewrite Hre2.
  setoid_rewrite <- (qeqT_imp_qeq _ _ (sum_upto_plus m                      (fun j => - 2 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j)))                      (fun j => 2 / (q_fact (4 * m + 1 - 2 * j) * q_fact (2 * j + 1))))).
  assert (Hv : sum_upto m (fun j => - 2 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j))
                               + 2 / (q_fact (4 * m + 1 - 2 * j) * q_fact (2 * j + 1))) ==
               2 / (q_fact (2 * m + 2) * q_fact (2 * m)) -
               1 / (q_fact (2 * m + 1) * q_fact (2 * m + 1))).
  apply qeqT_imp_qeq.
  { apply (vander_4m2 m Hm). }
  setoid_rewrite Hv.
  unfold Qdiv in *. unfold Qminus. ring.
Qed.

Lemma row_pair_main : forall (a : Q) (m : nat), (1 <= m)%nat ->QeqT (
  sum_upto m
    (fun j =>
       - 2 * esq_row (2 * m + 1 - j) (j + 2) a
       + 2 * esq_row (2 * m - j) (j + 1) a
       + 2 * osq_row (2 * m - j) (j + 1) a
       - 2 * osq_row (2 * m - 1 - j) j a
       + 2 * q_pow a (4 * m + 6) / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 4))
       - 2 * q_pow a (4 * m + 2) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2)))
  - 2 * esq_row (2 * m + 2) 1 a
  + 2 * osq_row (2 * m + 1) 0 a
  + 2 * q_pow a (4 * m + 6) / (q_fact (4 * m + 4) * q_fact 2) ) (
  2 * esq_row (Datatypes.S m) m a +
  (q_pow a (4 * m + 4) / (q_fact (2 * m + 2) * q_fact (2 * m + 2))) -
  2 * osq_row m (m - 1) a -
  (q_pow a (4 * m + 2) / (q_fact (2 * m + 1) * q_fact (2 * m + 1)))).
Proof.
  intros a m Hm.
  apply qeq_imp_qeqT.
  (* 1. Rearrange the row difference (indexed by j) pointwise into esq(j) + osq(j) + T(j), then split into three sums. *)
  assert (Hpre1538_7 : (forall i : nat, NatLe (Datatypes.S i) m ->QeqT ( (fun j => - 2 * esq_row (2 * m + 1 - j) (j + 2) a + 2 * esq_row (2 * m - j) (j + 1) a + 2 * osq_row (2 * m - j) (j + 1) a - 2 * osq_row (2 * m - 1 - j) j a + 2 * q_pow a (4 * m + 6) / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 4)) - 2 * q_pow a (4 * m + 2) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2))) i ) ( (fun j => (- 2 * esq_row (2 * m + 1 - j) (j + 2) a + 2 * esq_row (2 * m - j) (j + 1) a) + (2 * osq_row (2 * m - j) (j + 1) a - 2 * osq_row (2 * m - 1 - j) j a) + (2 * q_pow a (4 * m + 6) / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 4))        - 2 * q_pow a (4 * m + 2) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2)))) i))).
  { intros j Hlt. apply qeq_imp_qeqT. ring. }
  setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_ext_below m    (fun j =>
       - 2 * esq_row (2 * m + 1 - j) (j + 2) a
       + 2 * esq_row (2 * m - j) (j + 1) a
       + 2 * osq_row (2 * m - j) (j + 1) a
       - 2 * osq_row (2 * m - 1 - j) j a
       + 2 * q_pow a (4 * m + 6) / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 4))
       - 2 * q_pow a (4 * m + 2) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2)))
    (fun j =>
       (- 2 * esq_row (2 * m + 1 - j) (j + 2) a + 2 * esq_row (2 * m - j) (j + 1) a) +
       (2 * osq_row (2 * m - j) (j + 1) a - 2 * osq_row (2 * m - 1 - j) j a) +
       (2 * q_pow a (4 * m + 6) / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 4))        - 2 * q_pow a (4 * m + 2) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2)))) Hpre1538_7)).
   setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_plus m
     (fun j => (- 2 * esq_row (2 * m + 1 - j) (j + 2) a + 2 * esq_row (2 * m - j) (j + 1) a) +
     (2 * osq_row (2 * m - j) (j + 1) a - 2 * osq_row (2 * m - 1 - j) j a))
     (fun j => 2 * q_pow a (4 * m + 6) / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 4))
     - 2 * q_pow a (4 * m + 2) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2))))).
   setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_plus m
     (fun j => - 2 * esq_row (2 * m + 1 - j) (j + 2) a + 2 * esq_row (2 * m - j) (j + 1) a)
     (fun j => 2 * osq_row (2 * m - j) (j + 1) a - 2 * osq_row (2 * m - 1 - j) j a))).
   setoid_rewrite (qeqT_imp_qeq _ _ (esq_row_diff_closed m a Hm)).
   setoid_rewrite (qeqT_imp_qeq _ _ (osq_row_diff_closed m a Hm)).
   assert (Hm1 : (m + 1 = Datatypes.S m)%nat) by lia.
   assert (Heq : esq_row (m + 1) m a == esq_row (Datatypes.S m) m a).
   { rewrite Hm1. reflexivity. }
   setoid_rewrite Heq.
  setoid_rewrite (qeqT_imp_qeq _ _ (row_pair_esq2_expand m a)).
  setoid_rewrite (qeqT_imp_qeq _ _ (row_pair_osq1_expand m a)).
  (* Split the sum of T into the sum of (2*q6/D6') plus the sum of (-(2*q2/D2')) ([Hmov] needs the two sums separately). *)
  setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_plus m    (fun j => 2 * q_pow a (4 * m + 6) / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 4)))    (fun j => - (2 * q_pow a (4 * m + 2) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2)))))).
  (* [Hmov]: regroup into 2*esqSm - 2*osqmm + R6 + R4 + R2 (the layers R6/R4/R2 grouped by size, with the tail atoms at the end of R4). *)
  assert (Hmov : 2 * esq_row (Datatypes.S m) m a -
                 2 * (q_pow a (4 * m + 2) / (q_fact (4 * m + 2) * q_fact 0) +
                      q_pow a (4 * m + 4) / (q_fact (4 * m + 2) * q_fact 2) +
                      q_pow a (4 * m + 6) / (q_fact (4 * m + 2) * q_fact 4)) -
                 2 * sum_upto (m - 1) (fun j => q_pow a (4 * m + 4) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 4))) -
                 2 * sum_upto (m - 1) (fun j => q_pow a (4 * m + 6) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 6))) +
                 (- 2 * osq_row m (m - 1) a +
                  2 * (q_pow a (4 * m + 2) / (q_fact (4 * m + 1) * q_fact 1) +
                       q_pow a (4 * m + 4) / (q_fact (4 * m + 1) * q_fact 3)) +
                  2 * sum_upto (m - 1) (fun j => q_pow a (4 * m + 2) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 3))) +
                  2 * sum_upto (m - 1) (fun j => q_pow a (4 * m + 4) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 5)))) +
                 (sum_upto m (fun j => 2 * q_pow a (4 * m + 6) / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 4))) +
                  sum_upto m (fun j => - (2 * q_pow a (4 * m + 2) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2))))) -
                 2 * esq_row (2 * m + 2) 1 a + 2 * osq_row (2 * m + 1) 0 a +
                 2 * q_pow a (4 * m + 6) / (q_fact (4 * m + 4) * q_fact 2) ==
                 2 * esq_row (Datatypes.S m) m a - 2 * osq_row m (m - 1) a +
                 (- 2 * (q_pow a (4 * m + 6) / (q_fact (4 * m + 2) * q_fact 4))
                  - 2 * sum_upto (m - 1) (fun j => q_pow a (4 * m + 6) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 6)))
                  + sum_upto m (fun j => 2 * q_pow a (4 * m + 6) / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 4)))) +
                 (- 2 * (q_pow a (4 * m + 4) / (q_fact (4 * m + 2) * q_fact 2))
                  - 2 * sum_upto (m - 1) (fun j => q_pow a (4 * m + 4) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 4)))
                  + 2 * sum_upto (m - 1) (fun j => q_pow a (4 * m + 4) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 5)))
                  + 2 * (q_pow a (4 * m + 4) / (q_fact (4 * m + 1) * q_fact 3))
                  + (- 2 * esq_row (2 * m + 2) 1 a + 2 * osq_row (2 * m + 1) 0 a +
                     2 * q_pow a (4 * m + 6) / (q_fact (4 * m + 4) * q_fact 2))) +
                 (- 2 * (q_pow a (4 * m + 2) / (q_fact (4 * m + 2) * q_fact 0))
                  + 2 * sum_upto (m - 1) (fun j => q_pow a (4 * m + 2) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 3)))
                  + 2 * (q_pow a (4 * m + 2) / (q_fact (4 * m + 1) * q_fact 1))
                  + sum_upto m (fun j => - (2 * q_pow a (4 * m + 2) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2)))))).
  { unfold Qdiv in *. unfold Qminus. ring. }
  setoid_rewrite Hmov.
  (* Expand the tail terms (contiguous within R4). *)
  setoid_rewrite (qeqT_imp_qeq _ _ (row_pair_tail_expand m a)).
  (* Layered assertions: R6 == 0, R4 == Te^2 and R2 == −To^2. *)
  assert (H6 : - 2 * (q_pow a (4 * m + 6) / (q_fact (4 * m + 2) * q_fact 4))
               + (- (2 * sum_upto (m - 1) (fun j => q_pow a (4 * m + 6) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 6)))))
               + sum_upto m (fun j => 2 * q_pow a (4 * m + 6) / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 4)))
               == 0).
  { assert (Hc : - 2 / (q_fact (4 * m + 2) * q_fact 4)
                 - 2 * sum_upto (m - 1) (fun j => 1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 6)))
                 + 2 * sum_upto m (fun j => 1 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 4))) == 0).
    { apply qeqT_imp_qeq. apply (row_pair_high6 m Hm). }
    assert (H1' : - 2 * (q_pow a (4 * m + 6) / (q_fact (4 * m + 2) * q_fact 4)) ==
                  q_pow a (4 * m + 6) * (- 2 / (q_fact (4 * m + 2) * q_fact 4))).
    { unfold Qdiv. ring. }
    assert (H2' : - (2 * sum_upto (m - 1) (fun j => q_pow a (4 * m + 6) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 6)))) ==
                  q_pow a (4 * m + 6) * (- 2 * sum_upto (m - 1) (fun j => 1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 6))))).
    assert (Hpre1538_6 : (forall i : nat, NatLe (Datatypes.S i) (m - 1) ->QeqT ( (fun j => q_pow a (4 * m + 6) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 6))) i ) ( (fun j => q_pow a (4 * m + 6) * (1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 6)))) i))).
      {  intros j Hj. apply NatLe_drop in Hj. apply qeq_imp_qeqT. unfold Qdiv. ring. }
    { setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_ext_below (m - 1)        (fun j => q_pow a (4 * m + 6) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 6)))        (fun j => q_pow a (4 * m + 6) * (1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 6)))) Hpre1538_6)).
      setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_scale (m - 1) (q_pow a (4 * m + 6)) (fun j => 1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 6))))).
      unfold Qdiv in *. unfold Qminus. ring. }
    assert (H3' : sum_upto m (fun j => 2 * q_pow a (4 * m + 6) / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 4))) ==
                  q_pow a (4 * m + 6) * (2 * sum_upto m (fun j => 1 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 4))))).
    assert (Hpre1538_5 : (forall i : nat, NatLe (Datatypes.S i) m ->QeqT ( (fun j => 2 * q_pow a (4 * m + 6) / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 4))) i ) ( (fun j => 2 * (q_pow a (4 * m + 6) * (1 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 4))))) i))).
      {  intros j Hj. apply NatLe_drop in Hj. apply qeq_imp_qeqT. unfold Qdiv. ring. }
    { setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_ext_below m        (fun j => 2 * q_pow a (4 * m + 6) / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 4)))        (fun j => 2 * (q_pow a (4 * m + 6) * (1 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 4))))) Hpre1538_5)).
      assert (Hpre1538_4 : (forall i : nat, NatLe (Datatypes.S i) m ->QeqT ( (fun j => 2 * (q_pow a (4 * m + 6) * (1 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 4))))) i ) ( (fun j => q_pow a (4 * m + 6) * (2 * (1 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 4))))) i))).
      {  intros j Hj. apply NatLe_drop in Hj. apply qeq_imp_qeqT. ring. }
      setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_ext_below m        (fun j => 2 * (q_pow a (4 * m + 6) * (1 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 4)))))        (fun j => q_pow a (4 * m + 6) * (2 * (1 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 4))))) Hpre1538_4)).
       setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_scale m (q_pow a (4 * m + 6)) (fun j => 2 * (1 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 4)))))).
      setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_scale m 2 (fun j => 1 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 4))))).
      ring. }
    setoid_rewrite H1'. setoid_rewrite H2'. setoid_rewrite H3'.
    assert (Hfac : q_pow a (4 * m + 6) * (- 2 / (q_fact (4 * m + 2) * q_fact 4)) +
                   q_pow a (4 * m + 6) * (- 2 * sum_upto (m - 1) (fun j => 1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 6)))) +
                   q_pow a (4 * m + 6) * (2 * sum_upto m (fun j => 1 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 4)))) ==
                   q_pow a (4 * m + 6) * (- 2 / (q_fact (4 * m + 2) * q_fact 4)
                                          - 2 * sum_upto (m - 1) (fun j => 1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 6)))
                                          + 2 * sum_upto m (fun j => 1 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 4))))).
    { ring. }
    setoid_rewrite Hfac.
    setoid_rewrite Hc.
    unfold Qdiv in *. unfold Qminus. ring. }
  assert (H4 : - 2 * (q_pow a (4 * m + 4) / (q_fact (4 * m + 2) * q_fact 2))
               + (- (2 * sum_upto (m - 1) (fun j => q_pow a (4 * m + 4) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 4)))))
               + 2 * sum_upto (m - 1) (fun j => q_pow a (4 * m + 4) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 5)))
               + 2 * (q_pow a (4 * m + 4) / (q_fact (4 * m + 1) * q_fact 3))
               + (- 2 * q_pow a (4 * m + 4) / (q_fact (4 * m + 4) * q_fact 0) +
                  2 * q_pow a (4 * m + 4) / (q_fact (4 * m + 3) * q_fact 1)) ==
               q_pow a (4 * m + 4) / (q_fact (2 * m + 2) * q_fact (2 * m + 2))).
  { assert (Hc : - 2 / (q_fact (4 * m + 2) * q_fact 2)
                 - 2 * sum_upto (m - 1) (fun j => 1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 4)))
                 + 2 * sum_upto (m - 1) (fun j => 1 / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 5)))
                 + 2 / (q_fact (4 * m + 1) * q_fact 3)
                 - 2 / (q_fact (4 * m + 4) * q_fact 0)
                 + 2 / (q_fact (4 * m + 3) * q_fact 1) ==
                 1 / (q_fact (2 * m + 2) * q_fact (2 * m + 2))).
    { apply qeqT_imp_qeq. apply (row_pair_mid4 m Hm). }
    assert (H1' : - 2 * (q_pow a (4 * m + 4) / (q_fact (4 * m + 2) * q_fact 2)) ==
                  q_pow a (4 * m + 4) * (- 2 / (q_fact (4 * m + 2) * q_fact 2))).
    { unfold Qdiv. ring. }
    assert (H2' : - (2 * sum_upto (m - 1) (fun j => q_pow a (4 * m + 4) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 4)))) ==
                  q_pow a (4 * m + 4) * (- 2 * sum_upto (m - 1) (fun j => 1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 4))))).
    assert (Hpre1538_3 : (forall i : nat, NatLe (Datatypes.S i) (m - 1) ->QeqT ( (fun j => q_pow a (4 * m + 4) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 4))) i ) ( (fun j => q_pow a (4 * m + 4) * (1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 4)))) i))).
      {  intros j Hj. apply NatLe_drop in Hj. apply qeq_imp_qeqT. unfold Qdiv. ring. }
    { setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_ext_below (m - 1)        (fun j => q_pow a (4 * m + 4) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 4)))        (fun j => q_pow a (4 * m + 4) * (1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 4)))) Hpre1538_3)).
      setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_scale (m - 1) (q_pow a (4 * m + 4)) (fun j => 1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 4))))).
      unfold Qdiv in *. unfold Qminus. ring. }
    assert (H3' : 2 * sum_upto (m - 1) (fun j => q_pow a (4 * m + 4) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 5))) ==
                  q_pow a (4 * m + 4) * (2 * sum_upto (m - 1) (fun j => 1 / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 5))))).
    assert (Hpre1538_2 : (forall i : nat, NatLe (Datatypes.S i) (m - 1) ->QeqT ( (fun j => q_pow a (4 * m + 4) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 5))) i ) ( (fun j => q_pow a (4 * m + 4) * (1 / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 5)))) i))).
      {  intros j Hj. apply NatLe_drop in Hj. apply qeq_imp_qeqT. unfold Qdiv. ring. }
    { setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_ext_below (m - 1)        (fun j => q_pow a (4 * m + 4) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 5)))        (fun j => q_pow a (4 * m + 4) * (1 / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 5)))) Hpre1538_2)).
      setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_scale (m - 1) (q_pow a (4 * m + 4)) (fun j => 1 / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 5))))).
      unfold Qdiv in *. unfold Qminus. ring. }
    assert (H4' : 2 * (q_pow a (4 * m + 4) / (q_fact (4 * m + 1) * q_fact 3)) ==
                  q_pow a (4 * m + 4) * (2 / (q_fact (4 * m + 1) * q_fact 3))).
    { unfold Qdiv. ring. }
    assert (H5' : - 2 * q_pow a (4 * m + 4) / (q_fact (4 * m + 4) * q_fact 0) +
                  2 * q_pow a (4 * m + 4) / (q_fact (4 * m + 3) * q_fact 1) ==
                  q_pow a (4 * m + 4) * (- 2 / (q_fact (4 * m + 4) * q_fact 0) +
                                         2 / (q_fact (4 * m + 3) * q_fact 1))).
    { unfold Qdiv. ring. }
    setoid_rewrite H1'. setoid_rewrite H2'. setoid_rewrite H3'. setoid_rewrite H4'. setoid_rewrite H5'.
    assert (Hfac : q_pow a (4 * m + 4) * (- 2 / (q_fact (4 * m + 2) * q_fact 2)) +
                   q_pow a (4 * m + 4) * (- 2 * sum_upto (m - 1) (fun j => 1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 4)))) +
                   q_pow a (4 * m + 4) * (2 * sum_upto (m - 1) (fun j => 1 / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 5)))) +
                   q_pow a (4 * m + 4) * (2 / (q_fact (4 * m + 1) * q_fact 3)) +
                   q_pow a (4 * m + 4) * (- 2 / (q_fact (4 * m + 4) * q_fact 0) + 2 / (q_fact (4 * m + 3) * q_fact 1)) ==
                   q_pow a (4 * m + 4) * (- 2 / (q_fact (4 * m + 2) * q_fact 2)
                                          - 2 * sum_upto (m - 1) (fun j => 1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 4)))
                                          + 2 * sum_upto (m - 1) (fun j => 1 / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 5)))
                                          + 2 / (q_fact (4 * m + 1) * q_fact 3)
                                          - 2 / (q_fact (4 * m + 4) * q_fact 0)
                                          + 2 / (q_fact (4 * m + 3) * q_fact 1))).
    { unfold Qdiv in *. unfold Qminus. ring. }
    setoid_rewrite Hfac.
    setoid_rewrite Hc.
    unfold Qdiv in *. unfold Qminus. ring. }
  assert (H2 : - 2 * (q_pow a (4 * m + 2) / (q_fact (4 * m + 2) * q_fact 0))
               + 2 * sum_upto (m - 1) (fun j => q_pow a (4 * m + 2) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 3)))
               + 2 * (q_pow a (4 * m + 2) / (q_fact (4 * m + 1) * q_fact 1))
               + sum_upto m (fun j => - (2 * q_pow a (4 * m + 2) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2)))) ==
               - q_pow a (4 * m + 2) / (q_fact (2 * m + 1) * q_fact (2 * m + 1))).
  { assert (Hc : - 2 / (q_fact (4 * m + 2) * q_fact 0)
                 + 2 * sum_upto (m - 1) (fun j => 1 / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 3)))
                 + 2 / (q_fact (4 * m + 1) * q_fact 1)
                 - 2 * sum_upto m (fun j => 1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2))) ==
                 - 1 / (q_fact (2 * m + 1) * q_fact (2 * m + 1))).
    { apply qeqT_imp_qeq. apply (row_pair_mid2 m Hm). }
    assert (H1' : - 2 * (q_pow a (4 * m + 2) / (q_fact (4 * m + 2) * q_fact 0)) ==
                  q_pow a (4 * m + 2) * (- 2 / (q_fact (4 * m + 2) * q_fact 0))).
    { unfold Qdiv. ring. }
    assert (H2' : 2 * sum_upto (m - 1) (fun j => q_pow a (4 * m + 2) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 3))) ==
                  q_pow a (4 * m + 2) * (2 * sum_upto (m - 1) (fun j => 1 / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 3))))).
    assert (Hpre1538_1 : (forall i : nat, NatLe (Datatypes.S i) (m - 1) ->QeqT ( (fun j => q_pow a (4 * m + 2) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 3))) i ) ( (fun j => q_pow a (4 * m + 2) * (1 / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 3)))) i))).
      {  intros j Hj. apply NatLe_drop in Hj. apply qeq_imp_qeqT. unfold Qdiv. ring. }
    { setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_ext_below (m - 1)        (fun j => q_pow a (4 * m + 2) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 3)))        (fun j => q_pow a (4 * m + 2) * (1 / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 3)))) Hpre1538_1)).
      setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_scale (m - 1) (q_pow a (4 * m + 2)) (fun j => 1 / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 3))))).
      unfold Qdiv in *. unfold Qminus. ring. }
    assert (H3' : 2 * (q_pow a (4 * m + 2) / (q_fact (4 * m + 1) * q_fact 1)) ==
                  q_pow a (4 * m + 2) * (2 / (q_fact (4 * m + 1) * q_fact 1))).
    { unfold Qdiv. ring. }
    assert (H4' : sum_upto m (fun j => - (2 * q_pow a (4 * m + 2) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2)))) ==
                  q_pow a (4 * m + 2) * (- 2 * sum_upto m (fun j => 1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2))))).
      { assert (Hpre1538_200 : (forall i : nat, NatLe (Datatypes.S i) m ->QeqT ( (fun j => - (2 * q_pow a (4 * m + 2) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2)))) i ) ( (fun j => q_pow a (4 * m + 2) * (- 2 * (1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2))))) i))).
      {  intros j Hj. apply NatLe_drop in Hj. apply qeq_imp_qeqT. unfold Qdiv. ring. }
      setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_ext_below m (fun j => - (2 * q_pow a (4 * m + 2) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2)))) (fun j => q_pow a (4 * m + 2) * (- 2 * (1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2))))) Hpre1538_200)).
      setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_scale m (q_pow a (4 * m + 2)) (fun j => - 2 * (1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2)))))).
      setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_scale_neg2 m (fun j => 1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2))))).
      unfold Qdiv in *. unfold Qminus. ring. }
    setoid_rewrite H1'. setoid_rewrite H2'. setoid_rewrite H3'. setoid_rewrite H4'.
    assert (Hfac : q_pow a (4 * m + 2) * (- 2 / (q_fact (4 * m + 2) * q_fact 0)) +
                   q_pow a (4 * m + 2) * (2 * sum_upto (m - 1) (fun j => 1 / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 3)))) +
                   q_pow a (4 * m + 2) * (2 / (q_fact (4 * m + 1) * q_fact 1)) +
                   q_pow a (4 * m + 2) * (- 2 * sum_upto m (fun j => 1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2)))) ==
                   q_pow a (4 * m + 2) * (- 2 / (q_fact (4 * m + 2) * q_fact 0)
                                          + 2 * sum_upto (m - 1) (fun j => 1 / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 3)))
                                          + 2 / (q_fact (4 * m + 1) * q_fact 1)
                                          - 2 * sum_upto m (fun j => 1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2))))).
    { ring. }
    setoid_rewrite Hfac.
    setoid_rewrite Hc.
    unfold Qdiv in *. unfold Qminus. ring. }
  (* Assemble: R6 + R4 + R2 == Te^2 − To^2. *)
  setoid_rewrite H6.
  setoid_rewrite H4.
  setoid_rewrite H2.
  unfold Qdiv in *. unfold Qminus. ring.
Qed.

Lemma ksum_diff_row : forall (a : Q) (m : nat),
  (1 <= m)%nat ->QeqT (
  ksum_diff m m a + inner2 (2 * m + 1) (2 * Datatypes.S m - (2 * m + 1)) a ) (
  2 * esq_row (Datatypes.S m) m a +
  (q_pow a (4 * m + 4) /
     (q_fact (2 * m + 2) * q_fact (2 * m + 2))) -
  2 * osq_row m (m - 1) a -
  (q_pow a (2 * m + 2 * m + 2) /
     (q_fact (2 * m + 1) * q_fact (2 * m + 1)))).
Proof.
  intros a m Hm.
  apply qeq_imp_qeqT.
  (* 1. The left side == the difference of [corr] ([corr_succ_decomp] in reverse). *)
  setoid_rewrite <- (qeqT_imp_qeq _ _ (corr_succ_decomp a m Hm)).
  (* 2. The difference of [corr] == the row expression in the k' form ([corr_diff_expand]). *)
  setoid_rewrite (qeqT_imp_qeq _ _ (corr_diff_expand a m Hm)).
  (* 3. The row expression in the k' form == the j form (with j = m−1−k', via [sum_upto_rev] plus pointwise reduction). *)
  assert (Hrel : sum_upto m
            (fun k' =>
               - 2 * esq_row (m + 2 + k') (m + 1 - k') a
               + 2 * esq_row (m + 1 + k') (m - k') a
               + 2 * osq_row (m + 1 + k') (m - k') a
               - 2 * osq_row (m + k') (m - k' - 1) a
               + 2 * q_pow a (4 * m + 6) / (q_fact (2 * m + 2 * k' + 4) * q_fact (2 * m + 2 - 2 * k'))
               - 2 * q_pow a (4 * m + 2) / (q_fact (2 * m + 2 * k' + 2) * q_fact (2 * m - 2 * k'))) ==
                 sum_upto m
            (fun j =>
               - 2 * esq_row (2 * m + 1 - j) (j + 2) a
               + 2 * esq_row (2 * m - j) (j + 1) a
               + 2 * osq_row (2 * m - j) (j + 1) a
               - 2 * osq_row (2 * m - 1 - j) j a
               + 2 * q_pow a (4 * m + 6) / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 4))
               - 2 * q_pow a (4 * m + 2) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2)))).
  { rewrite <- (qeqT_imp_qeq _ _ (sum_upto_rev m      (fun j =>
         - 2 * esq_row (2 * m + 1 - j) (j + 2) a
         + 2 * esq_row (2 * m - j) (j + 1) a
         + 2 * osq_row (2 * m - j) (j + 1) a
         - 2 * osq_row (2 * m - 1 - j) j a
         + 2 * q_pow a (4 * m + 6) / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 4))         - 2 * q_pow a (4 * m + 2) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2))))).
    apply qeqT_imp_qeq. apply sum_upto_ext_below. intros k' Hk'. apply NatLe_drop in Hk'. apply qeq_imp_qeqT.
    (* Pointwise: the corr row difference at k' == the row difference at m−1−k' (arguments reduced by [lia]). *)
    assert (H1 : (2 * m + 1 - (m - 1 - k') = m + 2 + k')%nat) by lia.
    assert (H2 : ((m - 1 - k') + 2 = m + 1 - k')%nat) by lia.
    assert (H3 : (2 * m - (m - 1 - k') = m + 1 + k')%nat) by lia.
    assert (H4 : ((m - 1 - k') + 1 = m - k')%nat) by lia.
    assert (H5 : (2 * m - 1 - (m - 1 - k') = m + k')%nat) by lia.
    assert (H6 : ((m - 1 - k') = m - k' - 1)%nat) by lia.
    assert (H7 : (4 * m + 2 - 2 * (m - 1 - k') = 2 * m + 2 * k' + 4)%nat) by lia.
    assert (H8 : (2 * (m - 1 - k') + 4 = 2 * m + 2 - 2 * k')%nat) by lia.
    assert (H9 : (4 * m - 2 * (m - 1 - k') = 2 * m + 2 * k' + 2)%nat) by lia.
    assert (H10 : (2 * (m - 1 - k') + 2 = 2 * m - 2 * k')%nat) by lia.
    rewrite H1. rewrite H3. rewrite H5.
    rewrite H7. rewrite H8. rewrite H9. rewrite H10.
    rewrite H2. rewrite H4. rewrite H6.
    reflexivity. }
  setoid_rewrite Hrel.
  (* 4. The row expression in the j form == the right side ([row_pair_main]). *)
  setoid_rewrite (qeqT_imp_qeq _ _ (row_pair_main a m Hm)).
  (* 5. Reduce the exponent of To^2: 2m+2m+2 == 4m+2. *)
  assert (He : (2 * m + 2 * m + 2 = 4 * m + 2)%nat) by lia.
  setoid_replace (q_pow a (2 * m + 2 * m + 2)) with (q_pow a (4 * m + 2)).
  2: { apply (q_pow_comp_proper a a (Qeq_refl a) (2 * m + 2 * m + 2)%nat (4 * m + 2)%nat). exact He. }
  reflexivity.
Qed.

(* ============ The [esq_eq_corr] argument ============
   [corr_diff_eq_sq_diff]: the difference of [corr] == the difference of the E/O squared sums
   (via [corr_succ_decomp] -> [ksum_diff_row] -> [ksum_diff_row_rhs]).
   [esq_eq_corr]: E_m^2−O_m^2 == 1 + corr m (the main identity, base cases 0 and 1 plus the
   induction step). *)
Lemma corr_diff_eq_sq_diff : forall (a : Q) (m : nat), (1 <= m)%nat ->QeqT (
  corr (Datatypes.S m) a - corr m a ) (
  (e_sum (Datatypes.S m) a * e_sum (Datatypes.S m) a -
   o_sum (Datatypes.S m) a * o_sum (Datatypes.S m) a) -
  (e_sum m a * e_sum m a - o_sum m a * o_sum m a)).
Proof.
  intros a m Hm.
  apply qeq_imp_qeqT.
  setoid_rewrite (qeqT_imp_qeq _ _ (corr_succ_decomp a m Hm)).
  setoid_rewrite (qeqT_imp_qeq _ _ (ksum_diff_row a m Hm)).
  (* The exponent of To^2 is 2m+2m+2 in [ksum_diff_row] and 4m+2 in [ksum_diff_row_rhs]; reduce to bridge them. *)
  assert (He : (2 * m + 2 * m + 2 = 4 * m + 2)%nat) by lia.
  setoid_replace (q_pow a (2 * m + 2 * m + 2)) with (q_pow a (4 * m + 2)).
  2: { apply (q_pow_comp_proper a a (Qeq_refl a) (2 * m + 2 * m + 2)%nat (4 * m + 2)%nat). exact He. }
  setoid_rewrite (qeqT_imp_qeq _ _ (ksum_diff_row_rhs a m Hm)).
  reflexivity.
Qed.

Lemma esq_eq_corr : forall (a : Q) (m : nat),QeqT (
  e_sum m a * e_sum m a - o_sum m a * o_sum m a ) ( 1 + corr m a).
Proof.
  intros a m.
  apply qeq_imp_qeqT.
  induction m as [| m' IH].
  - (* Case m = 0: E_0 = 1, O_0 = 0 and corr 0 = 0. *)
    simpl. reflexivity.
  - destruct m' as [| m''].
    + (* Case m = 1: compute directly. *)
      unfold e_sum, o_sum, corr, kloop, inner2, brk2.
      simpl.
      field.
      all: repeat (split; [intro Hz1545; destruct (q_neq_of_lt _ (q_fact_pos _) (qeq_imp_qeqT _ _ Hz1545)) | idtac]);
           intro Hz1545; destruct (q_neq_of_lt _ (q_fact_pos _) (qeq_imp_qeqT _ _ Hz1545)).
    + (* Case m = S(S m''): the induction step, combining the formula for the difference of [corr] with the IH. *)
      assert (Hstep : e_sum (Datatypes.S (Datatypes.S m'')) a * e_sum (Datatypes.S (Datatypes.S m'')) a -
                      o_sum (Datatypes.S (Datatypes.S m'')) a * o_sum (Datatypes.S (Datatypes.S m'')) a ==
                      (e_sum (Datatypes.S m'') a * e_sum (Datatypes.S m'') a -
                       o_sum (Datatypes.S m'') a * o_sum (Datatypes.S m'') a) +
                      (corr (Datatypes.S (Datatypes.S m'')) a - corr (Datatypes.S m'') a)).
      { assert (Hd : corr (Datatypes.S (Datatypes.S m'')) a - corr (Datatypes.S m'') a ==
                     (e_sum (Datatypes.S (Datatypes.S m'')) a * e_sum (Datatypes.S (Datatypes.S m'')) a -
                      o_sum (Datatypes.S (Datatypes.S m'')) a * o_sum (Datatypes.S (Datatypes.S m'')) a) -
                     (e_sum (Datatypes.S m'') a * e_sum (Datatypes.S m'') a -
                      o_sum (Datatypes.S m'') a * o_sum (Datatypes.S m'') a)).
        { apply qeqT_imp_qeq. apply (corr_diff_eq_sq_diff a (Datatypes.S m'')). lia. }
        setoid_rewrite Hd.
        unfold Qminus. ring. }
      setoid_rewrite Hstep.
      setoid_rewrite IH.
      unfold Qminus. ring.
Qed.

(* ============ The [exp_even_neg_nonneg] argument ============
   [q_div_nonneg]/[e_sum_ge_one]/[o_sum_nonneg] (helpers: E >= 1 and O >= 0).
   [exp_even_mul_eq]: S_(2m)(−a) * S_(2m)(a) == 1 + corr m a (since (E−O)(E+O) = E^2−O^2).
   [exp_even_neg_nonneg]: 0 <= a implies 0 <= exp_partial (2*m) (−a) ([corr_nonneg] plus S(a) > 0
   plus the [field] identity). *)
Lemma q_div_nonneg : forall (x d : Q), QleT' 0 x -> QltT 0 d -> QleT' 0 (x / d).
Proof.
  intros x d Hx Hd.
  assert (HxQ : Qle 0 x) by (apply QleT'_to_Qle; exact Hx).
  assert (HdQ : Qlt 0 d) by (apply QltT_to_Qlt; exact Hd).
  apply Qle_to_QleT'.
  unfold Qdiv.
  exact (Qmult_le_0_compat x (Qinv d) HxQ
  (Qlt_le_weak 0 (Qinv d) (Qinv_lt_0_compat d HdQ))).
Qed.
Lemma e_sum_ge_one : forall (a : Q) (m : nat), QleT' 0 a -> QleT' 1 (e_sum m a).
Proof.
  intros a m Ha.
  apply Qle_to_QleT'.
  induction m as [| m' IH]; simpl.
  - apply Qle_refl.
  - apply (Qle_trans _ (e_sum m' a) _).
    + exact IH.
    + apply (Qle_trans _ (e_sum m' a + 0) _).
      * setoid_rewrite (Qplus_0_r (e_sum m' a)). apply Qle_refl.
      * apply (Qplus_le_compat (e_sum m' a) (e_sum m' a) 0 (q_pow a (2 * Datatypes.S m') / q_fact (2 * Datatypes.S m'))).
        -- apply Qle_refl.
        -- apply QleT'_to_Qle.
           apply (q_div_nonneg (q_pow a (2 * Datatypes.S m')) (q_fact (2 * Datatypes.S m'))).
           ++ apply (q_pow_nonneg a (2 * Datatypes.S m')). exact Ha.
           ++ apply q_fact_pos.
Qed.
Lemma o_sum_nonneg : forall (a : Q) (m : nat), QleT' 0 a -> QleT' 0 (o_sum m a).
Proof.
  intros a m Ha.
  apply Qle_to_QleT'.
  induction m as [| m' IH]; simpl.
  - exact (Qle_refl 0).
  - exact (Qplus_le_compat 0 (o_sum m' a) 0
  (q_pow a (Datatypes.S (2 * m')) / q_fact (Datatypes.S (2 * m')))
  IH (QleT'_to_Qle _ _ (q_div_nonneg (q_pow a (Datatypes.S (2 * m')))
  (q_fact (Datatypes.S (2 * m')))
  (q_pow_nonneg a (Datatypes.S (2 * m')) Ha)        (q_fact_pos (Datatypes.S (2 * m')))))).
Qed.
Lemma exp_even_mul_eq : forall (a : Q) (m : nat),QeqT (
  exp_partial (2 * m) (- a) * exp_partial (2 * m) a ) ( 1 + corr m a).
Proof.
  intros a m.
  apply qeq_imp_qeqT.
  setoid_rewrite (qeqT_imp_qeq _ _ (e_o_split_even a m)).
  setoid_rewrite (qeqT_imp_qeq _ _ (e_o_split_pos a m)).
  assert (Hring : (e_sum m a - o_sum m a) * (e_sum m a + o_sum m a) ==
                  e_sum m a * e_sum m a - o_sum m a * o_sum m a) by ring.
  setoid_rewrite Hring.
  setoid_rewrite (qeqT_imp_qeq _ _ (esq_eq_corr a m)).
  reflexivity.
Qed.
Lemma exp_even_neg_nonneg : forall (a : Q) (m : nat), QleT' 0 a -> QleT' 0 (exp_partial (2 * m) (- a)).
Proof.
  intros a m Ha.
  apply Qle_to_QleT'.
  assert (H01 : Qlt 0 1) by (unfold Qlt; simpl; lia).
  (* 1. 0 < S(−a) * S(a): since S(−a) * S(a) == 1 + corr >= 1 > 0. *)
  assert (Hmul_le : Qle 1 (exp_partial (2 * m) (- a) * exp_partial (2 * m) a)).
  { rewrite (qeqT_imp_qeq _ _ (exp_even_mul_eq a m)).
    apply (Qle_trans _ (1 + 0) _).
    - setoid_rewrite (Qplus_0_r 1). apply Qle_refl.
    - apply (Qplus_le_compat 1 1 0 (corr m a)).
      * apply Qle_refl.
      * apply QleT'_to_Qle.
        apply (corr_nonneg a m Ha). }
  assert (Hmul_pos : Qlt 0 (exp_partial (2 * m) (- a) * exp_partial (2 * m) a)).
  { apply (Qlt_le_trans 0 1 (exp_partial (2 * m) (- a) * exp_partial (2 * m) a)).
    - exact H01.
    - exact Hmul_le. }
  (* 2. 0 < S(a): since S(a) == E+O with E >= 1 > 0 and O >= 0, so E+O > 0. *)
  assert (Hspos : Qlt 0 (exp_partial (2 * m) a)).
  { setoid_rewrite (qeqT_imp_qeq _ _ (e_o_split_pos a m)).
    apply (Qlt_le_trans 0 (e_sum m a) (e_sum m a + o_sum m a)).
    - apply (Qlt_le_trans 0 1 (e_sum m a)).
      + exact H01.
      + apply QleT'_to_Qle.
        apply (e_sum_ge_one a m Ha).
    - apply (Qle_trans _ (e_sum m a + 0) _).
      * setoid_rewrite (Qplus_0_r (e_sum m a)). apply Qle_refl.
      * apply (Qplus_le_compat (e_sum m a) (e_sum m a) 0 (o_sum m a)).
        -- apply Qle_refl.
        -- apply QleT'_to_Qle.
           apply (o_sum_nonneg a m Ha). }
  (* 3. S(−a) == (S(−a) * S(a)) * inv(S(a)) (a [field] identity, using S(a) ≠ 0). *)
  assert (Hinv : exp_partial (2 * m) a * Qinv (exp_partial (2 * m) a) == 1).
  { apply Qmult_inv_r. intro Heq0. destruct (q_neq_of_lt (exp_partial (2 * m) a) (Qlt_to_QltT _ _ Hspos) (qeq_imp_qeqT _ _ Heq0)). }
  assert (Hfield : exp_partial (2 * m) (- a) ==
                   (exp_partial (2 * m) (- a) * exp_partial (2 * m) a) * Qinv (exp_partial (2 * m) a)).
  { transitivity (exp_partial (2 * m) (- a) *
                  (exp_partial (2 * m) a * Qinv (exp_partial (2 * m) a))).
    - setoid_rewrite Hinv. ring.
    - ring. }
  (* 4. (S(−a) * S(a)) * inv(S(a)) > 0 (positive times positive), hence S(−a) > 0, hence >= 0. *)
  assert (Hpos : Qlt 0 ((exp_partial (2 * m) (- a) * exp_partial (2 * m) a) * Qinv (exp_partial (2 * m) a))).
  { apply Qmult_lt_0_compat.
    - exact Hmul_pos.
    - apply Qinv_lt_0_compat. exact Hspos. }
  setoid_rewrite <- Hfield in Hpos.
  apply (Qlt_le_weak 0 (exp_partial (2 * m) (- a))). exact Hpos.
Qed.
(* ============ The [exp_partial_tail_pos] argument ============
   [exp_even_neg_pos]: 0 <= a implies 0 < exp_partial (2*m) (−a) (the strict form:
   S(−a) * S(a) >= 1 and S(a) > 0).
   [exp_partial_tail_pos]: 0 <= a implies 0 < exp_partial (2m+2) (−a) (the tail truncation is
   positive, the S m instance of [exp_even_neg_pos]).
   These feed [cauchy_real_exp_pos] (real_lt zero (cauchy_real_exp x)), the material for the
   exp_neg_pos field. *)
Lemma exp_even_neg_pos : forall (a : Q) (m : nat), QleT' 0 a -> QltT 0 (exp_partial (2 * m) (- a)).
Proof.
  intros a m Ha.
  apply Qlt_to_QltT.
  assert (H01 : Qlt 0 1) by (unfold Qlt; simpl; lia).
  assert (Hmul_le : Qle 1 (exp_partial (2 * m) (- a) * exp_partial (2 * m) a)).
  { rewrite (qeqT_imp_qeq _ _ (exp_even_mul_eq a m)).
    apply (Qle_trans _ (1 + 0) _).
    - setoid_rewrite (Qplus_0_r 1). apply Qle_refl.
    - apply (Qplus_le_compat 1 1 0 (corr m a)).
      * apply Qle_refl.
      * apply QleT'_to_Qle.
        apply (corr_nonneg a m Ha). }
  assert (Hmul_pos : Qlt 0 (exp_partial (2 * m) (- a) * exp_partial (2 * m) a)).
  { apply (Qlt_le_trans 0 1 (exp_partial (2 * m) (- a) * exp_partial (2 * m) a)).
    - exact H01.
    - exact Hmul_le. }
  assert (Hspos : Qlt 0 (exp_partial (2 * m) a)).
  { setoid_rewrite (qeqT_imp_qeq _ _ (e_o_split_pos a m)).
    apply (Qlt_le_trans 0 (e_sum m a) (e_sum m a + o_sum m a)).
    - apply (Qlt_le_trans 0 1 (e_sum m a)).
      + exact H01.
      + apply QleT'_to_Qle.
        apply (e_sum_ge_one a m Ha).
    - apply (Qle_trans _ (e_sum m a + 0) _).
      * setoid_rewrite (Qplus_0_r (e_sum m a)). apply Qle_refl.
      * apply (Qplus_le_compat (e_sum m a) (e_sum m a) 0 (o_sum m a)).
        -- apply Qle_refl.
        -- apply QleT'_to_Qle.
           apply (o_sum_nonneg a m Ha). }
  assert (Hinv : exp_partial (2 * m) a * Qinv (exp_partial (2 * m) a) == 1).
  { apply Qmult_inv_r. intro Heq0. destruct (q_neq_of_lt (exp_partial (2 * m) a) (Qlt_to_QltT _ _ Hspos) (qeq_imp_qeqT _ _ Heq0)). }
  assert (Hfield : exp_partial (2 * m) (- a) ==
                   (exp_partial (2 * m) (- a) * exp_partial (2 * m) a) * Qinv (exp_partial (2 * m) a)).
  { transitivity (exp_partial (2 * m) (- a) *
                  (exp_partial (2 * m) a * Qinv (exp_partial (2 * m) a))).
    - setoid_rewrite Hinv. ring.
    - ring. }
  assert (Hpos : Qlt 0 ((exp_partial (2 * m) (- a) * exp_partial (2 * m) a) * Qinv (exp_partial (2 * m) a))).
  { apply Qmult_lt_0_compat.
    - exact Hmul_pos.
    - apply Qinv_lt_0_compat. exact Hspos. }
  setoid_rewrite <- Hfield in Hpos.
  exact Hpos.
Qed.

Lemma exp_partial_tail_pos : forall (a : Q) (m : nat), QleT' 0 a -> QltT 0 (exp_partial (2 * m + 2) (- a)).
Proof.
  intros a m Ha.
  apply Qlt_to_QltT.
  assert (Hn : (2 * Datatypes.S m = 2 * m + 2)%nat) by lia.
  setoid_replace (exp_partial (2 * m + 2) (- a)) with (exp_partial (2 * Datatypes.S m) (- a)).
  2: { change (exp_partial (2 * m + 2) (- a) == exp_partial (2 * Datatypes.S m) (- a)).
       rewrite <- Hn. reflexivity. }
  apply QltT_to_Qlt. apply (exp_even_neg_pos a (Datatypes.S m)). exact Ha.
Qed.

(* The even truncation is positive for any argument: for all y, 0 < exp_partial (2*m) y.
   Trichotomy by [Qlt_le_dec]: for 0 < y the sum of nonnegative terms is >= 1 > 0; for y <= 0
   exp_pair_alt m (−y) > 0 by [exp_even_neg_pos]. *)
Lemma exp_even_all_pos : forall (y : Q) (m : nat), QltT 0 (exp_partial (2 * m) y).
Proof.
  intros y m.
  apply Qlt_to_QltT.
  destruct (Qlt_le_dec 0 y) as [Hy | Hy0].
  - (* Case 0 < y: ep (2m) y >= 1 > 0 (a sum of nonnegative terms). *)
    assert (Hy0' : QleT' 0 y) by (apply Qle_to_QleT'; apply (Qlt_le_weak 0 y); exact Hy).
    assert (Hle : Qle 1 (exp_partial (2 * m) y)).
    { induction m as [| m' IH].
      + simpl. apply Qle_refl.
      + assert (Hidx : (2 * Datatypes.S m' = Datatypes.S (Datatypes.S (2 * m')))%nat) by lia.
        rewrite Hidx. simpl.
        assert (HT1 : Qle 0 (q_pow y (Datatypes.S (2 * m')) / q_fact (Datatypes.S (2 * m')))).
        { apply QleT'_to_Qle.
          apply (q_div_nonneg (q_pow y (Datatypes.S (2 * m'))) (q_fact (Datatypes.S (2 * m')))).
          - apply (q_pow_nonneg y (Datatypes.S (2 * m'))). exact Hy0'.
          - apply q_fact_pos. }
        assert (HT2 : Qle 0 (q_pow y (Datatypes.S (Datatypes.S (2 * m'))) / q_fact (Datatypes.S (Datatypes.S (2 * m'))))).
        { apply QleT'_to_Qle.
          apply (q_div_nonneg (q_pow y (Datatypes.S (Datatypes.S (2 * m')))) (q_fact (Datatypes.S (Datatypes.S (2 * m'))))).
          - apply (q_pow_nonneg y (Datatypes.S (Datatypes.S (2 * m')))). exact Hy0'.
          - apply q_fact_pos. }
        apply (Qle_trans _ (exp_partial (2 * m') y) _).
        * exact IH.
        * apply (Qle_trans _ (exp_partial (2 * m') y +
                              q_pow y (Datatypes.S (2 * m')) / q_fact (Datatypes.S (2 * m'))) _).
          -- apply (Qle_trans _ (exp_partial (2 * m') y + 0) _).
             ++ setoid_rewrite (Qplus_0_r (exp_partial (2 * m') y)). apply Qle_refl.
             ++ apply (Qplus_le_compat (exp_partial (2 * m') y) (exp_partial (2 * m') y) 0
                        (q_pow y (Datatypes.S (2 * m')) / q_fact (Datatypes.S (2 * m')))).
                ** apply Qle_refl.
                ** exact HT1.
          -- apply (Qle_trans _ (exp_partial (2 * m') y +
                                q_pow y (Datatypes.S (2 * m')) / q_fact (Datatypes.S (2 * m')) + 0) _).
             ++ setoid_rewrite (Qplus_0_r (exp_partial (2 * m') y +
                                         q_pow y (Datatypes.S (2 * m')) / q_fact (Datatypes.S (2 * m')))). apply Qle_refl.
             ++ apply (Qplus_le_compat (exp_partial (2 * m') y +
                                       q_pow y (Datatypes.S (2 * m')) / q_fact (Datatypes.S (2 * m')))
                                     (exp_partial (2 * m') y +
                                      q_pow y (Datatypes.S (2 * m')) / q_fact (Datatypes.S (2 * m')))
                                     0 (q_pow y (Datatypes.S (Datatypes.S (2 * m'))) / q_fact (Datatypes.S (Datatypes.S (2 * m'))))).
                ** apply Qle_refl.
                ** exact HT2. }
    apply (Qlt_le_trans 0 1 (exp_partial (2 * m) y)).
    + unfold Qlt; simpl; lia.
    + exact Hle.
  - (* Case y <= 0: ep (2m) y = exp_pair_alt m (−y) > 0 ([exp_even_neg_pos] applied at −y >= 0). *)
    assert (Hny : Qle 0 (- y)).
    { change (Qle 0 (- y)) with (Qle (- 0) (- y)).
      apply (Qopp_le_compat y 0). exact Hy0. }
    assert (Hp : Qlt 0 (exp_partial (2 * m) (- (- y)))).
    { apply QltT_to_Qlt. apply (exp_even_neg_pos (- y) m). apply Qle_to_QleT'. exact Hny. }
    destruct y as [n d].
    destruct n; exact Hp.
Qed.
(* ============================================================
   The [cauchy_real_exp_pos] argument (the final step: material for the exp_neg_pos field).
   Goal: real_lt zero (cauchy_real_exp x).
   Strategy: a uniform lower bound 1/C for the even truncations ([exp_even_mul_eq] plus
   [corr_nonneg] plus [exp_series_arch]: S_(2m)(-a) * S_(2m)(a) == 1+corr >= 1 and
   S_(2m)(a) <= C, hence S_(2m)(-a) >= 1/C; for y >= 0, S_(2m)(y) >= 1 >= 1/C);
   the odd truncations are covered by the decay of the tail term
   (|y|^(2m+1)/(2m+1)! < 1/(2C) once 2m+1 >= m0).
   ============================================================ *)

(* 0b. [exp_partial] and [exp_series] are definitionally isomorphic: exp_partial n x == exp_series n x. *)
Lemma exp_partial_eq_series : forall (n : nat) (x : Q),QeqT ( exp_partial n x ) ( exp_series n x).
Proof.
  intros n x.
  apply qeq_imp_qeqT.
  induction n as [| m IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

(* 0c. Well-definedness of [exp_partial] in its argument: x == y implies exp_partial n x == exp_partial n y. *)
Lemma exp_partial_wd : forall (n : nat) (x y : Q),QeqT ( x ) ( y )->QeqT ( exp_partial n x ) ( exp_partial n y).
Proof.
  intros n x y Hxy.
  apply qeq_imp_qeqT.
  induction n as [| m IH]; simpl.
  - reflexivity.
  - rewrite IH.
    rewrite (qeqT_imp_qeq _ _ (q_pow_wd x y (Datatypes.S m) Hxy)).
    reflexivity.
Qed.

(* 1. Monotonicity of [exp_series] in its second argument: 0 <= B1 <= B2 implies exp_series n B1 <= exp_series n B2. *)
Lemma exp_series_arg_mono : forall (B1 B2 : Q) (n : nat),
  QleT' 0 B1 -> QleT' B1 B2 -> QleT' (exp_series n B1) (exp_series n B2).
Proof.
  intros B1 B2 n HB1 HB12.
  apply Qle_to_QleT'.
  induction n as [| n IH]; simpl.
  - apply Qle_refl.
  - apply Qplus_le_compat.
    + exact IH.
    + apply QleT'_to_Qle.
      apply (Qle_div_same_denom (q_pow B1 (Datatypes.S n)) (q_pow B2 (Datatypes.S n))
                               (q_fact (Datatypes.S n))).
      * apply q_fact_pos.
      * apply q_pow_mono; [exact HB1 | exact HB12].
Qed.

(* 2. Any truncation with a nonnegative argument is at least 1: 0 <= y implies 1 <= exp_partial n y (each step adds a nonnegative term). *)
Lemma exp_partial_ge_one : forall (y : Q) (n : nat), QleT' 0 y -> QleT' 1 (exp_partial n y).
Proof.
  intros y n Hy.
  apply Qle_to_QleT'.
  induction n as [| n IH]; simpl.
  - apply Qle_refl.
  - apply (Qle_trans _ (exp_partial n y) _).
    + exact IH.
    + apply (Qle_plus_nonneg_r (exp_partial n y) (q_pow y (Datatypes.S n) / q_fact (Datatypes.S n))).
      apply QleT'_to_Qle.
      apply q_pow_fact_nonneg. exact Hy.
Qed.

(* 3. exp_partial (2m) a <= C: for 0 <= a <= M, the uniform bound (exp_series n M <= C for all n) implies exp_partial (2m) a <= C. *)
Lemma exp_partial_even_upper : forall (a M C : Q) (m : nat),
  QleT' 0 M -> QleT' 0 a -> QleT' a M ->
  (forall n : nat, QleT' (exp_series n M) C) ->
  QleT' (exp_partial (2 * m) a) C.
Proof.
  intros a M C m HM Ha Ham HC.
  apply Qle_to_QleT'.
  exact (Qle_trans (exp_partial (2 * m) a) (exp_series (2 * m) a) C
    (QleT'_to_Qle _ _ (qeq_le (exp_partial (2 * m) a) (exp_series (2 * m) a)
      (qeq_imp_qeqT (exp_partial (2 * m) a) (exp_series (2 * m) a)
      (qeqT_imp_qeq _ _ (exp_partial_eq_series (2 * m) a)))))
    (Qle_trans (exp_series (2 * m) a) (exp_series (2 * m) M) C
      (QleT'_to_Qle _ _ (exp_series_arg_mono a M (2 * m)%nat Ha Ham))
      (QleT'_to_Qle _ _ (HC (2 * m)%nat)))).
Qed.

(* 4. Uniform lower bound for the even truncations: |y| <= M implies 1/C <= exp_partial (2m) y.
   For y >= 0 use that the sum of nonnegative terms is >= 1; for y <= 0 use
   S(-a) * S(a) == 1+corr >= 1 together with S(a) <= C, giving S(-a) >= 1/C. *)
Lemma exp_partial_even_lower : forall (M C : Q) (y : Q) (m : nat),
  QleT' 0 M -> QleT' 1 C ->
  (forall n : nat, QleT' (exp_series n M) C) ->
  QleT' (Qabs y) M -> QleT' (1 / C) (exp_partial (2 * m) y).
Proof.
  intros M C y m HM HC HCser Hy.
  apply Qle_to_QleT'.
  destruct (Qlt_le_dec 0 y) as [Hypos | Hyneg].
  - (* Case 0 < y: the sum of nonnegative terms is >= 1 >= 1/C. *)
    apply (Qle_trans _ 1 _).
    + (* 1/C <= 1: write 1/C == 1 * Qinv C, with Qinv C <= Qinv 1 == 1 and 1*x == x. *)
      change (Qle (1 * Qinv C) 1).
      apply (Qle_trans _ (Qinv C) _).
      * apply QleT'_to_Qle.
        apply qeq_leT'.
        apply qeq_imp_qeqT.
        apply (Qmult_1_l (Qinv C)).
      * apply QleT'_to_Qle.
        apply (q_inv_le_contravar C 1).
        -- apply Qlt_to_QltT.
           apply (Qlt_le_trans _ 1 _); [reflexivity | exact (QleT'_to_Qle _ _ HC)].
        -- apply Qlt_to_QltT.
           unfold Qlt; simpl; lia.
        -- exact HC.
    + apply QleT'_to_Qle. apply exp_partial_ge_one. apply Qle_to_QleT'. apply (Qlt_le_weak 0 y). exact Hypos.
  - (* Case y <= 0: put a = -y >= 0; then S_(2m)(-a) >= 1/S_(2m)(a) >= 1/C. *)
    assert (Ha : Qle 0 (- y)).
    { change (Qle 0 (- y)) with (Qle (- 0) (- y)).
      apply (Qopp_le_compat y 0). exact Hyneg. }
    assert (Ham : Qle (- y) M).
    { assert (Habs : Qabs y == - y) by (apply Qabs_neg; exact Hyneg).
      rewrite <- Habs. exact (QleT'_to_Qle _ _ Hy). }
    (* S_(2m)(a) >= 1 > 0 and S_(2m)(a) <= C, with a = -y. *)
    assert (Hsa_pos : Qlt 0 (exp_partial (2 * m) (- y))).
    { apply (Qlt_le_trans _ 1 _).
      - unfold Qlt; simpl; lia.
      - apply QleT'_to_Qle. apply exp_partial_ge_one. apply Qle_to_QleT'. exact Ha. }
    assert (Hsa_le : Qle (exp_partial (2 * m) (- y)) C).
    { apply QleT'_to_Qle.
      apply (exp_partial_even_upper (- y) M C m).
      - exact HM.
      - apply Qle_to_QleT'. exact Ha.
      - apply Qle_to_QleT'. exact Ham.
      - exact HCser. }
    (* 1 <= S(-(-y)) * S(-y), by [exp_even_mul_eq] plus [corr_nonneg]. *)
    assert (Hmul : Qle 1 (exp_partial (2 * m) (- (- y)) * exp_partial (2 * m) (- y))).
    { rewrite (qeqT_imp_qeq _ _ (exp_even_mul_eq (- y) m)).
      apply (Qle_trans _ (1 + 0) _).
      - setoid_rewrite (Qplus_0_r 1). apply Qle_refl.
      - apply (Qplus_le_compat 1 1 0 (corr m (- y))).
        * apply Qle_refl.
        * apply QleT'_to_Qle.
          apply (corr_nonneg (- y) m).
          apply Qle_to_QleT'. exact Ha. }
    (* Goal 1/C <= S_(2m)(y): since y == -(-y), the chain 1/C <= 1/S(-y) <= S(-(-y)) applies, then [exp_partial_wd] transports back to y. *)
    assert (Hyid : y == - (- y)) by ring.
    apply (Qle_trans _ (exp_partial (2 * m) (- (- y))) _).
    { (* 1/C <= S(-(-y)): the chain 1/C <= 1/S(-y) <= S(-(-y)). *)
      apply (Qle_trans _ (1 / exp_partial (2 * m) (- y)) _).
      { (* 1/C <= 1/S(-y): first cancel the 1 * factor (the shapes Qdiv 1 x and Qinv x differ),
         then apply [q_inv_le_contravar] (Qinv C <= Qinv S), and finally restore the 1 * factor. *)
        apply (Qle_trans _ (Qinv C) _).
        - (* 1/C <= Qinv C: 1 * Qinv C == Qinv C. *)
          apply QleT'_to_Qle.
          apply qeq_leT'.
          apply qeq_imp_qeqT.
          apply (Qmult_1_l (Qinv C)).
        - apply (Qle_trans _ (Qinv (exp_partial (2 * m) (- y))) _).
          + (* Qinv C <= Qinv S(-y): [q_inv_le_contravar] (with 0 < S(-y) <= C). *)
            apply QleT'_to_Qle.
            apply (q_inv_le_contravar C (exp_partial (2 * m) (- y))).
            * apply Qlt_to_QltT.
              apply (Qlt_le_trans _ 1 _); [reflexivity | exact (QleT'_to_Qle _ _ HC)].
            * apply Qlt_to_QltT. exact Hsa_pos.
            * exact (Qle_to_QleT' _ _ Hsa_le).
          + (* Qinv S(-y) <= 1 * Qinv S(-y) == 1/S(-y): restore the 1 * factor. *)
            apply QleT'_to_Qle.
            apply qeq_leT'.
            apply qeq_imp_qeqT.
            apply Qeq_sym. apply (Qmult_1_l (Qinv (exp_partial (2 * m) (- y)))). }
      { (* 1/S(-y) <= S(-(-y)): apply [Qle_shift_div_r 1 (S(-y)) (S(-(-y)))], which needs 1 <= S(-(-y)) * S(-y). *)
        apply (Qle_shift_div_r 1 (exp_partial (2 * m) (- y))
                                (exp_partial (2 * m) (- (- y)))).
        - exact Hsa_pos.
        - exact Hmul. } }
    { (* S(-(-y)) <= S(y): rewrite along y == -(-y) ([qeq_le], the well-defined form). *)
      apply QleT'_to_Qle.
      apply qeq_leT'.
      apply (exp_partial_wd (2 * m) (- (- y)) y).
      apply qeq_imp_qeqT.
      apply Qeq_sym.
      exact Hyid. }
Qed.

(* 5. Decay of the tail term: there is m0 with M^(2m+1)/(2m+1)! < 1/(2C) for all m >= m0.
   ([q_arch_geom] supplies the Archimedean bound N0; [arch_decay] gives
   (A^(N0)/N0! * 2) * (1/2)^(S t) < 1/C; [exp_tail_arch] concludes:
   for b >= N0 + S t, (A^b/b!) * 2 < 1/C, hence A^b/b! < 1/(2C).) *)
Lemma exp_partial_tail_small : forall (M C : Q), QleT' 0 M -> QleT' 1 C ->
  sigT (fun m0 : nat => forall m : nat, NatLe m0 m ->
    QltT (q_pow M (2 * m + 1) / q_fact (2 * m + 1)) (1 / (2 * C))).
Proof.
  intros M C HM HC.
  destruct (q_arch_geom M) as [N0 HN0].
  assert (HCpos : Qlt 0 C) by (apply (Qlt_le_trans _ 1 _); [reflexivity | exact (QleT'_to_Qle _ _ HC)]).
  assert (Hinv : Qlt 0 (1 / C)).
  { apply (Qlt_le_trans _ (Qinv C) _).
    - apply Qinv_lt_0_compat. exact HCpos.
    - apply QleT'_to_Qle.
      apply qeq_leT'.
      apply qeq_imp_qeqT.
      apply Qeq_sym. apply (Qmult_1_l (Qinv C)). }
  destruct (arch_decay ((q_pow M N0 / q_fact N0) * (1 + 1)%Q) (1 / C)) as [t Ht].
  { apply q_pow_fact2_nonneg. exact HM. }
  { apply Qlt_to_QltT. exact Hinv. }
  exists (N0 + Datatypes.S t)%nat.
  intros m Hm.
  apply NatLe_drop in Hm.
  apply Qlt_to_QltT.
  assert (Hb : (N0 + Datatypes.S t <= 2 * m + 1)%nat) by lia.
  (* (M^(2m+1)/(2m+1)!) * 2 < 1/C. *)
  assert (Harch : Qlt ((q_pow M (2 * m + 1) / q_fact (2 * m + 1)) * (1 + 1)%Q) (1 / C)).
  { apply QltT_to_Qlt.
    apply (exp_tail_arch M N0 t (2 * m + 1) (1 / C) HM
             (fun u Hu => HN0 u Hu)
             (Qlt_to_QltT _ _ Hinv) Ht Hb). }
  (* From x * (1+1) < 1/C conclude x < (1/C)/(1+1) == 1/(2C). *)
  apply (Qlt_le_trans _ ((1 / C) / (1 + 1)%Q) _).
  - apply (Qlt_shift_div_l (q_pow M (2 * m + 1) / q_fact (2 * m + 1)) (1 / C) (1 + 1)%Q).
    + unfold Qlt; simpl; lia.
    + exact Harch.
  - apply QleT'_to_Qle.
    apply qeq_leT'.
    apply qeq_imp_qeqT.
    unfold Qdiv.
    field.
    intro Heq0. destruct (q_neq_of_lt C (Qlt_to_QltT _ _ HCpos) (qeq_imp_qeqT _ _ Heq0)).
Qed.

(* 6. Uniform lower bound for the odd truncations: |y| <= M and m >= m0 imply
   1/(2C) < exp_partial (2m+1) y.
   (S_(2m+1)(y) == S_(2m)(y) + y^(2m+1)/(2m+1)!. For y >= 0 the sum of nonnegative terms is >= 1;
   for y <= 0, S_(2m)(y) >= 1/C and |y|^(2m+1)/(2m+1)! < 1/(2C).) *)
Lemma exp_partial_odd_lower : forall (M C : Q) (m0 m : nat) (y : Q),
  QleT' 0 M -> QleT' 1 C ->
  (forall n : nat, QleT' (exp_series n M) C) ->
  (forall k : nat, NatLe m0 k ->
    QltT (q_pow M (2 * k + 1) / q_fact (2 * k + 1)) (1 / (2 * C))) ->
  (m0 <= m)%nat ->
  QleT' (Qabs y) M -> QltT (1 / (2 * C)) (exp_partial (2 * m + 1) y).
Proof.
  intros M C m0 m y HM HC HCser Htail Hm0 Hy.
  apply Qlt_to_QltT.
  assert (Hidx : (2 * m + 1 = Datatypes.S (2 * m))%nat) by lia.
  rewrite Hidx.
  destruct (Qlt_le_dec 0 y) as [Hypos | Hyneg].
  - (* Case 0 < y: the sum of nonnegative terms is >= 1 > 1/(2C). *)
    apply (Qlt_le_trans _ 1 _).
    + (* 1/(2C) < 1: indeed 1/(2C) <= 1/2 < 1. *)
      apply (Qle_lt_trans _ (1 / 2) _).
      * (* 1/(2C) <= 1/2. *)
        apply (Qle_shift_div_r 1 (2 * C) (1 / 2)).
        -- apply (Qmult_lt_0_compat 2 C).
           ++ unfold Qlt; simpl; lia.
           ++ apply (Qlt_le_trans _ 1 _); [reflexivity | exact (QleT'_to_Qle _ _ HC)].
        -- (* 1 <= (1/2) * (2C): bridge through 1 <= C == (1/2) * (2C). *)
           apply (Qle_trans _ C _).
           ++ exact (QleT'_to_Qle _ _ HC).  (* 1 <= C *)
      ++ apply QleT'_to_Qle. apply qeq_leT'. apply qeq_imp_qeqT.
         unfold Qdiv. field.
      * reflexivity.  (* 1/2 < 1 is decidable by computation *)
    + apply QleT'_to_Qle. apply exp_partial_ge_one. apply Qle_to_QleT'. apply (Qlt_le_weak 0 y). exact Hypos.
  - (* Case y <= 0: S_(2m+1)(y) == S_(2m)(y) - |y|^(2m+1)/(2m+1)! >= 1/C - M^(2m+1)/(2m+1)! > 1/(2C). *)
    assert (Ha : Qle 0 (- y)).
    { change (Qle 0 (- y)) with (Qle (- 0) (- y)).
      apply (Qopp_le_compat y 0). exact Hyneg. }
    assert (Ham : Qle (- y) M).
    { assert (Habs : Qabs y == - y) by (apply Qabs_neg; exact Hyneg).
      rewrite <- Habs. exact (QleT'_to_Qle _ _ Hy). }
    assert (Hsl : Qle (1 / C) (exp_partial (2 * m) y)).
    { apply QleT'_to_Qle. apply (exp_partial_even_lower M C y m HM HC HCser). exact Hy. }
    (* Bound on the tail term: y^(2m+1) == -|y|^(2m+1) and |y|^(2m+1)/(2m+1)! <= M^(2m+1)/(2m+1)! < 1/(2C). *)
    assert (Htail_le : Qle (q_pow (Qabs y) (2 * m + 1) / q_fact (2 * m + 1))
                           (q_pow M (2 * m + 1) / q_fact (2 * m + 1))).
    { apply QleT'_to_Qle.
      apply (q_le_div_le (q_pow (Qabs y) (2 * m + 1)) (q_fact (2 * m + 1))
                         (q_pow M (2 * m + 1)) (q_fact (2 * m + 1))).
      - apply q_fact_pos.
      - apply q_fact_pos.
      - apply Qle_to_QleT'.
        apply (Qmult_le_compat_r (q_pow (Qabs y) (2 * m + 1)) (q_pow M (2 * m + 1))
                                 (q_fact (2 * m + 1))).
        + apply QleT'_to_Qle.
          apply q_pow_mono.
          * apply Qle_to_QleT'. apply Qabs_nonneg.
          * exact Hy.
        + apply QleT'_to_Qle.
          apply qltT_leT'. apply q_fact_pos. }
    assert (Htail_lt : Qlt (q_pow (Qabs y) (2 * m + 1) / q_fact (2 * m + 1))
                           (1 / (2 * C))).
    { apply (Qle_lt_trans _ (q_pow M (2 * m + 1) / q_fact (2 * m + 1)) _).
      - exact Htail_le.
      - exact (QltT_to_Qlt _ _ (Htail m (NatLe_lift _ _ Hm0))). }
    (* S_(2m+1)(y) == S_(2m)(y) - |y|^(2m+1)/(2m+1)!. *)
    assert (Hstep : exp_partial (Datatypes.S (2 * m)) y ==
                    exp_partial (2 * m) y -
                    q_pow (Qabs y) (2 * m + 1) / q_fact (2 * m + 1)).
    { assert (Hodd : q_pow y (Datatypes.S (2 * m)) == - q_pow (Qabs y) (Datatypes.S (2 * m))).
      { assert (Hm1 : Qabs y == - y) by (apply Qabs_neg; exact Hyneg).
        assert (Hy2 : y == - (Qabs y)).
        { transitivity (- (- y)).
          - apply Qeq_sym. apply Qopp_involutive.  (* y == -(-y) *)
          - apply (Qopp_comp (- y) (Qabs y)). exact (Qeq_sym _ _ Hm1). }
        (* y^(S(2m)) == (-|y|)^(S(2m)) == -|y|^(S(2m)): bridge y == -|y| with [q_pow_wd]; then
           [q_pow_neg_odd] gives (-|y|)^(S(2m)) == -|y|^(S(2m)) (avoid [setoid_rewrite], which
           would also rewrite the [Qabs] subterms). *)
        transitivity (q_pow (- (Qabs y)) (Datatypes.S (2 * m))).
        - apply qeqT_imp_qeq.
          apply (q_pow_wd y (- (Qabs y)) (Datatypes.S (2 * m))).
          apply qeq_imp_qeqT. exact Hy2.
        - apply qeqT_imp_qeq. apply (q_pow_neg_odd (Qabs y) m). }
      (* Bridge the exponent: S (2m) == 2m+1 ([q_pow_comp_proper] transports the [Qeq]; [lia] proves the [nat] equality). *)
      assert (Hidx_pow : q_pow (Qabs y) (Datatypes.S (2 * m)) == q_pow (Qabs y) (2 * m + 1)).
      { apply (q_pow_comp_proper (Qabs y) (Qabs y) (Qeq_refl (Qabs y))
                                (Datatypes.S (2 * m))%nat (2 * m + 1)%nat).
        lia. }
      assert (Hfn : (Datatypes.S (2 * m) = 2 * m + 1)%nat) by lia.
      assert (Hfq : q_fact (Datatypes.S (2 * m)) == q_fact (2 * m + 1)).
      { apply qeqT_imp_qeq. apply q_fact_nat_eq. exact Hfn. }
      (* Core: y^(S(2m))/q_fact(S(2m)) == -|y|^(2m+1)/(2m+1)!. *)
      assert (Hsub : q_pow y (Datatypes.S (2 * m)) / q_fact (Datatypes.S (2 * m)) ==
                     - (q_pow (Qabs y) (2 * m + 1) / q_fact (2 * m + 1))).
      { unfold Qdiv.
        setoid_rewrite Hodd.
        setoid_rewrite Hidx_pow.
        setoid_rewrite Hfq.
        ring. }
      (* Assemble: exp_partial (S(2m)) y == exp_partial (2m) y + the tail term == the goal's right side. *)
      transitivity (exp_partial (2 * m) y + q_pow y (Datatypes.S (2 * m)) / q_fact (Datatypes.S (2 * m))).
      - reflexivity.  (* exp_partial unfolds definitionally: S(2m) = S (2*m) and 2*m = 2*m *)
      - setoid_rewrite Hsub. ring. }
    rewrite Hstep.
    (* 1/C - |y|^(2m+1)/(2m+1)! > 1/(2C): since 1/(2C) == 1/C - 1/(2C) < 1/C - t whenever t < 1/(2C). *)
    apply (Qlt_le_trans _ (1 / C - q_pow (Qabs y) (2 * m + 1) / q_fact (2 * m + 1)) _).
    + (* 1/(2C) < 1/C - t: by the [Qlt_minus_iff] equivalence. *)
      apply (Qlt_minus_iff (1 / (2 * C)) (1 / C - q_pow (Qabs y) (2 * m + 1) / q_fact (2 * m + 1))).
      assert (Htmp : 1 / C - q_pow (Qabs y) (2 * m + 1) / q_fact (2 * m + 1) +
                     - (1 / (2 * C)) ==
                     1 / (2 * C) - q_pow (Qabs y) (2 * m + 1) / q_fact (2 * m + 1)).
      { field.
        split.
        - intro Heq0. destruct (q_neq_of_lt _ (q_fact_pos _) (qeq_imp_qeqT _ _ Heq0)).
        - assert (Hlt0C : Qlt 0 C) by (apply (Qlt_le_trans _ 1 _); [reflexivity | exact (QleT'_to_Qle _ _ HC)]). intro Heq0. destruct (q_neq_of_lt C (Qlt_to_QltT _ _ Hlt0C) (qeq_imp_qeqT _ _ Heq0)). }
      setoid_rewrite Htmp.
      change (Qlt 0 (1 / (2 * C) + - (q_pow (Qabs y) (2 * m + 1) / q_fact (2 * m + 1)))).
      apply (proj1 (Qlt_minus_iff (q_pow (Qabs y) (2 * m + 1) / q_fact (2 * m + 1)) (1 / (2 * C)))).
      exact Htail_lt.
    + (* 1/C - t <= S_(2m)(y) - t: order-preserving subtraction of [Hsl] (rewrite -t == +(-t) first). *)
      assert (Hrep : 1 / C - q_pow (Qabs y) (2 * m + 1) / q_fact (2 * m + 1) ==
                     1 / C + - (q_pow (Qabs y) (2 * m + 1) / q_fact (2 * m + 1))) by ring.
      apply (Qle_trans _ (1 / C + - (q_pow (Qabs y) (2 * m + 1) / q_fact (2 * m + 1))) _).
{ apply QleT'_to_Qle. apply qeq_leT'. apply qeq_imp_qeqT. exact Hrep. }
      { apply (Qle_trans _ (exp_partial (2 * m) y +
                            - (q_pow (Qabs y) (2 * m + 1) / q_fact (2 * m + 1))) _).
        { apply (Qplus_le_compat (1 / C) (exp_partial (2 * m) y)
                               (- (q_pow (Qabs y) (2 * m + 1) / q_fact (2 * m + 1)))
                               (- (q_pow (Qabs y) (2 * m + 1) / q_fact (2 * m + 1)))).
          - exact Hsl.
          - apply Qle_refl. }
{ apply QleT'_to_Qle. apply qeq_leT'. apply qeq_imp_qeqT. ring. } }
Qed.

(* ============================================================
   Main theorem [cauchy_real_exp_pos]: forall x : Real, real_lt zero (cauchy_real_exp x)
   (the final step: material instantiating the exp_neg_pos field).
   Strategy: the sequence u is bounded, |u n| <= M; [exp_series_arch] provides C
   (exp_series n M <= C); the even truncations are at least 1/C ([exp_partial_even_lower])
   and the odd truncations at least 1/(2C) ([exp_partial_tail_small] picking m0 plus
   [exp_partial_odd_lower]);
   take eps = 1/(2C) and N = 2*m0+1, which covers both parities for n >= N.
   ============================================================ *)
Lemma cauchy_real_exp_pos : forall x : Real, real_lt real_zero (cauchy_real_exp x).
Proof.
  intros x. destruct x as [u Hu].
  destruct (real_norm_bounded (existT (fun s : Qseq => cauchy s) u Hu)) as [M [HMpos HM]].
  destruct (exp_series_arch M (qltT_leT' 0 M HMpos)) as [C [HC1 HC]].
  assert (HCposT : QltT 0 C).
  { apply (qltT_leT'_ltT 0 1 C). exact qltT_0_1. exact HC1. }
  destruct (exp_partial_tail_small M C (qltT_leT' 0 M HMpos) HC1) as [m0 Hm0].
  (* Build the real_lt witness: eps = 1/(2C) (the Set-level positivity chain) and N = 2*m0 + 1. *)
  exists (1 / (2 * C)).
  split.
  - apply (qltT_div_pos 1 (2 * C)).
    + exact qltT_0_1.
    + apply (qmult_ltT_0_compat 2 C). exact qltT_0_2. exact HCposT.
  - exists (2 * m0 + 1)%nat.
    intros n Hn.
    assert (Hsub0 : exp_partial n (u n) - 0 == exp_partial n (u n)) by ring.
      change (QltT (1 / (2 * C)) (exp_partial n (u n) - 0)).
    apply (qltT_eq_compat_r (exp_partial n (u n) - 0) (exp_partial n (u n)) (1 / (2 * C))).
    + apply qeq_imp_qeqT. exact Hsub0.
    + (* Goal QltT (1/(2C)) (exp_partial n (u n)): convert to Prop and split by parity ([ex] removes the restriction). *)
      apply Qlt_to_QltT.
      destruct (Nat.odd n) eqn:En.
      * (* n odd: n = 2k+1, and m0 <= k is needed. *)
        apply Nat.odd_spec in En. destruct En as [k Hk].
        subst n.
        apply NatLe_drop in Hn.
        assert (Hk0 : (m0 <= k)%nat) by lia.
        apply QltT_to_Qlt.
        apply (exp_partial_odd_lower M C m0 k (u (2 * k + 1)%nat) (qltT_leT' 0 M HMpos) HC1 HC Hm0 Hk0).
        exact (HM (2 * k + 1)%nat).
      * (* n even: n = 2k, and 1/(2C) < 1/C <= exp_partial (2k) (u (2k)). *)
        assert (Heven_true : Nat.even n = true).
        { rewrite <- (Nat.negb_odd n).
          rewrite En. reflexivity. }
        apply Nat.even_spec in Heven_true. destruct Heven_true as [k Hk].
        subst n.
        apply (Qlt_le_trans _ (1 / C) _).
        -- (* 1/(2C) < 1/C *)
           apply (Qlt_minus_iff (1 / (2 * C)) (1 / C)).
           unfold Qdiv.
           assert (Hf : 1 / C + - (1 / (2 * C)) == 1 / (2 * C)).
           { field.
             assert (Hlt0C : Qlt 0 C) by (apply (Qlt_le_trans _ 1 _); [reflexivity | exact (QleT'_to_Qle _ _ HC1)]).
             intro Heq0. destruct (q_neq_of_lt C (Qlt_to_QltT _ _ Hlt0C) (qeq_imp_qeqT _ _ Heq0)). }
           setoid_rewrite Hf.
           apply (Qlt_le_trans _ (Qinv (2 * C)) _).
           { apply Qinv_lt_0_compat.
             apply (Qmult_lt_0_compat 2 C).
             - unfold Qlt; simpl; lia.
             - apply (Qlt_le_trans _ 1 _); [reflexivity | exact (QleT'_to_Qle _ _ HC1)]. }
        { apply QleT'_to_Qle. apply qeq_leT'.
          apply qeq_imp_qeqT.
          apply Qeq_sym. apply (Qmult_1_l (Qinv (2 * C))). }
        -- (* 1/C <= exp_partial (2k) (u (2k)). *)
           apply QleT'_to_Qle.
           apply (exp_partial_even_lower M C (u (2 * k)%nat) k (qltT_leT' 0 M HMpos) HC1 HC).
           exact (HM (2 * k)%nat).
Qed.

(* Reverse triangle inequality: | |a| − |b| | <= |a − b| (the [Qle] form at the Prop level; the
   core of the Cauchy property of [real_abs]).
   The standard library provides Qabs_triangle_reverse : Qabs x - Qabs y <= Qabs (x - y);
   the two-sided version is that lemma plus symmetry ([Qabs_opp] plus [Qabs_wd]). *)
Lemma q_abs_abs_triangle : forall a b : Q,
  QleT' (Qabs (Qabs a - Qabs b)) (Qabs (a - b)).
Proof.
  intros a b.
  apply Qle_to_QleT'.
  apply Qabs_Qle_condition.
  split.
  - (* Left side: -|a−b| <= |a|−|b| follows by negating |b|−|a| <= |a−b|. *)
    apply (Qle_trans _ (Qopp (Qabs b - Qabs a)) _).
    + apply (Qopp_le_compat (Qabs b - Qabs a) (Qabs (a - b))).
      apply (Qle_trans _ (Qabs (b - a)) _).
      * apply Qabs_triangle_reverse.
      * (* |b−a| <= |a−b|: since b−a == −(a−b), by the symmetry of [Qabs_opp]. *)
        apply QleT'_to_Qle.
        apply qeq_leT'.
        apply qeq_imp_qeqT.
        transitivity (Qabs (- (a - b))).
        -- apply Qabs_wd. ring.
        -- apply Qabs_opp.
    + apply QleT'_to_Qle. apply qeq_leT'. apply qeq_imp_qeqT. ring.
  - (* Right side: |a|−|b| <= |a−b| is given directly by the standard library. *)
    apply Qabs_triangle_reverse.
Qed.

(* Transitivity bridge for [QltT] from the main file (when needed): QltT x y -> QltT y z -> QltT x z. *)
Lemma qltT_trans : forall x y z : Q, QltT x y -> QltT y z -> QltT x z.
Proof.
  intros x y z Hxy Hyz.
  exact (Qlt_to_QltT x z
    (Qlt_trans x y z (QltT_to_Qlt x y Hxy) (QltT_to_Qlt y z Hyz))).
Qed.

(* [real_abs]: pointwise [Qabs] with the Cauchy property (via the reverse triangle inequality and the [QltT] bridge). *)
Definition real_abs (x : Real) : Real.
Proof.
  destruct x as [u Hu].
  exists (fun n => Qabs (u n)).
  intros eps Heps.
  destruct (Hu eps Heps) as [N HN].
  exists N.
  intros m n Hm Hn.
  (* Goal: QltT (Qabs (Qabs (u m) - Qabs (u n))) eps. *)
  apply Qlt_to_QltT.
  apply (Qle_lt_trans _ (Qabs (u m - u n)) _).
  - apply QleT'_to_Qle.
    apply (q_abs_abs_triangle (u m) (u n)).
  - apply QltT_to_Qlt. apply (HN m n Hm Hn).
Defined.

(* [real_metric]: |x - y|. *)
Definition real_metric (x y : Real) : Real :=
  real_abs (real_plus x (real_opp y)).

(* |-x| == |x|: pointwise [Qabs_opp] (the [real_eq] version, for every eps). *)
Lemma real_abs_opp : forall x : Real, real_eq (real_abs (real_opp x)) (real_abs x).
Proof.
  intros x. destruct x as [u Hu].
  unfold real_abs, real_opp, real_eq.
  intros eps Heps. exists 0%nat. intros n _.
  apply Qlt_to_QltT.
  apply (Qle_lt_trans _ 0 _).
- apply QleT'_to_Qle. apply qeq_leT'.
    apply qeq_imp_qeqT.
    apply (Qabs_wd (Qabs (Qopp (u n)) - Qabs (u n)) 0).
    rewrite (Qabs_opp (u n)). ring.
  - apply QltT_to_Qlt. exact Heps.
Qed.

(* Pointwise projection of [real_abs]: projT1 (real_abs x) n == Qabs (projT1 x n). *)
Lemma real_abs_proj : forall (x : Real) (n : nat),QeqT (
  projT1 (real_abs x) n ) ( Qabs (projT1 x n)).
Proof.
  intros x n. apply qeq_imp_qeqT. destruct x as [u Hu]. reflexivity.
Qed.

(* Triangle inequality (per-eps form): the Or-encoding of real_le cannot express "non-strict yet
   with vanishing slack", so the Bishop-style per-eps upper bound is used:
   for every eps > 0 there is N with A_n <= B_n + eps for all n >= N. *)
Lemma real_abs_triangle_eps : forall (x y : Real) (eps : Q),
  QltT 0 eps -> sigT (fun N : nat => forall n : nat, NatLe N n ->
    QleT' (projT1 (real_abs (real_plus x y)) n)
        (projT1 (real_abs x) n + projT1 (real_abs y) n + eps)).
Proof.
  intros x y eps Heps.
  exists 0%nat. intros n _.
  apply Qle_to_QleT'.
  rewrite (qeqT_imp_qeq _ _ (real_abs_proj (real_plus x y) n)).
  rewrite (qeqT_imp_qeq _ _ (real_abs_proj x n)).
  rewrite (qeqT_imp_qeq _ _ (real_abs_proj y n)).
  rewrite (qeqT_imp_qeq _ _ (real_plus_proj x y n)).
  destruct x as [u Hu]. destruct y as [v Hv].
  cbn [projT1].
  apply (Qle_trans _ (Qabs (u n) + Qabs (v n)) _).
  - exact (Qabs_triangle (u n) (v n)).
  - apply (Qle_trans _ (Qabs (u n) + Qabs (v n) + 0) _).
    + apply QleT'_to_Qle. apply qeq_leT'. apply qeq_imp_qeqT. ring.
    + apply (Qplus_le_compat (Qabs (u n) + Qabs (v n)) (Qabs (u n) + Qabs (v n)) 0 eps).
      * apply Qle_refl.
      * apply (Qlt_le_weak 0 eps). apply QltT_to_Qlt. exact Heps.
Qed.

(* ============ The Cauchy reciprocal: [real_inv_pos] ============ *)

(* Bound on the difference of reciprocals (the [Qle] form): for 0 < eps < a and 0 < eps < b,
   |1/a − 1/b| <= |a − b| * Qinv (eps*eps).
   Proof: |1/a−1/b| == |a−b|/(|a|*|b|) <= |a−b|/eps^2, sandwiched by expanding the denominators
   with [q_le_div_le]. *)
Lemma q_inv_diff_bound :
  forall (a b eps : Q), QltT 0 eps -> QltT eps a -> QltT eps b ->
  QleT' (Qabs (Qinv a - Qinv b))
      (Qmult (Qabs (a - b)) (Qinv (Qmult eps eps))).
Proof.
  intros a b eps Heps Ha Hb.
  assert (HepsQ : Qlt 0 eps) by (apply QltT_to_Qlt; exact Heps).
  assert (HaQ : Qlt eps a) by (apply QltT_to_Qlt; exact Ha).
  assert (HbQ : Qlt eps b) by (apply QltT_to_Qlt; exact Hb).
  apply Qle_to_QleT'.
  (* From a, b > eps > 0 both are nonzero and positive. *)
  assert (Ha0 : ~ a == 0) by (intro Heq0; destruct (q_neq_of_lt a (Qlt_to_QltT _ _ (Qlt_trans _ eps _ HepsQ HaQ)) (qeq_imp_qeqT _ _ Heq0))).
  assert (Hb0 : ~ b == 0) by (intro Heq0; destruct (q_neq_of_lt b (Qlt_to_QltT _ _ (Qlt_trans _ eps _ HepsQ HbQ)) (qeq_imp_qeqT _ _ Heq0))).
  assert (Hapos : Qlt 0 a) by (apply (Qlt_trans _ eps _); [exact HepsQ | exact HaQ]).
  assert (Hbpos : Qlt 0 b) by (apply (Qlt_trans _ eps _); [exact HepsQ | exact HbQ]).
  (* |1/a − 1/b| == |a − b| / (|a|·|b|) *)
  assert (Hmain : Qabs (Qinv a - Qinv b) ==
                  Qabs (a - b) / Qmult (Qabs a) (Qabs b)).
  { unfold Qdiv.
    transitivity (Qabs (Qmult (Qinv (Qmult a b)) (b - a))).
    - (* |1/a - 1/b| == |(b-a)/(ab)|: since 1/a - 1/b == (b-a)/(ab). *)
      apply Qabs_wd.
      field; split; assumption.
    - (* |(b−a)/(ab)| == |b−a|·|1/(ab)| == |a−b|/|ab| *)
      transitivity (Qmult (Qabs (Qinv (Qmult a b))) (Qabs (b - a))).
      + apply Qabs_Qmult.
      + transitivity (Qmult (Qabs (Qinv (Qmult a b))) (Qabs (a - b))).
        * apply Qmult_comp.
          -- apply Qeq_refl.
          -- (* Qabs (b-a) == Qabs (a-b): since b-a == -(a-b), by [Qabs_wd] plus [Qabs_opp]. *)
             apply (Qeq_trans _ (Qabs (- (a - b))) _).
             ++ apply Qabs_wd. ring.
             ++ apply Qabs_opp.
        * (* Qabs(|1/ab|)·|a−b| == |a−b|·Qinv(|ab|) == |a−b|·Qinv(|a||b|) *)
          transitivity (Qmult (Qabs (a - b)) (Qabs (Qinv (Qmult a b)))).
          -- apply Qeq_sym. apply Qmult_comm.
          -- transitivity (Qmult (Qabs (a - b)) (Qinv (Qabs (Qmult a b)))).
             ++ apply Qmult_comp.
                ** apply Qeq_refl.
                ** apply (Qabs_Qinv (Qmult a b)).
             ++ apply Qmult_comp.
                ** apply Qeq_refl.
                ** apply (Qinv_comp (Qabs (Qmult a b)) (Qmult (Qabs a) (Qabs b))).
                   apply Qabs_Qmult. }
  (* Apply [q_le_div_le] with a1 = |a−b|, b1 = |a|*|b|, c1 = |a−b| and d1 = eps*eps; this needs |a−b| * eps^2 <= |a−b| * (|a|*|b|). *)
  rewrite Hmain.
  apply QleT'_to_Qle.
  apply (q_le_div_le (Qabs (a - b)) (Qmult (Qabs a) (Qabs b))
                      (Qabs (a - b)) (Qmult eps eps)).
  - apply Qlt_to_QltT.
    apply (Qmult_lt_0_compat (Qabs a) (Qabs b)).
    + (* 0 < |a|: a > 0 forces |a| == a. *)
      apply (Qlt_le_trans _ a _).
      * exact Hapos.
      * apply QleT'_to_Qle. apply qeq_leT'. apply qeq_imp_qeqT. apply Qeq_sym. apply (Qabs_pos a). apply (Qlt_le_weak 0 a). exact Hapos.
    + apply (Qlt_le_trans _ b _).
      * exact Hbpos.
      * apply QleT'_to_Qle. apply qeq_leT'. apply qeq_imp_qeqT. apply Qeq_sym. apply (Qabs_pos b). apply (Qlt_le_weak 0 b). exact Hbpos.
  - apply Qlt_to_QltT. apply (Qmult_lt_0_compat eps eps); [exact HepsQ | exact HepsQ].
  - (* |a−b| * (eps*eps) <= |a−b| * (|a|*|b|): since |a−b| >= 0 and eps*eps <= |a|*|b|. *)
    (* First swap the factors: |a−b| * eps^2 == eps^2 * |a−b|, and likewise on the right. *)
    apply Qle_to_QleT'.
    rewrite (Qmult_comm (Qabs (a - b)) (Qmult eps eps)).
    rewrite (Qmult_comm (Qabs (a - b)) (Qmult (Qabs a) (Qabs b))).
    apply (Qmult_le_compat_r (Qmult eps eps) (Qmult (Qabs a) (Qabs b)) (Qabs (a - b))).
    + (* eps*eps <= |a|*|b|: since eps <= |a| and eps <= |b| (a, b > eps > 0). *)
      (* In two steps: eps*eps <= eps*|b| <= |a|*|b| (two applications of [Qmult_le_compat_r]). *)
      apply (Qle_trans _ (Qmult eps (Qabs b)) _).
      * (* eps*eps <= eps*|b|: multiply by eps on the right from eps <= |b| (x*z <= y*z gives eps*eps <= |b|*eps, then swap). *)
        apply (Qle_trans _ (Qmult (Qabs b) eps) _).
        -- apply (Qmult_le_compat_r eps (Qabs b) eps).
           ++ apply (Qle_trans _ b _).
              ** apply (Qlt_le_weak _ _ HbQ).
              ** apply QleT'_to_Qle. apply qeq_leT'. apply qeq_imp_qeqT. apply Qeq_sym. apply (Qabs_pos b). apply (Qlt_le_weak 0 b). exact Hbpos.
           ++ apply (Qlt_le_weak 0 eps). exact HepsQ.
        -- apply QleT'_to_Qle. apply qeq_leT'. apply qeq_imp_qeqT. apply Qmult_comm.
      * (* eps*|b| <= |a|*|b|: multiply by |b| on the right from eps <= |a|. *)
        apply (Qmult_le_compat_r eps (Qabs a) (Qabs b)).
        -- apply (Qle_trans _ a _).
           ++ apply (Qlt_le_weak _ _ HaQ).
           ++ apply QleT'_to_Qle. apply qeq_leT'. apply qeq_imp_qeqT. apply Qeq_sym. apply (Qabs_pos a). apply (Qlt_le_weak 0 a). exact Hapos.
        -- apply (Qlt_le_weak 0 (Qabs b)).
           apply (Qlt_le_trans _ b _).
           ++ exact Hbpos.
           ++ apply QleT'_to_Qle. apply qeq_leT'. apply qeq_imp_qeqT. apply Qeq_sym. apply (Qabs_pos b). apply (Qlt_le_weak 0 b). exact Hbpos.
    + apply Qabs_nonneg.
Qed.

(* [real_inv_pos]: the Cauchy reciprocal (guarded by the positive lower bound eps0; for m, n >= N0 the sequence takes Qinv (u n)). *)
Definition real_inv_pos (x : Real) (Hx : real_lt real_zero x) : Real.
Proof.
  destruct x as [u Hu].
  destruct Hx as [eps0 [Heps0 [N0 HN0]]].
  exists (fun n => if Nat.leb N0 n then Qinv (u n) else Qinv (u N0)).
  intros eps Heps.
  set (delta := Qmult eps (Qmult eps0 eps0)).
  assert (Hdlt : QltT 0 delta).
  { unfold delta. apply Qlt_to_QltT.
    apply (Qmult_lt_0_compat eps (Qmult eps0 eps0)).
    - apply QltT_to_Qlt. exact Heps.
    - apply (Qmult_lt_0_compat eps0 eps0).
      + apply QltT_to_Qlt. exact Heps0.
      + apply QltT_to_Qlt. exact Heps0. }
  destruct (Hu delta Hdlt) as [N1 HN1].
  exists (Nat.max N0 N1).
  intros m n Hm Hn.
  apply NatLe_drop in Hm. apply NatLe_drop in Hn.
  assert (Hm0 : (N0 <= m)%nat) by lia.
  assert (Hn0 : (N0 <= n)%nat) by lia.
  rewrite (leb_correct _ _ Hm0).
  rewrite (leb_correct _ _ Hn0).
  (* Goal: QltT (Qabs (Qinv (u m) - Qinv (u n))) eps. *)
  apply Qlt_to_QltT.
  (* Since u m, u n > eps0: [HN0] directly gives QltT eps0 (u m - 0), with x destructed into existT u Hu. *)
  assert (Hum : QltT eps0 (u m - 0)).
  { change (QltT eps0 (projT1 (existT (fun s : Qseq => cauchy s) u Hu) m - projT1 real_zero m)).
    apply (HN0 m). apply NatLe_lift. exact Hm0. }
  assert (Hun : QltT eps0 (u n - 0)).
  { change (QltT eps0 (projT1 (existT (fun s : Qseq => cauchy s) u Hu) n - projT1 real_zero n)).
    apply (HN0 n). apply NatLe_lift. exact Hn0. }
  apply (Qle_lt_trans _ (Qmult (Qabs (u m - u n)) (Qinv (Qmult eps0 eps0))) _).
  - apply QleT'_to_Qle.
    apply (q_inv_diff_bound (u m) (u n) eps0).
    + exact Heps0.
    + apply (qltT_eq_compat_r (u m) (u m - 0) eps0).
      * apply qeq_imp_qeqT. apply Qeq_sym. ring.
      * exact Hum.
    + apply (qltT_eq_compat_r (u n) (u n - 0) eps0).
      * apply qeq_imp_qeqT. apply Qeq_sym. ring.
      * exact Hun.
  - (* |u m − u n| * (1/eps0^2) < eps: from |u m − u n| < eps * eps0^2 ([HN1] at delta). *)
    assert (Hdiff : QltT (Qabs (u m - u n)) delta).
    { apply (HN1 m n); apply NatLe_lift; lia. }
    unfold delta in Hdiff.
    (* x * (1/eps0^2) < eps follows from x < eps * eps0^2 by multiplying with the positive Qinv (eps0*eps0). *)
    apply (Qlt_le_trans _ (Qmult (Qmult eps (Qmult eps0 eps0)) (Qinv (Qmult eps0 eps0))) _).
    { apply (Qmult_lt_compat_r (Qabs (u m - u n)) (Qmult eps (Qmult eps0 eps0))
                               (Qinv (Qmult eps0 eps0))).
      - apply Qinv_lt_0_compat.
        apply (Qmult_lt_0_compat eps0 eps0).
        + apply QltT_to_Qlt. exact Heps0.
        + apply QltT_to_Qlt. exact Heps0.
      - exact (QltT_to_Qlt _ _ Hdiff). }
    { (* eps * (eps0*eps0) * (1/(eps0*eps0)) <= eps: cancel with [Qmult_inv_r]. *)
apply QleT'_to_Qle. apply qeq_leT'. apply qeq_imp_qeqT.
      transitivity (eps * ((eps0 * eps0) * Qinv (eps0 * eps0))).
      { apply Qeq_sym.
        apply (Qmult_assoc eps (Qmult eps0 eps0) (Qinv (Qmult eps0 eps0))). }
      { transitivity (eps * 1).
        + rewrite (Qmult_inv_r (Qmult eps0 eps0)).
          * reflexivity.
          * assert (Hltm : Qlt 0 (eps0 * eps0)) by (apply (Qmult_lt_0_compat eps0 eps0); apply QltT_to_Qlt; exact Heps0).
            intro Heq0. destruct (q_neq_of_lt _ (Qlt_to_QltT _ _ Hltm) (qeq_imp_qeqT _ _ Heq0)).
        + ring. } }
Defined.

(* Correctness of [real_inv_pos]: x * (1/x) == 1 (for n >= N0, u n * (1/u n) == 1 by [field]). *)
Lemma real_inv_pos_correct :
  forall (x : Real) (Hx : real_lt real_zero x),
  real_eq (real_mult x (real_inv_pos x Hx)) real_one.
Proof.
  intros x Hx.
  destruct x as [u Hu].
  destruct Hx as [eps0 [Heps0 [N0 HN0]]].
  unfold real_mult, real_inv_pos, real_one, real_eq.
  intros eps Heps.
  exists N0.
  intros n Hn.
  (* Goal: QltT (Qabs (u n * (if N0 <= n then 1/u n else 1/u N0) - 1)) eps. *)
  (* Reduce projT1: the sequence of [real_mult] is fun n => u n * (if ...). *)
  cbn [projT1].
  destruct (Nat.leb N0 n) eqn:Eleb.
  - (* Case N0 <= n: the value 1/u n is used; u n * (1/u n) == 1 by [Qmult_inv_r], since u n ≠ 0. *)
    assert (Hun0 : ~ u n == 0).
    { assert (Hltun : Qlt 0 (u n)).
      { apply (Qlt_trans _ eps0 _); [apply QltT_to_Qlt; exact Heps0 | ].
      (* Goal: eps0 < u n; [HN0] gives eps0 < u n - 0, bridged by u n - 0 == u n. *)
      apply (Qlt_le_trans _ (u n - 0) _).
      - apply QltT_to_Qlt.
        change (QltT eps0 (projT1 (existT (fun s : Qseq => cauchy s) u Hu) n - projT1 real_zero n)).
        apply (HN0 n). apply NatLe_lift. apply Nat.leb_le. exact Eleb.
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
      intro Heq0. destruct (q_neq_of_lt (u n) (Qlt_to_QltT _ _ Hltun) (qeq_imp_qeqT _ _ Heq0)). }
    apply Qlt_to_QltT.
    apply (Qle_lt_trans _ 0 _).
    + (* |u n * (1/u n) - 1| == 0 <= 0: after [Hsub], rewrite with [Qabs_wd]. *)
      assert (Hsub : u n * / u n - 1 == 0).
      { rewrite (Qmult_inv_r (u n) Hun0). ring. }
      apply QleT'_to_Qle. apply qeq_le.
      apply qeq_imp_qeqT.
      (* Goal: Qabs (u n * (1/u n) - 1) == 0. *)
      transitivity (Qabs 0).
      * apply (Qabs_wd (u n * / u n - 1) 0). exact Hsub.
      * (* Qabs 0 == 0: by [Qabs_neg] (0 <= 0). *)
        apply (Qeq_trans _ (- 0) _).
        -- apply Qabs_neg. apply Qle_refl.
        -- ring.
    + apply QltT_to_Qlt. exact Heps.
  - (* Case not (N0 <= n), i.e. n < N0: this branch is impossible, since n >= N0 is guaranteed
      by the witness N0 — excluded. *)
    apply Nat.leb_gt in Eleb.
    apply NatLe_drop in Hn.
    exfalso. lia.
Qed.

(* Positivity of [real_inv_pos]: x > 0 implies 1/x > 0.
   Strategy: take eps := Qinv (M+1); for n >= N0 one has u n <= M < M+1, so [Qinv_lt_contravar]
   gives Qinv (M+1) < Qinv (u n), i.e. inv_n - 0 > eps. *)
Lemma real_inv_pos_pos :
  forall (x : Real) (Hx : real_lt real_zero x),
  real_lt real_zero (real_inv_pos x Hx).
Proof.
  intros x Hx.
  destruct x as [u Hu].
  destruct Hx as [eps0 [Heps0 [N0 HN0]]].
  (* The global bound M: |u k| <= M, by [real_norm_bounded]. *)
  destruct (real_norm_bounded (existT (fun s : Qseq => cauchy s) u Hu)) as [M [HMpos HM]].
  (* Take eps := Qinv (M + 1) and N := N0. *)
  unfold real_inv_pos, real_lt, real_zero.
  exists (Qinv (M + 1)).
  split.
  - (* 0 < Qinv (M+1). *)
    apply Qlt_to_QltT.
    apply Qinv_lt_0_compat.
    apply (Qlt_le_trans _ 1 _).
    + reflexivity.  (* 0 < 1 is decidable by computation *)
    + (* 1 <= M+1: indeed 1 <= 1+M == M+1. *)
      apply (Qle_trans _ (1 + M) _).
      * apply (Qle_plus_nonneg_r 1 M). apply (Qlt_le_weak 0 M). apply QltT_to_Qlt. exact HMpos.
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qplus_comm.
  - exists N0.
    intros n Hn.
    cbn [projT1].
    destruct (Nat.leb N0 n) eqn:Eleb.
    + (* Case n >= N0: inv_n == Qinv (u n); it remains to show Qinv (M+1) < Qinv (u n). *)
      apply Qlt_to_QltT.
      (* Premises: 0 < u n, 0 < M+1 and u n < M+1. *)
      assert (Hu0 : Qlt 0 (u n)).
      { apply (Qlt_le_trans _ (u n - 0) _).
        - apply (Qlt_trans _ eps0 _).
          + apply QltT_to_Qlt. exact Heps0.
          + apply QltT_to_Qlt. apply (HN0 n). apply NatLe_lift. apply Nat.leb_le. exact Eleb.
        - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
      assert (HM1 : Qlt 0 (M + 1)).
      { apply (Qlt_le_trans _ 1 _); [reflexivity | ].
        apply (Qle_trans _ (1 + M) _).
        - apply (Qle_plus_nonneg_r 1 M). apply (Qlt_le_weak 0 M). apply QltT_to_Qlt. exact HMpos.
        - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qplus_comm. }
      assert (Hult : Qlt (u n) (M + 1)).
      { apply (Qle_lt_trans _ (Qabs (u n)) _).
        - apply Qle_Qabs.
        - apply (Qle_lt_trans _ M _).
          + apply QleT'_to_Qle. apply (HM n).
          + (* M < M+1: write M == M+0, then M+0 < M+1 ([Qplus_lt_r] from 0 < 1), bridging M == M+0. *)
            apply (Qle_lt_trans _ (M + 0) _).
            * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.  (* M <= M+0: since M == M+0 *)
            * apply (proj2 (Qplus_lt_r 0 1 M)). reflexivity.  (* M+0 < M+1 follows from 0 < 1 *) }
      (* Goal: QltT (Qinv (M+1)) (Qinv (u n) - 0); the right side == Qinv (u n). *)
      apply (Qlt_le_trans _ (Qinv (u n)) _).
      { exact (proj1 (Qinv_lt_contravar (u n) (M + 1) Hu0 HM1) Hult). }
      { (* Qinv (u n) <= Qinv (u n) - 0: since Qinv(u n) - 0 == Qinv(u n), applied backwards. *)
        apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
    + (* Case not (N0 <= n): contradiction. *)
      apply Nat.leb_gt in Eleb.
      apply NatLe_drop in Hn.
      exfalso. lia.
Qed.

Print Assumptions Q2_nonneg.
Print Assumptions Qhalf_nonneg.
