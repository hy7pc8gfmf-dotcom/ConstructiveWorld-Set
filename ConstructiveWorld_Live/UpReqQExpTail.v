(* ConstructiveWorld-Set — explicit Cauchy moduli for rational exponential tail sums. *)

(** * UpReqQExpTail: explicit Cauchy moduli for the rational exponential tail sums.

    Mission.  The tail-sum family [qtail_sum] with nonnegativity
      [qtail_sum_nonneg], monotonicity [qtail_sum_mono], the term-decay
      bound [qtail_term_decay], the explicit ratio machine
      ([qtail_two_b_le]/[qtail_ratio_step]/[qtail_ratio_chain]), the
      geometric tail bound [qtail_sum_geo], and the constructive Cauchy
      modulus [qtail_cauchy_modulus] with its ordered-argument form
      [qtail_cauchy_modulus_ord].

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs], [QArith.Qround],
      [Lists.List], [Bool.Bool], [Arith.Arith], [Arith.Factorial],
      [Setoid], [Morphisms], [Lia], [QArith.Qminmax].  Requires
      [S01_BaseRing], [S02_CauchyComplete], [S03_QExp] of this development.

    References.  This development, UpReqQExpTail.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion: auxiliary [Qle]
      conclusions moved to [QleT'], [Qlt] conclusions to [QltT], [==]
      identities to [QeqT], nat order to [NatLe], negations to the
      Set-layer [Not]; the [QleT]-elimination bridge [qtail_QleT_to_Qle]
      is kept as a downward-directed interface lemma).

    Constructivity.  All named statements are carried by [Set] (decidable
      Q-carriers [QltT]/[QleT']/[QeqT], [Id], [NatLe], [Not], [sigT]);
      statements extract with [Obj.magic] = 0; [coqchk] reports
      [Axioms: <none>].

    Build.  [coqc -native-compiler no -q -Q . "" UpReqQExpTail.v]
      compiles cleanly (exit 0); the first eight bytes of the artifact
      are [436f7121 00015ff4]. *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               Lists.List Bool.Bool Arith.Arith Arith.Factorial.
Import ListNotations.
From Stdlib Require Import Setoid Morphisms Lia QArith.Qminmax.

(* ================= Section 1. nat-order engine ================= *)

Lemma qtail_two_pow_ge : forall t : nat, NatLe (Datatypes.S t) (2 ^ t).
Proof.
  intro t. apply NatLe_lift.
  induction t as [| t IH]; simpl; lia.
Qed.

(* Factorial overtakes the power of two (nat induction; 4! = 24 >= 16 = 2^4 from k = 4 on). *)
Lemma qtail_fact_ge_pow : forall k : nat, (4 <= k)%nat -> NatLe (2 ^ k) (fact k).
Proof.
  induction k as [| k IH]; intro Hk.
  - apply NatLe_lift. lia.
  - apply NatLe_lift.
    assert (H1 : (2 ^ Datatypes.S k = 2 * 2 ^ k)%nat) by reflexivity.
    assert (H2 : (fact (Datatypes.S k)
                  = Datatypes.S k * fact k)%nat) by reflexivity.
    rewrite H1, H2.
    destruct (Nat.eq_dec k 3%nat) as [Hk3 | Hkne].
    + subst k. simpl. lia.
    + assert (Hk4 : (4 <= k)%nat) by lia.
      specialize (IH Hk4).
      apply Nat.mul_le_mono.
      * lia.
      * exact (NatLe_drop _ _ IH).
Qed.

(* ================= Section 2. Q-side engine lemmas ================= *)

Lemma qtail_Qlt01 : QltT 0 1.
Proof.
  unfold QltT. compute. apply id_refl.
Qed.

Lemma qtail_neq0 : forall x : Q, Qlt 0 x -> Not (QeqT x 0).
Proof.
  intros x H Hz.
  exact (match q_neq_of_lt x (Qlt_to_QltT 0 x H) Hz with end).
Qed.

Lemma qtail_neq0_mul : forall v s : Q, ~ (v == 0) -> ~ (s == 0) -> Not (QeqT (v * s) 0).
Proof.
  intros v s Hv Hs Hz.
  exact (False_rect _ (Hs (Qmult_integral_l v s Hv (qeqT_imp_qeq (v * s) 0 Hz)))).
Qed.

(* Product splitting of division: (u*r)/(v*s) == (u/v)*(r/s). *)
Lemma qtail_div_split : forall u v r s : Q,
  ~ (v == 0) -> ~ (s == 0) -> QeqT ((u * r) / (v * s)) ((u / v) * (r / s)).
Proof.
  intros u v r s Hv Hs.
  assert (Hvs : ~ (v * s == 0))
    by (intro Hz; destruct (qtail_neq0_mul v s Hv Hs (qeq_imp_qeqT (v * s) 0 Hz))).
  apply qeq_imp_qeqT.
  field. repeat split; assumption.
Qed.

Lemma qtail_QleT_to_Qle : forall x y : Q, QleT x y -> Qle x y.
Proof.
  intros x y H. destruct H as [H | H].
  - apply (Qlt_le_weak x y). apply (QltT_to_Qlt x y). exact H.
  - apply QleT'_to_Qle. apply qeq_le. destruct H. exact (qeq_imp_qeqT x x (Qeq_refl x)).
Qed.

Lemma qtail_le_plus_r : forall x y : Q, Qle 0 y -> QleT' x (x + y).
Proof.
  intros x y Hy. apply Qle_to_QleT'.
  apply (Qle_trans x (x + 0) (x + y)).
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
  - apply (Qplus_le_compat x x 0 y).
    + apply Qle_refl.
    + exact Hy.
Qed.

(* For x >= 0 one has x <= (Z.of_nat (Z.to_nat (Qnum x)))#1: an explicit computable upper bound. *)
Lemma qtail_pos_upper : forall x : Q, Qle 0 x -> QleT' x (Z.of_nat (Z.to_nat (Qnum x)) # 1).
Proof.
  intros x Hx. apply Qle_to_QleT'.
  destruct x as [n d]. simpl.
  assert (Hn : (0 <= n)%Z).
  { unfold Qle in Hx. simpl in Hx. lia. }
  replace (Z.of_nat (Z.to_nat n)) with n by lia.
  unfold Qle.
  apply Z.mul_le_mono_nonneg_l.
  - exact Hn.
  - assert (H1 : (1 <= Z.pos d)%Z) by (induction d as [p IHp | p IHp | ]; simpl; lia).
    exact H1.
Qed.

(* Positivity of the denominator in the explicit Q form of 2^t (reused by field side goals). *)
Lemma qtail_pow2_denom_pos : forall t : nat, QltT 0 (Z.of_nat (2 ^ t) # 1).
Proof.
  intro t. apply Qlt_to_QltT.
  assert (Hp : (0 < 2 ^ t)%nat)
    by (apply (proj1 (Nat.neq_0_lt_0 (2 ^ t))); apply Nat.pow_nonzero; lia).
  unfold Qlt. simpl. lia.
Qed.

(* (1/2)^t <= 1/(t+1): derived explicitly from 2^t >= t+1. *)
Lemma qtail_half_pow_le_invT : forall t : nat,
  QleT' (q_pow (1 / 2) t) (1 / (Z.of_nat (Datatypes.S t) # 1)).
Proof.
  intro t. apply Qle_to_QleT'.
  assert (H2pos : (0 < 2 ^ t)%nat).
  { apply (proj1 (Nat.neq_0_lt_0 (2 ^ t))).
    apply Nat.pow_nonzero. lia. }
  assert (E : forall t0 : nat, q_pow (1 / 2) t0 == 1 / (Z.of_nat (2 ^ t0) # 1)).
  { intro t0. induction t0 as [| t0 IH].
    - reflexivity.
    - rewrite (qeqT_imp_qeq _ _ (q_pow_succ (1 / 2) t0)), IH.
      assert (Hz2 : (2 ^ Datatypes.S t0 = 2 * 2 ^ t0)%nat) by reflexivity.
      rewrite Hz2.
      assert (Hb : (0 < Z.of_nat (2 ^ t0))%Z).
      { assert (Hp : (0 < 2 ^ t0)%nat)
          by (apply (proj1 (Nat.neq_0_lt_0 (2 ^ t0))); apply Nat.pow_nonzero; lia).
        lia. }
      assert (HZ : ((Z.of_nat (2 * 2 ^ t0)) # 1
                    == (((Z.of_nat (2 ^ t0)) # 1) + ((Z.of_nat (2 ^ t0)) # 1)))%Q)
        by (unfold Qeq; simpl; lia).
      rewrite HZ.
      field.
      repeat split;
        first [ assumption
              | intro Hz;
                assert (Hp : Qlt 0 (Z.of_nat (2 ^ t0) # 1)) by (unfold Qlt; simpl; lia);
                destruct (qtail_neq0 _ Hp (qeq_imp_qeqT _ _ Hz))
              | intro Hz;
                assert (Hp : Qlt 0 ((Z.of_nat (2 ^ t0) # 1) + (Z.of_nat (2 ^ t0) # 1)))
                  by (unfold Qlt; simpl; lia);
                destruct (qtail_neq0 _ Hp (qeq_imp_qeqT _ _ Hz))
              | intro Hz; assert (Hp : Qlt 0 1) by (unfold Qlt; simpl; lia);
                destruct (qtail_neq0 _ Hp (qeq_imp_qeqT _ _ Hz)) ]. }
  rewrite (E t).
  apply QleT'_to_Qle.
  apply (q_le_div_le 1 (Z.of_nat (2 ^ t) # 1) 1 (Z.of_nat (Datatypes.S t) # 1)).
  - apply (Qlt_of_nat_lt 0 (2 ^ t)). exact H2pos.
  - apply (Qlt_of_nat_lt 0 (Datatypes.S t)). lia.
  - apply Qle_to_QleT'.
    setoid_replace (1 * (Z.of_nat (Datatypes.S t) # 1))
      with (Z.of_nat (Datatypes.S t) # 1) by ring.
    setoid_replace (1 * (Z.of_nat (2 ^ t) # 1))
      with (Z.of_nat (2 ^ t) # 1) by ring.
    apply QleT'_to_Qle.
    apply (Qle_of_nat (Datatypes.S t) (2 ^ t)).
    exact (NatLe_drop _ _ (qtail_two_pow_ge t)).
Qed.

(* Strict cross-multiplication: a*d < c*b implies a/b < c/d for positive denominators. *)
Lemma qtail_div_lt : forall a b c d : Q,
  Qlt 0 b -> Qlt 0 d -> Qlt (a * d) (c * b) -> QltT (a / b) (c / d).
Proof.
  intros a b c d Hb Hd Hcore. apply Qlt_to_QltT.
  assert (Hnb : ~ (b == 0)).
  { assert (Hp : Qlt 0 b) by exact Hb.
    intro Hz. destruct (qtail_neq0 b Hp (qeq_imp_qeqT b 0 Hz)). }
  assert (Hnd : ~ (d == 0)).
  { assert (Hp : Qlt 0 d) by exact Hd.
    intro Hz. destruct (qtail_neq0 d Hp (qeq_imp_qeqT d 0 Hz)). }
  assert (Hle : Qle (a / b) (c / d)).
  { apply QleT'_to_Qle.
    apply (q_le_div_le a b c d).
    - exact (Qlt_to_QltT 0 b Hb).
    - exact (Qlt_to_QltT 0 d Hd).
    - apply Qle_to_QleT'. apply (Qlt_le_weak _ _ Hcore). }
  destruct (Qle_lt_or_eq _ _ Hle) as [Hlt | Heq].
  - exact Hlt.
  - exfalso.
    assert (Hs : (a / b) * (b * d) == (c / d) * (b * d)) by (rewrite Heq; reflexivity).
    assert (E1 : (a / b) * (b * d) == a * d) by (field; repeat split; assumption).
    assert (E2 : (c / d) * (b * d) == c * b) by (field; repeat split; assumption).
    rewrite E1 in Hs. rewrite E2 in Hs.
    exact (Qlt_not_eq _ _ Hcore Hs).
Qed.

(* For 0 < u and 0 < v one has 0 < u/v. *)
Lemma qtail_div_pos : forall u v : Q, Qlt 0 u -> Qlt 0 v -> QltT 0 (u / v).
Proof.
  intros u v Hu Hv.
  assert (Hcore : Qlt (0 * v) (u * 1)).
  { apply (Qle_lt_trans (0 * v) (0 * 1) (u * 1)).
    - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
    - apply (Qmult_lt_compat_r 0 u 1).
      + apply (QltT_to_Qlt 0 1). apply qtail_Qlt01.
      + exact Hu. }
  apply (qtail_div_lt 0 1 u v).
  - apply (QltT_to_Qlt 0 1). apply qtail_Qlt01.
  - exact Hv.
  - exact Hcore.
Qed.

(* The platform lacks left variants of the multiplication order lemmas; these are rebuilt from the right variants closed by Qeq rings. *)
Lemma qtail_mult_le_compat_l : forall x y z : Q,
  Qle x y -> Qle 0 z -> QleT' (z * x) (z * y).
Proof.
  intros x y z H1 H2. apply Qle_to_QleT'.
  apply (Qle_trans _ (x * z)).
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
  - apply (Qle_trans _ (y * z)).
    + apply (Qmult_le_compat_r x y z).
      * exact H1.
      * exact H2.
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
Qed.

Lemma qtail_mult_lt_compat_l : forall z x y : Q,
  Qlt 0 z -> Qlt x y -> QltT (z * x) (z * y).
Proof.
  intros z x y Hz Hxy. apply Qlt_to_QltT.
  apply (Qle_lt_trans _ (x * z)).
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
  - apply (Qlt_le_trans (x * z) (y * z) (z * y)).
    + pose proof (Qmult_lt_compat_r x y z Hz Hxy) as Hr.
      exact Hr.
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
Qed.

(* ================= Section 3. Tail sums: definition, nonnegativity, monotonicity ================= *)

(* qtail_sum b m n = sum of b^k/k! for k from m to n-1; the n < m guard prevents nat subtraction truncation (the empty sum is 0). *)
Fixpoint qtail_sum (b : Q) (m n : nat) : Q :=
  match n with
  | 0%nat => 0
  | Datatypes.S n' => (if Nat.leb m n' then q_pow b n' / q_fact n' else 0)
                      + qtail_sum b m n'
  end.

Lemma qtail_sum_le_m : forall b m n, (n <= m)%nat -> QeqT (qtail_sum b m n) 0.
Proof.
  intros b m n Hn. revert Hn.
  induction n as [| n IH]; intro Hn.
  - apply qeq_imp_qeqT. reflexivity.
  - apply qeq_imp_qeqT.
    change (qtail_sum b m (Datatypes.S n))
      with ((if Nat.leb m n then q_pow b n / q_fact n else 0) + qtail_sum b m n).
    destruct (Nat.leb m n) eqn:E.
    + apply Nat.leb_le in E. exfalso. lia.
    + assert (IH' : qtail_sum b m n == 0)
        by (apply (qeqT_imp_qeq _ _); apply IH; lia).
      rewrite IH'. reflexivity.
Qed.

Lemma qtail_sum_add : forall b m p n, (m <= p)%nat -> (p <= n)%nat ->
  QeqT (qtail_sum b m n) (qtail_sum b m p + qtail_sum b p n).
Proof.
  intros b m p n Hmp Hpn. revert Hpn.
  induction n as [| n IH]; intro Hpn.
  - apply qeq_imp_qeqT.
    assert (Hp : p = 0%nat) by lia. subst p.
    assert (Hz : qtail_sum b 0 0 == 0)
      by (apply (qeqT_imp_qeq _ _); apply qtail_sum_le_m; lia).
    rewrite Hz.
    ring.
  - apply qeq_imp_qeqT.
    destruct (Nat.eq_dec p (Datatypes.S n)) as [HpSn | Hplt].
    + subst p.
      assert (Hz : qtail_sum b (Datatypes.S n) (Datatypes.S n) == 0)
        by (apply (qeqT_imp_qeq _ _); apply qtail_sum_le_m; lia).
      rewrite Hz.
      ring.
    + assert (Hpn' : (p <= n)%nat) by lia.
      change (qtail_sum b m (Datatypes.S n))
        with ((if Nat.leb m n then q_pow b n / q_fact n else 0) + qtail_sum b m n).
      change (qtail_sum b p (Datatypes.S n))
        with ((if Nat.leb p n then q_pow b n / q_fact n else 0) + qtail_sum b p n).
      assert (IH' : qtail_sum b m n == qtail_sum b m p + qtail_sum b p n)
        by (apply (qeqT_imp_qeq _ _); apply IH; exact Hpn').
      rewrite IH'.
      destruct (Nat.leb m n) eqn:Em; destruct (Nat.leb p n) eqn:Ep.
      * ring.
      * apply Nat.leb_gt in Ep. exfalso. lia.
      * apply Nat.leb_gt in Em. exfalso. lia.
      * ring.
Qed.

Lemma qtail_geo_nonneg : forall n : nat, QleT' 0 (geo_sum n).
Proof.
  intro n. apply Qle_to_QleT'.
  induction n as [| n IH].
  - apply Qle_refl.
  - change (geo_sum (Datatypes.S n)) with (geo_sum n + q_pow (1 / 2) n).
    apply (Qle_trans _ (q_pow (1 / 2) n) _).
    + apply QleT'_to_Qle. apply q_pow_nonneg. apply Qhalf_nonneg.
    + apply (Qle_trans (q_pow (1 / 2) n) (0 + q_pow (1 / 2) n)
                       (geo_sum n + q_pow (1 / 2) n)).
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
      * apply (Qplus_le_compat 0 (geo_sum n) (q_pow (1 / 2) n) (q_pow (1 / 2) n)).
        -- exact IH.
        -- apply Qle_refl.
Qed.

Lemma qtail_sum_nonneg_aux : forall b m n, Qle 0 b -> QleT' 0 (qtail_sum b m n).
Proof.
  intros b m n Hb. apply Qle_to_QleT'.
  induction n as [| n IH].
  - apply Qle_refl.
  - change (qtail_sum b m (Datatypes.S n))
      with ((if Nat.leb m n then q_pow b n / q_fact n else 0) + qtail_sum b m n).
    destruct (Nat.leb m n) eqn:E.
    + apply Nat.leb_le in E.
      apply (Qle_trans _ (q_pow b n / q_fact n) _).
      * apply QleT'_to_Qle. apply q_pow_fact_nonneg. exact (Qle_to_QleT' 0 b Hb).
      * apply QleT'_to_Qle. apply (qtail_le_plus_r _ (qtail_sum b m n)). apply IH.
    + setoid_replace (0 + qtail_sum b m n) with (qtail_sum b m n) by ring.
      apply IH.
Qed.

(* The tail sum grows with its upper index (monotonicity). *)
Lemma qtail_sum_mono_aux : forall b m n1 n2,
  Qle 0 b -> (m <= n1)%nat -> (n1 <= n2)%nat -> QleT' (qtail_sum b m n1) (qtail_sum b m n2).
Proof.
  intros b m n1 n2 Hb H1 H2. apply Qle_to_QleT'. revert H2.
  induction n2 as [| n2 IH]; intro H2.
  - assert (Hn1 : n1 = 0%nat) by lia. subst n1. apply Qle_refl.
  - destruct (Nat.eq_dec n1 (Datatypes.S n2)) as [He | Hd].
    + rewrite He. apply Qle_refl.
    + assert (H12 : (n1 <= n2)%nat) by lia.
      apply (Qle_trans _ (qtail_sum b m n2) _).
      * apply IH; assumption.
      * change (qtail_sum b m (Datatypes.S n2))
          with ((if Nat.leb m n2 then q_pow b n2 / q_fact n2 else 0) + qtail_sum b m n2).
        destruct (Nat.leb m n2) eqn:E.
        -- apply Nat.leb_le in E.
           apply (Qle_trans (qtail_sum b m n2) (0 + qtail_sum b m n2)
                            (q_pow b n2 / q_fact n2 + qtail_sum b m n2)).
           ++ apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
           ++ apply (Qplus_le_compat 0 (q_pow b n2 / q_fact n2)
                          (qtail_sum b m n2) (qtail_sum b m n2)).
              ** apply QleT'_to_Qle. apply q_pow_fact_nonneg. exact (Qle_to_QleT' 0 b Hb).
              ** apply Qle_refl.
        -- apply Nat.leb_gt in E. exfalso. lia.
Qed.

(* Exit statements of this section, in Set-layer QleT' form. *)
Lemma qtail_sum_nonneg : forall b m n, QleT' 0 b -> QleT' 0 (qtail_sum b m n).
Proof.
  intros b m n Hb.
  apply qtail_sum_nonneg_aux. apply (QleT'_to_Qle 0 b). exact Hb.
Qed.

Lemma qtail_sum_mono : forall b m n1 n2,
  QleT' 0 b -> (m <= n1)%nat -> (n1 <= n2)%nat ->
  QleT' (qtail_sum b m n1) (qtail_sum b m n2).
Proof.
  intros b m n1 n2 Hb H1 H2.
  apply qtail_sum_mono_aux.
  - apply (QleT'_to_Qle 0 b). exact Hb.
  - exact H1.
  - exact H2.
Qed.

(* ================= Section 4. Tail term decay control ================= *)

(* b^k/k! <= (b^4/4!) * (b/2)^(k-4) for k >= 4, valid for any b >= 0; the case split is handled by the main statement. *)
Lemma qtail_term_decay_aux : forall (b : Q) (j : nat), Qle 0 b ->
  QleT' (q_pow b (4 + j) / q_fact (4 + j)) ((q_pow b 4 / q_fact 4) * q_pow (b / 2) j).
Proof.
  intros b j Hb. apply Qle_to_QleT'.
  induction j as [| j IH].
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. simpl. ring.
  - replace (4 + Datatypes.S j)%nat with (Datatypes.S (4 + j))%nat by lia.
    rewrite (qeqT_imp_qeq _ _ (q_pow_succ b (4 + j))), (qeqT_imp_qeq _ _ (q_fact_succ (4 + j))).
    assert (Hc0 : ~ ((Z.of_nat (Datatypes.S (4 + j)) # 1) == 0)).
    { assert (Hp : Qlt 0 (Z.of_nat (Datatypes.S (4 + j)) # 1))
        by (apply QltT_to_Qlt; apply (Qlt_of_nat_lt 0 (Datatypes.S (4 + j))); lia).
      intro Hz. destruct (qtail_neq0 _ Hp (qeq_imp_qeqT _ _ Hz)). }
    assert (Hfc0 : ~ (q_fact (4 + j) == 0)).
    { assert (Hp : Qlt 0 (q_fact (4 + j))) by (apply QltT_to_Qlt; apply q_fact_pos).
      intro Hz. destruct (qtail_neq0 _ Hp (qeq_imp_qeqT _ _ Hz)). }
    assert (HCj : Qle 0 ((q_pow b 4 / q_fact 4) * q_pow (b / 2) j)).
    { apply Qmult_le_0_compat.
      - apply QleT'_to_Qle. apply q_pow_fact_nonneg. exact (Qle_to_QleT' 0 b Hb).
      - apply QleT'_to_Qle. apply q_pow_nonneg.
        apply Qle_to_QleT'.
        apply (Qle_trans 0 (b * (1 / 2)) (b / 2)).
        + apply (Qmult_le_0_compat).
          * exact Hb.
          * apply QleT'_to_Qle. apply Qhalf_nonneg.
        + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. reflexivity. }
    assert (Hbc0 : Qle 0 (b / (Z.of_nat (Datatypes.S (4 + j)) # 1))).
    { apply QleT'_to_Qle.
      apply (q_le_div_le 0 1 b (Z.of_nat (Datatypes.S (4 + j)) # 1)).
      - apply qtail_Qlt01.
      - apply (Qlt_of_nat_lt 0 (Datatypes.S (4 + j))). lia.
      - apply Qle_to_QleT'.
        apply (Qle_trans (0 * (Z.of_nat (Datatypes.S (4 + j)) # 1)) 0 (b * 1)).
        + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
        + apply (Qle_trans 0 b (b * 1)).
          * exact Hb.
          * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
    apply (Qle_trans _
      ((q_pow b (4 + j) / q_fact (4 + j)) * (b / (Z.of_nat (Datatypes.S (4 + j)) # 1))) _).
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
      rewrite (Qmult_comm (q_pow b (4 + j) / q_fact (4 + j))
                          (b / (Z.of_nat (Datatypes.S (4 + j)) # 1))).
      apply (qeqT_imp_qeq _ _).
      apply (qtail_div_split b (Z.of_nat (Datatypes.S (4 + j)) # 1)
                              (q_pow b (4 + j)) (q_fact (4 + j))).
      * exact Hc0.
      * exact Hfc0.
    + apply (Qle_trans _
        ((q_pow b 4 / q_fact 4) * q_pow (b / 2) j
           * (b / (Z.of_nat (Datatypes.S (4 + j)) # 1))) _).
      * apply (Qmult_le_compat_r _ _ (b / (Z.of_nat (Datatypes.S (4 + j)) # 1))).
        -- exact IH.
        -- exact Hbc0.
      * apply (Qle_trans _
          ((q_pow b 4 / q_fact 4) * q_pow (b / 2) j * (b / 2)%Q) _).
        -- apply QleT'_to_Qle.
           apply (qtail_mult_le_compat_l
                    (b / (Z.of_nat (Datatypes.S (4 + j)) # 1))
                    (b / 2)%Q ((q_pow b 4 / q_fact 4) * q_pow (b / 2) j)).
           ++ apply QleT'_to_Qle.
              apply (q_le_div_le b (Z.of_nat (Datatypes.S (4 + j)) # 1) b 2%Q).
              ** apply (Qlt_of_nat_lt 0 (Datatypes.S (4 + j))). lia.
              ** apply Q2_pos.
              ** apply Qle_to_QleT'.
                 apply (Qle_trans _ (2 * b)%Q).
                 --- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
                 --- apply (Qle_trans _
                              ((Z.of_nat (Datatypes.S (4 + j)) # 1) * b)).
                     +++ apply (Qmult_le_compat_r 2
                                  (Z.of_nat (Datatypes.S (4 + j)) # 1) b).
                         *** apply QleT'_to_Qle.
                             apply (Qle_of_nat 2 (Datatypes.S (4 + j))). lia.
                         *** exact Hb.
                     +++ apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
           ++ exact HCj.
        -- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
           rewrite (qeqT_imp_qeq _ _ (q_pow_succ (b / 2) j)).
           ring.
Qed.

Lemma qtail_term_decay : forall (b : Q) (k : nat), QleT' 0 b -> (4 <= k)%nat ->
  QleT' (q_pow b k / q_fact k) ((q_pow b 4 / q_fact 4) * q_pow (b / 2) (k - 4)).
Proof.
  intros b k Hb Hk.
  remember (k - 4)%nat as j eqn:Ej.
  replace k with (4 + j)%nat by lia.
  apply qtail_term_decay_aux. apply (QleT'_to_Qle 0 b). exact Hb.
Qed.

(* ================= Section 5. Explicit ratio machine, geometric tail, constructive Cauchy modulus ================= *)

(* Explicit bound: 2b <= (2 * Z.to_nat (Qnum b) + 1)#1. *)
Lemma qtail_two_b_le : forall b : Q, Qle 0 b ->
  QleT' ((1 + 1)%Q * b) (Z.of_nat (2 * Z.to_nat (Qnum b) + 1) # 1).
Proof.
  intros b Hb. apply Qle_to_QleT'.
  pose proof (qtail_pos_upper b Hb) as Hp.
  apply (Qle_trans _ ((Z.of_nat (Z.to_nat (Qnum b)) # 1) * (1 + 1)%Q) _).
  - apply (Qle_trans ((1 + 1)%Q * b)
                     ((1 + 1)%Q * (Z.of_nat (Z.to_nat (Qnum b)) # 1))
                     ((Z.of_nat (Z.to_nat (Qnum b)) # 1) * (1 + 1)%Q)).
    + apply QleT'_to_Qle.
      apply (qtail_mult_le_compat_l b (Z.of_nat (Z.to_nat (Qnum b)) # 1) (1 + 1)%Q).
      * exact (QleT'_to_Qle _ _ Hp).
      * apply QleT'_to_Qle. apply Q2_nonneg.
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
  - apply (Qle_trans _ (Z.of_nat (2 * Z.to_nat (Qnum b)) # 1) _).
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
      replace (2 * Z.to_nat (Qnum b))%nat
        with (Z.to_nat (Qnum b) + Z.to_nat (Qnum b))%nat by lia.
      unfold Qeq. simpl. lia.
    + apply QleT'_to_Qle.
      apply (Qle_of_nat (2 * Z.to_nat (Qnum b)) (2 * Z.to_nat (Qnum b) + 1)). lia.
Qed.

(* Single ratio step: for k >= K and 2b <= K+1, term_(k+1) <= term_k * (1/2). *)
Lemma qtail_ratio_step : forall (b : Q) (K k : nat),
  Qle 0 b -> Qle ((1 + 1)%Q * b) (Z.of_nat (Datatypes.S K) # 1) -> (K <= k)%nat ->
  QleT' (q_pow b (Datatypes.S k) / q_fact (Datatypes.S k))
        ((q_pow b k / q_fact k) * (1 / 2)%Q).
Proof.
  intros b K k Hb H2b Hk. apply Qle_to_QleT'.
  assert (Hc0 : ~ ((Z.of_nat (Datatypes.S k) # 1) == 0)).
  { assert (Hp : Qlt 0 (Z.of_nat (Datatypes.S k) # 1))
      by (apply QltT_to_Qlt; apply (Qlt_of_nat_lt 0 (Datatypes.S k)); lia).
    intro Hz. destruct (qtail_neq0 _ Hp (qeq_imp_qeqT _ _ Hz)). }
  assert (Hf0 : ~ (q_fact k == 0)).
  { assert (Hp : Qlt 0 (q_fact k)) by (apply QltT_to_Qlt; apply q_fact_pos).
    intro Hz. destruct (qtail_neq0 _ Hp (qeq_imp_qeqT _ _ Hz)). }
  assert (Hbc0 : Qle 0 (b / (Z.of_nat (Datatypes.S k) # 1))).
  { apply QleT'_to_Qle.
      apply (q_le_div_le 0 1 b (Z.of_nat (Datatypes.S k) # 1)).
    - apply qtail_Qlt01.
    - apply (Qlt_of_nat_lt 0 (Datatypes.S k)). lia.
    - apply Qle_to_QleT'.
      apply (Qle_trans (0 * (Z.of_nat (Datatypes.S k) # 1)) 0 (b * 1)).
      + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
      + apply (Qle_trans 0 b (b * 1)).
        * exact Hb.
        * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
  apply (Qle_trans _ ((q_pow b k / q_fact k) * (b / (Z.of_nat (Datatypes.S k) # 1))) _).
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
    rewrite (qeqT_imp_qeq _ _ (q_pow_succ b k)), (qeqT_imp_qeq _ _ (q_fact_succ k)).
    rewrite (Qmult_comm (q_pow b k / q_fact k) (b / (Z.of_nat (Datatypes.S k) # 1))).
    apply (qeqT_imp_qeq _ _).
    apply (qtail_div_split b (Z.of_nat (Datatypes.S k) # 1) (q_pow b k) (q_fact k)).
    + exact Hc0.
    + exact Hf0.
  - apply QleT'_to_Qle.
    apply (qtail_mult_le_compat_l (b / (Z.of_nat (Datatypes.S k) # 1))
             (1 / 2)%Q (q_pow b k / q_fact k)).
    + apply QleT'_to_Qle.
      apply (q_le_div_le b (Z.of_nat (Datatypes.S k) # 1) 1 2%Q).
      * apply (Qlt_of_nat_lt 0 (Datatypes.S k)). lia.
      * apply Q2_pos.
      * apply Qle_to_QleT'.
        apply (Qle_trans _ ((1 + 1)%Q * b) _).
        -- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
        -- apply (Qle_trans _ (Z.of_nat (Datatypes.S K) # 1) _).
           ++ exact H2b.
           ++ apply QleT'_to_Qle.
              apply (Qle_of_nat (Datatypes.S K) (Datatypes.S k)). lia.
    + apply QleT'_to_Qle. apply q_pow_fact_nonneg. exact (Qle_to_QleT' 0 b Hb).
Qed.

(* Chained ratios: for k >= K, term_k <= term_K * (1/2)^(k-K). *)
Lemma qtail_ratio_chain : forall (b : Q) (K k : nat),
  Qle 0 b -> Qle ((1 + 1)%Q * b) (Z.of_nat (Datatypes.S K) # 1) -> (K <= k)%nat ->
  QleT' (q_pow b k / q_fact k) ((q_pow b K / q_fact K) * q_pow (1 / 2) (k - K)).
Proof.
  intros b K k Hb H2b Hk. apply Qle_to_QleT'.
  revert Hk. revert k.
  induction k as [| k IH]; intro Hk.
  - assert (HK : K = 0%nat) by lia. subst K.
    apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. simpl. ring.
  - destruct (Nat.eq_dec (Datatypes.S k) K) as [He | Hne].
    + rewrite He.
      replace (K - K)%nat with 0%nat by lia.
      apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. simpl. ring.
    + assert (Hk' : (K <= k)%nat) by lia.
      replace (Datatypes.S k - K)%nat with (Datatypes.S (k - K))%nat by lia.
      apply (Qle_trans _ ((q_pow b k / q_fact k) * (1 / 2)%Q) _).
      * apply QleT'_to_Qle. apply (qtail_ratio_step b K k).
        -- exact Hb.
        -- exact H2b.
        -- lia.
      * apply (Qle_trans _
                 ((q_pow b K / q_fact K) * q_pow (1 / 2) (k - K) * (1 / 2)%Q)).
        -- apply (Qmult_le_compat_r (q_pow b k / q_fact k)
                     ((q_pow b K / q_fact K) * q_pow (1 / 2) (k - K)) (1 / 2)%Q).
           ++ apply IH. exact Hk'.
           ++ apply QleT'_to_Qle. apply Qhalf_nonneg.
        -- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
           rewrite (qeqT_imp_qeq _ _ (q_pow_succ (1 / 2) (k - K))).
           ring.
Qed.

(* Geometric sum: the tail from K+t to M-1 is bounded by term_K * (1/2)^t * geo_sum(M-(K+t)). *)
Lemma qtail_sum_geo : forall (b : Q) (K t M : nat),
  Qle 0 b -> Qle ((1 + 1)%Q * b) (Z.of_nat (Datatypes.S K) # 1) ->
  ((K + t) <= M)%nat ->
  QleT' (qtail_sum b (K + t) M)
        ((q_pow b K / q_fact K) * q_pow (1 / 2) t * geo_sum (M - (K + t))).
Proof.
  intros b K t M Hb H2b Ht. apply Qle_to_QleT'.
  revert Ht. revert t.
  induction M as [| M IH]; intros t Ht.
  - assert (HK : K = 0%nat) by lia.
    assert (Ht0 : t = 0%nat) by lia.
    rewrite HK, Ht0.
    apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. simpl. ring.
  - destruct (Nat.leb (K + t) M) eqn:E.
    + apply Nat.leb_le in E.
      assert (HM : (K + t <= M)%nat) by lia.
      specialize (IH t HM).
      change (qtail_sum b (K + t) (Datatypes.S M))
        with ((if Nat.leb (K + t) M then q_pow b M / q_fact M else 0)
              + qtail_sum b (K + t) M).
      assert (HL : Nat.leb (K + t) M = true) by (apply Nat.leb_le; exact E).
      replace (if Nat.leb (K + t) M then q_pow b M / q_fact M else 0)
        with (q_pow b M / q_fact M) by (rewrite HL; reflexivity).
      replace (Datatypes.S M - (K + t))%nat with (Datatypes.S (M - (K + t)))%nat by lia.
      change (geo_sum (Datatypes.S (M - (K + t))))
        with (geo_sum (M - (K + t)) + q_pow (1 / 2) (M - (K + t))).
      assert (Hterm : Qle (q_pow b M / q_fact M)
                        ((q_pow b K / q_fact K) * q_pow (1 / 2) t
                           * q_pow (1 / 2) (M - (K + t)))).
      { apply (Qle_trans _ ((q_pow b K / q_fact K) * q_pow (1 / 2) (M - K)) _).
        - apply QleT'_to_Qle. apply qtail_ratio_chain.
          + exact Hb.
          + exact H2b.
          + lia.
        - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
          replace (M - K)%nat with (t + (M - (K + t)))%nat by lia.
          rewrite (qeqT_imp_qeq _ _ (q_pow_add (1 / 2) t (M - (K + t)))).
          ring. }
      apply (Qle_trans _
        (((q_pow b K / q_fact K) * q_pow (1 / 2) t * q_pow (1 / 2) (M - (K + t)))
          + (q_pow b K / q_fact K) * q_pow (1 / 2) t * geo_sum (M - (K + t))) _).
      * apply (Qplus_le_compat (q_pow b M / q_fact M)
                  ((q_pow b K / q_fact K) * q_pow (1 / 2) t
                     * q_pow (1 / 2) (M - (K + t)))
                  (qtail_sum b (K + t) M)
                  ((q_pow b K / q_fact K) * q_pow (1 / 2) t
                     * geo_sum (M - (K + t)))).
        -- exact Hterm.
        -- exact IH.
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
    + apply Nat.leb_gt in E.
      apply (Qle_trans _ 0 _).
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply (qeqT_imp_qeq _ _). apply qtail_sum_le_m. lia.
      * apply Qmult_le_0_compat.
        -- apply Qmult_le_0_compat.
           ++ apply QleT'_to_Qle. apply q_pow_fact_nonneg. exact (Qle_to_QleT' 0 b Hb).
           ++ apply QleT'_to_Qle. apply q_pow_nonneg. apply Qhalf_nonneg.
        -- apply QleT'_to_Qle. apply qtail_geo_nonneg.
Qed.

(* Main statement: constructive Cauchy modulus; N = max(4, 2*floor(b)) + t0 fully explicit. *)
Lemma qtail_cauchy_modulus_aux : forall b e : Q, Qle 0 b -> Qlt 0 e ->
  sigT (fun N : nat => forall m n : nat, (N <= m)%nat -> (N <= n)%nat ->
    Qlt (qtail_sum b (Nat.min m n) (Nat.max m n)) e).
Proof.
  intros b e Hb He.
  assert (Hne : ~ (e == 0)).
  { assert (Hp : Qlt 0 e) by exact He.
    intro Hz. destruct (qtail_neq0 e Hp (qeq_imp_qeqT e 0 Hz)). }
  (* K = max(4, 2*floor(b)): from K on, each ratio step halves the term. *)
  assert (H2b : Qle ((1 + 1)%Q * b)
                     (Z.of_nat (Datatypes.S (Nat.max 4 (2 * Z.to_nat (Qnum b)))) # 1)).
  { apply (Qle_trans _ (Z.of_nat (2 * Z.to_nat (Qnum b) + 1) # 1) _).
    - apply QleT'_to_Qle. apply qtail_two_b_le. exact Hb.
    - apply QleT'_to_Qle.
      apply (Qle_of_nat (2 * Z.to_nat (Qnum b) + 1)
                        (Datatypes.S (Nat.max 4 (2 * Z.to_nat (Qnum b))))). lia. }
  set (K := Nat.max 4 (2 * Z.to_nat (Qnum b))) in *.
  set (C := q_pow b K / q_fact K).
  assert (HC : Qle 0 C) by (unfold C; apply QleT'_to_Qle; apply q_pow_fact_nonneg; exact (Qle_to_QleT' 0 b Hb)).
  destruct (Qeq_dec C 0) as [Hz | Hnz].
  - (* Case C = 0: every term from index K on is zero. *)
    remember (Z.to_nat (Qnum ((C * (1 + 1)) / e))) as t0 eqn:Et0.
    exists (K + t0)%nat.
    intros m n Hm Hn.
    assert (Hsum : Qle (qtail_sum b (Nat.min m n) (Nat.max m n))
                        (C * q_pow (1 / 2) t0 * (1 + 1)%Q)).
    { assert (HAnn : Qle 0 (qtail_sum b (K + t0) (Nat.min m n)))
        by (apply QleT'_to_Qle; apply qtail_sum_nonneg_aux; exact Hb).
      apply (Qle_trans _ (qtail_sum b (K + t0) (Nat.min m n)
                            + qtail_sum b (Nat.min m n) (Nat.max m n)) _).
      - apply (Qle_trans _ (0 + qtail_sum b (Nat.min m n) (Nat.max m n)) _).
        + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
        + apply (Qplus_le_compat 0 (qtail_sum b (K + t0) (Nat.min m n))
                      (qtail_sum b (Nat.min m n) (Nat.max m n))
                      (qtail_sum b (Nat.min m n) (Nat.max m n))).
          * exact HAnn.
          * apply Qle_refl.
      - apply (Qle_trans _ (qtail_sum b (K + t0) (Nat.max m n)) _).
        + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qeq_sym.
          apply (qeqT_imp_qeq _ _).
          apply (qtail_sum_add b (K + t0) (Nat.min m n) (Nat.max m n)); lia.
        + apply (Qle_trans _
                   (C * q_pow (1 / 2) t0 * geo_sum (Nat.max m n - (K + t0))) _).
          * apply QleT'_to_Qle.
        apply (qtail_sum_geo b K t0 (Nat.max m n) Hb H2b). lia.
          * apply QleT'_to_Qle.
            apply (qtail_mult_le_compat_l (geo_sum (Nat.max m n - (K + t0)))
                     (1 + 1)%Q (C * q_pow (1 / 2) t0)).
            -- apply QleT'_to_Qle. apply geo_sum_le_two.
            -- apply Qmult_le_0_compat.
               ++ exact HC.
               ++ apply QleT'_to_Qle. apply q_pow_nonneg. apply Qhalf_nonneg. }
    apply (Qle_lt_trans _ (C * q_pow (1 / 2) t0 * (1 + 1)%Q) _).
    + exact Hsum.
    + apply (Qle_lt_trans _ 0 _).
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. rewrite Hz. ring.
      * exact He.
  - (* Case C > 0: geometric remainder, with 2^t >= t+1 used explicitly. *)
    assert (HC2 : Qle 0 (C * (1 + 1)%Q))
      by (apply Qmult_le_0_compat; [ exact HC | apply QleT'_to_Qle; apply Q2_nonneg ]).
    assert (HC2pos : Qlt 0 (C * (1 + 1)%Q)).
    { apply Qmult_lt_0_compat.
      - destruct (Qle_lt_or_eq 0 C HC) as [H | H].
        + exact H.
        + exfalso. exact (Hnz (Qeq_sym _ _ H)).
      - apply QltT_to_Qlt. apply Q2_pos. }
    assert (HC2ne : ~ ((C * (1 + 1)%Q) == 0)).
    { assert (Hp : Qlt 0 (C * (1 + 1)%Q)) by exact HC2pos.
      intro Hz. destruct (qtail_neq0 _ Hp (qeq_imp_qeqT _ _ Hz)). }
    set (w := (C * (1 + 1)%Q) / e).
    assert (Hw0 : Qle 0 w).
    { unfold w. apply QleT'_to_Qle.
      apply (q_le_div_le 0 1 (C * (1 + 1)%Q) e).
      - apply qtail_Qlt01.
      - exact (Qlt_to_QltT 0 e He).
      - apply Qle_to_QleT'.
        apply (Qle_trans (0 * e) 0 ((C * (1 + 1)%Q) * 1)).
        + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
        + apply (Qle_trans 0 (C * (1 + 1)%Q) ((C * (1 + 1)%Q) * 1)).
          * exact HC2.
          * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
    assert (Hwpos : Qlt 0 w) by (unfold w; apply (QltT_to_Qlt 0 w); apply qtail_div_pos; assumption).
    assert (Hwne : ~ (((C * (1 + 1)%Q) / e) == 0)).
    { assert (Hp : Qlt 0 w) by (unfold w; apply (QltT_to_Qlt 0 w); apply qtail_div_pos; assumption).
      intro Hz. destruct (qtail_neq0 _ Hp (qeq_imp_qeqT _ _ Hz)). }
    assert (Hwlt : Qlt w (Z.of_nat (Datatypes.S (Z.to_nat (Qnum w))) # 1)).
    { assert (Hup : Qle w (Z.of_nat (Z.to_nat (Qnum w)) # 1))
        by (apply QleT'_to_Qle; apply qtail_pos_upper; exact Hw0).
      apply (Qle_lt_trans w (Z.of_nat (Z.to_nat (Qnum w)) # 1)
                           (Z.of_nat (Datatypes.S (Z.to_nat (Qnum w))) # 1)).
      - exact Hup.
      - apply QltT_to_Qlt.
        apply (Qlt_of_nat_lt (Z.to_nat (Qnum w))
                             (Datatypes.S (Z.to_nat (Qnum w)))). lia. }
    remember (Z.to_nat (Qnum w)) as t0 eqn:Et0.
    exists (K + t0)%nat.
    intros m n Hm Hn.
    assert (Hsum : Qle (qtail_sum b (Nat.min m n) (Nat.max m n))
                        (C * q_pow (1 / 2) t0 * (1 + 1)%Q)).
    { assert (HAnn : Qle 0 (qtail_sum b (K + t0) (Nat.min m n)))
        by (apply QleT'_to_Qle; apply qtail_sum_nonneg_aux; exact Hb).
      apply (Qle_trans _ (qtail_sum b (K + t0) (Nat.min m n)
                            + qtail_sum b (Nat.min m n) (Nat.max m n)) _).
      - apply (Qle_trans _ (0 + qtail_sum b (Nat.min m n) (Nat.max m n)) _).
        + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
        + apply (Qplus_le_compat 0 (qtail_sum b (K + t0) (Nat.min m n))
                      (qtail_sum b (Nat.min m n) (Nat.max m n))
                      (qtail_sum b (Nat.min m n) (Nat.max m n))).
          * exact HAnn.
          * apply Qle_refl.
      - apply (Qle_trans _ (qtail_sum b (K + t0) (Nat.max m n)) _).
        + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qeq_sym.
          apply (qeqT_imp_qeq _ _).
          apply (qtail_sum_add b (K + t0) (Nat.min m n) (Nat.max m n)); lia.
        + apply (Qle_trans _
                   (C * q_pow (1 / 2) t0 * geo_sum (Nat.max m n - (K + t0))) _).
          * apply QleT'_to_Qle.
        apply (qtail_sum_geo b K t0 (Nat.max m n) Hb H2b). lia.
          * apply QleT'_to_Qle.
            apply (qtail_mult_le_compat_l (geo_sum (Nat.max m n - (K + t0)))
                     (1 + 1)%Q (C * q_pow (1 / 2) t0)).
            -- apply QleT'_to_Qle. apply geo_sum_le_two.
            -- apply Qmult_le_0_compat.
               ++ exact HC.
               ++ apply QleT'_to_Qle. apply q_pow_nonneg. apply Qhalf_nonneg. }
    assert (Hst0 : ~ ((Z.of_nat (Datatypes.S t0) # 1) == 0)).
    { assert (Hp : Qlt 0 (Z.of_nat (Datatypes.S t0) # 1))
        by (apply QltT_to_Qlt; apply (Qlt_of_nat_lt 0 (Datatypes.S t0)); lia).
      intro Hz. destruct (qtail_neq0 _ Hp (qeq_imp_qeqT _ _ Hz)). }
    assert (Hinv : Qle ((C * (1 + 1)%Q) * q_pow (1 / 2) t0)
                        ((C * (1 + 1)%Q) * (1 / (Z.of_nat (Datatypes.S t0) # 1)))).
    { apply QleT'_to_Qle.
      apply (qtail_mult_le_compat_l (q_pow (1 / 2) t0)
                               (1 / (Z.of_nat (Datatypes.S t0) # 1))
                               (C * (1 + 1)%Q)).
      - apply QleT'_to_Qle. apply qtail_half_pow_le_invT.
      - exact HC2. }
    assert (Hwdef : ((C * (1 + 1)%Q) / w) == e).
    { unfold w. field. repeat split; assumption. }
    assert (Hst0pos : Qlt 0 (Z.of_nat (Datatypes.S t0) # 1)).
    { apply QltT_to_Qlt. apply (Qlt_of_nat_lt 0 (Datatypes.S t0)). lia. }
    assert (Hstrict : Qlt ((C * (1 + 1)%Q) * (1 / (Z.of_nat (Datatypes.S t0) # 1))) e).
    { assert (Hdv : Qlt ((C * (1 + 1)%Q) / (Z.of_nat (Datatypes.S t0) # 1))
                        ((C * (1 + 1)%Q) / w)).
      { apply (QltT_to_Qlt _ _).
        apply (qtail_div_lt (C * (1 + 1)%Q) (Z.of_nat (Datatypes.S t0) # 1)
                            (C * (1 + 1)%Q) w).
        - exact Hst0pos.
        - exact Hwpos.
        - apply (QltT_to_Qlt _ _).
          apply (qtail_mult_lt_compat_l (C * (1 + 1)%Q) w
                    (Z.of_nat (Datatypes.S t0) # 1)).
          + exact HC2pos.
          + exact Hwlt. }
      apply (Qle_lt_trans _ ((C * (1 + 1)%Q) / (Z.of_nat (Datatypes.S t0) # 1)) e).
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. field. repeat split; assumption.
      - apply (Qlt_le_trans _ ((C * (1 + 1)%Q) / w) e).
        + exact Hdv.
        + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold w. exact Hwdef. }
    apply (Qle_lt_trans _ ((C * q_pow (1 / 2) t0) * (1 + 1)%Q) _).
    + exact Hsum.
    + apply (Qle_lt_trans _
               ((C * (1 + 1)%Q) * (1 / (Z.of_nat (Datatypes.S t0) # 1))) _).
      * apply (Qle_trans _ ((C * (1 + 1)%Q) * q_pow (1 / 2) t0)).
        -- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
        -- exact Hinv.
      * exact Hstrict.
Qed.

(* Exit statement of this section (Set layer, QltT/sigT; symmetric min/max argument order). *)
Lemma qtail_cauchy_modulus : forall b e : Q,
  QleT 0 b -> QltT 0 e ->
  sigT (fun N : nat => forall m n : nat, (N <= m)%nat -> (N <= n)%nat ->
    QltT (qtail_sum b (Nat.min m n) (Nat.max m n)) e).
Proof.
  intros b e Hb He.
  destruct (qtail_cauchy_modulus_aux b e (qtail_QleT_to_Qle 0 b Hb)
              (QltT_to_Qlt 0 e He)) as [N HN].
  exists N. intros m n Hm Hn.
  apply Qlt_to_QltT. apply HN; assumption.
Qed.

(* Ordered-argument form (n <= m with both >= N), shaped for direct consumption as a Cauchy criterion. *)
Lemma qtail_cauchy_modulus_ord : forall b e : Q,
  QleT 0 b -> QltT 0 e ->
  sigT (fun N : nat => forall m n : nat, (N <= n)%nat -> (n <= m)%nat ->
    QltT (qtail_sum b n m) e).
Proof.
  intros b e Hb He.
  destruct (qtail_cauchy_modulus b e Hb He) as [N HN].
  exists N. intros m n Hn Hnm.
  assert (HB : QltT (qtail_sum b (Nat.min n m) (Nat.max n m)) e)
    by (apply (HN n m); lia).
  replace (Nat.min n m) with n in HB by lia.
  replace (Nat.max n m) with m in HB by lia.
  exact HB.
Qed.

(* Interface notes for the exponential-series modules.
   1) The difference of two truncated exponentials reduces, via
      [exp_partial_diff_tail], to a tail sum; for [Qabs x <= b] the
      modulus [qtail_cauchy_modulus_ord] applies directly with its
      explicitly computable witness [N(b, e)].
   2) Pade truncation remainders sum b^k/k! are controlled by
      [qtail_sum_mono] (growth), [qtail_sum_nonneg] (sign), and
      [qtail_cauchy_modulus] (explicit tail bound).
   3) Relation to [S03_QExp]: [qtail_sum b m n == exp_tail (pred m) (pred n) b]
      holds for [m, n >= 1] (identity recorded, not proven here);
      [qtail_fact_ge_pow] and [qtail_term_decay] supply the explicit
      lower bound [2^k <= k!] for the pow_fact family. *)
