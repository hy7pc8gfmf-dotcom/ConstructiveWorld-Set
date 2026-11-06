(* ConstructiveWorld-Set -- forward partial-sum upper bounds for the growth-quant supply family. *)

(** * piu1909_sall_upper: the forward partial-sum upper bound family.

    Mission.  The forward partial-sum arm of the row-total estimate: with
      [piu1905_T q n m = piu1888_qpow q m * piu1888_qfact (2 * n - m) /
      (piu1888_qfact (n - m) * piu1888_qfact m)], the truncation
      [piu1909_sall q n k] of the row sum over [m <= k] obeys
      [piu1909_sall_upper], [piu1909_sall q n n <= piu1909_UPTOT *
      piu1888_T0 n] with [piu1909_UPTOT = (337697#6048)] on the band
      [35#12 <= q <= 41#12] and [3 <= n]; the route runs through
      [piu1909_ffact], [piu1909_scale], [piu1909_bj_step], [piu1909_rem_step],
      [piu1909_rem_base], [piu1909_rem], and the file also carries the
      alternating odd-term sum face [piu1905_sodd], [piu1905_sodd_full].

    Dependencies.  Stdlib [QArith], [Lia], [Qring].  Requires
      [piu1888_growth_quant_lemma] of this development (the [piu1888_qN],
      [piu1888_qfact], [piu1888_qpow], [piu1888_T0] supply family).

    References.  This development, piu1909_sall_upper.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" piu1909_sall_upper.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 000160bc]. *)
From Stdlib Require Import QArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Qring.
Require Import piu1888_growth_quant_lemma.
Require Import S02_CauchyComplete
  (QltT_to_Qlt, QleT'_to_Qle, qeqT_imp_qeq).

Inductive piu1905_QleT (x y : Q) : Set :=
  piu1905_qleT_intro : x <= y -> piu1905_QleT x y.
Inductive piu1905_QltT (x y : Q) : Set :=
  piu1905_qltT_intro : x < y -> piu1905_QltT x y.
Inductive piu1905_QeqT (x y : Q) : Set :=
  piu1905_qeqT_intro : x == y -> piu1905_QeqT x y.
Inductive piu1905_band (q : Q) : Set :=
  piu1905_band_intro : (35#12) <= q -> q <= (41#12) -> piu1905_band q.

(* piu1905_bid packages the boolean equation [b = true] into a one-
   constructor Set carrier: its only constructor takes a proof of
   [b = true], so a term of type [piu1905_bid b] is exactly boolean
   evidence for [b]. *)
Inductive piu1905_bid (b : bool) : Set :=
| piu1905_bid_intro : b = true -> piu1905_bid b.

Definition piu1905_T (q : Q) (n m : nat) : Q :=
  piu1888_qpow q m * piu1888_qfact (2 * n - m) *
  / (piu1888_qfact (n - m) * piu1888_qfact m).
Definition piu1905_sodd_term (q : Q) (n k : nat) : Q :=
  if Nat.even k then piu1905_T q n (2 * k + 1)
                else Qopp (piu1905_T q n (2 * k + 1)).
Fixpoint piu1905_sodd (q : Q) (n k : nat) {struct k} : Q :=
  match k with
  | O => piu1905_sodd_term q n 0
  | S k' => piu1905_sodd q n k' + piu1905_sodd_term q n (S k')
  end.
Fixpoint piu1905_half (n : nat) : nat :=
  match n with
  | O => O
  | S O => O
  | S (S n') => S (piu1905_half n')
  end.
Definition piu1905_sodd_full (q : Q) (n : nat) : Q :=
  piu1905_sodd q n (piu1905_half (Nat.pred n)).

Lemma piu1905_prod_rotate : forall a b c : Q, a * (b * c) == b * (a * c).
Proof.
  intros a b c.
  rewrite (Qmult_assoc a b c).
  rewrite (Qmult_comm a b).
  rewrite <- (Qmult_assoc b a c).
  reflexivity.
Qed.

Lemma piu1905_T_pos : forall (q : Q) (n m : nat),
  (0#1) < q -> (m <= n)%nat -> piu1905_QltT (0#1) (piu1905_T q n m).
Proof.
  intros q n m Hq Hm. apply piu1905_qltT_intro. unfold piu1905_T.
  apply Qmult_lt_0_compat.
  - apply Qmult_lt_0_compat.
    + apply (QltT_to_Qlt (0#1) (piu1888_qpow q m)).
      apply piu1888_qpow_pos. exact Hq.
    + apply (QltT_to_Qlt (0#1) (piu1888_qfact (2 * n - m))).
      apply piu1888_qfact_pos.
  - apply Qinv_lt_0_compat. apply Qmult_lt_0_compat;
      [apply (QltT_to_Qlt (0#1) (piu1888_qfact (n - m))); apply piu1888_qfact_pos
      |apply (QltT_to_Qlt (0#1) (piu1888_qfact m)); apply piu1888_qfact_pos].
Qed.

Lemma piu1905_T0_pos : forall n : nat, piu1905_QltT (0#1) (piu1888_T0 n).
Proof.
  intros n. apply piu1905_qltT_intro.
  apply (QltT_to_Qlt (0#1) (piu1888_T0 n)). apply piu1888_T0_pos.
Qed.

Lemma piu1905_opp_le : forall x y : Q,
  piu1905_QleT x y -> piu1905_QleT (Qopp y) (Qopp x).
Proof.
  intros x y H. destruct H as [H]. apply piu1905_qleT_intro.
  apply (Qle_trans (Qopp y) (Qopp y + (y + Qopp x)) (Qopp x)).
  - apply (Qle_trans (Qopp y) (Qopp y + (0#1)) (Qopp y + (y + Qopp x))).
    + rewrite (Qplus_0_r (Qopp y)). apply Qle_refl.
    + apply (Qplus_le_compat (Qopp y) (Qopp y) (0#1) (y + Qopp x)).
      * apply Qle_refl.
      * apply (Qle_trans (0#1) (x + Qopp x) (y + Qopp x)).
        -- rewrite Qplus_opp_r. apply Qle_refl.
        -- apply (Qplus_le_compat x y (Qopp x) (Qopp x)).
           ++ exact H.
           ++ apply Qle_refl.
  - rewrite (Qplus_assoc (Qopp y) y (Qopp x)).
    rewrite (Qplus_comm (Qopp y) y).
    rewrite (Qplus_opp_r y).
    rewrite (Qplus_comm (0#1) (Qopp x)).
    rewrite (Qplus_0_r (Qopp x)). apply Qle_refl.
Qed.

Lemma piu1905_minus_le : forall a b c : Q,
  piu1905_QleT a b -> piu1905_QleT (c - b) (c - a).
Proof.
  intros a b c H. destruct H as [H]. apply piu1905_qleT_intro.
  apply (Qplus_le_compat c c (Qopp b) (Qopp a)).
  - apply Qle_refl.
  - apply piu1905_opp_le. apply piu1905_qleT_intro. exact H.
Qed.

Lemma piu1905_le_cancel : forall (c a b : Q),
  (0#1) < c -> piu1905_QleT (c * a) (c * b) -> piu1905_QleT a b.
Proof.
  intros c a b Hc H. destruct H as [H]. apply piu1905_qleT_intro.
  assert (Hc0 : ~ (c == 0)).
  { intro Heq. apply (Qlt_not_eq (0#1) c Hc). rewrite Heq. reflexivity. }
  assert (H1 : a * c <= b * c).
  { rewrite (Qmult_comm a c). rewrite (Qmult_comm b c). exact H. }
  assert (H2 : a * / c <= b * / c)
    by (apply (QleT'_to_Qle (a * / c) (b * / c));
        apply (piu1888_div_le a b c c); assumption).
  assert (Ha : a == a * / c * c).
  { rewrite <- (Qmult_assoc a (/ c) c).
    rewrite (Qmult_comm (/ c) c).
    rewrite (Qmult_inv_r c Hc0).
    rewrite Qmult_1_r. reflexivity. }
  assert (Hb : b == b * / c * c).
  { rewrite <- (Qmult_assoc b (/ c) c).
    rewrite (Qmult_comm (/ c) c).
    rewrite (Qmult_inv_r c Hc0).
    rewrite Qmult_1_r. reflexivity. }
  rewrite Ha. rewrite Hb.
  apply (Qmult_le_compat_r (a * / c) (b * / c) c).
  - exact H2.
  - apply Qlt_le_weak. exact Hc.
Qed.

Lemma piu1905_qN_add : forall a b : nat,
  piu1905_QeqT (piu1888_qN (a + b)) (piu1888_qN a + piu1888_qN b).
Proof.
  intros a b. apply piu1905_qeqT_intro.
  induction b as [|b IH].
  - replace (a + 0)%nat with a by lia.
    replace (piu1888_qN 0) with (0#1) by (vm_compute; reflexivity).
    rewrite Qplus_0_r. reflexivity.
  - replace (a + S b)%nat with (S (a + b)) by lia.
    rewrite (qeqT_imp_qeq _ _ (piu1888_qN_step (a + b))),
            (qeqT_imp_qeq _ _ (piu1888_qN_step b)), IH.
    rewrite (Qplus_assoc (1#1) (piu1888_qN a) (piu1888_qN b)).
    rewrite (Qplus_comm (1#1) (piu1888_qN a)).
    rewrite <- (Qplus_assoc (piu1888_qN a) (1#1) (piu1888_qN b)).
    reflexivity.
Qed.

Lemma piu1905_qN_mono : forall a b : nat,
  (a <= b)%nat -> piu1905_QleT (piu1888_qN a) (piu1888_qN b).
Proof.
  intros a b Hab. apply piu1905_qleT_intro.
  assert (Hsplit : piu1888_qN b == piu1888_qN a + piu1888_qN (b - a)).
  { assert (Hbr : b = (a + (b - a))%nat) by lia.
    destruct (piu1905_qN_add a (b - a)) as [Heq].
    rewrite Hbr at 1.
    rewrite Heq. reflexivity. }
  rewrite Hsplit.
  apply (Qle_trans (piu1888_qN a) (piu1888_qN a + (0#1))
                   (piu1888_qN a + piu1888_qN (b - a))).
  - rewrite Qplus_0_r. apply Qle_refl.
  - apply (Qplus_le_compat (piu1888_qN a) (piu1888_qN a) (0#1)
                           (piu1888_qN (b - a))).
    + apply Qle_refl.
    + apply (QleT'_to_Qle (0#1) (piu1888_qN (b - a))). apply piu1888_qN_ge0.
Qed.

Lemma piu1905_qpow_shift2 : forall (q : Q) (k : nat),
  piu1888_qpow q (k + 2) == q * q * piu1888_qpow q k.
Proof.
  intros q k. induction k as [|k IH].
  - cbn [piu1888_qpow Nat.add]. rewrite !Qmult_1_r. reflexivity.
  - cbn [piu1888_qpow Nat.add]. rewrite IH.
    rewrite (piu1905_prod_rotate q (q * q) (piu1888_qpow q k)).
    reflexivity.
Qed.

Lemma piu1905_T1_identity : forall (q : Q) (n : nat),
  (1 <= n)%nat -> piu1905_QeqT ((2#1) * piu1905_T q n 1) (q * piu1888_T0 n).
Proof.
  intros q n Hn. apply piu1905_qeqT_intro.
  unfold piu1905_T, piu1888_T0.
  cbn [piu1888_qpow]. rewrite Qmult_1_r.
  assert (Hq2 : piu1888_qfact (2 * n) == piu1888_qN (2 * n) * piu1888_qfact (2 * n - 1)).
  { replace (2 * n)%nat with (S (2 * n - 1)) by lia.
    rewrite (qeqT_imp_qeq _ _ (piu1888_qfact_step (2 * n - 1))).
    replace (S (2 * n - 1) - 1)%nat with (2 * n - 1)%nat by lia.
    reflexivity. }
  assert (Hqn : piu1888_qfact n == piu1888_qN n * piu1888_qfact (n - 1)).
  { replace n with (S (n - 1)) by lia.
    rewrite (qeqT_imp_qeq _ _ (piu1888_qfact_step (n - 1))).
    replace (S (n - 1) - 1)%nat with (n - 1)%nat by lia.
    reflexivity. }
  assert (Hc1 : piu1888_qfact 1 == (1#1)) by (vm_compute; reflexivity).
  rewrite Hq2, Hqn, Hc1, (qeqT_imp_qeq _ _ (piu1888_qN_double n)).
  rewrite Qmult_1_r.
  assert (HB0 : ~ (piu1888_qfact (n - 1) == 0)).
  { intro Heq.
    apply (Qlt_not_eq (0#1) (piu1888_qfact (n - 1))
            (QltT_to_Qlt (0#1) (piu1888_qfact (n - 1))
              (piu1888_qfact_pos (n - 1)))).
    rewrite Heq. reflexivity. }
  assert (HK0 : ~ (piu1888_qN n * piu1888_qfact (n - 1) == 0)).
  { intro Heq.
    assert (Hlt : (0#1) < piu1888_qN n).
    { replace n with (S (n - 1))%nat by lia.
      apply (QltT_to_Qlt (0#1) (piu1888_qN (S (n - 1)))).
      apply piu1888_qN_pos. }
    apply (Qlt_not_eq (0#1) (piu1888_qN n * piu1888_qfact (n - 1))
            (Qmult_lt_0_compat _ _ Hlt
               (QltT_to_Qlt (0#1) (piu1888_qfact (n - 1))
                 (piu1888_qfact_pos (n - 1))))).
    rewrite Heq. reflexivity. }
  apply qeqT_imp_qeq.
  apply (piu1888_Qmul_cancel
          ((2#1) * (q * piu1888_qfact (2 * n - 1) * / piu1888_qfact (n - 1)))
          (q * ((2#1) * piu1888_qN n * piu1888_qfact (2 * n - 1)
                * / (piu1888_qN n * piu1888_qfact (n - 1))))
          (piu1888_qN n * piu1888_qfact (n - 1)) HK0).
  rewrite <- (Qmult_assoc (2#1)
              (q * piu1888_qfact (2 * n - 1) * / piu1888_qfact (n - 1))
              (piu1888_qN n * piu1888_qfact (n - 1))).
  rewrite <- (Qmult_assoc (q * piu1888_qfact (2 * n - 1))
                       (/ piu1888_qfact (n - 1))
                       (piu1888_qN n * piu1888_qfact (n - 1))).
  rewrite (Qmult_comm (/ piu1888_qfact (n - 1))
                      (piu1888_qN n * piu1888_qfact (n - 1))).
  rewrite <- (Qmult_assoc (piu1888_qN n) (piu1888_qfact (n - 1))
                       (/ piu1888_qfact (n - 1))).
  rewrite (Qmult_inv_r (piu1888_qfact (n - 1)) HB0).
  rewrite Qmult_1_r.
  rewrite <- (Qmult_assoc q
              (((2#1) * piu1888_qN n) * piu1888_qfact (2 * n - 1)
               * / (piu1888_qN n * piu1888_qfact (n - 1)))
              (piu1888_qN n * piu1888_qfact (n - 1))).
  rewrite <- (Qmult_assoc (((2#1) * piu1888_qN n) * piu1888_qfact (2 * n - 1))
                       (/ (piu1888_qN n * piu1888_qfact (n - 1)))
                       (piu1888_qN n * piu1888_qfact (n - 1))).
  rewrite (Qmult_comm (/ (piu1888_qN n * piu1888_qfact (n - 1)))
                      (piu1888_qN n * piu1888_qfact (n - 1))).
  rewrite (Qmult_inv_r (piu1888_qN n * piu1888_qfact (n - 1)) HK0).
  rewrite Qmult_1_r.
  rewrite <- (Qmult_assoc (2#1) (piu1888_qN n) (piu1888_qfact (2 * n - 1))).
  rewrite (piu1905_prod_rotate q (2#1)
            (piu1888_qN n * piu1888_qfact (2 * n - 1))).
  rewrite (piu1905_prod_rotate q (piu1888_qN n)
            (piu1888_qfact (2 * n - 1))).
  rewrite (Qmult_comm (piu1888_qN n)
            (q * piu1888_qfact (2 * n - 1))).
  reflexivity.
Qed.

(* ---- band companions: positivity and the q * q <= 24 cap ---- *)

Lemma piu1905_band_pos : forall q : Q,
  piu1905_band q -> (0#1) < q.
Proof.
  intros q Hb. destruct Hb as [Hlo Hhi].
  apply (Qlt_le_trans (0#1) (35#12) q).
  - vm_compute. reflexivity.
  - exact Hlo.
Qed.

Lemma piu1905_band_qq_le : forall q : Q,
  piu1905_band q -> piu1905_QleT (q * q) (24#1).
Proof.
  intros q Hb. destruct Hb as [Hlo Hhi]. apply piu1905_qleT_intro.
  apply (Qle_trans (q * q) ((41#12) * (41#12)) (24#1)).
  - apply (Qle_trans (q * q) ((41#12) * q) ((41#12) * (41#12))).
    + apply (Qmult_le_compat_r q (41#12) q).
      * exact Hhi.
      * apply Qlt_le_weak.
        apply (piu1905_band_pos q (piu1905_band_intro q Hlo Hhi)).
    + rewrite (Qmult_comm (41#12) q).
      apply (Qmult_le_compat_r q (41#12) (41#12)).
      * exact Hhi.
      * vm_compute. discriminate.
  - vm_compute. discriminate.
Qed.


(* ---- the qN core inequality (2/3/4 decomposition) ---- *)

Lemma piu1905_qN_sum_ge0 : forall a b : nat,
  piu1905_QleT (0#1) (piu1888_qN a + piu1888_qN b).
Proof.
  intros a b. apply piu1905_qleT_intro.
  apply (Qle_trans (0#1) ((0#1) + (0#1)) (piu1888_qN a + piu1888_qN b)).
  - vm_compute. discriminate.
  - apply (Qplus_le_compat (0#1) (piu1888_qN a) (0#1) (piu1888_qN b)).
    + apply (QleT'_to_Qle (0#1) (piu1888_qN a)). apply piu1888_qN_ge0.
    + apply (QleT'_to_Qle (0#1) (piu1888_qN b)). apply piu1888_qN_ge0.
Qed.

Lemma piu1905_qN_core : forall (a2 a1 b2 b1 e3 e2 m : nat),
  (b2 = (a2 + m))%nat -> (b1 = (a1 + m))%nat ->
  (a2 <= m)%nat -> (a1 <= m)%nat ->
  (3 <= e3)%nat -> (2 <= e2)%nat ->
  piu1905_QleT ((24#1) * piu1888_qN a2 * piu1888_qN a1)
               (piu1888_qN b2 * (piu1888_qN e3 * (piu1888_qN e2 * piu1888_qN b1))).
Proof.
  intros a2 a1 b2 b1 e3 e2 m Hb2 Hb1 Ha2m Ha1m He3 He2.
  subst b2. subst b1.
  apply piu1905_qleT_intro.
  destruct (piu1905_qN_add a2 m) as [E2A].
  destruct (piu1905_qN_add a1 m) as [E1A].
  rewrite E2A, E1A.
  assert (Hmono2 : piu1905_QleT (piu1888_qN a2) (piu1888_qN m))
    by (apply piu1905_qN_mono; exact Ha2m).
  assert (Hmono1 : piu1905_QleT (piu1888_qN a1) (piu1888_qN m))
    by (apply piu1905_qN_mono; exact Ha1m).
  assert (HE3 : piu1905_QleT (piu1888_qN 3) (piu1888_qN e3))
    by (apply piu1905_qN_mono; exact He3).
  assert (HE2 : piu1905_QleT (piu1888_qN 2) (piu1888_qN e2))
    by (apply piu1905_qN_mono; exact He2).
  destruct HE3 as [HE3]. destruct HE2 as [HE2].
  assert (Hv3 : piu1888_qN 3 == (3#1)) by (vm_compute; reflexivity).
  assert (Hv2 : piu1888_qN 2 == (2#1)) by (vm_compute; reflexivity).
  rewrite Hv3 in HE3. rewrite Hv2 in HE2.
  assert (HA : piu1905_QleT ((2#1) * piu1888_qN a2)
                             (piu1888_qN a2 + piu1888_qN m)).
  { apply piu1905_qleT_intro.
    rewrite (Qmult_comm (2#1) (piu1888_qN a2)).
    assert (H2l : (2#1) == (1#1) + (1#1)) by (vm_compute; reflexivity).
    rewrite H2l, Qmult_plus_distr_r, Qmult_1_r.
    apply (Qplus_le_compat (piu1888_qN a2) (piu1888_qN a2)
                           (piu1888_qN a2) (piu1888_qN m)).
    - apply Qle_refl.
    - destruct Hmono2 as [Hm2]. exact Hm2. }
  assert (HB : piu1905_QleT ((2#1) * piu1888_qN a1)
                             (piu1888_qN a1 + piu1888_qN m)).
  { apply piu1905_qleT_intro.
    rewrite (Qmult_comm (2#1) (piu1888_qN a1)).
    assert (H2lb : (2#1) == (1#1) + (1#1)) by (vm_compute; reflexivity).
    rewrite H2lb, Qmult_plus_distr_r, Qmult_1_r.
    apply (Qplus_le_compat (piu1888_qN a1) (piu1888_qN a1)
                           (piu1888_qN a1) (piu1888_qN m)).
    - apply Qle_refl.
    - destruct Hmono1 as [Hm1]. exact Hm1. }
  assert (H4B : piu1905_QleT ((4#1) * piu1888_qN a1)
                             (piu1888_qN e2 * (piu1888_qN a1 + piu1888_qN m))).
  { apply piu1905_qleT_intro.
    assert (H4 : (4#1) == (2#1) * (2#1)) by (vm_compute; reflexivity).
    rewrite H4.
    apply (Qle_trans (((2#1) * (2#1)) * piu1888_qN a1)
                     ((piu1888_qN a1 + piu1888_qN m) * (2#1))
                     (piu1888_qN e2 * (piu1888_qN a1 + piu1888_qN m))).
    - rewrite <- (Qmult_assoc (2#1) (2#1) (piu1888_qN a1)).
      rewrite (Qmult_comm (2#1) (2 * piu1888_qN a1)).
      apply (Qmult_le_compat_r (2 * piu1888_qN a1)
               (piu1888_qN a1 + piu1888_qN m) (2#1)).
      + destruct HB as [HBx]. exact HBx.
      + vm_compute. discriminate.
    - rewrite (Qmult_comm (piu1888_qN a1 + piu1888_qN m) (2#1)).
      apply (Qmult_le_compat_r (2#1) (piu1888_qN e2)
               (piu1888_qN a1 + piu1888_qN m)).
      + exact HE2.
      + destruct (piu1905_qN_sum_ge0 a1 m) as [Hs1m]. exact Hs1m. }
  assert (Hrest : piu1905_QleT ((3#1) * ((4#1) * piu1888_qN a1))
                             (piu1888_qN e3 *
                              (piu1888_qN e2 *
                               (piu1888_qN a1 + piu1888_qN m)))).
  { apply piu1905_qleT_intro.
    apply (Qle_trans ((3#1) * ((4#1) * piu1888_qN a1))
                     ((3#1) * (piu1888_qN e2 *
                               (piu1888_qN a1 + piu1888_qN m)))
                     (piu1888_qN e3 *
                      (piu1888_qN e2 * (piu1888_qN a1 + piu1888_qN m)))).
    - rewrite (Qmult_comm (3#1) ((4#1) * piu1888_qN a1)).
      rewrite (Qmult_comm (3#1) (piu1888_qN e2 *
                                 (piu1888_qN a1 + piu1888_qN m))).
      apply (Qmult_le_compat_r ((4#1) * piu1888_qN a1)
                               (piu1888_qN e2 *
                                (piu1888_qN a1 + piu1888_qN m)) (3#1)).
      + destruct H4B as [H4B']. exact H4B'.
      + vm_compute. discriminate.
    - apply (Qmult_le_compat_r (3#1) (piu1888_qN e3)
                               (piu1888_qN e2 *
                                (piu1888_qN a1 + piu1888_qN m))).
      + exact HE3.
      + apply (QleT'_to_Qle (0#1)
                 (piu1888_qN e2 * (piu1888_qN a1 + piu1888_qN m)));
          apply piu1888_mul_ge0.
        * apply (QleT'_to_Qle (0#1) (piu1888_qN e2)). apply piu1888_qN_ge0.
        * destruct (piu1905_qN_sum_ge0 a1 m) as [Hs1m2]. exact Hs1m2. }
  assert (Hsp : ((24#1) * piu1888_qN a2) * piu1888_qN a1 ==
                ((2#1) * piu1888_qN a2) * ((3#1) * ((4#1) * piu1888_qN a1))).
  { rewrite <- (Qmult_assoc (24#1) (piu1888_qN a2) (piu1888_qN a1)).
    assert (H24 : (24#1) == (2#1) * ((3#1) * (4#1)))
      by (vm_compute; reflexivity).
    rewrite H24.
    rewrite <- (Qmult_assoc (2#1) ((3#1) * (4#1)) (piu1888_qN a2 * piu1888_qN a1)).
    rewrite <- (Qmult_assoc (3#1) (4#1) (piu1888_qN a2 * piu1888_qN a1)).
    rewrite (piu1905_prod_rotate (4#1) (piu1888_qN a2) (piu1888_qN a1)).
    rewrite (Qmult_assoc (3#1) (piu1888_qN a2) ((4#1) * piu1888_qN a1)).
    rewrite (Qmult_comm (3#1) (piu1888_qN a2)).
    rewrite <- (Qmult_assoc (piu1888_qN a2) (3#1) ((4#1) * piu1888_qN a1)).
    rewrite (Qmult_assoc (2#1) (piu1888_qN a2)
              ((3#1) * ((4#1) * piu1888_qN a1))).
    reflexivity. }
  rewrite Hsp.
  apply (Qle_trans ((2#1) * piu1888_qN a2 *
                     ((3#1) * ((4#1) * piu1888_qN a1)))
                   ((piu1888_qN a2 + piu1888_qN m) *
                    ((3#1) * ((4#1) * piu1888_qN a1)))
                   ((piu1888_qN a2 + piu1888_qN m) *
                    (piu1888_qN e3 *
                     (piu1888_qN e2 * (piu1888_qN a1 + piu1888_qN m))))).
  - destruct HA as [HA'].
    apply (Qmult_le_compat_r ((2#1) * piu1888_qN a2)
             (piu1888_qN a2 + piu1888_qN m)
             ((3#1) * ((4#1) * piu1888_qN a1))).
    + exact HA'.
    + apply (QleT'_to_Qle (0#1) ((3#1) * ((4#1) * piu1888_qN a1)));
        apply piu1888_mul_ge0.
      * vm_compute. discriminate.
      * apply (QleT'_to_Qle (0#1) ((4#1) * piu1888_qN a1));
          apply piu1888_mul_ge0.
        -- vm_compute. discriminate.
        -- apply (QleT'_to_Qle (0#1) (piu1888_qN a1)); apply piu1888_qN_ge0.
  - destruct Hrest as [Hrest'].
    rewrite (Qmult_comm (piu1888_qN a2 + piu1888_qN m)
              ((3#1) * ((4#1) * piu1888_qN a1))).
    rewrite (Qmult_comm (piu1888_qN a2 + piu1888_qN m)
              (piu1888_qN e3 *
               (piu1888_qN e2 * (piu1888_qN a1 + piu1888_qN m)))).
    apply (Qmult_le_compat_r ((3#1) * ((4#1) * piu1888_qN a1))
             (piu1888_qN e3 *
              (piu1888_qN e2 * (piu1888_qN a1 + piu1888_qN m)))
             (piu1888_qN a2 + piu1888_qN m)).
    + exact Hrest'.
    + destruct (piu1905_qN_sum_ge0 a2 m) as [Hs2m]. exact Hs2m.
Qed.


(* ---- adjacent odd-term decrease (L-dec) and the floor constant companions ---- *)

Lemma piu1905_T_pos' : forall (q : Q) (n m : nat),
  (0#1) < q -> piu1905_QltT (0#1) (piu1905_T q n m).
Proof.
  intros q n m Hq. apply piu1905_qltT_intro. unfold piu1905_T.
  apply Qmult_lt_0_compat.
  - apply Qmult_lt_0_compat.
    + apply (QltT_to_Qlt (0#1) (piu1888_qpow q m)).
      apply piu1888_qpow_pos. exact Hq.
    + apply (QltT_to_Qlt (0#1) (piu1888_qfact (2 * n - m))).
      apply piu1888_qfact_pos.
  - apply Qinv_lt_0_compat. apply Qmult_lt_0_compat;
      [apply (QltT_to_Qlt (0#1) (piu1888_qfact (n - m))); apply piu1888_qfact_pos
      |apply (QltT_to_Qlt (0#1) (piu1888_qfact m)); apply piu1888_qfact_pos].
Qed.

Lemma piu1905_floor_const_eq : (35#24) * (1775#3456) == (62125#82944).
Proof. vm_compute. reflexivity. Qed.

Lemma piu1905_negb_inv : forall b : bool, negb (negb b) = b.
Proof. destruct b; reflexivity. Qed.

Lemma piu1905_even_succ : forall k, Nat.even (S k) = negb (Nat.even k).
Proof.
  induction k as [|[|k] IH].
  - reflexivity.
  - reflexivity.
  - cbn [Nat.even] in IH |- *.
    rewrite IH.
    rewrite piu1905_negb_inv.
    reflexivity.
Qed.

Lemma piu1905_nat_double_ind : forall P : nat -> Set,
  P 0%nat -> P 1%nat -> (forall k, P k -> P (S (S k))) -> forall k, P k.
Proof.
  intros P H0 H1 HS k.
  (* the two adjacent values are paired in the informative sigma carrier,
     since the predicate ranges over [Set] and the pairing must stay
     extractable; the step rebuilds the pair from the step lemma *)
  assert (Hpair : { _ : P k & P (S k) }).
  { induction k as [|k [IH1 IH2]].
    - exact (existT _ H0 H1).
    - exact (existT _ IH2 (HS _ IH1)). }
  destruct Hpair as [Hk _]. exact Hk.
Qed.

Lemma piu1905_even_plus2 : forall a b : nat,
  Nat.even (a + S (S b)) = Nat.even (a + b).
Proof.
  induction a as [|a IH].
  - cbn [Nat.add]. cbn [Nat.even]. reflexivity.
  - intros b. cbn [Nat.add].
    rewrite piu1905_even_succ.
    rewrite piu1905_even_succ.
    rewrite IH. reflexivity.
Qed.

Lemma piu1905_even_2k : forall k, Nat.even (2 * k) = true.
Proof.
  (* the double-step induction runs on the boolean equation carried by
     [piu1905_bid], so the parity fact is first obtained as carrier
     evidence and then unpacked into the boolean equation *)
  assert (Hd : forall k, piu1905_bid (Nat.even (2 * k))).
  { apply piu1905_nat_double_ind.
    - apply piu1905_bid_intro. reflexivity.
    - apply piu1905_bid_intro. reflexivity.
    - intros k IH. apply piu1905_bid_intro.
      cbn [Nat.mul Nat.add Nat.even].
      rewrite (piu1905_even_plus2 k (k + 0)%nat).
      destruct IH as [Heq]. exact Heq. }
  intros k. destruct (Hd k) as [Heq]. exact Heq.
Qed.

Lemma piu1905_even_2k1 : forall k, Nat.even (2 * k + 1) = false.
Proof.
  intros k. replace (2 * k + 1)%nat with (S (2 * k))%nat by lia.
  rewrite piu1905_even_succ, piu1905_even_2k. reflexivity.
Qed.

Lemma piu1905_sodd_two_step : forall q n k,
  piu1905_sodd q n (S (S k)) ==
  piu1905_sodd q n k + (piu1905_sodd_term q n (S k) +
                        piu1905_sodd_term q n (S (S k))).
Proof.
  intros q n k. cbn [piu1905_sodd]. rewrite Qplus_assoc. reflexivity.
Qed.

Lemma piu1905_term_even : forall q n k, Nat.even k = true ->
  piu1905_sodd_term q n k == piu1905_T q n (2 * k + 1).
Proof.
  intros q n k H. unfold piu1905_sodd_term. rewrite H. reflexivity.
Qed.

Lemma piu1905_term_odd : forall q n k, Nat.even k = false ->
  piu1905_sodd_term q n k == Qopp (piu1905_T q n (2 * k + 1)).
Proof.
  intros q n k H. unfold piu1905_sodd_term. rewrite H. reflexivity.
Qed.

Lemma piu1905_T_odd_dec : forall (q : Q) (n i : nat),
  (0#1) < q -> (2 * i + 3 <= n)%nat ->
  (24#1) * piu1905_T q n (2 * i + 3) <= q * q * piu1905_T q n (2 * i + 1).
Proof.
  intros q n i Hq Hi.
  assert (Hqshift : piu1888_qpow q (2*i+3) == q * q * piu1888_qpow q (2*i+1)).
  { replace (2*i+3)%nat with (2*i+1+2)%nat by lia.
    rewrite piu1905_qpow_shift2. reflexivity. }
  assert (HfL : piu1888_qfact (n - (2*i+1)) ==
                piu1888_qN (n - (2*i+1)) *
                (piu1888_qN (n - (2*i+2)) * piu1888_qfact (n - (2*i+3)))).
  { replace (n - (2*i+1))%nat with (S (n - (2*i+2)))%nat by lia.
    rewrite (qeqT_imp_qeq _ _ (piu1888_qfact_step (n - (2*i+2)))).
    replace (n - (2*i+2))%nat with (S (n - (2*i+3)))%nat by lia.
    rewrite (qeqT_imp_qeq _ _ (piu1888_qfact_step (n - (2*i+3)))).
    reflexivity. }
  assert (HfG : piu1888_qfact (2*n - (2*i+1)) ==
                piu1888_qN (2*n - (2*i+1)) *
                (piu1888_qN (2*n - (2*i+2)) * piu1888_qfact (2*n - (2*i+3)))).
  { replace (2*n - (2*i+1))%nat with (S (2*n - (2*i+2)))%nat by lia.
    rewrite (qeqT_imp_qeq _ _ (piu1888_qfact_step (2*n - (2*i+2)))).
    replace (2*n - (2*i+2))%nat with (S (2*n - (2*i+3)))%nat by lia.
    rewrite (qeqT_imp_qeq _ _ (piu1888_qfact_step (2*n - (2*i+3)))).
    reflexivity. }
  assert (HfE : piu1888_qfact (2*i+3) ==
                piu1888_qN (2*i+3) *
                (piu1888_qN (2*i+2) * piu1888_qfact (2*i+1))).
  { replace (2*i+3)%nat with (S (2*i+2))%nat by lia.
    rewrite (qeqT_imp_qeq _ _ (piu1888_qfact_step (2*i+2))).
    replace (2*i+2)%nat with (S (2*i+1))%nat by lia.
    rewrite (qeqT_imp_qeq _ _ (piu1888_qfact_step (2*i+1))).
    reflexivity. }
  unfold piu1905_T.
  rewrite (Qmult_assoc (24#1)
            (piu1888_qpow q (2*i+3) * piu1888_qfact (2*n - (2*i+3)))
            (/ (piu1888_qfact (n - (2*i+3)) * piu1888_qfact (2*i+3)))).
  rewrite (Qmult_assoc (q*q)
            (piu1888_qpow q (2*i+1) * piu1888_qfact (2*n - (2*i+1)))
            (/ (piu1888_qfact (n - (2*i+1)) * piu1888_qfact (2*i+1)))).
  apply (QleT'_to_Qle
           (((24#1) * (piu1888_qpow q (2*i+3) * piu1888_qfact (2*n - (2*i+3)))) *
            / (piu1888_qfact (n - (2*i+3)) * piu1888_qfact (2*i+3)))
           ((q * q * (piu1888_qpow q (2*i+1) * piu1888_qfact (2*n - (2*i+1)))) *
            / (piu1888_qfact (n - (2*i+1)) * piu1888_qfact (2*i+1)))).
  apply (piu1888_div_le
          ((24#1) * (piu1888_qpow q (2*i+3) * piu1888_qfact (2*n - (2*i+3))))
          (q * q * (piu1888_qpow q (2*i+1) * piu1888_qfact (2*n - (2*i+1))))
          (piu1888_qfact (n - (2*i+3)) * piu1888_qfact (2*i+3))
          (piu1888_qfact (n - (2*i+1)) * piu1888_qfact (2*i+1))).
  - apply Qmult_lt_0_compat;
      [apply (QltT_to_Qlt (0#1) (piu1888_qfact (n - (2*i+3)))); apply piu1888_qfact_pos
      |apply (QltT_to_Qlt (0#1) (piu1888_qfact (2*i+3))); apply piu1888_qfact_pos].
  - apply Qmult_lt_0_compat;
      [apply (QltT_to_Qlt (0#1) (piu1888_qfact (n - (2*i+1)))); apply piu1888_qfact_pos
      |apply (QltT_to_Qlt (0#1) (piu1888_qfact (2*i+1))); apply piu1888_qfact_pos].
  - rewrite Hqshift, HfL, HfG, HfE.
    assert (E1 : ((24#1) * (((q*q) * piu1888_qpow q (2*i+1)) *
                             piu1888_qfact (2*n - (2*i+3)))) *
                 ((piu1888_qN (n - (2*i+1)) *
                   (piu1888_qN (n - (2*i+2)) * piu1888_qfact (n - (2*i+3)))) *
                  piu1888_qfact (2*i+1)) ==
                 ((24#1) * piu1888_qN (n - (2*i+1)) * piu1888_qN (n - (2*i+2))) *
                 ((((q*q) * piu1888_qpow q (2*i+1)) *
                   piu1888_qfact (2*n - (2*i+3))) *
                  (piu1888_qfact (n - (2*i+3)) * piu1888_qfact (2*i+1))))
      by ring.
    assert (E2 : ((q*q) * (piu1888_qpow q (2*i+1) *
                            (piu1888_qN (2*n - (2*i+1)) *
                             (piu1888_qN (2*n - (2*i+2)) *
                              piu1888_qfact (2*n - (2*i+3)))))) *
                 (piu1888_qfact (n - (2*i+3)) *
                  (piu1888_qN (2*i+3) *
                   (piu1888_qN (2*i+2) * piu1888_qfact (2*i+1)))) ==
                 (piu1888_qN (2*n - (2*i+1)) *
                  (piu1888_qN (2*i+3) *
                   (piu1888_qN (2*i+2) * piu1888_qN (2*n - (2*i+2))))) *
                 ((((q*q) * piu1888_qpow q (2*i+1)) *
                   piu1888_qfact (2*n - (2*i+3))) *
                  (piu1888_qfact (n - (2*i+3)) * piu1888_qfact (2*i+1))))
      by ring.
    rewrite E1, E2.
    apply (Qmult_le_compat_r
            ((24#1) * piu1888_qN (n - (2*i+1)) * piu1888_qN (n - (2*i+2)))
            (piu1888_qN (2*n - (2*i+1)) *
             (piu1888_qN (2*i+3) *
              (piu1888_qN (2*i+2) * piu1888_qN (2*n - (2*i+2)))))
            ((((q*q) * piu1888_qpow q (2*i+1)) *
              piu1888_qfact (2*n - (2*i+3))) *
             (piu1888_qfact (n - (2*i+3)) * piu1888_qfact (2*i+1)))).
    + assert (HCORE : piu1905_QleT
                        ((24#1) * piu1888_qN (n - (2*i+1)) *
                         piu1888_qN (n - (2*i+2)))
                        (piu1888_qN (2*n - (2*i+1)) *
                         (piu1888_qN (2*i+3) *
                          (piu1888_qN (2*i+2) *
                           piu1888_qN (2*n - (2*i+2)))))).
      * apply (piu1905_qN_core (n - (2*i+1)) (n - (2*i+2))
                 (2*n - (2*i+1)) (2*n - (2*i+2)) (2*i+3) (2*i+2) n).
        -- lia.
        -- lia.
        -- lia.
        -- lia.
        -- lia.
        -- lia.
      * destruct HCORE as [HC]. exact HC.
    + apply (QleT'_to_Qle (0#1)
               (((q*q) * piu1888_qpow q (2*i+1)) * piu1888_qfact (2*n - (2*i+3)) *
                (piu1888_qfact (n - (2*i+3)) * piu1888_qfact (2*i+1))));
      apply piu1888_mul_ge0.
      * apply (QleT'_to_Qle (0#1)
                 (((q*q) * piu1888_qpow q (2*i+1)) * piu1888_qfact (2*n - (2*i+3))));
        apply piu1888_mul_ge0.
        -- apply Qmult_le_0_compat.
           ++ apply Qmult_le_0_compat; apply Qlt_le_weak; exact Hq.
           ++ apply Qlt_le_weak.
              apply (QltT_to_Qlt (0#1) (piu1888_qpow q (2*i+1))).
              apply piu1888_qpow_pos. exact Hq.
        -- apply Qlt_le_weak.
           apply (QltT_to_Qlt (0#1) (piu1888_qfact (2*n - (2*i+3)))).
           apply piu1888_qfact_pos.
      * apply (QleT'_to_Qle (0#1)
                 (piu1888_qfact (n - (2*i+3)) * piu1888_qfact (2*i+1)));
          apply piu1888_mul_ge0;
          [apply Qlt_le_weak;
             apply (QltT_to_Qlt (0#1) (piu1888_qfact (n - (2*i+3))));
           apply piu1888_qfact_pos
          |apply Qlt_le_weak;
             apply (QltT_to_Qlt (0#1) (piu1888_qfact (2*i+1)));
           apply piu1888_qfact_pos].
Qed.

Print Assumptions piu1905_T_pos'.
Print Assumptions piu1905_floor_const_eq.
Print Assumptions piu1905_even_succ.
Print Assumptions piu1905_nat_double_ind.
Print Assumptions piu1905_even_2k.
Print Assumptions piu1905_even_2k1.
Print Assumptions piu1905_sodd_two_step.
Print Assumptions piu1905_term_even.
Print Assumptions piu1905_term_odd.
Print Assumptions piu1905_T_odd_dec.

Definition piu1909_UPTOT : Q := (337697#6048).

Fixpoint piu1909_sall (q : Q) (n k : nat) : Q :=
  match k with
  | O => piu1905_T q n 0
  | S k' => piu1909_sall q n k' + piu1905_T q n (S k')
  end.

Lemma piu1909_sall_SS : forall q n k,
  piu1909_sall q n (S k) == piu1909_sall q n k + piu1905_T q n (S k).
Proof. intros q n k. reflexivity. Qed.

Lemma piu1909_qpow_mono : forall (q c : Q) (k : nat),
  (0#1) < q -> q <= c -> piu1888_qpow q k <= piu1888_qpow c k.
Proof.
  intros q c k Hq Hqc. induction k as [|k IH].
  - vm_compute. discriminate.
  - cbn [piu1888_qpow].
    apply (Qle_trans (q * piu1888_qpow q k) (c * piu1888_qpow q k)
                     (c * piu1888_qpow c k)).
    + apply (Qmult_le_compat_r q c (piu1888_qpow q k)).
      * exact Hqc.
      * apply Qlt_le_weak.
        apply (QltT_to_Qlt (0#1) (piu1888_qpow q k)).
        apply piu1888_qpow_pos. exact Hq.
    + rewrite (Qmult_comm c (piu1888_qpow q k)).
      rewrite (Qmult_comm c (piu1888_qpow c k)).
      apply (Qmult_le_compat_r (piu1888_qpow q k) (piu1888_qpow c k) c).
      * exact IH.
      * apply Qlt_le_weak. exact (Qlt_le_trans (0#1) q c Hq Hqc).
Qed.

(* ==== falling factorial pairing: (2n-k)! * n! <= (2n)! * (n-k)! ==== *)

Lemma piu1909_ffact : forall n k : nat,
  (k <= n)%nat ->
  piu1888_qfact (2 * n - k) * piu1888_qfact n
  <= piu1888_qfact (2 * n) * piu1888_qfact (n - k).
Proof.
  intros n k. induction k as [|k IH].
  - intros Hk. replace (2 * n - 0)%nat with (2 * n)%nat by lia.
    replace (n - 0)%nat with n by lia. apply Qle_refl.
  - intros Hk.
    assert (HbG : piu1888_qfact (2 * n - k) ==
                  piu1888_qN (2 * n - k) * piu1888_qfact (2 * n - S k)).
    { replace (2 * n - k)%nat with (S (2 * n - S k))%nat by lia.
      rewrite (qeqT_imp_qeq _ _ (piu1888_qfact_step (2 * n - S k))).
      replace (S (2 * n - S k) - 1)%nat with (2 * n - S k)%nat by lia.
      reflexivity. }
    assert (HbL : piu1888_qfact (n - k) ==
                  piu1888_qN (n - k) * piu1888_qfact (n - S k)).
    { replace (n - k)%nat with (S (n - S k))%nat by lia.
      rewrite (qeqT_imp_qeq _ _ (piu1888_qfact_step (n - S k))).
      replace (S (n - S k) - 1)%nat with (n - S k)%nat by lia.
      reflexivity. }
    assert (HC : (0#1) < piu1888_qN (2 * n - k)).
    { replace (2 * n - k)%nat with (S (2 * n - S k))%nat by lia.
      apply (QltT_to_Qlt (0#1) (piu1888_qN (S (2 * n - S k)))).
      apply piu1888_qN_pos. }
    assert (E1 : piu1888_qN (2 * n - k) *
                 (piu1888_qfact (2 * n - S k) * piu1888_qfact n) ==
                 piu1888_qfact (2 * n - k) * piu1888_qfact n)
      by (rewrite HbG; ring).
    assert (EL : piu1888_qfact (2 * n) * piu1888_qfact (n - k) ==
                 piu1888_qfact (2 * n) *
                 (piu1888_qN (n - k) * piu1888_qfact (n - S k)))
      by (rewrite HbL; ring).
    assert (ER : piu1888_qN (2 * n - k) *
                 (piu1888_qfact (2 * n) * piu1888_qfact (n - S k)) ==
                 piu1888_qfact (2 * n) *
                 (piu1888_qN (2 * n - k) * piu1888_qfact (n - S k)))
      by ring.
    apply (piu1905_le_cancel (piu1888_qN (2 * n - k))
             (piu1888_qfact (2 * n - S k) * piu1888_qfact n)
             (piu1888_qfact (2 * n) * piu1888_qfact (n - S k)) HC).
    apply piu1905_qleT_intro.
    rewrite E1.
    apply (Qle_trans _ (piu1888_qfact (2 * n) * piu1888_qfact (n - k)) _).
    + apply IH. lia.
    + rewrite EL.
      rewrite (Qmult_comm (piu1888_qfact (2 * n))
                (piu1888_qN (n - k) * piu1888_qfact (n - S k))).
      rewrite ER.
      rewrite (Qmult_comm (piu1888_qfact (2 * n))
                (piu1888_qN (2 * n - k) * piu1888_qfact (n - S k))).
      apply (Qmult_le_compat_r
               (piu1888_qN (n - k) * piu1888_qfact (n - S k))
               (piu1888_qN (2 * n - k) * piu1888_qfact (n - S k))
               (piu1888_qfact (2 * n))).
      * apply (Qmult_le_compat_r (piu1888_qN (n - k))
                 (piu1888_qN (2 * n - k)) (piu1888_qfact (n - S k))).
        -- assert (HleNK : (n - k <= 2 * n - k)%nat) by lia.
           destruct (piu1905_qN_mono (n - k) (2 * n - k) HleNK) as [HqmNK].
           exact HqmNK.
        -- apply Qlt_le_weak.
           apply (QltT_to_Qlt (0#1) (piu1888_qfact (n - S k))).
           apply piu1888_qfact_pos.
      * apply Qlt_le_weak.
        apply (QltT_to_Qlt (0#1) (piu1888_qfact (2 * n))).
        apply piu1888_qfact_pos.
Qed.

(* ==== generic product monotone (compat_r-only route) ==== *)

Lemma piu1909_mult_le : forall x y z w : Q,
  x <= y -> z <= w -> (0#1) <= y -> (0#1) <= z -> x * z <= y * w.
Proof.
  intros x y z w Hxy Hzw Hy Hz.
  apply (Qle_trans (x * z) (y * z) (y * w)).
  - apply (Qmult_le_compat_r x y z); assumption.
  - rewrite (Qmult_comm y z). rewrite (Qmult_comm y w).
    apply (Qmult_le_compat_r z w y).
    + exact Hzw.
    + exact Hy.
Qed.

(* ==== factorial geometric floor: 6 * 4^j <= (j+3)! ==== *)

Lemma piu1909_qfact_ge4 : forall j : nat,
  (6#1) * piu1888_qpow (4#1) j <= piu1888_qfact (j + 3).
Proof.
  intros j. induction j as [|j IH].
  - vm_compute. discriminate.
  - replace (S j + 3)%nat with (S (j + 3))%nat by lia.
    rewrite (qeqT_imp_qeq _ _ (piu1888_qfact_step (j + 3))).
    assert (Hm0 : piu1905_QleT (piu1888_qN 4) (piu1888_qN (S (j + 3))))
      by (apply piu1905_qN_mono; lia).
    assert (Hq4 : (4#1) <= piu1888_qN (S (j + 3))).
    { destruct Hm0 as [Hm0']. exact Hm0'. }
    assert (E3 : (6#1) * piu1888_qpow (4#1) (S j) ==
                 (4#1) * ((6#1) * piu1888_qpow (4#1) j)).
    { cbn [piu1888_qpow]. ring. }
    assert (Hpos : (0#1) <= (6#1) * piu1888_qpow (4#1) j).
    { apply (QleT'_to_Qle (0#1) ((6#1) * piu1888_qpow (4#1) j)).
      apply piu1888_mul_ge0.
      - vm_compute. discriminate.
      - apply Qlt_le_weak.
        apply (QltT_to_Qlt (0#1) (piu1888_qpow (4#1) j)).
        apply piu1888_qpow_pos. vm_compute. reflexivity. }
    apply (Qle_trans ((6#1) * piu1888_qpow (4#1) (S j))
                     (piu1888_qN (S (j + 3)) * ((6#1) * piu1888_qpow (4#1) j))
                     (piu1888_qN (S (j + 3)) * piu1888_qfact (j + 3))).
    + rewrite E3.
      apply (Qmult_le_compat_r (4#1) (piu1888_qN (S (j + 3)))
                               ((6#1) * piu1888_qpow (4#1) j)).
      * exact Hq4.
      * exact Hpos.
    + apply (piu1909_mult_le (piu1888_qN (S (j + 3))) (piu1888_qN (S (j + 3)))
               ((6#1) * piu1888_qpow (4#1) j) (piu1888_qfact (j + 3))).
      * apply Qle_refl.
      * exact IH.
      * apply (QleT'_to_Qle (0#1) (piu1888_qN (S (j + 3)))).
        apply piu1888_qN_ge0.
      * exact Hpos.
Qed.

(* ==== Qinv antitone: 0 < a <= b -> /b <= /a ==== *)


(* ==== per-term scale bound: T(m) <= T0 * q^m / m!  (m <= n) ==== *)

Lemma piu1909_scale : forall (q : Q) (n m : nat),
  (0#1) < q -> (m <= n)%nat ->
  piu1905_QleT (piu1905_T q n m)
    (piu1888_T0 n * piu1888_qpow q m * / piu1888_qfact m).
Proof.
  intros q n m Hq Hm.
  assert (Hfn0 : ~ (piu1888_qfact n == 0)).
  { intro Heq.
    assert (Hn0 : ~ ((0#1) == piu1888_qfact n))
      by (apply (Qlt_not_eq (0#1) (piu1888_qfact n));
          apply (QltT_to_Qlt (0#1) (piu1888_qfact n)); apply piu1888_qfact_pos).
    exact (Qnot_eq_sym (0#1) (piu1888_qfact n) Hn0 Heq). }
  assert (Hcore : piu1888_qfact (2 * n - m) * piu1888_qfact n * / piu1888_qfact n
                  <= piu1888_qfact (2 * n) * piu1888_qfact (n - m) * / piu1888_qfact n).
  { apply (Qmult_le_compat_r (piu1888_qfact (2 * n - m) * piu1888_qfact n)
             (piu1888_qfact (2 * n) * piu1888_qfact (n - m)) (/ piu1888_qfact n)).
    - assert (Hff' := piu1909_ffact n m Hm). exact Hff'.
    - apply Qlt_le_weak. apply Qinv_lt_0_compat.
      apply (QltT_to_Qlt (0#1) (piu1888_qfact n)). apply piu1888_qfact_pos. }
  assert (E1 : piu1888_qfact (2 * n - m) * piu1888_qfact n * / piu1888_qfact n
               == piu1888_qfact (2 * n - m)).
  { rewrite <- (Qmult_assoc (piu1888_qfact (2 * n - m)) (piu1888_qfact n) (/ piu1888_qfact n)).
    rewrite (Qmult_inv_r (piu1888_qfact n) Hfn0). rewrite Qmult_1_r. reflexivity. }
  rewrite E1 in Hcore.
  assert (E2 : piu1888_qfact (2 * n) * piu1888_qfact (n - m) * / piu1888_qfact n
               == piu1888_T0 n * piu1888_qfact (n - m)).
  { unfold piu1888_T0. ring. }
  rewrite E2 in Hcore.
  unfold piu1905_T.
  apply piu1905_qleT_intro.
  apply (QleT'_to_Qle
           (piu1888_qpow q m * piu1888_qfact (2 * n - m) *
            / (piu1888_qfact (n - m) * piu1888_qfact m))
           (piu1888_T0 n * piu1888_qpow q m * / piu1888_qfact m)).
  apply (piu1888_div_le (piu1888_qpow q m * piu1888_qfact (2 * n - m))
           (piu1888_T0 n * piu1888_qpow q m)
           (piu1888_qfact (n - m) * piu1888_qfact m) (piu1888_qfact m)).
  - apply Qmult_lt_0_compat;
      [apply (QltT_to_Qlt (0#1) (piu1888_qfact (n - m))); apply piu1888_qfact_pos
      |apply (QltT_to_Qlt (0#1) (piu1888_qfact m)); apply piu1888_qfact_pos].
  - apply (QltT_to_Qlt (0#1) (piu1888_qfact m)). apply piu1888_qfact_pos.
  - assert (EL : (piu1888_qpow q m * piu1888_qfact (2 * n - m)) * piu1888_qfact m
                 == piu1888_qfact (2 * n - m) * (piu1888_qpow q m * piu1888_qfact m))
      by ring.
    assert (ER : (piu1888_T0 n * piu1888_qpow q m) *
                 (piu1888_qfact (n - m) * piu1888_qfact m)
                 == (piu1888_T0 n * piu1888_qfact (n - m)) *
                    (piu1888_qpow q m * piu1888_qfact m)) by ring.
    rewrite EL. rewrite ER.
    apply (piu1909_mult_le (piu1888_qfact (2 * n - m))
             (piu1888_T0 n * piu1888_qfact (n - m))
             (piu1888_qpow q m * piu1888_qfact m)
             (piu1888_qpow q m * piu1888_qfact m)).
    + exact Hcore.
    + apply Qle_refl.
    + apply (QleT'_to_Qle (0#1) (piu1888_T0 n * piu1888_qfact (n - m)));
        apply piu1888_mul_ge0; apply Qlt_le_weak;
          [apply (QltT_to_Qlt (0#1) (piu1888_T0 n)); apply piu1888_T0_pos
          |apply (QltT_to_Qlt (0#1) (piu1888_qfact (n - m)));
             apply piu1888_qfact_pos].
    + apply (QleT'_to_Qle (0#1) (piu1888_qpow q m * piu1888_qfact m));
        apply piu1888_mul_ge0;
          [apply Qlt_le_weak; apply (QltT_to_Qlt (0#1) (piu1888_qpow q m));
             apply piu1888_qpow_pos; exact Hq
          |apply Qlt_le_weak; apply (QltT_to_Qlt (0#1) (piu1888_qfact m));
             apply piu1888_qfact_pos].
Qed.

Print Assumptions piu1909_scale.

(* ==== B(j) ratio step: B(S j) <= B(j) * 41/60  (band) ==== *)

Lemma piu1909_bj_step : forall (q : Q) (n j : nat),
  (0#1) < q -> piu1905_band q ->
  piu1905_QleT (piu1888_T0 n * piu1888_qpow q (S (4 + j)) * / piu1888_qfact (S (4 + j)))
               (piu1888_T0 n * piu1888_qpow q (4 + j) * / piu1888_qfact (4 + j) * (41#60)).
Proof.
  intros q n j Hq Hb. destruct Hb as [Hlo Hhi].
  assert (HT0 : (0#1) < piu1888_T0 n)
    by (apply (QltT_to_Qlt (0#1) (piu1888_T0 n)); apply piu1888_T0_pos).
  assert (Hqp : (0#1) < piu1888_qpow q (4 + j))
    by (apply (QltT_to_Qlt (0#1) (piu1888_qpow q (4 + j)));
        apply piu1888_qpow_pos; exact Hq).
  assert (Hpos0 : (0#1) < piu1888_T0 n * piu1888_qpow q (4 + j))
    by (apply Qmult_lt_0_compat; assumption).
  assert (Hf'0 : ~ (piu1888_qfact (S (4 + j)) == 0)).
  { intro He.
    assert (Hn0 : ~ ((0#1) == piu1888_qfact (S (4 + j))))
      by (apply (Qlt_not_eq (0#1) (piu1888_qfact (S (4 + j))));
            apply (QltT_to_Qlt (0#1) (piu1888_qfact (S (4 + j))));
            apply piu1888_qfact_pos).
    exact (Qnot_eq_sym (0#1) (piu1888_qfact (S (4 + j))) Hn0 He). }
  assert (Hfj0 : ~ (piu1888_qfact (4 + j) == 0)).
  { intro He.
    assert (Hn0 : ~ ((0#1) == piu1888_qfact (4 + j)))
      by (apply (Qlt_not_eq (0#1) (piu1888_qfact (4 + j)));
            apply (QltT_to_Qlt (0#1) (piu1888_qfact (4 + j)));
            apply piu1888_qfact_pos).
    exact (Qnot_eq_sym (0#1) (piu1888_qfact (4 + j)) Hn0 He). }
  assert (Hm5 : piu1905_QleT (piu1888_qN 5) (piu1888_qN (S (4 + j))))
    by (apply piu1905_qN_mono; lia).
  assert (HN5 : (5#1) <= piu1888_qN (S (4 + j))).
  { destruct Hm5 as [Hm5']. exact Hm5'. }
  assert (Hfb : piu1888_qfact (S (4 + j))
                == piu1888_qN (S (4 + j)) * piu1888_qfact (4 + j))
    by (apply qeqT_imp_qeq; apply piu1888_qfact_step).
  assert (Hres : q * (60#1) <= (41#1) * piu1888_qN (S (4 + j))).
  { apply (Qle_trans (q * (60#1)) ((41#12) * (60#1))
                     ((41#1) * piu1888_qN (S (4 + j)))).
    - apply (Qmult_le_compat_r q (41#12) (60#1)).
      + exact Hhi.
      + vm_compute. discriminate.
    - assert (Hc205 : (41#12) * (60#1) == (205#1)) by (vm_compute; reflexivity).
      rewrite Hc205.
      apply (Qle_trans (205#1) ((41#1) * (5#1))
                       ((41#1) * piu1888_qN (S (4 + j)))).
      + vm_compute. discriminate.
      + rewrite (Qmult_comm (41#1) (piu1888_qN (S (4 + j)))).
        apply (Qmult_le_compat_r (5#1) (piu1888_qN (S (4 + j))) (41#1)).
        * exact HN5.
        * vm_compute. discriminate. }
  assert (Ecbn : piu1888_qpow q (S (4 + j)) == q * piu1888_qpow q (4 + j))
    by (cbn [piu1888_qpow]; reflexivity).
  assert (ELHS : piu1888_T0 n * piu1888_qpow q (S (4 + j)) * / piu1888_qfact (S (4 + j))
                 == (piu1888_T0 n * piu1888_qpow q (4 + j)) *
                    (q * / piu1888_qfact (S (4 + j))))
    by (rewrite Ecbn; ring).
  assert (ERHS : piu1888_T0 n * piu1888_qpow q (4 + j) * / piu1888_qfact (4 + j) * (41#60)
                 == (piu1888_T0 n * piu1888_qpow q (4 + j)) *
                    (/ piu1888_qfact (4 + j) * (41#60)))
    by ring.
  assert (Hm0 : (0#1) < (60#1) * piu1888_qfact (S (4 + j))).
  { apply Qmult_lt_0_compat.
    - vm_compute. reflexivity.
    - apply (QltT_to_Qlt (0#1) (piu1888_qfact (S (4 + j)))).
      apply piu1888_qfact_pos. }
  assert (EL2 : (q * / piu1888_qfact (S (4 + j))) *
                ((60#1) * piu1888_qfact (S (4 + j))) == q * (60#1)).
  { assert (Einv : (q * / piu1888_qfact (S (4 + j))) *
                   ((60#1) * piu1888_qfact (S (4 + j)))
                   == q * (60#1) *
                      (/ piu1888_qfact (S (4 + j)) * piu1888_qfact (S (4 + j))))
      by ring.
    rewrite Einv.
    rewrite (Qmult_comm (/ piu1888_qfact (S (4 + j))) (piu1888_qfact (S (4 + j)))).
    rewrite (Qmult_inv_r (piu1888_qfact (S (4 + j))) Hf'0).
    rewrite Qmult_1_r. reflexivity. }
  assert (ER2 : (/ piu1888_qfact (4 + j) * (41#60)) *
                ((60#1) * piu1888_qfact (S (4 + j)))
                == (41#1) * piu1888_qN (S (4 + j))).
  { rewrite Hfb.
    assert (Einv : (/ piu1888_qfact (4 + j) * (41#60)) *
                   ((60#1) * (piu1888_qN (S (4 + j)) * piu1888_qfact (4 + j)))
                   == (41#1) * piu1888_qN (S (4 + j)) *
                      (/ piu1888_qfact (4 + j) * piu1888_qfact (4 + j)))
      by ring.
    rewrite Einv.
    rewrite (Qmult_comm (/ piu1888_qfact (4 + j)) (piu1888_qfact (4 + j))).
    rewrite (Qmult_inv_r (piu1888_qfact (4 + j)) Hfj0).
    rewrite Qmult_1_r. reflexivity. }
  apply piu1905_qleT_intro.
  rewrite ELHS. rewrite ERHS.
  assert (Hcancel : q * / piu1888_qfact (S (4 + j))
                    <= / piu1888_qfact (4 + j) * (41#60)).
  { apply (piu1905_le_cancel ((60#1) * piu1888_qfact (S (4 + j)))
             (q * / piu1888_qfact (S (4 + j)))
             (/ piu1888_qfact (4 + j) * (41#60)) Hm0).
    apply piu1905_qleT_intro.
    rewrite (Qmult_comm ((60#1) * piu1888_qfact (S (4 + j)))
              (q * / piu1888_qfact (S (4 + j)))).
    rewrite (Qmult_comm ((60#1) * piu1888_qfact (S (4 + j)))
              (/ piu1888_qfact (4 + j) * (41#60))).
    rewrite EL2. rewrite ER2. exact Hres. }
  apply (piu1909_mult_le (piu1888_T0 n * piu1888_qpow q (4 + j))
           (piu1888_T0 n * piu1888_qpow q (4 + j))
           (q * / piu1888_qfact (S (4 + j)))
           (/ piu1888_qfact (4 + j) * (41#60))).
  + apply Qle_refl.
  + exact Hcancel.
  + apply (QleT'_to_Qle (0#1) (piu1888_T0 n * piu1888_qpow q (4 + j)));
      apply piu1888_mul_ge0;
      [apply Qlt_le_weak; apply (QltT_to_Qlt (0#1) (piu1888_T0 n));
         apply piu1888_T0_pos
      |apply Qlt_le_weak; apply (QltT_to_Qlt (0#1) (piu1888_qpow q (4 + j)));
         apply piu1888_qpow_pos; exact Hq].
  + apply (QleT'_to_Qle (0#1) (q * / piu1888_qfact (S (4 + j))));
      apply piu1888_mul_ge0;
      [apply Qlt_le_weak; exact Hq
      |apply Qlt_le_weak; apply Qinv_lt_0_compat;
         apply (QltT_to_Qlt (0#1) (piu1888_qfact (S (4 + j))));
         apply piu1888_qfact_pos].
Qed.

Print Assumptions piu1909_bj_step.

(* ==== remainder step: T(4+j) + B(S j)*60/19 <= B(j)*60/19 ==== *)

Lemma piu1909_rem_step : forall (q : Q) (n j : nat),
  (0#1) < q -> (4 + j <= n)%nat -> piu1905_band q ->
  piu1905_QleT (piu1905_T q n (4 + j)
                 + piu1888_T0 n * piu1888_qpow q (S (4 + j))
                   * / piu1888_qfact (S (4 + j)) * (60#19))
               (piu1888_T0 n * piu1888_qpow q (4 + j)
                 * / piu1888_qfact (4 + j) * (60#19)).
Proof.
  intros q n j Hq Hle Hb.
  assert (Hbj := piu1909_bj_step q n j Hq Hb).
  apply piu1905_qleT_intro.
  assert (E : piu1888_T0 n * piu1888_qpow q (4 + j) * / piu1888_qfact (4 + j) * (60#19)
              == piu1888_T0 n * piu1888_qpow q (4 + j) * / piu1888_qfact (4 + j)
                 + piu1888_T0 n * piu1888_qpow q (4 + j) * / piu1888_qfact (4 + j) * (41#19)).
  { assert (Hfold : (60#19) == (1#1) + (41#19)) by (vm_compute; reflexivity).
    rewrite Hfold. rewrite Qmult_plus_distr_r.
    rewrite (Qmult_1_r (piu1888_T0 n * piu1888_qpow q (4 + j) * / piu1888_qfact (4 + j))).
    reflexivity. }
  rewrite E.
  apply (Qplus_le_compat (piu1905_T q n (4 + j))
           (piu1888_T0 n * piu1888_qpow q (4 + j) * / piu1888_qfact (4 + j))
           (piu1888_T0 n * piu1888_qpow q (S (4 + j)) * / piu1888_qfact (S (4 + j)) * (60#19))
           (piu1888_T0 n * piu1888_qpow q (4 + j) * / piu1888_qfact (4 + j) * (41#19))).
  - destruct (piu1909_scale q n (4 + j) Hq Hle) as [Hs'].
    exact Hs'.
  - destruct Hbj as [Hbj'].
    apply (Qle_trans _
      (piu1888_T0 n * piu1888_qpow q (4 + j) * / piu1888_qfact (4 + j)
         * (41#60) * (60#19)) _).
    + apply (Qmult_le_compat_r
               (piu1888_T0 n * piu1888_qpow q (S (4 + j)) * / piu1888_qfact (S (4 + j)))
               (piu1888_T0 n * piu1888_qpow q (4 + j) * / piu1888_qfact (4 + j) * (41#60))
               ((60#19))).
      * exact Hbj'.
      * vm_compute. discriminate.
    + rewrite <- (Qmult_assoc (piu1888_T0 n * piu1888_qpow q (4 + j)
                                * / piu1888_qfact (4 + j)) (41#60) (60#19)).
      assert (Hc719 : (41#60) * (60#19) == (41#19)) by (vm_compute; reflexivity).
      rewrite Hc719. apply Qle_refl.
Qed.

Print Assumptions piu1909_rem_step.

(* ==== remainder base: sall(3) + B(0)*60/19 <= T0*UPTOT ==== *)

Lemma piu1909_rem_base : forall (q : Q) (n : nat),
  (0#1) < q -> (3 <= n)%nat -> piu1905_band q ->
  piu1909_sall q n 3
  + piu1888_T0 n * piu1888_qpow q 4 * / piu1888_qfact 4 * (60#19)
  <= piu1888_T0 n * piu1909_UPTOT.
Proof.
  intros q n Hq Hn3 Hb. destruct Hb as [Hlo Hhi].
  rewrite (piu1909_sall_SS q n 2). rewrite (piu1909_sall_SS q n 1).
  cbn [piu1909_sall].
  assert (HT0 : (0#1) <= piu1888_T0 n)
    by (apply Qlt_le_weak; apply (QltT_to_Qlt (0#1) (piu1888_T0 n));
        apply piu1888_T0_pos).
  assert (Hn1 : (1 <= n)%nat) by lia.
  assert (Hn2 : (2 <= n)%nat) by lia.
  (* T0 == T(q,n,0) *)
  assert (E0 : piu1905_T q n 0 == piu1888_T0 n).
  { unfold piu1905_T, piu1888_T0.
    replace (2 * n - 0)%nat with (2 * n)%nat by lia.
    replace (n - 0)%nat with n by lia.
    cbn [piu1888_qpow piu1888_qfact].
    rewrite (Qmult_1_r (piu1888_qfact n)).
    rewrite (Qmult_1_l (piu1888_qfact (2 * n))).
    reflexivity. }
  (* T1 == q*T0/2 and its bound *)
  assert (E1 : piu1905_T q n 1 == q * piu1888_T0 n * / (2#1)).
  { destruct (piu1905_T1_identity q n Hn1) as [Heq].
    assert (H20 : ~ ((2#1) == (0#1))).
    { intro He0. vm_compute in He0. discriminate He0. }
    assert (H2 : (2#1) * piu1905_T q n 1 * / (2#1) == q * piu1888_T0 n * / (2#1))
      by (rewrite Heq; reflexivity).
    rewrite <- (Qmult_assoc (2#1) (piu1905_T q n 1) (/ (2#1))) in H2.
    rewrite (Qmult_comm (2#1) (piu1905_T q n 1 * / (2#1))) in H2.
    rewrite <- (Qmult_assoc (piu1905_T q n 1) (/ (2#1)) (2#1)) in H2.
    rewrite (Qmult_comm (/ (2#1)) (2#1)) in H2.
    rewrite (Qmult_inv_r (2#1) H20) in H2.
    rewrite Qmult_1_r in H2.
    exact H2. }
  assert (HbT1 : piu1905_T q n 1 <= piu1888_T0 n * (41#24)).
  { rewrite E1.
    apply (Qle_trans (q * piu1888_T0 n * / (2#1))
             ((41#12) * piu1888_T0 n * / (2#1)) (piu1888_T0 n * (41#24))).
    - apply (Qmult_le_compat_r (q * piu1888_T0 n)
               ((41#12) * piu1888_T0 n) (/ (2#1))).
      + apply (piu1909_mult_le q (41#12) (piu1888_T0 n) (piu1888_T0 n)).
        * exact Hhi.
        * apply Qle_refl.
        * vm_compute. discriminate.
        * exact HT0.
      + apply Qlt_le_weak. apply Qinv_lt_0_compat.
        vm_compute. reflexivity.
    - assert (H24 : (41#12) * / (2#1) == (41#24)) by (vm_compute; reflexivity).
      rewrite (Qmult_comm (41#12) (piu1888_T0 n)).
      rewrite <- (Qmult_assoc (piu1888_T0 n) (41#12) (/ (2#1))).
      rewrite H24. apply Qle_refl. }
  (* T2 bound *)
  assert (HbT2 : piu1905_T q n 2 <= piu1888_T0 n * (1681#288)).
  { destruct (piu1909_scale q n 2 Hq Hn2) as [Hs2].
    apply (Qle_trans (piu1905_T q n 2)
             (piu1888_T0 n * piu1888_qpow q 2 * / piu1888_qfact 2)
             (piu1888_T0 n * (1681#288))).
    - exact Hs2.
    - rewrite <- (Qmult_assoc (piu1888_T0 n) (piu1888_qpow q 2) (/ piu1888_qfact 2)).
      apply (piu1909_mult_le (piu1888_T0 n) (piu1888_T0 n)
               (piu1888_qpow q 2 * / piu1888_qfact 2) (1681#288)).
      + apply Qle_refl.
      + apply (Qle_trans (piu1888_qpow q 2 * / piu1888_qfact 2)
                 (piu1888_qpow (41#12) 2 * / piu1888_qfact 2) (1681#288)).
        * apply (Qmult_le_compat_r (piu1888_qpow q 2) (piu1888_qpow (41#12) 2)
                   (/ piu1888_qfact 2)).
          -- apply (piu1909_qpow_mono q (41#12) 2 Hq Hhi).
          -- apply Qlt_le_weak. apply Qinv_lt_0_compat.
             apply (QltT_to_Qlt (0#1) (piu1888_qfact 2)).
             apply piu1888_qfact_pos.
        * assert (Hc2 : piu1888_qpow (41#12) 2 * / piu1888_qfact 2 == (1681#288))
            by (vm_compute; reflexivity).
          rewrite Hc2. apply Qle_refl.
      + exact HT0.
      + apply (QleT'_to_Qle (0#1) (piu1888_qpow q 2 * / piu1888_qfact 2));
          apply piu1888_mul_ge0.
        * apply Qlt_le_weak. apply (QltT_to_Qlt (0#1) (piu1888_qpow q 2)).
          apply piu1888_qpow_pos. exact Hq.
        * apply Qlt_le_weak. apply Qinv_lt_0_compat.
          apply (QltT_to_Qlt (0#1) (piu1888_qfact 2)). apply piu1888_qfact_pos. }
  (* T3 bound *)
  assert (HbT3 : piu1905_T q n 3 <= piu1888_T0 n * (68921#10368)).
  { assert (Hn3' : (3 <= n)%nat) by exact Hn3.
    destruct (piu1909_scale q n 3 Hq Hn3') as [Hs3].
    apply (Qle_trans (piu1905_T q n 3)
             (piu1888_T0 n * piu1888_qpow q 3 * / piu1888_qfact 3)
             (piu1888_T0 n * (68921#10368))).
    - exact Hs3.
    - rewrite <- (Qmult_assoc (piu1888_T0 n) (piu1888_qpow q 3) (/ piu1888_qfact 3)).
      apply (piu1909_mult_le (piu1888_T0 n) (piu1888_T0 n)
               (piu1888_qpow q 3 * / piu1888_qfact 3) (68921#10368)).
      + apply Qle_refl.
      + apply (Qle_trans (piu1888_qpow q 3 * / piu1888_qfact 3)
                 (piu1888_qpow (41#12) 3 * / piu1888_qfact 3) (68921#10368)).
        * apply (Qmult_le_compat_r (piu1888_qpow q 3) (piu1888_qpow (41#12) 3)
                   (/ piu1888_qfact 3)).
          -- apply (piu1909_qpow_mono q (41#12) 3 Hq Hhi).
          -- apply Qlt_le_weak. apply Qinv_lt_0_compat.
             apply (QltT_to_Qlt (0#1) (piu1888_qfact 3)).
             apply piu1888_qfact_pos.
        * assert (Hc3 : piu1888_qpow (41#12) 3 * / piu1888_qfact 3 == (68921#10368))
            by (vm_compute; reflexivity).
          rewrite Hc3. apply Qle_refl.
      + exact HT0.
      + apply (QleT'_to_Qle (0#1) (piu1888_qpow q 3 * / piu1888_qfact 3));
          apply piu1888_mul_ge0.
        * apply Qlt_le_weak. apply (QltT_to_Qlt (0#1) (piu1888_qpow q 3)).
          apply piu1888_qpow_pos. exact Hq.
        * apply Qlt_le_weak. apply Qinv_lt_0_compat.
          apply (QltT_to_Qlt (0#1) (piu1888_qfact 3)). apply piu1888_qfact_pos. }
  (* B(0)*60/19 bound *)
  assert (HbT4 : piu1888_T0 n * piu1888_qpow q 4 * / piu1888_qfact 4 * (60#19)
                 <= piu1888_T0 n * (169545660#9455616)).
  { rewrite <- (Qmult_assoc (piu1888_T0 n) (piu1888_qpow q 4) (/ piu1888_qfact 4)).
    rewrite <- (Qmult_assoc (piu1888_T0 n)
                 (piu1888_qpow q 4 * / piu1888_qfact 4) ((60#19))).
    apply (piu1909_mult_le (piu1888_T0 n) (piu1888_T0 n)
             (piu1888_qpow q 4 * / piu1888_qfact 4 * (60#19)) (169545660#9455616)).
    + apply Qle_refl.
    + apply (Qle_trans (piu1888_qpow q 4 * / piu1888_qfact 4 * (60#19))
               (piu1888_qpow (41#12) 4 * / piu1888_qfact 4 * (60#19))
               (169545660#9455616)).
      * apply (piu1909_mult_le (piu1888_qpow q 4 * / piu1888_qfact 4)
                 (piu1888_qpow (41#12) 4 * / piu1888_qfact 4)
                 ((60#19)) ((60#19))).
        -- apply (Qmult_le_compat_r (piu1888_qpow q 4) (piu1888_qpow (41#12) 4)
                    (/ piu1888_qfact 4)).
           ++ apply (piu1909_qpow_mono q (41#12) 4 Hq Hhi).
           ++ apply Qlt_le_weak. apply Qinv_lt_0_compat.
              apply (QltT_to_Qlt (0#1) (piu1888_qfact 4)).
              apply piu1888_qfact_pos.
        -- apply Qle_refl.
        -- apply (QleT'_to_Qle (0#1)
                   (piu1888_qpow (41#12) 4 * / piu1888_qfact 4));
             apply piu1888_mul_ge0.
           ++ apply Qlt_le_weak.
              apply (QltT_to_Qlt (0#1) (piu1888_qpow (41#12) 4)).
              apply piu1888_qpow_pos. vm_compute. reflexivity.
           ++ apply Qlt_le_weak. apply Qinv_lt_0_compat.
              apply (QltT_to_Qlt (0#1) (piu1888_qfact 4)).
              apply piu1888_qfact_pos.
        -- vm_compute. discriminate.
      * assert (Hc4 : piu1888_qpow (41#12) 4 * / piu1888_qfact 4 * (60#19)
                    == (169545660#9455616)) by (vm_compute; reflexivity).
        rewrite Hc4. apply Qle_refl.
    + exact HT0.
    + apply (QleT'_to_Qle (0#1)
               ((piu1888_qpow q 4 * / piu1888_qfact 4) * (60#19)));
        apply piu1888_mul_ge0.
      * apply (QleT'_to_Qle (0#1) (piu1888_qpow q 4 * / piu1888_qfact 4));
          apply piu1888_mul_ge0.
        -- apply Qlt_le_weak. apply (QltT_to_Qlt (0#1) (piu1888_qpow q 4)).
           apply piu1888_qpow_pos. exact Hq.
        -- apply Qlt_le_weak. apply Qinv_lt_0_compat.
           apply (QltT_to_Qlt (0#1) (piu1888_qfact 4)). apply piu1888_qfact_pos.
      * vm_compute. discriminate. }
  (* five-addend chain *)
  apply (Qle_trans
      (piu1905_T q n 0 + piu1905_T q n 1 + piu1905_T q n 2 + piu1905_T q n 3
         + piu1888_T0 n * piu1888_qpow q 4 * / piu1888_qfact 4 * (60#19))
      (piu1888_T0 n * (1#1) + piu1888_T0 n * (41#24)
         + piu1888_T0 n * (1681#288) + piu1888_T0 n * (68921#10368)
         + piu1888_T0 n * (169545660#9455616))
      (piu1888_T0 n * piu1909_UPTOT)).
  - rewrite E0.
    apply (Qplus_le_compat
        (piu1888_T0 n + piu1905_T q n 1 + piu1905_T q n 2 + piu1905_T q n 3)
        (piu1888_T0 n * (1#1) + piu1888_T0 n * (41#24)
           + piu1888_T0 n * (1681#288) + piu1888_T0 n * (68921#10368))
        (piu1888_T0 n * piu1888_qpow q 4 * / piu1888_qfact 4 * (60#19))
        (piu1888_T0 n * (169545660#9455616))).
    + apply (Qplus_le_compat
        (piu1888_T0 n + piu1905_T q n 1 + piu1905_T q n 2)
        (piu1888_T0 n * (1#1) + piu1888_T0 n * (41#24)
           + piu1888_T0 n * (1681#288))
        (piu1905_T q n 3) (piu1888_T0 n * (68921#10368))).
      * apply (Qplus_le_compat
          (piu1888_T0 n + piu1905_T q n 1)
          (piu1888_T0 n * (1#1) + piu1888_T0 n * (41#24))
          (piu1905_T q n 2) (piu1888_T0 n * (1681#288))).
        -- apply (Qplus_le_compat (piu1888_T0 n) (piu1888_T0 n * (1#1))
                    (piu1905_T q n 1) (piu1888_T0 n * (41#24))).
           ++ rewrite (Qmult_1_r (piu1888_T0 n)). apply Qle_refl.
           ++ exact HbT1.
        -- exact HbT2.
      * exact HbT3.
    + exact HbT4.
  - rewrite <- (Qmult_plus_distr_r (piu1888_T0 n) (1#1) (41#24)).
    rewrite <- (Qplus_assoc (piu1888_T0 n * ((1#1) + (41#24)))
                  (piu1888_T0 n * (1681#288)) (piu1888_T0 n * (68921#10368))).
    rewrite <- (Qmult_plus_distr_r (piu1888_T0 n) (1681#288) (68921#10368)).
    rewrite <- (Qmult_plus_distr_r (piu1888_T0 n)
                  ((1#1) + (41#24)) ((1681#288) + (68921#10368))).
    rewrite <- (Qmult_plus_distr_r (piu1888_T0 n)
                  ((1#1) + (41#24) + ((1681#288) + (68921#10368)))
                  (169545660#9455616)).
    assert (HS5 : (1#1) + (41#24) + ((1681#288) + (68921#10368))
                    + (169545660#9455616) == (26100097#787968))
      by (vm_compute; reflexivity).
    rewrite HS5.
    rewrite (Qmult_comm (piu1888_T0 n) (26100097#787968)).
    rewrite (Qmult_comm (piu1888_T0 n) piu1909_UPTOT).
    apply (Qmult_le_compat_r (26100097#787968) piu1909_UPTOT (piu1888_T0 n)).
    + vm_compute. discriminate.
    + exact HT0.
Qed.

Print Assumptions piu1909_rem_base.

(* ==== remainder induction ==== *)

Lemma piu1909_rem : forall (q : Q) (n j : nat),
  (0#1) < q -> (3 <= n)%nat -> piu1905_band q -> (3 + j <= n)%nat ->
  piu1909_sall q n (3 + j)
  + piu1888_T0 n * piu1888_qpow q (4 + j) * / piu1888_qfact (4 + j) * (60#19)
  <= piu1888_T0 n * piu1909_UPTOT.
Proof.
  intros q n j. induction j as [|j IH]; intros Hq Hn3 Hb Hjle.
  - replace (3 + 0)%nat with 3%nat by lia.
    replace (4 + 0)%nat with 4%nat by lia.
    apply (piu1909_rem_base q n Hq Hn3 Hb).
  - assert (Hpre : (3 + j <= n)%nat) by lia.
    assert (Hle4 : (4 + j <= n)%nat) by lia.
    specialize (IH Hq Hn3 Hb Hpre).
    replace (3 + S j)%nat with (S (3 + j))%nat by lia.
    rewrite piu1909_sall_SS.
    replace (S (3 + j))%nat with (4 + j)%nat by lia.
    replace (4 + S j)%nat with (S (4 + j))%nat by lia.
    destruct (piu1909_rem_step q n j Hq Hle4 Hb) as [Hst].
    apply (Qle_trans
        (piu1909_sall q n (3 + j) + piu1905_T q n (4 + j)
           + piu1888_T0 n * piu1888_qpow q (S (4 + j)) * / piu1888_qfact (S (4 + j)) * (60#19))
        (piu1909_sall q n (3 + j)
           + piu1888_T0 n * piu1888_qpow q (4 + j) * / piu1888_qfact (4 + j) * (60#19))
        (piu1888_T0 n * piu1909_UPTOT)).
    + rewrite <- Qplus_assoc.
      apply (Qplus_le_compat (piu1909_sall q n (3 + j)) (piu1909_sall q n (3 + j))
               (piu1905_T q n (4 + j)
                  + piu1888_T0 n * piu1888_qpow q (S (4 + j))
                    * / piu1888_qfact (S (4 + j)) * (60#19))
               (piu1888_T0 n * piu1888_qpow q (4 + j) * / piu1888_qfact (4 + j) * (60#19))).
      * apply Qle_refl.
      * exact Hst.
    + exact IH.
Qed.

Print Assumptions piu1909_rem.

(* ==== master: sall q n n <= (337697/6048) * T0 n ==== *)

Theorem piu1909_sall_upper : forall (q : Q) (n : nat),
  (3 <= n)%nat -> piu1905_band q ->
  piu1905_QleT (piu1909_sall q n n) ((337697#6048) * piu1888_T0 n).
Proof.
  intros q n Hn3 Hb.
  apply piu1905_qleT_intro.
  assert (Hq : (0#1) < q) by (apply piu1905_band_pos; exact Hb).
  assert (Hj : (3 + (n - 3) <= n)%nat) by lia.
  assert (Hrem := piu1909_rem q n (n - 3) Hq Hn3 Hb Hj).
  assert (Hnat : (3 + (n - 3) = n)%nat) by lia.
  rewrite Hnat in Hrem.
  unfold piu1909_UPTOT in Hrem.
  rewrite (Qmult_comm (piu1888_T0 n) (337697#6048)) in Hrem.
  apply (Qle_trans (piu1909_sall q n n)
           (piu1909_sall q n n
              + piu1888_T0 n * piu1888_qpow q (4 + (n - 3))
                * / piu1888_qfact (4 + (n - 3)) * (60#19))
           ((337697#6048) * piu1888_T0 n)).
  - apply (Qle_trans (piu1909_sall q n n)
             (piu1909_sall q n n + (0#1))
             (piu1909_sall q n n
                + piu1888_T0 n * piu1888_qpow q (4 + (n - 3))
                  * / piu1888_qfact (4 + (n - 3)) * (60#19))).
    + rewrite Qplus_0_r. apply Qle_refl.
    + apply (Qplus_le_compat (piu1909_sall q n n) (piu1909_sall q n n)
               (0#1)
               (piu1888_T0 n * piu1888_qpow q (4 + (n - 3))
                  * / piu1888_qfact (4 + (n - 3)) * (60#19))).
      * apply Qle_refl.
      * apply (QleT'_to_Qle (0#1)
               ((piu1888_T0 n * piu1888_qpow q (4 + (n - 3)) *
                 / piu1888_qfact (4 + (n - 3))) * (60#19)));
        apply piu1888_mul_ge0.
        -- apply (QleT'_to_Qle (0#1)
                   (piu1888_T0 n * piu1888_qpow q (4 + (n - 3)) *
                    / piu1888_qfact (4 + (n - 3))));
           apply piu1888_mul_ge0.
           ++ apply (QleT'_to_Qle (0#1)
                       (piu1888_T0 n * piu1888_qpow q (4 + (n - 3))));
              apply piu1888_mul_ge0.
              ** apply Qlt_le_weak.
                 apply (QltT_to_Qlt (0#1) (piu1888_T0 n)).
                 apply piu1888_T0_pos.
              ** apply Qlt_le_weak.
                 apply (QltT_to_Qlt (0#1) (piu1888_qpow q (4 + (n - 3)))).
                 apply piu1888_qpow_pos. exact Hq.
           ++ apply Qlt_le_weak. apply Qinv_lt_0_compat.
              apply (QltT_to_Qlt (0#1) (piu1888_qfact (4 + (n - 3)))).
              apply piu1888_qfact_pos.
        -- vm_compute. discriminate.
  - exact Hrem.
Qed.

Print Assumptions piu1909_sall_upper.
Print Assumptions piu1909_sall_SS.
Print Assumptions piu1909_qpow_mono.
Print Assumptions piu1909_ffact.
Print Assumptions piu1909_qfact_ge4.
Print Assumptions piu1909_mult_le.
