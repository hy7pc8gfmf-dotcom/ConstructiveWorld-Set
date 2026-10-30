(* ConstructiveWorld-Set -- abl_W9_pi_widen_13: pi zero uniqueness bridge,
   widened ablation (upper bound 2 -> 7/2), concrete Cauchy real layer. *)
(** * abl_W9_pi_widen_13: pi zero uniqueness bridge widened ablation.
    Mission.  [abl13_cos_pi_half_unique_widened2]: for every Cauchy real [w]
      with [real_lt (real_const (3 / 2)) w] and [real_lt w (real_const
      (7 / 2))], [real_eq (cauchy_real_cos w) real_zero] implies
      [real_eq w cos_pi_half]. Source slot [cos_pi_half_unique]
      (S10:8610); [cos_pi_half_unique_widened] (S10:9465) already relaxed
      the bound 5/3 -> 2; this piece is the second step 2 -> 7/2.
      Kernel: cos has no zero on (2, 7/2) — (i) tail even-pairing
      induction (k >= 4, t^2 <= 49/4 imply cos_partial k t <=
      cos_partial 4 t); (ii) the S4 anchor (s := t^2 - 4 in [0, 33/4];
      cos_partial 4 t + 2/5 == (s^4 - 40 s^3 + 1104 s^2 - 9152 s -
      640)/40320 < 0); (iii) pointwise Q decidable branch assembly.
    Dependencies.  Stdlib [QArith], [Qabs], [Qround], [ZArith], [Lia],
      [Qminmax], [Arith], [Setoid], [Morphisms], [Extraction]; chain
      pieces S01_BaseRing, S02_CauchyComplete, S03_QExp, S10_KVQuantTrig.
    References.  ConstructiveWorld_Live/S10_KVQuantTrig.v (read-only
      source); [cos_pi_half_unique_widened] (S10:9465).
    Constructivity.  Purely constructive; no classical faces; zero
      admission word faces; all pieces closed by [Qed]; tail
      [Print Assumptions] Closed x26; extraction [Obj.magic] 0.
    Build.  [rocq c -native-compiler no -q -Q . "" abl_W9_pi_widen_13.v]
      in the seat world closure; wrapped by cpu_guard (-Reg
      /tmp/cw_reg_nw1 -Front 0 -Mid 1 -MaxWaitSec 600) with
      [ulimit -s 65532]. *)

From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround ZArith.
From Stdlib Require Import Lia QArith.Qminmax.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Extraction.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S10_KVQuantTrig.

(* ============================================================ *)
(* Part 1 · Q-layer micro machinery (square nonneg / absolute    *)
(* value / division order preservation / sign factors)           *)
(* ============================================================ *)

(* Square nonneg: t^2 >= 0 (constructive dichotomy, zero classical). *)
Lemma abl13_qsq_nonneg : forall t : Q, QleT' 0 (t * t).
Proof.
  intro t. apply Qle_to_QleT'.
  destruct (Qlt_le_dec 0 t) as [Hpos | Hneg].
  - apply (Qmult_le_0_compat t t).
    + apply Qlt_le_weak. exact Hpos.
    + apply Qlt_le_weak. exact Hpos.
  - assert (Hopp : Qle 0 (- t)).
    { assert (H := Qopp_le_compat t 0 Hneg).
      assert (Hz : - 0 == 0) by ring.
      rewrite Hz in H. exact H. }
    assert (Hr : t * t == (- t) * (- t)) by ring.
    rewrite Hr.
    apply (Qmult_le_0_compat (- t) (- t) Hopp Hopp).
Qed.

(* t^2 == |t| * |t|. *)
Lemma abl13_qsq_abs : forall t : Q, QeqT (t * t) (Qabs t * Qabs t).
Proof.
  intro t. apply qeq_imp_qeqT.
  assert (H1 : Qabs (t * t) == Qabs t * Qabs t) by apply Qabs_Qmult.
  assert (H2 : Qabs (t * t) == t * t)
    by (apply Qabs_pos; apply QleT'_to_Qle; apply abl13_qsq_nonneg).
  rewrite <- H1. symmetry. exact H2.
Qed.

(* Positive modulus division order preservation: 0 < M, a*M <= b*M implies
   a <= b (Qle_dec constructive dichotomy). *)
Lemma abl13_qdiv_le : forall a b M : Q, QltT 0 M -> QleT' (a * M) (b * M) -> QleT' a b.
Proof.
  intros a b M HM H.
  apply Qle_to_QleT'.
  assert (HM' : Qlt 0 M) by (apply QltT_to_Qlt; exact HM).
  assert (H' : Qle (a * M) (b * M)) by (apply QleT'_to_Qle; exact H).
  destruct (Qlt_le_dec b a) as [Hlt | Hle].
  - exfalso.
    assert (Hlt2 : Qlt (b * M) (a * M))
      by (apply (Qmult_lt_compat_r b a M); [exact HM' | exact Hlt]).
    exact (Qlt_irrefl (b * M) (Qlt_le_trans (b * M) (a * M) (b * M) Hlt2 H')).
  - exact Hle.
Qed.

(* |x| <= c from the two side bounds (0 <= c). *)
Lemma abl13_qabs_le : forall x c : Q,
  QleT' 0 c -> QleT' (- c) x -> QleT' x c -> QleT' (Qabs x) c.
Proof.
  intros x c Hc0 Hlo Hhi.
  apply Qle_to_QleT'.
  assert (Hc0' : Qle 0 c) by (apply QleT'_to_Qle; exact Hc0).
  assert (Hlo' : Qle (- c) x) by (apply QleT'_to_Qle; exact Hlo).
  assert (Hhi' : Qle x c) by (apply QleT'_to_Qle; exact Hhi).
  destruct (Qlt_le_dec 0 x) as [Hpos | Hnonpos].
  - rewrite (Qabs_pos x (Qlt_le_weak 0 x Hpos)). exact Hhi'.
  - assert (Hnx : Qle 0 (- x)).
    { assert (H := Qopp_le_compat x 0 Hnonpos).
      assert (Hz : - 0 == 0) by ring.
      rewrite Hz in H. exact H. }
    rewrite <- (Qabs_opp x).
    rewrite (Qabs_pos (- x) Hnx).
    assert (Hc : Qle (- x) c).
    { assert (H := Qopp_le_compat (- c) x Hlo').
      assert (Hr : - (- c) == c) by ring.
      rewrite Hr in H. exact H. }
    exact Hc.
Qed.

(* |x| < d implies -d < x. *)
Lemma abl13_qabs_lt_opp : forall x d : Q, QltT (Qabs x) d -> QltT (- d) x.
Proof.
  intros x d H.
  apply Qlt_to_QltT.
  assert (H' : Qlt (Qabs x) d) by (apply QltT_to_Qlt; exact H).
  assert (Hle : Qle (- x) (Qabs x)).
  { rewrite <- (Qabs_opp x). apply Qle_Qabs. }
  assert (Hlt : Qlt (- x) d)
    by (apply (Qle_lt_trans (- x) (Qabs x) d); [exact Hle | exact H']).
  assert (Hr : - (- x) == x) by ring.
  rewrite <- Hr.
  apply (Qopp_lt_compat (- x) d Hlt).
Qed.

(* Nonpositive right-summand cancellation: z <= 0 implies x + z <= x.
   (Four-explicit-argument Qplus_le_compat + ring elimination of +0. A bare
   apply of Qplus_le_compat with RHS = cos_partial (2*S m') t makes the
   unifier expose the index head reduction and wrongly decompose the RHS;
   with this helper the conclusion shape ?x + ?z <= ?x has a bare variable
   on the right, so the decomposition trap is structurally excluded.) *)
Lemma abl13_qplus_nonpos_le : forall x z : Q, QleT' z 0 -> QleT' (x + z) x.
Proof.
  intros x z Hz.
  apply Qle_to_QleT'.
  assert (Hz' : Qle z 0) by (apply QleT'_to_Qle; exact Hz).
  assert (H0 : x + 0 == x) by ring.
  apply (Qle_trans _ (x + 0) _).
  - apply (Qplus_le_compat x x z 0); [apply Qle_refl | exact Hz'].
  - rewrite H0. apply Qle_refl.
Qed.

(* Even/odd powers of (-1) (S-shaped index, for cos_term sign rewriting). *)
Lemma abl13_qpow_neg1_S2 : forall n : nat,
  QeqT (q_pow (-1) (Datatypes.S (Datatypes.S n))) (q_pow (-1) n).
Proof.
  intro n. apply qeq_imp_qeqT. cbn [q_pow]. ring.
Qed.

Lemma abl13_qpow_neg1_even : forall m : nat, QeqT (q_pow (-1) (2 * m)) 1.
Proof.
  intro m. induction m as [| m IH].
  - apply qeq_imp_qeqT. reflexivity.
  - apply qeq_imp_qeqT.
    replace (2 * (Datatypes.S m))%nat
      with (Datatypes.S (Datatypes.S (2 * m)))%nat by lia.
    assert (HS2 : q_pow (-1) (Datatypes.S (Datatypes.S (2 * m))) == q_pow (-1) (2 * m)).
    { apply qeqT_imp_qeq. apply abl13_qpow_neg1_S2. }
    rewrite HS2. apply qeqT_imp_qeq. exact IH.
Qed.

Lemma abl13_qpow_neg1_odd : forall m : nat,
  QeqT (q_pow (-1) (Datatypes.S (2 * m))) (-1)%Q.
Proof.
  intro m. induction m as [| m IH].
  - apply qeq_imp_qeqT.
    replace (Datatypes.S (2 * 0))%nat with (Datatypes.S 0)%nat by lia.
    cbn [q_pow]. ring.
  - apply qeq_imp_qeqT.
    replace (Datatypes.S (2 * (Datatypes.S m)))%nat
      with (Datatypes.S (Datatypes.S (Datatypes.S (2 * m))))%nat by lia.
    assert (HS2 : q_pow (-1) (Datatypes.S (Datatypes.S (Datatypes.S (2 * m))))
                  == q_pow (-1) (Datatypes.S (2 * m))).
    { apply qeqT_imp_qeq. apply abl13_qpow_neg1_S2. }
    rewrite HS2. apply qeqT_imp_qeq. exact IH.
Qed.

(* Even-exponent power absolute-value identity: t^{2k} == |t|^{2k}
   (via Qabs + even power nonneg). *)
Lemma abl13_qpow_even_abs : forall (k : nat) (t : Q),
  QeqT (q_pow t (2 * k)) (q_pow (Qabs t) (2 * k)).
Proof.
  intros k t. apply qeq_imp_qeqT.
  assert (Hpos : Qle 0 (q_pow t (2 * k))).
  { induction k as [| k IHk].
    - replace (2 * 0)%nat with 0%nat by lia. cbn [q_pow]. unfold Qle; simpl; lia.
    - replace (2 * (Datatypes.S k))%nat
        with (Datatypes.S (Datatypes.S (2 * k)))%nat by lia.
      cbn [q_pow].
      assert (Hr : t * (t * q_pow t (2 * k)) == (t * t) * q_pow t (2 * k)) by ring.
      rewrite Hr.
      apply (Qmult_le_0_compat (t * t) (q_pow t (2 * k))).
      + apply QleT'_to_Qle. apply abl13_qsq_nonneg.
      + exact IHk. }
  assert (H1 : q_pow t (2 * k) == Qabs (q_pow t (2 * k))).
  { symmetry. apply Qabs_pos. exact Hpos. }
  assert (H2 : Qabs (q_pow t (2 * k)) == q_pow (Qabs t) (2 * k)).
  { rewrite (qeqT_imp_qeq _ _ (q_pow_abs t (2 * k))). reflexivity. }
  rewrite H1. rewrite H2. reflexivity.
Qed.

(* Series term absolute-value shape: a_j(t) := |t|^{2j}/(2j)!. *)
Definition abl13_a (j : nat) (t : Q) : Q := q_pow (Qabs t) (2 * j) / q_fact (2 * j).

Lemma abl13_a_nonneg : forall j t, QleT' 0 (abl13_a j t).
Proof.
  intros j t. unfold abl13_a. apply q_pow_fact_nonneg.
  apply Qle_to_QleT'. apply Qabs_nonneg.
Qed.

(* q_fact nonzero at literal Z-Q shapes (field-side condition stocking). *)
Lemma abl13_qfact_neq0 : forall k : nat, Not (QeqT (q_fact k) 0).
Proof.
  intros k Heq.
  destruct (Qlt_not_eq 0 (q_fact k)
             (QltT_to_Qlt 0 (q_fact k) (q_fact_pos k))
             (Qeq_sym (q_fact k) 0 (qeqT_imp_qeq (q_fact k) 0 Heq))).
Qed.

Lemma abl13_zQ_neq0 : forall k : nat, Not (QeqT (Z.of_nat (Datatypes.S k) # 1) 0).
Proof.
  intros k Heq.
  assert (H : Qlt 0 ((Z.of_nat (Datatypes.S k) # 1))).
  { unfold Qlt. simpl. lia. }
  rewrite (qeqT_imp_qeq _ _ Heq) in H.
  exact (False_rect Empty_set (Qlt_irrefl 0 H)).
Qed.

(* Division cancellation: X/D*D == X (D != 0; Qdiv unfolding + Qmult_inv_r +
   ring rearrangement, field-free). *)
Lemma abl13_qdiv_cancel : forall X D : Q, Not (QeqT D 0) -> QeqT ((X / D) * D) X.
Proof.
  intros X D HD.
  apply qeq_imp_qeqT.
  assert (HD' : ~ (D == 0)).
  { intro Hdeq. destruct (HD (qeq_imp_qeqT D 0 Hdeq)). }
  unfold Qdiv.
  rewrite <- Qmult_assoc.
  assert (Hinv : Qinv D * D == 1).
  { rewrite (Qmult_comm (Qinv D) D). apply Qmult_inv_r. exact HD'. }
  rewrite Hinv.
  rewrite Qmult_1_r.
  reflexivity.
Qed.

(* Nonneg base power. *)
Lemma abl13_qpow_nonneg : forall (k : nat) (A : Q), QleT' 0 A -> QleT' 0 (q_pow A k).
Proof.
  intros k A H.
  apply Qle_to_QleT'.
  assert (H' : Qle 0 A) by (apply QleT'_to_Qle; exact H).
  induction k as [| k IH].
  - cbn [q_pow]. unfold Qle; simpl; lia.
  - cbn [q_pow]. apply (Qmult_le_0_compat A (q_pow A k)); [exact H' | exact IH].
Qed.

(* Term decrease: j >= 2 and t^2 <= 49/4 imply a(S j) <= a j.
   (Ratio a(S j)/a j == t^2/((2j+1)(2j+2)) <= (49/4)/30 < 1; the closing walk
   uses the division-cancellation lemma — Qdiv unfolding + Qmult_inv_r + ring
   rearrangement, field-free throughout.) *)
Lemma abl13_a_decr : forall (j : nat) (t : Q), NatLe 2 j -> QleT' (t * t) (49 / 4) ->
  QleT' (abl13_a (Datatypes.S j) t) (abl13_a j t).
Proof.
  intros j t Hj Htt.
  assert (Hj' : (2 <= j)%nat) by (apply NatLe_drop; exact Hj).
  assert (Htt' : Qle (t * t) (49 / 4)) by (apply QleT'_to_Qle; exact Htt).
  assert (HA : t * t == Qabs t * Qabs t) by (apply qeqT_imp_qeq; apply abl13_qsq_abs).
  (* The two new factors (Q shape): Z1 := 2j+1 >= 5 and Z2 := 2j+2 >= 6 (j >= 2). *)
  assert (Hb1 : Qle 5 ((Z.of_nat (Datatypes.S (2 * j)) # 1))).
  { unfold Qle. simpl. lia. }
  assert (Hb2 : Qle 6 ((Z.of_nat (Datatypes.S (Datatypes.S (2 * j))) # 1))).
  { unfold Qle. simpl. lia. }
  assert (Hb3 : Qle 30 ((Z.of_nat (Datatypes.S (2 * j)) # 1)
                        * (Z.of_nat (Datatypes.S (Datatypes.S (2 * j))) # 1))).
  { apply (Qle_trans 30 (6 * (Z.of_nat (Datatypes.S (2 * j)) # 1)) _).
    - unfold Qle. simpl. lia.
    - assert (Hr : (Z.of_nat (Datatypes.S (Datatypes.S (2 * j))) # 1)
                   * (Z.of_nat (Datatypes.S (2 * j)) # 1) ==
                   (Z.of_nat (Datatypes.S (2 * j)) # 1)
                   * (Z.of_nat (Datatypes.S (Datatypes.S (2 * j))) # 1)) by ring.
      rewrite <- Hr.
      apply (Qmult_le_compat_r 6 (Z.of_nat (Datatypes.S (Datatypes.S (2 * j))) # 1)
                                 (Z.of_nat (Datatypes.S (2 * j)) # 1)).
      + exact Hb2.
      + unfold Qle. simpl. lia. }
  assert (Hbridge : Qle (Qabs t * Qabs t)
                        ((Z.of_nat (Datatypes.S (2 * j)) # 1)
                         * (Z.of_nat (Datatypes.S (Datatypes.S (2 * j))) # 1))).
  { apply (Qle_trans _ (49 / 4) _).
    - rewrite <- HA. exact Htt'.
    - apply (Qle_trans _ 30 _).
      + unfold Qle, Qdiv. simpl. lia.
      + exact Hb3. }
  (* The exact divisor D' := Z2*(Z1*D0) and its positivity. *)
  assert (Hz2pos : Qlt 0 ((Z.of_nat (Datatypes.S (Datatypes.S (2 * j))) # 1))).
  { apply (Qlt_le_trans 0 6 _); [unfold Qlt; simpl; lia | exact Hb2]. }
  assert (Hz1D0pos : Qlt 0 ((Z.of_nat (Datatypes.S (2 * j)) # 1) * q_fact (2 * j))).
  { apply (Qmult_lt_0_compat _ _).
    - apply (Qlt_le_trans 0 5 _); [unfold Qlt; simpl; lia | exact Hb1].
    - apply (QltT_to_Qlt 0 (q_fact (2 * j))). apply q_fact_pos. }
  assert (HDpos : Qlt 0 ((Z.of_nat (Datatypes.S (Datatypes.S (2 * j))) # 1) *
                         ((Z.of_nat (Datatypes.S (2 * j)) # 1) * q_fact (2 * j)))).
  { apply (Qmult_lt_0_compat _ _ Hz2pos Hz1D0pos). }
  (* The cbn-expanded shape of a(S j). *)
  assert (Hexpand : abl13_a (Datatypes.S j) t ==
                    (Qabs t * (Qabs t * q_pow (Qabs t) (2 * j))) /
                    ((Z.of_nat (Datatypes.S (Datatypes.S (2 * j))) # 1) *
                     ((Z.of_nat (Datatypes.S (2 * j)) # 1) * q_fact (2 * j)))).
  { unfold abl13_a.
    replace (2 * (Datatypes.S j))%nat
      with (Datatypes.S (Datatypes.S (2 * j)))%nat by lia.
    cbn [q_pow q_fact]. reflexivity. }
  (* Cancellation one: a(S j)*D' == A^2*P0. *)
  assert (Hcancel1 : abl13_a (Datatypes.S j) t *
                     ((Z.of_nat (Datatypes.S (Datatypes.S (2 * j))) # 1) *
                      ((Z.of_nat (Datatypes.S (2 * j)) # 1) * q_fact (2 * j))) ==
                     (Qabs t * Qabs t) * q_pow (Qabs t) (2 * j)).
  { rewrite Hexpand.
    assert (Hstep : (Qabs t * (Qabs t * q_pow (Qabs t) (2 * j))) /
                    ((Z.of_nat (Datatypes.S (Datatypes.S (2 * j))) # 1) *
                     ((Z.of_nat (Datatypes.S (2 * j)) # 1) * q_fact (2 * j))) *
                    ((Z.of_nat (Datatypes.S (Datatypes.S (2 * j))) # 1) *
                     ((Z.of_nat (Datatypes.S (2 * j)) # 1) * q_fact (2 * j))) ==
                    (Qabs t * (Qabs t * q_pow (Qabs t) (2 * j)))).
    { apply qeqT_imp_qeq. apply abl13_qdiv_cancel.
      exact (q_neq_of_lt _ (Qlt_to_QltT _ _ HDpos)). }
    rewrite Hstep. ring. }
  (* Cancellation two: a j*D' == Z2*Z1*P0. *)
  assert (Hcancel2 : abl13_a j t *
                     ((Z.of_nat (Datatypes.S (Datatypes.S (2 * j))) # 1) *
                      ((Z.of_nat (Datatypes.S (2 * j)) # 1) * q_fact (2 * j))) ==
                    ((Z.of_nat (Datatypes.S (Datatypes.S (2 * j))) # 1) *
                     (Z.of_nat (Datatypes.S (2 * j)) # 1)) * q_pow (Qabs t) (2 * j)).
  { unfold abl13_a. unfold Qdiv.
    assert (Hinv : Qinv (q_fact (2 * j)) * q_fact (2 * j) == 1).
    { rewrite (Qmult_comm (Qinv (q_fact (2 * j))) (q_fact (2 * j))).
      apply Qmult_inv_r. intro Heq0.
      destruct (abl13_qfact_neq0 (2 * j) (qeq_imp_qeqT (q_fact (2 * j)) 0 Heq0)). }
    assert (Hrr : (q_pow (Qabs t) (2 * j) * Qinv (q_fact (2 * j))) *
                  ((Z.of_nat (Datatypes.S (Datatypes.S (2 * j))) # 1) *
                   ((Z.of_nat (Datatypes.S (2 * j)) # 1) * q_fact (2 * j))) ==
                  (((Z.of_nat (Datatypes.S (Datatypes.S (2 * j))) # 1) *
                    (Z.of_nat (Datatypes.S (2 * j)) # 1)) * q_pow (Qabs t) (2 * j)) *
                  (Qinv (q_fact (2 * j)) * q_fact (2 * j))) by ring.
    rewrite Hrr. rewrite Hinv.
    rewrite Qmult_1_r. reflexivity. }
  apply (abl13_qdiv_le (abl13_a (Datatypes.S j) t) (abl13_a j t)
                       ((Z.of_nat (Datatypes.S (Datatypes.S (2 * j))) # 1) *
                        ((Z.of_nat (Datatypes.S (2 * j)) # 1) * q_fact (2 * j)))).
  - apply Qlt_to_QltT. exact HDpos.
  - apply Qle_to_QleT'.
    rewrite Hcancel1. rewrite Hcancel2.
    assert (Hbr : (Z.of_nat (Datatypes.S (Datatypes.S (2 * j))) # 1) *
                  (Z.of_nat (Datatypes.S (2 * j)) # 1) ==
                  (Z.of_nat (Datatypes.S (2 * j)) # 1) *
                  (Z.of_nat (Datatypes.S (Datatypes.S (2 * j))) # 1)) by ring.
    rewrite Hbr.
    apply (Qmult_le_compat_r (Qabs t * Qabs t)
            ((Z.of_nat (Datatypes.S (2 * j)) # 1)
             * (Z.of_nat (Datatypes.S (Datatypes.S (2 * j))) # 1))
            (q_pow (Qabs t) (2 * j))).
    + exact Hbridge.
    + apply QleT'_to_Qle. apply abl13_qpow_nonneg.
      apply Qle_to_QleT'. apply Qabs_nonneg.
Qed.

(* ============================================================ *)
(* Part 2 · S4 envelope: k >= 4 and t^2 <= 49/4 imply            *)
(* cos_partial k t <= cos_partial 4 t                            *)
(* ============================================================ *)

(* Even-index induction: cos_partial (2m) <= cos_partial 4 (m >= 2). *)
Lemma abl13_cp_even_le : forall (m : nat) (t : Q), NatLe 2 m -> QleT' (t * t) (49 / 4) ->
  QleT' (cos_partial (2 * m) t) (cos_partial 4 t).
Proof.
  intros m t. induction m as [| m IH]; intros Hm Htt.
  - exfalso. apply NatLe_drop in Hm. lia.
  - apply Qle_to_QleT'.
    assert (Htt' : Qle (t * t) (49 / 4)) by (apply QleT'_to_Qle; exact Htt).
    destruct m as [| m'].
    + exfalso. apply NatLe_drop in Hm. lia.
    + assert (Hunfold : cos_partial (2 * Datatypes.S (Datatypes.S m')) t ==
                        (cos_partial (2 * Datatypes.S m') t
                         + cos_term (Datatypes.S (2 * Datatypes.S m')) t)
                        + cos_term (Datatypes.S (Datatypes.S (2 * Datatypes.S m'))) t).
      { replace (2 * Datatypes.S (Datatypes.S m'))%nat
          with (Datatypes.S (Datatypes.S (2 * Datatypes.S m')))%nat by lia.
        cbn [cos_partial]. reflexivity. }
      rewrite Hunfold.
      assert (Hc1 : cos_term (Datatypes.S (2 * Datatypes.S m')) t
                    == - abl13_a (Datatypes.S (2 * Datatypes.S m')) t).
      { unfold cos_term, abl13_a.
        rewrite (qeqT_imp_qeq _ _ (abl13_qpow_neg1_odd (Datatypes.S m'))).
        rewrite (qeqT_imp_qeq _ _ (abl13_qpow_even_abs (Datatypes.S (2 * Datatypes.S m')) t)).
        ring. }
      assert (Hc2 : cos_term (Datatypes.S (Datatypes.S (2 * Datatypes.S m'))) t
                    == abl13_a (Datatypes.S (Datatypes.S (2 * Datatypes.S m'))) t).
      { unfold cos_term, abl13_a.
        rewrite (qeqT_imp_qeq _ _ (abl13_qpow_neg1_S2 (2 * Datatypes.S m'))).
        rewrite (qeqT_imp_qeq _ _ (abl13_qpow_neg1_even (Datatypes.S m'))).
        rewrite (qeqT_imp_qeq _ _ (abl13_qpow_even_abs (Datatypes.S (Datatypes.S (2 * Datatypes.S m'))) t)).
        ring. }
      rewrite Hc1, Hc2.
      assert (Hneg : Qle (- abl13_a (Datatypes.S (2 * Datatypes.S m')) t
                          + abl13_a (Datatypes.S (Datatypes.S (2 * Datatypes.S m'))) t) 0).
      { assert (Hr : - abl13_a (Datatypes.S (2 * Datatypes.S m')) t
                     + abl13_a (Datatypes.S (Datatypes.S (2 * Datatypes.S m'))) t ==
                     - (abl13_a (Datatypes.S (2 * Datatypes.S m')) t
                        - abl13_a (Datatypes.S (Datatypes.S (2 * Datatypes.S m'))) t)) by ring.
        rewrite Hr.
        assert (Hz : - 0 == 0) by ring.
        rewrite <- Hz.
        apply (Qopp_le_compat 0 (abl13_a (Datatypes.S (2 * Datatypes.S m')) t -
                                 abl13_a (Datatypes.S (Datatypes.S (2 * Datatypes.S m'))) t)).
        apply (proj1 (Qle_minus_iff (abl13_a (Datatypes.S (Datatypes.S (2 * Datatypes.S m'))) t)
                                    (abl13_a (Datatypes.S (2 * Datatypes.S m')) t))).
        assert (Hdec : QleT' (abl13_a (Datatypes.S (Datatypes.S (2 * Datatypes.S m'))) t)
                             (abl13_a (Datatypes.S (2 * Datatypes.S m')) t)).
        { apply (abl13_a_decr (Datatypes.S (2 * Datatypes.S m')) t).
          - apply NatLe_lift. lia.
          - exact Htt. }
        exact (QleT'_to_Qle _ _ Hdec). }
      assert (Hrr : (cos_partial (2 * Datatypes.S m') t
                     + (- abl13_a (Datatypes.S (2 * Datatypes.S m')) t))
                    + abl13_a (Datatypes.S (Datatypes.S (2 * Datatypes.S m'))) t ==
                    cos_partial (2 * Datatypes.S m') t
                    + ((- abl13_a (Datatypes.S (2 * Datatypes.S m')) t)
                       + abl13_a (Datatypes.S (Datatypes.S (2 * Datatypes.S m'))) t)) by ring.
      rewrite Hrr.
      destruct m' as [| m''].
      * (* For m' = 0 (original m = 2) the IH premise 2 <= S 0 is false (lia
           decides), and the Qle_trans branch cp 2 <= cp 4 is mathematically
           false (t^2 <= 49/4 < 56 implies cp4 < cp2) — the base-case main
           goal closes by reflexivity: cp4 = cp2 + (-a3 + a4) is term-wise
           identical to the LHS. Note: the concrete-exponent rewrites need
           explicit instances (evars under a mul head are not solved). *)
        (* X13 R7 fix: normalize the long-exponent word faces on the LHS to
           the 3/4 short forms first (replace by reflexivity), sparing
           Qle_refl the word-face mismatch; Q addition associativity is not
           conversion-passable, so re-align parentheses via Hrb. *)
        replace (abl13_a (Datatypes.S (2 * Datatypes.S 0)) t)
          with (abl13_a 3 t) by reflexivity.
        replace (abl13_a (Datatypes.S (Datatypes.S (2 * Datatypes.S 0))) t)
          with (abl13_a 4 t) by reflexivity.
        assert (Hcp4 : cos_partial 4 t ==
                       (cos_partial (2 * Datatypes.S 0) t + cos_term 3 t)
                       + cos_term 4 t)
          by (cbn [cos_partial]; reflexivity).
        assert (Hc3 : cos_term 3 t == - abl13_a 3 t).
        { unfold cos_term, abl13_a.
          rewrite (qeqT_imp_qeq _ _ (abl13_qpow_neg1_odd 1)).
          rewrite (qeqT_imp_qeq _ _ (abl13_qpow_even_abs 3 t)).
          ring. }
        assert (Hc4 : cos_term 4 t == abl13_a 4 t).
        { unfold cos_term, abl13_a.
          rewrite (qeqT_imp_qeq _ _ (abl13_qpow_neg1_even 2)).
          rewrite (qeqT_imp_qeq _ _ (abl13_qpow_even_abs 4 t)).
          ring. }
        rewrite Hcp4. rewrite Hc3, Hc4.
        assert (Hrb : (cos_partial (2 * Datatypes.S 0) t + (- abl13_a 3 t))
                      + abl13_a 4 t
                      == cos_partial (2 * Datatypes.S 0) t
                         + (- abl13_a 3 t + abl13_a 4 t)) by ring.
        rewrite Hrb.
        apply Qle_refl.
      * apply (Qle_trans _ (cos_partial (2 * Datatypes.S (Datatypes.S m'')) t) _).
        -- exact (QleT'_to_Qle _ _
                    (abl13_qplus_nonpos_le _ _ (Qle_to_QleT' _ _ Hneg))).
        -- assert (HIH : QleT' (cos_partial (2 * Datatypes.S (Datatypes.S m'')) t)
                               (cos_partial 4 t)).
           { apply IH; [apply NatLe_lift; lia | exact Htt]. }
           exact (QleT'_to_Qle _ _ HIH).
Qed.

(* S4 envelope main lemma: k >= 4 and t^2 <= 49/4 imply
   cos_partial k t <= cos_partial 4 t
   (even k goes directly through the even induction; odd k = 2m+1 has last
   term -a(2m+1) <= 0 and then hangs the even induction). *)
Lemma abl13_cp_le_s4 : forall (k : nat) (t : Q), NatLe 4 k -> QleT' (t * t) (49 / 4) ->
  QleT' (cos_partial k t) (cos_partial 4 t).
Proof.
  intros k t Hk Htt.
  apply Qle_to_QleT'.
  assert (Hk' : (4 <= k)%nat) by (apply NatLe_drop; exact Hk).
  destruct (Nat.Even_or_Odd k) as [[m Hm] | [m Hm]].
  - subst k. assert (Hm2 : NatLe 2 m) by (apply NatLe_lift; lia).
    exact (QleT'_to_Qle _ _ (abl13_cp_even_le m t Hm2 Htt)).
  - subst k. assert (Hm2 : NatLe 2 m) by (apply NatLe_lift; lia).
    replace (2 * m + 1)%nat with (Datatypes.S (2 * m))%nat by lia.
    cbn [cos_partial].
    assert (Hc : cos_term (Datatypes.S (2 * m)) t == - abl13_a (Datatypes.S (2 * m)) t).
    { unfold cos_term, abl13_a.
      rewrite (qeqT_imp_qeq _ _ (abl13_qpow_neg1_odd m)).
      rewrite (qeqT_imp_qeq _ _ (abl13_qpow_even_abs (Datatypes.S (2 * m)) t)).
      ring. }
    rewrite Hc.
    assert (Hneg : Qle (- abl13_a (Datatypes.S (2 * m)) t) 0).
    { assert (H := Qopp_le_compat 0 (abl13_a (Datatypes.S (2 * m)) t)
                    (QleT'_to_Qle _ _ (abl13_a_nonneg (Datatypes.S (2 * m)) t))).
      assert (Hz : - 0 == 0) by ring.
      rewrite Hz in H. exact H. }
    apply (Qle_trans _ (cos_partial (2 * m) t) _).
    + exact (QleT'_to_Qle _ _
              (abl13_qplus_nonpos_le _ _ (Qle_to_QleT' _ _ Hneg))).
    + exact (QleT'_to_Qle _ _ (abl13_cp_even_le m t Hm2 Htt)).
Qed.

(* ============================================================ *)
(* Part 3 · S4 anchor: 2 <= t <= 7/2 implies cos_partial 4 t     *)
(*   <= -2/5. Substitute s := t^2-4 in [0,33/4];                 *)
(*   cos_partial 4 t + 2/5 == (s^4-40s^3+1104s^2-9152s-640)/40320; *)
(*   the two dominating pairs s^3(s-40) <= 0 and s(1104s-9152)   *)
(*   <= 0 give numerator <= -640 < 0.                            *)
(* ============================================================ *)

(* In-window square bound: 2 <= t <= 7/2 implies t^2 <= 49/4. *)
Lemma abl13_sq_window : forall t : Q,
  QleT' 2 t -> QleT' t (7 / 2) -> QleT' (t * t) (49 / 4).
Proof.
  intros t Ht2 Ht72.
  apply Qle_to_QleT'.
  assert (Ht2' : Qle 2 t) by (apply QleT'_to_Qle; exact Ht2).
  assert (Ht72' : Qle t (7 / 2)) by (apply QleT'_to_Qle; exact Ht72).
  assert (Ht0 : Qle 0 t).
  { apply (Qle_trans 0 2 t); [unfold Qle; simpl; lia | exact Ht2']. }
  assert (Hc : (7 / 2) * t == t * (7 / 2)) by ring.
  assert (Hv : (7 / 2) * (7 / 2) == 49 / 4) by (unfold Qdiv; field; unfold Qeq; simpl; lia).
  apply (Qle_trans _ ((7 / 2) * (7 / 2)) _).
  - apply (Qle_trans _ ((7 / 2) * t) _).
    + apply (Qmult_le_compat_r t (7 / 2) t); [exact Ht72' | exact Ht0].
    + rewrite Hc. apply (Qmult_le_compat_r t (7 / 2) (7 / 2));
        [exact Ht72' | unfold Qle, Qdiv; simpl; lia].
  - rewrite Hv. apply Qle_refl.
Qed.

(* cos_partial 4 t == 1 - t^2/2 + t^4/24 - t^6/720 + t^8/40320 ((t*t) atomic
   shape, for the substitution rewriting). *)
Lemma abl13_cp4_G : forall t : Q,
  QeqT (cos_partial 4 t)
       (1 - (t * t) / 2 + (t * t) * (t * t) / 24
          - (t * t) * (t * t) * (t * t) / 720
          + (t * t) * (t * t) * (t * t) * (t * t) / 40320).
Proof.
  intro t. apply qeq_imp_qeqT.
  (* cos_term has no match structure; a restricted cbn and even a full cbn
     both refuse to unfold ("no progress with a constructor head", reported
     in two rounds as "not a valid field equation") — first cbn
     [cos_partial] to spread the sum, then unfold cos_term to force the
     expansion, then cbn to reduce the numeric coefficients, and finally
     field closes. *)
  cbn [cos_partial]. unfold cos_term. cbn.
  field; unfold Qeq; simpl; lia.
Qed.

(* The G(u) + 2/5 substitution domination identity (pure field). *)
Lemma abl13_G_P : forall u : Q,
  QeqT (1 - u / 2 + u * u / 24 - u * u * u / 720 + u * u * u * u / 40320 + 2 / 5)
       (((u - 4) * (u - 4) * (u - 4) * (u - 4)
         - 40 * ((u - 4) * (u - 4) * (u - 4))
         + 1104 * ((u - 4) * (u - 4))
         - 9152 * (u - 4) - 640) * (1 / 40320)).
Proof.
  intro u. apply qeq_imp_qeqT. unfold Qdiv. field; unfold Qeq; simpl; lia.
Qed.

Lemma abl13_cp4_le_neg25 : forall t : Q,
  QleT' 2 t -> QleT' t (7 / 2) -> QleT' (cos_partial 4 t) (- (2 / 5)).
Proof.
  intros t Ht2 Ht72.
  apply Qle_to_QleT'.
  assert (Ht2' : Qle 2 t) by (apply QleT'_to_Qle; exact Ht2).
  assert (Ht72' : Qle t (7 / 2)) by (apply QleT'_to_Qle; exact Ht72).
  assert (Hsq : Qle 4 (t * t)).
  { apply (Qle_trans _ (2 * t) _).
    - (* Q multiplication is not conversion-passable: the 2*t and t*2 word
         faces must be normalized before feeding _r (the original
         Qmult_le_compat_r 2 t 2 concluded 2*2 <= t*2, mismatching the goal
         4 <= 2*t). *)
      assert (Hc : t * 2 == 2 * t) by ring.
      rewrite <- Hc.
      replace 4 with (2 * 2) by reflexivity.
      apply (Qmult_le_compat_r 2 t 2); [exact Ht2' | unfold Qle; simpl; lia].
    - apply (Qmult_le_compat_r 2 t t);
        [exact Ht2' | apply (Qle_trans 0 2 t); [unfold Qle; simpl; lia | exact Ht2']]. }
  assert (Htt : Qle (t * t) (49 / 4)).
  { exact (QleT'_to_Qle _ _ (abl13_sq_window t Ht2 Ht72)). }
  remember (t * t - 4) as s eqn:Hsdef.
  assert (Hs4 : t * t == s + 4) by (rewrite Hsdef; ring).
  assert (Hs0 : Qle 0 s) by (rewrite Hsdef; apply (proj1 (Qle_minus_iff 4 (t * t))); exact Hsq).
  assert (Hs33 : Qle s (33 / 4)).
  { rewrite Hsdef.
    apply (Qle_trans _ (49 / 4 - 4) _).
    - apply (Qplus_le_compat (t * t) (49 / 4) (- 4) (- 4)); [exact Htt | apply Qle_refl].
    - assert (Hr : 49 / 4 - 4 == 33 / 4) by (unfold Qdiv; field; unfold Qeq; simpl; lia).
      rewrite Hr. apply Qle_refl. }
  assert (HG : cos_partial 4 t ==
               1 - (s + 4) / 2 + (s + 4) * (s + 4) / 24
                 - (s + 4) * (s + 4) * (s + 4) / 720
                 + (s + 4) * (s + 4) * (s + 4) * (s + 4) / 40320).
  { rewrite (qeqT_imp_qeq _ _ (abl13_cp4_G t)). rewrite Hs4. reflexivity. }
  assert (Hexp : cos_partial 4 t + 2 / 5 ==
                 ((s * s * s * s - 40 * (s * s * s) + 1104 * (s * s) - 9152 * s - 640))
                 * (1 / 40320)).
  { rewrite HG. rewrite (qeqT_imp_qeq _ _ (abl13_G_P (s + 4))).
    (* The rewriting leftover (s+4-4) differs word-wise from s (Q subtraction
       is not conversion-passable, reflexivity fails) — ring's polynomial
       normalization closes. *)
    ring. }
  (* Domination one: s^4 - 40s^3 == s^3(s-40) <= 0 (0 <= s <= 33/4 < 40). *)
  assert (Hd1 : Qle (s * s * s * s - 40 * (s * s * s)) 0).
  { assert (Hs3 : Qle 0 (s * s * s)).
    { apply (Qmult_le_0_compat (s * s) s).
      - apply (Qmult_le_0_compat s s); exact Hs0.
      - exact Hs0. }
    (* The original Hs40 block (proj1 (Qle_minus_iff s 40) concluded
       0 <= 40 + s^- misaligned against the goal s - 40 <= 0; apply was
       bound to fail) is removed wholesale — its only consumer Hpos has been
       changed to prove 0 <= 40 - s via proj1 directly, no longer depending
       on Hs40. *)
    assert (Hr : s * s * s * s - 40 * (s * s * s) == (s * s * s) * (s - 40)) by ring.
    rewrite Hr.
    assert (Hpos : Qle 0 ((s * s * s) * (40 - s))).
    { apply (Qmult_le_0_compat (s * s * s) (40 - s)).
      - exact Hs3.
      - (* proj2 (Qle_minus_iff (s-40) 0) concludes s - 40 <= 0, misaligned
           with this goal 0 <= 40 - s — use proj1 to prove 0 <= 40 - s
           directly (from s <= 33/4 <= 40). *)
        apply (proj1 (Qle_minus_iff s 40)).
        apply (Qle_trans s (33 / 4) 40); [exact Hs33 | unfold Qle, Qdiv; simpl; lia]. }
    assert (Hneg0 := Qopp_le_compat 0 ((s * s * s) * (40 - s)) Hpos).
    assert (Hz : - 0 == 0) by ring.
    rewrite Hz in Hneg0.
    assert (Hr2 : - ((s * s * s) * (40 - s)) == (s * s * s) * (s - 40)) by ring.
    rewrite Hr2 in Hneg0. exact Hneg0. }
  (* Domination two: 1104s^2 - 9152s == s(1104s-9152) <= 0
     (1104 * (33/4) == 9108 < 9152). *)
  assert (Hd2 : Qle (1104 * (s * s) - 9152 * s) 0).
  { assert (Hb : Qle (1104 * s) 9108).
    { assert (H := Qmult_le_compat_r s (33 / 4) 1104 Hs33).
      assert (Hv : (33 / 4) * 1104 == 9108) by (unfold Qdiv; field; unfold Qeq; simpl; lia).
      assert (Hc : 1104 * s == s * 1104) by ring.
      rewrite <- Hc in H. rewrite Hv in H.
      (* The second premise 0 <= 1104 of Qmult_le_compat_r was unfed; H was
         an unapplied arrow (exact fails directly) — feed it and close. *)
      apply H.
      apply Qlt_le_weak. change (Qlt 0 1104). compute. reflexivity. }
    assert (Hlt : Qle (1104 * s) 9152).
    { apply (Qle_trans (1104 * s) 9108 9152);
        [exact Hb | apply Qlt_le_weak; unfold Qlt; simpl; lia]. }
    assert (Hinner : Qle 0 (9152 - 1104 * s)).
    { (* (Same-round static mine-clearing): Hm is exactly 0 <= 9152 + -(1104s),
         differing from the goal 0 <= 9152 - 1104s only in the Qminus word
         face (conversion-passable) — the original Qopp_le_compat step had a
         premise misalignment (Hm's type 0 <= 9152 - 1104s was misused as
         1104s - 9152 <= 0; the lexical application is bound to mistype) and
         the whole segment is removed. *)
      exact (proj1 (Qle_minus_iff (1104 * s) 9152) Hlt). }
    assert (Hr : 1104 * (s * s) - 9152 * s == s * (1104 * s - 9152)) by ring.
    rewrite Hr.
    assert (Hpos : Qle 0 (s * (9152 - 1104 * s))).
    { apply (Qmult_le_0_compat s (9152 - 1104 * s)); [exact Hs0 | exact Hinner]. }
    assert (Hneg0 := Qopp_le_compat 0 (s * (9152 - 1104 * s)) Hpos).
    assert (Hz : - 0 == 0) by ring.
    rewrite Hz in Hneg0.
    assert (Hr2 : - (s * (9152 - 1104 * s)) == s * (1104 * s - 9152)) by ring.
    rewrite Hr2 in Hneg0. exact Hneg0. }
  (* Numerator <= -640. *)
  assert (HPle : Qle (s * s * s * s - 40 * (s * s * s) + 1104 * (s * s) - 9152 * s - 640)
                     (- 640)).
  { assert (Hsum : s * s * s * s - 40 * (s * s * s) + 1104 * (s * s) - 9152 * s - 640 ==
                   ((s * s * s * s - 40 * (s * s * s)) + (1104 * (s * s) - 9152 * s))
                   + (- 640)) by ring.
    rewrite Hsum.
    apply (Qle_trans _ (0 + 0 + (- 640)) _).
    - apply Qplus_le_compat.
      + apply Qplus_le_compat; [exact Hd1 | exact Hd2].
      + apply Qle_refl.
    - assert (Hn : 0 + 0 + (- 640) == - 640) by ring.
      rewrite Hn. apply Qle_refl. }
  (* Assembly: cos_partial 4 t + 2/5 <= 0 implies cos_partial 4 t <= -2/5. *)
  assert (Hfin : Qle (cos_partial 4 t + 2 / 5) 0).
  { rewrite Hexp.
    apply (Qle_trans _ ((- 640) * (1 / 40320)) _).
    - apply (Qmult_le_compat_r _ _ (1 / 40320)).
      + exact HPle.
      + apply Qlt_le_weak. change (Qlt 0 (1 / 40320)). compute. reflexivity.
    - apply Qlt_le_weak.
      assert (Hval : (- 640) * (1 / 40320) == - (1 / 63))
        by (unfold Qdiv; field; unfold Qeq; simpl; lia).
      rewrite Hval.
      unfold Qlt. simpl. lia. }
  apply (proj2 (Qle_minus_iff (cos_partial 4 t) (- (2 / 5)))).
  assert (Hr0 : - (2 / 5) - cos_partial 4 t == - (cos_partial 4 t + 2 / 5)) by ring.
  rewrite Hr0.
  assert (Hz : - 0 == 0) by ring.
  rewrite <- Hz.
  apply (Qopp_le_compat (cos_partial 4 t + 2 / 5) 0 Hfin).
Qed.

(* Main anchor: k >= 4 and 2 <= t <= 7/2 imply cos_partial k t <= -2/5. *)
Lemma abl13_cos_partial_neg25 : forall (k : nat) (t : Q), NatLe 4 k ->
  QleT' 2 t -> QleT' t (7 / 2) -> QleT' (cos_partial k t) (- (2 / 5)).
Proof.
  intros k t Hk Ht2 Ht72.
  apply Qle_to_QleT'.
  apply (Qle_trans _ (cos_partial 4 t) _).
  - exact (QleT'_to_Qle _ _ (abl13_cp_le_s4 k t Hk (abl13_sq_window t Ht2 Ht72))).
  - exact (QleT'_to_Qle _ _ (abl13_cp4_le_neg25 t Ht2 Ht72)).
Qed.

(* ============================================================ *)
(* Part 4 · Main theorem: cos zero uniqueness bridge widened to  *)
(*   (3/2, 7/2). Follows the eps assembly of                     *)
(*   cos_pi_half_unique_widened (S10:9465) with the upper        *)
(*   endpoint 2 -> 7/2; the new branch w_n > 2 is closed by the  *)
(*   main anchor -2/5.                                           *)
(* ============================================================ *)

Lemma abl13_cos_pi_half_unique_widened2 : forall (w : Real),
  real_lt (real_const (3 / 2)) w -> real_lt w (real_const (7 / 2)) ->
  real_eq (cauchy_real_cos w) real_zero ->
  real_eq w cos_pi_half.
Proof.
  intros w Hlow Hup Hw0.
  intros eps Heps.
  assert (HepsQ : Qlt 0 eps) by (apply QltT_to_Qlt; exact Heps).
  assert (Heps8 : Qlt 0 (eps / 8)).
  { apply (Qlt_shift_div_l 0 eps 8).
    - change (Qlt 0 8). compute. reflexivity.
    - simpl. exact HepsQ. }
  (* Pointwise bound sources: the w side (endpoints + cos w == 0 diagonal),
     the z side (cos_zero_lower/upper + cos z == 0 diagonal). *)
  destruct (real_lt_lower_pt (3 / 2) w Hlow) as [Nlo HNlo].
  destruct (real_lt_upper_pt (7 / 2) w Hup) as [Nup HNup].
  destruct (cos_eq_zero_diag_bound w Hw0 (eps / 8) Heps8) as [Nwd Hwd].
  destruct (cos_eq_zero_diag_bound cos_pi_half real_cos_pi_half_zero (eps / 8) Heps8) as [Nzd Hzd].
  (* X13 R3 fix: q_pow_arch belongs to the S07_RealSetoidExpLog piece; S10
     only Require Imports it without propagating names, so the bare name is
     not visible — use the qualified name, sparing the whole-piece Import
     with its name-shadowing risk. *)
  destruct (S07_RealSetoidExpLog.q_pow_arch 1 (eps / 8)) as [t Ht].
  { apply Qle_to_QleT'. unfold Qle. simpl. lia. }
  { apply Qlt_to_QltT. exact Heps8. }
  set (A := Nat.max Nlo (Nat.max Nup (Nat.max Nwd Nzd))).
  exists (Nat.max 4 (Nat.max A (Datatypes.S t))).
  intros n Hn.
  apply Qlt_to_QltT.
  (* The branch (b) main anchor abl13_cos_partial_neg25 needs 4 <= n (the S4
     envelope starts at 4 terms); witness lower bound 2 -> 4, Hn4/Hn2 both
     derived (cos_inv_dist_le2 still takes Hn2). *)
  assert (Hn4 : (4 <= n)%nat) by (apply (Nat.le_trans _ (Nat.max 4 (Nat.max A (Datatypes.S t))) _); [apply Nat.le_max_l | exact (NatLe_drop _ _ Hn)]).
  assert (Hn2 : (2 <= n)%nat) by (apply (Nat.le_trans _ 4 _); [lia | exact Hn4]).
  assert (HnAt : (Nat.max A (Datatypes.S t) <= n)%nat) by (apply (Nat.le_trans _ (Nat.max 4 (Nat.max A (Datatypes.S t))) _); [apply Nat.le_max_r | exact (NatLe_drop _ _ Hn)]).
  assert (HnA : (A <= n)%nat) by (apply (Nat.le_trans _ (Nat.max A (Datatypes.S t)) _); [apply Nat.le_max_l | exact HnAt]).
  assert (Hnlo : (Nlo <= n)%nat).
  { apply (Nat.le_trans _ (Nat.max Nlo (Nat.max Nup (Nat.max Nwd Nzd))) _); [apply Nat.le_max_l | ].
    unfold A in HnA. exact HnA. }
  assert (Hnup : (Nup <= n)%nat).
  { apply (Nat.le_trans _ (Nat.max Nup (Nat.max Nwd Nzd)) _); [apply Nat.le_max_l | ].
    apply (Nat.le_trans _ A _); [apply Nat.le_max_r | exact HnA]. }
  assert (Hnwd : (Nwd <= n)%nat).
  { apply (Nat.le_trans _ (Nat.max Nwd Nzd) _); [apply Nat.le_max_l | ].
    apply (Nat.le_trans _ (Nat.max Nup (Nat.max Nwd Nzd)) _); [apply Nat.le_max_r | ].
    apply (Nat.le_trans _ A _); [apply Nat.le_max_r | exact HnA]. }
  assert (Hnzd : (Nzd <= n)%nat).
  { apply (Nat.le_trans _ (Nat.max Nwd Nzd) _); [apply Nat.le_max_r | ].
    apply (Nat.le_trans _ (Nat.max Nup (Nat.max Nwd Nzd)) _); [apply Nat.le_max_r | ].
    apply (Nat.le_trans _ A _); [apply Nat.le_max_r | exact HnA]. }
  (* w_n in (3/2, 7/2) and z_n in (3/2, 5/3) (Q layer). *)
  assert (Hwlo : Qle (3 / 2) (projT1 w n)) by (apply Qlt_le_weak; apply (HNlo n); exact Hnlo).
  assert (Hwup : Qle (projT1 w n) (7 / 2)) by (apply Qlt_le_weak; apply (HNup n); exact Hnup).
  assert (Hzlo : Qle (3 / 2) (cos_zero_seq n))
    by (apply Qlt_le_weak; exact (QltT_to_Qlt _ _ (cos_zero_lower n))).
  assert (Hzup : Qle (cos_zero_seq n) (5 / 3))
    by (apply Qlt_le_weak; exact (QltT_to_Qlt _ _ (cos_zero_upper n))).
  assert (Hzup2 : Qle (cos_zero_seq n) 2).
  { apply (Qle_trans _ (5 / 3) _); [exact Hzup | change (Qle (5 / 3) 2); unfold Qle, Qdiv; simpl; lia]. }
  (* Diagonal bounds of cos w_n and cos z_n, < eps/8. *)
  assert (Hwpt : Qlt (Qabs (projT1 (cauchy_real_cos w) n - projT1 real_zero n)) (eps / 8)).
  { exact (QltT_to_Qlt _ _ (Hwd n Hnwd)). }
  assert (Hzpt : Qlt (Qabs (projT1 (cauchy_real_cos cos_pi_half) n - projT1 real_zero n)) (eps / 8)).
  { exact (QltT_to_Qlt _ _ (Hzd n Hnzd)). }
  (* Pointwise Q decidable branch: w_n <= 2 (reverse-bound assembly) or
     2 < w_n (closed by the main anchor). *)
  destruct (Qlt_le_dec (projT1 w n) 2) as [Hw2 | Hwgt2].
  - (* Branch (a): w_n <= 2 — inherited from the widened form (v <= 2
       reverse bounds). *)
    assert (Hw2le : Qle (projT1 w n) 2) by (apply Qlt_le_weak; exact Hw2).
    destruct (Qlt_le_dec (cos_zero_seq n) (projT1 w n)) as [Hzw | Hwz].
    + (* z_n < w_n: u := z_n, v := w_n. *)
      assert (Hd : Qlt (projT1 w n - cos_zero_seq n) (2 * (eps / 8 + eps / 8))).
      { apply QltT_to_Qlt.
        apply (cos_inv_dist_le2 (cos_zero_seq n) (projT1 w n) (eps / 8) (eps / 8) n).
        - exact Hn2.
        - exact Hzlo.
        - apply Qlt_le_weak. exact Hzw.
        - exact Hw2le.
        - apply (Qle_lt_trans (Qabs (projT1 (cauchy_real_cos (real_const (cos_zero_seq n))) n - projT1 real_zero n))
                              (Qabs (projT1 (cauchy_real_cos cos_pi_half) n - projT1 real_zero n))
                              (eps / 8)).
          + assert (Hp : projT1 (cauchy_real_cos (real_const (cos_zero_seq n))) n ==
                         projT1 (cauchy_real_cos cos_pi_half) n).
            { cbn [projT1 cauchy_real_cos cos_pi_half real_const]. reflexivity. }
            rewrite Hp. apply Qle_refl.
          + exact Hzpt.
        - assert (Hwpt' : Qlt (Qabs (projT1 (cauchy_real_cos (real_const (projT1 w n))) n - projT1 real_zero n)) (eps / 8)).
          { apply (Qle_lt_trans (Qabs (projT1 (cauchy_real_cos (real_const (projT1 w n))) n - projT1 real_zero n))
                                (Qabs (projT1 (cauchy_real_cos w) n - projT1 real_zero n))
                                (eps / 8)).
            - assert (Hq : projT1 (cauchy_real_cos (real_const (projT1 w n))) n == projT1 (cauchy_real_cos w) n).
              { rewrite (qeqT_imp_qeq _ _ (real_cos_proj (real_const (projT1 w n)) n)).
                rewrite (qeqT_imp_qeq _ _ (real_cos_proj w n)). reflexivity. }
              rewrite Hq. apply Qle_refl.
            - exact Hwpt. }
          exact Hwpt'.
      }
      apply (Qle_lt_trans (Qabs (projT1 w n - cos_zero_seq n)) (projT1 w n - cos_zero_seq n) eps).
      * assert (Hge : Qle 0 (projT1 w n - cos_zero_seq n)).
        { apply (proj1 (Qle_minus_iff (cos_zero_seq n) (projT1 w n))). apply Qlt_le_weak. exact Hzw. }
        rewrite (Qabs_pos (projT1 w n - cos_zero_seq n) Hge). apply Qle_refl.
      * apply (Qle_lt_trans _ (2 * (eps / 8 + eps / 8)) _).
        -- apply Qlt_le_weak. exact Hd.
        -- assert (Hm : 2 * (eps / 8 + eps / 8) == eps / 2) by (unfold Qdiv; field).
           apply (Qle_lt_trans (2 * (eps / 8 + eps / 8)) (eps / 2) eps).
           ++ rewrite Hm. apply Qle_refl.
           ++ apply (proj2 (Qlt_minus_iff (eps / 2) eps)).
              apply (Qlt_le_trans 0 (eps / 2) (eps - eps / 2)).
              ** apply (Qlt_shift_div_l 0 eps 2).
                 --- change (Qlt 0 2). compute. reflexivity.
                 --- simpl. exact HepsQ.
              ** assert (Heq : (eps / 2) == (eps - eps / 2)) by (unfold Qminus; field).
                 rewrite <- Heq. apply Qle_refl.
    + (* w_n <= z_n: u := w_n, v := z_n (symmetric). *)
      assert (Hwpt' : Qlt (Qabs (projT1 (cauchy_real_cos (real_const (projT1 w n))) n - projT1 real_zero n)) (eps / 8)).
      { apply (Qle_lt_trans (Qabs (projT1 (cauchy_real_cos (real_const (projT1 w n))) n - projT1 real_zero n))
                            (Qabs (projT1 (cauchy_real_cos w) n - projT1 real_zero n))
                            (eps / 8)).
        - assert (Hq : projT1 (cauchy_real_cos (real_const (projT1 w n))) n == projT1 (cauchy_real_cos w) n).
          { rewrite (qeqT_imp_qeq _ _ (real_cos_proj (real_const (projT1 w n)) n)).
            rewrite (qeqT_imp_qeq _ _ (real_cos_proj w n)). reflexivity. }
          rewrite Hq. apply Qle_refl.
        - exact Hwpt. }
      assert (Hd : Qlt (cos_zero_seq n - projT1 w n) (2 * (eps / 8 + eps / 8))).
      { apply QltT_to_Qlt.
        apply (cos_inv_dist_le2 (projT1 w n) (cos_zero_seq n) (eps / 8) (eps / 8) n).
        - exact Hn2.
        - exact Hwlo.
        - exact Hwz.
        - exact Hzup2.
        - exact Hwpt'.
        - apply (Qle_lt_trans (Qabs (projT1 (cauchy_real_cos (real_const (cos_zero_seq n))) n - projT1 real_zero n))
                              (Qabs (projT1 (cauchy_real_cos cos_pi_half) n - projT1 real_zero n))
                              (eps / 8)).
          + assert (Hp : projT1 (cauchy_real_cos (real_const (cos_zero_seq n))) n ==
                         projT1 (cauchy_real_cos cos_pi_half) n).
            { cbn [projT1 cauchy_real_cos cos_pi_half real_const]. reflexivity. }
            rewrite Hp. apply Qle_refl.
          + exact Hzpt. }
      apply (Qle_lt_trans (Qabs (projT1 w n - cos_zero_seq n)) (cos_zero_seq n - projT1 w n) eps).
      * rewrite (Qabs_Qminus (projT1 w n) (cos_zero_seq n)).
        assert (Hge : Qle 0 (cos_zero_seq n - projT1 w n)).
        { apply (proj1 (Qle_minus_iff (projT1 w n) (cos_zero_seq n))). exact Hwz. }
        rewrite (Qabs_pos (cos_zero_seq n - projT1 w n) Hge). apply Qle_refl.
      * apply (Qle_lt_trans _ (2 * (eps / 8 + eps / 8)) _).
        -- apply Qlt_le_weak. exact Hd.
        -- assert (Hm : 2 * (eps / 8 + eps / 8) == eps / 2) by (unfold Qdiv; field).
           apply (Qle_lt_trans (2 * (eps / 8 + eps / 8)) (eps / 2) eps).
           ++ rewrite Hm. apply Qle_refl.
           ++ apply (proj2 (Qlt_minus_iff (eps / 2) eps)).
              apply (Qlt_le_trans 0 (eps / 2) (eps - eps / 2)).
              ** apply (Qlt_shift_div_l 0 eps 2).
                 --- change (Qlt 0 2). compute. reflexivity.
                 --- simpl. exact HepsQ.
              ** assert (Heq : (eps / 2) == (eps - eps / 2)) by (unfold Qminus; field).
                 rewrite <- Heq. apply Qle_refl.
  - (* Branch (b): 2 < w_n — the main anchor cos_partial n w_n <= -2/5 and
       the diagonal bound |cos_partial n w_n| < eps/8 are compatible only if
       eps > 16/5; then |w_n - z_n| <= 2 < 16/5 <= eps lets the goal pass
       directly. *)
    assert (Hanch : Qle (cos_partial n (projT1 w n)) (- (2 / 5))).
    { exact (QleT'_to_Qle _ _
              (abl13_cos_partial_neg25 n (projT1 w n) (NatLe_lift _ _ Hn4)
                 (Qle_to_QleT' _ _ Hwgt2) (Qle_to_QleT' _ _ Hwup))). }
    assert (Hwdc : Qlt (Qabs (cos_partial n (projT1 w n) - projT1 real_zero n)) (eps / 8)).
    { pose proof (QltT_to_Qlt _ _ (Hwd n Hnwd)) as Hw.
      rewrite (qeqT_imp_qeq _ _ (real_cos_proj w n)) in Hw.
      exact Hw. }
    assert (Hwdc2 : Qlt (Qabs (cos_partial n (projT1 w n))) (eps / 8)).
    { apply (Qle_lt_trans (Qabs (cos_partial n (projT1 w n)))
                          (Qabs (cos_partial n (projT1 w n) - projT1 real_zero n)) (eps / 8)).
      - assert (Hr : cos_partial n (projT1 w n) == cos_partial n (projT1 w n) - projT1 real_zero n).
        { cbn [projT1 real_zero]. ring. }
        rewrite Hr at 1. apply Qle_refl.
      - exact Hwdc. }
    destruct (Qlt_le_dec (16 / 5) eps) as [Hepsbig | Hepssmall].
    + (* eps > 16/5: |w_n - z_n| <= 2 < 16/5 < eps. *)
      apply (Qle_lt_trans (Qabs (projT1 w n - cos_zero_seq n)) 2 eps).
      * apply QleT'_to_Qle. apply abl13_qabs_le.
        -- apply Qle_to_QleT'. unfold Qle; simpl; lia.
        -- (* -2 <= w_n - z_n (2 <= w_n and z_n <= 5/3 imply 0 <= w_n - z_n). *)
           apply Qle_to_QleT'.
           assert (Hzw0 : Qle (cos_zero_seq n) (projT1 w n)).
           { apply (Qle_trans (cos_zero_seq n) 2 (projT1 w n)).
             - apply (Qle_trans (cos_zero_seq n) (5 / 3) 2);
                 [exact Hzup | change (Qle (5 / 3) 2); unfold Qle, Qdiv; simpl; lia].
             - exact Hwgt2. }
           apply (Qle_trans (- 2) 0 (projT1 w n - cos_zero_seq n)).
           ++ unfold Qle; simpl; lia.
           ++ apply (proj1 (Qle_minus_iff (cos_zero_seq n) (projT1 w n))). exact Hzw0.
        -- (* w_n - z_n <= 2 (w_n < 7/2 <= 2 + z_n). *)
           apply Qle_to_QleT'.
           assert (Hlt2 : Qlt (projT1 w n - cos_zero_seq n) 2).
           { apply (proj2 (Qlt_minus_iff (projT1 w n - cos_zero_seq n) 2)).
             assert (Hr : 2 - (projT1 w n - cos_zero_seq n) == (2 + cos_zero_seq n) - projT1 w n) by ring.
             rewrite Hr.
             apply (proj1 (Qlt_minus_iff (projT1 w n) (2 + cos_zero_seq n))).
             apply (Qlt_le_trans (projT1 w n) (7 / 2) (2 + cos_zero_seq n)).
             --- exact (HNup n Hnup).
             --- assert (Hr7 : 7 / 2 == 2 + 3 / 2) by (unfold Qdiv; field; unfold Qeq; simpl; lia).
                 rewrite Hr7.
                 apply Qplus_le_compat; [change (Qle 2 2); apply Qle_refl | exact Hzlo]. }
           exact (Qlt_le_weak _ _ Hlt2).
      * apply (Qlt_le_trans 2 (16 / 5) eps).
        -- change (Qlt 2 (16 / 5)). unfold Qlt, Qdiv; simpl; lia.
        -- apply Qlt_le_weak. exact Hepsbig.
    + (* eps <= 16/5: contradiction (-eps/8 < cos_partial n w_n <= -2/5
         implies eps/8 > 2/5). *)
      exfalso.
      assert (Hle8 : Qle (eps / 8) (2 / 5)).
      { assert (Hd : eps / 8 == eps * (1 / 8)) by (unfold Qdiv; field; unfold Qeq; simpl; lia).
        assert (Hd2 : 2 / 5 == (16 / 5) * (1 / 8)) by (unfold Qdiv; field; unfold Qeq; simpl; lia).
        rewrite Hd, Hd2.
        apply (Qmult_le_compat_r eps (16 / 5) (1 / 8)).
        - exact Hepssmall.
        - apply Qlt_le_weak. change (Qlt 0 (1 / 8)). compute. reflexivity. }
      assert (Hwdc2T : QltT (Qabs (cos_partial n (projT1 w n))) (eps / 8)).
      { apply Qlt_to_QltT. exact Hwdc2. }
      assert (Hopp8 : Qlt (- (eps / 8)) (cos_partial n (projT1 w n))).
      { exact (QltT_to_Qlt _ _
                (abl13_qabs_lt_opp (cos_partial n (projT1 w n)) (eps / 8) Hwdc2T)). }
      assert (Hpre : Qlt (- (eps / 8)) (- (2 / 5))).
      { apply (Qlt_le_trans (- (eps / 8)) (cos_partial n (projT1 w n)) (- (2 / 5)));
          [exact Hopp8 | exact Hanch]. }
      assert (Hlt25 : Qlt (2 / 5) (eps / 8)).
      { assert (Hq := Qopp_lt_compat (- (eps / 8)) (- (2 / 5)) Hpre).
        assert (Hr1 : - (- (2 / 5)) == 2 / 5) by ring.
        assert (Hr2 : - (- (eps / 8)) == eps / 8) by ring.
        rewrite Hr1, Hr2 in Hq. exact Hq. }
      exact (Qlt_irrefl (2 / 5) (Qlt_le_trans (2 / 5) (eps / 8) (2 / 5) Hlt25 Hle8)).
Qed.

(* ============================================================ *)
(* Part 5 · Strength relation: widened2 implies widened (a       *)
(*   machine-verified strengthening chain). The widened-form     *)
(*   premise is strictly weaker (w < 2 implies w < 7/2); the     *)
(*   instance set is a strict superset.                          *)
(* ============================================================ *)

Lemma abl13_real_lt_le_widen : forall x : Real,
  real_lt x (real_const 2) -> real_lt x (real_const (7 / 2)).
Proof.
  intros x [eps [Heps [N HN]]].
  exists eps. split; [exact Heps | ].
  exists N. intros n Hn.
  apply Qlt_to_QltT.
  apply (Qlt_le_trans eps (projT1 (real_const 2) n - projT1 x n) ((7 / 2) - projT1 x n)).
  - apply QltT_to_Qlt. exact (HN n Hn).
  - assert (Hle2 : Qle (projT1 (real_const 2) n) (7 / 2)).
    { rewrite (qeqT_imp_qeq _ _ (real_const_proj 2 n)). unfold Qle, Qdiv; simpl; lia. }
    assert (Hr : (projT1 (real_const 2) n - projT1 x n) == (projT1 (real_const 2) n + (- projT1 x n))) by ring.
    rewrite Hr.
    assert (Hr2 : ((7 / 2) - projT1 x n) == ((7 / 2) + (- projT1 x n))) by ring.
    rewrite Hr2.
    apply Qplus_le_compat; [exact Hle2 | apply Qle_refl].
Qed.

Corollary abl13_widened_of_widened2 : forall (w : Real),
  real_lt (real_const (3 / 2)) w -> real_lt w (real_const 2) ->
  real_eq (cauchy_real_cos w) real_zero ->
  real_eq w cos_pi_half.
Proof.
  intros w Hlow Hup Hw0.
  apply (abl13_cos_pi_half_unique_widened2 w Hlow).
  - apply abl13_real_lt_le_widen. exact Hup.
  - exact Hw0.
Qed.

(* ============================================================ *)
(* Part 6 · Admission-face final audit + extraction check        *)
(* ============================================================ *)

(* PA statements checked one by one against the 26 theorems
   (three ledgers, zero discrepancy). *)
Print Assumptions abl13_qsq_nonneg.
Print Assumptions abl13_qsq_abs.
Print Assumptions abl13_qdiv_le.
Print Assumptions abl13_qabs_le.
Print Assumptions abl13_qabs_lt_opp.
Print Assumptions abl13_qplus_nonpos_le.
Print Assumptions abl13_qpow_neg1_S2.
Print Assumptions abl13_qpow_neg1_even.
Print Assumptions abl13_qpow_neg1_odd.
Print Assumptions abl13_qpow_even_abs.
Print Assumptions abl13_a_nonneg.
Print Assumptions abl13_qfact_neq0.
Print Assumptions abl13_zQ_neq0.
Print Assumptions abl13_qdiv_cancel.
Print Assumptions abl13_qpow_nonneg.
Print Assumptions abl13_a_decr.
Print Assumptions abl13_cp_even_le.
Print Assumptions abl13_cp_le_s4.
Print Assumptions abl13_sq_window.
Print Assumptions abl13_cp4_G.
Print Assumptions abl13_G_P.
Print Assumptions abl13_cp4_le_neg25.
Print Assumptions abl13_cos_partial_neg25.
Print Assumptions abl13_cos_pi_half_unique_widened2.
Print Assumptions abl13_real_lt_le_widen.
Print Assumptions abl13_widened_of_widened2.

(* Extraction check: Set-layer data faces (one Q-level anchor + one Real-level
   main theorem); criterion = extraction product Obj.magic count 0. *)
Recursive Extraction abl13_cos_partial_neg25.
Recursive Extraction abl13_widened_of_widened2.
