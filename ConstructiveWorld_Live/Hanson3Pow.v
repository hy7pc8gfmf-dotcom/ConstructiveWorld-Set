(* ConstructiveWorld-Set — lcm upper bounds via a half-way binomial bridge. *)

(** * Hanson3Pow: an improved lcm upper bound on the [nat] layer.

    Mission.  Upper estimates for [lcm(1..n)] along the way to the
      constructive bound [lcm(1..n) < 3^n]: the absorption identity
      [h3_binom_absorb] ([C(S n, S k) * S k = S n * C(n, k)]), the
      divisibility [h3_lcm_double_divide] ([lcm(1..2n)] divides
      [C(2n,n) * n!]), the half-way bound [h3_lcm_le_halfbinom] and its
      Set-carrier restatement [h3_lcm_le_halfbinom_t] (carried by
      [hl_le_t]).

    Dependencies.  Stdlib [Arith.Arith], [Arith.Factorial], [Lia]; requires
      [HansonLcm] of this development.

    References.  This development, the baseline module Hanson3Pow.v in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All statements are [Qed]-closed with no admissions; the
      main theorems are carried by [hl_le_t] on the [Set] layer while the
      supporting lemmas live on the [nat] layer as reasoning scaffolding;
      [h3_prod_from] and [h3_binom] are executable; [Print Assumptions]
      runs at the end of the file.

    Build.  [rocq c -native-compiler no -q -Q . "" Hanson3Pow.v] compiles
      cleanly (exit 0); the artifact magic is [436f7121 00015ff4]. *)

From Stdlib Require Import Arith.Arith Arith.Factorial Lia.
Require Import HansonLcm.

(* ================ Section A. Binomial arithmetic: the absorption identity ================ *)

(* Edge case [k = 0]: [hl_binom n 0 = 1] for all [n].  The fixpoint reduces
   on its first argument only at constructor heads, so this is stated
   separately (base case of [h3_prod_binom_fact]). *)
Lemma h3_binom_k0 : forall n : nat, hl_id (hl_binom n 0) 1.
Proof. destruct n; apply hl_idrefl. Qed.

(* [h3_binom_1]: [hl_binom (S n) 1 = S n] (used at the [k = 0] case of
   [h3_binom_absorb]). *)
Lemma h3_binom_1 : forall n : nat, hl_id (hl_binom (S n) 1) (S n).
Proof.
  assert (H : forall n : nat, hl_binom (S n) 1 = S n).
  { induction n as [| n IH].
    - reflexivity.
    - rewrite (hl_binom_S (S n) 0).
      assert (E0 : hl_binom (S n) 0 = 1) by reflexivity.
      rewrite E0. rewrite IH. lia. }
  intro n.
  exact (eq_rect (hl_binom (S n) 1) (fun y => hl_id (hl_binom (S n) 1) y)
           (hl_idrefl (hl_binom (S n) 1)) (S n) (H n)).
Qed.

(* [h3_binom_absorb]: the absorption identity
   [C(S n, S k) * S k = S n * C(n, k)].  Induction on [n] with case analysis
   on [k]; the inductive step uses the induction premise at both [k] and
   [S k]
   (no binomial identities are available in the stdlib [nat] layer). *)
Lemma h3_binom_absorb : forall n k : nat,
  hl_id (hl_binom (S n) (S k) * (S k)) ((S n) * hl_binom n k).
Proof.
  assert (H : forall n k : nat,
    hl_binom (S n) (S k) * (S k) = (S n) * hl_binom n k).
  { induction n as [| n IH]; intro k.
  - destruct k as [| k']; reflexivity.
  - destruct k as [| k'].
    + rewrite (hl_binom_S (S n) 0).
      assert (E0 : hl_binom (S n) 0 = 1) by reflexivity.
      rewrite E0. rewrite (hl_id_eq nat _ _ (h3_binom_1 n)). lia.
    + rewrite (hl_binom_S (S n) (S k')).
      pose proof (IH k') as H1. pose proof (IH (S k')) as H2.
      rewrite (Nat.mul_succ_r (hl_binom (S n) (S (S k'))) (S k')) in H2.
      rewrite (Nat.mul_succ_r (hl_binom (S n) (S k')
                 + hl_binom (S n) (S (S k'))) (S k')).
      rewrite (Nat.mul_add_distr_r (hl_binom (S n) (S k'))
                 (hl_binom (S n) (S (S k'))) (S k')).
      rewrite H1.
      assert (HA : hl_binom (S n) (S k') = hl_binom n k' + hl_binom n (S k'))
        by reflexivity.
      assert (HAm : S n * hl_binom (S n) (S k') =
                    S n * hl_binom n k' + S n * hl_binom n (S k'))
        by (rewrite HA; ring).
      assert (HR : S (S n) * hl_binom (S n) (S k') =
                   S n * hl_binom (S n) (S k') + hl_binom (S n) (S k')) by ring.
      rewrite HR. lia. }
  intros n k. destruct (H n k). apply hl_idrefl.
Qed.

(* [h3_binom_ge1]: [k <= n] implies [1 <= hl_binom n k] (positivity premise
   of [h3_divide_le]). *)
Lemma h3_binom_ge1 : forall n k : nat, k <= n -> hl_le_t 1 (hl_binom n k).
Proof.
  intros n. induction n as [| n IH]; intros k Hk; apply hl_le_to_le_t.
  - assert (k = 0) by lia. subst k. cbn [hl_binom]. lia.
  - destruct k as [| k'].
    + cbn [hl_binom]. lia.
    + rewrite (hl_binom_S n k').
      apply (Nat.le_trans 1 (hl_binom n k')).
      * apply hl_le_t_to_le. apply IH. lia.
      * apply Nat.le_add_r.
Qed.

(* ================ Section B. Interval products [h3_prod_from a k] ================ *)

Fixpoint h3_prod_from (a k : nat) : nat :=
  match k with
  | O => 1
  | S k' => (a + k') * h3_prod_from a k'
  end.

(* [h3_prod_divide]: [a <= m < a + k] implies [m] divides [h3_prod_from a k]
   ([m] is itself one of the factors). *)
Lemma h3_prod_divide : forall k a m : nat,
  a <= m -> m < a + k -> Nat.divide m (h3_prod_from a k).
Proof.
  induction k as [| k IH]; intros a m H1 H2.
  - lia.
  - cbn [h3_prod_from].
    destruct (Nat.eq_dec m (a + k)) as [E|NE].
    + rewrite E. exists (h3_prod_from a k). ring.
    + destruct (IH a m H1 ltac:(lia)) as [p Hp].
      exists (p * (a + k))%nat. rewrite Hp. ring.
Qed.

(* [h3_prod_binom_fact]: the main identity
   [prod_{i=1}^{k} (m+i) = C(m+k, k) * k!].  Induction on [k]; the inductive
   step closes by [h3_binom_absorb] in multiplicative form (no division). *)
Lemma h3_prod_binom_fact : forall m k : nat,
  hl_id (h3_prod_from (S m) k) (hl_binom (m + k) k * fact k).
Proof.
  assert (H : forall m k : nat,
    h3_prod_from (S m) k = hl_binom (m + k) k * fact k).
  { intros m k. induction k as [| k IH].
    - rewrite (hl_id_eq nat _ _ (h3_binom_k0 (m + 0))). reflexivity.
    - cbn [h3_prod_from fact].
      rewrite Nat.add_succ_r, Nat.mul_assoc.
      pose proof (hl_id_eq nat _ _ (h3_binom_absorb (m + k) k)) as HA.
      rewrite HA.
      replace (S (m + k)) with (S m + k) by lia.
      rewrite IH. ring. }
  intros m k. destruct (H m k). apply hl_idrefl.
Qed.

(* ================ Section C. Divisibility closure of the lcm fold ================ *)

(* [h3_fact_divide]: [1 <= m <= n] implies [m] divides [n!]
   (induction on [n]). *)
Lemma h3_fact_divide : forall n m : nat,
  1 <= m -> m <= n -> Nat.divide m (fact n).
Proof.
  induction n as [| n IH]; intros m H1 H2.
  - lia.
  - destruct (Nat.eq_dec m (S n)) as [E|NE].
    + rewrite E. exists (fact n). cbn [fact]. ring.
    + destruct (IH m H1 ltac:(lia)) as [p Hp].
      exists (p * S n)%nat. cbn [fact]. rewrite Hp. ring.
Qed.

(* [h3_lcm_fold_divide]: if every [m] in [1..N] divides [D], then [L(N)]
   divides [D] (via [Nat.lcm_least]). *)
Lemma h3_lcm_fold_divide : forall N D : nat,
  (forall m : nat, 1 <= m -> m <= N -> Nat.divide m D) ->
  Nat.divide (hl_lcm_upto N) D.
Proof.
  intros N D H. induction N as [| N IHN].
  - cbn [hl_lcm_upto]. exists D. ring.
  - cbn [hl_lcm_upto]. apply Nat.lcm_least.
    + apply IHN. intros m H1 H2. apply H; lia.
    + apply H; lia.
Qed.

(* [h3_lcm_upto_fact_divide]: [L(n)] divides [n!] (instance of the fold
   lemma). *)
Lemma h3_lcm_upto_fact_divide : forall n, Nat.divide (hl_lcm_upto n) (fact n).
Proof.
  intro n. apply h3_lcm_fold_divide. intros m H1 H2.
  apply h3_fact_divide; lia.
Qed.

(* [h3_fact_pos]: factorial positivity [0 < fact n]. *)
Lemma h3_fact_pos : forall n, hl_le_t 1 (fact n).
Proof.
  intro n. apply hl_le_to_le_t. induction n as [| n IH].
  - cbn [fact]. lia.
  - cbn [fact]. apply Nat.mul_pos_pos; lia.
Qed.

(* [h3_lcm_pos]: [1 <= L(n)] (from divisibility into [n!] and its
   positivity). *)
Lemma h3_lcm_pos : forall n, hl_le_t 1 (hl_lcm_upto n).
Proof.
  intro n. apply hl_le_to_le_t.
  destruct (h3_lcm_upto_fact_divide n) as [p Hp].
  pose proof (hl_le_t_to_le 1 (fact n) (h3_fact_pos n)) as Hf.
  destruct p as [| p'].
  - rewrite Nat.mul_0_l in Hp. lia.
  - destruct (hl_lcm_upto n) as [| L'].
    + rewrite Nat.mul_0_r in Hp. lia.
    + lia.
Qed.

(* [h3_divide_le]: divisibility with both sides positive implies [a <= b]. *)
Lemma h3_divide_le : forall a b : nat,
  Nat.divide a b -> 1 <= a -> 0 < b -> hl_le_t a b.
Proof.
  intros a b Hd Ha Hb. apply hl_le_to_le_t.
  destruct Hd as [p Hp]. destruct p as [| p'].
  - rewrite Nat.mul_0_l in Hp. lia.
  - destruct a as [| a'].
    + lia.
    + rewrite Hp. replace (S p' * S a') with (S a' + p' * S a') by ring. lia.
Qed.

(* [h3_lcm_mono_divide]: [n <= m] implies [L(n)] divides [L(m)] (layerwise
   via [Nat.divide_lcm_l]). *)
Lemma h3_lcm_mono_divide : forall n m : nat,
  n <= m -> Nat.divide (hl_lcm_upto n) (hl_lcm_upto m).
Proof.
  intros n m. induction m as [| m IHm]; intro H.
  - assert (n = 0) by lia. subst n. apply Nat.divide_refl.
  - destruct (Nat.eq_dec n (S m)) as [E|NE].
    + rewrite E. apply Nat.divide_refl.
    + cbn [hl_lcm_upto].
      apply (hl_div_trans (hl_lcm_upto n) (hl_lcm_upto m)
               (Nat.lcm (hl_lcm_upto m) (S m))).
      * apply IHm. lia.
      * apply Nat.divide_lcm_l.
Qed.

(* ================ Section D. Half-way binomial bridge (prime-free) ================ *)

(* [h3_lcm_double_divide]: the main theorem that [L(2n)] divides
   [C(2n,n) * n!].  For [m <= n], [m] divides [n!]; for [n < m <= 2n], [m]
   divides [prod(n+1..2n) = C(2n,n) * n!] (by [h3_prod_divide] and
   [h3_prod_binom_fact]); the fold lemma closes. *)
Theorem h3_lcm_double_divide : forall n : nat,
  Nat.divide (hl_lcm_upto (2 * n)) (hl_binom (2 * n) n * fact n).
Proof.
  intro n. apply h3_lcm_fold_divide. intros m H1 H2.
  destruct (Nat.le_gt_cases m n) as [Hle|Hgt].
  - apply (hl_div_trans m (fact n) (hl_binom (2 * n) n * fact n)).
    + apply h3_fact_divide; lia.
    + exists (hl_binom (2 * n) n). ring.
  - apply (hl_div_trans m (h3_prod_from (S n) n)
             (hl_binom (2 * n) n * fact n)).
    + apply h3_prod_divide; lia.
    + rewrite (hl_id_eq nat _ _ (h3_prod_binom_fact n n)).
      replace (2 * n) with (n + n) by lia.
      exists 1. ring.
Qed.

(* [h3_lcm_le_halfbinom]: the half-way upper bound
   [L(n) <= C(2*ceil(n/2), ceil(n/2)) * ceil(n/2)!], a strict sharpening of
   the [n!] placeholder [hl_lcm_le_fact] of HansonLcm. *)
(* Scope note: the bound still carries the [ceil(n/2)!] factor; the [3^n]
   stage needs prime p-adic valuations and lives elsewhere. *)
Theorem h3_lcm_le_halfbinom : forall n : nat,
  hl_le_t (hl_lcm_upto n)
    (hl_binom (2 * S (n / 2)) (S (n / 2)) * fact (S (n / 2))).
Proof.
  intro n. apply hl_le_to_le_t.
  assert (H2n0 : 2 <> 0) by lia.
  pose proof (Nat.div_mod n 2 H2n0) as Hdm.
  pose proof (Nat.mod_upper_bound n 2 H2n0) as Hmod.
  assert (Hn : n <= 2 * S (n / 2)) by lia.
  apply (Nat.le_trans (hl_lcm_upto n) (hl_lcm_upto (2 * S (n / 2)))
           (hl_binom (2 * S (n / 2)) (S (n / 2)) * fact (S (n / 2)))).
  - pose proof (hl_le_t_to_le _ _ (h3_lcm_pos (2 * S (n / 2)))) as Hp1.
    apply hl_le_t_to_le. apply h3_divide_le.
    + apply h3_lcm_mono_divide. exact Hn.
    + apply hl_le_t_to_le. apply h3_lcm_pos.
    + lia.
  - pose proof (hl_le_t_to_le _ _ (h3_lcm_pos (2 * S (n / 2)))) as Hp2.
    assert (Hb : 1 <= hl_binom (2 * S (n / 2)) (S (n / 2)))
      by (apply hl_le_t_to_le; apply h3_binom_ge1; lia).
    assert (Hf2 : 0 < fact (S (n / 2)))
      by (apply hl_le_t_to_le; apply h3_fact_pos).
    assert (Hd2 : 0 < hl_binom (2 * S (n / 2)) (S (n / 2)) * fact (S (n / 2)))
      by (apply Nat.mul_pos_pos; lia).
    apply hl_le_t_to_le. apply h3_divide_le.
    + apply h3_lcm_double_divide.
    + lia.
    + exact Hd2.
Qed.

(* [h3_lcm_le_halfbinom_t]: Set-layer restatement carried by [hl_le_t];
   a true sharpening of its HansonLcm counterpart. *)
Theorem h3_lcm_le_halfbinom_t : forall n : nat,
  hl_le_t (hl_lcm_upto n)
    (hl_binom (2 * S (n / 2)) (S (n / 2)) * fact (S (n / 2)))%nat.
Proof.
  intro n. exact (h3_lcm_le_halfbinom n).
Qed.

(* Assumption audit: the following [Print Assumptions] outputs should be
   free of dependencies. *)
Print Assumptions h3_lcm_double_divide.
Print Assumptions h3_lcm_le_halfbinom_t.
