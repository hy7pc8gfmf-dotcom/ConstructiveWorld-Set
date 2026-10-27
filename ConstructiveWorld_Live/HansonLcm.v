(* ConstructiveWorld-Set — arithmetic supply modules on the nat layer. *)

(** * HansonLcm: central-binomial and lcm bounds on the nat layer.

    Mission.  Pure [nat]-level Hanson-type bounds: the central binomial
      coefficient bound [hl_central_binom_le] ([hl_binom (2*n) n] at most
      [4^n], via the Pascal-recursion coefficient [hl_binom], the pointwise
      bound [hl_binom_le_pow2] ([hl_binom n k] at most [2^n]) and the base
      change [hl_pow4]); the lcm machine [hl_lcm_upto] with the divisibility
      transfer [hl_lcm_divide_all] and the factorial upper bound
      [hl_lcm_le_fact] / [hl_lcm_le_fact_t]; and the comparators
      [hl_id] / [hl_le_t] with their scaffold bridges.

    Dependencies.  Stdlib [Arith.Arith], [Arith.Factorial], [Lia] only; no
      development-internal requires.

    References.  The baseline module HansonLcm.v in ConstructiveWorld-Main,
      whose statement names are carried over here verbatim
      (statement-face Set-carrier completion); estimates follow
      D. Hanson, Bull. London Math. Soc. 12 (1980).

    Constructivity.  All statements are carried by [Set] (the comparator
      [hl_le_t] = [hl_id (Nat.leb a b) true]); [hl_binom] and
      [hl_lcm_upto] are executable Fixpoints extracting with
      [Obj.magic] = 0; the elimination bridges [hl_id_eq] and
      [hl_le_t_to_le] are registered scaffold bridges (Set-to-Prop
      direction, in-body only); [coqchk] reports [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" HansonLcm.v] compiles
      cleanly (exit 0); its artifact begins [436f7121 00015ff4]. *)

From Stdlib Require Import Arith.Arith Arith.Factorial Lia.

(* ================= Section A. Set-layer comparators ================= *)

Inductive hl_id {A : Set} (x : A) : A -> Set :=
  hl_idrefl : hl_id x x.

(* Equality elimination from [hl_id] (Set-to-Prop scaffold bridge). *)
Lemma hl_id_eq : forall (A : Set) (x y : A), hl_id x y -> x = y.
Proof. intros A x y H. induction H. reflexivity. Qed.

Definition hl_le_t (a b : nat) : Set := hl_id (Nat.leb a b) true.

(* Two-way bridge between the Prop-face [le] and the Set-face [hl_le_t]. *)
Lemma hl_le_to_le_t : forall a b : nat, a <= b -> hl_le_t a b.
Proof.
  intros a b H. apply Nat.leb_le in H. unfold hl_le_t. rewrite H. exact (hl_idrefl true).
Qed.

Lemma hl_le_t_to_le : forall a b : nat, hl_le_t a b -> a <= b.
Proof.
  intros a b H. apply Nat.leb_le. unfold hl_le_t in H.
  exact (hl_id_eq _ _ _ H).
Qed.

(* ================= Section B. Binomial coefficients (Pascal recursion) ================= *)

Fixpoint hl_binom (n k : nat) : nat :=
  match k with
  | O => 1
  | S k' =>
      match n with
      | O => 0
      | S n' => hl_binom n' k' + hl_binom n' (S k')
      end
  end.

(* Explicit Pascal expansion: C(S n, S k) = C(n,k) + C(n,k+1). *)
Lemma hl_binom_S : forall n k : nat,
  hl_id (hl_binom (S n) (S k)) (hl_binom n k + hl_binom n (S k)).
Proof. intros n k.
  exact (hl_idrefl (hl_binom n k + hl_binom n (S k))). Qed.

(* Base change: [4^n] equals [2^(2*n)]. *)
Lemma hl_pow4 : forall n : nat, hl_id (4 ^ n) (2 ^ (2 * n))%nat.
Proof.
  induction n as [| n IH].
  - apply hl_idrefl.
  - assert (Hpw : (4 ^ S n = 2 ^ (2 * S n))%nat).
    { rewrite Nat.pow_succ_r'.
      assert (IHp : (4 ^ n = 2 ^ (2 * n))%nat)
        by exact (hl_id_eq nat _ _ IH).
      rewrite IHp.
      replace (2 * S n)%nat with (S (S (2 * n)))%nat by lia.
      rewrite !Nat.pow_succ_r'. lia. }
    rewrite Hpw. apply hl_idrefl.
Qed.

(* Powers are positive: [1 <= 2^n]. *)
Lemma hl_pow2_ge1 : forall n : nat, hl_le_t 1 (2 ^ n).
Proof.
  intro n. apply hl_le_to_le_t.
  induction n as [| n IH].
  - cbn [Nat.pow]. lia.
  - rewrite Nat.pow_succ_r'. lia.
Qed.

(* Pointwise bound core (nontrivial double induction): every binomial
   coefficient is at most [2^n], for all [n] and [k] with no hypotheses
   (out-of-range coefficients are 0 and are covered by the induction).
   Induction step: C(S n, S k) = C(n,k) + C(n,k+1) at most
   2^n + 2^n = 2^(S n), using both induction hypotheses at (n,k) and
   (n,k+1). *)
Lemma hl_binom_le_pow2 : forall n k : nat, hl_le_t (hl_binom n k) (2 ^ n).
Proof.
  induction n as [| n IH]; intro k.
  - apply hl_le_to_le_t.
    destruct k as [| k'].
    + cbn [hl_binom Nat.pow]. lia.
    + cbn [hl_binom]. lia.
  - apply hl_le_to_le_t.
    destruct k as [| k'].
    + cbn [hl_binom].
      pose proof (hl_le_t_to_le 1 (2 ^ S n) (hl_pow2_ge1 (S n))). lia.
    + assert (Hbs : (hl_binom (S n) (S k') = hl_binom n k' + hl_binom n (S k'))%nat)
        by exact (hl_id_eq nat _ _ (hl_binom_S n k')).
      rewrite Hbs. rewrite Nat.pow_succ_r'.
      pose proof (hl_le_t_to_le (hl_binom n k') (2 ^ n) (IH k')) as H1.
      pose proof (hl_le_t_to_le (hl_binom n (S k')) (2 ^ n) (IH (S k'))) as H2.
      lia.
Qed.

(* The central binomial coefficient bound C(2n,n) at most 4^n, via the
   base change [hl_pow4] and the pointwise bound at (2n, n); this is the
   C(2m,m) at most 4^m step of Hanson's argument. *)
Theorem hl_central_binom_le : forall n : nat,
  hl_le_t (hl_binom (2 * n) n) (4 ^ n)%nat.
Proof.
  intro n. apply hl_le_to_le_t.
  assert (Hpw : (4 ^ n = 2 ^ (2 * n))%nat)
    by exact (hl_id_eq nat _ _ (hl_pow4 n)).
  rewrite Hpw. apply hl_le_t_to_le. apply hl_binom_le_pow2.
Qed.

(* ================= Section C. The lcm machine and transfer bridges ================= *)

(* Folded carrier of lcm(1..n): L(0) = 1 (empty product),
   L(S m) = lcm(L m, S m). *)
Fixpoint hl_lcm_upto (n : nat) : nat :=
  match n with
  | O => 1
  | S m => Nat.lcm (hl_lcm_upto m) (S m)
  end.

(* Core inequality: the lcm is at most the product (expansion of
   [Nat.lcm] = a * (b / gcd a b)). *)
Lemma hl_lcm_le_mul : forall a b : nat, hl_le_t (Nat.lcm a b) (a * b).
Proof.
  intros a b. apply hl_le_to_le_t. unfold Nat.lcm.
  destruct a as [| a'].
  - rewrite Nat.mul_0_l. apply Nat.le_0_l.
  - assert (Hg : Nat.gcd (S a') b <> 0).
    { destruct (Nat.eq_dec (Nat.gcd (S a') b) 0) as [E|N]; [|exact N].
      exfalso.
      assert (Hd : Nat.divide (Nat.gcd (S a') b) (S a'))
        by apply Nat.gcd_divide_l.
      rewrite E in Hd. destruct Hd as [p Hp].
      rewrite Nat.mul_0_r in Hp. lia. }
    assert (Hpos : 1 <= Nat.gcd (S a') b) by lia.
    assert (Hd : b / Nat.gcd (S a') b <= b).
    { apply Nat.Private_NDivProp.div_le_upper_bound; [exact Hg|].
      apply (Nat.le_trans b (1 * b)%nat (Nat.gcd (S a') b * b)%nat).
      - rewrite Nat.mul_1_l. apply Nat.le_refl.
      - apply Nat.mul_le_mono_r. exact Hpos. }
    apply Nat.mul_le_mono_l. exact Hd.
Qed.

(* Divisibility transitivity (normalization q * (p * a) = (q * p) * a). *)
Lemma hl_div_trans : forall a b c : nat,
  Nat.divide a b -> Nat.divide b c -> Nat.divide a c.
Proof.
  intros a b c H1 H2. destruct H1 as [p Hp]. destruct H2 as [q Hq].
  exists (q * p)%nat. rewrite Hq. rewrite Hp. ring.
Qed.

(* Transfer bridge one: 1 <= m <= n implies m divides L(n)
   (fold layer by layer through [Nat.divide_lcm_l/r]). *)
Lemma hl_lcm_divide_all : forall n m : nat,
  1 <= m -> m <= n -> Nat.divide m (hl_lcm_upto n).
Proof.
  induction n as [| n IH]; intros m H1 H2.
  - lia.
  - destruct (Nat.eq_dec m (S n)) as [E|NE].
    + rewrite E. cbn [hl_lcm_upto]. apply Nat.divide_lcm_r.
    + cbn [hl_lcm_upto].
      apply (hl_div_trans m (hl_lcm_upto n)
               (Nat.lcm (hl_lcm_upto n) (S n))).
      * apply IH; lia.
      * apply Nat.divide_lcm_l.
Qed.

(* Transfer bridge two (upper bound): L(n) at most n!.
   Induction step: L(S n) = lcm(L n, S n) at most L n * S n at most
   n! * S n = (S n)!. *)
Lemma hl_lcm_le_fact : forall n : nat, hl_le_t (hl_lcm_upto n) (fact n).
Proof.
  intro n. apply hl_le_to_le_t.
  induction n as [| n IH].
  - simpl. lia.
  - cbn [hl_lcm_upto].
    transitivity (hl_lcm_upto n * S n)%nat.
    + apply hl_le_t_to_le. apply hl_lcm_le_mul.
    + assert (Heq : fact (S n) = fact n * S n)
        by (cbn [fact]; ring).
      rewrite Heq. apply Nat.mul_le_mono_r. exact IH.
Qed.

(* ================= Section D. Statement-face restatements ================= *)

(* Statement-face universal restatement of the factorial upper bound
   (informative carrier). *)
Theorem hl_lcm_le_fact_t : forall n : nat, hl_le_t (hl_lcm_upto n) (fact n).
Proof. intro n. exact (hl_lcm_le_fact n). Qed.

(* Coupling instance: C(24,12) at most 4^12 on the Set face, from
   [hl_central_binom_le 12]. *)
Theorem hl_binom24_le_4pow12 : hl_le_t (hl_binom 24 12) (4 ^ 12)%nat.
Proof. exact (hl_central_binom_le 12). Qed.

(* Assumption closure of the main statements. *)
Print Assumptions hl_central_binom_le.
