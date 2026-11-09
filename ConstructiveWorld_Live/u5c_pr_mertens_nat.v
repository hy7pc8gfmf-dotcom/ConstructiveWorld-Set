(* ConstructiveWorld-Set -- u5c_pr_mertens_nat: the full constructive chain for the divergence of the sum of prime reciprocals. *)

(** * u5c_pr_mertens_nat: divergence of the prime reciprocals with an extractable witness.

    Mission.  The full constructive chain for the divergence of the sum of prime reciprocals,
      delivering an extractable witness: the harmonic divergence core (abl_Pr_recip_sum), the
      Euler-Harm transfer (pze_euler_harm), the Mertens reverse nat finite form
      [pzs_mertens_reverse] (with [pzs_prodsum] and [pzs_lcm_ge_pow4], lcm(1..2^m) >= 4^m),
      the per-milestone assembly [pzs_step] over the decidable bounded search [pzs_find], and
      the main statement [pzs_prime_recip_diverge] (Defined, extractable): for every K an
      explicit (n, C) with 2 <= n, 1 <= C, 128(n+1) <= C and K*C <= 4 * [sum_{p<=n} (C/p)].

    Dependencies.  Pure Stdlib ([Arith]/[List]/[Bool]/[Lia]) plus [HansonLcm] and the abl_Pr_
      modules core_01, enum_02, lcmdecomp_04, recip_sum, euler_prod.

    References.  The Isabelle AFP entry Prime_Number_Theorem, Mertens' second theorem (Eberl &
      Paulson 2018, the classical asymptotic form); mathlib SumPrimeReciprocals.lean; the
      difference here is the extractable nat form, an explicit witness (n, C) per K via sigT
      (Euler 1737, no asymptotic comparison); this development, u5c_pr_mertens_nat.v, the
      baseline module carried over verbatim (comment-face wash, UpReqMisc5B interface-alignment,
      361-red statement carrier re-cast of [pzs_pen_split]; zero name edits).

    Constructivity.  Main statement and search items are nat-dependent pairs (sigT); conjunction
      and comparison carriers live in Set ([And] := A*B; [NatLebT] = [Nat.leb] reflected through
      [Id]); all definitions first-order nat, extractable; Prop inequalities scaffolding only;
      nonlinear steps explicit multiplication and ring; zero axioms, zero admissions, zero
      classical logic; smoke tests by small-instance cbv.

    Build.  Rocq 9.1 direct [coqc -Q . "" -native-compiler no] (the vo shadow tree rebuilt in the
      same world, cpu_guard load capping); the artifact starts with [436f7121 000160bc]. *)

From Stdlib Require Import Arith.Arith List Bool Lia.
Require Import HansonLcm.
Require Import abl_Pr_core_01.
Require Import abl_Pr_enum_02.
Require Import abl_Pr_lcm_eq.
Require Import abl_Pr_lcmdecomp_04.
Require Import abl_Pr_recip_sum.
Require Import abl_Pr_euler_prod.

(* ---- §0 the Set-layer connectives and comparison carriers ---- *)

(* the Set-layer identity type (the single constructor id_refl); equality comparisons in Set-carried statements are expressed through it *)
Inductive Id {A : Set} (x : A) : A -> Set :=
| id_refl : Id x x.

Arguments id_refl {A} {x}.

(* the Set-layer conjunction (a type former); the conjunction positions of witness statements live in Set, so certificates carry computational content *)
Definition And (A B : Set) : Set := A * B.

(* the Set carrier of the nat weak comparison: the boolean decider Nat.leb
   reflected through the identity type; a <= b holds exactly when
   NatLebT a b is inhabited *)
Definition NatLebT (a b : nat) : Set := Id (Nat.leb a b) true.

(* ---- §1 basic arithmetic: the divisibility gap, coprimality, the power-gap product bound ---- *)

(* a divisor d of both a and a−1 with a ≥ 1 forces d = 1 *)
Lemma u5c_dvd_sub_gap : forall d a : nat,
  1 <= a -> 1 <= d -> Nat.divide d a -> Nat.divide d (a - 1) -> d = 1.
Proof.
  intros d a Ha Hd [x Hx] [y Hy].
  assert (Hxy : y <= x).
  { destruct (le_lt_dec y x) as [Hle | Hlt]; [exact Hle | exfalso].
    assert (Hm : x * d <= y * d) by (apply Nat.mul_le_mono_r; lia).
    lia. }
  replace x with (y + (x - y)) in Hx by lia.
  rewrite Nat.mul_add_distr_r in Hx.
  assert (Hone : (x - y) * d = 1) by lia.
  destruct (x - y) as [|k] eqn:Ek.
  - lia.
  - assert (Hle : 1 * d <= S k * d) by (apply Nat.mul_le_mono_r; lia).
    rewrite Nat.mul_1_l in Hle. lia.
Qed.

(* if d divides both numbers then d divides their difference *)
Lemma u5c_dvd_diff : forall d a b : nat,
  Nat.divide d a -> Nat.divide d b -> Nat.divide d (a - b).
Proof.
  intros d a b [x Hx] [y Hy]. exists (x - y).
  rewrite Nat.mul_sub_distr_r. lia.
Qed.

(* if every common factor of two numbers is one then their gcd is one *)
Lemma u5c_gcd_one_of_dvd : forall a b : nat,
  (forall e : nat, Nat.divide e a -> Nat.divide e b -> e = 1) ->
  Nat.gcd a b = 1.
Proof.
  intros a b H. apply H.
  - apply Nat.gcd_divide_l.
  - apply Nat.gcd_divide_r.
Qed.

Lemma u5c_pow2_ge2 : forall m : nat, 1 <= m -> 2 <= 2 ^ m.
Proof.
  intros m Hm.
  assert (Hr : 2 ^ m = 2 * 2 ^ (m - 1)) by (rewrite <- prs_pow_succ; f_equal; lia).
  (* interface-generation alignment per UpReqMisc5B precedent: the
     Set-face NatLe certificate (prs_pow2_pos) is replaced by the
     Stdlib-derivable Prop positivity that the arithmetic tail consumes *)
  assert (Hp0 : 2 ^ (m - 1) <> 0) by (apply Nat.pow_nonzero; lia).
  lia.
Qed.

Lemma u5c_pow2_ge_succ : forall n : nat, 2 ^ n >= n + 1.
Proof.
  induction n as [|n IH].
  - simpl. lia.
  - rewrite prs_pow_succ.
    assert (H2 : 2 * (n + 1) <= 2 * 2 ^ n) by (apply Nat.mul_le_mono_l; lia).
    lia.
Qed.

(* the adjacent powers 2^m and 2^m − 1 are coprime *)
Lemma u5c_coprime_pow2_prev : forall m : nat, 1 <= m ->
  Nat.gcd (2 ^ m) (2 ^ m - 1) = 1.
Proof.
  intros m Hm. apply u5c_gcd_one_of_dvd. intros e He1 He2.
  (* interface-generation alignment per UpReqMisc5B precedent: the
     Set-face NatLe certificate (prs_pow2_pos) is replaced by the
     Stdlib-derivable Prop positivity that the arithmetic tail consumes *)
  assert (Hpos : 1 <= 2 ^ m)
    by (assert (Hz : 2 ^ m <> 0) by (apply Nat.pow_nonzero; lia); lia).
  destruct He1 as [k Hk].
  assert (He11 : 1 <= e) by lia.
  apply (u5c_dvd_sub_gap e (2 ^ m) Hpos He11).
  - exists k. exact Hk.
  - exact He2.
Qed.

(* 2^m and the half-step gap 2^(m−1) − 1 are coprime (m ≥ 2) *)
Lemma u5c_coprime_pow2_half : forall m : nat, 2 <= m ->
  Nat.gcd (2 ^ m) (2 ^ (m - 1) - 1) = 1.
Proof.
  intros m Hm. apply u5c_gcd_one_of_dvd. intros e He1 He2.
  (* interface-generation alignment per UpReqMisc5B precedent: the
     Set-face NatLe certificate (prs_pow2_pos) is replaced by the
     Stdlib-derivable Prop positivity that the arithmetic tail consumes *)
  assert (Hpos : 1 <= 2 ^ m)
    by (assert (Hz : 2 ^ m <> 0) by (apply Nat.pow_nonzero; lia); lia).
  destruct He1 as [k Hk].
  assert (He11 : 1 <= e) by lia.
  destruct He2 as [w Hw].
  assert (Hp2 : 2 ^ m = 2 * 2 ^ (m - 1)) by (rewrite <- prs_pow_succ; f_equal; lia).
  assert (Hs : 2 ^ (m - 1) = e * w + 1) by lia.
  assert (Hw2 : 2 ^ m - 2 = e * (2 * w)) by (rewrite Hp2, Hs; lia).
  assert (Hd2x : Nat.divide e (2 ^ m - (2 ^ m - 2))).
  { apply (u5c_dvd_diff e (2 ^ m) (2 ^ m - 2)).
    - exists k. exact Hk.
    - exists (2 * w). lia. }
  assert (Heq : 2 ^ m - (2 ^ m - 2) = 2) by lia.
  rewrite Heq in Hd2x.
  destruct Hd2x as [u Hu].
  destruct u as [|u'].
  - simpl in Hu. lia.
  - assert (Hge : 1 * e <= S u' * e) by (apply Nat.mul_le_mono_r; lia).
    rewrite Nat.mul_1_l in Hge.
    assert (Hodd : e <> 2).
    { intro Heq2. rewrite Heq2 in Hw.
      assert (Hhalf : 2 ^ (m - 1) = 2 * 2 ^ (m - 2))
        by (rewrite <- prs_pow_succ; f_equal; lia).
      (* interface-generation alignment per UpReqMisc5B precedent: the
         Set-face NatLe certificate (prs_pow2_pos) is replaced by the
         Stdlib-derivable Prop positivity that lia consumes *)
      assert (Hp22 : 1 <= 2 ^ (m - 2))
        by (assert (Hz : 2 ^ (m - 2) <> 0) by (apply Nat.pow_nonzero; lia); lia).
      rewrite Hhalf in Hw. lia. }
    lia.
Qed.

(* 2^m − 1 and 2^(m−1) − 1 are coprime (m ≥ 2): their difference is 1 *)
Lemma u5c_coprime_prev_half : forall m : nat, 2 <= m ->
  Nat.gcd (2 ^ m - 1) (2 ^ (m - 1) - 1) = 1.
Proof.
  intros m Hm. apply u5c_gcd_one_of_dvd. intros e He1 He2.
  destruct He1 as [k Hk]. destruct He2 as [w Hw].
  assert (Hp2 : 2 ^ m = 2 * 2 ^ (m - 1)) by (rewrite <- prs_pow_succ; f_equal; lia).
  assert (Hs : 2 ^ (m - 1) = e * w + 1).
  { (* interface-generation alignment per UpReqMisc5B precedent: the
       Set-face NatLe certificate is replaced by the Stdlib-derivable
       Prop positivity; the divisibility product is commuted for lia *)
    assert (Hp1 : 1 <= 2 ^ (m - 1))
      by (assert (Hz : 2 ^ (m - 1) <> 0) by (apply Nat.pow_nonzero; lia); lia).
    rewrite (Nat.mul_comm w e) in Hw. lia. }
  assert (Hw2 : 2 ^ m - 2 = e * (2 * w)) by (rewrite Hp2, Hs; lia).
  assert (Hpos : 1 <= 2 ^ m - 1).
  { (* interface-generation alignment per UpReqMisc5B precedent: the
       Set-face NatLe certificate is replaced by the file-local
       Prop-face [u5c_pow2_ge2] *)
    assert (H2m : 2 <= 2 ^ m) by (apply u5c_pow2_ge2; lia).
    lia. }
  apply (u5c_dvd_sub_gap e (2 ^ m - 1) Hpos).
  - lia.
  - exists k. exact Hk.
  - exists (2 * w). lia.
Qed.

(* the power-gap product bound: 2^m ≤ (2^m − 1)(2^(m−1) − 1) for m ≥ 3 *)
Lemma u5c_pow_gap_prod : forall m : nat, 3 <= m ->
  2 ^ m <= (2 ^ m - 1) * (2 ^ (m - 1) - 1).
Proof.
  intros m. induction m as [|m IH]; intro Hm.
  - lia.
  - destruct (le_lt_dec 3 m) as [Hle | Hlt].
    + specialize (IH Hle).
      rewrite prs_pow_succ.
      replace (S m - 1) with m by lia.
      remember (2 ^ m) as A eqn:HA.
      remember (2 ^ m - 1) as X eqn:HX.
      remember (2 ^ (m - 1) - 1) as Y eqn:HY.
      assert (HmA : 1 <= m) by lia.
      pose proof (u5c_pow2_ge2 m HmA) as H2A.
      rewrite <- HA in H2A.
      assert (HAX : A = X + 1) by lia.
      assert (HYLE : Y <= X).
      { assert (Hp : 2 ^ (m - 1) <= 2 ^ m) by (apply Nat.pow_le_mono_r; lia). lia. }
      assert (E1 : X * (2 * Y) <= X * (2 * X + 1)) by (apply Nat.mul_le_mono_l; lia).
      assert (H2 : 2 * A <= 2 * (X * Y)).
      { assert (HXY : (A - 1) * Y = X * Y) by (f_equal; lia).
        lia. }
      assert (E2 : 2 * (X * Y) = X * (2 * Y)) by ring.
      replace (2 * A - 1) with (2 * X + 1) by lia.
      replace (A - 1) with X by lia.
      rewrite (Nat.mul_comm (2 * X + 1) X).
      lia.
    + assert (Hm2 : m = 2) by lia. subst m. cbv. lia.
Qed.

(* the lcm bound: lcm(1..2^m) ≥ 4^m for m ≥ 3, through the divisibility
   transfer over the product of the coprime triple 2^m, 2^m − 1, 2^(m−1) − 1 *)
Lemma pzs_lcm_ge_pow4 : forall m : nat, 3 <= m ->
  2 ^ (2 * m) <= hl_lcm_upto (2 ^ m).
Proof.
  intros m Hm.
  assert (Hm2 : 2 <= m) by lia.
  (* interface-generation alignment per UpReqMisc5B precedent: the
     Set-face NatLe certificate is replaced by the Stdlib-derivable
     Prop positivity *)
  assert (HN1 : 1 <= 2 ^ m)
    by (assert (Hz : 2 ^ m <> 0) by (apply Nat.pow_nonzero; lia); lia).
  assert (HN2 : 2 <= 2 ^ m) by (apply u5c_pow2_ge2; lia).
  assert (Hk31 : 1 <= 2 ^ (m - 1) - 1).
  { assert (Hm1 : 1 <= m - 1) by lia.
    pose proof (u5c_pow2_ge2 (m - 1) Hm1) as Hh. lia. }
  assert (Hk3N : 2 ^ (m - 1) - 1 <= 2 ^ m)
    by (apply Nat.le_trans with (2 ^ (m - 1));
        [lia | apply Nat.pow_le_mono_r; lia]).
  assert (Hd1 : Nat.divide (2 ^ m) (hl_lcm_upto (2 ^ m)))
    by (apply hl_lcm_divide_all; lia).
  assert (Hd2 : Nat.divide (2 ^ m - 1) (hl_lcm_upto (2 ^ m)))
    by (apply hl_lcm_divide_all; lia).
  assert (Hd3 : Nat.divide (2 ^ (m - 1) - 1) (hl_lcm_upto (2 ^ m)))
    by (apply hl_lcm_divide_all; lia).
  assert (Hg1 : Nat.gcd (2 ^ m) (2 ^ m - 1) = 1) by (apply u5c_coprime_pow2_prev; lia).
  assert (Hg2 : Nat.gcd (2 ^ m) (2 ^ (m - 1) - 1) = 1) by (apply u5c_coprime_pow2_half; lia).
  assert (Hg3 : Nat.gcd (2 ^ m - 1) (2 ^ (m - 1) - 1) = 1)
    by (apply u5c_coprime_prev_half; lia).
  assert (HgN : Nat.gcd (2 ^ m * (2 ^ m - 1)) (2 ^ (m - 1) - 1) = 1).
  { rewrite Nat.gcd_comm.
    (* interface-generation alignment per UpReqMisc5B precedent: the
       plm_coprime_mul conclusion is the Set-face Id, eliminated inline
       (singleton match) into the Prop goal *)
    assert (Hid : S01_BaseRing.Id (Nat.gcd (2 ^ (m - 1) - 1) (2 ^ m * (2 ^ m - 1))) 1).
    { apply plm_coprime_mul.
      - rewrite Nat.gcd_comm. exact Hg2.
      - rewrite Nat.gcd_comm. exact Hg3. }
    exact (match Hid in S01_BaseRing.Id _ z
           return Nat.gcd (2 ^ (m - 1) - 1) (2 ^ m * (2 ^ m - 1)) = z
           with S01_BaseRing.id_refl => eq_refl end). }
  assert (HdN : Nat.divide (2 ^ m * (2 ^ m - 1)) (hl_lcm_upto (2 ^ m)))
    by (apply plm_dvd_mul_coprime; assumption).
  assert (HdF : Nat.divide (2 ^ m * (2 ^ m - 1) * (2 ^ (m - 1) - 1))
                  (hl_lcm_upto (2 ^ m)))
    by (apply plm_dvd_mul_coprime; assumption).
  destruct HdF as [c Hc].
  assert (HL1 : 1 <= hl_lcm_upto (2 ^ m)).
  { (* interface-generation alignment per UpReqMisc5B precedent: the
       Set-face NatLe certificate (plq_lcm_pos) is eliminated inline
       (singleton match, the S07 Id_eq route) to the Prop face *)
    pose proof (plq_lcm_pos (2 ^ m)) as HN.
    apply Nat.leb_le.
    exact (match HN in S01_BaseRing.Id _ z
           return (Nat.leb 1 (hl_lcm_upto (2 ^ m)) = z)
           with S01_BaseRing.id_refl => eq_refl end). }
  assert (Hc1 : 1 <= c).
  { destruct c as [|c'].
    - rewrite Nat.mul_0_l in Hc. lia.
    - lia. }
  assert (Hlow : 2 ^ m * (2 ^ m - 1) * (2 ^ (m - 1) - 1) <= hl_lcm_upto (2 ^ m)).
  { rewrite Hc.
    assert (Hle : 2 ^ m * (2 ^ m - 1) * (2 ^ (m - 1) - 1) * 1
                  <= 2 ^ m * (2 ^ m - 1) * (2 ^ (m - 1) - 1) * c)
      by (apply Nat.mul_le_mono_l; lia).
    rewrite Nat.mul_1_r in Hle. lia. }
  assert (Hsq : 2 ^ m * 2 ^ m = 2 ^ (2 * m))
    by (rewrite <- Nat.pow_add_r; f_equal; lia).
  assert (Hgap : 2 ^ m <= (2 ^ m - 1) * (2 ^ (m - 1) - 1)) by (apply u5c_pow_gap_prod; lia).
  assert (Hmul : 2 ^ m * 2 ^ m <= 2 ^ m * (2 ^ m - 1) * (2 ^ (m - 1) - 1)).
  { assert (H2 : 2 ^ m * 2 ^ m
                 <= (2 ^ m - 1) * (2 ^ (m - 1) - 1) * 2 ^ m)
      by (apply Nat.mul_le_mono_r; exact Hgap).
    assert (Er : 2 ^ m * (2 ^ m - 1) * (2 ^ (m - 1) - 1)
                 = (2 ^ m - 1) * (2 ^ (m - 1) - 1) * 2 ^ m) by ring.
    lia. }
  lia.
Qed.

(* ---- §2 sums and products over the prime table ---- *)

(* the prime reciprocal partial sum at scale C: Σ_{p≤n} ⌊C/p⌋ (termwise nat floors) *)
Definition pzs_rsum (n C : nat) : nat :=
  pze_lsum (fun p => C / p) (pen_primes_upto n).
(* the prime product ∏_{p≤n} p and the companion product ∏_{p≤n}(p−1) *)
Definition pzs_pprod (n : nat) : nat := pze_prod (fun p => p) (pen_primes_upto n).
Definition pzs_qprod (n : nat) : nat := pze_prod (fun p => p - 1) (pen_primes_upto n).

Lemma pzs_prod_app : forall (f : nat -> nat) (l1 l2 : list nat),
  pze_prod f (l1 ++ l2) = pze_prod f l1 * pze_prod f l2.
Proof.
  intros f l1. induction l1 as [|a t IH]; intro l2.
  - change (pze_prod f (nil ++ l2)) with (pze_prod f l2).
    rewrite pze_prod_nil. lia.
  - rewrite <- app_comm_cons. rewrite !pze_prod_cons. rewrite IH. ring.
Qed.

Lemma pzs_len_app : forall (l1 l2 : list nat),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros l1. induction l1 as [|a t IH]; intro l2.
  - reflexivity.
  - simpl. rewrite IH. lia.
Qed.

(* interval decomposition of the prime table: for d ≤ N the table is the prefix ++ the (d, N] segment *)
(* the Set-face carrier for pzs_pen_split (statement-face carrier re-cast per 361-red
   prescription: the original mixed conjunction is distributed over the constructor
   component slots; the prime condition is carried in its Prop realization,
   the Set-face pr_prime certificate being convertible to it at the leaves through
   the inline singleton-match bridge) *)
Inductive pzs_pen_split_c (N d : nat) : Set :=
| pzs_pen_split_cI :
    forall l : list nat,
      pen_primes_upto N = pen_primes_upto d ++ l ->
      (forall p : nat, In p l ->
         d < p /\ p <= N /\ 2 <= p /\
         (forall d0 : nat, 2 <= d0 -> S d0 <= p -> p mod d0 <> 0)) ->
      length l <= N ->
      pzs_pen_split_c N d.

Lemma pzs_pen_split : forall (N d : nat), d <= N -> pzs_pen_split_c N d.
Proof.
  intros N. induction N as [|N IH]; intros d Hd.
  - assert (Hd0 : d = 0) by lia. subst d.
    apply pzs_pen_split_cI with (l := nil).
    + reflexivity.
    + intros p Hp. destruct Hp.
    + simpl. lia.
  - destruct (Nat.eq_dec d (S N)) as [Heq | Hne].
    + subst d. apply pzs_pen_split_cI with (l := nil).
      * rewrite app_nil_r; reflexivity.
      * intros p Hp. destruct Hp.
      * simpl. lia.
    + assert (HdN : d <= N) by lia.
      destruct (IH d HdN) as [l H1 H2 H3].
      destruct (pr_prime_bool (S N)) as [|] eqn:Eb.
      * apply pzs_pen_split_cI with (l := l ++ S N :: nil).
        -- rewrite pen_primes_upto_S. rewrite Eb. rewrite H1. rewrite app_assoc.
           reflexivity.
        -- intros p Hp. apply in_app_or in Hp. destruct Hp as [Hp | Hp].
           ++ apply H2 in Hp. destruct Hp as [H4 [H5 [H7 H8]]].
              split; [lia | split; [lia | split; [exact H7 | exact H8]]].
           ++ simpl in Hp. destruct Hp as [Heqp | Hf].
              ** subst p.
                 (* interface-generation alignment per UpReqMisc5B
                    precedent: the Set-face pr_prime certificate of the
                    appended prime is realized in Prop at the leaves
                    (NatLe through the singleton-match bridge, the
                    divisibility Id through the same route) *)
                 assert (Hpp : pr_prime (S N))
                   by (apply pr_prime_bool_true; exact Eb).
                 unfold pr_prime in Hpp. destruct Hpp as [Hp2 Hp3].
                 pose proof (match Hp2 in S01_BaseRing.Id _ z
                             return (Nat.leb 2 (S N) = z)
                             with S01_BaseRing.id_refl => eq_refl
                             end) as HL2.
                 apply Nat.leb_le in HL2.
                 assert (Hdv : forall d0 : nat, 2 <= d0 -> S d0 <= S N ->
                           S N mod d0 <> 0).
                 { intros d0 Hd0 Hd1.
                   assert (HL0 : S01_BaseRing.NatLe 2 d0).
                   { unfold S01_BaseRing.NatLe. apply Nat.leb_le in Hd0.
                     rewrite Hd0. apply S01_BaseRing.id_refl. }
                   assert (HL1 : S01_BaseRing.NatLe (S d0) (S N)).
                   { unfold S01_BaseRing.NatLe. apply Nat.leb_le in Hd1.
                     rewrite Hd1. apply S01_BaseRing.id_refl. }
                   pose proof (match Hp3 d0 HL0 HL1 in S01_BaseRing.Id _ z
                               return (Nat.eqb (S N mod d0) 0 = z)
                               with S01_BaseRing.id_refl => eq_refl
                               end) as HE.
                   apply Nat.eqb_neq in HE. exact HE. }
                 split; [lia | split; [lia | split; [exact HL2 | exact Hdv]]].
              ** destruct Hf.
        -- rewrite pzs_len_app. simpl. lia.
      * apply pzs_pen_split_cI with (l := l).
        -- rewrite pen_primes_upto_S. rewrite Eb.
           change (if false then S N :: nil else nil) with nil.
           rewrite H1, app_nil_r. reflexivity.
        -- intros p Hp. apply H2 in Hp. destruct Hp as [H4 [H5 [H7 H8]]].
           split; [exact H4 | split; [lia | split; [exact H7 | exact H8]]].
        -- lia.
Qed.

(* ---- §3 the per-prime cost and the product-versus-sum suppression ---- *)

(* the per-prime cost bound: (p−1)·(2⌊C/p⌋+2) ≥ C for p ≥ 2 *)
Lemma pzs_cost_ge : forall p C : nat, 2 <= p -> 1 <= C ->
  C <= (p - 1) * (2 * (C / p) + 2).
Proof.
  intros p C Hp HC.
  assert (Hp0 : p <> 0) by lia.
  pose proof (Nat.div_mod C p Hp0) as Hdm.
  pose proof (Nat.mod_upper_bound C p Hp0) as Hmb.
  destruct p as [|p'].
  - lia.
  - assert (E1 : p' * (2 * (C / S p')) + 2 * (C / S p')
                 = 2 * (S p' * (C / S p'))) by ring.
    assert (E2 : 2 * (C / S p') <= S p' * (C / S p'))
      by (apply Nat.mul_le_mono_r; lia).
    assert (E3 : p' * (2 * (C / S p') + 2)
                 = p' * (2 * (C / S p')) + p' * 2) by ring.
    replace (S p' - 1) with p' by lia.
    lia.
Qed.

(* the product-versus-sum inequality (the nat integral form):
   ∏_{p∈l} p · (C − Σ_{p∈l}(2⌊C/p⌋+2)) ≤ C · ∏_{p∈l}(p−1); that is, when
   Σ(2⌊C/p⌋+2) < C, ∏ p / ∏(p−1) ≤ C/(C−Σa), the per-prime bound
   a_p ≥ 1/(p−1) holding term by term *)
Lemma pzs_prodsum : forall (l : list nat) (C : nat),
  1 <= C ->
  (forall p : nat, In p l -> 2 <= p) ->
  pze_prod (fun p => p) l * (C - pze_lsum (fun p => 2 * (C / p) + 2) l)
  <= C * pze_prod (fun p => p - 1) l.
Proof.
  intros l. induction l as [|a t IH]; intros C HC Hall.
  - rewrite pze_prod_nil, pze_prod_nil.
    change (pze_lsum (fun p => 2 * (C / p) + 2) nil) with 0.
    lia.
  - rewrite pze_prod_cons, pze_prod_cons. cbn beta.
    change (pze_lsum (fun p => 2 * (C / p) + 2) (a :: t))
      with (2 * (C / a) + 2 + pze_lsum (fun p => 2 * (C / p) + 2) t).
    remember (pze_prod (fun p => p) t) as X eqn:EX.
    remember (pze_prod (fun p => p - 1) t) as Y eqn:EY.
    remember (pze_lsum (fun p => 2 * (C / p) + 2) t) as S1 eqn:ES1.
    assert (HIH : X * (C - pze_lsum (fun p => 2 * (C / p) + 2) t) <= C * Y).
    { apply IH; [exact HC | intros p Hp; apply Hall; right; exact Hp]. }
    rewrite <- ES1 in HIH.
    assert (Ha : 2 <= a) by (apply Hall; left; reflexivity).
    assert (Ha2 : C <= (a - 1) * (2 * (C / a) + 2)) by (apply pzs_cost_ge; assumption).
    destruct (le_lt_dec (S1 + (2 * (C / a) + 2)) C) as [Hge | Hlt].
    + remember (C - S1) as T eqn:ET.
      assert (Ha2le : 2 * (C / a) + 2 <= T) by lia.
      assert (HWleV : (a - 1) * (2 * (C / a) + 2) <= a * (2 * (C / a) + 2))
        by (apply Nat.mul_le_mono_r; lia).
      assert (HTle : T <= a * (2 * (C / a) + 2)) by lia.
      assert (Hle2 : a * (2 * (C / a) + 2) <= a * T)
        by (apply Nat.mul_le_mono_l; exact Ha2le).
      assert (E0 : a * (T - (2 * (C / a) + 2)) + a * (2 * (C / a) + 2) = a * T).
      { rewrite Nat.mul_sub_distr_l. apply Nat.sub_add. exact Hle2. }
      assert (E0b : (a - 1) * T + T = a * T).
      { destruct a as [|a'].
        - lia.
        - replace (S a' - 1) with a' by lia. ring. }
      assert (E1 : a * (T - (2 * (C / a) + 2)) <= (a - 1) * T) by lia.
      assert (E2 : X * (a * (T - (2 * (C / a) + 2))) <= X * ((a - 1) * T))
        by (apply Nat.mul_le_mono_l; exact E1).
      assert (E3 : X * ((a - 1) * T) = (a - 1) * (X * T)).
      { rewrite !Nat.mul_sub_distr_r, !Nat.mul_sub_distr_l. f_equal; ring. }
      assert (E4 : (a - 1) * (X * T) <= (a - 1) * (C * Y))
        by (apply Nat.mul_le_mono_l; exact HIH).
      assert (E5 : (a - 1) * (C * Y) = C * ((a - 1) * Y)).
      { rewrite !Nat.mul_sub_distr_r, !Nat.mul_sub_distr_l. f_equal; ring. }
      assert (E6 : (a * X) * (T - (2 * (C / a) + 2))
                   = X * (a * (T - (2 * (C / a) + 2)))).
      { rewrite !Nat.mul_sub_distr_l. f_equal; ring. }
      assert (E7 : (a * X) * (C - (2 * (C / a) + 2 + S1))
                   = (a * X) * (T - (2 * (C / a) + 2))) by (f_equal; lia).
      rewrite E7. lia.
    + assert (Hz : C - (2 * (C / a) + 2 + S1) = 0).
      { apply (proj2 (Nat.sub_0_le _ _)). lia. }
      rewrite Hz. lia.
Qed.

Lemma pzs_lsum_const : forall (k : nat) (l : list nat),
  pze_lsum (fun _ => k) l = k * length l.
Proof.
  intros k l. induction l as [|a t IH].
  - change (pze_lsum (fun _ => k) nil) with 0.
    change (length (@nil nat)) with 0.
    rewrite Nat.mul_0_r. reflexivity.
  - change (pze_lsum (fun _ => k) (a :: t)) with (k + pze_lsum (fun _ => k) t).
    change (length (a :: t)) with (S (length t)).
    rewrite IH. lia.
Qed.

Lemma pzs_lsum_cost_split : forall (C : nat) (l : list nat),
  pze_lsum (fun p => 2 * (C / p) + 2) l
  = 2 * pze_lsum (fun p => C / p) l + 2 * length l.
Proof.
  intros C l. induction l as [|a t IH]; [reflexivity |].
  change (pze_lsum (fun p => 2 * (C / p) + 2) (a :: t))
    with (2 * (C / a) + 2 + pze_lsum (fun p => 2 * (C / p) + 2) t).
  change (pze_lsum (fun p => C / p) (a :: t))
    with (C / a + pze_lsum (fun p => C / p) t).
  rewrite IH.
  change (length (a :: t)) with (S (length t)).
  ring.
Qed.

Lemma pzs_lsum_scale : forall (t C : nat) (l : list nat),
  1 <= t -> t * pze_lsum (fun p => C / p) l <= pze_lsum (fun p => t * C / p) l.
Proof.
  intros t C l Ht. induction l as [|a rest IH].
  - change (pze_lsum (fun p => C / p) nil) with 0.
    change (pze_lsum (fun p => t * C / p) nil) with 0.
    lia.
  - change (pze_lsum (fun p => C / p) (a :: rest))
      with (C / a + pze_lsum (fun p => C / p) rest).
    change (pze_lsum (fun p => t * C / p) (a :: rest))
      with (t * C / a + pze_lsum (fun p => t * C / p) rest).
    assert (Hterm : t * (C / a) <= t * C / a)
      by apply Nat.Div0.div_mul_le.
    lia.
Qed.

Lemma pzs_rsum_scale : forall (n t C : nat),
  1 <= t -> t * pzs_rsum n C <= pzs_rsum n (t * C).
Proof.
  intros n t C Ht. unfold pzs_rsum. apply pzs_lsum_scale. exact Ht.
Qed.

(* ---- §4 numerical smoke tests (small-instance cbv, axiom-free) ---- *)

Lemma pzs_rsum_10_8 : pzs_rsum 10 8 = 8.
Proof. cbv. reflexivity. Qed.

Lemma pzs_rsum_8_128 : pzs_rsum 8 128 = 149.
Proof. cbv. reflexivity. Qed.

Lemma pzs_pprod_10 : pzs_pprod 10 = 210.
Proof. cbv. reflexivity. Qed.

Lemma pzs_qprod_10 : pzs_qprod 10 = 48.
Proof. cbv. reflexivity. Qed.

(* a nontrivial numerical instance of the product-versus-sum inequality:
   Σ(2⌊30/3⌋+2) = 22 < 30 and 3·(30−22) = 24 ≤ 30·2 = 60 (small values
   avoid the deep terms of the unary nat representation) *)
Lemma pzs_prodsum_smoke :
  pze_prod (fun p => p) (3 :: nil)
  * (30 - pze_lsum (fun p => 2 * (30 / p) + 2) (3 :: nil))
  <= 30 * pze_prod (fun p => p - 1) (3 :: nil).
Proof. cbv. lia. Qed.

Lemma pzs_cost_smoke : (3 - 1) * (2 * (30 / 3) + 2) = 44.
Proof. cbv. reflexivity. Qed.

(* the lcm bound: one numerical instance and one theorem instance *)
Lemma pzs_lcm_smoke_3 : 2 ^ (2 * 3) <= hl_lcm_upto (2 ^ 3).
Proof. cbv. lia. Qed.

Lemma pzs_lcm_bridge_smoke : 2 ^ (2 * 5) <= hl_lcm_upto (2 ^ 5).
Proof. apply pzs_lcm_ge_pow4. lia. Qed.

(* a numerical instance of the product-ratio bound: ∏_{p≤5}p = 30 ≤ 4·∏_{p≤5}(p−1) = 32 *)
Lemma pzs_reverse_shape_smoke : pzs_pprod 5 <= 4 * pzs_qprod 5.
Proof. cbv. lia. Qed.

(* ---- §5 the Euler-Harm transfer and the harmonic rescaling ---- *)

Lemma pzs_qprod_pos : forall n : nat, 1 <= pzs_qprod n.
Proof.
  intro n. unfold pzs_qprod. apply pze_prod_pos. intros x Hx. cbn beta.
  destruct (fst (pen_in_primes_upto x n) Hx) as [Hpp _].
  destruct Hpp as [Hp2 _].
  pose proof (S01_BaseRing.NatLe_drop 2 x Hp2) as H2x.
  lia.
Qed.

Lemma pzs_pprod_pos : forall n : nat, 1 <= pzs_pprod n.
Proof.
  intro n. unfold pzs_pprod. apply pze_prod_pos. intros x Hx. cbn beta.
  destruct (fst (pen_in_primes_upto x n) Hx) as [Hpp _].
  destruct Hpp as [Hp2 _].
  pose proof (S01_BaseRing.NatLe_drop 2 x Hp2) as H2x.
  lia.
Qed.

(* the Euler-Harm suppression: ∏(p−1)·H_n ≤ ∏p (pze_euler_harm) implies
   that the product-ratio bound B dominates the harmonic carrier sum at
   the same scale *)
Lemma pzs_hsum_le_of_pprod : forall (N B : nat),
  1 <= B -> pzs_pprod N <= B * pzs_qprod N ->
  prs_hsum N (hl_lcm_upto N) <= B * hl_lcm_upto N.
Proof.
  intros N B HB1 HB.
  pose proof (pze_euler_harm N) as He.
  change (pze_prod (fun p => p - 1) (pen_primes_upto N)) with (pzs_qprod N) in He.
  change (pze_prod (fun p => p) (pen_primes_upto N)) with (pzs_pprod N) in He.
  assert (HQ : 1 <= pzs_qprod N) by apply pzs_qprod_pos.
  assert (E : hl_lcm_upto N * pzs_pprod N <= hl_lcm_upto N * (B * pzs_qprod N))
    by (apply Nat.mul_le_mono_l; exact HB).
  assert (E2 : hl_lcm_upto N * (B * pzs_qprod N)
               = (hl_lcm_upto N * B) * pzs_qprod N) by ring.
  assert (E3 : pzs_qprod N * prs_hsum N (hl_lcm_upto N)
               <= (hl_lcm_upto N * B) * pzs_qprod N).
  { apply Nat.le_trans with (hl_lcm_upto N * pzs_pprod N).
    - exact He.
    - lia. }
  rewrite (Nat.mul_comm (pzs_qprod N) (prs_hsum N (hl_lcm_upto N))) in E3.
  assert (Hpos : 0 < pzs_qprod N) by lia.
  apply (proj2 (Nat.mul_le_mono_pos_r (prs_hsum N (hl_lcm_upto N))
                  (hl_lcm_upto N * B) (pzs_qprod N) Hpos)) in E3.
  lia.
Qed.

(* harmonic rescaling (downward): q·S ≤ L gives q·Σ⌊S/k⌋ ≤ Σ⌊L/k⌋ *)
Lemma pzs_hsum_scale_dn : forall (n q S1 L : nat),
  q * S1 <= L -> q * prs_hsum n S1 <= prs_hsum n L.
Proof.
  intros n q S1 L Hq. induction n as [|n IH].
  - simpl. lia.
  - rewrite !prs_hsum_S.
    assert (Ht : q * (S1 / S n) <= L / S n).
    { assert (H1 : q * (S1 / S n) <= (q * S1) / S n).
      { apply Nat.div_le_lower_bound; [lia |].
        rewrite (prs_mul_swap (S n) q (S1 / S n)).
        apply Nat.mul_le_mono_l.
        assert (H1n : 1 <= S n) by lia.
        pose proof (S01_BaseRing.NatLe_lift 1 (S n) H1n) as HL1.
        pose proof (prs_mul_div_le (S n) S1 HL1) as Hmd.
        pose proof (S01_BaseRing.NatLe_drop (S n * (S1 / S n)) S1 Hmd) as Hmd2.
        exact Hmd2. }
      assert (H2 : (q * S1) / S n <= L / S n)
        by (apply Nat.div_le_mono; [lia | exact Hq]).
      lia. }
    lia.
Qed.

(* ---- §6 the Mertens reverse nat finite form (the main lemma added by this module) ---- *)

(* the [1, d] segment product-ratio bound: ∏_{p≤d} p ≤ (⌊ratio⌋+1)·∏_{p≤d}(p−1) *)
Definition pzs_B (d : nat) : nat := pzs_pprod d / pzs_qprod d + 1.

Lemma pzs_B_spec : forall d : nat, 1 <= d -> pzs_pprod d <= pzs_B d * pzs_qprod d.
Proof.
  intros d Hd. unfold pzs_B.
  assert (HQ : 1 <= pzs_qprod d) by apply pzs_qprod_pos.
  assert (Hp0 : pzs_qprod d <> 0) by lia.
  pose proof (Nat.div_mod (pzs_pprod d) (pzs_qprod d) Hp0) as Hdm.
  pose proof (Nat.mod_upper_bound (pzs_pprod d) (pzs_qprod d) Hp0) as Hmb.
  assert (E : (pzs_pprod d / pzs_qprod d + 1) * pzs_qprod d
              = pzs_qprod d * (pzs_pprod d / pzs_qprod d) + pzs_qprod d) by ring.
  lia.
Qed.

(* the Mertens reverse form (the nat finite-segment shape): when the prime
   reciprocal sum at scale C gains less than C over [d, N] (at every point
   4·Σ < C + 4·Σ_d), the product over the whole span is dominated by
   4·B·∏(p−1).  Argument: on the interval segment the product-versus-sum
   inequality gives ∏_seg p ≤ 4·∏_seg(p−1), multiplied with the base
   segment ratio bound. *)
Theorem pzs_mertens_reverse : forall (d N B C : nat),
  2 <= d -> d <= N -> 1 <= C ->
  pzs_pprod d <= B * pzs_qprod d ->
  (forall n : nat, d <= n -> n <= N -> 4 * pzs_rsum n C < C + 4 * pzs_rsum d C) ->
  8 * N <= C ->
  pzs_pprod N <= 4 * B * pzs_qprod N.
Proof.
  intros d N B C Hd2 HdN HC HB Hsum H8N.
  destruct (pzs_pen_split N d HdN) as [l H1 H2 H3].
  assert (Hsplit : pze_lsum (fun p => C / p) l + pzs_rsum d C = pzs_rsum N C).
  { unfold pzs_rsum. rewrite H1, pze_lsum_app. lia. }
  assert (Hspl : pze_prod (fun p => p) l * pzs_pprod d = pzs_pprod N).
  { unfold pzs_pprod. rewrite H1, pzs_prod_app. lia. }
  assert (Hsql : pze_prod (fun p => p - 1) l * pzs_qprod d = pzs_qprod N).
  { unfold pzs_qprod. rewrite H1, pzs_prod_app. lia. }
  assert (HCOST : pze_prod (fun p => p) l
                    * (C - pze_lsum (fun p => 2 * (C / p) + 2) l)
                  <= C * pze_prod (fun p => p - 1) l).
  { apply pzs_prodsum; [exact HC |].
    intros p Hp. destruct (H2 p Hp) as [_ [_ [H7 _]]]. exact H7. }
  assert (HCOST2 : pze_lsum (fun p => 2 * (C / p) + 2) l
                   = 2 * pze_lsum (fun p => C / p) l + 2 * length l)
    by apply pzs_lsum_cost_split.
  assert (HSEG4 : 4 * pze_lsum (fun p => C / p) l < C).
  { assert (HNn := Hsum N HdN (Nat.le_refl N)).
    unfold pzs_rsum in HNn. rewrite H1, pze_lsum_app in HNn. lia. }
  assert (HS' : C <= 4 * (C - pze_lsum (fun p => 2 * (C / p) + 2) l)).
  { rewrite HCOST2.
    assert (HX : 4 * pze_lsum (fun p => 2 * (C / p) + 2) l + C <= 4 * C) by lia.
    destruct (le_lt_dec (pze_lsum (fun p => 2 * (C / p) + 2) l) C)
      as [HleX | HgtX].
    - assert (Hadd : pze_lsum (fun p => 2 * (C / p) + 2) l
                     + (C - pze_lsum (fun p => 2 * (C / p) + 2) l) = C).
      { rewrite Nat.add_comm. apply Nat.sub_add. exact HleX. }
      lia.
    - assert (Hz : C - (2 * pze_lsum (fun p => C / p) l + 2 * length l) = 0).
      { apply (proj2 (Nat.sub_0_le _ _)). lia. }
      rewrite Hz. lia. }
  assert (Hcancel : pze_prod (fun p => p) l <= 4 * pze_prod (fun p => p - 1) l).
  { assert (Hpre : pze_prod (fun p => p) l * C
                   <= pze_prod (fun p => p) l
                      * (4 * (C - pze_lsum (fun p => 2 * (C / p) + 2) l)))
      by (apply Nat.mul_le_mono_l; exact HS').
    assert (Hc4 : 4 * (pze_prod (fun p => p) l
                         * (C - pze_lsum (fun p => 2 * (C / p) + 2) l))
                  <= 4 * (C * pze_prod (fun p => p - 1) l))
      by (apply Nat.mul_le_mono_l; exact HCOST).
    assert (Ea : pze_prod (fun p => p) l
                 * (4 * (C - pze_lsum (fun p => 2 * (C / p) + 2) l))
                 = 4 * (pze_prod (fun p => p) l
                        * (C - pze_lsum (fun p => 2 * (C / p) + 2) l))) by ring.
    assert (Eb : 4 * (C * pze_prod (fun p => p - 1) l)
                 = (4 * C) * pze_prod (fun p => p - 1) l) by ring.
    assert (Ec : (4 * C) * pze_prod (fun p => p - 1) l
                 = C * (4 * pze_prod (fun p => p - 1) l)) by ring.
    assert (HposC : 0 < C) by lia.
    assert (Hfin : pze_prod (fun p => p) l * C
                   <= (4 * pze_prod (fun p => p - 1) l) * C) by lia.
    exact (proj2 (Nat.mul_le_mono_pos_r (pze_prod (fun p => p) l)
                   (4 * pze_prod (fun p => p - 1) l) C HposC) Hfin). }
  assert (HB1 : 1 <= B).
  { destruct B as [|B'].
    - rewrite Nat.mul_0_l in HB.
      pose proof (pzs_pprod_pos d) as HX. lia.
    - lia. }
  assert (Hlast : pzs_pprod d * pze_prod (fun p => p) l
                  <= (B * pzs_qprod d) * (4 * pze_prod (fun p => p - 1) l)).
  { apply Nat.mul_le_mono; assumption. }
  assert (ET : 4 * B * pzs_qprod N
               = 4 * B * (pzs_qprod d * pze_prod (fun p => p - 1) l))
    by (f_equal; lia).
  lia.
Qed.

(* ---- §7 the decidable bounded search and the per-milestone iterative assembly ---- *)

Lemma pzs_rsum_0 : forall C : nat, pzs_rsum 0 C = 0.
Proof. intros C. reflexivity. Qed.

Lemma pzs_pen_1_nil : pen_primes_upto 1 = nil.
Proof.
  destruct (pen_primes_upto 1) as [|x l'] eqn:E.
  - reflexivity.
  - exfalso.
    assert (Hin : In x (pen_primes_upto 1)) by (rewrite E; simpl; left; reflexivity).
    destruct (fst (pen_in_primes_upto x 1) Hin) as [Hpp Hle1].
    destruct Hpp as [Hp2 _].
    pose proof (S01_BaseRing.NatLe_drop 2 x Hp2) as Hp2le.
    pose proof (S01_BaseRing.NatLe_drop x 1 Hle1) as Hle1le.
    lia.
Qed.

Lemma pzs_rsum_1 : forall C : nat, pzs_rsum 1 C = 0.
Proof.
  intros C. unfold pzs_rsum. rewrite pzs_pen_1_nil. reflexivity.
Qed.

(* the decidable bounded search: if nowhere true inside the bound is impossible, a true point inside the bound is extractable *)
Lemma pzs_find : forall (f : nat -> bool) (N : nat),
  ((forall n : nat, n <= N -> f n = false) -> False) ->
  { n : nat & And (NatLebT n N) (Id (f n) true) }.
Proof.
  intros f N. induction N as [|N IH]; intros H.
  - destruct (f 0) as [|] eqn:E0.
    + exists 0. split; [reflexivity | rewrite E0; reflexivity].
    + exfalso. apply H. intros n Hn. assert (Hn0 : n = 0) by lia. subst n. exact E0.
  - destruct (f (S N)) as [|] eqn:ES.
    + exists (S N).
      assert (E : Nat.leb (S N) (S N) = true).
      { apply (proj2 (Nat.leb_le (S N) (S N))). lia. }
      split; [unfold NatLebT; rewrite E; reflexivity | rewrite ES; reflexivity].
    + assert (Hpre : (forall n : nat, n <= N -> f n = false) -> False).
      { intros Hcontra. apply H. intros n Hn.
        destruct (Nat.eq_dec n (S N)) as [Heq | Hne].
        - subst n. exact ES.
        - apply Hcontra. lia. }
      destruct (IH Hpre) as [m [Hm Hfm]].
      assert (Hm' : m <= N).
      { unfold NatLebT in Hm. destruct (Nat.leb m N) eqn:Em in Hm; [| inversion Hm].
        apply (proj1 (Nat.leb_le m N)). exact Em. }
      assert (E : Nat.leb m (S N) = true) by (apply (proj2 (Nat.leb_le m (S N))); lia).
      exists m. split; [unfold NatLebT; rewrite E; reflexivity | exact Hfm].
Defined.

(* the per-milestone iterative step: from the layer-j milestone (n_j, C_j)
   build the layer-(j+1) milestone.  With the search bound
   N = 2^(3+32B) (B the base-segment product-ratio bound) and the scale
   enlarged to C' = C_j·(4 + 128(N+1)), the decidable search runs inside
   the bound. *)
Lemma pzs_step : forall j : nat,
  { n : nat & { C : nat & And (NatLebT 2 n)
                (And (NatLebT 1 C) (And (NatLebT (128 * (n + 1)) C)
                     (NatLebT (j * C) (4 * pzs_rsum n C)))) } } ->
  { n : nat & { C : nat & And (NatLebT 2 n)
                (And (NatLebT 1 C) (And (NatLebT (128 * (n + 1)) C)
                     (NatLebT (S j * C) (4 * pzs_rsum n C)))) } }.
Proof.
  intros j [d [Cj [Hd2 [HC1 [Hd128 Hdj]]]]].
  (* the bridge from certificate carriers to propositional reasoning (inlined in the proof) *)
  assert (Hd2p : 2 <= d).
  { unfold NatLebT in Hd2. destruct (Nat.leb 2 d) eqn:E in Hd2; [| inversion Hd2].
    apply (proj1 (Nat.leb_le 2 d)). exact E. }
  assert (HC1p : 1 <= Cj).
  { unfold NatLebT in HC1. destruct (Nat.leb 1 Cj) eqn:E in HC1; [| inversion HC1].
    apply (proj1 (Nat.leb_le 1 Cj)). exact E. }
  assert (Hd128p : 128 * (d + 1) <= Cj).
  { unfold NatLebT in Hd128.
    destruct (Nat.leb (128 * (d + 1)) Cj) eqn:E in Hd128; [| inversion Hd128].
    apply (proj1 (Nat.leb_le _ _)). exact E. }
  assert (Hdjp : j * Cj <= 4 * pzs_rsum d Cj).
  { unfold NatLebT in Hdj.
    destruct (Nat.leb (j * Cj) (4 * pzs_rsum d Cj)) eqn:E in Hdj; [| inversion Hdj].
    apply (proj1 (Nat.leb_le _ _)). exact E. }
  assert (HB : pzs_pprod d <= pzs_B d * pzs_qprod d) by (apply pzs_B_spec; lia).
  assert (HB1 : 1 <= pzs_B d) by (unfold pzs_B; lia).
  remember (pzs_B d) as B eqn:HBdef.
  remember (3 + 32 * B + d) as m eqn:Hmdef.
  remember (2 ^ m) as N eqn:HNdef.
  remember (Cj * (4 + 128 * (N + 1))) as C eqn:HCdef.
  assert (Hm3 : 3 <= m) by lia.
  assert (HdN : d <= N).
  { pose proof (u5c_pow2_ge_succ m) as Hp. lia. }
  assert (HN1 : 1 <= N)
    by (rewrite HNdef; assert (Hz : 2 ^ m <> 0) by (apply Nat.pow_nonzero; lia); lia).
  assert (HN8 : 8 <= N).
  { rewrite HNdef, Hmdef. rewrite Nat.pow_add_r, Nat.pow_add_r.
    assert (H3 : 2 ^ 3 = 8) by reflexivity.
    rewrite H3.
    assert (Hmul : 8 * 1 <= 8 * 2 ^ (32 * B))
      by (apply Nat.mul_le_mono_l;
          assert (Hz : 2 ^ (32 * B) <> 0) by (apply Nat.pow_nonzero; lia); lia).
    assert (Hm2 : 8 * 2 ^ (32 * B) <= 8 * (2 ^ (32 * B) * 2 ^ d)).
    { assert (H1 : 2 ^ (32 * B) * 1 <= 2 ^ (32 * B) * 2 ^ d).
      { apply Nat.mul_le_mono_l.
        assert (Hz : 2 ^ d <> 0) by (apply Nat.pow_nonzero; lia). lia. }
      rewrite Nat.mul_1_r in H1. lia. }
    rewrite Nat.mul_1_r in Hmul. lia. }
  assert (HC1' : 1 <= C) by (rewrite HCdef; lia).
  assert (Hd128le : 128 * (N + 1) <= C).
  { rewrite HCdef.
    apply (Nat.le_trans _ (1 * (4 + 128 * (N + 1)))).
    - rewrite Nat.mul_1_l. lia.
    - apply Nat.mul_le_mono_r. lia. }
  assert (H8N : 8 * N <= C) by lia.
  (* the milestone survives the scale enlargement *)
  assert (Hlift : j * C <= 4 * pzs_rsum d C).
  { assert (Ht1 : 1 <= 4 + 128 * (N + 1)) by lia.
    assert (Hsc := pzs_rsum_scale d (4 + 128 * (N + 1)) Cj Ht1).
    assert (Hsc2 : pzs_rsum d (Cj * (4 + 128 * (N + 1)))
                   = pzs_rsum d ((4 + 128 * (N + 1)) * Cj)) by (f_equal; ring).
    rewrite HCdef, Hsc2.
    assert (Hasso : j * (Cj * (4 + 128 * (N + 1)))
                    = (4 + 128 * (N + 1)) * (j * Cj)) by ring.
    assert (Hstep : (4 + 128 * (N + 1)) * (j * Cj)
                    <= (4 + 128 * (N + 1)) * (4 * pzs_rsum d Cj)).
    { apply Nat.mul_le_mono_l. lia. }
    lia. }
  (* by contradiction: at every point inside the bound, 4·Σ < (j+1)·C *)
  assert (Hcontra : (forall n : nat, n <= N ->
                     Nat.leb (S j * C) (4 * pzs_rsum n C) = false) -> False).
  { intros Hall.
    assert (Hlt : forall n : nat, d <= n -> n <= N ->
                  4 * pzs_rsum n C < C + 4 * pzs_rsum d C).
    { intros n Ha1 Ha2.
      assert (Hb := Hall n Ha2).
      apply Nat.leb_gt in Hb.
      lia. }
    (* Mertens reverse: the product is dominated *)
    assert (Hmert : pzs_pprod N <= 4 * B * pzs_qprod N).
    { apply (pzs_mertens_reverse d N B C).
      - lia.
      - exact HdN.
      - lia.
      - exact HB.
      - intros n Ha1 Ha2. apply Hlt; assumption.
      - lia. }
    (* Euler-Harm: the harmonic carrier sum is dominated *)
    assert (Hcap : prs_hsum N (hl_lcm_upto N) <= 4 * B * hl_lcm_upto N).
    { apply pzs_hsum_le_of_pprod; [lia | exact Hmert]. }
    (* the lcm rescaling factor q ≥ 1 and the closing chain of the contradiction *)
    assert (HS1nz : 2 ^ (2 * m) <> 0)
      by (apply Nat.pow_nonzero; lia).
    assert (Hdm : hl_lcm_upto N
                  = 2 ^ (2 * m) * (hl_lcm_upto N / 2 ^ (2 * m))
                  + hl_lcm_upto N mod 2 ^ (2 * m))
      by (apply Nat.div_mod; exact HS1nz).
    assert (Hmb : hl_lcm_upto N mod 2 ^ (2 * m) < 2 ^ (2 * m))
      by (apply Nat.mod_upper_bound; exact HS1nz).
    assert (HL := pzs_lcm_ge_pow4 m Hm3).
    rewrite <- HNdef in HL.
    remember (hl_lcm_upto N / 2 ^ (2 * m)) as q eqn:Hqdef.
    assert (Hq1 : 1 <= q).
    { destruct q as [|q'].
      - lia.
      - lia. }
    assert (Hscale : q * prs_hsum N (2 ^ (2 * m)) <= prs_hsum N (hl_lcm_upto N)).
    { apply pzs_hsum_scale_dn. lia. }
    pose proof (prs_harm_dyad m) as Hdyad.
    rewrite <- HNdef in Hdyad.
    (* interface-generation alignment per UpReqMisc5B precedent: the
       Set-face NatLe certificate is dropped to the Prop face
       (qualified NatLe_drop) *)
    pose proof (S01_BaseRing.NatLe_drop (S m * 2 ^ (2 * m))
                  (2 * prs_hsum N (2 ^ (2 * m))) Hdyad) as Hdyadle.
    assert (Hchain1 : q * S m * 2 ^ (2 * m)
                      <= 2 * (q * prs_hsum N (2 ^ (2 * m)))).
    { assert (Er : 2 * (q * prs_hsum N (2 ^ (2 * m)))
                   = q * (2 * prs_hsum N (2 ^ (2 * m)))) by ring.
      rewrite Er.
      rewrite <- (Nat.mul_assoc q (S m) (2 ^ (2 * m))).
      apply (Nat.mul_le_mono_l (S m * 2 ^ (2 * m))
                (2 * prs_hsum N (2 ^ (2 * m))) q).
      exact Hdyadle. }
    assert (Hchain2 : 2 * (q * prs_hsum N (2 ^ (2 * m)))
                      <= 8 * B * ((q + 1) * 2 ^ (2 * m))).
    { assert (E2a : 2 * (4 * B * hl_lcm_upto N) = 8 * B * hl_lcm_upto N) by ring.
      assert (E2b : 2 * prs_hsum N (hl_lcm_upto N)
                    <= 2 * (4 * B * hl_lcm_upto N))
        by (apply Nat.mul_le_mono_l; exact Hcap).
      assert (E3 : hl_lcm_upto N <= (q + 1) * 2 ^ (2 * m)) by lia.
      assert (E4 : 8 * B * hl_lcm_upto N <= 8 * B * ((q + 1) * 2 ^ (2 * m)))
        by (apply Nat.mul_le_mono_l; exact E3).
      lia. }
    assert (Hcancel : q * S m <= 8 * B * (q + 1)).
    { (* interface-generation alignment per UpReqMisc5B precedent:
         the Set-face NatLe certificate is replaced by the
         Stdlib-derivable Prop positivity *)
      assert (HS1pos : 1 <= 2 ^ (2 * m))
        by (assert (Hz : 2 ^ (2 * m) <> 0) by (apply Nat.pow_nonzero; lia); lia).
      assert (Ec1 : q * S m * 2 ^ (2 * m) = (q * S m) * 2 ^ (2 * m)) by ring.
      assert (Ec2 : 8 * B * ((q + 1) * 2 ^ (2 * m))
                    = (8 * B * (q + 1)) * 2 ^ (2 * m)) by ring.
      assert (Hfin : (q * S m) * 2 ^ (2 * m)
                     <= (8 * B * (q + 1)) * 2 ^ (2 * m)) by lia.
      exact (proj2 (Nat.mul_le_mono_pos_r (q * S m) (8 * B * (q + 1))
                     (2 ^ (2 * m)) HS1pos) Hfin). }
    assert (Hlast : S m <= 16 * B).
    { assert (E1 : 8 * B * (q + 1) = 8 * B * q + 8 * B) by ring.
      assert (E2 : 8 * B * 1 <= 8 * B * q)
        by (apply Nat.mul_le_mono_l; exact Hq1).
      rewrite Nat.mul_1_r in E2.
      assert (E3 : 8 * B * q <= 16 * B * q) by lia.
      assert (Ec3 : 16 * B * q = 2 * (8 * B * q)) by ring.
      assert (Ec4 : q * S m = S m * q) by ring.
      assert (Hfin : S m * q <= 16 * B * q) by lia.
      exact (proj2 (Nat.mul_le_mono_pos_r (S m) (16 * B) q Hq1) Hfin). }
    lia. }
  (* the witness found inside the bound *)
  destruct (pzs_find (fun n : nat => Nat.leb (S j * C) (4 * pzs_rsum n C)) N
             Hcontra) as [n' [Hn' Hb']].
  cbn beta in Hb'.
  destruct (Nat.leb (S j * C) (4 * pzs_rsum n' C)) eqn:Eb in Hb';
    [| inversion Hb'].
  assert (Eb' : S j * C <= 4 * pzs_rsum n' C)
    by (apply (proj1 (Nat.leb_le _ _)); exact Eb).
  assert (Hn'le : n' <= N).
  { unfold NatLebT in Hn'. destruct (Nat.leb n' N) eqn:E in Hn'; [| inversion Hn'].
    apply (proj1 (Nat.leb_le n' N)). exact E. }
  exists n'. exists C. repeat split.
  - destruct n' as [|[|n'']].
    + exfalso. rewrite pzs_rsum_0 in Eb'. simpl in Eb'. lia.
    + exfalso. rewrite pzs_rsum_1 in Eb'. simpl in Eb'. lia.
    + unfold NatLebT. reflexivity.
  - assert (E : Nat.leb 1 C = true) by (apply (proj2 (Nat.leb_le 1 C)); exact HC1').
    unfold NatLebT. rewrite E. reflexivity.
  - assert (E : Nat.leb (128 * (n' + 1)) C = true)
      by (apply (proj2 (Nat.leb_le _ _)); lia).
    unfold NatLebT. rewrite E. reflexivity.
  - unfold NatLebT. rewrite Eb. reflexivity.
Defined.

(* the main statement: the extractable witness of the divergence of the sum
   of prime reciprocals.  For every K there is an explicit (n, C) with
   C ≥ 128(n+1) and the scale-C prime reciprocal partial sum reaching
   K·C/4 (that is, Σ_{p≤n} 1/p ≥ K/4, the rounding loss below 1/128). *)
Theorem pzs_prime_recip_diverge : forall K : nat,
  { n : nat & { C : nat & And (NatLebT 2 n)
                (And (NatLebT 1 C) (And (NatLebT (128 * (n + 1)) C)
                     (NatLebT (K * C) (4 * pzs_rsum n C)))) } }.
Proof.
  intros K. induction K as [|K IH].
  - exists 2, 384.
    split; [unfold NatLebT; reflexivity|].
    split; [unfold NatLebT; reflexivity|].
    split; [unfold NatLebT; reflexivity| unfold NatLebT; reflexivity].
  - destruct IH as [n [C [H1 [H2 [H3 H4]]]]].
    apply pzs_step.
    exists n. exists C.
    split; [exact H1 | split; [exact H2 | split; [exact H3 | exact H4]]].
Defined.

(* ---- §8 the axiom audit (the Print Assumptions evidence face) ---- *)

Print Assumptions pzs_cost_ge.
Print Assumptions pzs_prodsum.
Print Assumptions pzs_lcm_ge_pow4.
Print Assumptions pzs_mertens_reverse.
Print Assumptions pzs_hsum_le_of_pprod.
Print Assumptions pzs_hsum_scale_dn.
Print Assumptions pzs_find.
Print Assumptions pzs_step.
Print Assumptions pzs_prime_recip_diverge.
