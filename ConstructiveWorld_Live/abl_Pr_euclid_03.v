(* ============================================================ *)
(* abl_Pr_euclid_03.v - prime-domain constructive Euclid, piece 3 *)
(* Mission. Washed carrier of the piece-3 statement set: the       *)
(*   coprimality kernel (peu_dvd_both_1: k | a and k | a+1 force   *)
(*   k = 1; peu_dvd_fact: 1 <= k <= n implies k | n!;              *)
(*   peu_coprime_core: gcd k (n!+1) = 1, equation form), the       *)
(*   witness machine peu_next n = least prime factor of n!+1       *)
(*   (projT1 over piece-1 sigT pr_min_factor_exists) with          *)
(*   pair peu_next_dvd / peu_next_prime, main theorem peu_next_gt  *)
(*   (n < peu_next n) and sigT witness peu_exists_gt (forall n,    *)
(*   {p & NatLe (S n) p And pr_prime p}, Defined). Conclusions     *)
(*   Set types (Id for equations, NatLe for order); premises keep  *)
(*   Prop faces; peu_next_pair joins two Set-carried faces (And).  *)
(* Dependencies. Stdlib (Arith.Arith, Arith.Factorial, List,       *)
(*   Bool, Lia); S01_BaseRing (Id, id_refl, NatLe, NatLe_lift,     *)
(*   NatLe_drop); abl_Pr_core_01 (pr_prime, pr_min_factor_exists). *)
(* References. lt_O_fact, Nat.mul_le_mono_r/succ_l/0_r, le_lt_dec, *)
(*   Nat.eq_dec, Nat.mul_comm/assoc, Nat.divide_trans,             *)
(*   Nat.gcd_divide_l/r, NatLe_lift, NatLe_drop, id_refl, sig proj. *)
(* Constructivity. peu_next: first-order nat projection, directly  *)
(*   extractable; kernel closes on gcd equations; negative faces   *)
(*   go through exfalso + lia; smokes close by vm_compute          *)
(*   (instances <= 6); all proofs Qed except peu_exists_gt         *)
(*   (Defined); no assumed constants (Print Assumptions block      *)
(*   at the file end).                                             *)
(* Build. Rocq 9.1.0: env.sh; unset COQLIB ROCQLIB; ulimit -s      *)
(*   65532; prebuilt S01_BaseRing.vo / abl_Pr_core_01.vo beside    *)
(*   the file; run: rocq c -native-compiler no -Q . ""             *)
(*   abl_Pr_euclid_03.v                                            *)
(* ============================================================ *)

From Stdlib Require Import Arith.Arith Arith.Factorial List Bool Lia.
Require Import S01_BaseRing (Id, id_refl, NatLe, NatLe_lift, NatLe_drop, And).
Require Import abl_Pr_core_01.

(* ---- Section 0. factorial in-registry anchor (stdlib 9.1 Arith.Factorial direct) ---- *)

Lemma peu_fact_pos : forall n : nat, NatLe 1 (fact n).
Proof. intros n. apply NatLe_lift. apply lt_O_fact. Qed.

Lemma peu_fact1_ge2 : forall n : nat, NatLe 2 (fact n + 1).
Proof. intros n. assert (H := NatLe_drop _ _ (peu_fact_pos n)). apply NatLe_lift. lia. Qed.

(* ---- Section 1. Coprimality kernel, three pieces ---- *)

(* Kernel 1: a k dividing both a and a+1 must be 1 (k | a, k | a+1 -> k = 1;
   premise-free minimal form) *)
Lemma peu_dvd_both_1 : forall k a : nat,
  Nat.divide k a -> Nat.divide k (a + 1) -> Id k 1.
Proof.
  intros k a Hd1 Hd2.
  assert (Hk : k = 1).
  { destruct Hd1 as [c Hc]. destruct Hd2 as [e He].
    destruct k as [|k'].
    - rewrite Nat.mul_0_r in Hc, He. exfalso. lia.
    - destruct (le_lt_dec e c) as [Hec|Hce].
      + exfalso.
        assert (Hle : e * (S k') <= c * (S k')).
        { apply Nat.mul_le_mono_r. exact Hec. }
        lia.
      + assert (Hsc : S c * (S k') <= e * (S k')).
        { apply Nat.mul_le_mono_r. lia. }
        rewrite Nat.mul_succ_l in Hsc.
        lia. }
  rewrite Hk. apply id_refl.
Qed.

(* Kernel 2: k divides n! (1 <= k <= n; induction on n) *)
Lemma peu_dvd_fact : forall n k : nat,
  1 <= k -> k <= n -> Nat.divide k (fact n).
Proof.
  intros n. induction n as [|n IH]; intros k Hk1 Hkn.
  - exfalso. lia.
  - destruct (Nat.eq_dec k (S n)) as [Heq|Hne].
    + subst k. exists (fact n).
      change (fact (S n)) with (S n * fact n).
      apply Nat.mul_comm.
    + assert (Hkn' : k <= n) by lia.
      destruct (IH k Hk1 Hkn') as [c Hc].
      exists (S n * c).
      change (fact (S n)) with (S n * fact n).
      rewrite Hc.
      apply Nat.mul_assoc.
Qed.

(* Kernel 3: coprimality kernel main piece -- 1 <= k <= n implies
   gcd(k, n!+1) = 1 (equation form as the constructive exit:
   the chain d = gcd divides k gives d | n!, and together with
   d | n!+1 both land in kernel 1 forcing d = 1) *)
Lemma peu_coprime_core : forall n k : nat,
  1 <= k -> k <= n -> Id (Nat.gcd k (fact n + 1)) 1.
Proof.
  intros n k Hk1 Hkn.
  apply (peu_dvd_both_1 (Nat.gcd k (fact n + 1)) (fact n)).
  - apply (Nat.divide_trans (Nat.gcd k (fact n + 1)) k (fact n)).
    + apply Nat.gcd_divide_l.
    + apply peu_dvd_fact; assumption.
  - apply Nat.gcd_divide_r.
Qed.

(* ---- Section 2. Witness machine peu_next (least prime factor of n!+1;
        piece-1 sigT interface projection) ---- *)

Definition peu_next (n : nat) : nat :=
  projT1 (pr_min_factor_exists (fact n + 1)
          (NatLe_drop 2 (fact n + 1) (peu_fact1_ge2 n))).

Lemma peu_next_pair : forall n : nat,
  And (Nat.divide (peu_next n) (fact n + 1)) (pr_prime (peu_next n)).
Proof.
  intros n. unfold peu_next.
  exact (projT2 (pr_min_factor_exists (fact n + 1)
                 (NatLe_drop 2 (fact n + 1) (peu_fact1_ge2 n)))).
Qed.

Theorem peu_next_prime : forall n : nat, pr_prime (peu_next n).
Proof. intros n. exact (snd (peu_next_pair n)). Qed.

Theorem peu_next_dvd : forall n : nat,
  Nat.divide (peu_next n) (fact n + 1).
Proof. intros n. exact (fst (peu_next_pair n)). Qed.

(* ---- Section 3. Main theorem: n < peu_next n + sigT witness form ---- *)

Theorem peu_next_gt : forall n : nat, NatLe (S n) (peu_next n).
Proof.
  intros n. apply NatLe_lift.
  destruct (le_lt_dec (peu_next n) n) as [Hle|Hgt].
  - exfalso.
    assert (Hp2 : 2 <= peu_next n).
    { apply NatLe_drop. exact (fst (peu_next_prime n)). }
    assert (HdF : Nat.divide (peu_next n) (fact n)).
    { apply peu_dvd_fact; [lia | exact Hle]. }
    assert (H1 : Id (peu_next n) 1).
    { apply (peu_dvd_both_1 (peu_next n) (fact n)).
      - exact HdF.
      - apply peu_next_dvd. }
    assert (H1' : peu_next n = 1).
    { exact (match H1 in Id _ z
             return (peu_next n = z) with
             | id_refl => eq_refl end). }
    lia.
  - exact Hgt.
Qed.

(* sigT witness form: every n gets a computable witness p > n and prime
   (not a bare existential proposition) *)
Theorem peu_exists_gt : forall n : nat,
  { p : nat & And (NatLe (S n) p) (pr_prime p) }.
Proof.
  intros n. exists (peu_next n). split.
  - apply peu_next_gt.
  - apply peu_next_prime.
Defined.

(* ---- Section 4. Coprimality kernel numeric smoke closures (gcd equation
        direct computation, instances <= 6) ---- *)

Lemma peu_coprime_smoke_4 : Id (Nat.gcd 4 (fact 4 + 1)) 1.
Proof. vm_compute. apply id_refl. Qed.

Lemma peu_coprime_smoke_5 : Id (Nat.gcd 5 (fact 5 + 1)) 1.
Proof. vm_compute. apply id_refl. Qed.

Lemma peu_coprime_smoke_6 : Id (Nat.gcd 6 (fact 6 + 1)) 1.
Proof. vm_compute. apply id_refl. Qed.

(* ---- Section 5. Witness machine end-to-end numeric closures (straight
        through the piece-1 sigT interface; covers the end-to-end
        numeric-use face logged in piece 1) ---- *)

Lemma peu_fact_6 : Id (fact 6) 720.
Proof. vm_compute. apply id_refl. Qed.

Lemma peu_next_1 : Id (peu_next 1) 2.
Proof. vm_compute. apply id_refl. Qed.

Lemma peu_next_2 : Id (peu_next 2) 3.
Proof. vm_compute. apply id_refl. Qed.

Lemma peu_next_3 : Id (peu_next 3) 7.
Proof. vm_compute. apply id_refl. Qed.

Lemma peu_next_4 : Id (peu_next 4) 5.
Proof. vm_compute. apply id_refl. Qed.

Lemma peu_next_5 : Id (peu_next 5) 11.
Proof. vm_compute. apply id_refl. Qed.

Lemma peu_next_6 : Id (peu_next 6) 7.
Proof. vm_compute. apply id_refl. Qed.

(* ---- Section 6. Assumption audit (Print Assumptions block) ---- *)

Print Assumptions peu_dvd_both_1.
Print Assumptions peu_dvd_fact.
Print Assumptions peu_coprime_core.
Print Assumptions peu_next_dvd.
Print Assumptions peu_next_prime.
Print Assumptions peu_next_gt.
Print Assumptions peu_exists_gt.
