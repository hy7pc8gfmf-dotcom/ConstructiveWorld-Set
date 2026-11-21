(* ====================================================================
   Module: piu_zz_pnt_window
   Mission. Window coverage of the set P_n for the effective-PNT
     consumption chain: a prime p lying in a half-open window
     (3n/(3k+2), 2n/(2k+1)] has fractional part {n/p} in [1/2, 2/3),
     hence belongs to the Zeilberger-Zudilin window set P_n; plus the
     window-position corollary 3n < p*p holding whenever the kept
     windows sit above sqrt(3n).
   Dependencies. piu_zz_padic_clearing (zz_in_Pn, zz_primeb, BidT,
     BidT_intro, BidT_elim); Stdlib ZArith/Arith/Lia/Bool (nia for the
     bilinear quotient step of the fraction face).
   References. Zeilberger-Zudilin 2020 v2, Lemma 2: the window set
     P_n = {p prime : p > max(5, sqrt(3n)), 1/2 <= {n/p} < 2/3}; window
     endpoints a_k = 3n/(3k+2), b_k = 2n/(2k+1) with floor-form
     inequalities p*(3k+2) > 3n and p*(2k+1) <= 2n.
   Constructivity. Every statement face is Set-carried: nat order
     predicates in premise and conclusion positions are boolean
     identities carried by BidT (Nat.ltb / Nat.leb), the same carrier
     family as the andb components of zz_in_Pn; conclusions are pairs
     over BidT or BidT (zz_in_Pn n p).  Boolean-to-Prop conversions
     (Nat.ltb_lt, Nat.leb_le) appear only inside proof terms; the
     quotient step uses Nat.div_mod_eq with nia on lifted Z faces.
     Face note: premises formerly stated in bare nat lt/le form are
     migrated to BidT carriers; consumers convert downward with
     BidT_elim followed by Nat.ltb_lt / Nat.leb_le, and upward with
     Nat.ltb_lt / Nat.leb_le followed by BidT_intro.  All statements
     are transparent (Defined) so the witness data stays computable.
   Build. coqc -Q <certified vo tree> "" piu_zz_pnt_window.v
     (single compile lane under the thermal guard wrapper).
   ==================================================================== *)

From Stdlib Require Import ZArith Arith Lia Bool.
Require Import piu_zz_padic_clearing.

(* This module is pure nat arithmetic; the imported padic-clearing module
   exports the Z scope, so the nat scope is re-opened locally. *)
Local Open Scope nat_scope.

(* ================= Section 1. Window fraction face ================= *)

(* The discrete fractional-part condition: from the floor-form window
   inequalities p*(2k+1) <= 2n and 3n < p*(3k+2) the quotient q = n/p
   equals k exactly, so 2*(n mod p) >= p and 3*(n mod p) < 2p.  The
   premise inequalities arrive as boolean identities and are read on the
   propositional face only inside the proof. *)
Theorem zz_pnt_window_frac : forall n k p : nat,
  BidT (Nat.ltb 0 p) ->
  BidT (Nat.leb (p * (2 * k + 1)) (2 * n)) ->
  BidT (Nat.ltb (3 * n) (p * (3 * k + 2))) ->
  prod (BidT (Nat.leb p (2 * (n mod p))%nat))
       (BidT (Nat.ltb (3 * (n mod p))%nat (2 * p)%nat)).
Proof.
  intros n k p Hp Hlow Hhigh.
  assert (Hplt : (0 < p)%nat)
    by (apply Nat.ltb_lt; apply BidT_elim; exact Hp).
  assert (HlowP : (p * (2 * k + 1) <= 2 * n)%nat)
    by (apply Nat.leb_le; apply BidT_elim; exact Hlow).
  assert (HhighP : (3 * n < p * (3 * k + 2))%nat)
    by (apply Nat.ltb_lt; apply BidT_elim; exact Hhigh).
  assert (Hd : (n = p * (n / p) + n mod p)%nat) by apply Nat.div_mod_eq.
  assert (Hr : (n mod p < p)%nat) by (apply Nat.mod_upper_bound; lia).
  assert (Hzn : (Z.of_nat n
                   = Z.of_nat p * Z.of_nat (n / p) + Z.of_nat (n mod p))%Z)
    by lia.
  assert (HlowZ : (Z.of_nat p * (2 * Z.of_nat k + 1) <= 2 * Z.of_nat n)%Z)
    by lia.
  assert (HhighZ : (3 * Z.of_nat n
                      < Z.of_nat p * (3 * Z.of_nat k + 2))%Z)
    by lia.
  assert (HmodZ : (0 <= Z.of_nat (n mod p) < Z.of_nat p)%Z) by lia.
  assert (Hq1 : (Z.of_nat (n / p) <= Z.of_nat k)%Z) by nia.
  assert (Hq2 : (Z.of_nat k <= Z.of_nat (n / p))%Z) by nia.
  assert (HqNat : (n / p = k)%nat) by (apply Nat2Z.inj_iff; lia).
  rewrite HqNat in Hd.
  split.
  - apply BidT_intro. apply Nat.leb_le. lia.
  - apply BidT_intro. apply Nat.ltb_lt. lia.
Defined.

(* ================= Section 2. Window membership ================= *)

(* Window membership: a prime p above 5 with p*p > 3n lying in window k
   belongs to the window set, i.e. zz_in_Pn n p is true -- each andb
   component is discharged from the fraction face or from a premise. *)
Theorem zz_pnt_window_subset : forall n k p : nat,
  BidT (zz_primeb p) -> BidT (Nat.ltb 5 p) ->
  BidT (Nat.ltb (3 * n) (p * p)) ->
  BidT (Nat.leb (p * (2 * k + 1)) (2 * n)) ->
  BidT (Nat.ltb (3 * n) (p * (3 * k + 2))) ->
  BidT (zz_in_Pn n p).
Proof.
  intros n k p Hpb Hp5 Hsqrt Hlow Hhigh.
  apply BidT_elim in Hpb.
  apply BidT_intro. unfold zz_in_Pn.
  apply Bool.andb_true_iff. split; [exact Hpb |].
  assert (Hp5t : (5 < p)%nat)
    by (apply Nat.ltb_lt; apply BidT_elim; exact Hp5).
  apply Bool.andb_true_iff. split; [apply Nat.ltb_lt; exact Hp5t |].
  assert (HsqrtP : (3 * n < p * p)%nat)
    by (apply Nat.ltb_lt; apply BidT_elim; exact Hsqrt).
  apply Bool.andb_true_iff. split; [apply Nat.ltb_lt; exact HsqrtP |].
  assert (HposB : BidT (Nat.ltb 0 p))
    by (apply BidT_intro; apply Nat.ltb_lt; lia).
  destruct (zz_pnt_window_frac n k p HposB Hlow Hhigh) as [Hf1 Hf2].
  apply Bool.andb_true_iff. split.
  - apply BidT_elim. exact Hf1.
  - apply BidT_elim. exact Hf2.
Defined.

(* ============== Section 3. Window position above the square root ======= *)

(* If every kept window index satisfies k <= K and the K-th window still
   lies above the curve, i.e. (3K+2)*(3K+2) < 3n, then every window
   prime satisfies 3n < p*p: the window membership condition of Section 2
   is automatic for large n. *)
Theorem zz_pnt_window_above_sqrt : forall n K k p : nat,
  BidT (Nat.leb k K) ->
  BidT (Nat.ltb (3 * n) (p * (3 * k + 2))) ->
  BidT (Nat.ltb ((3 * K + 2) * (3 * K + 2)) (3 * n)) ->
  BidT (Nat.ltb (3 * n) (p * p)).
Proof.
  intros n K k p HkK Hwin Hbig.
  assert (HkKP : (k <= K)%nat)
    by (apply Nat.leb_le; apply BidT_elim; exact HkK).
  assert (HwinP : (3 * n < p * (3 * k + 2))%nat)
    by (apply Nat.ltb_lt; apply BidT_elim; exact Hwin).
  assert (HbigP : ((3 * K + 2) * (3 * K + 2) < 3 * n)%nat)
    by (apply Nat.ltb_lt; apply BidT_elim; exact Hbig).
  assert (Hconcl : (3 * n < p * p)%nat).
  { assert (HV : p * (3 * k + 2) <= p * (3 * K + 2))
      by (apply Nat.mul_le_mono_l; lia).
    destruct (Nat.le_gt_cases p (3 * K + 2)) as [Hc | Hc].
    - exfalso.
      assert (Hm : p * (3 * K + 2) <= (3 * K + 2) * (3 * K + 2)) by nia.
      lia.
    - assert (Hpp : p * (3 * K + 2) + p <= p * p) by nia.
      lia. }
  apply BidT_intro. apply Nat.ltb_lt. exact Hconcl.
Defined.

(* ================= Section 4. Numeric smoke sample ================= *)

(* Sample run of the fraction face at n = 100, k = 0, p = 160 (window
   (150, 200]): both Set-carried boolean components evaluate true. *)
Lemma zz_pnt_window_frac_sample :
  prod (BidT (Nat.leb 160%nat (2 * (100 mod 160)%nat)%nat))
       (BidT (Nat.ltb (3 * (100 mod 160)%nat)%nat (2 * 160)%nat)).
Proof.
  apply (zz_pnt_window_frac 100 0 160).
  - apply BidT_intro. apply Nat.ltb_lt. lia.
  - apply BidT_intro. apply Nat.leb_le. lia.
  - apply BidT_intro. apply Nat.ltb_lt. lia.
Defined.

(* ================= Section 5. Certification face ================= *)

Print Assumptions zz_pnt_window_frac.
Print Assumptions zz_pnt_window_subset.
Print Assumptions zz_pnt_window_above_sqrt.
Print Assumptions zz_pnt_window_frac_sample.
