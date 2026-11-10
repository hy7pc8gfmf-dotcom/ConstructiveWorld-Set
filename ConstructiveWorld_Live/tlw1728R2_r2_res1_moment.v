(* ConstructiveWorld-Set -- residual-coefficient moment-sum expansions over the arctan Pade table. *)

(** * tlw1728R2_r2_res1_moment: the first residual coefficient of the diagonal arctan Pade pair as a finite moment sum.

    Mission.  Unfold table entries at arbitrary indices ([nth_vsmul_gen],
      [nth_vadd_gen], [nth_vconv_cons], [altser_length], [altser_nth]) and
      restate the first residual coefficient of the diagonal Pade pair for
      arctan, res1_n = nth (2n+1) (conv (padeV (2n)) (altser)), as an
      explicit finite moment sum over the denominator table:
      [r2_wsum] writes the convolution sum, [r2_vconv_wsum] equates every
      Cauchy-product entry with it, [r2_msq] resolves the alternating
      summands to signed reciprocals, and [r2_res1_moment] / [r2_res1_recip]
      carry the two degree forms of [r2_res1]; computable anchors at
      n = 0..3 close the file ([r2_res1_anchor_0..3]).

    Dependencies.  Stdlib [QArith], [ZArith], [List], [Setoid], [Lia].
      Requires [tlw1463_pade_table] of this development.

    References.  This development, tlw1728R2_r2_res1_moment.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" tlw1728R2_r2_res1_moment.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 000160bc]. *)
From Stdlib Require Import QArith.
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Setoid.
From Stdlib Require Import Lia.
Require Import tlw1463_pade_table.
Import ListNotations.

(* ================= §1 Arbitrary-index entries of the table arithmetic ================= *)

(* nth of a scaled table at an arbitrary index, by induction on the index. *)
Lemma nth_vsmul_gen : forall (k : nat) (c : Q) (l : list Q),
  nth k (vsmul c l) 0%Q == c * nth k l 0%Q.
Proof.
  intros k. induction k as [|k IH]; intros c l.
  - apply nth0_vsmul.
  - destruct l as [|x t].
    + cbn [vsmul nth]. rewrite Qmult_0_r. apply Qeq_refl.
    + cbn [vsmul nth]. apply IH.
Qed.

(* nth of a pointwise sum at an arbitrary index: the short side is        *)
(* zero-padded, so the entry is the sum of the two entries.               *)
Lemma nth_vadd_gen : forall (k : nat) (a b : list Q),
  nth k (vadd a b) 0%Q == nth k a 0%Q + nth k b 0%Q.
Proof.
  intros k. induction k as [|k IH]; intros a b.
  - apply nth0_vadd.
  - destruct a as [|x t]; destruct b as [|y s].
    + cbn [vadd nth]. rewrite Qplus_0_l. apply Qeq_refl.
    + cbn [vadd nth]. rewrite Qplus_0_l. apply Qeq_refl.
    + cbn [vadd nth]. rewrite Qplus_0_r. apply Qeq_refl.
    + cbn [vadd nth]. apply IH.
Qed.

(* Unfolding step of the Cauchy product at an arbitrary index: the head   *)
(* of the left table pairs with degree k of the right one, and the tail   *)
(* contributes at the shifted degree. *)
Lemma nth_vconv_cons : forall (a : list Q) (x : Q) (b : list Q) (k : nat),
  nth k (vconv (x :: a) b) 0%Q ==
  x * nth k b 0%Q
    + (match k with
       | O => 0%Q
       | S k' => nth k' (vconv a b) 0%Q
       end).
Proof.
  intros a x b k.
  replace (vconv (x :: a) b) with (vadd (vsmul x b) (0%Q :: vconv a b))
    by reflexivity.
  rewrite nth_vadd_gen, nth_vsmul_gen.
  destruct k as [|k'].
  - cbn [nth]. rewrite Qplus_0_r. apply Qeq_refl.
  - cbn [nth]. apply Qeq_refl.
Qed.

(* Length of the alternating series table: it carries degrees 0..N-1. *)
Lemma altser_length : forall N : nat, length (altser N) = N.
Proof.
  intros N. induction N as [|N IH].
  - reflexivity.
  - replace (altser (S N))
      with (altser N ++ ((altsign N) # (Pos.of_succ_nat (2 * N)))%Q :: nil)
      by reflexivity.
    rewrite app_length. cbn [length]. rewrite IH. lia.
Qed.

(* Entry of the alternating series table at degree m: the signed          *)
(* reciprocal (-1)^m / (2m+1), for every index below the table length.    *)
Lemma altser_nth : forall (N m : nat), (m < N)%nat ->
  nth m (altser N) 0%Q == ((altsign m) # (Pos.of_succ_nat (2 * m)))%Q.
Proof.
  induction N as [|N IH]; intros m Hm.
  - exfalso. lia.
  - replace (altser (S N))
      with (altser N ++ ((altsign N) # (Pos.of_succ_nat (2 * N)))%Q :: nil)
      by reflexivity.
    destruct m as [|m'].
    + destruct N as [|N'].
      * cbn [app nth Nat.mul]. apply Qeq_refl.
      * rewrite app_nth1 by (rewrite altser_length; lia).
        apply IH. lia.
    + assert (HlN : length (altser N) = N) by apply altser_length.
      destruct (Nat.le_gt_cases (length (altser N)) (S m')) as [Hlen|Hlen].
      * assert (Heq : S m' = N) by lia.
        rewrite app_nth2 by lia.
        replace (S m' - length (altser N))%nat with 0%nat by lia.
        cbn [app nth]. rewrite Heq. apply Qeq_refl.
      * rewrite app_nth1 by lia.
        apply IH. lia.
Qed.

(* ================= §2 The residual coefficient as a finite moment sum ================= *)

(* Convolution sum: sum_j a[j] * b[k-j] over the entries of a; indices    *)
(* below zero contribute nothing, which the k = 0 branch makes explicit.  *)
Fixpoint r2_wsum (a b : list Q) (k : nat) {struct a} : Q :=
  match a, k with
  | nil, _ => 0%Q
  | x :: t, O => x * nth 0 b 0%Q
  | x :: t, S k' => x * nth (S k') b 0%Q + r2_wsum t b k'
  end.

(* Every Cauchy-product entry is the corresponding convolution sum; both  *)
(* sides are total with zero padding, so no length premise is needed.     *)
Lemma r2_vconv_wsum : forall (a b : list Q) (k : nat),
  nth k (vconv a b) 0%Q == r2_wsum a b k.
Proof.
  intros a. induction a as [|x t IH]; intros b k.
  - revert k. induction k as [|k IHk]; cbn [vconv nth r2_wsum].
    + apply Qeq_refl.
    + apply Qeq_refl.
  - replace (vconv (x :: t) b) with (vadd (vsmul x b) (0%Q :: vconv t b))
      by reflexivity.
    rewrite nth_vadd_gen, nth_vsmul_gen.
    destruct k as [|k'].
    + cbn [nth r2_wsum]. rewrite Qplus_0_r. apply Qeq_refl.
    + cbn [nth r2_wsum]. rewrite IH. apply Qeq_refl.
Qed.

(* Moment sum with each alternating-series entry resolved to its signed   *)
(* reciprocal; every complementary degree stays inside the table.         *)
Fixpoint r2_msq (a : list Q) (k : nat) {struct a} : Q :=
  match a, k with
  | nil, _ => 0%Q
  | x :: t, O => x * ((altsign 0) # (Pos.of_succ_nat 0))%Q
  | x :: t, S k' => x * ((altsign (S k')) # (Pos.of_succ_nat (2 * S k')))%Q
                    + r2_msq t k'
  end.

Lemma r2_wsum_altser : forall (a : list Q) (N k : nat), (k < N)%nat ->
  r2_wsum a (altser N) k == r2_msq a k.
Proof.
  intros a. induction a as [|x t IH]; intros N k Hk.
  - apply Qeq_refl.
  - destruct k as [|k'].
    + cbn [r2_wsum r2_msq]. rewrite altser_nth by lia. apply Qeq_refl.
    + cbn [r2_wsum r2_msq]. rewrite altser_nth by lia. rewrite IH by lia.
      apply Qeq_refl.
Qed.

(* The first residual coefficient: degree 2n+1 of the Cauchy product of   *)
(* the diagonal denominator table with the alternating series, exactly    *)
(* the entry consumed by pade_decay_premise in tlw1463_pade_table.        *)
Definition r2_res1 (n : nat) : Q :=
  nth (2 * n + 1) (vconv (padeV (2 * n)) (altser (2 * n + 4))) 0%Q.

(* Moment-sum representation of the residual (degree form). *)
Theorem r2_res1_moment : forall n : nat,
  r2_res1 n == r2_wsum (padeV (2 * n)) (altser (2 * n + 4)) (2 * n + 1).
Proof.
  intros n. apply r2_vconv_wsum.
Qed.

(* Moment-sum representation with signed reciprocal summands:             *)
(* r2_res1 n = sum_j padeV(2n)[j] * (-1)^(2n+1-j) / (2(2n+1-j)+1).        *)
Theorem r2_res1_recip : forall n : nat,
  r2_res1 n == r2_msq (padeV (2 * n)) (2 * n + 1).
Proof.
  intros n.
  eapply Qeq_trans.
  - apply r2_res1_moment.
  - apply r2_wsum_altser. lia.
Qed.

(* ================= §3 Computable anchors at n = 0..3 ================= *)

(* The four oracle values, read straight off the tables by computation.   *)
Lemma r2_res1_anchor_0 : r2_res1 0 == ((-1) # 3)%Q.
Proof.
  vm_compute. reflexivity.
Qed.

Lemma r2_res1_anchor_1 : r2_res1 1 == ((-12) # 35)%Q.
Proof.
  vm_compute. reflexivity.
Qed.

Lemma r2_res1_anchor_2 : r2_res1 2 == ((-320) # 231)%Q.
Proof.
  vm_compute. reflexivity.
Qed.

Lemma r2_res1_anchor_3 : r2_res1 3 == ((-1792) # 143)%Q.
Proof.
  vm_compute. reflexivity.
Qed.

Print Assumptions r2_res1_moment.
Print Assumptions r2_res1_recip.
Print Assumptions r2_res1_anchor_3.
