(* ========================================================================= *)
(* Module   : tlw1738_r2_res1_decay                                          *)
(* Mission.  Residual recursion for the diagonal Pade pair of arctan.       *)
(*            With r2_coef m j the degree-j entry of V_m g - U_m, the       *)
(*            two-step recursion transports it linearly: coef (k+2) (S j) = *)
(*            (2k+5) coef (k+1) (S j) + (k+2)^2 coef k j, so a vanishing    *)
(*            diagonal entry gives (2k+5) R(k+1) = -(k+2)^2 R(k) on         *)
(*            R(k) = coef k (k+1), and even steps compose into (4n+5)(4n+7) *)
(*            res1 (n+1) = (2n+2)^2 (2n+3)^2 res1 n; the vanishing entries  *)
(*            are explicit premises, and the closed form (4n+3)! res1 n =   *)
(*            -2^(2n+1) ((2n+1)!)^3 is certified by computation at n=1..3.  *)
(* Dependencies. tlw1463_pade_table, tlw1728R2_r2_res1_moment of this tree  *)
(*            (bid/bidI/bidE carrier, qeqbI, nat_double_ind, pade tables,   *)
(*            r2_msq, r2_res1, r2_res1_recip, nth_vadd_gen, nth_vsmul_gen); *)
(*            Stdlib QArith/ZArith/List/Setoid/Arith/Lia.                   *)
(* References. Lambert continued-fraction remainders; classical Pade        *)
(*            remainder theory for arctan (Mahler 1953).                    *)
(* Constructivity. Every named statement is carried by Set: each predicate  *)
(*            face is the decidable boolean identity carrier                *)
(*            bid (Qeq_bool x y) true over Q and bid (Nat.eqb / Nat.ltb ...) *)
(*            true over nat (the tree-wide QeqT-family form); no Prop       *)
(*            statement face and no Prop component inside any Set carrier.  *)
(*            Constructive Prop reasoning (ring, lia, one auxiliary nia use *)
(*            on the unfolded Z face) stays inside proof bodies behind the  *)
(*            bidI/bidE bridge; all proofs end in Defined (no Qed); zero    *)
(*            axioms, zero classical logic, zero admits; vm_compute         *)
(*            confined to the six concrete numeral anchors.                 *)
(* Build.     rocq c -native-compiler no -q -Q <tree root> ""               *)
(*            tlw1738_r2_res1_decay.v                                       *)
(* ========================================================================= *)
From Stdlib Require Import QArith.
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Setoid.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
Require Import tlw1463_pade_table.
Require Import tlw1728R2_r2_res1_moment.

(* Read the Q equality behind a boolean identity carrier premise.    *)
Ltac bidq H := apply bidE in H; apply Qeq_bool_eq in H.

(* ================= Section 1. Linearity of the moment sum ================= *)

(* Subtraction of zero is trivial (the stdlib carries no such lemma). *)
Lemma r2_q_minus_0 : forall x : Q, bid (Qeq_bool (x - 0%Q) x) true.
Proof.
  intros [n d]. apply bidI. apply qeqbI. ring.
Defined.

(* The moment sum is linear in the table. *)
Lemma r2_msq_vsmul : forall (c : Q) (l : list Q) (j : nat),
  bid (Qeq_bool (r2_msq (vsmul c l) j) (c * r2_msq l j)) true.
Proof.
  intros c l. induction l as [|x t IH]; intros j.
  - apply bidI. apply qeqbI. cbn [vsmul r2_msq]. rewrite Qmult_0_r. apply Qeq_refl.
  - destruct j as [|j'].
    + apply bidI. apply qeqbI. cbn [vsmul r2_msq]. rewrite Qmult_assoc. apply Qeq_refl.
    + assert (IHq : r2_msq (vsmul c t) j' == c * r2_msq t j').
      { specialize (IH j'). bidq IH. exact IH. }
      apply bidI. apply qeqbI. cbn [vsmul r2_msq]. rewrite IHq. ring.
Defined.

(* The moment sum is additive in the table. *)
Lemma r2_msq_vadd : forall (a b : list Q) (j : nat),
  bid (Qeq_bool (r2_msq (vadd a b) j) (r2_msq a j + r2_msq b j)) true.
Proof.
  intros a. induction a as [|x t IH]; intros b j.
  - apply bidI. apply qeqbI. cbn [vadd r2_msq]. rewrite Qplus_0_l. apply Qeq_refl.
  - destruct b as [|y s].
    + apply bidI. apply qeqbI. cbn [vadd]. rewrite Qplus_0_r. apply Qeq_refl.
    + destruct j as [|j'].
      * apply bidI. apply qeqbI. cbn [vadd r2_msq]. rewrite Qmult_plus_distr_l.
        apply Qeq_refl.
      * assert (IHq : r2_msq (vadd t s) j' == r2_msq t j' + r2_msq s j').
        { specialize (IH s j'). bidq IH. exact IH. }
        apply bidI. apply qeqbI. cbn [vadd r2_msq]. rewrite IHq. ring.
Defined.

(* A zero-padded head contributes nothing above degree zero. *)
Lemma r2_msq_shift : forall (l : list Q) (j : nat),
  bid (Qeq_bool (r2_msq (0%Q :: l) (S j)) (r2_msq l j)) true.
Proof.
  intros l j. apply bidI. apply qeqbI. cbn [r2_msq].
  rewrite Qmult_0_l, Qplus_0_l. apply Qeq_refl.
Defined.

(* ================= Section 2. The residual coefficients ================= *)

(* The degree-j entry of V_m g - U_m: the moment sum of the denominator   *)
(* table minus the numerator table entry (zero padding beyond its degree). *)
Definition r2_coef (m j : nat) : Q :=
  r2_msq (padeV m) j - nth j (padeU m) 0%Q.

(* Atomic Q-algebra used to assemble the linear transport (the whole      *)
(* solver load of the transport sits in these three lemmas). *)
Lemma r2_q_linear : forall (c d A B C D : Q),
  bid (Qeq_bool ((c * A + d * B) - (c * C + d * D)) (c * (A - C) + d * (B - D))) true.
Proof.
  intros c d A B C D. apply bidI. apply qeqbI. ring.
Defined.

Lemma r2_q_zero_move : forall (c d X Y : Q),
  bid (Qeq_bool 0%Q (c * X + d * Y)) true ->
  bid (Qeq_bool (c * X) (- d * Y)) true.
Proof.
  intros c d X Y H. bidq H.
  assert (Hg : c * X == - d * Y).
  { unfold Qeq in *. cbn [Qnum Qden Qmult Qplus Qminus Qopp] in *. nia. }
  apply bidI. apply qeqbI. exact Hg.
Defined.

Lemma r2_q_ring_1 : forall (a u v : Q),
  bid (Qeq_bool (a * (- u * v)) (- (u * (a * v)))) true.
Proof.
  intros a u v. apply bidI. apply qeqbI. ring.
Defined.

Lemma r2_q_ring_2 : forall (b c X : Q),
  bid (Qeq_bool (- (c * (- b * X))) (b * (c * X))) true.
Proof.
  intros b c X. apply bidI. apply qeqbI. ring.
Defined.

Lemma r2_q_step2 : forall (e f b c X Y R : Q),
  bid (Qeq_bool (e * R) (- b * X)) true ->
  bid (Qeq_bool (f * Y) (- c * R)) true ->
  bid (Qeq_bool (e * (f * Y)) (b * (c * X))) true.
Proof.
  intros e f b c X Y R H1 H2. bidq H1. bidq H2.
  assert (Hr1 : forall (a0 u0 v0 : Q), a0 * (- u0 * v0) == - (u0 * (a0 * v0))).
  { intros a0 u0 v0. pose proof (r2_q_ring_1 a0 u0 v0) as H. bidq H. exact H. }
  assert (Hr2 : forall (b0 c0 X0 : Q), - (c0 * (- b0 * X0)) == b0 * (c0 * X0)).
  { intros b0 c0 X0. pose proof (r2_q_ring_2 b0 c0 X0) as H. bidq H. exact H. }
  assert (Hg : e * (f * Y) == b * (c * X)).
  { assert (K1 : c * (e * R) == c * (- b * X)) by (rewrite H1; reflexivity).
    assert (K2 : e * (f * Y) == e * (- c * R)) by (rewrite H2; reflexivity).
    rewrite K2, (Hr1 e c R), K1.
    apply (Hr2 b c X). }
  apply bidI. apply qeqbI. exact Hg.
Defined.

(* Step equation of the denominator table at an arbitrary index above     *)
(* zero, unfolded from the four-tuple recursion as in padeV_hd. *)
Lemma padeV_step_msq : forall (k j : nat),
  bid (Qeq_bool (r2_msq (padeV (S (S k))) (S j))
                (((Z.of_nat (2 * k + 5)) # 1)%Q * r2_msq (padeV (S k)) (S j)
                   + ((Z.of_nat ((k + 2) * (k + 2))) # 1)%Q * r2_msq (padeV k) j)) true.
Proof.
  intros k j.
  assert (Hvadd : forall (a b : list Q) (n : nat),
    r2_msq (vadd a b) n == r2_msq a n + r2_msq b n).
  { intros a b n. pose proof (r2_msq_vadd a b n) as H. bidq H. exact H. }
  assert (Hvsmul : forall (c : Q) (l : list Q) (n : nat),
    r2_msq (vsmul c l) n == c * r2_msq l n).
  { intros c l n. pose proof (r2_msq_vsmul c l n) as H. bidq H. exact H. }
  assert (Hshift : forall (l : list Q) (n : nat),
    r2_msq (0%Q :: l) (S n) == r2_msq l n).
  { intros l n. pose proof (r2_msq_shift l n) as H. bidq H. exact H. }
  assert (Hg : r2_msq (padeV (S (S k))) (S j) ==
    ((Z.of_nat (2 * k + 5)) # 1)%Q * r2_msq (padeV (S k)) (S j)
    + ((Z.of_nat ((k + 2) * (k + 2))) # 1)%Q * r2_msq (padeV k) j).
  { unfold padeV.
    destruct (pade_pair k) as [[u0 u1][v0 v1]] eqn:Ek.
    rewrite (pade_pair_step (S k)), (pade_pair_step k), Ek.
    cbn [fst snd].
    assert (Hr1 : (2 * S (S k) + 1)%nat = (2 * k + 5)%nat) by lia.
    assert (Hr2 : (S (S k) * S (S k))%nat = ((k + 2) * (k + 2))%nat) by lia.
    rewrite Hr1, Hr2.
    rewrite Hvadd, Hvsmul, Hvsmul, Hshift.
    apply Qeq_refl. }
  apply bidI. apply qeqbI. exact Hg.
Defined.

(* Step equation of the numerator table at an arbitrary index above       *)
(* zero, unfolded the same way. *)
Lemma padeU_step_nth : forall (k j : nat),
  bid (Qeq_bool (nth (S j) (padeU (S (S k))) 0%Q)
                (((Z.of_nat (2 * k + 5)) # 1)%Q * nth (S j) (padeU (S k)) 0%Q
                   + ((Z.of_nat ((k + 2) * (k + 2))) # 1)%Q * nth j (padeU k) 0%Q)) true.
Proof.
  intros k j.
  assert (Hg : nth (S j) (padeU (S (S k))) 0%Q ==
    ((Z.of_nat (2 * k + 5)) # 1)%Q * nth (S j) (padeU (S k)) 0%Q
    + ((Z.of_nat ((k + 2) * (k + 2))) # 1)%Q * nth j (padeU k) 0%Q).
  { unfold padeU.
    destruct (pade_pair k) as [[u0 u1][v0 v1]] eqn:Ek.
    rewrite (pade_pair_step (S k)), (pade_pair_step k), Ek.
    cbn [fst snd].
    assert (Hr3 : (2 * S (S k) + 1)%nat = (2 * k + 5)%nat) by lia.
    assert (Hr4 : (S (S k) * S (S k))%nat = ((k + 2) * (k + 2))%nat) by lia.
    rewrite Hr3, Hr4.
    rewrite nth_vadd_gen, nth_vsmul_gen, nth_vsmul_gen.
    cbn [nth].
    apply Qeq_refl. }
  apply bidI. apply qeqbI. exact Hg.
Defined.

(* The residual transports linearly under the two-step table recursion. *)
Lemma r2_coef_step : forall (k j : nat),
  bid (Qeq_bool (r2_coef (S (S k)) (S j))
                (((Z.of_nat (2 * k + 5)) # 1)%Q * r2_coef (S k) (S j)
                   + ((Z.of_nat ((k + 2) * (k + 2))) # 1)%Q * r2_coef k j)) true.
Proof.
  intros k j.
  assert (HV : forall (a b : nat),
    r2_msq (padeV (S (S a))) (S b) ==
    ((Z.of_nat (2 * a + 5)) # 1)%Q * r2_msq (padeV (S a)) (S b)
    + ((Z.of_nat ((a + 2) * (a + 2))) # 1)%Q * r2_msq (padeV a) b).
  { intros a b. pose proof (padeV_step_msq a b) as H. bidq H. exact H. }
  assert (HU : forall (a b : nat),
    nth (S b) (padeU (S (S a))) 0%Q ==
    ((Z.of_nat (2 * a + 5)) # 1)%Q * nth (S b) (padeU (S a)) 0%Q
    + ((Z.of_nat ((a + 2) * (a + 2))) # 1)%Q * nth b (padeU a) 0%Q).
  { intros a b. pose proof (padeU_step_nth a b) as H. bidq H. exact H. }
  assert (HQL : forall (c d A B C D : Q),
    (c * A + d * B) - (c * C + d * D) == c * (A - C) + d * (B - D)).
  { intros c d A B C D. pose proof (r2_q_linear c d A B C D) as H. bidq H. exact H. }
  assert (Hg : r2_coef (S (S k)) (S j) ==
    ((Z.of_nat (2 * k + 5)) # 1)%Q * r2_coef (S k) (S j)
    + ((Z.of_nat ((k + 2) * (k + 2))) # 1)%Q * r2_coef k j).
  { unfold r2_coef. rewrite HV, HU. apply HQL. }
  apply bidI. apply qeqbI. exact Hg.
Defined.

(* The numerator table entry above its degree is the zero padding, as a   *)
(* two-step induction over the order (Set-carried form, bid bridge). *)
Lemma padeU_pad_beyond : forall (m j : nat),
  bid (Nat.ltb (m + 1) (2 * j)) true ->
  bid (Qeq_bool (nth j (padeU m) 0%Q) 0%Q) true.
Proof.
  apply (nat_double_ind (fun m => forall j : nat,
    bid (Nat.ltb (m + 1) (2 * j)) true ->
    bid (Qeq_bool (nth j (padeU m) 0%Q) 0%Q) true)).
  - intros j Hj. apply bidE in Hj.
    assert (Hlt : (0 + 1 < 2 * j)%nat) by (exact (proj1 (Nat.ltb_lt _ _) Hj)).
    destruct j as [|j']; [lia|].
    apply bidI. cbn. destruct j' as [|j'']; reflexivity.
  - intros j Hj. apply bidE in Hj.
    assert (Hlt : (1 + 1 < 2 * j)%nat) by (exact (proj1 (Nat.ltb_lt _ _) Hj)).
    destruct j as [|j']; [lia|].
    apply bidI. cbn. destruct j' as [|j'']; reflexivity.
  - intros m IHm IHm1 j Hj. apply bidE in Hj.
    assert (Hlt : (S (S m) + 1 < 2 * j)%nat) by (exact (proj1 (Nat.ltb_lt _ _) Hj)).
    destruct j as [|j']; [lia|].
    assert (IHj : nth j' (padeU m) 0%Q == 0%Q).
    { pose proof (IHm j' (ltac:(apply bidI; apply (proj2 (Nat.ltb_lt _ _)); lia)))
        as Hp. bidq Hp. exact Hp. }
    assert (IHj1 : nth (S j') (padeU (S m)) 0%Q == 0%Q).
    { pose proof (IHm1 (S j') (ltac:(apply bidI; apply (proj2 (Nat.ltb_lt _ _)); lia)))
        as Hp. bidq Hp. exact Hp. }
    assert (Hstep : nth (S j') (padeU (S (S m))) 0%Q ==
      ((Z.of_nat (2 * m + 5)) # 1)%Q * nth (S j') (padeU (S m)) 0%Q
      + ((Z.of_nat ((m + 2) * (m + 2))) # 1)%Q * nth j' (padeU m) 0%Q).
    { pose proof (padeU_step_nth m j') as Hp. bidq Hp. exact Hp. }
    apply bidI. apply qeqbI.
    rewrite Hstep, IHj, IHj1.
    rewrite Qmult_0_r, Qmult_0_r, Qplus_0_l.
    apply Qeq_refl.
Defined.

(* The consumed residual is the mismatch-front coefficient of order 2n:   *)
(* the numerator table cannot reach degree 2n+1. *)
Lemma r2_res1_coef : forall n : nat,
  bid (Qeq_bool (r2_res1 n) (r2_coef (2 * n) (2 * n + 1))) true.
Proof.
  intros n.
  assert (Hprem : bid (Nat.ltb (2 * n + 1) (2 * (2 * n + 1))) true)
    by (apply bidI; apply (proj2 (Nat.ltb_lt _ _)); lia).
  pose proof (padeU_pad_beyond (2 * n) (2 * n + 1) Hprem) as Hp.
  bidq Hp.
  assert (Hm0 : forall x : Q, x - 0%Q == x).
  { intros x. pose proof (r2_q_minus_0 x) as H0. bidq H0. exact H0. }
  assert (Hg : r2_res1 n == r2_coef (2 * n) (2 * n + 1)).
  { unfold r2_coef.
    rewrite r2_res1_recip, Hp, Hm0.
    apply Qeq_refl. }
  apply bidI. apply qeqbI. exact Hg.
Defined.

(* ============ Section 3. The first-order ratio on the mismatch front ============ *)

(* A vanishing diagonal entry at order k+2 moves the mismatch front one   *)
(* step: (2k+5) R(k+1) = -(k+2)^2 R(k). *)
Lemma r2_ratio_step : forall k : nat,
  bid (Qeq_bool (r2_coef (S (S k)) (S (S k))) 0%Q) true ->
  bid (Qeq_bool (((Z.of_nat (2 * k + 5)) # 1)%Q * r2_coef (S k) (S (S k)))
                (- ((Z.of_nat ((k + 2) * (k + 2))) # 1)%Q * r2_coef k (S k))) true.
Proof.
  intros k H. bidq H.
  assert (HZM : forall (c d X Y : Q), 0%Q == c * X + d * Y -> c * X == - d * Y).
  { intros c d X Y H0.
    assert (Hpb : bid (Qeq_bool 0%Q (c * X + d * Y)) true)
      by (apply bidI; apply qeqbI; exact H0).
    pose proof (r2_q_zero_move c d X Y Hpb) as Hc.
    bidq Hc. exact Hc. }
  assert (Hg : ((Z.of_nat (2 * k + 5)) # 1)%Q * r2_coef (S k) (S (S k)) ==
               - ((Z.of_nat ((k + 2) * (k + 2))) # 1)%Q * r2_coef k (S k)).
  { pose proof (r2_coef_step k (S k)) as Hstep. bidq Hstep.
    rewrite H in Hstep.
    apply HZM. exact Hstep. }
  apply bidI. apply qeqbI. exact Hg.
Defined.

(* Even-step composition: two applications of r2_ratio_step give the      *)
(* two-step ratio on res1 itself. *)
Lemma r2_res1_step : forall n : nat,
  bid (Qeq_bool (r2_coef (2 * n + 2) (2 * n + 2)) 0%Q) true ->
  bid (Qeq_bool (r2_coef (2 * n + 3) (2 * n + 3)) 0%Q) true ->
  bid (Qeq_bool (((Z.of_nat (4 * n + 5)) # 1)%Q
                   * (((Z.of_nat (4 * n + 7)) # 1)%Q * r2_res1 (S n)))
                (((Z.of_nat ((2 * n + 2) * (2 * n + 2))) # 1)%Q
                   * (((Z.of_nat ((2 * n + 3) * (2 * n + 3))) # 1)%Q * r2_res1 n))) true.
Proof.
  intros n H1 H2. bidq H1. bidq H2.
  assert (H1b : bid (Qeq_bool (r2_coef (S (S (2 * n))) (S (S (2 * n)))) 0%Q) true).
  { assert (En1 : (S (S (2 * n)))%nat = (2 * n + 2)%nat) by lia. rewrite En1.
    apply bidI. apply qeqbI. exact H1. }
  assert (H2b : bid (Qeq_bool (r2_coef (S (S (S (2 * n)))) (S (S (S (2 * n))))) 0%Q) true).
  { assert (En2 : (S (S (S (2 * n))))%nat = (2 * n + 3)%nat) by lia. rewrite En2.
    apply bidI. apply qeqbI. exact H2. }
  pose proof (r2_ratio_step (2 * n) H1b) as Ha.
  pose proof (r2_ratio_step (S (2 * n)) H2b) as Hb.
  bidq Ha. bidq Hb.
  assert (HRC : forall m : nat, r2_res1 m == r2_coef (2 * m) (2 * m + 1)).
  { intros m. pose proof (r2_res1_coef m) as H. bidq H. exact H. }
  apply bidI. apply qeqbI.
  rewrite (HRC (S n)), (HRC n).
  assert (Hr5 : (S (S (S (2 * n))))%nat = (2 * n + 3)%nat) by lia. rewrite Hr5 in Hb.
  assert (Hr6 : (S (S (2 * n)))%nat = (2 * n + 2)%nat) by lia. rewrite Hr6 in Ha, Hb.
  assert (Hr7 : (S (2 * n))%nat = (2 * n + 1)%nat) by lia. rewrite Hr7 in Ha, Hb.
  assert (Hr8 : (2 * (2 * n) + 5)%nat = (4 * n + 5)%nat) by lia. rewrite Hr8 in Ha.
  assert (Hr9 : (2 * (2 * n + 1) + 5)%nat = (4 * n + 7)%nat) by lia. rewrite Hr9 in Hb.
  assert (Hr10 : (2 * n + 1 + 2)%nat = (2 * n + 3)%nat) by lia. rewrite Hr10 in Hb.
  assert (Hr11 : (2 * S n)%nat = (2 * n + 2)%nat) by lia. rewrite Hr11.
  assert (Hr12 : (2 * n + 2 + 1)%nat = (2 * n + 3)%nat) by lia. rewrite Hr12.
  assert (HQS : forall (e f b0 c0 X Y R : Q),
    e * R == - b0 * X -> f * Y == - c0 * R -> e * (f * Y) == b0 * (c0 * X)).
  { intros e f b0 c0 X Y R K1 K2.
    assert (Pb1 : bid (Qeq_bool (e * R) (- b0 * X)) true)
      by (apply bidI; apply qeqbI; exact K1).
    assert (Pb2 : bid (Qeq_bool (f * Y) (- c0 * R)) true)
      by (apply bidI; apply qeqbI; exact K2).
    pose proof (r2_q_step2 e f b0 c0 X Y R Pb1 Pb2) as Hc.
    bidq Hc. exact Hc. }
  apply (HQS ((Z.of_nat (4 * n + 5)) # 1)%Q ((Z.of_nat (4 * n + 7)) # 1)%Q
              ((Z.of_nat ((2 * n + 2) * (2 * n + 2))) # 1)%Q
              ((Z.of_nat ((2 * n + 3) * (2 * n + 3))) # 1)%Q
              _ _ (r2_coef (2 * n + 1) (2 * n + 2))).
  - exact Ha.
  - exact Hb.
Defined.

(* ================= Section 4. The closed form by induction ================= *)

Fixpoint r2_fact (n : nat) : nat :=
  match n with
  | O => 1%nat
  | S m => S m * r2_fact m
  end.

Lemma r2_fact_add2 : forall m : nat,
  bid (Nat.eqb (r2_fact (m + 2)) (S (S m) * (S m * r2_fact m))) true.
Proof.
  intros m. apply bidI. apply (proj2 (Nat.eqb_eq _ _)).
  assert (Ef2 : (m + 2)%nat = (S (S m))%nat) by lia. rewrite Ef2.
  reflexivity.
Defined.

Lemma r2_fact_add4 : forall m : nat,
  bid (Nat.eqb (r2_fact (m + 4))
               (S (S (S (S m))) * (S (S (S m)) * (S (S m) * (S m * r2_fact m))))) true.
Proof.
  intros m. apply bidI. apply (proj2 (Nat.eqb_eq _ _)).
  assert (Ef4 : (m + 4)%nat = (S (S (S (S m))))%nat) by lia. rewrite Ef4.
  reflexivity.
Defined.

(* Binary factorial over Z: same values as r2_fact, computed in binary. *)
Fixpoint r2_zfact (n : nat) : Z :=
  match n with
  | O => 1%Z
  | S m => Z.of_nat (S m) * r2_zfact m
  end.

(* ================= Section 5. Computational anchors ================= *)

(* Oracle anchors for the composed two-step ratio, read straight off the  *)
(* tables by computation. *)
Lemma r2_step_anchor_0 :
  bid (Qeq_bool (((Z.of_nat (4 * 0 + 5)) # 1)%Q
                   * (((Z.of_nat (4 * 0 + 7)) # 1)%Q * r2_res1 1))
                (((Z.of_nat ((2 * 0 + 2) * (2 * 0 + 2))) # 1)%Q
                   * (((Z.of_nat ((2 * 0 + 3) * (2 * 0 + 3))) # 1)%Q * r2_res1 0))) true.
Proof. vm_compute. exact bidT. Defined.

Lemma r2_step_anchor_1 :
  bid (Qeq_bool (((Z.of_nat (4 * 1 + 5)) # 1)%Q
                   * (((Z.of_nat (4 * 1 + 7)) # 1)%Q * r2_res1 2))
                (((Z.of_nat ((2 * 1 + 2) * (2 * 1 + 2))) # 1)%Q
                   * (((Z.of_nat ((2 * 1 + 3) * (2 * 1 + 3))) # 1)%Q * r2_res1 1))) true.
Proof. vm_compute. exact bidT. Defined.

Lemma r2_step_anchor_2 :
  bid (Qeq_bool (((Z.of_nat (4 * 2 + 5)) # 1)%Q
                   * (((Z.of_nat (4 * 2 + 7)) # 1)%Q * r2_res1 3))
                (((Z.of_nat ((2 * 2 + 2) * (2 * 2 + 2))) # 1)%Q
                   * (((Z.of_nat ((2 * 2 + 3) * (2 * 2 + 3))) # 1)%Q * r2_res1 2))) true.
Proof. vm_compute. exact bidT. Defined.

(* Oracle anchors for the closed form at n = 1..3. *)
Lemma r2_closed_anchor_1 :
  bid (Qeq_bool (((r2_zfact (4 * 1 + 3)) # 1)%Q * r2_res1 1)
                (- ((2 ^ (Z.of_nat (2 * 1 + 1))
                      * r2_zfact (2 * 1 + 1) * r2_zfact (2 * 1 + 1)
                      * r2_zfact (2 * 1 + 1)) # 1)%Q)) true.
Proof. vm_compute. exact bidT. Defined.

Lemma r2_closed_anchor_2 :
  bid (Qeq_bool (((r2_zfact (4 * 2 + 3)) # 1)%Q * r2_res1 2)
                (- ((2 ^ (Z.of_nat (2 * 2 + 1))
                      * r2_zfact (2 * 2 + 1) * r2_zfact (2 * 2 + 1)
                      * r2_zfact (2 * 2 + 1)) # 1)%Q)) true.
Proof. vm_compute. exact bidT. Defined.

Lemma r2_closed_anchor_3 :
  bid (Qeq_bool (((r2_zfact (4 * 3 + 3)) # 1)%Q * r2_res1 3)
                (- ((2 ^ (Z.of_nat (2 * 3 + 1))
                      * r2_zfact (2 * 3 + 1) * r2_zfact (2 * 3 + 1)
                      * r2_zfact (2 * 3 + 1)) # 1)%Q)) true.
Proof. vm_compute. exact bidT. Defined.

(* ================= Section 6. Assumption audit ================= *)

Print Assumptions r2_q_minus_0.
Print Assumptions r2_msq_vsmul.
Print Assumptions r2_msq_vadd.
Print Assumptions r2_msq_shift.
Print Assumptions r2_q_linear.
Print Assumptions r2_q_zero_move.
Print Assumptions r2_q_ring_1.
Print Assumptions r2_q_ring_2.
Print Assumptions r2_q_step2.
Print Assumptions padeV_step_msq.
Print Assumptions padeU_step_nth.
Print Assumptions r2_coef_step.
Print Assumptions padeU_pad_beyond.
Print Assumptions r2_res1_coef.
Print Assumptions r2_ratio_step.
Print Assumptions r2_res1_step.
Print Assumptions r2_fact_add2.
Print Assumptions r2_fact_add4.
Print Assumptions r2_step_anchor_0.
Print Assumptions r2_step_anchor_1.
Print Assumptions r2_step_anchor_2.
Print Assumptions r2_closed_anchor_1.
Print Assumptions r2_closed_anchor_2.
Print Assumptions r2_closed_anchor_3.
