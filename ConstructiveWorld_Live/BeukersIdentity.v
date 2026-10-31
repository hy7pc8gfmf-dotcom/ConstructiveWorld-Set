(* ========================================================================== *)
(* BeukersIdentity.v -- Beukers-type q_n square-sum identity and the true     *)
(* normalization factor, carried on the rational layer.                       *)
(*                                                                            *)
(* Mission. The Delannoy-core reversal identity bi_D_eq_qtilde (the sum of    *)
(*   C(n,k)^2 with falling-power weights reverts to bk_Qn_qtilde n as an Id   *)
(*   of nat), the main pieces bi_core_qtilde / bi_norm_factor (QeqT carriers  *)
(*   bridging 2^(n+1) * q_n and 2^(2n+1) * Q_n(1/2)), the strict lower-bound  *)
(*   family bi_Qn_half_gt1 / bi_square_disc and the n=1 numeric anchors.      *)
(* Dependencies. S01_BaseRing, S02_CauchyComplete, S03_QExp,                  *)
(*   S07_RealSetoidExpLog (Id/eq conversion source), BeukersLists;            *)
(*   Stdlib QArith, Lists.List, Arith, ZArith, Lia, Setoid.                   *)
(* References. Integer-part identities of Apery-Beuker-type convergence       *)
(*   acceleration sequences (q_n = sum_k C(n,k)^2 and the 3^n growth law).    *)
(* Constructivity. Every piece ends in Qed with no classical logic;           *)
(*   statement faces ride Set-layer carriers (order predicates and equality  *)
(*   as Set values, zero Prop leakage); proof bodies introduce no extra       *)
(*   assumptions.                                                             *)
(* Build. rocq c -native-compiler no -q -Q . "" BeukersIdentity.v under the   *)
(*   cpu_guard wrapper, COQLIB/ROCQLIB unset, one flat -Q world root.         *)
(* ========================================================================== *)

From Stdlib Require Import QArith.QArith Lists.List Arith.Arith ZArith.ZArith Lia.
From Stdlib Require Import Setoid.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import BeukersLists.

(* QArith leaks Q_scope (bare numerals would parse as Q constructors); reopen nat first *)
Open Scope nat_scope.

(* ======================================================================== *)
(* Section A. Delannoy core (the rising-power sum carrier) and the reversal. *)
(*   bi_D n = sum_{k<=n} C(n,n-k)^2 * 2^(n-k); the change of variable        *)
(*   j = n-k turns it into the rising sum sum_{j<=n} C(n,j)^2 * 2^j          *)
(*   (the reversal is carried by the recursion structure of bk_psd).         *)
(* ======================================================================== *)

Definition bi_D (n : nat) : nat :=
  bk_psd (fun k => bkC n (n - k) * bkC n (n - k)) (Datatypes.S n).

(* Reversal: C(n,k)^2 symmetry (bk_Qn_sym) implies the reverted sum is the
   pointwise rearrangement of q~_n (the bk_psd_ext window k < S n iff k <= n
   is exactly the symmetric domain). *)
Lemma bi_D_eq_qtilde : forall n : nat, Id (bi_D n) (bk_Qn_qtilde n).
Proof.
  intro n. unfold bi_D, bk_Qn_qtilde.
  apply bk_psd_ext. intros k Hk.
  assert (Hkle : NatLe k n) by (pose proof (NatLe_drop _ _ Hk); apply NatLe_lift; lia).
  rewrite (RealSetoid.Id_eq _ _ (bk_Qn_sym n k Hkle)).
  reflexivity.
Qed.

(* Main piece 1: Delannoy core == q~_n (QeqT Set face) *)
Theorem bi_core_qtilde : forall n : nat,
  QeqT ((Z.of_nat (bi_D n) # 1)%Q) ((Z.of_nat (bk_Qn_qtilde n) # 1)%Q).
Proof.
  intro n. apply qeq_imp_qeqT.
  rewrite <- (RealSetoid.Id_eq _ _ (bi_D_eq_qtilde n)). reflexivity.
Qed.

(* Q-layer power of two: q_pow (2#1) n == Q#2^n (conversion helper) *)
Lemma bi_q_pow_2 : forall n : nat, QeqT (q_pow (2 # 1)%Q n) ((Z.of_nat (2 ^ n) # 1)%Q).
Proof.
  induction n as [| n IH].
  - apply qeq_imp_qeqT. reflexivity.
  - apply qeq_imp_qeqT. cbn [q_pow]. rewrite (qeqT_imp_qeq _ _ IH).
    replace (2 # 1)%Q with (Z.of_nat 2 # 1)%Q by reflexivity.
    replace (2 ^ Datatypes.S n)%nat with (2 * 2 ^ n)%nat by (cbn [Nat.pow]; lia).
    apply qeqT_imp_qeq. apply bk_Qmul_nat.
Qed.

(* ======================================================================== *)
(* Section B. Main piece 2: the true normalization closed form               *)
(*   2^(n+1) * q~_n == 2^(2n+1) * Q_n(1/2).                                  *)
(*   (The normalization slot of ln2 - x'_n = I_n / (2^(n+1) * q~_n);         *)
(*    2^(n+1) * q~_n = 2^(2n+1) * Q_n(1/2) is the correct landing point of   *)
(*    the 2^-(2n+1) normalization.)                                          *)
(* ======================================================================== *)

Theorem bi_norm_factor : forall n : nat,
  QeqT ((Z.of_nat (2 ^ (Datatypes.S n) * bk_Qn_qtilde n) # 1)%Q)
       ((q_pow (2 # 1)%Q (Datatypes.S (2 * n)) * bkQ (bk_Qn_list n) (1 # 2)%Q)%Q).
Proof.
  intro n. apply qeq_imp_qeqT.
  replace (Datatypes.S (2 * n))%nat with (Datatypes.S n + n)%nat by lia.
  rewrite (qeqT_imp_qeq _ _ (q_pow_add (2 # 1)%Q (Datatypes.S n) n)).
  transitivity ((q_pow (2 # 1)%Q (Datatypes.S n) * (Z.of_nat (bk_Qn_qtilde n) # 1))%Q).
  - rewrite (qeqT_imp_qeq _ _ (bi_q_pow_2 (Datatypes.S n))). apply Qeq_sym.
    apply qeqT_imp_qeq. apply bk_Qmul_nat.
  - assert (Hh := bk_Qn_half_closed n).
    rewrite <- Qmult_assoc. rewrite (qeqT_imp_qeq _ _ Hh). reflexivity.
Qed.

(* ======================================================================== *)
(* Section C. Q-layer support lemmas (Prop face, reasoning aids only).       *)
(* ======================================================================== *)

(* Same-denominator Qlt (direct Z-layer rendering) *)
Lemma bi_Qlt_same_den : forall (a b : Z) (d : positive),
  (a < b)%Z -> QltT (a # d) (b # d).
Proof.
  intros a b d Hab.
  apply Qlt_to_QltT.
  assert (Hd : (0 < Z.pos d)%Z) by apply Pos2Z.is_pos.
  unfold Qlt. cbn [Qnum Qden]. nia.
Qed.

(* Qlt transport along Qeq *)
Lemma bi_qlt_eq : forall a b c d : Q, QltT a b -> QeqT a c -> QeqT b d -> QltT c d.
Proof.
  intros a b c d Hab Hac Hbd.
  apply Qlt_to_QltT.
  rewrite <- (qeqT_imp_qeq _ _ Hac), <- (qeqT_imp_qeq _ _ Hbd).
  exact (QltT_to_Qlt _ _ Hab).
Qed.

(* Positive Q-power *)
Lemma bi_q_pow_pos2 : forall n : nat, QltT 0%Q (q_pow (2 # 1)%Q n).
Proof.
  intro n. apply Qlt_to_QltT.
  induction n as [| n IH].
  - cbn [q_pow]. unfold Qlt. cbn [Qnum Qden]. lia.
  - cbn [q_pow]. apply Qmult_lt_0_compat.
    + unfold Qlt. cbn [Qnum Qden]. lia.
    + exact IH.
Qed.

(* Positive-product cancellation: a*q < c*q with 0 < q implies a < c *)
Lemma bi_Qlt_mul_cancel_r : forall a c q : Q,
  QltT 0%Q q -> QltT (a * q)%Q (c * q)%Q -> QltT a c.
Proof.
  intros a c q Hq0 Hlt.
  apply Qlt_to_QltT.
  destruct (Qlt_le_dec a c) as [Hac | Hca].
  - exact Hac.
  - exfalso. apply (Qlt_not_le (a * q)%Q (c * q)%Q (QltT_to_Qlt _ _ Hlt)).
    apply Qmult_le_compat_r.
    + exact Hca.
    + apply Qlt_le_weak. exact (QltT_to_Qlt _ _ Hq0).
Qed.

(* 3^k > 0 (power positivity, feeding nia/lia) *)
Lemma bi_pow3_pos : forall k : nat, Id (Nat.ltb 0 (3 ^ k)) true.
Proof.
  intro k.
  assert (Hp : (0 < 3 ^ k)%nat) by (induction k as [| k IH]; cbn [Nat.pow]; lia).
  destruct (Nat.ltb 0 (3 ^ k)) eqn:E.
  - reflexivity.
  - exfalso. pose proof (proj1 (Nat.ltb_ge 0 (3 ^ k)) E). lia.
Qed.

(* 2^n < 3^n (n >= 1) *)
Lemma bi_half_gt_nat : forall n : nat, NatLe 1 n -> Id (Nat.ltb (2 ^ n) (3 ^ n)) true.
Proof.
  intros n Hn.
  assert (Hn' : (1 <= n)%nat) by (apply NatLe_drop; exact Hn).
  assert (Hlt : forall m : nat, (1 <= m)%nat -> (2 ^ m < 3 ^ m)%nat).
  { induction m as [| m IH]; intros Hm.
    - cbn [Nat.pow]. lia.
    - destruct m as [| j].
      + cbn [Nat.pow]. lia.
      + assert (Hj : 1 <= Datatypes.S j) by lia. specialize (IH Hj).
        assert (Hp : (0 < 3 ^ Datatypes.S j)%nat).
        { pose proof (bi_pow3_pos (Datatypes.S j)) as HpI.
          destruct (Nat.ltb 0 (3 ^ Datatypes.S j)) eqn:E.
          - apply (proj1 (Nat.ltb_lt 0 (3 ^ Datatypes.S j))). exact E.
          - inversion HpI. }
        rewrite (Nat.pow_succ_r' 2 (Datatypes.S j)), (Nat.pow_succ_r' 3 (Datatypes.S j)).
        nia. }
  pose proof (Hlt n Hn') as Hltf.
  destruct (Nat.ltb (2 ^ n) (3 ^ n)) eqn:E.
  - reflexivity.
  - exfalso. pose proof (proj1 (Nat.ltb_ge (2 ^ n) (3 ^ n)) E). lia.
Qed.

(* ======================================================================== *)
(* Section D. The half-integer lower bound and the refutation piece.         *)
(* ======================================================================== *)

Theorem bi_Qn_half_gt1 : forall n : nat, NatLe 1 n ->
  QltT (1 # 1)%Q (bkQ (bk_Qn_list n) (1 # 2)%Q).
Proof.
  intros n Hn.
  pose proof (NatLe_drop _ _ (bk_Qn_ge_3pow_nat n)) as Hge.
  assert (H23 : (2 ^ n < 3 ^ n)%nat).
  { pose proof (bi_half_gt_nat n Hn) as H23I.
    destruct (Nat.ltb (2 ^ n) (3 ^ n)) eqn:E.
    - apply (proj1 (Nat.ltb_lt (2 ^ n) (3 ^ n))). exact E.
    - inversion H23I. }
  assert (Hq : (2 ^ n < bk_Qn_qtilde n)%nat) by lia.
  assert (Hz : (Z.of_nat (2 ^ n) < Z.of_nat (bk_Qn_qtilde n))%Z)
    by (apply Nat2Z.inj_lt; exact Hq).
  assert (HQ : QltT (Z.of_nat (2 ^ n) # 1) (Z.of_nat (bk_Qn_qtilde n) # 1))
    by (apply bi_Qlt_same_den; exact Hz).
  assert (Hh := bk_Qn_half_closed n).
  assert (HQ2 : QltT ((q_pow (2 # 1)%Q n * (1 # 1))%Q)
                     ((q_pow (2 # 1)%Q n * bkQ (bk_Qn_list n) (1 # 2))%Q)).
  { apply (bi_qlt_eq _ _ _ _ HQ).
    - apply qeq_imp_qeqT. rewrite (qeqT_imp_qeq _ _ (bi_q_pow_2 n)). symmetry.
      apply Qmult_1_r.
    - apply qeq_imp_qeqT. apply Qeq_sym. exact (qeqT_imp_qeq _ _ Hh). }
  assert (HQ3 : QltT (1 # 1)%Q (bkQ (bk_Qn_list n) (1 # 2)%Q)).
  { apply (bi_Qlt_mul_cancel_r (1 # 1)%Q (bkQ (bk_Qn_list n) (1 # 2)%Q)
             (q_pow (2 # 1)%Q n)).
    - apply bi_q_pow_pos2.
    - apply (bi_qlt_eq _ _ _ _ HQ2); apply qeq_imp_qeqT; ring. }
  exact HQ3.
Qed.

(* Q_n(1/2) <> 1 (n >= 1) -- the refutation piece forcing Q_n(1/2) == 1 *)
Lemma bi_half_not1 : forall n : nat, NatLe 1 n ->
  Not (QeqT (bkQ (bk_Qn_list n) (1 # 2)%Q) (1 # 1)%Q).
Proof.
  intros n Hn He.
  assert (Hlt : Qlt (1 # 1)%Q (bkQ (bk_Qn_list n) (1 # 2)%Q))
    by (apply QltT_to_Qlt, bi_Qn_half_gt1, Hn).
  exact (False_rect Empty_set
          (Qlt_not_eq (1 # 1)%Q (bkQ (bk_Qn_list n) (1 # 2)%Q) Hlt
             (Qeq_sym _ _ (qeqT_imp_qeq _ _ He)))).
Qed.

(* ======================================================================== *)
(* Section E. Main piece 4: the square-normalization separation witness      *)
(*   (x < x^2 for n >= 1 everywhere), which would force                      *)
(*   Q_n(1/2)^2 == Q_n(1/2), i.e. Q_n(1/2) == 1 -- refuted in Section D.     *)
(* ======================================================================== *)

Theorem bi_square_disc : forall n : nat, NatLe 1 n ->
  QltT (bkQ (bk_Qn_list n) (1 # 2)%Q)
       ((bkQ (bk_Qn_list n) (1 # 2)%Q * bkQ (bk_Qn_list n) (1 # 2)%Q)%Q).
Proof.
  intros n Hn.
  assert (Hlt := bi_Qn_half_gt1 n Hn).
  assert (H2 : QltT ((1 # 1)%Q * bkQ (bk_Qn_list n) (1 # 2)%Q)
                    ((bkQ (bk_Qn_list n) (1 # 2)%Q * bkQ (bk_Qn_list n) (1 # 2)%Q))%Q).
  { apply Qlt_to_QltT.
    apply Qmult_lt_compat_r.
    - apply (Qlt_trans 0%Q (1 # 1)%Q).
      + unfold Qlt. cbn [Qnum Qden]. lia.
      + exact (QltT_to_Qlt _ _ Hlt).
    - exact (QltT_to_Qlt _ _ Hlt). }
  apply (bi_qlt_eq _ _ _ _ H2); apply qeq_imp_qeqT; ring.
Qed.

(* ======================================================================== *)
(* Section F. Numeric anchors (n=1: q~_1 = 3, 2^(2*1+1) * Q_1(1/2) = 12,     *)
(*   Q_1(1/2) = 3/2).                                                        *)
(* ======================================================================== *)

Theorem bi_n1_anchor : QeqT ((Z.of_nat (2 ^ 2 * bk_Qn_qtilde 1) # 1)%Q) (12 # 1)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem bi_Qn_half_n1 : QeqT (bkQ (bk_Qn_list 1) (1 # 2)%Q) (3 # 2)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

(* ======================================================================== *)
(* Assumption audit: Print Assumptions                                       *)
(* ======================================================================== *)

Print Assumptions bi_core_qtilde.
Print Assumptions bi_norm_factor.
Print Assumptions bi_Qn_half_gt1.
Print Assumptions bi_square_disc.
Print Assumptions bi_n1_anchor.
Print Assumptions bi_Qn_half_n1.
