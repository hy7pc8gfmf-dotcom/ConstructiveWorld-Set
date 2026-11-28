(* ========================================================================= *)
(* Module   : tlw1463_pade_r29_faces                                        *)
(* Mission. The four algebraic faces of the Lambert three-term table        *)
(*   (tlw1463_pade_table) at w = 1, all carried by Set via the boolean      *)
(*   carrier bid with decidable order tests: (1) the adjacent-pair          *)
(*   determinant identity V_{j+1} U_j - V_j U_{j+1} = (-1)^j ((j+1)!)^2;    *)
(*   (2) its alternating sign (even indices positive, odd negative);        *)
(*   (3) the nonzero lower bound 3((2n+1)!)^2 / V_{2n+1}(1) > 0; (4) the    *)
(*   relative decay gap_n <= (71/100000) (21/100)^n under the explicit      *)
(*   one-step gap premise slot, with computed anchors for n <= 3.           *)
(* Dependencies. tlw1463_pade_table (bid/bidI/bidE/qeqbI, vadd/vsmul,       *)
(*   vleeq, q_pown, pade_rho_hat, altsign, padeU/padeV, pade_pair,          *)
(*   pade_pair_step, nat_double_ind); Stdlib QArith, ZArith, List, Setoid,  *)
(*   Lia, QArith.Qring.                                                     *)
(* References. Statement names carried over verbatim from the baseline      *)
(*   module tlw1463_pade_r29_faces; K. Mahler, On the approximation of pi,  *)
(*   Indagationes Math. 15 (1953), the classical source of the Lambert      *)
(*   continued-fraction convergent determinant identity.                    *)
(* Constructivity. Every named statement is Set-carried; every predicate    *)
(*   position is a decidable test (Qeq_bool, Qle_bool, the componentwise    *)
(*   strict test Qltb, Nat/Z boolean tests) under bid, so conclusions      *)
(*   extract; no sigT and no Prop-bearing component occurs inside any      *)
(*   carrier. Constructive Prop reasoning stays inside proof bodies: Q     *)
(*   order reduces componentwise to integer lia/nia. The only Prop-typed   *)
(*   items are transparent one-line reflection bridges (qltb_true,         *)
(*   qltb_of_lt, qleb_true, qleb_of_le, bidQeq, bidQlt, bidQle, bidZlt,    *)
(*   bidZle, bidNlt, qltb_bid, qleb_bid, bidQlt_move, bidQlt_moveR),       *)
(*   consumed inside proofs only; zero Qed in this file.                   *)
(* Build. rocq c -native-compiler no -q -Q <live root> "" (single shot).        *)
(* ========================================================================= *)

From Stdlib Require Import QArith.
From Stdlib Require Import ZArith.
From Stdlib Require Import QArith.Qring.
From Stdlib Require Import List.
From Stdlib Require Import Setoid.
From Stdlib Require Import Lia.
Require Import tlw1463_pade_table.
Import ListNotations.
(* ============================================================ *)
(* Section 1: reflection bridges, the only Prop-typed items of   *)
(* this file. Qltb is the componentwise decidable strict order   *)
(* test on Q; the bridges move facts between its boolean form    *)
(* and the ordinary Q order, always transparently.               *)
(* ============================================================ *)

Definition Qltb (x y : Q) : bool := Z.ltb (Qnum x * QDen y) (Qnum y * QDen x).

Definition qltb_true (x y : Q) (H : Qltb x y = true) : (x < y)%Q :=
  proj1 (Z.ltb_lt (Qnum x * QDen y) (Qnum y * QDen x)) H.
Definition qltb_of_lt (x y : Q) (H : (x < y)%Q) : Qltb x y = true :=
  proj2 (Z.ltb_lt (Qnum x * QDen y) (Qnum y * QDen x)) H.
Definition qleb_true (x y : Q) (H : Qle_bool x y = true) : (x <= y)%Q :=
  proj1 (Z.leb_le (Qnum x * QDen y) (Qnum y * QDen x)) H.
Definition qleb_of_le (x y : Q) (H : (x <= y)%Q) : Qle_bool x y = true :=
  proj2 (Z.leb_le (Qnum x * QDen y) (Qnum y * QDen x)) H.
Definition bidQeq (x y : Q) (H : bid (Qeq_bool x y) true) : x == y :=
  Qeq_bool_eq x y (bidE (Qeq_bool x y) H).
Definition bidQlt (x y : Q) (H : bid (Qltb x y) true) : (x < y)%Q :=
  qltb_true x y (bidE (Qltb x y) H).
Definition bidQle (x y : Q) (H : bid (Qle_bool x y) true) : (x <= y)%Q :=
  qleb_true x y (bidE (Qle_bool x y) H).
Definition bidZlt (x y : Z) (H : bid (Z.ltb x y) true) : (x < y)%Z :=
  proj1 (Z.ltb_lt x y) (bidE (Z.ltb x y) H).
Definition bidZle (x y : Z) (H : bid (Z.leb x y) true) : (x <= y)%Z :=
  proj1 (Z.leb_le x y) (bidE (Z.leb x y) H).
Definition bidNlt (n m : nat) (H : bid (Nat.ltb n m) true) : (n < m)%nat :=
  proj1 (Nat.ltb_lt n m) (bidE (Nat.ltb n m) H).
Definition qltb_bid (x y : Q) (H : (x < y)%Q) : bid (Qltb x y) true :=
  bidI (Qltb x y) (qltb_of_lt x y H).
Definition qleb_bid (x y : Q) (H : (x <= y)%Q) : bid (Qle_bool x y) true :=
  bidI (Qle_bool x y) (qleb_of_le x y H).

Lemma bidQlt_move : forall x y z : Q,
  x == y -> bid (Qltb x z) true -> bid (Qltb y z) true.
Proof.
  intros x y z Hxy H. apply bidI. apply qltb_of_lt.
  rewrite <- Hxy. apply (bidQlt x z H).
Defined.

Lemma bidQlt_moveR : forall x y z : Q,
  x == y -> bid (Qltb z x) true -> bid (Qltb z y) true.
Proof.
  intros x y z Hxy H. apply bidI. apply qltb_of_lt.
  rewrite <- Hxy. apply (bidQlt z x H).
Defined.

Lemma qlt_le_weakB : forall x y : Q,
  bid (Qltb x y) true -> bid (Qle_bool x y) true.
Proof.
  intros x y H. apply bidI. apply qleb_of_le.
  apply Qlt_le_weak. exact (bidQlt x y H).
Defined.


(* ============================================================ *)
(* Section 2: table evaluation at w = 1. The value of the table  *)
(* at w = 1 is the coefficient sum; the factorial entering the   *)
(* determinant identity never vanishes.                         *)
(* ============================================================ *)

Definition padeU1 (k : nat) : Q := fold_right Qplus 0%Q (padeU k).
Definition padeV1 (k : nat) : Q := fold_right Qplus 0%Q (padeV k).

Fixpoint natfact (n : nat) : nat :=
  match n with
  | O => 1%nat
  | S m => S m * natfact m
  end.

Lemma natfact_pos : forall n : nat, bid (Nat.ltb 0 (natfact n)) true.
Proof.
  induction n as [|n IH]; apply bidI; apply (proj2 (Nat.ltb_lt 0 _)).
  - cbn [natfact]. lia.
  - cbn [natfact]. pose proof (bidNlt 0%nat (natfact n) IH) as Hp. nia.
Defined.

(* ============================================================ *)
(* Section 3: the evaluation homomorphisms and the one-step      *)
(* recursion at w = 1: U_{m+2}(1) = (2m+5) U_{m+1}(1) +          *)
(* (m+2)^2 U_m(1), likewise on the denominator side.             *)
(* ============================================================ *)

Lemma val1_vadd : forall a b : list Q,
  bid (Qeq_bool (fold_right Qplus 0%Q (vadd a b))
                (fold_right Qplus 0%Q a + fold_right Qplus 0%Q b)) true.
Proof.
  intros a. induction a as [|x a' IH]; intros b; destruct b as [|y b']; apply bidI.
  - apply qeqbI. cbn [vadd fold_right]. rewrite Qplus_0_l. apply Qeq_refl.
  - apply qeqbI. cbn [vadd fold_right]. rewrite Qplus_0_l. apply Qeq_refl.
  - apply qeqbI. cbn [vadd fold_right]. rewrite Qplus_0_r. apply Qeq_refl.
  - specialize (IH b'). apply bidE in IH. apply Qeq_bool_eq in IH.
    apply qeqbI. cbn [vadd fold_right]. rewrite IH. ring.
Defined.

Lemma val1_vsmul : forall (c : Q) (l : list Q),
  bid (Qeq_bool (fold_right Qplus 0%Q (vsmul c l))
                (c * fold_right Qplus 0%Q l)) true.
Proof.
  intros c l. induction l as [|x t IH]; apply bidI.
  - apply qeqbI. cbn [vsmul fold_right]. rewrite Qmult_0_r. apply Qeq_refl.
  - apply qeqbI. cbn [vsmul fold_right].
    apply bidE in IH. apply Qeq_bool_eq in IH.
    rewrite IH. rewrite Qmult_plus_distr_r. apply Qeq_refl.
Defined.

Lemma padeU1_step : forall m : nat,
  bid (Qeq_bool (padeU1 (S (S m)))
                (((Z.of_nat (2 * S (S m) + 1)) # 1)%Q * padeU1 (S m)
                 + ((Z.of_nat (S (S m) * S (S m))) # 1)%Q * padeU1 m)) true.
Proof.
  intros m. apply bidI. apply qeqbI.
  unfold padeU1, padeU.
  destruct (pade_pair m) as [[u0 u1][v0 v1]] eqn:Em.
  rewrite (pade_pair_step (S m)).
  rewrite (pade_pair_step m).
  rewrite Em.
  cbn [fst snd].
  rewrite (bidQeq _ _ (val1_vadd _ _)).
  rewrite (bidQeq _ _ (val1_vsmul _ _)).
  rewrite (bidQeq _ _ (val1_vsmul _ _)).
  cbn [fold_right].
  rewrite Qplus_0_l.
  apply Qeq_refl.
Defined.

Lemma padeV1_step : forall m : nat,
  bid (Qeq_bool (padeV1 (S (S m)))
                (((Z.of_nat (2 * S (S m) + 1)) # 1)%Q * padeV1 (S m)
                 + ((Z.of_nat (S (S m) * S (S m))) # 1)%Q * padeV1 m)) true.
Proof.
  intros m. apply bidI. apply qeqbI.
  unfold padeV1, padeV.
  destruct (pade_pair m) as [[u0 u1][v0 v1]] eqn:Em.
  rewrite (pade_pair_step (S m)).
  rewrite (pade_pair_step m).
  rewrite Em.
  cbn [fst snd].
  rewrite (bidQeq _ _ (val1_vadd _ _)).
  rewrite (bidQeq _ _ (val1_vsmul _ _)).
  rewrite (bidQeq _ _ (val1_vsmul _ _)).
  cbn [fold_right].
  rewrite Qplus_0_l.
  apply Qeq_refl.
Defined.

(* ============================================================ *)
(* Section 4: the determinant D_j := V_{j+1} U_j - V_j U_{j+1},  *)
(* its one-step recursion D_{m+1} = -(m+2)^2 D_m, and the        *)
(* closed identity D_j = (-1)^j ((j+1)!)^2.                      *)
(* ============================================================ *)

Definition pade_det (j : nat) : Q :=
  padeV1 (S j) * padeU1 j - padeV1 j * padeU1 (S j).

Lemma qmul_one : forall z w : Z,
  bid (Qeq_bool (((z * w) # 1)%Q) (((z # 1)%Q * (w # 1)%Q))) true.
Proof.
  intros z w. apply bidI. apply qeqbI. apply Qeq_refl.
Defined.

Lemma qneg_one_mul : forall z : Z,
  bid (Qeq_bool ((Z.opp z # 1)%Q) ((- (z # 1)%Q))) true.
Proof.
  intros z. apply bidI. apply qeqbI. apply Qeq_refl.
Defined.

Lemma pade_det_step : forall m : nat,
  bid (Qeq_bool (pade_det (S m))
                ((-(Z.of_nat (S (S m) * S (S m))) # 1)%Q * pade_det m)) true.
Proof.
  intros m. apply bidI. apply qeqbI. unfold pade_det.
  rewrite (bidQeq _ _ (padeV1_step m)).
  rewrite (bidQeq _ _ (padeU1_step m)).
  rewrite (bidQeq _ _ (qneg_one_mul (Z.of_nat (S (S m) * S (S m))))).
  ring.
Defined.

Lemma altsign_step : forall n : nat,
  bid (Z.eqb (altsign (S n)) (Z.opp (altsign n))) true.
Proof.
  intros n. apply bidI. unfold altsign.
  rewrite Nat.even_succ, <- Nat.negb_even.
  destruct (Nat.even n); reflexivity.
Defined.

Definition pade_det_identity (j : nat) : Set :=
  bid (Qeq_bool (padeV1 (S j) * padeU1 j - padeV1 j * padeU1 (S j))
                ((altsign j * Z.of_nat (natfact (S j) * natfact (S j))) # 1)%Q) true.

Lemma pade_det_identity_G : forall j : nat, pade_det_identity j.
Proof.
  apply nat_double_ind.
  - apply bidI. vm_compute. reflexivity.
  - apply bidI. vm_compute. reflexivity.
  - intros m IHm IHSm.
    apply bidE in IHSm. apply Qeq_bool_eq in IHSm.
    fold (pade_det (S m)) in IHSm.
    apply bidI. apply qeqbI.
    change (pade_det (S (S m))
              == ((altsign (S (S m))
                   * Z.of_nat (natfact (S (S (S m))) * natfact (S (S (S m))))) # 1)%Q).
    rewrite (bidQeq _ _ (pade_det_step (S m))).
    rewrite IHSm.
    assert (Has : altsign (S (S m)) = (- altsign (S m))%Z).
    { apply (proj1 (Z.eqb_eq (altsign (S (S m))) (Z.opp (altsign (S m))))).
      apply bidE. apply altsign_step. }
    rewrite Has.
    unfold altsign.
    rewrite Nat.even_succ, <- Nat.negb_even.
    destruct (Nat.even m) eqn:Em; cbn [negb] in *;
      unfold Qeq;
      cbn [Qnum Qden Qmult Qminus Qopp Qplus Pos.mul];
      cbn [natfact];
      rewrite ?Nat2Z.inj_mul;
      rewrite ?Nat2Z.inj_succ;
      rewrite <- ?Z.add_1_r;
      ring.
Defined.

Lemma pade_det_anchors :
  bid (vleeq (map pade_det (seq 0 10))
             (((1 # 1) :: ((-4) # 1) :: (36 # 1) :: ((-576) # 1) :: (14400 # 1) ::
               ((-518400) # 1) :: (25401600 # 1) :: ((-1625702400) # 1) ::
               (131681894400 # 1) :: ((-13168189440000) # 1) :: nil)%Q)) true.
Proof.
  apply bidI. vm_compute. reflexivity.
Defined.

(* ============================================================ *)
(* Section 5: componentwise order kit on Q, all Set-carried.     *)
(* ============================================================ *)

Lemma qden_pos : forall x : Q, bid (Z.ltb 0 (Z.pos (Qden x))) true.
Proof.
  intros [n d]. apply bidI. apply (proj2 (Z.ltb_lt 0 (Z.pos d))).
  apply Pos2Z.is_pos.
Defined.

Lemma qpos_mul : forall a b : Q,
  bid (Qltb (0 # 1)%Q a) true -> bid (Qltb (0 # 1)%Q b) true ->
  bid (Qltb (0 # 1)%Q (a * b)) true.
Proof.
  intros a b Ha Hb. apply bidI. apply qltb_of_lt.
  pose proof (bidQlt (0 # 1)%Q a Ha) as HA.
  pose proof (bidQlt (0 # 1)%Q b Hb) as HB.
  unfold Qlt in *. cbn [Qnum Qden Qmult] in *. nia.
Defined.

Lemma qpos_add_le : forall a b : Q,
  bid (Qltb (0 # 1)%Q a) true -> bid (Qle_bool (0 # 1)%Q b) true ->
  bid (Qltb (0 # 1)%Q (a + b)) true.
Proof.
  intros a b Ha Hb. apply bidI. apply qltb_of_lt.
  pose proof (bidQlt (0 # 1)%Q a Ha) as HA.
  pose proof (bidQle (0 # 1)%Q b Hb) as HB.
  pose proof (bidZlt 0%Z (Z.pos (Qden a)) (qden_pos a)) as HDA.
  pose proof (bidZlt 0%Z (Z.pos (Qden b)) (qden_pos b)) as HDB.
  unfold Qlt, Qle in *. cbn [Qnum Qden Qplus Qmult] in *.
  rewrite ?Z.mul_0_l, ?Z.mul_1_r in *.
  assert (Hp1 : (0 < Qnum a * QDen b)%Z)
    by (apply Z.mul_pos_pos; [exact HA | exact HDB]).
  assert (Hp2 : (0 <= Qnum b * QDen a)%Z).
  { destruct (Z_lt_le_dec 0 (Qnum b)) as [Hc | Hc].
    - apply Z.lt_le_incl. apply Z.mul_pos_pos; [exact Hc | exact HDA].
    - assert (Hb0 : (Qnum b = 0)%Z) by (apply Z.le_antisymm; [exact Hc | exact HB]).
      rewrite Hb0, Z.mul_0_l. apply Z.le_refl. }
  apply (Z.lt_le_trans 0%Z (Qnum a * QDen b) (Qnum a * QDen b + Qnum b * QDen a)).
  - exact Hp1.
  - rewrite <- (Z.add_0_r (Qnum a * QDen b)) at 1.
    apply Z.add_le_mono; [apply Z.le_refl | exact Hp2].
Defined.

Lemma qle_add_r : forall x t : Q,
  bid (Qle_bool (0 # 1)%Q t) true -> bid (Qle_bool x (x + t)) true.
Proof.
  intros x t Ht. apply bidI. apply qleb_of_le.
  pose proof (bidQle (0 # 1)%Q t Ht) as HT.
  pose proof (bidZlt 0%Z (Z.pos (Qden x)) (qden_pos x)) as HDX.
  pose proof (bidZlt 0%Z (Z.pos (Qden t)) (qden_pos t)) as HDT.
  unfold Qle in *. cbn [Qnum Qden Qplus Qmult] in *.
  rewrite Pos2Z.inj_mul.
  nia.
Defined.

Lemma natfact_sq_qpos : forall k : nat,
  bid (Qltb (0 # 1)%Q (((Z.of_nat (natfact k) * Z.of_nat (natfact k)) # 1)%Q)) true.
Proof.
  intros k. apply bidI. apply qltb_of_lt.
  pose proof (bidNlt 0%nat (natfact k) (natfact_pos k)) as Hp.
  unfold Qlt. cbn [Qnum Qden]. nia.
Defined.

Lemma qdiv_pos : forall a b : Q,
  bid (Qltb (0 # 1)%Q a) true -> bid (Qltb (0 # 1)%Q b) true ->
  bid (Qltb (0 # 1)%Q (a / b)) true.
Proof.
  intros a b Ha Hb. unfold Qdiv. apply qpos_mul; [exact Ha |].
  destruct b as [n d]. destruct n as [|p|p].
  - pose proof (bidQlt (0 # 1)%Q ((0 # d)%Q) Hb) as HC.
    apply (False_rect _).
    unfold Qlt in HC. cbn [Qnum Qden] in HC. lia.
  - apply bidI. apply qltb_of_lt. cbn [Qinv Qnum Qden].
    assert (Hd : (0 < Z.pos d)%Z) by apply Pos2Z.is_pos.
    unfold Qlt. cbn [Qnum Qden]. lia.
  - pose proof (bidQlt (0 # 1)%Q ((Z.neg p # d)%Q) Hb) as HC.
    apply (False_rect _).
    pose proof (Pos2Z.neg_is_neg p) as HN.
    unfold Qlt in HC. cbn [Qnum Qden] in HC. lia.
Defined.

Lemma qle_mul_pos : forall n d : Z,
  bid (Z.leb 0 n) true -> bid (Z.ltb 0 d) true -> bid (Z.leb 0 (n * d)) true.
Proof.
  intros n d Hn Hd. apply bidI. apply (proj2 (Z.leb_le 0 (n * d))).
  pose proof (bidZle 0%Z n Hn) as HN.
  pose proof (bidZlt 0%Z d Hd) as HD.
  destruct (Z_lt_le_dec 0 n) as [H | H].
  - assert (Hp : (0 < n * d)%Z) by nia.
    apply Z.lt_le_incl. exact Hp.
  - nia.
Defined.

Lemma qle_mul_nonneg_Z : forall n d : Z,
  bid (Z.leb 0 n) true -> bid (Z.leb 0 d) true -> bid (Z.leb 0 (n * d)) true.
Proof.
  intros n d Hn Hd. apply bidI. apply (proj2 (Z.leb_le 0 (n * d))).
  pose proof (bidZle 0%Z n Hn) as HN.
  pose proof (bidZle 0%Z d Hd) as HD.
  destruct (Z_lt_le_dec 0 d) as [H | H].
  - nia.
  - assert (E : (d = 0)%Z) by (apply Z.le_antisymm; [exact H | exact HD]).
    rewrite E, Z.mul_0_r. lia.
Defined.

Lemma qle_mul_nonneg : forall a b : Q,
  bid (Qle_bool (0 # 1)%Q a) true -> bid (Qle_bool (0 # 1)%Q b) true ->
  bid (Qle_bool (0 # 1)%Q (a * b)) true.
Proof.
  intros a b Ha Hb. apply bidI. apply qleb_of_le.
  pose proof (bidQle (0 # 1)%Q a Ha) as HA.
  pose proof (bidQle (0 # 1)%Q b Hb) as HB.
  pose proof (bidZlt 0%Z (Z.pos (Qden a)) (qden_pos a)) as HDA.
  pose proof (bidZlt 0%Z (Z.pos (Qden b)) (qden_pos b)) as HDB.
  unfold Qle in *. cbn [Qnum Qden Qmult] in *. nia.
Defined.

Lemma qpos_qneg_mul : forall a b : Q,
  bid (Qltb (0 # 1)%Q a) true -> bid (Qltb b (0 # 1)%Q) true ->
  bid (Qltb (b * a) (0 # 1)%Q) true.
Proof.
  intros a b Ha Hb. apply bidI. apply qltb_of_lt.
  pose proof (bidQlt (0 # 1)%Q a Ha) as HA.
  pose proof (bidQlt b (0 # 1)%Q Hb) as HB.
  unfold Qlt in *. cbn [Qnum Qden Qmult] in *. nia.
Defined.

(** The denominator-side table value is strictly positive: V_k(1) > 0. *)
Lemma padeV1_pos : forall k : nat, bid (Qltb (0 # 1)%Q (padeV1 k)) true.
Proof.
  apply nat_double_ind.
  - apply bidI. vm_compute. reflexivity.
  - apply bidI. vm_compute. reflexivity.
  - intros m IHm IHSm.
    apply (bidQlt_moveR _ _ _ (Qeq_sym _ _ (bidQeq _ _ (padeV1_step m)))).
    apply qpos_add_le.
    + apply qpos_mul.
      * apply bidI. apply qltb_of_lt.
        assert (Hpos : (0 < 2 * S (S m) + 1)%nat) by lia.
        unfold Qlt. cbn [Qnum Qden]. lia.
      * exact IHSm.
    + apply qle_mul_nonneg.
      * apply bidI. apply qleb_of_le. unfold Qle. cbn [Qnum Qden]. lia.
      * apply qlt_le_weakB. exact IHm.
Defined.

(* ============================================================ *)
(* Section 6: the alternating sign of the determinant:           *)
(* D_{m+2} = (m+3)^2 (m+4)^2 D_m, D_{2n} > 0, D_{2n+1} < 0, and  *)
(* the sign flip across each adjacent pair.                      *)
(* ============================================================ *)

Lemma pade_det_two_step : forall m : nat,
  bid (Qeq_bool (pade_det (S (S m)))
                (((Z.of_nat (S (S (S m)) * S (S (S m))))
                  * (Z.of_nat (S (S m) * S (S m))) # 1)%Q * pade_det m)) true.
Proof.
  intros m. apply bidI. apply qeqbI.
  rewrite (bidQeq _ _ (pade_det_step (S m))).
  rewrite (bidQeq _ _ (pade_det_step m)).
  rewrite (bidQeq _ _ (qmul_one (Z.of_nat (S (S (S m)) * S (S (S m))))
                                (Z.of_nat (S (S m) * S (S m))))).
  rewrite (bidQeq _ _ (qneg_one_mul (Z.of_nat (S (S (S m)) * S (S (S m)))))).
  rewrite (bidQeq _ _ (qneg_one_mul (Z.of_nat (S (S m) * S (S m))))).
  ring.
Defined.

Lemma pade_det_pos_even : forall n : nat,
  bid (Qltb (0 # 1)%Q (pade_det (2 * n))) true.
Proof.
  apply nat_double_ind.
  - apply bidI. vm_compute. reflexivity.
  - apply bidI. vm_compute. reflexivity.
  - intros m IHm IHSm.
    replace (pade_det (2 * S (S m))) with (pade_det (S (S (S (S (2 * m)))))) by (f_equal; lia).
    apply (bidQlt_moveR _ _ _ (Qeq_sym _ _ (bidQeq _ _ (pade_det_two_step (S (S (2 * m))))))).
    replace (pade_det (S (S (2 * m)))) with (pade_det (2 * S m)) by (f_equal; lia).
    apply qpos_mul.
    + apply bidI. apply qltb_of_lt.
      unfold Qlt. cbn [Qnum Qden].
      rewrite ?Nat2Z.inj_mul.
      assert (Hb1 : (0 < Z.of_nat (S (S (S m))) * Z.of_nat (S (S (S m))))%Z)
        by (apply Z.mul_pos_pos; lia).
      assert (Hb2 : (0 < Z.of_nat (S (S m)) * Z.of_nat (S (S m)))%Z)
        by (apply Z.mul_pos_pos; lia).
      assert (Hc2 : (0 < Z.of_nat (S (S (S m))) * Z.of_nat (S (S (S m)))
                             * (Z.of_nat (S (S m)) * Z.of_nat (S (S m))))%Z)
        by (apply Z.mul_pos_pos; [exact Hb1 | exact Hb2]).
      rewrite Z.mul_0_l, Z.mul_1_r.
      exact Hc2.
    + exact IHSm.
Defined.

Lemma pade_det_neg_odd : forall n : nat,
  bid (Qltb (pade_det (2 * n + 1)) (0 # 1)%Q) true.
Proof.
  intros n.
  replace (2 * n + 1)%nat with (S (2 * n))%nat by lia.
  apply (bidQlt_move _ _ _ (Qeq_sym _ _ (bidQeq _ _ (pade_det_step (2 * n))))).
  apply qpos_qneg_mul.
  - apply pade_det_pos_even.
  - apply bidI. apply qltb_of_lt.
    unfold Qlt. cbn [Qnum Qden]. lia.
Defined.

Lemma pade_step_between_even : forall n : nat,
  bid (Qltb (pade_det (2 * n + 1) * pade_det (2 * n)) (0 # 1)%Q) true.
Proof.
  intros n. apply qpos_qneg_mul.
  - apply pade_det_pos_even.
  - apply pade_det_neg_odd.
Defined.

Lemma pade_step_between_odd : forall n : nat,
  bid (Qltb (pade_det (S (2 * n + 1)) * pade_det (2 * n + 1)) (0 # 1)%Q) true.
Proof.
  intros n.
  apply (bidQlt_move _ _ _ (Qmult_comm (pade_det (2 * n + 1)) (pade_det (S (2 * n + 1))))).
  apply qpos_qneg_mul.
  - replace (S (2 * n + 1))%nat with (2 * S n)%nat by lia.
    apply pade_det_pos_even.
  - apply pade_det_neg_odd.
Defined.

(* ============================================================ *)
(* Section 7: the nonzero lower bound LB1_n :=                   *)
(* 3 ((2n+1)!)^2 / V_{2n+1}(1) is strictly positive.             *)
(* ============================================================ *)

Definition pade_LB1 (n : nat) : Q :=
  (3 # 1)%Q * (((Z.of_nat (natfact (2 * n + 1)) * Z.of_nat (natfact (2 * n + 1))) # 1)%Q
                 / padeV1 (2 * n + 1)).

Lemma pade_nz_lb_G : forall n : nat, bid (Qltb (0 # 1)%Q (pade_LB1 n)) true.
Proof.
  intros n. unfold pade_LB1. apply qpos_mul.
  - apply bidI. apply qltb_of_lt. unfold Qlt. cbn [Qnum Qden]. lia.
  - apply qdiv_pos.
    + apply natfact_sq_qpos.
    + apply padeV1_pos.
Defined.

(* ============================================================ *)
(* Section 8: the relative decay bound. gap_n is the cross-      *)
(* multiplied shape ((2n+1)!)^2 / (V_{2n} V_{2n+1}); under the   *)
(* explicit one-step premise slot gap_{n+1} <= (21/100) gap_n    *)
(* the constant bound (71/100000) (21/100)^n holds for n >= 3,   *)
(* with computed anchors at the small indices.                   *)
(* ============================================================ *)

Definition pade_gapq (n : nat) : Q :=
  ((Z.of_nat (natfact (2 * n + 1)) * Z.of_nat (natfact (2 * n + 1))) # 1)%Q
    / (padeV1 (2 * n) * padeV1 (2 * n + 1)).

Definition pade_rho_rel_bound (n : nat) : Set :=
  bid (Qle_bool (pade_gapq n) ((71 # 100000)%Q * q_pown pade_rho_hat n)) true.

Definition pade_gap_step_premise (n : nat) : Set :=
  bid (Qle_bool (pade_gapq (S n)) ((21 # 100)%Q * pade_gapq n)) true.

Lemma pade_gapq_anchor_1 : bid (Qeq_bool (pade_gapq 1) ((1 # 136)%Q)) true.
Proof. apply bidI. vm_compute. reflexivity. Defined.

Lemma pade_gapq_anchor_2 : bid (Qeq_bool (pade_gapq 2) ((1 # 4551)%Q)) true.
Proof. apply bidI. vm_compute. reflexivity. Defined.

Lemma pade_gapq_anchor_3 : bid (Qeq_bool (pade_gapq 3) ((1 # 153364)%Q)) true.
Proof. apply bidI. vm_compute. reflexivity. Defined.

Lemma pade_gap_3_anchor :
  bid (Qle_bool (pade_gapq 3) ((71 # 100000)%Q * q_pown pade_rho_hat 3)) true.
Proof. apply bidI. vm_compute. reflexivity. Defined.

Lemma pade_gapq_3_bound :
  bid (Qle_bool (pade_gapq 3) ((71 # 100000)%Q * q_pown pade_rho_hat 3)) true.
Proof. exact pade_gap_3_anchor. Defined.

Lemma pade_gapq_rel_bound_aux : forall d n : nat,
  bid (Nat.eqb n (3 + d)) true ->
  (forall k : nat, pade_gap_step_premise k) ->
  bid (Qle_bool (pade_gapq n) ((71 # 100000)%Q * q_pown pade_rho_hat n)) true.
Proof.
  induction d as [|d IH]; intros n En Hstep.
  - assert (HnE : (n = 3 + 0)%nat)
      by (apply (proj1 (Nat.eqb_eq n ((3 + 0)%nat))); apply bidE; exact En).
    subst n. replace (3 + 0)%nat with 3%nat by lia.
    exact pade_gapq_3_bound.
  - assert (HnE : (n = 3 + S d)%nat)
      by (apply (proj1 (Nat.eqb_eq n ((3 + S d)%nat))); apply bidE; exact En).
    subst n.
    replace (3 + S d)%nat with (S (3 + d))%nat by lia.
    assert (Hs : pade_gapq (S (3 + d)) <= (21 # 100)%Q * pade_gapq (3 + d)).
    { apply bidQle. apply (Hstep (3 + d)%nat). }
    assert (HI : pade_gapq (3 + d) <= (71 # 100000)%Q * q_pown pade_rho_hat (3 + d)).
    { apply bidQle. apply (IH (3 + d)%nat).
      - apply bidI. apply Nat.eqb_refl.
      - exact Hstep. }
    apply bidI. apply qleb_of_le.
    apply Qle_trans with (y := (21 # 100)%Q * pade_gapq (3 + d)); [exact Hs |].
    apply Qle_trans
      with (y := (21 # 100)%Q * ((71 # 100000)%Q * q_pown pade_rho_hat (3 + d))).
    + rewrite (Qmult_comm (21 # 100)%Q (pade_gapq (3 + d))).
      rewrite (Qmult_comm (21 # 100)%Q ((71 # 100000)%Q * q_pown pade_rho_hat (3 + d))).
      apply Qmult_le_compat_r; [exact HI | unfold Qle; cbn [Qnum Qden]; lia].
    + assert (E : ((21 # 100)%Q * ((71 # 100000)%Q * q_pown pade_rho_hat (3 + d)))%Q
                  == ((71 # 100000)%Q * q_pown pade_rho_hat (S (3 + d)))).
      { cbn [q_pown]. unfold pade_rho_hat. ring. }
      rewrite E. apply Qle_refl.
Defined.

Lemma pade_rho_rel_bound_general : forall n : nat,
  bid (Nat.leb 3 n) true ->
  (forall k : nat, pade_gap_step_premise k) ->
  pade_rho_rel_bound n.
Proof.
  intros n Hn Hstep. unfold pade_rho_rel_bound.
  assert (Hle : (3 <= n)%nat) by (apply (proj1 (Nat.leb_le 3 n)); apply bidE; exact Hn).
  assert (HnE : (n = 3 + (n - 3))%nat) by (rewrite <- (Nat.sub_add 3 n Hle) at 1; lia).
  apply (pade_gapq_rel_bound_aux (n - 3)%nat n).
  - apply bidI. exact (proj2 (Nat.eqb_eq n ((3 + (n - 3))%nat)) HnE).
  - exact Hstep.
Defined.

Lemma pade_gapq_instance_n0 :
  bid (Qle_bool (pade_gapq 0) ((1 # 1)%Q * q_pown pade_rho_hat 0)) true.
Proof. apply bidI. vm_compute. reflexivity. Defined.

Lemma pade_gapq_instance_n1 :
  bid (Qle_bool (pade_gapq 1) ((1 # 1)%Q * q_pown pade_rho_hat 1)) true.
Proof. apply bidI. vm_compute. reflexivity. Defined.

Lemma pade_gapq_instance_n2 :
  bid (Qle_bool (pade_gapq 2) ((1 # 1)%Q * q_pown pade_rho_hat 2)) true.
Proof. apply bidI. vm_compute. reflexivity. Defined.

Lemma pade_LB1_anchor_1 : bid (Qeq_bool (pade_LB1 1) ((9 # 17)%Q)) true.
Proof. apply bidI. vm_compute. reflexivity. Defined.

Lemma pade_LB1_anchor_2 : bid (Qeq_bool (pade_LB1 2) ((60 # 41)%Q)) true.
Proof. apply bidI. vm_compute. reflexivity. Defined.

Lemma pade_LB1_anchor_3 : bid (Qeq_bool (pade_LB1 3) ((15120 # 1667)%Q)) true.
Proof. apply bidI. vm_compute. reflexivity. Defined.

(* ============================================================ *)
(* Section 9: assumption audit, one line per theorem.            *)
(* ============================================================ *)

Print Assumptions natfact_pos.
Print Assumptions val1_vadd.
Print Assumptions val1_vsmul.
Print Assumptions padeU1_step.
Print Assumptions padeV1_step.
Print Assumptions qmul_one.
Print Assumptions pade_det_step.
Print Assumptions altsign_step.
Print Assumptions pade_det_identity_G.
Print Assumptions pade_det_anchors.
Print Assumptions bidQlt_move.
Print Assumptions bidQlt_moveR.
Print Assumptions qlt_le_weakB.
Print Assumptions qden_pos.
Print Assumptions qpos_mul.
Print Assumptions qpos_add_le.
Print Assumptions qle_add_r.
Print Assumptions natfact_sq_qpos.
Print Assumptions qdiv_pos.
Print Assumptions qle_mul_pos.
Print Assumptions qle_mul_nonneg_Z.
Print Assumptions qle_mul_nonneg.
Print Assumptions qpos_qneg_mul.
Print Assumptions padeV1_pos.
Print Assumptions pade_det_two_step.
Print Assumptions pade_det_pos_even.
Print Assumptions pade_det_neg_odd.
Print Assumptions pade_step_between_even.
Print Assumptions pade_step_between_odd.
Print Assumptions pade_nz_lb_G.
Print Assumptions pade_gapq_anchor_1.
Print Assumptions pade_gapq_anchor_2.
Print Assumptions pade_gapq_anchor_3.
Print Assumptions pade_gap_3_anchor.
Print Assumptions pade_gapq_3_bound.
Print Assumptions pade_gapq_rel_bound_aux.
Print Assumptions pade_rho_rel_bound_general.
Print Assumptions pade_gapq_instance_n0.
Print Assumptions pade_gapq_instance_n1.
Print Assumptions pade_gapq_instance_n2.
Print Assumptions pade_LB1_anchor_1.
Print Assumptions pade_LB1_anchor_2.
Print Assumptions pade_LB1_anchor_3.
