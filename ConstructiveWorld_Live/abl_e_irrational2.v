(* ===================================================================== *)
(*  abl_e_irrational2.v -- constructive kernel for the irrationality of e *)
(*  (Fourier 1815; Q closure). Pool e_irr2/prefix eir2_ (slots in-reg).   *)
(*  Mission. Second tower of the e-irrationality program. Layer 1:        *)
(*    eir2_q_fact (true Q Fixpoint factorial; positivity and QeqT value   *)
(*    face vs Z.of_nat (fact n)); eir2_s (true Fixpoint partial sums with *)
(*    step/positivity/monotonicity); eir2_s_fact_int: n! * s_n has an     *)
(*    explicit integer witness z for every n (sigT). Layer 2: given       *)
(*    a : Z, b : nat (NatLe 1 b), n := b: N := b*n!*(a/b - s_n)           *)
(*    (eir2_core_qty, computable) has witness z with N == (z#1) integer   *)
(*    and 0 < N < 1 (eir2_kernel_witness, sigT x2 + And), closed into     *)
(*    eir2_irrational_core : False. "e = a/b" enters as the two-branch    *)
(*    Q-order slot eir2_hyp (Set-level; layer-3 real tower supplies it).  *)
(*    it). The b | n! side condition dissolves (b pulled out once);       *)
(*    (0, N < 1/b) weakens losslessly to (0, N < 1); the n := S k step    *)
(*    runs on the Qeq chain + eir2_qdiv_mul_inv (lia, no Qinv).           *)
(*  Dependencies. Stdlib QArith/Arith.Arith/ZArith.ZArith/Lia/Setoid/     *)
(*    Arith.Factorial; S01_BaseRing (And/Id/NatLe Set faces);             *)
(*    S02_CauchyComplete (QeqT/QltT, qltT_0_1, bridges qeq_imp_qeqT /     *)
(*    qeqT_imp_qeq / qeq_imp_qle / QleT'_to_Qle).                         *)
(*  References. Fourier 1815/1826; LW0PiIrrational (sigT+And+QltT) as     *)
(*    layer-3 interface model; abl_ln2_integmachine_bridge discipline.    *)
(*  Constructivity. Statement faces all Set (sigT/And (S01)/QeqT/QltT     *)
(*    (S02)/NatLe (S01)); Prop only inside proof bodies, absorbed via     *)
(*    Qlt_to_QltT/qeq_imp_qeqT/NatLe_lift; two true Fixpoints; Print      *)
(*    Assumptions all Closed; Separate Extraction validated.              *)
(*  Build. env.sh; unset COQLIB ROCQLIB; ulimit -s 65532; cd world;       *)
(*    cpu_guard -Reg /tmp/cw_reg_nw1 -Front 0 -Mid 1 -MaxWaitSec 600      *)
(*    rocq c -native-compiler no -q -Q . "" abl_e_irrational2.v           *)
(* ===================================================================== *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
From Stdlib Require Import QArith.QArith Arith.Arith ZArith.ZArith Lia Setoid.
From Stdlib Require Import Arith.Factorial.

(* ============================================================ *)
(* S0. Z<->Q boundary and Q order lemmas (proof-body reasoning; Set faces) *)
(* ============================================================ *)

(* order reading of single-denominator Q: positivity / <1 of z#1 via Z-level lia *)
Lemma eir2_zq_pos_of : forall z : Z, (0 < z)%Z -> QltT 0 (z#1).
Proof.
  intros z Hz.
  apply Qlt_to_QltT.
  unfold Qlt. cbn [Qnum Qden].
  lia.
Qed.

Lemma eir2_zq_qpos : forall z : Z, QltT 0 (z#1) -> (0 < z)%Z.
Proof.
  intros z H.
  apply QltT_to_Qlt in H.
  unfold Qlt in H. cbn [Qnum Qden] in H.
  lia.
Qed.

Lemma eir2_zq_qlt : forall z : Z, QltT (z#1) 1 -> (z < 1)%Z.
Proof.
  intros z H.
  apply QltT_to_Qlt in H.
  unfold Qlt in H. cbn [Qnum Qden] in H.
  lia.
Qed.

(* three Qeq facts on Z single denominators (component unfolding + lia) *)
Lemma eir2_zq_zq_plus : forall u v : Z, QeqT ((u#1) + (v#1)) ((u+v)#1).
Proof.
  intros u v. apply qeq_imp_qeqT.
  unfold Qeq, Qplus. cbn [Qnum Qden]. lia.
Qed.

Lemma eir2_zq_zq_mult : forall u v : Z, QeqT ((u#1) * (v#1)) ((u*v)#1).
Proof.
  intros u v. apply qeq_imp_qeqT.
  unfold Qeq, Qmult. cbn [Qnum Qden]. lia.
Qed.

(* cancellation-with-scale core: for w <> 0, ((w#1)*(v#1))*((c#1)/(w#1)) == (v*c)#1 *)
(* (Qinv three-way split, denominators made positive, then lia: F*(a/b) cancel core) *)
Lemma eir2_qscale_div : forall v c w : Z, w <> 0%Z ->
  QeqT (((w#1) * (v#1)) * ((c#1) / (w#1))%Q) ((v*c)#1).
Proof.
  intros v c w Hw.
  apply qeq_imp_qeqT.
  destruct w as [| p | p].
  - exfalso. apply Hw. reflexivity.
  - unfold Qeq. cbn [Qmult Qdiv Qinv Qnum Qden].
    rewrite ?Pos.mul_1_l, ?Pos.mul_1_r. lia.
  - unfold Qeq. cbn [Qmult Qdiv Qinv Qnum Qden].
    rewrite ?Pos.mul_1_l, ?Pos.mul_1_r. lia.
Qed.

(* reciprocal keeps positivity: 0 < x -> 0 < 1/x (Qinv split on Qnum; lia/nia) *)
Lemma eir2_qdiv_pos : forall x : Q, QltT 0 x -> QltT 0 ((1#1) / x).
Proof.
  intros [xn xd] Hx.
  apply QltT_to_Qlt in Hx.
  destruct xn as [| p | p].
  - unfold Qlt in Hx. cbn [Qnum Qden] in Hx.
    apply Qlt_to_QltT. unfold Qlt.
    cbn [Qmult Qdiv Qinv Qnum Qden].
    exfalso. lia.
  - apply Qlt_to_QltT. unfold Qlt.
    cbn [Qmult Qdiv Qinv Qnum Qden].
    rewrite ?Pos.mul_1_l, ?Pos.mul_1_r. lia.
  - unfold Qlt in Hx. cbn [Qnum Qden] in Hx.
    apply Qlt_to_QltT. unfold Qlt.
    cbn [Qmult Qdiv Qinv Qnum Qden].
    rewrite ?Pos.mul_1_l, ?Pos.mul_1_r.
    exfalso. nia.
Qed.

(* positive times positive stays positive (mult): component-wise nia *)
Lemma eir2_qmult_pos : forall x y : Q, QltT 0 x -> QltT 0 y -> QltT 0 (x * y).
Proof.
  intros [xn xd] [yn yd] Hx Hy.
  apply QltT_to_Qlt in Hx. apply QltT_to_Qlt in Hy.
  unfold Qlt in Hx, Hy. cbn [Qnum Qden] in Hx, Hy.
  apply Qlt_to_QltT.
  unfold Qlt, Qmult. cbn [Qnum Qden].
  nia.
Qed.

(* positive times positive stays positive (add): component-wise nia *)
Lemma eir2_qplus_pos : forall x y : Q, QltT 0 x -> QltT 0 y -> QltT 0 (x + y).
Proof.
  intros [xn xd] [yn yd] Hx Hy.
  apply QltT_to_Qlt in Hx. apply QltT_to_Qlt in Hy.
  unfold Qlt in Hx, Hy. cbn [Qnum Qden] in Hx, Hy.
  apply Qlt_to_QltT.
  unfold Qlt, Qplus. cbn [Qnum Qden].
  nia.
Qed.

(* right sign distribution of multiplication: component-wise lia *)
Lemma eir2_qmult_opp_r : forall x y : Q, QeqT (x * (-y)) (-(x * y)).
Proof.
  intros [xn xd] [yn yd].
  apply qeq_imp_qeqT.
  unfold Qmult, Qopp, Qeq. cbn [Qnum Qden].
  lia.
Qed.

(* reciprocal square core: z*(1/z) == 1 (Qinv split on Qnum; no Qmult_inv_r use) *)
Lemma eir2_qdiv_mul_inv : forall z : Q, QltT 0 z -> QeqT (z * ((1#1) / z)) (1#1).
Proof.
  intros [xn xd] Hx.
  apply qeq_imp_qeqT.
  apply QltT_to_Qlt in Hx.
  destruct xn as [| p | p].
  - unfold Qlt in Hx. cbn [Qnum Qden] in Hx.
    exfalso. lia.
  - unfold Qeq. cbn [Qmult Qdiv Qinv Qnum Qden].
    rewrite ?Pos2Z.inj_mul, ?Pos.mul_1_l, ?Pos.mul_1_r. lia.
  - unfold Qlt in Hx. cbn [Qnum Qden] in Hx.
    exfalso. nia.
Qed.

(* QeqT sideways transfer, two branches (via S02 bridges; no setoid dependency) *)
Lemma eir2_qltT_eq_l : forall a a' b : Q, Qeq a a' -> QltT a' b -> QltT a b.
Proof.
  intros a a' b Ha H.
  exact (Qlt_to_QltT _ _
    (Qle_lt_trans a a' b
       (QleT'_to_Qle _ _ (qeq_imp_qle _ _ (qeq_imp_qeqT _ _ Ha)))
       (QltT_to_Qlt _ _ H))).
Qed.

Lemma eir2_qltT_eq_r : forall a b b' : Q, Qeq b b' -> QltT a b -> QltT a b'.
Proof.
  intros a b b' Hb Hab.
  exact (Qlt_to_QltT _ _
    (Qlt_le_trans a b b' (QltT_to_Qlt _ _ Hab)
       (QleT'_to_Qle _ _ (qeq_imp_qle _ _ (qeq_imp_qeqT _ _ Hb))))).
Qed.

(* the integrality witness face (Set-level sigT) is closed under + and negation *)
Lemma eir2_intq_add : forall x y : Q,
  (sigT (fun z : Z => QeqT x (z#1))) ->
  (sigT (fun z : Z => QeqT y (z#1))) ->
  sigT (fun z : Z => QeqT (x + y) (z#1)).
Proof.
  intros x y [u Hu] [v Hv].
  exists (u + v)%Z.
  apply qeq_imp_qeqT.
  apply (Qeq_trans _ ((u#1) + (v#1))%Q _).
  - exact (Qplus_comp x (u#1) (qeqT_imp_qeq x (u#1) Hu)
                   y (v#1) (qeqT_imp_qeq y (v#1) Hv)).
  - apply qeqT_imp_qeq. apply eir2_zq_zq_plus.
Qed.

Lemma eir2_intq_opp : forall x : Q,
  (sigT (fun z : Z => QeqT x (z#1))) ->
  sigT (fun z : Z => QeqT (- x) (z#1)).
Proof.
  intros x [z Hz].
  exists (- z)%Z.
  apply qeq_imp_qeqT.
  apply (Qopp_comp x (z#1) (qeqT_imp_qeq x (z#1) Hz)).
Qed.

(* ============================================================ *)
(* S1. Layer 1, factorial face: true Q-level Fixpoint + positivity + value face *)
(* ============================================================ *)

Fixpoint eir2_q_fact (n : nat) : Q :=
  match n with
  | Datatypes.O => 1#1
  | Datatypes.S k => ((Z.of_nat (Datatypes.S k))#1) * eir2_q_fact k
  end.

Lemma eir2_q_fact_pos : forall n : nat, QltT 0 (eir2_q_fact n).
Proof.
  induction n as [| k IH].
  - exact qltT_0_1.
  - cbn [eir2_q_fact].
    apply eir2_qmult_pos.
    + apply eir2_zq_pos_of. lia.
    + exact IH.
Qed.

Lemma eir2_q_fact_val : forall n : nat, QeqT (eir2_q_fact n) ((Z.of_nat (fact n))#1).
Proof.
  induction n as [| k IH].
  - apply qeq_imp_qeqT. apply Qeq_refl.
  - apply qeq_imp_qeqT.
    cbn [eir2_q_fact].
    apply (Qeq_trans _ (((Z.of_nat (Datatypes.S k))#1) * ((Z.of_nat (fact k))#1))%Q _).
    + exact (Qmult_comp ((Z.of_nat (Datatypes.S k))#1) ((Z.of_nat (Datatypes.S k))#1)
                        (Qeq_refl ((Z.of_nat (Datatypes.S k))#1))
                        (eir2_q_fact k) ((Z.of_nat (fact k))#1)
                        (qeqT_imp_qeq _ _ IH)).
    + change (fact (Datatypes.S k)) with (Datatypes.S k * fact k)%nat.
      rewrite Nat2Z.inj_mul.
      apply qeqT_imp_qeq. apply eir2_zq_zq_mult.
Qed.

(* ============================================================ *)
(* S2. Layer 1, series face: true Fixpoint partial sums + step + positivity + mono *)
(* ============================================================ *)

Definition eir2_term (n : nat) : Q := (1#1) / eir2_q_fact n.

Fixpoint eir2_s (n : nat) : Q :=
  match n with
  | Datatypes.O => 1#1
  | Datatypes.S k => eir2_s k + eir2_term (Datatypes.S k)
  end.

Lemma eir2_s_step : forall n : nat,
  QeqT (eir2_s (Datatypes.S n)) (eir2_s n + eir2_term (Datatypes.S n)).
Proof.
  intro n.
  apply qeq_imp_qeqT. apply Qeq_refl.
Qed.

(* term positivity: 1/fact(n) > 0 (via the reciprocal positivity lemma) *)
Lemma eir2_term_pos : forall n : nat, QltT 0 (eir2_term n).
Proof.
  intro n.
  apply eir2_qdiv_pos.
  apply eir2_q_fact_pos.
Qed.

Lemma eir2_s_pos : forall n : nat, QltT 0 (eir2_s n).
Proof.
  induction n as [| k IH].
  - exact qltT_0_1.
  - cbn [eir2_s].
    apply eir2_qplus_pos.
    + exact IH.
    + apply eir2_term_pos.
Qed.

Lemma eir2_s_mono : forall n : nat, QltT (eir2_s n) (eir2_s (Datatypes.S n)).
Proof.
  intro n.
  apply Qlt_to_QltT.
  assert (H : Qlt (eir2_s n + 0) (eir2_s n + eir2_term (Datatypes.S n))).
  { apply (proj2 (Qplus_lt_r 0 (eir2_term (Datatypes.S n)) (eir2_s n))).
    apply QltT_to_Qlt. apply eir2_term_pos. }
  rewrite Qplus_0_r in H.
  exact H.
Qed.

(* ============================================================ *)
(* S3. Layer 1, integrality face: explicit integer witness for n!*s_n (sigT, induction) *)
(* ============================================================ *)

Theorem eir2_s_fact_int :
  forall n : nat, sigT (fun z : Z => QeqT (eir2_q_fact n * eir2_s n) (z#1)).
Proof.
  induction n as [| k [z0 IH]].
  - exists 1%Z.
    apply qeq_imp_qeqT.
    reflexivity.
  - exists (Z.of_nat (Datatypes.S k) * z0 + 1)%Z.
    cbn [eir2_q_fact eir2_s].
    unfold eir2_term. cbn [eir2_q_fact].
    assert (Hz0q : Qeq (eir2_q_fact k * eir2_s k) (z0#1))
      by (apply qeqT_imp_qeq; exact IH).
    assert (H1 : Qeq ((((Z.of_nat (Datatypes.S k))#1) * eir2_q_fact k) * eir2_s k)
                      (((Z.of_nat (Datatypes.S k)) * z0)#1)).
    { apply (Qeq_trans _ (((Z.of_nat (Datatypes.S k))#1) *
                          (eir2_q_fact k * eir2_s k))%Q _).
      - exact (Qeq_sym _ _ (Qmult_assoc ((Z.of_nat (Datatypes.S k))#1)
                           (eir2_q_fact k) (eir2_s k))).
      - apply (Qeq_trans _ (((Z.of_nat (Datatypes.S k))#1) * (z0#1))%Q _).
        + exact (Qmult_comp ((Z.of_nat (Datatypes.S k))#1) ((Z.of_nat (Datatypes.S k))#1)
                   (Qeq_refl ((Z.of_nat (Datatypes.S k))#1))
                   (eir2_q_fact k * eir2_s k) (z0#1) Hz0q).
        + apply qeqT_imp_qeq. apply eir2_zq_zq_mult. }
    assert (H2 : Qeq ((((Z.of_nat (Datatypes.S k))#1) * eir2_q_fact k) *
                      ((1#1) / (((Z.of_nat (Datatypes.S k))#1) * eir2_q_fact k)))
                      (1#1)).
    { apply qeqT_imp_qeq.
      apply eir2_qdiv_mul_inv.
      apply eir2_qmult_pos.
      - apply eir2_zq_pos_of. lia.
      - apply eir2_q_fact_pos. }
    apply qeq_imp_qeqT.
    apply (Qeq_trans _
             (((((Z.of_nat (Datatypes.S k))#1) * eir2_q_fact k) * eir2_s k) +
               ((((Z.of_nat (Datatypes.S k))#1) * eir2_q_fact k) * ((1#1) / (((Z.of_nat (Datatypes.S k))#1) * eir2_q_fact k))))%Q _).
    + exact (Qmult_plus_distr_r
               (((Z.of_nat (Datatypes.S k))#1) * eir2_q_fact k)
               (eir2_s k)
               ((1#1) / (((Z.of_nat (Datatypes.S k))#1) * eir2_q_fact k))).
    + apply (Qeq_trans _ (Qplus ((Z.of_nat (Datatypes.S k) * z0)#1) 1)%Q _).
      * exact (Qplus_comp _ _ H1 _ _ H2).
      * apply qeqT_imp_qeq. apply eir2_zq_zq_plus.
Qed.

(* ============================================================ *)
(* S4. Layer 2, integrality contradiction kernel: eir2_hyp slot + witness + net *)
(* ============================================================ *)

(* gap g_n := a/b - s_n (the slot supplies both order branches; a/b as a Qdiv term) *)
Definition eir2_gap (a : Z) (b n : nat) : Q :=
  (((a#1) / ((Z.of_nat b)#1))%Q - eir2_s n)%Q.

(* core quantity N_{a,b,n} := n'*n!*(a/b - s_n), n' := Z.of_nat n; at n := b *)
(* this is exactly the classic b*b!*(a/b - s_b) (the n' factor lands in one step) *)
Definition eir2_core_qty (a : Z) (b n : nat) : Q :=
  ((Z.of_nat n)#1) * eir2_q_fact n * eir2_gap a b n.

(* slot (Set-level): for n >= 1, 0 < a/b - s_n < 1/(n*n!) -- supplied by the layer-3 real tower *)
Definition eir2_hyp (a : Z) (b : nat) : Set :=
  forall n : nat, NatLe 1 n ->
    And (QltT 0 (eir2_gap a b n))
        (QltT (eir2_gap a b n)
              ((1#1) / (((Z.of_nat n)#1) * eir2_q_fact n))).

(* explicit witness shape: at n := b, N := b*b!*(a/b - s_b) has witness z, 0<z#1<1 *)
Theorem eir2_kernel_witness : forall (a : Z) (b : nat), NatLe 1 b -> eir2_hyp a b ->
  sigT (fun n : nat => sigT (fun z : Z =>
    And (NatLe 1 n)
    (And (QeqT (eir2_core_qty a b n) (z#1))
    (And (QltT 0 (z#1)) (QltT (z#1) 1))))).
Proof.
  intros a b Hb H.
  exists b.
  destruct (H b Hb) as [Hpos Hupper].
  assert (HF : QltT 0 (((Z.of_nat b)#1) * eir2_q_fact b)).
  { apply eir2_qmult_pos.
    - apply eir2_zq_pos_of.
      pose proof (NatLe_drop 1 b Hb). lia.
    - apply eir2_q_fact_pos. }
  assert (Hqty_pos : QltT 0 (eir2_core_qty a b b)).
  { unfold eir2_core_qty.
    apply eir2_qmult_pos; assumption. }
  assert (Hqty_lt : QltT (eir2_core_qty a b b) 1).
  { unfold eir2_core_qty.
    apply (eir2_qltT_eq_r _
             ((((Z.of_nat b)#1) * eir2_q_fact b) *
              ((1#1) / (((Z.of_nat b)#1) * eir2_q_fact b)))%Q 1%Q).
    - apply qeqT_imp_qeq. apply eir2_qdiv_mul_inv. exact HF.
    - apply Qlt_to_QltT.
      rewrite (Qmult_comm (((Z.of_nat b)#1) * eir2_q_fact b) (eir2_gap a b b)).
      rewrite (Qmult_comm (((Z.of_nat b)#1) * eir2_q_fact b)
                           (((1#1) / (((Z.of_nat b)#1) * eir2_q_fact b))%Q)).
      apply (Qmult_lt_compat_r (eir2_gap a b b)
               (((1#1) / (((Z.of_nat b)#1) * eir2_q_fact b))%Q)
               (((Z.of_nat b)#1) * eir2_q_fact b)).
      + exact (QltT_to_Qlt _ _ HF).
      + exact (QltT_to_Qlt _ _ Hupper). }
  assert (Hqty_int : sigT (fun z : Z =>
    QeqT (((Z.of_nat b)#1) * eir2_q_fact b * eir2_gap a b b) (z#1))).
  { destruct (eir2_s_fact_int b) as [z0 Hz0].
    assert (Hz0q : Qeq (eir2_q_fact b * eir2_s b) (z0#1))
      by (apply qeqT_imp_qeq; exact Hz0).
    assert (Hw0 : (Z.of_nat b <> 0)%Z).
    { pose proof (NatLe_drop 1 b Hb). lia. }
    exists ((Z.of_nat (fact b) * a) - Z.of_nat b * z0)%Z.
    unfold eir2_core_qty, eir2_gap.
    assert (H1 : Qeq (((Z.of_nat b)#1) * eir2_q_fact b *
                      (((a#1) / ((Z.of_nat b)#1))%Q))
                      ((Z.of_nat (fact b) * a)#1)).
    { apply (Qeq_trans _ (((Z.of_nat b)#1) * ((Z.of_nat (fact b))#1) *
                          (((a#1) / ((Z.of_nat b)#1))%Q))%Q _).
      - exact (Qmult_comp
                 (((Z.of_nat b)#1) * eir2_q_fact b)
                 (((Z.of_nat b)#1) * ((Z.of_nat (fact b))#1))
                 (Qmult_comp ((Z.of_nat b)#1) ((Z.of_nat b)#1)
                    (Qeq_refl ((Z.of_nat b)#1))
                    (eir2_q_fact b) ((Z.of_nat (fact b))#1)
                    (qeqT_imp_qeq (eir2_q_fact b) ((Z.of_nat (fact b))#1)
                       (eir2_q_fact_val b)))
                 (((a#1) / ((Z.of_nat b)#1))%Q)
                 (((a#1) / ((Z.of_nat b)#1))%Q)
                 (Qeq_refl (((a#1) / ((Z.of_nat b)#1))%Q))).
      - exact (qeqT_imp_qeq _ _
                 (eir2_qscale_div (Z.of_nat (fact b)) a (Z.of_nat b) Hw0)). }
    assert (H2 : Qeq (((Z.of_nat b)#1) * eir2_q_fact b * (-(eir2_s b)))
                      ((- (Z.of_nat b * z0))#1)).
    { apply (Qeq_trans _
               (- (((Z.of_nat b)#1) * eir2_q_fact b * eir2_s b))%Q _).
      - apply qeqT_imp_qeq. apply eir2_qmult_opp_r.
      - assert (HFz : Qeq (((Z.of_nat b)#1) * eir2_q_fact b * eir2_s b)
                           ((Z.of_nat b * z0)#1)).
        { apply (Qeq_trans _ (((Z.of_nat b)#1) *
                              (eir2_q_fact b * eir2_s b))%Q _).
          - exact (Qeq_sym _ _ (Qmult_assoc ((Z.of_nat b)#1) (eir2_q_fact b) (eir2_s b))).
          - apply (Qeq_trans _ (((Z.of_nat b)#1) * (z0#1))%Q _).
            + exact (Qmult_comp ((Z.of_nat b)#1) ((Z.of_nat b)#1)
                       (Qeq_refl ((Z.of_nat b)#1))
                       (eir2_q_fact b * eir2_s b) (z0#1) Hz0q).
            + apply qeqT_imp_qeq. apply eir2_zq_zq_mult. }
        exact (Qopp_comp _ _ HFz). }
    apply qeq_imp_qeqT.
    apply (Qeq_trans _
             ((((Z.of_nat b)#1) * eir2_q_fact b) *
              (((a#1) / ((Z.of_nat b)#1))%Q) +
              (((Z.of_nat b)#1) * eir2_q_fact b) * (-(eir2_s b)))%Q _).
    + change ((((a#1) / ((Z.of_nat b)#1))%Q - eir2_s b)%Q)
        with ((((a#1) / ((Z.of_nat b)#1))%Q) + (-(eir2_s b)))%Q.
      exact (Qmult_plus_distr_r
               (((Z.of_nat b)#1) * eir2_q_fact b)
               (((a#1) / ((Z.of_nat b)#1))%Q) (-(eir2_s b))).
    + rewrite H1, H2.
      exact (qeqT_imp_qeq _ _
               (eir2_zq_zq_plus
               (Z.of_nat (fact b) * a)
               (- (Z.of_nat b * z0)))). }
  destruct Hqty_int as [z Hz].
  exists z.
  split; [ exact Hb | ].
  split.
  - exact Hz.
  - split.
    + apply (eir2_qltT_eq_r 0 (eir2_core_qty a b b) (z#1)).
      * apply qeqT_imp_qeq. exact Hz.
      * exact Hqty_pos.
    + apply (eir2_qltT_eq_l (z#1) (eir2_core_qty a b b) 1).
      * apply Qeq_sym. apply qeqT_imp_qeq. exact Hz.
      * exact Hqty_lt.
Qed.

(* the net: a positive integer cannot fall in (0,1) -- the classic e-irrationality kernel *)
Theorem eir2_irrational_core : forall (a : Z) (b : nat), NatLe 1 b -> eir2_hyp a b -> False.
Proof.
  intros a b Hb H.
  destruct (eir2_kernel_witness a b Hb H) as [n [z [_ [Heq [Hz0 Hz1]]]]].
  apply (eir2_zq_qpos z) in Hz0.
  apply (eir2_zq_qlt z) in Hz1.
  lia.
Qed.

(* ============================================================ *)
(* evidence block: Print Assumptions + Separate Extraction      *)
(* ============================================================ *)

From Stdlib Require Import Extraction.
Separate Extraction eir2_q_fact eir2_s eir2_core_qty eir2_s_fact_int.

Print Assumptions eir2_q_fact_pos.
Print Assumptions eir2_q_fact_val.
Print Assumptions eir2_term_pos.
Print Assumptions eir2_s_pos.
Print Assumptions eir2_s_mono.
Print Assumptions eir2_s_fact_int.
Print Assumptions eir2_kernel_witness.
Print Assumptions eir2_irrational_core.
