(* ConstructiveWorld-Main -> Set - Ln2Escape: integral-face ln2 route on the
   exact Q-polynomial integrator (statements carried on Set). *)
(** * Ln2Escape: the Beta-carrier integral route to the ln2 window condition.

    Mission.  The rational shape t^n(1-t)^n/(1+t)^{n+1} escapes the pint_
      polynomial integrator and (t(1-t))^n <= 4^{-n} needs a positivity
      machine; this file carries [lne_B n] := int_0^1 t^n(1-t)^n dt =
      (n!)^2/(2n+1)! by the coefficient list of t^n(1-t)^n and delivers
      [lne_B_posT], [lne_B_le_p4] (core [lne_nat_core]: (n!)^2 * 4^n <=
      (2n+1)!; window match [lne_B_lt_p2]), [lne_B_int] (sigT witness (n!)^2),
      combined as [lne_three_spec], witnessed by [lne_three_spec_holds],
      consumed by [lne_B_in_window], closed as [lne_ln2_irrational_cond].
    Dependencies.  Stdlib [QArith], [List], [Arith], [ZArith], [Factorial],
      [Lia], [Setoid], [Morphisms], [Qfield]; this development [S01_BaseRing],
      [S02_CauchyComplete], [S03_QExp], [PolyIntegral], [SumInvFactEscape]
      ([sif_qfact_Z]), [UpReqIrrationalCriterion], [UpReqLn2Irrational].
    References.  ConstructiveWorld-Main Ln2Escape.v, the baseline module
      whose statement names are carried over verbatim (statement-face
      Set-carrier completion); the Section A engine and [lne_list]/
      [lne_beta_value] are structure-preserving renamings of the
      PadeErrorIntegral engine (pei_ prefix).
    Constructivity.  Statements carried by Set ([QeqT], [QltT], [QleT'],
      [Id], [NatLe], [sigT], [And] := A*B); all proofs end in [Qed]; the five
      tail [Print Assumptions] audits read Closed; extraction gives
      [Obj.magic] = 0 on all 18 modules.
    Build.  [rocq c -native-compiler no -q -Q . "" Ln2Escape.v] exits 0; the
      artifact's first eight bytes are [436f7121 00015ff4]. *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import PolyIntegral.
Require Import SumInvFactEscape.
Require Import UpReqIrrationalCriterion.
Require Import UpReqLn2Irrational.
From Stdlib Require Import QArith.QArith QArith.Qabs Lists.List Arith.Arith
  ZArith.ZArith.
From Stdlib Require Import Arith.Factorial.
From Stdlib Require Import Lia Setoid Morphisms Qfield.

(* ============================================================ *)
(* Section A. Rational-domain engine: structure-preserving port of the PadeErrorIntegral Section A engine under the lne_ names. *)
(* ============================================================ *)

Lemma lne_mult_canc : forall a b c : Q, a * c == b * c -> ~ (c == 0%Q) -> QeqT a b.
Proof.
  intros a b c H Hc0.
  apply qeq_imp_qeqT.
  apply (proj1 (Qmult_inj_r a b c Hc0) H).
Qed.

Lemma lne_mult_nz : forall x y : Q,
  ~ (x == 0%Q) -> ~ (y == 0%Q) -> Not (QeqT (x * y) 0%Q).
Proof.
  intros x y Hx Hy Heq. apply False_rect. apply Hx.
  apply (qeqT_imp_qeq x 0%Q).
  apply (lne_mult_canc x 0%Q y).
  - rewrite Qmult_0_l. exact (qeqT_imp_qeq _ _ Heq).
  - exact Hy.
Qed.

Lemma lne_div_eq : forall p q r s : Q,
  Qlt 0 q -> Qlt 0 s -> p * s == q * r -> QeqT (p / q) (r / s).
Proof.
  intros p q r s Hq Hs H. apply qeq_imp_qeqT.
  assert (Hqz : ~ (q == 0%Q)).
  { intro E. apply (Qlt_not_eq 0%Q q Hq). exact (Qeq_sym _ _ E). }
  assert (Hsz : ~ (s == 0%Q)).
  { intro E. apply (Qlt_not_eq 0%Q s Hs). exact (Qeq_sym _ _ E). }
  assert (Hqsz : ~ (q * s == 0%Q)) by (intro E; apply False_rect;
    exact (match lne_mult_nz q s Hqz Hsz (qeq_imp_qeqT _ _ E) with end)).
  apply (fun H1 H2 => qeqT_imp_qeq _ _
           (lne_mult_canc (p / q) (r / s) (q * s) H1 H2)).
  - unfold Qdiv.
    assert (E1 : (p * Qinv q) * (q * s) == (p * Qinv q * q) * s) by ring.
    rewrite E1.
    assert (E2 : (p * Qinv q * q) * s == p * s).
    { rewrite <- (Qmult_assoc p (Qinv q) q). rewrite (Qmult_comm (Qinv q) q).
      rewrite (Qmult_inv_r q Hqz). ring. }
    rewrite E2.
    assert (E3 : (r * Qinv s) * (q * s) == (r * Qinv s * s) * q) by ring.
    rewrite E3.
    assert (E4 : (r * Qinv s * s) * q == q * r).
    { rewrite <- (Qmult_assoc r (Qinv s) s). rewrite (Qmult_comm (Qinv s) s).
      rewrite (Qmult_inv_r s Hsz). ring. }
    rewrite E4. exact H.
  - exact Hqsz.
Qed.

Lemma lne_div_sub : forall a b c d : Q,
  Qlt 0 b -> Qlt 0 d -> QeqT (a / b - c / d) ((a * d - c * b) / (b * d)).
Proof.
  intros a b c d Hb Hd. apply qeq_imp_qeqT.
  assert (Hbz : ~ (b == 0%Q)).
  { intro E. apply (Qlt_not_eq 0%Q b Hb). exact (Qeq_sym _ _ E). }
  assert (Hdz : ~ (d == 0%Q)).
  { intro E. apply (Qlt_not_eq 0%Q d Hd). exact (Qeq_sym _ _ E). }
  assert (Hbdz : ~ (b * d == 0%Q)) by (intro E; apply False_rect;
    exact (match lne_mult_nz b d Hbz Hdz (qeq_imp_qeqT _ _ E) with end)).
  assert (Hbd1 : (b * d) * Qinv (b * d) == 1%Q) by (apply Qmult_inv_r; exact Hbdz).
  apply (fun H1 H2 => qeqT_imp_qeq _ _
           (lne_mult_canc (a / b - c / d) ((a * d - c * b) / (b * d)) (b * d)
                          H1 H2)).
  - unfold Qdiv.
    assert (E1 : (a * Qinv b - c * Qinv d) * (b * d)
                 == a * (Qinv b * b) * d - c * (Qinv d * d) * b) by ring.
    rewrite E1.
    rewrite <- (Qmult_assoc (a * d - c * b) (Qinv (b * d)) (b * d)).
    rewrite (Qmult_comm (Qinv (b * d)) (b * d)). rewrite Hbd1.
    rewrite (Qmult_comm (Qinv b) b).
    assert (Hb1 : b * Qinv b == 1%Q) by (apply Qmult_inv_r; exact Hbz).
    rewrite Hb1.
    rewrite (Qmult_comm (Qinv d) d).
    assert (Hd1 : d * Qinv d == 1%Q) by (apply Qmult_inv_r; exact Hdz).
    rewrite Hd1.
    ring.
  - exact Hbdz.
Qed.

Lemma lne_qfact_nz : forall k : nat, Not (QeqT (q_fact k) 0%Q).
Proof.
  intro k. intro E.
  pose proof (qeqT_imp_qeq _ _ E) as E'.
  apply False_rect. apply (Qlt_not_eq 0%Q (q_fact k)).
  apply QltT_to_Qlt. apply q_fact_pos. exact (Qeq_sym _ _ E').
Qed.

(* Factorial >= 1 on the nat face ([NatLe]), feeding the Z-side transitivity step. *)
Lemma lne_fact_ge1 : forall k : nat, NatLe 1 (fact k).
Proof.
  intro k. apply NatLe_lift.
  induction k as [| k IH].
  - cbn [fact]. lia.
  - cbn [fact]. lia.
Qed.

(* ============================================================ *)
(* Section B. Beta carrier: the coefficient list of t^a(1-t)^b, its construction and closed form. *)
(*    Port of PadeErrorIntegral Section B; integration semantics = the pint_ face of PolyIntegral. *)
(* ============================================================ *)

(* Tail-zero pad: append one 0 at the list end; value and integral unchanged, lengths stay equal. *)
Definition lne_ztail (p : list Q) : list Q := p ++ (0%Q :: nil).

Lemma lne_eval_ztail : forall (p : list Q) (x : Q),
  QeqT (pint_eval (lne_ztail p) x) (pint_eval p x).
Proof.
  intros p x. apply qeq_imp_qeqT. unfold lne_ztail.
  induction p as [| a p' IH].
  - cbn [app pint_eval]. ring.
  - cbn [app pint_eval]. rewrite IH. ring.
Qed.

Lemma lne_integral_ztail : forall p : list Q,
  QeqT (pint_integral (lne_ztail p)) (pint_integral p).
Proof.
  intro p. apply qeq_imp_qeqT. unfold pint_integral, lne_ztail. generalize 0%nat.
  induction p as [| a p' IH]; intro k.
  - cbn [app pint_integral_from]. unfold pint_monomial_int.
    rewrite (fun d => qeqT_imp_qeq _ _ (pint_zero_div d)). ring.
  - cbn [app pint_integral_from]. rewrite IH. ring.
Qed.

(* Canonical coefficient list of t^a(1-t)^b (head = constant term; length a+b+1):
   list-level recursion on (1-t)^{b+1} = (1-t)^b - t*(1-t)^b; the first operand is zero-padded to keep lengths equal *)
Fixpoint lne_list (a b : nat) : list Q :=
  match b with
  | 0%nat => pint_pow_poly a
  | Datatypes.S b' =>
      pint_add (lne_ztail (lne_list a b'))
               (pint_scale (- 1)%Q (lne_list (Datatypes.S a) b'))
  end.

Lemma lne_scale_length : forall (a : Q) (p : list Q),
  Id (length (pint_scale a p)) (length p).
Proof.
  intros a p. induction p as [| c p' IH].
  - apply id_refl.
  - cbn [pint_scale length]. exact (id_cong (fun n => Datatypes.S n) IH).
Qed.

Lemma lne_add_length : forall p q : list Q,
  length p = length q -> Id (length (pint_add p q)) (length p).
Proof.
  intros p. induction p as [| a p' IH]; intros q Hlen.
  - destruct q as [| b q'].
    + apply id_refl.
    + discriminate Hlen.
  - destruct q as [| b q'].
    + discriminate Hlen.
    + cbn [pint_add length]. injection Hlen as Hlen'.
      exact (id_cong (fun n => Datatypes.S n) (IH q' Hlen')).
Qed.

Lemma lne_list_length : forall a b : nat,
  Id (length (lne_list a b)) (Datatypes.S (a + b))%nat.
Proof.
  intros x y.
  assert (He : forall a b : nat,
           (length (lne_list a b) = Datatypes.S (a + b))%nat).
  { intros a0 b0. revert a0. induction b0 as [| b' IH]; intros a.
    - cbn [lne_list]. replace (Datatypes.S (a + 0))%nat with (Datatypes.S a)%nat by lia.
      induction a as [| a' IHa].
      + reflexivity.
      + cbn [pint_pow_poly length] in IHa. cbn [pint_pow_poly length].
        rewrite IHa. reflexivity.
    - cbn [lne_list].
      assert (Hadd : forall p q : list Q,
               length p = length q -> length (pint_add p q) = length p).
      { intros u v Huv. destruct (lne_add_length u v Huv); reflexivity. }
      assert (Hscl : forall (c : Q) (p : list Q),
               length (pint_scale c p) = length p).
      { intros c u. destruct (lne_scale_length c u); reflexivity. }
      rewrite (Hadd (lne_ztail (lne_list a b'))
                    (pint_scale (- 1)%Q (lne_list (Datatypes.S a) b'))).
      + unfold lne_ztail. rewrite app_length, IH. cbn [length]. lia.
      + unfold lne_ztail. rewrite app_length, IH.
        rewrite (Hscl (- 1)%Q (lne_list (Datatypes.S a) b')), (IH (Datatypes.S a)).
        cbn [length]. lia. }
  destruct (He x y). apply id_refl.
Qed.

(* Evaluation linearity (no length premise: the zero-pad-free semantics is self-consistent). *)
Lemma lne_eval_add : forall (p q : list Q) (x : Q),
  QeqT (pint_eval (pint_add p q) x) (pint_eval p x + pint_eval q x).
Proof.
  intros p. induction p as [| a p' IH]; intros q x; apply qeq_imp_qeqT.
  - destruct q as [| b q'].
    + cbn [pint_add pint_eval]. ring.
    + cbn [pint_add pint_eval]. ring.
  - destruct q as [| b q'].
    + cbn [pint_add pint_eval]. ring.
    + cbn [pint_add pint_eval].
      rewrite (fun r y => qeqT_imp_qeq _ _ (IH r y)). ring.
Qed.

Lemma lne_eval_scale : forall (a : Q) (p : list Q) (x : Q),
  QeqT (pint_eval (pint_scale a p) x) (a * pint_eval p x).
Proof.
  intros a p x. apply qeq_imp_qeqT. induction p as [| c p' IH].
  - cbn [pint_scale pint_eval]. ring.
  - cbn [pint_scale pint_eval]. rewrite IH. ring.
Qed.

(* Semantic anchor: lne_list a b evaluates pointwise == t^a * (1-t)^b. *)
Lemma lne_beta_eval : forall (a b : nat) (t : Q),
  QeqT (pint_eval (lne_list a b) t) (q_pow t a * q_pow (1 - t) b).
Proof.
  intros a b t. apply qeq_imp_qeqT. revert a.
  induction b as [| b' IH]; intros a.
  - cbn [lne_list]. cbn [q_pow].
    rewrite <- (qeqT_imp_qeq _ _ (pint_eval_pow_poly a t)).
    ring.
  - cbn [lne_list].
    rewrite (qeqT_imp_qeq _ _ (lne_eval_add (lne_ztail (lne_list a b'))
               (pint_scale (- 1)%Q (lne_list (Datatypes.S a) b')) t)).
    rewrite (qeqT_imp_qeq _ _ (lne_eval_ztail (lne_list a b') t)).
    rewrite (qeqT_imp_qeq _ _ (lne_eval_scale (- 1)%Q
               (lne_list (Datatypes.S a) b') t)).
    rewrite (IH (Datatypes.S a)).
    rewrite (IH a).
    rewrite (qeqT_imp_qeq _ _ (q_pow_succ t a)).
    rewrite (qeqT_imp_qeq _ _ (q_pow_succ (1 - t)%Q b')). ring.
Qed.

(* Beta closed form: int_0^1 t^a(1-t)^b dt == a! * b! / (a+b+1)!.
   Induction on the second argument b: step = linear split + division merge (lne_div_sub / lne_div_eq). *)
Theorem lne_beta_value : forall a b : nat,
  QeqT (pint_integral (lne_list a b))
       (q_fact a * q_fact b / q_fact (a + b + 1)%nat).
Proof.
  intros a b. apply qeq_imp_qeqT. revert a.
  induction b as [| b' IH]; intros a.
  - cbn [lne_list].
    assert (H := qeqT_imp_qeq _ _ (pint_integral_pow_poly a)).
    rewrite H.
    replace (a + 0 + 1)%nat with (Datatypes.S a)%nat by lia.
    cbn [q_fact].
    apply qeqT_imp_qeq. apply lne_div_eq.
    + unfold Qlt. cbn [Qnum Qden Qplus Qmult Qinv q_fact]. lia.
    + apply Qmult_lt_0_compat.
      * unfold Qlt. cbn [Qnum Qden Qplus Qmult Qinv q_fact]. lia.
      * apply QltT_to_Qlt. apply q_fact_pos.
    + ring.
  - cbn [lne_list].
    assert (HL : length (lne_ztail (lne_list a b'))
                 = length (pint_scale (- 1)%Q (lne_list (Datatypes.S a) b'))).
    { unfold lne_ztail. rewrite app_length.
      assert (Hll1 : (length (lne_list a b') = Datatypes.S (a + b'))%nat)
        by (destruct (lne_list_length a b'); reflexivity).
      assert (Hll2 : (length (lne_list (Datatypes.S a) b')
                        = Datatypes.S (Datatypes.S a + b'))%nat)
        by (destruct (lne_list_length (Datatypes.S a) b'); reflexivity).
      assert (Hsc : (length (pint_scale (- 1)%Q (lne_list (Datatypes.S a) b'))
                       = length (lne_list (Datatypes.S a) b'))%nat)
        by (destruct (lne_scale_length (- 1)%Q
               (lne_list (Datatypes.S a) b')); reflexivity).
      rewrite Hll1, Hsc, Hll2. cbn [length]. lia. }
    assert (Hadd := qeqT_imp_qeq _ _ (pint_integral_add _ _ HL)).
    rewrite Hadd, (qeqT_imp_qeq _ _ (lne_integral_ztail (lne_list a b'))).
    assert (Hsc := qeqT_imp_qeq _ _ (pint_integral_scale (- 1)%Q (lne_list (Datatypes.S a) b'))).
    rewrite Hsc.
    rewrite (IH a), (IH (Datatypes.S a)).
    rewrite (qeqT_imp_qeq _ _ (q_fact_succ b')).
    rewrite (qeqT_imp_qeq _ _ (q_fact_succ a)).
    replace (a + Datatypes.S b' + 1)%nat with (Datatypes.S (a + b' + 1))%nat by lia.
    replace (Datatypes.S a + b' + 1)%nat with (Datatypes.S (a + b' + 1))%nat by lia.
    rewrite (qeqT_imp_qeq _ _ (q_fact_succ (a + b' + 1)%nat)).
    assert (EJ : (Z.of_nat (Datatypes.S (a + b' + 1)) # 1)%Q
                 == ((Z.of_nat (Datatypes.S a) # 1)
                       + (Z.of_nat (Datatypes.S b') # 1))%Q).
    { unfold Qeq, Qplus. cbn [Qnum Qden Qmult Pos.mul].
      replace (Z.of_nat (Datatypes.S (a + b' + 1)))
        with ((Z.of_nat (Datatypes.S a) + Z.of_nat (Datatypes.S b'))%Z) by lia.
      lia. }
    rewrite EJ.
    transitivity (q_fact a * q_fact b' / q_fact (a + b' + 1)
                  - (((Z.of_nat (Datatypes.S a) # 1) * q_fact a * q_fact b')
                       / (((Z.of_nat (Datatypes.S a) # 1)
                             + (Z.of_nat (Datatypes.S b') # 1))
                            * q_fact (a + b' + 1)))).
    + ring.
    + rewrite (fun H1 H2 => qeqT_imp_qeq _ _
                 (lne_div_sub (q_fact a * q_fact b')
                 (q_fact (a + b' + 1))
                 (((Z.of_nat (Datatypes.S a) # 1) * q_fact a) * q_fact b')
                 (((Z.of_nat (Datatypes.S a) # 1)
                     + (Z.of_nat (Datatypes.S b') # 1))
                    * q_fact (a + b' + 1)) H1 H2)).
      * apply qeqT_imp_qeq.
        apply (lne_div_eq
                 ((q_fact a * q_fact b')
                    * (((Z.of_nat (Datatypes.S a) # 1)
                          + (Z.of_nat (Datatypes.S b') # 1))
                         * q_fact (a + b' + 1))
                  - (((Z.of_nat (Datatypes.S a) # 1) * q_fact a) * q_fact b')
                      * q_fact (a + b' + 1))
                 (q_fact (a + b' + 1)
                    * (((Z.of_nat (Datatypes.S a) # 1)
                          + (Z.of_nat (Datatypes.S b') # 1))
                         * q_fact (a + b' + 1)))
                 (q_fact a * ((Z.of_nat (Datatypes.S b') # 1) * q_fact b'))
                 (((Z.of_nat (Datatypes.S a) # 1)
                     + (Z.of_nat (Datatypes.S b') # 1))
                    * q_fact (a + b' + 1))).
        -- apply Qmult_lt_0_compat.
           ++ apply QltT_to_Qlt. apply q_fact_pos.
           ++ apply Qmult_lt_0_compat.
              ** unfold Qlt. cbn [Qnum Qden Qplus]. lia.
              ** apply QltT_to_Qlt. apply q_fact_pos.
        -- apply Qmult_lt_0_compat.
           ++ unfold Qlt. cbn [Qnum Qden Qplus]. lia.
           ++ apply QltT_to_Qlt. apply q_fact_pos.
        -- ring.
      * apply QltT_to_Qlt. apply q_fact_pos.
      * apply Qmult_lt_0_compat.
        -- unfold Qlt. cbn [Qnum Qden Qplus Qmult Qinv q_fact]. lia.
        -- apply QltT_to_Qlt. apply q_fact_pos.
Qed.

(* Main carrier: lne_B n := int_0^1 t^n(1-t)^n dt (the discrete bearer of the Pade integrand numerator). *)
Definition lne_B (n : nat) : Q := pint_integral (lne_list n n).

(* Carrier closed form (diagonal specialization): lne_B n == (n!)^2/(2n+1)!. *)
Lemma lne_B_closed : forall n : nat,
  QeqT (lne_B n) (q_fact n * q_fact n / q_fact (Datatypes.S (n + n))%nat).
Proof.
  intro n. unfold lne_B. apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (lne_beta_value n n)).
  replace (n + n + 1)%nat with (Datatypes.S (n + n))%nat by lia.
  reflexivity.
Qed.

(* ============================================================ *)
(* Section C. Exponential upper bound: lne_B n <= 4^{-n} (core: nat factorial inequality by induction). *)
(* ============================================================ *)

Lemma lne_pow4 : forall n : nat, Id (4 ^ n)%nat (2 ^ (2 * n))%nat.
Proof.
  intro n.
  assert (He : (4 ^ n = 2 ^ (2 * n))%nat).
  { induction n as [| n IH].
    - cbn [Nat.mul Nat.pow]. reflexivity.
    - rewrite Nat.pow_succ_r'. rewrite IH.
      replace (2 * Datatypes.S n)%nat with (Datatypes.S (Datatypes.S (2 * n)))%nat by lia.
      rewrite !Nat.pow_succ_r'. lia. }
  destruct He. apply id_refl.
Qed.

(* Core inequality: (n!)^2 * 4^n <= (2n+1)! (integral form of (2n+1)*C(2n,n) >= 4^n).
   Induction step: multiply the IH by 4(n+1)^2 <= (2n+2)(2n+3). *)
Lemma lne_nat_core : forall n : nat,
  NatLe (fact n * fact n * (2 ^ (2 * n))%nat) (fact (2 * n + 1)).
Proof.
  intro n. apply NatLe_lift.
  induction n as [| n IH].
  - simpl. lia.
  - cbn [fact].
    replace (2 * Datatypes.S n + 1)%nat
      with (Datatypes.S (Datatypes.S (2 * n + 1)))%nat by lia.
    cbn [fact].
    replace (2 * Datatypes.S n)%nat
      with (Datatypes.S (Datatypes.S (2 * n)))%nat by lia.
    rewrite !Nat.pow_succ_r'.
    assert (H4 : (4 * Datatypes.S n * Datatypes.S n
                  <= Datatypes.S (Datatypes.S (2 * n + 1))
                       * Datatypes.S (2 * n + 1))%nat) by lia.
    assert (H5 : (fact n * fact n * 2 ^ (2 * n)
                    * (4 * Datatypes.S n * Datatypes.S n)
                  <= fact (2 * n + 1) * (4 * Datatypes.S n * Datatypes.S n))%nat)
      by (apply Nat.mul_le_mono_r; exact IH).
    transitivity (fact (2 * n + 1) * (4 * Datatypes.S n * Datatypes.S n))%nat.
    + replace ((Datatypes.S n * fact n) * (Datatypes.S n * fact n)
                 * (2 * (2 * 2 ^ (2 * n)))%nat)%nat
        with ((fact n * fact n * 2 ^ (2 * n))%nat
                * (4 * Datatypes.S n * Datatypes.S n)%nat)%nat
        by ring.
      exact H5.
    + assert (H6 : ((4 * Datatypes.S n * Datatypes.S n) * fact (2 * n + 1)
                     <= (Datatypes.S (Datatypes.S (2 * n + 1))
                          * Datatypes.S (2 * n + 1)) * fact (2 * n + 1))%nat)
        by (apply Nat.mul_le_mono_r; exact H4).
      lia.
Qed.

Lemma lne_pow_ge1 : forall n : nat, NatLe 1 (4 ^ n)%nat.
Proof.
  intro n. apply NatLe_lift.
  induction n as [| n IH].
  - cbn [Nat.pow]. lia.
  - rewrite Nat.pow_succ_r'. lia.
Qed.

(* The Q-face bearer of 4^n and its positivity. *)
Fixpoint lne_p4 (n : nat) : Q :=
  match n with
  | O => (1 # 1)
  | Datatypes.S m => (4 # 1) * lne_p4 m
  end.

Lemma lne_p4_Z : forall n : nat, QeqT (lne_p4 n) ((Z.of_nat (4 ^ n)) # 1)%Q.
Proof.
  intro n. apply qeq_imp_qeqT.
  induction n as [| n IH].
  - reflexivity.
  - cbn [lne_p4]. rewrite IH. rewrite Nat.pow_succ_r'.
    rewrite Nat2Z.inj_mul. cbn [Z.of_nat].
    unfold Qmult. cbn [Qnum Qden Pos.mul]. reflexivity.
Qed.

Lemma lne_p4_pos : forall n : nat, QltT 0 (lne_p4 n).
Proof.
  intro n. apply Qlt_to_QltT.
  induction n as [| n IH].
  - unfold Qlt. cbn [Qnum Qden lne_p4]. lia.
  - cbn [lne_p4]. apply Qmult_lt_0_compat.
    + unfold Qlt. cbn [Qnum Qden]. lia.
    + exact IH.
Qed.

(* Divide-by-right-inverse comparator: 0 < y, 0 < w, x*w <= y imply x/y <= 1/w (all on the Q face). *)
Lemma lne_div_le_inv : forall x y w : Q,
  Qlt 0 y -> Qlt 0 w -> Qle (x * w) y -> QleT' (x / y) (Qinv w).
Proof.
  intros x y w Hy Hw Hxy. apply Qle_to_QleT'. unfold Qdiv.
  assert (Hy0 : ~ (y == 0%Q)).
  { intro E. apply (Qlt_not_eq 0%Q y Hy). exact (Qeq_sym _ _ E). }
  assert (Hw0 : ~ (w == 0%Q)).
  { intro E. apply (Qlt_not_eq 0%Q w Hw). exact (Qeq_sym _ _ E). }
  assert (Eyw : (w * Qinv w)%Q == 1%Q) by (apply Qmult_inv_r; exact Hw0).
  assert (Eyy : (y * Qinv y)%Q == 1%Q) by (apply Qmult_inv_r; exact Hy0).
  assert (H1 : Qle ((x * w) * Qinv y) (y * Qinv y)).
  { apply (Qmult_le_compat_r (x * w) y).
    - exact Hxy.
    - apply Qlt_le_weak. apply Qinv_lt_0_compat. exact Hy. }
  rewrite Eyy in H1.
  assert (H2 : Qle (((x * w) * Qinv y) * Qinv w) (1%Q * Qinv w)).
  { apply (Qmult_le_compat_r ((x * w) * Qinv y) (1%Q)).
    - exact H1.
    - apply Qlt_le_weak. apply Qinv_lt_0_compat. exact Hw. }
  rewrite Qmult_1_l in H2.
  assert (E3 : (((x * w) * Qinv y) * Qinv w)%Q
               == (x * (w * Qinv w) * Qinv y)%Q) by ring.
  rewrite E3 in H2. rewrite Eyw in H2. rewrite Qmult_1_r in H2.
  exact H2.
Qed.

(* Upper-bound main statement (Set face): lne_B n <= 4^{-n}. *)
Theorem lne_B_le_p4 : forall n : nat, QleT' (lne_B n) (Qinv (lne_p4 n)).
Proof.
  intro n. apply Qle_to_QleT'.
  rewrite (qeqT_imp_qeq _ _ (lne_B_closed n)).
  rewrite (qeqT_imp_qeq _ _ (sif_qfact_Z n)).
  rewrite (qeqT_imp_qeq _ _ (sif_qfact_Z (Datatypes.S (n + n)))).
  rewrite (qeqT_imp_qeq _ _ (lne_p4_Z n)).
  apply (fun H1 H2 H3 => QleT'_to_Qle _ _
           (lne_div_le_inv ((Z.of_nat (fact n) # 1) * (Z.of_nat (fact n) # 1))
              ((Z.of_nat (fact (Datatypes.S (n + n))) # 1))
              ((Z.of_nat (4 ^ n) # 1)) H1 H2 H3)).
  - unfold Qlt. cbn [Qnum Qden].
    pose proof (NatLe_drop _ _ (lne_fact_ge1 (Datatypes.S (n + n)))) as Hg. lia.
  - unfold Qlt. cbn [Qnum Qden].
    pose proof (NatLe_drop _ _ (lne_pow_ge1 n)) as Hg. lia.
  - assert (He4 : (4 ^ n = 2 ^ (2 * n))%nat) by (destruct (lne_pow4 n); reflexivity).
    rewrite He4.
    pose proof (NatLe_drop _ _ (lne_nat_core n)) as Hnat.
    replace (2 * n + 1)%nat with (Datatypes.S (n + n))%nat in Hnat by lia.
    unfold Qle. cbn [Qnum Qden Qmult Pos.mul].
    lia.
Qed.

(* ============================================================ *)
(* Section D. Integrality: lne_B n * (2n+1)! = (n!)^2 in Z (sigT witness form). *)
(* ============================================================ *)

Theorem lne_B_int : forall n : nat,
  sigT (fun m : Z => QeqT (lne_B n * q_fact (Datatypes.S (n + n))%nat)
                           (m # 1)).
Proof.
  intro n. exists (Z.of_nat (fact n * fact n))%Z. apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (lne_B_closed n)).
  rewrite (qeqT_imp_qeq _ _ (sif_qfact_Z n)).
  rewrite (qeqT_imp_qeq _ _ (sif_qfact_Z (Datatypes.S (n + n)))).
  unfold Qdiv.
  transitivity (((Z.of_nat (fact n) # 1) * (Z.of_nat (fact n) # 1))%Q).
  - assert (E1 : ((((Z.of_nat (fact n) # 1) * (Z.of_nat (fact n) # 1))
                     * Qinv ((Z.of_nat (fact (Datatypes.S (n + n))) # 1)))
                    * (Z.of_nat (fact (Datatypes.S (n + n))) # 1))%Q
                 == (((Z.of_nat (fact n) # 1) * (Z.of_nat (fact n) # 1))
                       * ((Z.of_nat (fact (Datatypes.S (n + n))) # 1)
                            * Qinv ((Z.of_nat (fact (Datatypes.S (n + n))) # 1))))%Q)
      by ring.
    rewrite E1.
    rewrite (Qmult_inv_r
      ((Z.of_nat (fact (Datatypes.S (n + n))) # 1)%Q)).
    + ring.
    + intro E. apply (Qlt_not_eq 0%Q
          ((Z.of_nat (fact (Datatypes.S (n + n))) # 1))%Q).
      * unfold Qlt. cbn [Qnum Qden].
        pose proof (NatLe_drop _ _ (lne_fact_ge1 (Datatypes.S (n + n)))) as Hg. lia.
      * exact (Qeq_sym _ _ E).
  - rewrite Nat2Z.inj_mul.
    unfold Qmult. cbn [Qnum Qden Pos.mul]. reflexivity.
Qed.

(* Positivity (Set face): 0 < lne_B n strictly. *)
Theorem lne_B_posT : forall n : nat, QltT 0 (lne_B n).
Proof.
  intro n. apply Qlt_to_QltT. rewrite (qeqT_imp_qeq _ _ (lne_B_closed n)).
  unfold Qdiv.
  apply Qmult_lt_0_compat.
  - apply Qmult_lt_0_compat; apply QltT_to_Qlt; apply q_fact_pos.
  - apply Qinv_lt_0_compat. apply QltT_to_Qlt. apply q_fact_pos.
Qed.

(* ============================================================ *)
(* Section E. The triple Set specification and the window-match statement. *)
(* ============================================================ *)

(* Positivity + exponential bound + integrality, the triple as one Set specification. *)
Definition lne_three_spec : Set :=
  sigT (fun n : nat =>
    And (QltT 0 (lne_B n))
      (And (QleT' (lne_B n) (Qinv (lne_p4 n)))
           (sigT (fun m : Z =>
             QeqT (lne_B n * q_fact (Datatypes.S (n + n))%nat)
                    (m # 1))))).

Definition lne_three_spec_holds : forall n : nat, lne_three_spec :=
  fun n => existT _ n
    ((lne_B_posT n, (lne_B_le_p4 n, lne_B_int n))).

(* Window match: lne_B n falls strictly inside the decision window 2^{-n} (n >= 1; via 4^{-n} < 2^{-n}). *)
Lemma lne_B_lt_p2 : forall n : nat, (1 <= n)%nat ->
  QltT (lne_B n) (Qinv (ln2i_p2 n)).
Proof.
  intros n Hn. apply Qlt_to_QltT.
  apply (Qle_lt_trans (lne_B n) (Qinv (lne_p4 n)) (Qinv (ln2i_p2 n))).
  - apply QleT'_to_Qle. apply lne_B_le_p4.
  - assert (Huv : Qlt (ln2i_p2 n) (lne_p4 n)).
    { rewrite ln2i_p2_Z. rewrite (qeqT_imp_qeq _ _ (lne_p4_Z n)).
      assert (He4 : (4 ^ n = 2 ^ (2 * n))%nat)
        by (destruct (lne_pow4 n); reflexivity).
      rewrite He4.
      pose proof (Nat.pow_lt_mono_r 2 n (2 * n) ltac:(lia) ltac:(lia)) as Hp.
      unfold Qlt. cbn [Qnum Qden]. lia. }
    pose proof (QltT_to_Qlt 0 (lne_p4 n) (lne_p4_pos n)) as Hp4.
    assert (Hu0 : Qlt 0 (ln2i_p2 n)) by apply ln2i_p2_pos.
    exact (proj1 (Qinv_lt_contravar (ln2i_p2 n) (lne_p4 n) Hu0 Hp4) Huv).
Qed.

(* Consumption: the carrier falls strictly inside the UpReqLn2Irrational decision window ln2i_e n = 2^{-n}. *)
Theorem lne_B_in_window : forall n : nat, (1 <= n)%nat ->
  QltT (lne_B n) (ln2i_e n).
Proof.
  intros n Hn. unfold ln2i_e. apply lne_B_lt_p2. exact Hn.
Qed.

(* ============================================================ *)
(* Section F. Conditional-form closing consumption: routes through the criterion theorem itself, no bypass. *)
(* ============================================================ *)

Theorem lne_ln2_irrational_cond : forall (Hesc : ln2i_escape_spec) (q : Q),
  sigT (fun c : Q => And (QltT 0 c)
    (real_lt (real_const c)
       (real_metric (existT (fun u : Qseq => cauchy u) ln2i_x
                         (lic_seq_cauchy ln2i_x ln2i_e ln2i_tail ln2i_vanish))
       (real_const q)))).
Proof.
  intros Hesc q.
  exact (ln2i_irrational_criterion_cond Hesc q).
Qed.

(* ============================================================ *)
(* Section G. Extraction probe and axiom-face self-audit. *)
(* ============================================================ *)

From Stdlib Require Import Extraction.
Separate Extraction lne_three_spec_holds lne_B_int lne_B_lt_p2
  lne_B_in_window lne_ln2_irrational_cond lne_B lne_p4.

Print Assumptions lne_three_spec_holds.
Print Assumptions lne_B_le_p4.
Print Assumptions lne_B_int.
Print Assumptions lne_B_in_window.
Print Assumptions lne_ln2_irrational_cond.
