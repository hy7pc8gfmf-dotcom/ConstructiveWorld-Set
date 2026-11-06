(* ConstructiveWorld-Set -- constructive escape-window and gap-floor certificates for the ln 2 native route. *)

(** * abl_Ln2_native_escape_03: the d_n = 2^n * n! integrality ladder and the native gap floor for ln 2.

    Mission.  First step of the native escape route for ln 2: the master line
      [abl3_dn] with d_n = 2^n * n!, the integrality ladders [abl3_dn_xn_int]
      and [abl3_dn_q_int], the native gap floor [abl3_native_gap], the window
      fit certificate [abl3_floor_le_window], and the conditional escape
      interface [abl3_escape_of_floor_beat].

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs], [ZArith.ZArith],
      [Arith.Arith], [Arith.Factorial], [Bool.Bool], [Lia], [Setoid],
      [Morphisms], [Qfield], [Extraction].  Requires
      [S01_BaseRing], [S02_CauchyComplete], [S03_QExp], [SumInvFactEscape],
      [UpReqBanachExp], [UpReqBanachInst], [UpReqBanachInstB],
      [UpReqBanachInstReal], [UpReqBanachNormOpp], [UpReqIrrationalCriterion],
      [UpReqLn2Irrational] of this development.

    References.  This development, abl_Ln2_native_escape_03.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" abl_Ln2_native_escape_03.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 00015ff4]. *)
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import SumInvFactEscape.
Require Import UpReqBanachNormOpp.
Require Import UpReqIrrationalCriterion.
Require Import UpReqLn2Irrational.
From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith
  Arith.Arith Bool.Bool.
From Stdlib Require Import Arith.Factorial.
From Stdlib Require Import Lia Setoid Morphisms Qfield.

(* ============================================================ *)
(* Section 1. The master line: d_0 = 1, d_{S m} = 2 * (S m) * d_m, i.e. 2^n * n!. *)
(* ============================================================ *)

Fixpoint abl3_dn (n : nat) : Q :=
  match n with
  | O => (1 # 1)
  | Datatypes.S m => ((2 # 1) * ((Z.of_nat (Datatypes.S m)) # 1)) * abl3_dn m
  end.

Lemma abl3_dn_succ : forall m : nat,
  abl3_dn (Datatypes.S m) == ((2 # 1) * ((Z.of_nat (Datatypes.S m)) # 1)) * abl3_dn m.
Proof.
  intro m. exact (Qeq_refl (((2 # 1) * ((Z.of_nat (Datatypes.S m)) # 1)) * abl3_dn m)%Q).
Qed.

Lemma abl3_dn_pos : forall n : nat, Qlt 0 (abl3_dn n).
Proof.
  induction n as [|n IH].
  - unfold Qlt. cbn [abl3_dn Qnum Qden]. lia.
  - rewrite abl3_dn_succ. apply Qmult_lt_0_compat.
    + apply Qmult_lt_0_compat; unfold Qlt; cbn [Qnum Qden]; lia.
    + exact IH.
Qed.

(* Z-carried form: [abl3_dn n] equals [(2^n)#1] times [(n!)#1]. *)
Lemma abl3_dn_Z : forall n : nat,
  abl3_dn n == ((Z.of_nat (2 ^ n)) # 1) * ((Z.of_nat (fact n)) # 1).
Proof.
  induction n as [|n IH].
  - reflexivity.
  - rewrite abl3_dn_succ. rewrite IH.
    rewrite Nat.pow_succ_r'.
    replace (fact (Datatypes.S n)) with (Datatypes.S n * fact n)%nat by reflexivity.
    rewrite !Nat2Z.inj_mul. cbn [Z.of_nat].
    unfold Qmult, Qeq. cbn [Qnum Qden Pos.mul]. lia.
Qed.

Lemma abl3_fact_ge1 : forall n : nat, (1 <= fact n)%nat.
Proof.
  induction n as [|n IH]; cbn [fact].
  - lia.
  - nia.
Qed.

(* Divisibility ladder for the factorial: for 1 <= v <= n, [fact n] = v * c *)
(* holds with an explicit quotient witness [c]. *)
Lemma abl3_fact_dvd : forall v n : nat, (1 <= v)%nat -> (v <= n)%nat ->
  sigT (fun c : nat => fact n = (v * c)%nat).
Proof.
  intros v n. induction n as [|n IH]; intros Hle Hle2.
  - lia.
  - destruct (Nat.eq_dec v (Datatypes.S n)) as [E | NE].
    + subst v. exists (fact n). cbn [fact]. lia.
    + assert (Hvn : (v <= n)%nat) by lia.
      destruct (IH ltac:(lia) Hvn) as [c Hc].
      exists (Datatypes.S n * c)%nat. cbn [fact]. lia.
Qed.

(* ============================================================ *)
(* Section 2. Main integrality ladder: d_n * x_n in Z, carrying over the   *)
(*   recursion pattern of [sif_d].  Recursion core:                        *)
(*   d_{S m} * t_{S m} = 2(S m) * d_m / ((S m) * 2^{S m}) = d_m / 2^m = m!, *)
(*   an integral step of the same shape as the e-chain                     *)
(*   n! * s_{n+1} = (n+1) * n! * s_n + 1.                                  *)
(* ============================================================ *)

Lemma abl3_dn_t : forall m : nat,
  abl3_dn (Datatypes.S m) * ln2i_t (Datatypes.S m) == ((Z.of_nat (fact m)) # 1).
Proof.
  intro m. unfold ln2i_t.
  replace (2 ^ Datatypes.S m)%nat with (2 * 2 ^ m)%nat
    by (rewrite Nat.pow_succ_r'; reflexivity).
  rewrite abl3_dn_succ. rewrite (abl3_dn_Z m).
  pose proof (Nat2Z.inj_mul 2 (2 ^ m)) as Hm.
  pose proof (ln2i_powZ_pos m) as Hp.
  destruct ((Z.of_nat (Datatypes.S m) * Z.of_nat ((2 * 2 ^ m)%nat))%Z) as [|p|p] eqn:E.
  - exfalso. nia.
  - unfold Qinv, Qmult, Qeq. cbn [Qnum Qden Pos.mul]. nia.
  - unfold Qinv, Qmult, Qeq. cbn [Qnum Qden Pos.mul]. nia.
Qed.

Theorem abl3_dn_xn_int : forall n : nat,
  sigT (fun z : Z => QeqT (abl3_dn n * ln2i_x n) (z # 1)).
Proof.
  induction n as [|n IH].
  - exists 0%Z. apply qeq_imp_qeqT. cbn [abl3_dn ln2i_x].
    unfold Qmult, Qeq. cbn [Qnum Qden Pos.mul]. lia.
  - destruct IH as [z Hz].
    assert (Hzq : abl3_dn n * ln2i_x n == (z # 1))
      by (apply qeqT_imp_qeq; exact Hz).
    exists ((2 * Z.of_nat (Datatypes.S n)) * z + Z.of_nat (fact n))%Z.
    apply qeq_imp_qeqT.
    cbn [ln2i_x].
    transitivity (abl3_dn (Datatypes.S n) * ln2i_x n
                  + abl3_dn (Datatypes.S n) * ln2i_t (Datatypes.S n))%Q.
    + ring.
    + rewrite (abl3_dn_t n). rewrite abl3_dn_succ.
      (* After the [abl3_dn_succ] rewrite the goal product is left-associated,
         so the [Hzq] equation mismatches by associativity; reassociate with
         [Qmult_assoc] first, then rewrite. *)
      rewrite <- (Qmult_assoc ((2 # 1) * ((Z.of_nat (Datatypes.S n)) # 1))
                   (abl3_dn n) (ln2i_x n)). rewrite Hzq.
      unfold Qplus, Qmult, Qeq. cbn [Qnum Qden Pos.mul]. lia.
Qed.

(* ============================================================ *)
(* Section 3. Integrality by common multiplication: n >= den q implies     *)
(*   d_n * q in Z.                                                         *)
(* ============================================================ *)

Theorem abl3_dn_q_int : forall (u : Z) (pv : positive) (n : nat),
  (Z.pos pv <= Z.of_nat n)%Z ->
  sigT (fun z : Z => QeqT (abl3_dn n * ((u # pv)%Q)) (z # 1)).
Proof.
  intros u pv n Hd.
  pose (vn := Z.to_nat (Z.pos pv)).
  assert (Hpv : Z.pos pv = Z.of_nat vn)
    by (unfold vn; symmetry; apply Z2Nat.id; apply Z.lt_le_incl; apply Pos2Z.is_pos).
  assert (Hvn : (vn <= n)%nat).
  { apply (proj2 (Nat2Z.inj_le vn n)). rewrite <- Hpv. exact Hd. }
  assert (Hvn1 : (1 <= vn)%nat).
  { apply (proj2 (Nat2Z.inj_lt 0 vn)). rewrite <- Hpv. apply Pos2Z.is_pos. }
  destruct (abl3_fact_dvd vn n Hvn1 Hvn) as [c Hc].
  exists ((Z.of_nat (2 ^ n)) * (Z.of_nat c) * u)%Z.
  apply qeq_imp_qeqT.
  rewrite (abl3_dn_Z n).
  unfold Qmult, Qeq. cbn [Qnum Qden Pos.mul].
  rewrite Hc. rewrite Hpv. rewrite !Nat2Z.inj_mul. cbn [Z.of_nat]. lia.
Qed.

(* ============================================================ *)
(* Section 4. Native gap floor: q <> x_n (a Set-level separation premise)  *)
(*   implies |q - x_n| >= 1/d_n, with 1/d_n = 2^{-n}/n! the explicit       *)
(*   master-line form of the order-2/(n! * 2^n) gap.                       *)
(* ============================================================ *)

Theorem abl3_native_gap : forall (u : Z) (pv : positive) (n : nat),
  (Z.pos pv <= Z.of_nat n)%Z ->
  QltT 0 (Qabs (((u # pv)%Q - ln2i_x n)%Q)) ->
  QleT' (Qinv (abl3_dn n)) (Qabs (((u # pv)%Q - ln2i_x n)%Q)).
Proof.
  intros u pv n Hd Hpos.
  destruct (abl3_dn_xn_int n) as [z2 Hz2].
  destruct (abl3_dn_q_int u pv n Hd) as [z1 Hz1].
  assert (Hne : ~ (abl3_dn n == 0%Q)).
  { intro E. pose proof (abl3_dn_pos n) as Hp.
    exact (Qlt_not_eq 0%Q (abl3_dn n) Hp (eq_sym E)). }
  (* Core scaling identity: d_n * (q - x_n) == (z1 - z2)#1. *)
  assert (Hscale : abl3_dn n * ((u # pv)%Q - ln2i_x n)%Q == ((z1 - z2) # 1)%Q).
  { apply qeqT_imp_qeq in Hz1. apply qeqT_imp_qeq in Hz2.
    transitivity ((abl3_dn n * (u # pv)%Q - abl3_dn n * ln2i_x n)%Q).
    { ring. }
    rewrite Hz1. rewrite Hz2.
    (* The ring tactic does not see through the Qmake-Z atoms here, so the *)
    (* argument proceeds at the Z level by unfolding. *)
    unfold Qminus, Qplus, Qopp, Qmult, Qeq. cbn [Qnum Qden Pos.mul]. lia. }
  assert (Habs : Qabs (abl3_dn n * ((u # pv)%Q - ln2i_x n)%Q)
                 == abl3_dn n * Qabs (((u # pv)%Q - ln2i_x n)%Q)).
  { rewrite (Qabs_Qmult (abl3_dn n) (((u # pv)%Q - ln2i_x n)%Q)).
    rewrite (Qabs_pos (abl3_dn n) (Qlt_le_weak 0%Q (abl3_dn n) (abl3_dn_pos n))).
    reflexivity. }
  pose proof (QltT_to_Qlt _ _ Hpos) as Hposq.
  assert (Hspos : Qlt 0 (abl3_dn n * Qabs (((u # pv)%Q - ln2i_x n)%Q))).
  { apply Qmult_lt_0_compat.
    - exact (abl3_dn_pos n).
    - exact Hposq. }
  (* Hence |z1 - z2| >= 1, the absolute-value floor of a nonzero integer. *)
  assert (Hzne : ~ ((z1 - z2)%Z = 0%Z)).
  { intro E.
    assert (Habs0 : Qlt 0 (Qabs (abl3_dn n * ((u # pv)%Q - ln2i_x n)%Q))).
    { rewrite Habs. exact Hspos. }
    rewrite Hscale in Habs0.
    rewrite E in Habs0. cbn [Qabs] in Habs0.
    unfold Qlt in Habs0. cbn [Qnum Qden] in Habs0. lia. }
  assert (Habsform : Qabs (((z1 - z2) # 1)%Q) == ((Z.abs (z1 - z2)) # 1)%Q)
    by reflexivity.
  pose proof (proj2 (Z.abs_pos (z1 - z2)) Hzne) as Habsz.
  assert (Hchain : Qle (1 # 1) (abl3_dn n * Qabs (((u # pv)%Q - ln2i_x n)%Q))).
  { rewrite <- Habs. rewrite Hscale. rewrite Habsform.
    unfold Qle. cbn [Qnum Qden]. lia. }
  (* From d_n * |g| >= 1 the bound |g| >= 1/d_n follows by right             *)
  (* multiplication with [Qinv (abl3_dn n)].                                 *)
  assert (Hinvpos : Qlt 0 (Qinv (abl3_dn n)))
    by (apply Qinv_lt_0_compat; exact (abl3_dn_pos n)).
  assert (Hdn1 : abl3_dn n * Qinv (abl3_dn n) == 1%Q)
    by (apply Qmult_inv_r; exact Hne).
  assert (H1 : Qle ((1 # 1) * Qinv (abl3_dn n))
                   ((abl3_dn n * Qabs (((u # pv)%Q - ln2i_x n)%Q))
                      * Qinv (abl3_dn n)))
    by (apply Qmult_le_compat_r; [exact Hchain | apply Qlt_le_weak; exact Hinvpos]).
  assert (E2 : ((abl3_dn n * Qabs (((u # pv)%Q - ln2i_x n)%Q)) * Qinv (abl3_dn n))%Q
               == (Qabs (((u # pv)%Q - ln2i_x n)%Q)
                     * (abl3_dn n * Qinv (abl3_dn n)))%Q) by ring.
  rewrite E2, Hdn1, Qmult_1_r in H1.
  apply Qle_to_QleT'.
  apply (Qle_trans (Qinv (abl3_dn n)) ((1 # 1) * Qinv (abl3_dn n))
                   (Qabs (((u # pv)%Q - ln2i_x n)%Q))).
  - (* qeq_le proves the boolean-carrier QleT' form; the goal here is the *)
    (* order Qle, so bridge with QleT'_to_Qle before the equality step. *)
    apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
    symmetry. apply Qmult_1_l.
  - exact H1.
Qed.

(* ============================================================ *)
(* Section 5. Window fit certificate: the floor is at most the decision     *)
(*   window 2^{-n} for every index n, unconditionally.  Factor identity:    *)
(*   1/d_n = (1/n!) * 2^{-n} with 1/n! <= 1, and 1/n! does not grow with n, *)
(*   so the native gap through the [abl3_dn] master line never exceeds the  *)
(*   decision window [ln2i_e n] = 2^{-n} at any index.                      *)
(* ============================================================ *)

Theorem abl3_floor_le_window : forall n : nat, QleT' (Qinv (abl3_dn n)) (ln2i_e n).
Proof.
  intro n. unfold ln2i_e. apply Qle_to_QleT'.
  pose proof (abl3_dn_Z n) as HZ.
  pose proof (abl3_fact_ge1 n) as Hf1.
  assert (Hc1 : Qle (Qinv ((Z.of_nat (fact n)) # 1)) (Qinv (1 # 1))).
  { apply (ln2i_inv_le (1 # 1) ((Z.of_nat (fact n)) # 1)).
    - unfold Qlt. cbn [Qnum Qden]. lia.
    - unfold Qle. cbn [Qnum Qden]. lia. }
  pose proof (Qmult_le_compat_r (Qinv ((Z.of_nat (fact n)) # 1)) (Qinv (1 # 1))
                (Qinv (ln2i_p2 n)) Hc1
                (Qlt_le_weak 0%Q (Qinv (ln2i_p2 n)) (ln2i_inv_pos n))) as Hstep.
  assert (E10 : Qinv (1 # 1) == (1 # 1)%Q) by reflexivity.
  rewrite E10 in Hstep.
  apply (Qle_trans (Qinv (abl3_dn n))
                   (Qinv (ln2i_p2 n) * Qinv ((Z.of_nat (fact n)) # 1))
                   (Qinv (ln2i_p2 n))).
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
    rewrite HZ. rewrite ln2i_p2_Z.
    rewrite (Qinv_mult_distr ((Z.of_nat (2 ^ n)) # 1) ((Z.of_nat (fact n)) # 1)).
    reflexivity.
  - apply (Qle_trans _ (Qinv ((Z.of_nat (fact n)) # 1) * Qinv (ln2i_p2 n))).
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
    + apply (Qle_trans _ ((1 # 1) * Qinv (ln2i_p2 n))).
      * exact Hstep.
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qmult_1_l.
Qed.

(* ============================================================ *)
(* Section 6. Conditional escape interface: a window beaten by the floor    *)
(*   yields the single-point escape (the mounting face of future            *)
(*   approximation work).  Single-point form of the escape-window slot      *)
(*   [lic_escape_window].  The beat premise has no instance on this route,  *)
(*   since Sections 4 and 5 jointly show that it contradicts the floor for  *)
(*   growing n; a genuine instance belongs to the first-level Pade limb     *)
(*   face, where this interface becomes the direct application site of the  *)
(*   conditional form of the master criterion.                              *)
(* ============================================================ *)

Theorem abl3_escape_of_floor_beat : forall (q : Q) (n : nat), (1 <= n)%nat ->
  QltT 0 (Qabs ((q - ln2i_x n)%Q)) ->
  QltT (ln2i_e n) (Qinv (abl3_dn n)) ->
  sigT (fun m : nat => And ((1 <= m)%nat)
    (QltT (ln2i_e m) (Qabs ((q - ln2i_x m)%Q)))).
Proof.
  intros q n Hn1 Hsep Hbeat.
  exists n. split.
  - exact Hn1.
  - exfalso.
    (* The beat premise (window below floor) contradicts the Section 5 bound *)
    (* floor <= window, so it has no instance on this route; the sandwiched  *)
    (* chain yields a Qlt self-contradiction, closed by ex falso. *)
    pose proof (abl3_floor_le_window n) as Hfw.
    pose proof (QltT_to_Qlt _ _ Hbeat) as Hblt.
    pose proof (QleT'_to_Qle _ _ Hfw) as Hfle.
    exact (Qlt_not_eq (Qinv (abl3_dn n)) (Qinv (abl3_dn n))
             (Qle_lt_trans (Qinv (abl3_dn n)) (ln2i_e n) (Qinv (abl3_dn n))
                Hfle Hblt)
             (Qeq_refl (Qinv (abl3_dn n)))).
Qed.

(* ============================================================ *)
(* Section 7. Extraction check and assumption audit.                       *)
(* ============================================================ *)

From Stdlib Require Import Extraction.
Separate Extraction abl3_dn abl3_dn_xn_int abl3_dn_q_int
  abl3_native_gap abl3_floor_le_window abl3_escape_of_floor_beat.

Print Assumptions abl3_dn_xn_int.
Print Assumptions abl3_dn_q_int.
Print Assumptions abl3_native_gap.
Print Assumptions abl3_floor_le_window.
Print Assumptions abl3_escape_of_floor_beat.
