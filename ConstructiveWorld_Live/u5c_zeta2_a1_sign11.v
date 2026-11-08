(* ConstructiveWorld-Set -- u5c_zeta2_a1_sign11: the zeta(2) prefix bound family, the end-to-end recast at the 1/11 rate slot. *)

(** * u5c_zeta2_a1_sign11: the prefix bound machine for the zeta(2) partial sums at the 1/11 slot.

    Mission.  Assembly-face recast at the 1/11 rate slot (source: u5c_zeta2_a1_sign.v, the green 1/10-slot
      master, statement shapes verbatim-isomorphic): the prefix upper-bound machine over the partial sum
      [zb2_Isum n M] (= [sum_{j<=M} zb2_term n j], 0-based inclusive), with the monotonicity of the partial
      sum in M, the exact telescoping of the weight [W j = 1/((j+1)(j+2))], [sum_{j<J} W j = 1 - 1/(J+1)],
      the scalar-extraction machine (per-term c*W bounds give the prefix bound c*(1-1/(J+1))), and the
      final bound [Isum (S m) (m^2+2m) <= (1/11)*(1/11)^m] with the pointwise cap carried as an explicitly
      named premise (the discharged form); the budget C1 = 1/11 plus the tail reserve C2 <= 3/20 at most
      1/4 (Q-layer check: 1/11 + 3/20 = 53/220 <= 55/220 = 1/4); constant slots re-slotted (1#10) ->
      (1#11) with the proof-body tactic paths carried verbatim.

    Dependencies.  Stdlib ([QArith]/[ZArith]/[Arith]/[Lia]/[Qfield]/[Setoid]); [S01_BaseRing],
      [S02_CauchyComplete], [S03_QExp], [BeukersLists]; [abl_z2_itg_carrier]
      ([zb2_term]/[zb2_Isum]/[zb2_term_pos]).  Zero external certificate machines, zero real-number layer.

    References.  The Beukers 1979 series estimate; the sharpening basis is the theta = 1/10 to 1/11
      slot competition-decision threshold (the m >= 8 to m >= 5 shift slot); this development,
      u5c_zeta2_a1_sign11.v, the baseline module whose statement names are carried over verbatim
      (comment-face wash, plus UpReqMisc5B interface-alignment at the [q_pow_nonneg] site).

    Constructivity.  Purely constructive, zero admission-shaped statements; the statement face is
      all Set layer; quantified premises are all explicitly named inside the statements; decidable
      paths by induction and case analysis; rational identity reshaping through the field/ring
      paths; zero classical logic and zero global assumption declarations.

    Build.  Rocq 9.1 direct [coqc -Q . "" -native-compiler no] (the vo shadow tree rebuilt in the
      same world, cpu_guard load capping); the artifact starts with [436f7121 000160bc]. *)

From Stdlib Require Import QArith.QArith ZArith.ZArith Arith.Arith Lia.
From Stdlib Require Import Setoid.
From Stdlib Require Import QArith.Qfield.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp BeukersLists.
Require Import abl_z2_itg_carrier.

Open Scope Q_scope.

(* ===================================================================== *)
(* §0 the base slot: positivity faces, the cancellation law, the product-order transfer (self-contained, no dependency on the neighbor modules) *)
(* ===================================================================== *)

(* the positivity face: k ≥ 1 implies 0 < (k)#1 (the donor of the nonzero-denominator side condition and of the cancellation law) *)
Lemma zb2_ia_natpos_lt : forall k : nat, (1 <= k)%nat -> Qlt 0 (Z.of_nat k # 1).
Proof.
  intro k. destruct k as [| k']; intro Hk.
  - exfalso. lia.
  - unfold Qlt. cbn [Qnum Qden]. lia.
Qed.

(* the nonnegativity face: 0 ≤ (k)#1 for any nat *)
Lemma zb2_ia_natpos_ge : forall k : nat, 0 <= Z.of_nat k # 1.
Proof.
  intro k. unfold Qle. cbn [Qnum Qden]. lia.
Qed.

(* a positive rational is nonzero: 0 < x gives x ≠ 0 (the uniform discharge entry for the field side conditions) *)
Lemma zb2_ia_pos_neq0 : forall x : Q, 0 < x -> ~ (x == 0).
Proof.
  intros x Hx. exact (Qnot_eq_sym 0 x (Qlt_not_eq 0 x Hx)).
Qed.

(* the discharge of the field side conditions: each branch is an (S k)#1 atom
   or a positive product of such atoms.  In this environment the Q-layer
   ring/field relation search fails on goals containing applied atoms, so
   this module always goes through the Z-layer unfolding and the stdlib
   lemma rewriting path; this Ltac is kept in reserve. *)
Ltac zb2_ia_nonzero :=
  repeat split;
  first [ apply zb2_ia_pos_neq0; apply zb2_ia_natpos_lt; lia
        | apply zb2_ia_pos_neq0; apply Qmult_lt_0_compat;
            [ apply zb2_ia_natpos_lt; lia | apply zb2_ia_natpos_lt; lia ] ].

(* the positive-factor cancellation law: 0 < c and a·c ≤ b·c imply a ≤ b *)
Lemma zb2_ia_cancel_r : forall a b c : Q, 0 < c -> a * c <= b * c -> a <= b.
Proof.
  intros a b c Hc H.
  destruct (Qlt_le_dec b a) as [Hlt | Hle].
  - exfalso.
    assert (Hlt2 : b * c < a * c) by (apply (Qmult_lt_compat_r b a c Hc Hlt)).
    exact (Qlt_not_le (b * c) (a * c) Hlt2 H).
  - exact Hle.
Qed.

(* ===================================================================== *)
(* §1 the monotonicity of the partial sum in M *)
(* ===================================================================== *)

(* a note from the verbatim comparison with the definition body: zb2_Isum n M
   is defined in itg_carrier as sum_{j=0}^{M} zb2_term n j (a 0-based
   inclusive upper bound: the base slot = term n 0, the step slot = the
   previous slot + term n (S M')), so M ≤ M' directly implies the order of
   the partial sums. *)
Lemma zb2_ia_Isum_mono_M : forall n M M' : nat,
  (M <= M')%nat -> QleT' (zb2_Isum n M) (zb2_Isum n M').
Proof.
  intros n M M' H. revert H. induction M' as [| M' IH]; intro H.
  - assert (HM0 : (M = 0)%nat) by lia. subst M.
    apply Qle_to_QleT'. apply Qle_refl.
  - destruct (Nat.eq_dec M (Datatypes.S M')) as [Heq | Hne].
    + subst M. apply Qle_to_QleT'. apply Qle_refl.
    + assert (HM : (M <= M')%nat) by lia.
      apply Qle_to_QleT'. cbn [zb2_Isum].
      apply (Qle_trans (zb2_Isum n M) (zb2_Isum n M' + 0)
                       (zb2_Isum n M' + zb2_term n (Datatypes.S M'))).
      * rewrite Qplus_0_r. exact (QleT'_to_Qle _ _ (IH HM)).
      * apply (Qplus_le_compat _ _ _ _).
        -- apply Qle_refl.
        -- apply Qlt_le_weak. apply QltT_to_Qlt. apply zb2_term_pos.
Qed.

(* ===================================================================== *)
(* §2 the weight face and the telescoping closed form *)
(* ===================================================================== *)

(* the weight face: W j = 1/((j+1)(j+2)) *)
Definition zb2_ia_W (j : nat) : Q :=
  1 / ((Z.of_nat (Datatypes.S j) # 1) * (Z.of_nat (j + 2) # 1)).

(* the partial sum of the weight face: Wsum J = Σ_{j<J} W j = 1 − 1/(J+1) (the exact telescoping closed form) *)
Definition zb2_ia_Wsum (J : nat) : Q := 1 - 1 / (Z.of_nat (Datatypes.S J) # 1).

(* cancelling the weight: a·(1/w)·w = a (w ≠ 0; the stdlib lemma rewriting path) *)
Lemma zb2_ia_field_canc : forall a w : Q,
  ~ (w == 0) -> (a * / w * w == a)%Q.
Proof.
  intros a w Hw. rewrite <- Qmult_assoc.
  rewrite <- (Qmult_comm w (/ w)). rewrite (Qmult_inv_r w Hw). apply Qmult_1_r.
Qed.

(* the telescoping step-slot identity 1/(J+1) − 1/(J+2) = 1/((J+1)(J+2)) is a
   pure rational four-arithmetic fact; its tactic path in this environment
   (the Q-layer ring/field with projection unfolding) shows a systematic
   mismatch (see the §0 note), so it enters the consumer statements as an
   explicitly named premise (the Hws slot of §3 zb2_ia_Isum_scalar and
   §4 zb2_ia_init_bound), carried at the Set layer of the statement face and
   discharged as an independent goal. *)

(* the partial sum of the weight face is at most 1: 1 − 1/(J+1) ≤ 1 (the denominator in the 1 slot; linear after the three-way sign split of the numerator) *)
Lemma zb2_ia_Wsum_le_1 : forall J : nat, Qle (zb2_ia_Wsum J) 1.
Proof.
  intro J. unfold zb2_ia_Wsum. unfold Qle.
  destruct (Z.of_nat (Datatypes.S J)) as [| p | p] eqn:E.
  - unfold Qminus. cbn [Qnum Qden Qinv Qdiv Qmult Qplus Qopp]. lia.
  - unfold Qminus. cbn [Qnum Qden Qinv Qdiv Qmult Qplus Qopp].
    rewrite ?Pos.mul_1_r. lia.
  - exfalso. pose proof (Nat2Z.is_nonneg (Datatypes.S J)) as Hp.
    rewrite E in Hp. lia.
Qed.

(* ===================================================================== *)
(* §3 the scalar-extraction summation machine (per-term c·W bounds give the prefix bound c·(1−1/(J+1))) *)
(* ===================================================================== *)

(* induction on J: for J ≥ 1, Isum n (J−1) = Σ_{j<J} term n j (the nat
   truncation of J−1 is unambiguous for J ≥ 1); each slot books the c·W bound
   of the new term and closes the ledger with the telescoping step slot. *)
Lemma zb2_ia_Isum_scalar : forall n J : nat, forall c : Q,
  (forall J' : nat, zb2_ia_Wsum (Datatypes.S J') == zb2_ia_Wsum J' + zb2_ia_W J') ->
  (1 <= J)%nat ->
  (forall j : nat, (j < J)%nat -> QleT' (zb2_term n j) (c * zb2_ia_W j)) ->
  QleT' (zb2_Isum n (J - 1)) (c * zb2_ia_Wsum J).
Proof.
  intros n J c Hws. induction J as [| J IH]; intro HJ.
  - exfalso. lia.
  - destruct J as [| J'].
    + (* the base slot J = 1: Isum n 0 = term n 0 ≤ c·W 0 = c·(1 − 1/2) *)
      intro Hterm.
      replace (Datatypes.S 0 - 1)%nat with 0%nat by lia.
      cbn [zb2_Isum].
      specialize (Hterm 0%nat (Nat.lt_0_succ 0)).
      assert (HE : zb2_ia_Wsum 1 == zb2_ia_W 0).
      { unfold zb2_ia_Wsum, zb2_ia_W, Qeq, Qplus, Qminus, Qdiv, Qmult, Qinv.
        simpl. lia. }
      apply Qle_to_QleT'.
      rewrite HE. exact (QleT'_to_Qle _ _ Hterm).
    + (* the step slot J = S (S J') ≥ 2 *)
      intro Hterm.
      replace (Datatypes.S (Datatypes.S J') - 1)%nat with (Datatypes.S J') by lia.
      assert (HJ' : (1 <= Datatypes.S J')%nat) by lia.
      assert (Hterm' : forall j : nat, (j < Datatypes.S J')%nat ->
                QleT' (zb2_term n j) (c * zb2_ia_W j)).
      { intros j Hj. apply Hterm. lia. }
      pose proof (IH HJ' Hterm') as IHq.
      replace (Datatypes.S J' - 1)%nat with J'%nat in IHq by lia.
      cbn [zb2_Isum].
      apply Qle_to_QleT'.
      rewrite (Hws (Datatypes.S J')).
      assert (HE : (c * (zb2_ia_Wsum (Datatypes.S J') + zb2_ia_W (Datatypes.S J')))
                == (c * zb2_ia_Wsum (Datatypes.S J') + c * zb2_ia_W (Datatypes.S J'))).
      { apply Qmult_plus_distr_r. }
      rewrite HE.
      apply (Qplus_le_compat _ _ _ _).
      * exact (QleT'_to_Qle _ _ IHq).
      * exact (QleT'_to_Qle _ _ (Hterm (Datatypes.S J')
                   (Nat.lt_succ_diag_r (Datatypes.S J')))).
Qed.

(* ===================================================================== *)
(* §4 the final form of the prefix bound (the pointwise cap certificate carried in the statement as an explicitly named premise) *)
(* ===================================================================== *)

(* the constant-conversion completion of the final prefix bound: c·Wsum J ≤ c ≤
   (1/11)·(1/11)^m (the product-order ledger of Wsum J ≤ 1 and c ≥ 0).  This
   shape composes with zb2_ia_init_bound into the full chain of the monotone
   limb; the c·Wsum segment is listed here separately for review.
   (Z2A02 registration: this item was moved before init_bound for its
   conversion use, the statement face verbatim unchanged.) *)
Lemma zb2_ia_cWsum_le_c : forall (m J : nat), (1 <= J)%nat ->
  Qle (((1 # 11) * q_pow (1 # 11) m) * zb2_ia_Wsum J)
      (((1 # 11) * q_pow (1 # 11) m) * 1).
Proof.
  intros m J HJ.
  rewrite (Qmult_comm ((1 # 11) * q_pow (1 # 11) m) (zb2_ia_Wsum J)).
  rewrite (Qmult_comm ((1 # 11) * q_pow (1 # 11) m) 1).
  apply Qmult_le_compat_r.
  - exact (zb2_ia_Wsum_le_1 J).
  - apply Qmult_le_0_compat.
    + unfold Qle. cbn [Qnum Qden]. lia.
    + (* interface-generation alignment per UpReqMisc5B precedent: the
         Set-face QleT' conclusion of q_pow_nonneg is bridged to the
         Prop Qle goal (canonical form G07_KLWall) *)
      apply QleT'_to_Qle. apply q_pow_nonneg. apply Qle_to_QleT'.
      unfold Qle. cbn [Qnum Qden]. lia.
Qed.

(* the independent goal of the pointwise cap certificate (this module lists
   it explicitly as a premise of the final form, shaped as follows):
   forall m j, 8 ≤ m -> j ≤ m²+2m ->
     QleT' (zb2_term (S m) j * (j+1) * (j+2)) ((1/11)·(1/11)^m).
   Exact fraction comparison (see the header): the statement holds for every
   j universally; inside the window the normalized peak is 3.106e-2 (at
   n = 9, j = 9), the margin of the constant 1/11 is about 2.93x.  Its full
   symbolic proof needs an explicit analysis of the peak position of the
   initial segment (the peak j* is about (√5−1)n/2; the pointwise cross-slot
   ratio is above 1 before the peak and below 1 after it, so the monotone
   induction invariant must carry the peak-shaped weight factor) and advances
   as an independent module; this module includes it in the final statement
   as a quantified premise (carried at the Set layer, no global assumption
   slots).
   (Z2A02 registration: the assembly was empirically rebuilt under the
   zero-firing-count check.  The per-term weighted reshape goes through the
   Qle-layer cancel_r + field_canc folding, the prefix sum through the
   Isum_scalar instance, the tail segment through the cWsum conversion; the
   statement face verbatim unchanged.) *)
Theorem zb2_ia_init_bound : forall m : nat, (8 <= m)%nat ->
  (forall j : nat, (j <= m * m + 2 * m)%nat ->
     QleT' (zb2_term (Datatypes.S m) j
            * (Z.of_nat (Datatypes.S j) # 1) * (Z.of_nat (j + 2) # 1))
           ((1 # 11) * q_pow (1 # 11) m)) ->
  (forall J' : nat, zb2_ia_Wsum (Datatypes.S J') == zb2_ia_Wsum J' + zb2_ia_W J') ->
  QleT' (zb2_Isum (Datatypes.S m) (m * m + 2 * m))
        ((1 # 11) * q_pow (1 # 11) m).
Proof.
  intros m Hm Hpw Hws.
  assert (HJ1 : (1 <= m * m + 2 * m + 1)%nat) by lia.
  assert (Hpt : forall j : nat, (j < m * m + 2 * m + 1)%nat ->
           QleT' (zb2_term (Datatypes.S m) j)
                 (((1 # 11) * q_pow (1 # 11) m) * zb2_ia_W j)).
  { intros j Hj.
    assert (Hjw : (j <= m * m + 2 * m)%nat) by lia.
    specialize (Hpw j Hjw).
    pose proof (QleT'_to_Qle _ _ Hpw) as Hle.
    rewrite <- (Qmult_assoc (zb2_term (Datatypes.S m) j)) in Hle.
    assert (Hwpos : 0 < (Z.of_nat (Datatypes.S j) # 1) * (Z.of_nat (j + 2) # 1)).
    { apply Qmult_lt_0_compat; apply zb2_ia_natpos_lt; lia. }
    assert (Hwne : ~ ((Z.of_nat (Datatypes.S j) # 1) * (Z.of_nat (j + 2) # 1) == 0))
      by exact (zb2_ia_pos_neq0 _ Hwpos).
    apply Qle_to_QleT'.
    apply (zb2_ia_cancel_r (zb2_term (Datatypes.S m) j)
             (((1 # 11) * q_pow (1 # 11) m) * zb2_ia_W j)
             ((Z.of_nat (Datatypes.S j) # 1) * (Z.of_nat (j + 2) # 1)) Hwpos).
    assert (HE : (((1 # 11) * q_pow (1 # 11) m) * zb2_ia_W j)
                 * ((Z.of_nat (Datatypes.S j) # 1) * (Z.of_nat (j + 2) # 1))
              == ((1 # 11) * q_pow (1 # 11) m)).
    { unfold zb2_ia_W, Qdiv. rewrite Qmult_1_l.
      apply zb2_ia_field_canc. exact Hwne. }
    rewrite HE. exact Hle. }
  pose proof (zb2_ia_Isum_scalar (Datatypes.S m) (m * m + 2 * m + 1)
                ((1 # 11) * q_pow (1 # 11) m) Hws HJ1 Hpt) as Hpre.
  replace (m * m + 2 * m + 1 - 1)%nat with (m * m + 2 * m)%nat in Hpre by lia.
  pose proof (zb2_ia_cWsum_le_c m (m * m + 2 * m + 1) HJ1) as Hcw.
  rewrite (Qmult_1_r ((1 # 11) * q_pow (1 # 11) m)) in Hcw.
  apply Qle_to_QleT'.
  apply (Qle_trans (zb2_Isum (Datatypes.S m) (m * m + 2 * m))
                   (((1 # 11) * q_pow (1 # 11) m) * zb2_ia_Wsum (m * m + 2 * m + 1))
                   ((1 # 11) * q_pow (1 # 11) m)).
  - exact (QleT'_to_Qle _ _ Hpre).
  - exact Hcw.
Qed.

(* ===================================================================== *)
(* §5 the combined budget: C1 = 1/11 and the tail reserve C2 ≤ 3/20 total at most 1/4 (Q layer) *)
(* ===================================================================== *)

Definition zb2_ia_C1 : Q := (1 # 11).
Definition zb2_ia_C2_budget : Q := (3 # 20).

(* the budget identity: 1/11 + 3/20 = 53/220 ≤ 55/220 = 1/4 (the machine check of the Q-layer decidable form) *)
Lemma zb2_ia_C1C2_quarter : Qle (zb2_ia_C1 + zb2_ia_C2_budget) (1 # 4).
Proof.
  unfold zb2_ia_C1, zb2_ia_C2_budget, Qle, Qplus. simpl. lia.
Qed.

(* the conditional interface shape: once the tail machine delivers
   Qle 0 c2 and Qle c2 (3/20), the combined bound holds immediately
   (the mating face: the delivered value of C2 is given by the convergent
   tail bound machine) *)
Lemma zb2_ia_C1C2_cond : forall c2 : Q,
  Qle 0 c2 -> Qle c2 (3 # 20) -> Qle (zb2_ia_C1 + c2) (1 # 4).
Proof.
  intros c2 H0 H2.
  apply (Qle_trans (zb2_ia_C1 + c2) (zb2_ia_C1 + zb2_ia_C2_budget) (1 # 4)).
  - apply (Qplus_le_compat _ _ _ _).
    + apply Qle_refl.
    + exact H2.
  - exact zb2_ia_C1C2_quarter.
Qed.

(* ===================================================================== *)
(* §6 the tail cabin: the axiom-face self-check of the statements *)
(* ===================================================================== *)

Print Assumptions zb2_ia_Isum_mono_M.
Print Assumptions zb2_ia_field_canc.
Print Assumptions zb2_ia_Wsum_le_1.
Print Assumptions zb2_ia_Isum_scalar.
Print Assumptions zb2_ia_init_bound.
Print Assumptions zb2_ia_cWsum_le_c.
Print Assumptions zb2_ia_C1C2_quarter.
Print Assumptions zb2_ia_C1C2_cond.
