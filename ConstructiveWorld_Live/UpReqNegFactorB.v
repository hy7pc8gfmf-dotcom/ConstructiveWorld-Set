(* ConstructiveWorld-Set -- order reversal of multiplication by negative factors for the boolean consistent order. *)

(** * UpReqNegFactorB: order reversal of [real_le_b] multiplication by a non-positive or strictly negative factor.

    Mission.  For the boolean consistent order [real_le_b] this file derives
      the factor-sign reversal family: [real_le_b a b] with a non-positive
      factor certificate gives [real_le_b (real_mult b c) (real_mult a c)]
      ([t27_le_b_mult_r_nonpos_or]; strict variant [t27_le_b_mult_r_negstrict],
      opposite-factor core [t27_le_b_mult_r_nonpos_opp]; commuted-factor form
      [t27_le_b_mult_l_nonpos_or]); [t27_le_nonpos_to_nonneg_opp] turns
      [real_le c real_zero] into [real_le real_zero (real_opp c)].

    Dependencies.  Requires [S01_BaseRing], [S02_CauchyComplete],
      [S03_QExp], [S04_RealExpLogConv], [S05_AlignmentGRPO],
      [S06_DiffSamplingGibbs], [S07_RealSetoidExpLog], [S08_RealMainlineDPO],
      [S09_EntropyReal], [S10_KVQuantTrig], [S11_TP3B5], [S12_B5RecycleSF],
      [S13_NLiveAudit], [S14_B5BatchBlock], [S15_TailFEPUp], [UpRealLeB],
      [UpRealLeB3], [UpReqPowMonoBridge] of this development.

    References.  This development, UpReqNegFactorB.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" UpReqNegFactorB.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 00015ff4]. *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
Require Import S14_B5BatchBlock.
Require Import S15_TailFEPUp.
Require Import UpRealLeB.
Require Import UpRealLeB3.
Require Import UpReqPowMonoBridge.

(* ============================================================ *)
(*  Section 1.  Certificate bridge for a non-positive factor: the Or-form     *)
(*  premise [real_le c real_zero] yields [real_le real_zero (real_opp c)].    *)
(*  Negation reverses the order ([real_opp_le_compat]); normalization at      *)
(*  negative zero ([real_opp_zero]) performs the change of form.  This is     *)
(*  the negative-sign counterpart of the positive-sign face's one-way         *)
(*  Or-to-B certificate bridge [x3d_le_b_mult_r_nonneg_or].                   *)
(* ============================================================ *)
Lemma t27_le_nonpos_to_nonneg_opp : forall c : Real,
  real_le c real_zero -> real_le real_zero (real_opp c).
Proof.
  intros c Hc.
  exact (RealSetoid.real_le_id_l real_zero (real_opp real_zero)           (real_opp c)           (real_eq_sym (real_opp real_zero) real_zero real_opp_zero)           (real_opp_le_compat c real_zero Hc)).
Qed.

(* ============================================================ *)
(*  Section 2.  Conjugate core: the Or-form premise                           *)
(*  [real_le real_zero (real_opp c)] yields                                   *)
(*  [real_le_b (real_mult b c) (real_mult a c)].  Chain: order preservation   *)
(*  applied at the negated factor (Hrev); order reversal under negation for   *)
(*  [real_le_b] (Hflip), the reversal step supplied by [leb3_le_b_opp_rev];   *)
(*  transport along the pointwise equalities HoppA/HoppB given by             *)
(*  [real_opp_mult] together with the involution [real_opp_opp]; double       *)
(*  transport through [leb3_le_b_eq_l] and [leb3_le_b_eq_r] concludes.        *)
(* ============================================================ *)
Lemma t27_le_b_mult_r_nonpos_opp : forall a b c : Real,
  real_le_b a b -> real_le real_zero (real_opp c) ->
  real_le_b (real_mult b c) (real_mult a c).
Proof.
  intros a b c H Hc0.
  (* order preservation transfers to the conjugate position with the factor    *)
  (* negated: [real_le_b (real_mult a (real_opp c)) (real_mult b (real_opp c))] *)
  assert (Hrev : real_le_b (real_mult a (real_opp c))
                           (real_mult b (real_opp c)))
    by exact (x3d_le_b_mult_r_nonneg_or a b (real_opp c) H Hc0).
  (* negation reverses [real_le_b] on the negated products, giving the flipped  *)
  (* order [real_le_b (real_opp (real_mult b (real_opp c))) (real_opp (real_mult a (real_opp c)))] *)
  assert (Hflip : real_le_b
                    (real_opp (real_mult b (real_opp c)))
                    (real_opp (real_mult a (real_opp c))))
    by exact (leb3_le_b_opp_rev (real_mult a (real_opp c))
                                (real_mult b (real_opp c)) Hrev).
  (* change of form at the right end point: negation moves into the product and *)
  (* the double negation normalizes, giving [real_eq (real_opp (real_mult a (real_opp c))) (real_mult a c)] *)
  assert (HoppA : real_eq (real_opp (real_mult a (real_opp c)))
                          (real_mult a c)).
  { apply (real_eq_trans _ (real_mult a (real_opp (real_opp c))) _).
    - exact (real_opp_mult a (real_opp c)).
    - apply (RealSetoid.real_eq_mult_compat a
               (real_opp (real_opp c)) a c).
      + apply real_eq_refl.
      + exact (real_opp_opp c). }
  (* change of form at the left end point, by the same computation:             *)
  (* [real_eq (real_opp (real_mult b (real_opp c))) (real_mult b c)] *)
  assert (HoppB : real_eq (real_opp (real_mult b (real_opp c)))
                          (real_mult b c)).
  { apply (real_eq_trans _ (real_mult b (real_opp (real_opp c))) _).
    - exact (real_opp_mult b (real_opp c)).
    - apply (RealSetoid.real_eq_mult_compat b
               (real_opp (real_opp c)) b c).
      + apply real_eq_refl.
      + exact (real_opp_opp c). }
  (* transport at both end points through [leb3_le_b_eq_l] and [leb3_le_b_eq_r] *)
  (* concludes [real_le_b (real_mult b c) (real_mult a c)] *)
  exact (leb3_le_b_eq_r (real_mult b c)
           (real_opp (real_mult a (real_opp c))) (real_mult a c)
           (leb3_le_b_eq_l (real_opp (real_mult b (real_opp c)))
              (real_mult b c)
              (real_opp (real_mult a (real_opp c))) HoppB Hflip)
           HoppA).
Qed.

(* ============================================================ *)
(*  Section 3.  Main statement, carried verbatim: [real_le_b a b] together    *)
(*  with [real_le c real_zero] gives [real_le_b (real_mult b c)               *)
(*  (real_mult a c)].  The Section 1 bridge plugs into the conjugate core.    *)
(*  The argument positions line up one to one with                            *)
(*  [x3d_le_b_mult_r_nonneg_or]:                                              *)
(*  the certificate [real_le c real_zero] takes the place of                  *)
(*  [real_le real_zero c], and the conclusion direction reverses.             *)
(* ============================================================ *)
Lemma t27_le_b_mult_r_nonpos_or : forall a b c : Real,
  real_le_b a b -> real_le c real_zero ->
  real_le_b (real_mult b c) (real_mult a c).
Proof.
  intros a b c H Hc.
  apply t27_le_b_mult_r_nonpos_opp.
  - exact H.
  - exact (t27_le_nonpos_to_nonneg_opp c Hc).
Qed.

(* ============================================================ *)
(*  Section 4.  Left-factor variant: [real_le_b (real_mult c b)               *)
(*  (real_mult c a)].  Commuting both products transports the Section 3       *)
(*  statement across [real_mult_comm].  This is the negative-sign             *)
(*  counterpart of the positive-sign face's left-factor statement.            *)
(* ============================================================ *)
Lemma t27_le_b_mult_l_nonpos_or : forall a b c : Real,
  real_le_b a b -> real_le c real_zero ->
  real_le_b (real_mult c b) (real_mult c a).
Proof.
  intros a b c H Hc.
  apply (leb3_le_b_eq_l (real_mult b c) (real_mult c b) (real_mult c a)).
  - apply real_mult_comm.
  - apply (leb3_le_b_eq_r (real_mult b c) (real_mult a c) (real_mult c a)).
    + exact (t27_le_b_mult_r_nonpos_or a b c H Hc).
    + apply real_mult_comm.
Qed.

(* ============================================================ *)
(*  Section 5.  Strictly negative factor: [real_lt c real_zero] gives         *)
(*  [real_le_b (real_mult b c) (real_mult a c)].  [real_lt_le_iff_req]        *)
(*  converts the strict premise to Or form (its inl branch), after which the  *)
(*  Section 3 statement applies in one step.  This is the negative-sign       *)
(*  counterpart of the positive-sign face's strictly-positive comparison      *)
(*  form.                                                                     *)
(* ============================================================ *)
Lemma t27_le_b_mult_r_negstrict : forall a b c : Real,
  real_le_b a b -> real_lt c real_zero ->
  real_le_b (real_mult b c) (real_mult a c).
Proof.
  intros a b c H Hc.
  apply t27_le_b_mult_r_nonpos_or.
  - exact H.
  - exact (RealSetoid.real_lt_le_iff_req c real_zero (inl Hc)).
Qed.

(* ============================================================ *)
(*  Section 6.  Assumption audit: the compile log carries the evidence for    *)
(*  every statement (Closed under the global context).                        *)
(* ============================================================ *)

Print Assumptions t27_le_nonpos_to_nonneg_opp.
Print Assumptions t27_le_b_mult_r_nonpos_opp.
Print Assumptions t27_le_b_mult_r_nonpos_or.
Print Assumptions t27_le_b_mult_l_nonpos_or.
Print Assumptions t27_le_b_mult_r_negstrict.

(* ============================================================ *)
(*  Epilogue, symmetry record: the contravariant negative-sign face (the      *)
(*  main statement of Section 3) and the order-preserving positive-sign face  *)
(*  ([x3d_le_b_mult_r_nonneg_or]) together form the complete two-face pair    *)
(*  for multiplication under Or-shaped factor certificates: given a sign      *)
(*  certificate on the factor, whether multiplication preserves or reverses   *)
(*  the order is determined by the factor's sign alone, and the two faces     *)
(*  are conjugate copies of each other under negation.                        *)
(*  Epilogue, scope record: a negative-side statement for a factor known only *)
(*  through [real_le_b] itself, with no Or-shaped sign certificate, mirrors   *)
(*  the positive-sign face's corresponding premise-carrying form; the two     *)
(*  faces state their side conditions symmetrically, and no statement is      *)
(*  asserted beyond the strength of its certificate.                          *)
(* ============================================================ *)
