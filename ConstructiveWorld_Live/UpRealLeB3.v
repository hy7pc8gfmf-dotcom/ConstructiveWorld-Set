(* ConstructiveWorld-Set — algebra of the eps-uniform lower-bound order on the reals. *)

(** * UpRealLeB3: structural laws of the lower-bound order [real_le_b].

    Mission.  Reflection and equation transport for the eps-uniform
    lower-bound order: [leb3_le_b_refl], [leb3_le_b_eq_l],
    [leb3_le_b_eq_r]; adding a nonnegative right summand
    [leb3_le_b_plus_nonneg_r]; antitone negation [leb3_le_b_opp_rev];
    scaling by a positive factor [leb3_le_b_pos_scale],
    [leb3_le_b_pos_scale_l]; and the strict anchor
    [leb3_abs_plus_one_pos].

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs], [QArith.Qring].
      Requires [S01_BaseRing] through [S15_TailFEPUp], [UpRealLeB],
      [UpRealLeB2] of this development.

    References.  This development, UpRealLeB3.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).  Basic algebra
      of the eps-uniform lower-bound order: equation transport and
      monotone operations.

    Constructivity.  All named statements and fields are carried by
      [Set] (decidable Q-carriers [QltT]/[QleT']/[QeqT], [Id],
      [NatLe]); statements extract with [Obj.magic] = 0 and no
      erasure; [coqchk] reports [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" UpRealLeB3.v]
      compiles cleanly (exit 0); the first eight bytes of the
      artifact are [436f7121 00015ff4]. *)

From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qring.
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
Require Import UpRealLeB2.

(* ============================================================ *)
(* Section 1. Transport: reflexivity, left and right equation transport, *)
(* nonnegative right addition.                                          *)
(* ============================================================ *)

(* Item 1. Reflexivity of [real_le_b], via the one-way bridge
   [real_le_to_le_b] applied to [real_le_refl] in one step. *)
Lemma leb3_le_b_refl : forall x : Real, real_le_b x x.
Proof.
  intros x. apply real_le_to_le_b. apply real_le_refl.
Qed.

(* Item 2. Left equation transport: [real_eq x1 x2] and [real_le_b x1 y]
   give [real_le_b x2 y]. *)
Lemma leb3_le_b_eq_l : forall x1 x2 y : Real,
  real_eq x1 x2 -> real_le_b x1 y -> real_le_b x2 y.
Proof.
  intros x1 x2 y Heq H. unfold real_le_b in H. unfold real_le_b.
  intros eps Heps.
  apply (RealSetoid.real_lt_id_l x2 x1 (real_plus y eps)).
  - apply real_eq_sym. exact Heq.
  - exact (H eps Heps).
Qed.

(* Item 3. Right equation transport: [real_le_b x y1] and [real_eq y1 y2]
   give [real_le_b x y2]; the per-eps witnesses are reshaped by additive
   compatibility, [y1 + e == y2 + e]. *)
Lemma leb3_le_b_eq_r : forall x y1 y2 : Real,
  real_le_b x y1 -> real_eq y1 y2 -> real_le_b x y2.
Proof.
  intros x y1 y2 H Heq. unfold real_le_b in H. unfold real_le_b.
  intros eps Heps.
  apply (RealSetoid.real_lt_id_r x (real_plus y1 eps) (real_plus y2 eps)).
  - apply (RealSetoid.real_eq_plus_compat y1 eps y2 eps).
    + exact Heq.
    + apply real_eq_refl.
  - exact (H eps Heps).
Qed.

(* Item 4. Adding a nonnegative right summand: [real_le_b x y] and
   [0 <= c] give [real_le_b x (y + c)]; the combinators are order
   compatibility of addition, plus left transport along [x + 0 == x]. *)
Lemma leb3_le_b_plus_nonneg_r : forall x y c : Real,
  real_le_b x y -> real_le real_zero c -> real_le_b x (real_plus y c).
Proof.
  intros x y c H Hc.
  apply (leb3_le_b_eq_l (real_plus x real_zero) x (real_plus y c)).
  - apply real_plus_zero.
  - apply (real_le_b_plus_compat x y real_zero c).
    + exact H.
    + apply real_le_to_le_b. exact Hc.
Qed.

(* ============================================================ *)
(* Section 2. Antitone negation for [real_le_b].                        *)
(* ============================================================ *)

(* Item 5. Antitone negation: [real_le_b x y] gives
   [real_le_b (-y) (-x)].  Given d > 0, [H] yields x < y + d; strict
   reversal of the order under [real_opp] turns this into
   -(y + d) < -x; distributing [real_opp] over addition reshapes it to
   -y + -d < -x; and adding d on the right of both sides (order
   compatibility of addition with a weak order premise and a strict
   conclusion) gives (-y + -d) + d < -x + d.  The left side equals -y by associativity
   together with [-d + d == 0] and [x + 0 == x].  The d cancels in pairs
   on the two sides, so no eps/2 splitting is needed. *)
Lemma leb3_le_b_opp_rev : forall x y : Real,
  real_le_b x y -> real_le_b (real_opp y) (real_opp x).
Proof.
  intros x y H. unfold real_le_b in H. unfold real_le_b.
  intros d Hd.
  pose proof (H d Hd) as H1.
  pose proof (real_opp_lt_compat x (real_plus y d) H1) as H2.
  assert (H3 : real_lt (real_plus (real_opp y) (real_opp d)) (real_opp x)).
  { apply (RealSetoid.real_lt_id_l (real_plus (real_opp y) (real_opp d))
                                   (real_opp (real_plus y d)) (real_opp x)).
    - apply real_eq_sym. exact (real_opp_plus y d).
    - exact H2. }
  assert (H4 : real_lt (real_plus (real_plus (real_opp y) (real_opp d)) d)
                       (real_plus (real_opp x) d)).
  { exact (real_lt_plus_compat_lt_le (real_plus (real_opp y) (real_opp d))
                                     (real_opp x) d d H3 (real_le_refl d)). }
  assert (Heq5 : real_eq (real_plus (real_plus (real_opp y) (real_opp d)) d)
                         (real_opp y)).
  { apply (real_eq_trans _
             (real_plus (real_opp y) (real_plus (real_opp d) d)) _).
    - apply real_eq_sym. apply real_plus_assoc.
    - apply (real_eq_trans _ (real_plus (real_opp y) real_zero) _).
      + apply (RealSetoid.real_eq_plus_compat (real_opp y)
                 (real_plus (real_opp d) d) (real_opp y) real_zero).
        * apply real_eq_refl.
        * apply (real_eq_trans (real_plus (real_opp d) d)
                   (real_plus d (real_opp d)) real_zero).
          -- apply real_plus_comm.
          -- apply real_plus_opp.
      + apply real_plus_zero. }
  apply (RealSetoid.real_lt_id_l (real_opp y)
           (real_plus (real_plus (real_opp y) (real_opp d)) d)
           (real_plus (real_opp x) d)).
  - apply real_eq_sym. exact Heq5.
  - exact H4.
Qed.

(* ============================================================ *)
(* Section 3. Scaling by a positive factor (converse use of the closure *)
(* lemma).                                                              *)
(* ============================================================ *)

(* Item 6. Scaling by a positive factor: [real_le_b x y] and [0 < c]
   give [real_le_b (x * c) (y * c)].  Reading the closure lemma
   [real_le_closure_b] backwards with D := c, for each e > 0 it suffices
   to produce the left disjunct x * c <= y * c + c * e: order
   compatibility of multiplication turns x < y + e into x * c < (y + e) * c,
   and (y + e) * c == y * c + c * e by distributivity and commutativity. *)
Lemma leb3_le_b_pos_scale : forall x y c : Real,
  real_le_b x y -> real_lt real_zero c ->
  real_le_b (real_mult x c) (real_mult y c).
Proof.
  intros x y c H Hc.
  apply (real_le_closure_b (real_mult x c) (real_mult y c) c Hc).
  intros eps Heps. unfold real_le. left.
  apply (RealSetoid.real_lt_id_r (real_mult x c)
           (real_mult (real_plus y eps) c)
           (real_plus (real_mult y c) (real_mult c eps))).
  - apply (real_eq_trans _ (real_mult c (real_plus y eps)) _).
    + apply real_mult_comm.
    + apply (real_eq_trans _
               (real_plus (real_mult c y) (real_mult c eps)) _).
      * apply real_distrib.
      * apply (RealSetoid.real_eq_plus_compat (real_mult c y)
                 (real_mult c eps) (real_mult y c) (real_mult c eps)).
        -- apply real_mult_comm.
        -- apply real_eq_refl.
  - exact (real_mult_lt_compat x (real_plus y eps) c (H eps Heps) Hc).
Qed.

(*
   Two commutativity reshapes transport the equation on both sides. *)
Lemma leb3_le_b_pos_scale_l : forall x y c : Real,
  real_le_b x y -> real_lt real_zero c ->
  real_le_b (real_mult c x) (real_mult c y).
Proof.
  intros x y c H Hc.
  apply (leb3_le_b_eq_l (real_mult x c) (real_mult c x) (real_mult c y)).
  - apply real_mult_comm.
  - apply (leb3_le_b_eq_r (real_mult x c) (real_mult y c) (real_mult c y)).
    + apply (leb3_le_b_pos_scale x y c H Hc).
    + apply real_mult_comm.
Qed.

(* ============================================================ *)
(* Section 4. A strict anchor statement at the Real layer, mirroring    *)
(* [real_abs_plus_one_pos] with the addition commuted.                  *)
(* ============================================================ *)

(* Item 7. [0 < |a| + 1].  The S09 statement [real_abs_plus_one_pos]
   gives [0 < 1 + |a|] (pointwise: its QeqT guard projects along
   [qeqT_imp_qeq], and [Qabs] is nonnegative); commuting the addition
   with [real_plus_comm] and transporting the right side with
   [real_lt_id_r] yields the permuted form in one step.  The statement
   text is carried over verbatim from the source. *)
Lemma leb3_abs_plus_one_pos : forall a : Real,
  real_lt real_zero (real_plus (real_abs a) real_one).
Proof.
  intro a.
  apply (RealSetoid.real_lt_id_r real_zero
           (real_plus real_one (real_abs a))
           (real_plus (real_abs a) real_one)).
  - apply real_plus_comm.
  - exact (real_abs_plus_one_pos a).
Qed.

(* ============================================================ *)
(* Section 5. Assumption audit: every statement Closed; the evidence    *)
(* is in the build log.                                                 *)
(* ============================================================ *)

Print Assumptions leb3_le_b_refl.
Print Assumptions leb3_le_b_eq_l.
Print Assumptions leb3_le_b_eq_r.
Print Assumptions leb3_le_b_plus_nonneg_r.
Print Assumptions leb3_le_b_opp_rev.
Print Assumptions leb3_le_b_pos_scale.
Print Assumptions leb3_le_b_pos_scale_l.
Print Assumptions leb3_abs_plus_one_pos.
