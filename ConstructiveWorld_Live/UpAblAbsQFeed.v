(* ConstructiveWorld-Set -- Q-layer corollary feed for absolute-value triangle inequalities. *)

(** * UpAblAbsQFeed: Set-level triangle bounds for [Qabs] over the rationals.

    Mission.  The triangle inequality for absolute value and its corollaries
      on [Q], carried on the [Set] order carriers [QleT'] and [QltT]:
      [uaq_abs_triangle_plus] bounds [Qabs (a + b)] and the subtraction
      form [uaq_abs_triangle_minus] bounds [Qabs (a - b)] by
      [Qabs a + Qabs b]; the reverse form [uaq_abs_triangle_reverse_leT]
      bounds [Qabs a - Qabs b] by [Qabs (a - b)]; [uaq_abs_abs_diff_le]
      and its strict companion [uaq_abs_abs_diff_ltT] bound the double
      difference [Qabs (Qabs a - Qabs b)]; [uaq_qfloor_abs_margin] carries
      the unit fraction [1 / (N e + 1)] past [Qabs]; [uaq_abs_nonneg]
      states [0 <= Qabs x].

    Dependencies.  Stdlib [List], [QArith.QArith], [QArith.Qabs], [QArith.Qring],
      [Lia], [Lqa].  Requires [S01_BaseRing] through [S06_DiffSamplingGibbs]
      and the sibling [UpAblAbsSumLeB2] of this development.

    References.  This development, UpAblAbsQFeed.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" UpAblAbsQFeed.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 000160bc]. *)
From Stdlib Require Import List.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qring.
From Stdlib Require Import Lia.
From Stdlib Require Import Lqa.
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
Require Import UpAblAbsSumLeB2.

(* ============================================================ *)
(* Part 0. Signature audit of the dependency interface (a signature drift fails compilation). *)
(* ============================================================ *)

Check QltT. Check QleT'.
Check Qle_to_QleT'. Check QleT'_to_Qle. Check qeq_le.
Check qltT_eq_compat_l. Check qleT'_ltT_ltT. Check qabs_nonnegT.
Check Qabs_triangle. Check Qabs_triangle_reverse. Check Qabs_pos.
Check Qabs_opp. Check Qabs_wd. Check Qabs_Qle_condition.
Check Qopp_comp. Check Qopp_le_compat. Check Qeq_sym.
Check Qle_trans. Check Qminus.
Check uabS4b_arch_N. Check uabS4b_null_lt. Check uabS4b_null_nonneg.

(* ============================================================ *)
(* Part A. The plus-form triangle family for the S10 use sites. *)
(* ============================================================ *)

(* A.1 The plus-form triangle, stated exactly in the shape used at the four
   use sites of S10_KVQuantTrig.  It follows directly from the stdlib lemma
   [Qabs_triangle] transported by [Qle_to_QleT'], with no further proof
   steps; the module keeps this statement standing in Set-level form as
   part of the Q-world statement face. *)
Corollary uaq_abs_triangle_plus : forall a b : Q,
  QleT' (Qabs (a + b)) (Qabs a + Qabs b).
Proof.
  intros a b. apply Qle_to_QleT'. apply Qabs_triangle.
Qed.

(* A.2 The subtraction form stated directly.  The two use sites in
   S10_KVQuantTrig normalize into the plus form by ring rewriting before
   applying the triangle inequality; the subtraction form stated here
   absorbs that normalization, so each use site is spared the rewriting
   step. *)
Corollary uaq_abs_triangle_minus : forall a b : Q,
  QleT' (Qabs (a - b)) (Qabs a + Qabs b).
Proof.
  intros a b. apply Qle_to_QleT'.
  assert (Hm : a - b == a + Qopp b) by (unfold Qminus; ring).
  assert (Ho : Qabs (Qopp b) == Qabs b) by apply Qabs_opp.
  apply (Qle_trans _ (Qabs (a + Qopp b)) _).
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qabs_wd. exact Hm.
  - apply (Qle_trans _ (Qabs a + Qabs (Qopp b)) _).
    + apply Qabs_triangle.
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. rewrite Ho. reflexivity.
Qed.

(* A.3 The bare reverse form, verbatim in the stdlib statement face; it is
   the direct component for both branches at the S08 use sites. *)
Corollary uaq_abs_triangle_reverse_leT : forall a b : Q,
  QleT' (Qabs a - Qabs b) (Qabs (a - b)).
Proof.
  intros a b. apply Qle_to_QleT'. apply Qabs_triangle_reverse.
Qed.

(* ============================================================ *)
(* Part B. The double-difference statements for S08. *)
(* ============================================================ *)

(* B.1 The double-difference bound [Qabs (Qabs a - Qabs b) <= Qabs (a - b)],
   corresponding to the double-difference statement of S08_RealMainlineDPO
   whose use sites inline both branches through [Qabs_Qle_condition]; this
   module gathers the argument into one standing statement.  Proof: the
   [Qopp] branch transports by [Qabs_opp], continues in the reversed order
   by [Qopp_le_compat] and normalizes the difference by ring under
   [Qminus]; the forward branch is [Qabs_triangle_reverse] directly. *)
Theorem uaq_abs_abs_diff_le : forall a b : Q,
  QleT' (Qabs (Qabs a - Qabs b)) (Qabs (a - b)).
Proof.
  intros a b. apply Qle_to_QleT'.
  assert (Hrev : Qabs b - Qabs a <= Qabs (b - a)) by apply Qabs_triangle_reverse.
  assert (Heq : Qabs (b - a) == Qabs (a - b)).
  { apply (Qeq_trans (Qabs (b - a)) (Qabs (Qopp (a - b))) (Qabs (a - b))).
    - apply Qabs_wd. unfold Qminus. ring.
    - apply Qabs_opp. }
  apply (proj2 (Qabs_Qle_condition (Qabs a - Qabs b) (Qabs (a - b)))).
  split.
  - (* the [Qopp] branch of [Qabs_Qle_condition]: [Heq] transports the
       right side of [Hrev] to [Qabs (a - b)], [Qopp_le_compat] reverses
       the sign preserving the order, and the difference identity
       [Qopp (x - y) == y - x] closes the goal once [Qminus] is
       unfolded *)
    rewrite Heq in Hrev.
    apply (Qle_trans _ (Qopp (Qabs b - Qabs a))).
    + apply Qopp_le_compat. exact Hrev.
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qminus. ring.
  - (* the forward branch: [Qabs a - Qabs b <= Qabs (a - b)] *)
    exact (Qabs_triangle_reverse a b).
Qed.

(* B.2 The strict-margin version through the conversion layer: a tail bound
   [e] for [Qabs] transports directly to the double difference, giving the
   [QltT]-face statement used by the local difference chains of
   S10_KVQuantTrig and at the tail-bound use sites of S08.  The order
   reasoning stays on the [Set] layer throughout, via the conversion
   [qleT'_ltT_ltT] from a left [QleT'] to a right [QltT]. *)
Corollary uaq_abs_abs_diff_ltT : forall a b e : Q,
  QltT (Qabs (a - b)) e -> QltT (Qabs (Qabs a - Qabs b)) e.
Proof.
  intros a b e Hab.
  exact (qleT'_ltT_ltT _ _ _ (uaq_abs_abs_diff_le a b) Hab).
Qed.

(* ============================================================ *)
(* Part C. Link to the Qfloor lineage: the S4B unit-fraction certificate under [Qabs]. *)
(* ============================================================ *)

(* C.1 The [Qabs]-shaped tail-margin certificate: the unit fraction
   [1/(N(e)+1)] attached to the archimedean index [uabS4b_arch_N] of S4B
   passes [Qabs] unchanged, so it carries the margin when a Q-world Cauchy
   chain states its tail bound with [Qabs]; a direct application of the
   lineage module [UpAblAbsSumLeB2]. *)
Theorem uaq_qfloor_abs_margin : forall e : Q, QltT 0 e ->
  QltT (Qabs (1#(Pos.of_succ_nat (uabS4b_arch_N e)))) e.
Proof.
  intros e He.
  assert (Hpos : Qle 0 (1#(Pos.of_succ_nat (uabS4b_arch_N e))))
    by apply uabS4b_null_nonneg.
  assert (Habs : Qabs (1#(Pos.of_succ_nat (uabS4b_arch_N e)))
                 == 1#(Pos.of_succ_nat (uabS4b_arch_N e)))
    by (apply Qabs_pos; exact Hpos).
  apply (qltT_eq_compat_l (1#(Pos.of_succ_nat (uabS4b_arch_N e)))
                          (Qabs (1#(Pos.of_succ_nat (uabS4b_arch_N e))))
                          e (qeq_imp_qeqT _ _ (Qeq_sym _ _ Habs))).
  exact (uabS4b_null_lt e He).
Qed.

(* C.2 The nonnegativity form [0 <= Qabs x] carried on the [Set] layer, as
   used in S10_KVQuantTrig; it keeps the S02 statement [qabs_nonnegT]
   standing in the same shape. *)
Corollary uaq_abs_nonneg : forall x : Q, QleT' 0 (Qabs x).
Proof. intros x. apply qabs_nonnegT. Qed.

(* ============================================================ *)
(* Assumption audit: the whole module is closed, with no external unproved assumptions. *)
(* ============================================================ *)

Print Assumptions uaq_abs_triangle_plus.
Print Assumptions uaq_abs_triangle_minus.
Print Assumptions uaq_abs_triangle_reverse_leT.
Print Assumptions uaq_abs_abs_diff_le.
Print Assumptions uaq_abs_abs_diff_ltT.
Print Assumptions uaq_qfloor_abs_margin.
Print Assumptions uaq_abs_nonneg.
