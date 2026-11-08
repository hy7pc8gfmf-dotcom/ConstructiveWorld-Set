(* ConstructiveWorld-Set — concrete instances of the alignment-layer logarithm and reciprocal lemmas. *)

(** * UpAblT5_S05_AlignmentGRPO: concrete-instance restatements of two
       S05_AlignmentGRPO lemmas.

    Mission.  Two statements of the source module restated with
    one-step direct-reference proof bodies: [abl_S05_inv_pos_lt_contra]
    (strict antitone reciprocals in the abstract [RI] layer) and
    [abl_S05_log_lt_mono] (strict monotonicity of the logarithm, at the
    concrete [Real] layer).  Both bodies coincide verbatim with the
    current originals apart from the two provenance-block adjustments
    (supplier closure and [Let] qualification).

    Dependencies.  Requires [S01_BaseRing] through [S15_TailFEPUp],
    [InvPosLtCompat], [G05_LogSmall] of this development;
    [S05_AlignmentGRPO] is a read-only source module (tree untouched,
    no extra [Require]).

    References.  This development, UpAblT5_S05_AlignmentGRPO.v, the
    baseline module in ConstructiveWorld-Main whose statement names are
    carried over here verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by
      [Set] (decidable Q-carriers [QltT]/[QleT']/[QeqT], [Id],
      [NatLe]); statements extract with [Obj.magic] = 0 and no
      erasure; [coqchk] reports [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . ""
      UpAblT5_S05_AlignmentGRPO.v] compiles cleanly (exit 0); the first
      eight bytes of the artifact are [436f7121 00015ff4]. *)

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
Require Import InvPosLtCompat.
Require Import G05_LogSmall.

(* ============================================================ *)
(* Source provenance (S05_AlignmentGRPO.v, read-only; the source tree   *)
(* is untouched).                                                       *)
(*   (1) L2303 [inv_pos_lt_contra] — direct substitution in the         *)
(*   abstract [RI] layer (supply grade N1); the discharging lemma is    *)
(*   [ipl_inv_pos_lt_compat] at InvPosLtCompat.v:68 (same layer, same   *)
(*   shape; the source differs only in name, the argument group in the  *)
(*   (a b) parenthesized form, statement verbatim identical);           *)
(*   dependency slot S05:2330 (the [sigmoid_strict_inc] construction).  *)
(*   (2) L2314 [log_lt_mono] — Real-layer instance supply (grade N3);   *)
(*   the G05 package member cited by the original is outside this       *)
(*   compilation closure ([G05_LogSmall] lineage difference), so the    *)
(*   active supplier is [real_log_lt_mono] at S07:6663 (the [cw_log]    *)
(*   face converts via the transparent definition [real_log] at         *)
(*   S07:8011; same layer, same face, statement verbatim identical);    *)
(*   dependency slot S05:2373 (the third step of                        *)
(*   [sigmoid_strict_inc]).                                             *)
(*   The six [Let]s of the abstract-RI section are fully qualified by   *)
(*   the base member name [S01_BaseRing] (the G05 notation face shadows *)
(*   the S01 projection names — a lineage difference).  Discipline:     *)
(*   purely constructive; statement face entirely at the Set layer;     *)
(*   axiom face zero additions; the [abl_] prefix prevents name clashes *)
(*   within this file.                                                  *)
(* ============================================================ *)

(* ################ (1) inv_pos_lt_contra (argument shape carried over verbatim
   from the source L2303-2305) ################ *)
(* Source section: Section Alignment (from L24), abstract RI layer; the
   copy section matches the InvPosLtCompat shape. *)
Section AblS05Alignment.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.

Let R := @S01_BaseRing.R RI.
Let zero := @S01_BaseRing.zero RI.
Let one := @S01_BaseRing.one RI.
Let mult := @S01_BaseRing.mult RI.
Let inv_pos := @S01_BaseRing.inv_pos RI.
Let lt := @S01_BaseRing.lt RI.

Theorem abl_S05_inv_pos_lt_contra :
  forall (a b : R) (Ha : lt zero a) (Hb : lt zero b),
    lt a b -> lt (inv_pos b Hb) (inv_pos a Ha).
Proof.
  intros a b Ha Hb Hab.
  exact (ipl_inv_pos_lt_compat a b Ha Hb Hab).
Qed.

End AblS05Alignment.

(* ################ (2) log_lt_mono (argument shape carried over verbatim from
   the source L2314-2315; Real-layer instance form) ##################### *)
(* The source statement is the abstract RI-layer total-log form (Section
   Alignment); the instance supply takes the active Real-layer real_log
   witness form (direct reference to S07 real_log_lt_mono; the cw_log
   conclusion face differs only by transparent definitional conversion;
   the statement face is verbatim identical). *)
Theorem abl_S05_log_lt_mono : forall (a b : Real) (Ha : real_lt real_zero a)
    (Hb : real_lt real_zero b),
  real_lt a b -> real_lt (real_log a Ha) (real_log b Hb).
Proof.
  intros a b Ha Hb Hlt.
  exact (real_log_lt_mono a b Ha Hb Hlt).
Qed.

(* ---- Assumption self-check section (one Print Assumptions per statement) ---- *)
Print Assumptions abl_S05_inv_pos_lt_contra.
Print Assumptions abl_S05_log_lt_mono.
