(* UpAblD1S16_UpReqMixTime.v -- data-supply pack for the MixTime residual      *)
(*   12-slot statement, supplied as a conditional form over arbitrary RI.      *)
(*                                                                             *)
(* Mission. Formalize the interface face of the residual 12-slot statement of  *)
(*   UpReqAttnMixTime as a Type-level inductive bundle uabd1s16_fmt_pack12:    *)
(*   for every old-layer interface instance RI it carries the two interface    *)
(*   slots SS : StateSpace RI and SO : SumOver RI SS plus the nine data slots  *)
(*   in source-declaration field order -- enum, enum_nonempty, temp and Delta  *)
(*   (both strictly positive), z, z_lb/z_ub (pointwise le (opp Delta) (z s s') *)
(*   and le (z s s') Delta) -- and supplies every data slot for arbitrary RI.  *)
(* Dependencies. Stdlib List; the declared Require face S01_BaseRing through   *)
(*   S15_TailFEPUp, all in-tree; the statements consume the S01 old-layer      *)
(*   RealInterfaceEnhanced and its StateSpace/SumOver/lt/le/zero/opp/one/      *)
(*   one_pos/szero projections plus lt_zero_opp/lt_le_iff; no Require of the   *)
(*   source module UpReqAttnMixTime and no import of RealInterfaceEnhancedMod  *)
(*   (its field names lt/le/zero/opp would shadow the same-name S01            *)
(*   projections); the reachability anchor cites the Setoid sister-class       *)
(*   instance as RealInterfaceEnhancedMod.RealEnhancedReal.                    *)
(* References. The pack mirrors the standard single-point data-supply form:    *)
(*   enum := cons szero nil, temp := Delta := one, z := the zero function;     *)
(*   the bounds opp one <= zero <= one follow from one_pos via lt_zero_opp     *)
(*   and lt_le_iff composed with the Or injection inl.                         *)
(* Constructivity. The carrier is the Type-level inductive uabd1s16_fmt_pack12;*)
(*   statements ride Context {RI : RealInterfaceEnhanced} with Local Existing  *)
(*   Instance RI_base and exit after End as universal conditional forms in RI. *)
(*   The assumption face is empty: Print Assumptions reports Closed under the  *)
(*   global context for all four stations. No concrete RI instance exists      *)
(*   in-tree (only the Setoid sister class), so the conditional form is honest.*)
(* Build. rocq c -native-compiler no -q -Q . "" UpAblD1S16_UpReqMixTime.v      *)
(*   (every compile wrapped by the thermal-guard protocol of the CI).          *)

From Stdlib Require Import List.
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
(* Note: RealInterfaceEnhancedMod is deliberately not imported -- its field    *)
(*   names (lt/le/zero/opp) would shadow the same-name S01 old-layer           *)
(*   projections, and bare names in this file must resolve to the S01          *)
(*   old-layer face; the reachability anchor cites the module by qualified     *)
(*   name (see the note at the anchor below).                                  *)

(* ======= Section 1: interface conditional form of the 12-slot statement ======= *)
(* (carried by the section Context, universal form after End)                    *)
(* Field order = source-declaration order: SS/SO are explicit constructor        *)
(*   parameters; the nine data slots correspond one-to-one. z_lb and z_ub are    *)
(*   pointwise statements (for all s s' : S), matching the pointwise obligations *)
(*   of the source module. Section instance note: Local Existing Instance        *)
(*   RI_base makes the type-class projections available inside the section;      *)
(*   after End the exit face quantifies RI explicitly, with no reliance on the   *)
(*   section-local implicit-instance mechanism.                                  *)

Section UabD1S16Fmt.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.

Inductive uabd1s16_fmt_pack12 : Type :=
| uabd1s16_fmt_pack12_intro :
    forall (SS : StateSpace RI) (SO : SumOver RI SS),
      forall (enum : list S),
        Not (Id enum nil) ->
        forall (temp : R),
          lt zero temp ->
          forall (Delta : R),
            lt zero Delta ->
            forall (z : S -> S -> R),
              (forall s s' : S, le (opp Delta) (z s s')) ->
              (forall s s' : S, le (z s s') Delta) ->
              uabd1s16_fmt_pack12.

(* ---- Enumeration nonemptiness supply (independent lemma: the constructors   *)
(*   of the single-point enumeration are disjoint).                            ---- *)
(* Note: the S01 unit equality Id is not the primitive equality, so                *)
(*   discriminate does not recognize it; the proof transports H along the          *)
(*   type-constant classifier nil => zero / cons => one (the S01 old-layer R)      *)
(*   by id_cong and closes by one_neq_zero.                                        *)

Lemma uabd1s16_fmt_enum_ne :
  forall SS : StateSpace RI, Not (Id (cons szero nil) nil).
Proof.
  intros SS H.
  exact (one_neq_zero
          (id_cong (fun l : list S =>
                      match l return R with
                      | nil => zero
                      | cons _ _ => one
                      end) H)).
Qed.

(* ---- Supply theorem: give the nine data fields for any old-layer interface  *)
(*   instance.                                                                 ---- *)

Theorem uabd1s16_fmt_pack12_supplied :
  forall (SS : StateSpace RI) (SO : SumOver RI SS), uabd1s16_fmt_pack12.
Proof.
  intros SS SO.
  exact (uabd1s16_fmt_pack12_intro SS SO
           (cons szero nil)
           (uabd1s16_fmt_enum_ne SS)
           one one_pos
           one one_pos
           (fun _ _ : S => zero)
           (fun (_ _ : S) =>
              lt_le_iff (opp one) zero (inl (lt_zero_opp one one_pos)))
           (fun (_ _ : S) => lt_le_iff zero one (inl one_pos))).
Qed.

End UabD1S16Fmt.

(* ======= Section 2: reachability anchor (named type-existence statement, ======= *)
(*   non-dependency module). RealEnhancedReal declares the type existence of the    *)
(*   concrete in-tree instance of the Setoid sister class (the req carrier layer);  *)
(*   no Setoid-to-RI backward conversion is registered in-tree and concrete         *)
(*   old-layer RI instances remain at zero, so the conditional form of this file    *)
(*   is the honest shape. Boundary note: this file does not construct a concrete    *)
(*   old-layer RI instance; the in-tree existence of such instances and the         *)
(*   availability of a Setoid-to-RI backward conversion are upstream matters,       *)
(*   outside this supply face.                                                      *)

Definition uabd1s16_fmt_anchor_setoid := RealInterfaceEnhancedMod.RealEnhancedReal.

Check uabd1s16_fmt_anchor_setoid.

(* ======= Section 3: post-End fully quantified form ======= *)
(* The global form explicitly quantifies RI, so downstream modules can take the  *)
(*   pack at any old-layer interface instance. Application face: downstream      *)
(*   modules of the MixTime residual 12-slot statement substitute slot by slot;  *)
(*   the nine data values are uniform over every RI instance, and the interface  *)
(*   trio is supplied by the caller.                                             *)

Theorem uabd1s16_fmt_pack12_supplied_global :
  forall (RI : RealInterfaceEnhanced) (SS : StateSpace RI) (SO : SumOver RI SS),
    @uabd1s16_fmt_pack12 RI.
Proof.
  intros RI SS SO.
  exact (uabd1s16_fmt_pack12_supplied (RI := RI) SS SO).
Qed.

(* ======= Section 4: assumption-face audit ======= *)

Print Assumptions uabd1s16_fmt_pack12_supplied.
Print Assumptions uabd1s16_fmt_pack12_supplied_global.
Print Assumptions uabd1s16_fmt_enum_ne.
Print Assumptions uabd1s16_fmt_anchor_setoid.
