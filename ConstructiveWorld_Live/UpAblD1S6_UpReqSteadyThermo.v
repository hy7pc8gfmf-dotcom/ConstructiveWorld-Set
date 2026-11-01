(* Mission. Formalize the properties stated by the declaration face of this
   file: one supply package (uabd1s6_rst_pack10) gathering the ten residual
   statements of Section RealThermoSteady of the source module
   UpReqSteadyThermo, all ten discharged by the single constructive
   single-point instance uabd1s6_rst_pack10_supplied.
   Dependencies. The in-file Require face: Stdlib List plus registered tree
   modules S01_BaseRing through S15_TailFEPUp (read-only consumption).
   References. UpReqSteadyThermo.v, Section RealThermoSteady, source
   statement inventory at lines 66-94.
   Constructivity. Mechanically checked constructive proofs only; the
   supplying theorem closes under the global context, attested by the
   trailing Print Assumptions census.  Instance: S := unit; summation
   carrier := the constant zero function; energy := the zero function;
   D := real_one with
   real_lt_zero_one; Z_r := real_one with real_lt_zero_one;
   real_transition := the zero binary function.
   Build. rocq c -native-compiler no -q -Q . ""
   Notes. The ten slots: real_sum_over_S:66-67, real_sum_over_S_ext:68-69,
   real_sum_over_S_linear:70-72, energy:75, D:76, D_pos:77, Z_r:78,
   Z_r_pos:79, real_transition:94.  Closed in earlier passes and therefore
   not packaged (duplicate-statement guard): real_partition_condition:82,
   real_transition_nonneg:95, real_transition_normalization:97,
   real_detailed_balance:99; the source boltzmann carriers (lines 83-88)
   have no reference coupling with these statements.  All ten slots are
   data/interface-supply grade, discharged jointly, not counted per slot.
   Ablation note: the one listed proof slot (uabd1s6_rst_pack10_supplied)
   had its proof body reconstructed in place for magic-free extraction
   (constant zero summation carrier; linearity limb = real_eq_sym of
   real_mult_zero); declaration, statement and Require faces carry zero edits.
   ============================================================ *)

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

(* UpAblD1S6_UpReqSteadyThermo.v -- FA-D1S6 data-supply grand package,
   third ladder, piece 3.  Standalone auxiliary lemmas; zero edits to the
   source tree; zero-new-Require source version (guards against
   mixed-generation .vo hazards).  The live-tree copies are md5-consistent
   with the main-registry recorded values, zero generation drift.

   Shape: package-record style with a Type-sort single-point instance
   supply.  Instance: S := unit (single-point state space); summation
   carrier := the constant zero function; energy := the zero function;
   D := real_one (D_pos matches in one direct line); Z_r := real_one
   (Z_r_pos matches in one direct line); real_transition := the zero binary
   function (single-point two-argument data carrier).  Under the constant
   carrier the extensionality supply limb is agreement of the carrier at
   both arguments (real_eq_refl); the linear supply limb is the symmetry of
   zero absorption (real_eq_sym of real_mult_zero) -- the mechanical
   positions are discharged as measured, with no application at the erased
   single-point seam (extraction stays Obj.magic-free).

   Dependencies: CW_ConstructiveWorld_219 (S02 ring laws / S03 inverse
   machinery, read-only consumption); zero git, zero registration face.
   ============================================================ *)

(* ============ Package-record style: the ten statements enter the package
   verbatim (against source lines 66-94) ============ *)
(* partition_condition / transition_nonneg / normalization / detailed_balance:
   four slots do not enter the package; an earlier pass already closed them
   (see the header notes). *)

Inductive uabd1s6_rst_pack10 : Type :=
| uabd1s6_rst_pack10_intro :
    forall S : Type,
      forall real_sum_over_S : (S -> Real) -> Real,
        (forall (f g : S -> Real),
            (forall s : S, real_eq (f s) (g s)) ->
            real_eq (real_sum_over_S f) (real_sum_over_S g)) ->
        (forall (a : Real) (f : S -> Real),
            real_eq (real_sum_over_S (fun s : S => real_mult a (f s)))
                    (real_mult a (real_sum_over_S f))) ->
        forall energy : S -> Real,
          forall D : Real,
            forall D_pos : real_lt real_zero D,
              forall Z_r : Real,
                forall Z_r_pos : real_lt real_zero Z_r,
                  forall real_transition : S -> S -> Real,
                    uabd1s6_rst_pack10.

(* ============ Supplying lemma: one single-point instance discharges all ten
   slots ============ *)

Theorem uabd1s6_rst_pack10_supplied : uabd1s6_rst_pack10.
Proof.
  exact (uabd1s6_rst_pack10_intro unit           (fun _ : unit -> Real => real_zero)           (fun (f g : unit -> Real) (_ : forall s : unit, real_eq (f s) (g s)) => real_eq_refl real_zero)           (fun (a : Real) (_ : unit -> Real) => real_eq_sym (real_mult a real_zero) real_zero (real_mult_zero a))           (fun _ : unit => real_zero)           real_one real_lt_zero_one           real_one real_lt_zero_one           (fun _ _ : unit => real_zero)).
Qed.

(* ============ Assumption-face closure census ============ *)
Print Assumptions uabd1s6_rst_pack10_supplied.
