(* ConstructiveWorld-Set -- tail entropy supply positivity certificates. *)

(** * abl_tail_pos_certs: one-instantiated positivity certificates for tail entropy supply.

    Mission.  Twelve certificate slots, each fixing a designated real to
      [one]: six Real-face statements [tspp_ems_t_star_pos_one] through
      [tspp_bbd_z_pos_one] asserting [real_lt real_zero real_one]; the
      generic interface statement [tspp_tsi_temperature_pos_one]; four setoid
      statements [tspp_pa04_rqg_t_pos_one] through [tspp_pa04_rfe_z_pos_one]; and
      the sum-zero translations [tspp_sum_zero_nonneg_slot_of_carrier_agree] and
      [tspp_sum_zero_nonneg_slot_bool_two].

    Dependencies.  Stdlib [List], [Extraction].  Requires [S01_BaseRing],
      [S02_CauchyComplete], [S03_QExp], [S04_RealExpLogConv],
      [S05_AlignmentGRPO], [S06_DiffSamplingGibbs], [S07_RealSetoidExpLog],
      [S08_RealMainlineDPO], [S09_EntropyReal], [S10_KVQuantTrig],
      [S11_TP3B5], [S12_B5RecycleSF], [S13_NLiveAudit], [S14_B5BatchBlock],
      [S15_TailFEPUp], [UpReqAlgebra], [UpReqDist], [UpReqSumD] of this development.

    References.  This development, abl_tail_pos_certs.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" abl_tail_pos_certs.v] compiles cleanly
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
Require Import UpReqSumD.
From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import Extraction.
Import RealInterfaceEnhancedMod.
(* Interface adaptation: the interface class in this tree is unparameterized; its carrier is
   the global Real (S07_RealSetoidExpLog.v:8075 zero-argument Class RealInterfaceEnhancedSetoid
   plus the global Instance RealEnhancedReal).  The parameterized binders
   forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R}. are removed from the statement
   faces; the carrier R is bound to the global Real and the used field names resolve through
   the concrete global twins below (the bindings the instance assigns), the world's own
   UpReqAlign3.v precedent spelled with the Abbreviation vernacular.  Statement names are
   unchanged apart from the dropped binder arguments. *)
Abbreviation R := Real.
Abbreviation req := real_eq.
Abbreviation le := real_le.
Abbreviation zero := real_zero.
Abbreviation lt := real_lt.
Abbreviation one := real_one.
Abbreviation one_pos := real_lt_zero_one.

(* ============================================================ *)
(* Duplication review (no repeated supply statements; whole-library         *)
(* grep):                                                                   *)
(*   (1) The six Real-face closed statements have the face real_lt          *)
(*     real_zero real_one, the same face as the in-service theorem          *)
(*     real_lt_zero_one (S07_RealSetoidExpLog.v:6967): once the slot value  *)
(*     is set to one, the slot statements take exactly this form, so these  *)
(*     six are named forwarders (no reproof, one exact citation each).      *)
(*     The in-service same-face precedent is p2t1_one_pos_lt                *)
(*     (UpAblP2T1_Cert.v:2301); the generic RI and RIS closed forms below   *)
(*     have no same-statement match in the whole library.                   *)
(*   (2) The two zero_nonneg translations differ in statement face from the *)
(*     sibling tsp_sumd_sum_zero_nonneg_full_bool, which states the         *)
(*     concrete sumd operator form (its conclusion is the sumd_sumf list    *)
(*     sum); this file states the abstract sumf slot form extended by a     *)
(*     carrier-agreement premise, the family pattern of the slot-form       *)
(*     input extensions; the generic en form also differs in statement      *)
(*     face from the sumd operator generic en form                          *)
(*     uabT1_rte_fsum_zero_nonneg.                                          *)
(*   (3) The coverage witness below restates, self-contained, the face of   *)
(*     the sibling tsp_bool_enum_sumd_in_witness: the target modules are    *)
(*     not required here, so the two-point coverage witness is rebuilt      *)
(*     locally.                                                             *)
(*   (4) No reserved position is touched: BBD :98 partition and             *)
(*     :100/:102 sup, PA_04 :886/:910/:915/:1354/:1356/:1370/:1377,         *)
(*     tmw :50 and :65-71/:74-76, and the slc/ToyR_04 sumpos with the       *)
(*     EMS/EmsC real_sum_pos_preserved statements all stay untouched.       *)
(* ============================================================ *)

(* ============================================================ *)
(* Section 1.  Six closed Real-face statements (targets 1-4 and 8-9;        *)
(*   one instantiation, a distinct name per target).                        *)
(* ============================================================ *)

(* ---- Target 1: ToyR_EntropyMonoSplitInst.v:135.                         ---- *)
(* ----   (Section EntropyMonoSplitInst; the host section variable S lives  ---- *)
(* ----   in Type, and that account stays with the full chain: this         ---- *)
(* ----   slot-level closed form consumes only the T value certificate      ---- *)
(* ----   position and does not touch the S carrier.)                       ---- *)
Theorem tspp_ems_t_star_pos_one : real_lt real_zero real_one.
Proof.
  exact real_lt_zero_one.
Qed.

(* ---- Target 2: UpAblP6_EntropyMonoSplit_C.v:66 (the same host statement ---- *)
(* ----   fills a second target verbatim; each target keeps its own name). ---- *)
Theorem tspp_emsc_t_star_pos_one : real_lt real_zero real_one.
Proof.
  exact real_lt_zero_one.
Qed.

(* ---- Target 3: PA_ToyR_SecondLawConsume.v:128                           ---- *)
Theorem tspp_slc_t_pos_one : real_lt real_zero real_one.
Proof.
  exact real_lt_zero_one.
Qed.

(* ---- Target 4: Arch_ToyR_04.v:90 (the same host statement fills a       ---- *)
(* ----   second target verbatim; each target keeps its own name).         ---- *)
Theorem tspp_toyr04_t_pos_one : real_lt real_zero real_one.
Proof.
  exact real_lt_zero_one.
Qed.

(* ---- Target 8: BBDBridgeSupply.v:95 (Section BBDBridgeSumSupply; the    ---- *)
(* ----   section carries no context, so lt and zero resolve through the   ---- *)
(* ----   global RealEnhancedReal instance, and the D := one closed form   ---- *)
(* ----   agrees with the real_lt face).                                   ---- *)
Theorem tspp_bbd_d_pos_one : real_lt real_zero real_one.
Proof.
  exact real_lt_zero_one.
Qed.

(* ---- Target 9: BBDBridgeSupply.v:97                                     ---- *)
Theorem tspp_bbd_z_pos_one : real_lt real_zero real_one.
Proof.
  exact real_lt_zero_one.
Qed.

(* ============================================================ *)
(* Section 2.  One closed RI-face statement (S01 RealInterfaceEnhanced,     *)
(*   target 5).  The blueprint originally fixed RI := Real, but the whole   *)
(*   library contains no concrete RealInterfaceEnhanced instance            *)
(*   (grep-checked), so the statement is lifted to the generic RI form:     *)
(*   the class field one_pos (S01_BaseRing.v:230) is itself the zero < one  *)
(*   certificate, and one direct citation proves the goal (the p2t1         *)
(*   precedent pattern).                                                    *)
(* ============================================================ *)

Theorem tspp_tsi_temperature_pos_one :
  forall RI : RealInterfaceEnhanced,
    @S01_BaseRing.lt RI (@S01_BaseRing.zero RI) (@S01_BaseRing.one RI).
Proof.
  intros RI.
  exact (@S01_BaseRing.one_pos RI).
Qed.

(* ============================================================ *)
(* Section 3.  Four closed RIS-face statements                             *)
(*   (RealInterfaceEnhancedSetoid; targets 6-7 and 10-11).  The carrier    *)
(*   faces: the setoid class field one_pos (class body from                *)
(*   S07_RealSetoidExpLog.v:7945 on) is itself the zero < one certificate; *)
(*   the blueprint instantiation R := Real with RIS := RealEnhancedReal    *)
(*   is stated directly over the concrete global twins (the instance block *)
(*   assembles one_pos := real_lt_zero_one, from S07_RealSetoidExpLog.v    *)
(*   :8596 on), so the statements below carry the same face as the six     *)
(*   Real-face statements of Section 1.                                    *)
(* ============================================================ *)

(* ---- Target 6: Arch_PA_04.v:1359 (Section ReqGibbsPilot, T := one).     ---- *)
Theorem tspp_pa04_rqg_t_pos_one :
  lt zero one.
Proof.
  exact one_pos.
Qed.

(* ---- Target 7: Arch_PA_04.v:1361 (same section, D := one).              ---- *)
Theorem tspp_pa04_rqg_d_pos_one :
  lt zero one.
Proof.
  exact one_pos.
Qed.

(* ---- Target 10: Arch_PA_04.v:883 (Section ReqFreeEnergyPilot, D := one). ---- *)
Theorem tspp_pa04_rfe_d_pos_one :
  lt zero one.
Proof.
  exact one_pos.
Qed.

(* ---- Target 11: Arch_PA_04.v:885 (same section, Z := one).              ---- *)
Theorem tspp_pa04_rfe_z_pos_one :
  lt zero one.
Proof.
  exact one_pos.
Qed.

(* ============================================================ *)
(* Section 4.  Itemwise zeroing translation (target 12:                     *)
(*   tmw_sum_zero_nonneg of PA_TempMonoW2Mark.v:54-57, together with the    *)
(*   same-face verbatim second filling frd_sum_zero_nonneg of               *)
(*   Arch_PA_02.v:902-905).  Statement face follows the current archive     *)
(*   verbatim: forall f, pointwise nonnegative -> zero sum -> pointwise     *)
(*   zero.  The slot-form input extension carries a surjective coverage     *)
(*   premise (forall s, sumd_in S s en) and a carrier-agreement premise     *)
(*   (sumf and the sumd list sum are req-equal pointwise), the family       *)
(*   pattern of the slot-form input extensions; the bool two-point          *)
(*   instance restates the coverage witness in a self-contained way (same   *)
(*   face as the sibling tsp_bool_enum_sumd_in_witness).                    *)
(* ============================================================ *)

Definition tspp_enum_bool : list bool := true :: false :: nil.

Lemma tspp_bool_enum_sumd_in_witness :
  forall s : bool, sumd_in bool s tspp_enum_bool.
Proof.
  intro s.
  destruct s as [|].
  - exact (sumd_in_head bool true true (false :: nil) (@id_refl bool true)).
  - exact (sumd_in_tail bool false true (false :: nil)
             (sumd_in_head bool false false nil (@id_refl bool false))).
Qed.

Theorem tspp_sum_zero_nonneg_slot_of_carrier_agree :
  forall (S : Set)
    (sumf : (S -> R) -> R) (en : list S),
    (forall s : S, sumd_in S s en) ->
    (forall f : S -> R, req (sumf f) (sumd_sumf S en f)) ->
    forall f : S -> R,
      (forall s : S, le zero (f s)) -> req (sumf f) zero ->
      forall s : S, req (f s) zero.
Proof.
  intros S sumf en Hcov Hagree f Hnn H0 s.
  exact (sumd_sum_zero_nonneg_surj S en f Hcov Hnn
           (req_trans (sumd_sumf S en f) (sumf f) zero
              (req_sym (sumf f) (sumd_sumf S en f) (Hagree f)) H0) s).
Qed.

Theorem tspp_sum_zero_nonneg_slot_bool_two :
  forall (sumf : (bool -> R) -> R),
    (forall f : bool -> R,
       req (sumf f) (sumd_sumf bool tspp_enum_bool f)) ->
    forall f : bool -> R,
      (forall s : bool, le zero (f s)) -> req (sumf f) zero ->
      forall s : bool, req (f s) zero.
Proof.
  intros sumf Hagree f Hnn H0 s.
  exact (tspp_sum_zero_nonneg_slot_of_carrier_agree bool sumf
           tspp_enum_bool tspp_bool_enum_sumd_in_witness Hagree f Hnn H0 s).
Qed.

(* ============================================================ *)
(* Section 5.  Assumption audit: Print Assumptions at every named exit,     *)
(*   each Closed under the global context; the name list and the Qed        *)
(*   count agree at 14.                                                     *)
(* ============================================================ *)
Print Assumptions tspp_ems_t_star_pos_one.
Print Assumptions tspp_emsc_t_star_pos_one.
Print Assumptions tspp_slc_t_pos_one.
Print Assumptions tspp_toyr04_t_pos_one.
Print Assumptions tspp_bbd_d_pos_one.
Print Assumptions tspp_bbd_z_pos_one.
Print Assumptions tspp_tsi_temperature_pos_one.
Print Assumptions tspp_pa04_rqg_t_pos_one.
Print Assumptions tspp_pa04_rqg_d_pos_one.
Print Assumptions tspp_pa04_rfe_d_pos_one.
Print Assumptions tspp_pa04_rfe_z_pos_one.
Print Assumptions tspp_bool_enum_sumd_in_witness.
Print Assumptions tspp_sum_zero_nonneg_slot_of_carrier_agree.
Print Assumptions tspp_sum_zero_nonneg_slot_bool_two.

(* ============================================================ *)
(* Section 6.  Extraction probe.  Library-layer transcriptions and this     *)
(*   file's own introductions are counted separately: a control probe       *)
(*   outside this file extracts the three library roots alone               *)
(*   (real_lt_zero_one, the two one_pos projections and                     *)
(*   sumd_sum_zero_nonneg_surj), so any Obj.magic reproduced there is       *)
(*   inherent to the library closure; the probe file shares this module's   *)
(*   name with a ctrl suffix and is not part of the delivered set.          *)
(* ============================================================ *)
Set Extraction Output Directory "_log/extraction".
Recursive Extraction tspp_ems_t_star_pos_one tspp_emsc_t_star_pos_one
  tspp_slc_t_pos_one tspp_toyr04_t_pos_one tspp_bbd_d_pos_one
  tspp_bbd_z_pos_one.
Recursive Extraction tspp_tsi_temperature_pos_one.
Recursive Extraction tspp_pa04_rqg_t_pos_one tspp_pa04_rqg_d_pos_one
  tspp_pa04_rfe_d_pos_one tspp_pa04_rfe_z_pos_one.
Recursive Extraction tspp_sum_zero_nonneg_slot_of_carrier_agree
  tspp_sum_zero_nonneg_slot_bool_two.
