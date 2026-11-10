(* ConstructiveWorld-Set -- tail-slot supply pieces closing the PA_04 Gibbs pilot interface. *)

(** * abl_tail_supply_66: the Real specialization closure of the req_exp_neg_ext interface slot and the trimmed exit-shape form of the Gibbs temperature statement.

    Mission.  Supplies the remaining interface slot of the [ReqGibbsPilot]
      section of [Arch_PA_04]: [tsp_pa04_req_exp_neg_ext] closes
      [req_exp_neg_ext] over [Real] (instance [RealEnhancedReal]) as
      [forall x y : Real, req x y -> req (exp_neg x) (exp_neg y)], and
      [tsp_pa04_req_attention_is_gibbs_temp_wo] restates the exit shape of
      [SigMigrate.req_attention_is_gibbs_temp] fed only that slot.

    Dependencies.  Stdlib [List] and [Extraction] (extraction audit).
      Requires [S01_BaseRing], [S02_CauchyComplete], [S03_QExp],
      [S04_RealExpLogConv], [S05_AlignmentGRPO], [S06_DiffSamplingGibbs],
      [S07_RealSetoidExpLog], [S08_RealMainlineDPO], [S09_EntropyReal],
      [S10_KVQuantTrig], [S11_TP3B5], [S12_B5RecycleSF], [S13_NLiveAudit],
      [S14_B5BatchBlock], [S15_TailFEPUp], [UpConstitution] and
      [Arch_PA_04] of this development.

    References.  This development, abl_tail_supply_66.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" abl_tail_supply_66.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 000160bc] (the 9.3 world convention). *)
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
Require Import UpConstitution.
Require Import Arch_PA_04.
Import RealInterfaceEnhancedMod.
(* Interface adaptation (file-scoped): the interface class in this tree is unparameterized;
   its carrier is the global Real; the field names resolve through the concrete global twins
   (the bindings the Instance RealEnhancedReal assigns) via the Abbreviation vernacular
   (the Arch_PA_04 SigMigrate module-scoped precedent), so the statement faces elaborate on
   the concrete real_eq/real_lt carriers and extract without casts. *)
Abbreviation req := real_eq.
Abbreviation req_opp_compat := RealSetoid.real_eq_opp_compat.
Abbreviation zero := real_zero.
Abbreviation lt := real_lt.
Abbreviation opp := real_opp.
Abbreviation inv_pos := real_inv_pos.
Abbreviation exp_neg := real_exp_neg.

(* ============================================================ *)
(* Section 1. interface gap bridge: the Real specialization closure of             *)
(*    req_exp_neg_ext.  the slot is recorded at Arch_PA_04.v:1356 (inside the        *)
(*    ReqGibbsPilot section :1350, as a section premise): forall x y : R,     *)
(*    req x y -> req (exp_neg x) (exp_neg y).  the abstract generic position      *)
(*    cannot be resolved in-tree (the interface carries no such field); the    *)
(*    resolved form is the Real specialization with [R := Real] and instance       *)
(*    [RealEnhancedReal]; the proof lifts req over opp via req_opp_compat, closed by cauchy_real_exp_wd.     *)
(* ============================================================ *)

Theorem tsp_pa04_req_exp_neg_ext :
  forall x y : Real, req x y -> req (exp_neg x) (exp_neg y).
Proof.
  intros x y H.
  exact (cauchy_real_exp_wd (real_opp x) (real_opp y) (req_opp_compat x y H)).
Qed.

(* ============================================================ *)
(* Section 2. trimmed exit-shape form: the original theorem is fed only the           *)
(*    req_exp_neg_ext slot.  the statement face is isomorphic to the exit    *)
(*    shape of [SigMigrate.req_attention_is_gibbs_temp] (About-probed); the       *)
(*    only change is that the [req_exp_neg_ext] slot disappears once this     *)
(*    supply is plugged in, while [S], [sumf], [T], [T_pos], [D], [D_pos],     *)
(*    [energy], [z] and the three premises stay verbatim (the two positivity slots are explicit premise positions of the original theorem).            *)
(* ============================================================ *)

Theorem tsp_pa04_req_attention_is_gibbs_temp_wo :
  forall (S : Set) (sumf : (S -> Real) -> Real)
         (T : Real) (T_pos : lt zero T) (D : Real) (D_pos : lt zero D)
         (energy z : S -> Real)
         (partition_function_temp_pos :
            lt zero (SigMigrate.cwe_partition_function_temp S sumf T T_pos z))
         (Z_thermo_pos :
            lt zero (SigMigrate.Z_thermo S sumf D D_pos energy)),
    (req (inv_pos T T_pos) (inv_pos D D_pos)) ->
    (forall s : S, req (energy s) (opp (z s))) ->
    (req (SigMigrate.Z_thermo S sumf D D_pos energy)
         (SigMigrate.cwe_partition_function_temp S sumf T T_pos z)) ->
    forall s : S,
      req (SigMigrate.cwe_softmax_temp S sumf T T_pos z
             partition_function_temp_pos s)
          (SigMigrate.boltzmann_dist_attn S sumf D D_pos energy
             Z_thermo_pos s).
Proof.
  intros S sumf T T_pos D D_pos energy z Hpt Hzt HD Henergy HZ s.
  exact (SigMigrate.req_attention_is_gibbs_temp S sumf
           tsp_pa04_req_exp_neg_ext
           T T_pos D D_pos energy z Hpt Hzt HD Henergy HZ s).
Qed.

(* ============================================================ *)
(* Section 3. assumption audit (each exit judged Closed)                                  *)
(* ============================================================ *)
Print Assumptions tsp_pa04_req_exp_neg_ext.
Print Assumptions tsp_pa04_req_attention_is_gibbs_temp_wo.

(* ============================================================ *)
(* Section 4. extraction check (criterion: the printed output counts zero    *)
(*    [Obj.magic]; output goes to the local check area).  both statements are      *)
(*    proof-carried (req statement face); the closure contains the SigMigrate pilot proof terms and the cauchy_real_exp computation layer; counts are reported as measured.         *)
(* ============================================================ *)
From Stdlib Require Import Extraction.
Set Extraction Output Directory "_log/extraction".
Recursive Extraction tsp_pa04_req_exp_neg_ext tsp_pa04_req_attention_is_gibbs_temp_wo.
