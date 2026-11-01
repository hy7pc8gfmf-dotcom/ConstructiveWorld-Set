(* =====================================================================
   abl_tbase_tempsum_feed.v - named application forms of the tree list
   summation for the four temperature-family host sections (17 theorems).
   Mission.  For each host section - RealTempDefs (UpReqTempDefs.v),
     RealEntropyDeficitTemp (UpReqEntropyDeficitTemp.v), RealEntropyMaxTemp
     (UpReqEntropyMaxTemp.v, plus the extra le entry) and RealTempDual
     (UpReqTempDual.v) - provide a named per-host application form of the
     generic list fold sum real_list_sum (Section RealListSumMain of
     S08_RealMainlineDPO.v, Variable X : Type, matching the hosts'
     S : Type verbatim): positivity, pointwise-equality respect, linearity,
     additivity, and pointwise monotonicity (EntropyMaxTemp only).
   Dependencies.  Tree modules S01_BaseRing through S15_TailFEPUp (the six
     RealListSumMain roots live in S08); Stdlib List, Extraction; no other
     imports; the four upstream host files untouched (no edits, no cascade).
   References.  uabt4_sum_carrier4_realized (UpAblT4_SumCarrier.v), the
     sigT realization pack of the same sum; uabT1_rte_fsum_* family
     (UpAblT1_UpReqEntropy.v), the per-host application-form style.  Host
     faces quoted verbatim: UpReqTempDefs.v 90-104, UpReqEntropyDeficitTemp.v
     167-181, UpReqEntropyMaxTemp.v 132-149, UpReqTempDual.v 32-46.
   Constructivity.  Every theorem ends in Qed by direct takes on the
     exported tree roots; no proof gaps, no unstated premises, no classical
     logic.  Predicates ride the real-layer Set carriers of the tree
     (real_eq / real_lt / real_le).  Positivity carries its non-emptiness
     witness as data (cons head w, tail rest): an empty enumeration has no
     constructive positive sum; each proof loads the witness at the head.
   Build.  source Live/toolchain/env.sh && unset COQLIB ROCQLIB &&
     ulimit -s 65532; rocq c -native-compiler no -q -Q . ""; green =
     exit 0, zero Error lines, .vo head bytes 436f7121 00015ff4, .vo newer
     than .v, fifth check rocqchk; tail extraction check, Obj.magic count.
   ===================================================================== *)

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
From Stdlib Require Import List.
From Stdlib Require Import Extraction.

(* The seventeen statements below quote each host variable face verbatim (order, names, implicit positions included); the summation carrier position reads real_sum_over_S as the instance real_list_sum S l. *)

(* Host 1: UpReqTempDefs.v, Section RealTempDefs - four entries (carrier line 94; pos 95, ext 98, linear 100, add 102). *)

(* Entry real_sum_pos_preserved, host lines verbatim; the sum reads real_list_sum S (w :: rest): non-emptiness rides the cons-head witness data, since under an S : Type carrier the Not (Id l nil) premise form is ill-typed (the Id position constrains its carrier to Set, established by a type check), so the witness is stated as data - a declared strengthening. *)
Theorem tbtf_tdefs_sum_pos :
  forall (S : Type) (w : S) (rest : list S) (f : S -> Real),
    (forall s : S, real_lt real_zero (f s)) ->
    real_lt real_zero (real_list_sum S f (w :: rest)).
Proof.
  intros S w rest f Hf.
  apply (real_list_sum_pos S f (w :: rest) Hf).
  intro Hc. discriminate Hc.
Qed.

(* Entry real_sum_over_S_ext, host lines verbatim. *)
Theorem tbtf_tdefs_sum_ext :
  forall (S : Type) (l : list S) (f g : S -> Real),
    (forall s : S, real_eq (f s) (g s)) ->
    real_eq (real_list_sum S f l) (real_list_sum S g l).
Proof.
  intros S l f g H.
  exact (real_list_sum_ext S f g l H).
Qed.

(* Entry real_sum_over_S_linear, host lines verbatim. *)
Theorem tbtf_tdefs_sum_linear :
  forall (S : Type) (l : list S) (a : Real) (f : S -> Real),
    real_eq (real_list_sum S (fun s : S => real_mult a (f s)) l)
            (real_mult a (real_list_sum S f l)).
Proof.
  intros S l a f.
  exact (real_list_sum_linear S a f l).
Qed.

(* Entry real_sum_over_S_add, host lines verbatim. *)
Theorem tbtf_tdefs_sum_add :
  forall (S : Type) (l : list S) (f g : S -> Real),
    real_eq (real_list_sum S (fun s : S => real_plus (f s) (g s)) l)
            (real_plus (real_list_sum S f l) (real_list_sum S g l)).
Proof.
  intros S l f g.
  exact (real_list_sum_add S f g l).
Qed.

(* Host 2: UpReqEntropyDeficitTemp.v, Section RealEntropyDeficitTemp - four entries (carrier line 170; pos 171, ext 174, linear 176, add 179); variable face identical to host 1. *)

Theorem tbtf_edt_sum_pos :
  forall (S : Type) (w : S) (rest : list S) (f : S -> Real),
    (forall s : S, real_lt real_zero (f s)) ->
    real_lt real_zero (real_list_sum S f (w :: rest)).
Proof.
  intros S w rest f Hf.
  apply (real_list_sum_pos S f (w :: rest) Hf).
  intro Hc. discriminate Hc.
Qed.

Theorem tbtf_edt_sum_ext :
  forall (S : Type) (l : list S) (f g : S -> Real),
    (forall s : S, real_eq (f s) (g s)) ->
    real_eq (real_list_sum S f l) (real_list_sum S g l).
Proof.
  intros S l f g H.
  exact (real_list_sum_ext S f g l H).
Qed.

Theorem tbtf_edt_sum_linear :
  forall (S : Type) (l : list S) (a : Real) (f : S -> Real),
    real_eq (real_list_sum S (fun s : S => real_mult a (f s)) l)
            (real_mult a (real_list_sum S f l)).
Proof.
  intros S l a f.
  exact (real_list_sum_linear S a f l).
Qed.

Theorem tbtf_edt_sum_add :
  forall (S : Type) (l : list S) (f g : S -> Real),
    real_eq (real_list_sum S (fun s : S => real_plus (f s) (g s)) l)
            (real_plus (real_list_sum S f l) (real_list_sum S g l)).
Proof.
  intros S l f g.
  exact (real_list_sum_add S f g l).
Qed.

(* Host 3: UpReqEntropyMaxTemp.v, Section RealEntropyMaxTemp - five entries (carrier line 134; pos 135, ext 138, le 142 - the host file cites the tree root real_list_sum_le of S08 line 421 in place -, linear 144, add 147). *)

Theorem tbtf_emt_sum_pos :
  forall (S : Type) (w : S) (rest : list S) (f : S -> Real),
    (forall s : S, real_lt real_zero (f s)) ->
    real_lt real_zero (real_list_sum S f (w :: rest)).
Proof.
  intros S w rest f Hf.
  apply (real_list_sum_pos S f (w :: rest) Hf).
  intro Hc. discriminate Hc.
Qed.

Theorem tbtf_emt_sum_ext :
  forall (S : Type) (l : list S) (f g : S -> Real),
    (forall s : S, real_eq (f s) (g s)) ->
    real_eq (real_list_sum S f l) (real_list_sum S g l).
Proof.
  intros S l f g H.
  exact (real_list_sum_ext S f g l H).
Qed.

(* Extra entry real_sum_over_S_le, host lines verbatim; root proved inside the host file itself. *)
Theorem tbtf_emt_sum_le :
  forall (S : Type) (l : list S) (f g : S -> Real),
    (forall s : S, real_le (f s) (g s)) ->
    real_le (real_list_sum S f l) (real_list_sum S g l).
Proof.
  intros S l f g H.
  exact (real_list_sum_le S f g l H).
Qed.

Theorem tbtf_emt_sum_linear :
  forall (S : Type) (l : list S) (a : Real) (f : S -> Real),
    real_eq (real_list_sum S (fun s : S => real_mult a (f s)) l)
            (real_mult a (real_list_sum S f l)).
Proof.
  intros S l a f.
  exact (real_list_sum_linear S a f l).
Qed.

Theorem tbtf_emt_sum_add :
  forall (S : Type) (l : list S) (f g : S -> Real),
    real_eq (real_list_sum S (fun s : S => real_plus (f s) (g s)) l)
            (real_plus (real_list_sum S f l) (real_list_sum S g l)).
Proof.
  intros S l f g.
  exact (real_list_sum_add S f g l).
Qed.

(* Host 4: UpReqTempDual.v, Section RealTempDual - four entries (carrier line 35; pos 36, ext 39, linear 41, add 44); variable face identical to host 1. *)

Theorem tbtf_tdu_sum_pos :
  forall (S : Type) (w : S) (rest : list S) (f : S -> Real),
    (forall s : S, real_lt real_zero (f s)) ->
    real_lt real_zero (real_list_sum S f (w :: rest)).
Proof.
  intros S w rest f Hf.
  apply (real_list_sum_pos S f (w :: rest) Hf).
  intro Hc. discriminate Hc.
Qed.

Theorem tbtf_tdu_sum_ext :
  forall (S : Type) (l : list S) (f g : S -> Real),
    (forall s : S, real_eq (f s) (g s)) ->
    real_eq (real_list_sum S f l) (real_list_sum S g l).
Proof.
  intros S l f g H.
  exact (real_list_sum_ext S f g l H).
Qed.

Theorem tbtf_tdu_sum_linear :
  forall (S : Type) (l : list S) (a : Real) (f : S -> Real),
    real_eq (real_list_sum S (fun s : S => real_mult a (f s)) l)
            (real_mult a (real_list_sum S f l)).
Proof.
  intros S l a f.
  exact (real_list_sum_linear S a f l).
Qed.

Theorem tbtf_tdu_sum_add :
  forall (S : Type) (l : list S) (f g : S -> Real),
    real_eq (real_list_sum S (fun s : S => real_plus (f s) (g s)) l)
            (real_plus (real_list_sum S f l) (real_list_sum S g l)).
Proof.
  intros S l f g.
  exact (real_list_sum_add S f g l).
Qed.

(* Global-context closure audit: one Print Assumptions per supply theorem (seventeen). *)
Print Assumptions tbtf_tdefs_sum_pos.
Print Assumptions tbtf_tdefs_sum_ext.
Print Assumptions tbtf_tdefs_sum_linear.
Print Assumptions tbtf_tdefs_sum_add.
Print Assumptions tbtf_edt_sum_pos.
Print Assumptions tbtf_edt_sum_ext.
Print Assumptions tbtf_edt_sum_linear.
Print Assumptions tbtf_edt_sum_add.
Print Assumptions tbtf_emt_sum_pos.
Print Assumptions tbtf_emt_sum_ext.
Print Assumptions tbtf_emt_sum_le.
Print Assumptions tbtf_emt_sum_linear.
Print Assumptions tbtf_emt_sum_add.
Print Assumptions tbtf_tdu_sum_pos.
Print Assumptions tbtf_tdu_sum_ext.
Print Assumptions tbtf_tdu_sum_linear.
Print Assumptions tbtf_tdu_sum_add.

(* Extraction check: two representative theorems of this module plus one root-family control entry, extracted separately; Obj.magic counts are attributed per surface (this module vs library-layer transcription). *)
Extraction "_tbtf_g3_probe.ml" tbtf_tdefs_sum_pos tbtf_tdefs_sum_ext.
Extraction "_tbtf_g3_ctrl_root.ml" real_list_sum_ext.
