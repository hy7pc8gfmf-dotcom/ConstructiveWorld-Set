(* abl_tbase_tempsum.v - Real-face abstract-summation interface supply family
   (up-base batch UB5; upstream register _tbase100 family, card 1 F1).
   Mission. Five bridge theorems (tspt_rsum_ prefix: ext/add/linear/le plus
   a pos cons-head witness bridge) feed the Real-face remainder of the sumf
   six-property family across thirteen host sections, carried by the
   definitional reading real_sum_over_S := real_list_sum X f l of section
   S08_RealListSumMain (X : Type carrier, fold real_plus, nil to real_zero);
   graded N1 across the board, exact one-step citations, zero padding.
   Dependencies. S01_BaseRing .. S15_TailFEPUp (fifteen in-tree modules,
   read-only) plus Stdlib List and Extraction, and the interface import
   RealInterfaceEnhancedMod; the thirteen host target files take zero
   Require (slot-level check against the host slot statement faces only,
   never through host modules), zero bytes touched, zero cascade.
   References. Supply roots measured this session: real_list_sum_ext at
   S08_RealMainlineDPO.v:301, _add :346, _linear :368, _le :438, _pos :469
   (archived header cites 296/341/363/433/464, an older revision; pristine
   probe re-measured, RC=0); precedents G06_BForm/UpReqRealFEP/SteadyThermo.
   Constructivity. Statement faces fully Set-carried (real_eq/real_le/
   real_lt Set-valued interface predicates; list cons data carries the
   witness; zero Prop positions on statement faces); every proof ends in
   Qed as a true construction. The pos bridge keeps its statement
   premise-free: the tree root carries an l <> nil premise, dissolved
   inside the proof body by the cons head w::rest itself as the witness
   (discriminate), a declared position, never a silent strengthening. Print
   Assumptions per piece: all Closed under the global context; the trailing
   extraction probe is judged by Obj.magic counting.
   Build. source env.sh, unset COQLIB ROCQLIB, ulimit -s 65532; every
   launch passes the cpu_guard thermal wrapper (-Reg /tmp/cw_reg_nw3
   -Front 0 -Mid 1 -MaxWaitSec 600); rocq c -native-compiler no -q -Q . ""
   in the seat-private world_tbase room, product delivered same-address. *)

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
Import ListNotations.
Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* Grading declaration (same verdict for all five pieces): N1 - direct
   citation of the in-library instantiated discharge pieces (the five
   real_list_sum roots of S08_RealListSumMain in service; each bridge names
   its feed position explicitly, exact in one step). Per-bridge statement
   faces are extracted word for word from the host slot archives (argument
   order, naming and implicit positions included; the G02 two-section bare
   fun s => and the fun s : S => of the other host sections are the same
   term modulo parsing sugar - three-face cross-check on file); the
   real_sum_over_S position is read as the real_list_sum S en instantiation
   (X : Type verbatim same-face as the host S : Type; carrier-substitution
   precedent = UpReqSteadyThermo SteadyThermoSumSlotsSupply). *)
(* ============================================================ *)

(* ---- Bridge 1: sum extensionality (host slot real_sum_over_S_ext verbatim;
      TempDefs:98/EDT:174/EMT:139/TempDual:39/EUTemp:108/EUNeg:904/
      TKTV:112/TKTVF:385/G06:53/G02:223/:548/UpRealLeB:382/RFEP:121 -
      thirteen sections same shape; root real_list_sum_ext@S08:301 cited) ---- *)
Theorem tspt_rsum_ext :
  forall (S : Type) (en : list S) (f g : S -> Real),
    (forall s : S, real_eq (f s) (g s)) ->
    real_eq (real_list_sum S f en) (real_list_sum S g en).
Proof.
  intros S en f g H.
  exact (real_list_sum_ext S f g en H).
Qed.

(* ---- Bridge 2: sum additivity split (host slot real_sum_over_S_add
      verbatim; TempDefs:102/EDT:179/EMT:148/TempDual:44/EUTemp:113/
      EUNeg:909/TKTV:115/TKTVF:388/G06:57/UpRealLeB:386/RFEP:123 - eleven
      sections same shape; root real_list_sum_add@S08:346 cited) ---- *)
Theorem tspt_rsum_add :
  forall (S : Type) (en : list S) (f g : S -> Real),
    real_eq (real_list_sum S (fun s : S => real_plus (f s) (g s)) en)
            (real_plus (real_list_sum S f en) (real_list_sum S g en)).
Proof.
  intros S en f g.
  exact (real_list_sum_add S f g en).
Qed.

(* ---- Bridge 3: sum left linearity (host slot real_sum_over_S_linear
      verbatim; TempDefs:100/EDT:176/EMT:145/TempDual:41/EUTemp:110/
      EUNeg:906/TKTVF:391/G06:61/G02:225/:550/UpRealLeB:389/RFEP:127 -
      twelve sections same shape; root real_list_sum_linear@S08:368 cited) ---- *)
Theorem tspt_rsum_linear :
  forall (S : Type) (en : list S) (a : Real) (f : S -> Real),
    real_eq (real_list_sum S (fun s : S => real_mult a (f s)) en)
            (real_mult a (real_list_sum S f en)).
Proof.
  intros S en a f.
  exact (real_list_sum_linear S a f en).
Qed.

(* ---- Bridge 4: sum monotone (host slot real_sum_over_S_le verbatim;
      EMT:143/TKTV:118/G06:55/UpRealLeB:384 four sections same shape;
      root real_list_sum_le@S08:438 cited) ---- *)
Theorem tspt_rsum_le :
  forall (S : Type) (en : list S) (f g : S -> Real),
    (forall s : S, real_le (f s) (g s)) ->
    real_le (real_list_sum S f en) (real_list_sum S g en).
Proof.
  intros S en f g H.
  exact (real_list_sum_le S f g en H).
Qed.

(* ---- Bridge 5: sum positivity, cons-head witness feed (host slot
      real_sum_pos_preserved verbatim + declared position: the host slot has
      no premise position; the non-emptiness witness is carried by the
      enumeration w::rest data shape, and w::rest is the witness itself, so
      the statement face is zero-Prop; the l <> nil premise of root
      real_list_sum_pos@S08:469 is dissolved inside the proof body by the
      cons-head data witness (the :: against [] constructor conflict,
      discriminate in one stroke); eight sections same shape =
      TempDefs:95/EDT:171/EMT:136/TempDual:36/EUTemp:105/EUNeg:901/
      G02:220/:545) ---- *)
Theorem tspt_rsum_pos_cons :
  forall (S : Type) (f : S -> Real) (w : S) (rest : list S),
    (forall s : S, real_lt real_zero (f s)) ->
    real_lt real_zero (real_list_sum S f (w :: rest)).
Proof.
  intros S f w rest H.
  apply (real_list_sum_pos S f (w :: rest) H).
  intro Hn.
  discriminate Hn.
Qed.

(* ============================================================ *)
(* PA audit segment (per-piece Closed verdicts; name list = Qed count = 5,
   zero delta) *)
(* ============================================================ *)
Print Assumptions tspt_rsum_ext.
Print Assumptions tspt_rsum_add.
Print Assumptions tspt_rsum_linear.
Print Assumptions tspt_rsum_le.
Print Assumptions tspt_rsum_pos_cons.

(* ============================================================ *)
(* Extraction check segment (criterion = Obj.magic counts of the
   library-layer transcription and the self-introduced faces counted
   separately, registered honestly; three representative bridges cover three
   statement families: ext direct citation / linear per-item form / pos cons
   form; if the extractor hard-fails or the record-layer transcription is
   nonzero, handle by the in-pool 63/68 precedent control-experiment caliber
   and register item by item - never report a false pass) *)
(* ============================================================ *)
From Stdlib Require Import Extraction.
Set Extraction Output Directory "_log/extraction".
Recursive Extraction tspt_rsum_ext tspt_rsum_linear tspt_rsum_pos_cons.
