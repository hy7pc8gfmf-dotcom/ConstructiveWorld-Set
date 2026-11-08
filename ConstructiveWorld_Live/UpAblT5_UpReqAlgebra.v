(* ConstructiveWorld-Set — concrete Real instances of the logarithm lemmas of the request algebra. *)

(** * UpAblT5_UpReqAlgebra: concrete-instance restatements of the
       UpReqAlgebra logarithm lemmas.

    Mission.  The source lemmas restated as concrete [Real]-layer
    instances, discharged by one-step direct reference:
    [abl_UpReqAlgebra_log_req_compat] (compatibility of [log] with
    [req], the Setoid interface instance) and
    [abl_UpReqAlgebra_log_inv_exp_neg_req] ([log_inv] of [exp_neg]
    returns its argument).  Both proof bodies coincide verbatim with
    the current Main originals (identity conservation).

    Dependencies.  Requires [S01_BaseRing] through [S15_TailFEPUp],
    [UpRealLeB], [G05_LogSmall] of this development; [UpReqAlgebra] is
    a read-only source module (tree untouched, no extra [Require]).

    References.  This development, UpAblT5_UpReqAlgebra.v, the baseline
    module in ConstructiveWorld-Main whose statement names are carried
    over here verbatim (statement-face Set-carrier completion); the
    source-provenance block below records the line-level derivation.

    Constructivity.  All named statements and fields are carried by
      [Set] (decidable Q-carriers [QltT]/[QleT']/[QeqT], [Id],
      [NatLe]); statements extract with [Obj.magic] = 0 and no
      erasure; [coqchk] reports [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" UpAblT5_UpReqAlgebra.v]
      compiles cleanly (exit 0); the first eight bytes of the
      artifact are [436f7121 00015ff4]. *)


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
Require Import G05_LogSmall.
Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* Source provenance (UpReqAlgebra.v, read-only; the source tree is     *)
(* untouched).                                                          *)
(*   (1) L1498 [log_req_compat] — concrete-instance supply of the       *)
(*      Setoid interface (supply grade N3): the source section          *)
(*      [ReqLogBridge] (from L1495, [Context {R}{RIS}]) is instantiated *)
(*      at [R := Real], [RIS := RealEnhancedReal] (S07:8566); the       *)
(*      discharging lemma is [logd_log_compat_real] at                  *)
(*      G05_LogSmall.v:302 (case class B1 conclusion: closed at the     *)
(*      Real layer; its body is the mono chain over                     *)
(*      [real_log_le_mono]); dependency slot UpReqAlgebra:1538.         *)
(*   (2) L1502 [log_inv_exp_neg_req] — same grade (N3); the             *)
(*      discharging lemma is [logd_log_inv_exp_neg_real] at             *)
(*      G05_LogSmall.v:344 (case class B4 conclusion: the proof family  *)
(*      names the argument slots of log_inv_exp_neg_req(5) explicitly); *)
(*      dependency slot UpReqAlgebra:1521.                              *)
(* Discipline: purely constructive; statement face entirely at the Set  *)
(* layer; axiom face zero additions; the [abl_] prefix prevents name    *)
(* clashes within this file.                                            *)
(* ============================================================ *)
(* Note on the class-free world: the interface field names below bind to
   the concrete Real root names (a direct lineage form with no class
   arguments). *)
Notation req := real_eq.
Notation zero := real_zero.
Notation lt := real_lt.
Notation log := real_log.
Notation log_inv := real_log_inv.
Notation exp_neg := real_exp_neg.
Notation exp_neg_pos := real_exp_neg_pos.

(* ################ (1) log_req_compat (argument shape carried over verbatim
   from the source L1498-1500; concrete-instance form) ################ *)
(* The source section is quantified over {R}{RIS}; outside the section the
   concrete instance R := Real, RIS := RealEnhancedReal is taken: the names
   in the statement (lt/req/log/zero) resolve through the
   RealInterfaceEnhancedMod namespace and elaborate identically to
   G05:302 logd_log_compat_real. *)
Theorem abl_UpReqAlgebra_log_req_compat : forall (x y : Real) (Hx : lt zero x) (Hy : lt zero y),
  req x y -> req (log x Hx) (log y Hy).
Proof.
  exact logd_log_compat_real.
Qed.

(* ################ (2) log_inv_exp_neg_req (argument shape carried over
   verbatim from the source L1502-1503; concrete-instance form) ######### *)
Theorem abl_UpReqAlgebra_log_inv_exp_neg_req : forall x : Real,
  req (log_inv (exp_neg x) (exp_neg_pos x)) x.
Proof.
  exact logd_log_inv_exp_neg_real.
Qed.

(* ---- Assumption self-check section (one Print Assumptions per statement) ---- *)
Print Assumptions abl_UpReqAlgebra_log_req_compat.
Print Assumptions abl_UpReqAlgebra_log_inv_exp_neg_req.
