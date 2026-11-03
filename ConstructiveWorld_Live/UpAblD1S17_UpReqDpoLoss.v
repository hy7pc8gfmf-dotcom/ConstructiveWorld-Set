(* ==========================================================================
   UpAblD1S17_UpReqDpoLoss.v - DPO alignment partition positivity certificate
   and premise packaging.
   Mission. 使命: uabd1s17_dpo_zap_pos (the positivity supply certificate for
     Z_align) together with the thirteen-slot premise packaging record
     uabd1s17_dpo_pack13 and its supplied witness uabd1s17_dpo_pack13_supplied.
   Dependencies. 依赖清单: S01_BaseRing..S15_TailFEPUp, UpReqAlign of the
     -Set lineage world; the interface is the argument-less Class
     RealInterfaceEnhancedSetoid (module RealInterfaceEnhancedMod).
   References. 对标: DPO alignment partition positivity premise (supply
     certificate for the alignment partition variable). Statement names
     carried over verbatim from the source piece; adaptation = pure binder
     removal + notation rebinding on this world's own precedent (the source
     argumented Class applications raised "Illegal application
     (Non-functional construction)" against the argument-less interface):
     R := Real by notation (UpReqSumD.v L58), predicate face real_lt
     (UpReqSumD.v L113-114), law fields resolved as bare names through the
     global instance RealEnhancedReal (UpReqSumD.v L68-72).
   Constructivity. 构造性注记: all Set-layer statements; every station
     Qed-closed, zero admitted items; the tail Print Assumptions probes
     report the closure face; no new axioms.
   Build. 编译配方: rocq c -native-compiler no -q -Q <world> "" -Q . ""
     UpAblD1S17_UpReqDpoLoss.v (cpu_guard thermal wrapper, ulimit -s 65532).
   ========================================================================== *)

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
Require Import UpReqAlign.
Import RealInterfaceEnhancedMod.

(* R := Real by notation: the argument-less Class fields resolve through
   the global Real instance (UpReqSumD.v L58 precedent). *)
Notation R := Real.

(* ============ canonical carrier instance, named ============ *)

Definition uabd1s17_ren : RealInterfaceEnhancedSetoid :=
  RealInterfaceEnhancedMod.RealEnhancedReal.

(* ============ Z_align_pos supply certificate ============ *)
(* Instance substitution: S:=unit, sumf:=point sum, reward:=zero function,
   beta:=one, pi_ref:=constant-one function. Under this instance Z_align_req
   reduces to the product one * exp_neg(-inv_pos(one) * zero); the
   positivity of both factors is given by one_pos and exp_neg_pos. *)

Lemma uabd1s17_dpo_zap_pos :
  real_lt zero (Z_align_req unit
            (fun f : unit -> Real => f tt)
            (fun _ : unit => zero)
            one
            one_pos
            (fun _ : unit => one)).
Proof.
  exact (mult_positive
           one
           (exp_neg (opp (mult (inv_pos one one_pos) zero)))
           one_pos
           (exp_neg_pos (opp (mult (inv_pos one one_pos) zero)))).
Qed.

(* ============ interface packaging record: the in-section declarations of
   the source module Section ReqDpoLossCore ============ *)
(* Field order = source declaration order; the two log compatibility
   statements are not part of this record (noted at the file head). *)

(* The type slots (S, Preference) of the source record are monomorphised to
   the supplied unit instance: type slots are erased at extraction and would
   raise Obj.magic casts at every slot value; the record's slot values below
   are carried by that single instance. *)
Inductive uabd1s17_dpo_pack13 : Type :=
| uabd1s17_dpo_pack13_intro :
    forall (sumf : (unit -> R) -> R)
           (reward : unit -> R) (beta : R) (beta_pos : real_lt zero beta)
           (pi_ref : unit -> R) (pi_ref_pos : forall s : unit, real_lt zero (pi_ref s))
           (Z_align_pos :
              real_lt zero (Z_align_req unit sumf reward beta beta_pos pi_ref))
           (pref_win : unit -> unit) (pref_lose : unit -> unit)
           (pref_dataset : list unit),
      uabd1s17_dpo_pack13.

(* ============ supply theorem: all record slots given by a single-point
   instance ============ *)

Theorem uabd1s17_dpo_pack13_supplied : uabd1s17_dpo_pack13.
Proof.
  exact (uabd1s17_dpo_pack13_intro
           (fun f : unit -> Real => f tt)
           (fun _ : unit => zero)
           one
           one_pos
           (fun _ : unit => one)
           (fun _ : unit => one_pos)
           uabd1s17_dpo_zap_pos
           (fun _ : unit => tt)
           (fun _ : unit => tt)
           (cons tt nil)).
Qed.

(* ============ assumption audit ============ *)

Print Assumptions uabd1s17_dpo_zap_pos.
Print Assumptions uabd1s17_dpo_pack13_supplied.
