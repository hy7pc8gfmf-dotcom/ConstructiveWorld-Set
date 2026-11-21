(* ==========================================================================
   SumDCarrierFeed.v -- concrete enumerated-sum carrier pieces for the
   fifteen slot positions of the sum/order/cancellation interface families.
   Mission.  Fifteen feed_ pieces over the concrete operator [sumd_sumf S enum]:
     the four rpli_ slots (le/ext/add/linear), the three asum_ slots, the
     cancellation piece [feed_b_mult_cancel] (a > 0 and a*x == 0 give x == 0),
     the psum_ pair, the positivity piece [feed_sumf_pos], the ssum_ pair with
     [feed_ralt_sum_ext], and the nonnegativity piece [feed_sum_nonneg_h];
     every body is a direct slot discharge of the certified [sumd_*] family.
   Dependencies.  S01_BaseRing..S15_TailFEPUp, UpReqAlgebra, UpReqPPOPlain,
     UpSigMigrate2, UpReqDist, UpFirewallReq, UpReqAlignRestA, UpReqAttnIter,
     UpReqSumD, Stdlib List.  Interface note: in this tree
     RealInterfaceEnhancedSetoid is the argument-less Class of module
     RealInterfaceEnhancedMod (S07_RealSetoidExpLog.v); req/lt/le are bound by
     Notation to the concrete carriers real_eq/real_lt/real_le.
   References.  The enumerated finite-sum discharge family of UpReqSumD
     ([sumd_sum_le]/[sumd_sum_ext]/[sumd_sum_add]/[sumd_sum_linear]/
     [sumd_sum_pos]/[sumd_list_sum_nonneg]/[sumd_list_sum_pos_cons]) and the
     cancellation lemma [req_mult_cancel_l] of UpReqAlgebra; the baseline
     module in ConstructiveWorld-Main carries the same slot names verbatim.
   Constructivity.  All statements ride the Set layer (req/le/lt are
     Set-valued); the nonemptiness premise of [feed_sumf_pos] is the Set-level
     identity carrier [Not (Id (list S) enum nil)] (S01_BaseRing
     [one_neq_zero] idiom), mathematically necessary since the empty carrier
     sums to zero and [lt zero zero] is unprovable; zero Prop leakage, zero
     extraction casts; every piece ends in Defined, and the trailing Print
     Assumptions block covers all fifteen.
   Build.  Rocq 9.1 direct coqc -native-compiler no -q -Q . "" (vo shadow
     tree, same-world rebuild), cpu_guard wrapped, ulimit -s 65532.
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
Require Import UpReqAlgebra.
Require Import UpReqPPOPlain.
Require Import UpSigMigrate2.
Require Import UpReqDist.
Require Import UpFirewallReq.
Require Import UpReqAlignRestA.
Require Import UpReqAttnIter.
Require Import UpReqSumD.
From Stdlib Require Import List.
Import ListNotations.
Import RealInterfaceEnhancedMod.

(* Statement-face relation fields bound to the informative concrete carriers
   (UpAlignIdReq.v form): the Notations name exactly the carriers the global
   Real instance RealEnhancedReal assigns to these class fields, so each
   statement below elaborates to the concrete real_* term. *)
Notation R := Real.
Notation lt := real_lt.
Notation req := real_eq.
Notation le := real_le.

Section SumDCarrierFeed.

Variable S : Set.
Variable enum : list S.

(* ---- Slot group 1: the plain-PPO summation slots (le/ext/add/linear) ---- *)

Definition feed_rpli_sum_le :
  forall f g : S -> R, (forall s : S, le (f s) (g s)) -> le (sumd_sumf S enum f) (sumd_sumf S enum g)
  := @sumd_sum_le S enum.

Definition feed_rpli_sum_ext :
  forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumd_sumf S enum f) (sumd_sumf S enum g)
  := @sumd_sum_ext S enum.

Definition feed_rpli_sum_add :
  forall f g : S -> R,
    req (sumd_sumf S enum (fun s : S => plus (f s) (g s)))
        (plus (sumd_sumf S enum f) (sumd_sumf S enum g))
  := @sumd_sum_add S enum.

Definition feed_rpli_sum_linear :
  forall (a : R) (f : S -> R),
    req (sumd_sumf S enum (fun s : S => mult a (f s))) (mult a (sumd_sumf S enum f))
  := @sumd_sum_linear S enum.

(* ---- Slot group 2: the alignment-core summation slots (ext/add/linear) ---- *)

Definition feed_asum_ext :
  forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumd_sumf S enum f) (sumd_sumf S enum g)
  := @sumd_sum_ext S enum.

Definition feed_asum_add :
  forall f g : S -> R,
    req (sumd_sumf S enum (fun s : S => plus (f s) (g s)))
        (plus (sumd_sumf S enum f) (sumd_sumf S enum g))
  := @sumd_sum_add S enum.

Definition feed_asum_linear :
  forall (a : R) (f : S -> R),
    req (sumd_sumf S enum (fun s : S => mult a (f s))) (mult a (sumd_sumf S enum f))
  := @sumd_sum_linear S enum.

(* Cancellation slot: a > 0 and a*x == 0 give x == 0.  Body: left
   cancellation [req_mult_cancel_l] at b := x, c := zero (UpReqAlgebra),
   with [mult_zero] folded through [req_trans]/[req_sym]. *)
Definition feed_b_mult_cancel :
  forall (a x : R), lt zero a -> req (mult a x) zero -> req x zero
  := fun (a x : R) (Ha : lt zero a) (Hax : req (mult a x) zero) =>
       req_mult_cancel_l a x zero Ha
         (req_trans (mult a x) zero (mult a zero) Hax
            (req_sym (mult a zero) zero (mult_zero a))).

(* ---- Slot group 3: the probability/softmax-dual summation slots ---- *)

Definition feed_psum_linear :
  forall (a : R) (f : S -> R),
    req (sumd_sumf S enum (fun s : S => mult a (f s))) (mult a (sumd_sumf S enum f))
  := @sumd_sum_linear S enum.

Definition feed_psum_add :
  forall f g : S -> R,
    req (sumd_sumf S enum (fun s : S => plus (f s) (g s)))
        (plus (sumd_sumf S enum f) (sumd_sumf S enum g))
  := @sumd_sum_add S enum.

(* Positivity slot.  The host statement carries no premise; the feed face
   adds the explicit nonemptiness premise [Not (Id (list S) enum nil)] (the
   S01_BaseRing [one_neq_zero] idiom): the empty carrier sums to zero and
   [lt zero zero] is constructively unprovable, so the premise is
   mathematically necessary, not decorative.  The body discharges
   [sumd_sum_pos] at the same slot shape, reading the Set-level identity
   carrier through the standard equality-to-Id cast. *)
Definition feed_sumf_pos :
  forall f : S -> R,
    Not (@Id (list S) enum nil) -> (forall s : S, lt zero (f s)) -> lt zero (sumd_sumf S enum f)
  := fun (f : S -> R) (Hne : Not (@Id (list S) enum nil)) (Hpos : forall s : S, lt zero (f s)) =>
       @sumd_sum_pos S enum f
         (fun Hz : enum = nil =>
            Hne (match Hz in (_ = e) return @Id (list S) enum e with eq_refl => id_refl end))
         Hpos.

(* ---- Slot group 4: the firewall and alignment-rest summation slots ---- *)

Definition feed_ssum_add :
  forall f g : S -> R,
    req (sumd_sumf S enum (fun s : S => plus (f s) (g s)))
        (plus (sumd_sumf S enum f) (sumd_sumf S enum g))
  := @sumd_sum_add S enum.

Definition feed_ssum_le :
  forall f g : S -> R, (forall s : S, le (f s) (g s)) -> le (sumd_sumf S enum f) (sumd_sumf S enum g)
  := @sumd_sum_le S enum.

Definition feed_ralt_sum_ext :
  forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumd_sumf S enum f) (sumd_sumf S enum g)
  := @sumd_sum_ext S enum.

(* ---- Slot group 5: the attention-iteration nonnegativity slot ---- *)

(* Nonnegativity slot: one-step specialization of [sumd_list_sum_nonneg] at
   l := enum; the nil branch closes by [le_refl zero], so no nonemptiness
   premise is needed here. *)
Definition feed_sum_nonneg_h :
  forall f : S -> R, (forall s : S, le zero (f s)) -> le zero (sumd_sumf S enum f)
  := fun (f : S -> R) (Hnn : forall s : S, le zero (f s)) =>
       @sumd_list_sum_nonneg S f enum Hnn.

End SumDCarrierFeed.

(* Assumption audits: every statement of this file is closed under the global context. *)

Print Assumptions feed_rpli_sum_le.
Print Assumptions feed_rpli_sum_ext.
Print Assumptions feed_rpli_sum_add.
Print Assumptions feed_rpli_sum_linear.
Print Assumptions feed_asum_ext.
Print Assumptions feed_asum_add.
Print Assumptions feed_asum_linear.
Print Assumptions feed_b_mult_cancel.
Print Assumptions feed_psum_linear.
Print Assumptions feed_psum_add.
Print Assumptions feed_sumf_pos.
Print Assumptions feed_ssum_add.
Print Assumptions feed_ssum_le.
Print Assumptions feed_ralt_sum_ext.
Print Assumptions feed_sum_nonneg_h.
