(* Mission.  Formalization of the properties stated by the theorem/lemma
   statement face of this file.  FA-D1 batch D1-3 slot-expansion batch:
   sum interchange and absolute-value idempotence as referential
   ablation pieces, each slot expanding without restatement.  Slot 1:
   sum_swap_i at UpReqAttnIter.v L152; slot 2: abs_ge_zero_i at
   UpReqAttnIter.v L156; statements verbatim.

   Dependencies.  CW_ConstructiveWorld_219, UpReqSumD, fa53_compat_abs,
   TempSoftmaxInstantiation, AbsLeId; read-only use, base tree untouched;
   requires follow the in-file Require Import surface.

   References.  sumd_sum_swap at UpReqSumD.v (req-face list Fubini;
   header notes sum_swap_i@AttnIter:151 as the same-shape source);
   fa53_abs_ge_zero_id_dec (abs idempotence piece 3, the supply);
   ali_real_abs_ge_zero_id at AbsLeId.v, same-shape precedent;
   p7d_swap_of_sum_eq_list at P7BoundedSoftmaxDeep:107; no-restatement
   cross-check against UpReqAttnMixTime L100/L103/L105 and
   UpReqConcMixSel L767/L770/L772.  Interface-generation adaptation
   (UpReqDist precedent per the merged UpReqMisc5B transcription,
   first-hand grep): the section RIS binder pair removed with
   Abbreviation R := Real and premise faces forward-cast to concrete
   real_eq; slot 2 monomorphised to the canonical Real carrier per its
   own receipt (pack16 control 0/0); statement names verbatim.

   Constructivity.  Zero-admitted statements, mechanically checked; one
   referential ablation theorem per slot; slot 1 transports sumf to the
   concrete list fold sumd_sumf, slot 2 resolves on the canonical carrier.

   Build.  coqc -native-compiler no -q -Q . "" ; magic [436f7121 000160bc].
   ==================================================================== *)

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
Require Import UpReqAlgebra.
Require Import UpReqSumD.
Require Import fa53_compat_abs.
Require Import AbsLeId.
Require TempSoftmaxInstantiation.
Import RealInterfaceEnhancedMod.
(* the interface class in this tree is unparameterized (the UpReqDist
   precedent, per the merged UpReqMisc5B transcription); its carrier
   is the global Cauchy real [Real] *)
Abbreviation R := Real.

(* ============ section S: slot 1, UpReqAttnIter.v L152 (direct supply from
   the sumd instance) ============
   original slot world: inside Context {R : Set}
   {RIS : RealInterfaceEnhancedSetoid R}, the Variable sum_swap_i (statement
   verbatim) reads: forall f : S -> S -> R,
     req (sumf (fun s => sumf (fun s' => f s s')))
         (sumf (fun s' => sumf (fun s => f s s'))).
   transported reading: sumf |-> sumd_sumf S0 en (the concrete list fold),
   supplied verbatim by the source lemma. *)
Section UabD1S2IterSumFeed.
Variable S0 : Set.
Variable enum0 : list S0.

Theorem uabd1s2_iter_sum_swap_i : forall f : S0 -> S0 -> R,
  real_eq (sumd_sumf S0 enum0 (fun s : S0 => sumd_sumf S0 enum0 (fun s' : S0 => f s s')))
      (sumd_sumf S0 enum0 (fun s' : S0 => sumd_sumf S0 enum0 (fun s : S0 => f s s'))).
Proof.
  intro f.
  exact (sumd_sum_swap S0 enum0 f).
Qed.

End UabD1S2IterSumFeed.

(* ============ section A: slot 2, UpReqAttnIter.v L156 (direct supply via
   the assembly-bridge instance) ============
   original slot statement verbatim: forall a : R, le zero a -> req (abs a) a.
   transported form = assembly-bridge instance supply (req as the identity
   equality); it resolves on the canonical carrier, supplied directly by
   fa53 piece 3. *)

Theorem uabd1s2_iter_abs_ge_zero_i :
  forall a : Real, real_le real_zero a -> real_eq (real_abs a) a.
Proof.
  exact ali_real_abs_ge_zero_id.
Qed.

(* ============ closing: Print Assumptions audit at file end for each
   export (G2 trace) ============ *)
Print Assumptions uabd1s2_iter_sum_swap_i.
Print Assumptions uabd1s2_iter_abs_ge_zero_i.
