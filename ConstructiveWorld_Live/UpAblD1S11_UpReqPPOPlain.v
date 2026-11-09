(* Mission.  Formalization of the properties stated by the theorem/lemma
   statement face of this file.  FA-D1S11 data-supply grand wrapper, ladder
   seven, piece 1: a standalone companion module that supplies the remaining
   ReqPPOPlain slots of UpReqPPOPlain.v (section 2: pi, p_old, eps, Hpos;
   section 3: R, RIS, RDP, S, sumf, rpli_sum_le, rpli_sum_ext, rpli_sum_add,
   rpli_sum_linear, pi, p_old, Hpos, Hnorm) through two wrapper records plus
   two instance-supply export theorems.

   Dependencies.  CW_ConstructiveWorld_219; UpReqAlign (definition file of
   Z_align_req, same Require surface as S8); UpReqRDF (definition file of the
   ReqDiffPlain class); read-only use, no git, no registry increments; the
   library requires follow the in-file Require Import surface.

   References.  Source file UpReqPPOPlain.v L306-308 and L386-408; S8
   precedent UpAblD1S8_UpReqPPOPlain (piece 3, pack5); RealEnhancedReal at
   S07_RealSetoidExpLog.v:8566 inside RealInterfaceEnhancedMod (qualified
   name reference).  Interface-generation adaptation (UpReqDist precedent
   per the merged UpReqMisc5B transcription, first-hand grep): binder
   pairs (R : Set) (RIS : RealInterfaceEnhancedSetoid R) and @ReqDiffPlain
   shells are carrier-ized away with Abbreviation R := Real; premise
   predicate faces forward-cast to concrete real_lt/real_le/real_eq; the
   space slot monomorphised to unit (pack16 control 0/0); statement
   names verbatim.

   Constructivity.  Zero-admitted statements, mechanically checked; both
   export theorems close by Qed and keep their Print Assumptions audits.

   Build.  coqc -native-compiler no -q -Q . "" ; magic [436f7121 000160bc].
   ==================================================================== *)

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
Require Import UpReqRDF.
Import RealInterfaceEnhancedMod.
(* the interface class in this tree is unparameterized (the UpReqDist
   precedent, per the merged UpReqMisc5B transcription); its carrier
   is the global Cauchy real [Real] *)
Abbreviation R := Real.

(* ============ wrapper record form (section 2, remaining 3 slots): cf. source file L306-308 ============ *)
(* the leading 6 telescope positions = the section-2 slots already closed by
   S8 (carried as context conditions, not counted as positions here) *)

Inductive uabd1s11_ppo2_pack3 : Type :=
| uabd1s11_ppo2_pack3_intro :
      forall (RDP : ReqDiffPlain),
        forall (sumf : (unit -> R) -> R),
          (forall f : unit -> R,
              (forall s : unit, real_le zero (f s)) -> real_le zero (sumf f)) ->
          forall (pi p_old : unit -> R),
            forall (eps : R),
              (forall s : unit, real_lt zero (p_old s)) ->
              uabd1s11_ppo2_pack3.

(* ============ wrapper record form (section 3, all 11 slots): cf. source file L386-408 ============ *)

Inductive uabd1s11_ppo3_pack11 : Type :=
| uabd1s11_ppo3_pack11_intro :
    forall (RDP : ReqDiffPlain),
      forall (sumf : (unit -> R) -> R),
          (forall f g : unit -> R,
              (forall s : unit, real_le (f s) (g s)) -> real_le (sumf f) (sumf g)) ->
          (forall f g : unit -> R,
              (forall s : unit, real_eq (f s) (g s)) -> real_eq (sumf f) (sumf g)) ->
          (forall f g : unit -> R,
              real_eq (sumf (fun s : unit => plus (f s) (g s)))
                  (plus (sumf f) (sumf g))) ->
          (forall (a : R) (f : unit -> R),
              real_eq (sumf (fun s : unit => mult a (f s))) (mult a (sumf f))) ->
          forall (pi p_old : unit -> R),
            (forall s : unit, real_lt zero (p_old s)) ->
            real_eq (sumf pi) one ->
            uabd1s11_ppo3_pack11.

(* ============ dependency module: one feed fixes an arbitrary RDP instance
   (RDP taken in universally conditional form) ============ *)

Theorem uabd1s11_ppo2_pack3_supplied :
  forall RDP : ReqDiffPlain,
    uabd1s11_ppo2_pack3.
Proof.
  intro RDP.
  exact (uabd1s11_ppo2_pack3_intro
           RDP
           (fun f : unit -> Real => f tt)
           (fun (f : unit -> Real)
              (H : forall s : unit, real_le zero (f s)) => H tt)
           (fun _ : unit => one)
           (fun _ : unit => one)
           one
           (fun _ : unit =>
              @RealInterfaceEnhancedMod.one_pos
                RealInterfaceEnhancedMod.RealEnhancedReal)).
Qed.

Theorem uabd1s11_ppo3_pack11_supplied :
  forall RDP : ReqDiffPlain,
    uabd1s11_ppo3_pack11.
Proof.
  intro RDP.
  exact (uabd1s11_ppo3_pack11_intro
           RDP
           (fun f : unit -> Real => f tt)
           (fun (f g : unit -> Real)
              (H : forall s : unit, real_le (f s) (g s)) => H tt)
           (fun (f g : unit -> Real)
              (H : forall s : unit, real_eq (f s) (g s)) => H tt)
           (fun (f g : unit -> Real) =>
              @req_refl RealInterfaceEnhancedMod.RealEnhancedReal
                (plus (f tt) (g tt)))
           (fun (a : Real) (f : unit -> Real) =>
              @req_refl RealInterfaceEnhancedMod.RealEnhancedReal
                (mult a (f tt)))
           (fun _ : unit => one)
           (fun _ : unit => one)
           (fun _ : unit =>
              @RealInterfaceEnhancedMod.one_pos
                RealInterfaceEnhancedMod.RealEnhancedReal)
           (@req_refl RealInterfaceEnhancedMod.RealEnhancedReal one)).
Qed.

(* ============ assumption-surface closure declaration ============ *)

Print Assumptions uabd1s11_ppo2_pack3_supplied.
Print Assumptions uabd1s11_ppo3_pack11_supplied.
