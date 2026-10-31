(* UpAblD1S8_TempSoftmaxInstantiation.v -- data-supply pack for Section TsiMains
   Mission. Record, as one inductive datum, the ten statements of that section
   (RI, Token, neg_log_prob, temperature, temperature_pos, sumf, Hsum_ext,
   Hsum_linear, Hsum_add, Hsum_pos; source lines 222-241, transcribed
   verbatim, req-family fields in the bridge delta same-body Id form) and
   supply a witness: one arbitrary RealInterfaceEnhanced instance fixes all
   ten slots at once -- Token := unit single point, temperature := one,
   temperature_pos := one_pos matched directly, sumf := single-point sum,
   extensionality/positivity slots by H tt at the single point, linear/add
   slots by id_refl in one line.
   Dependencies. Stdlib List; the tree S-chain S01_BaseRing through
   S15_TailFEPUp, consumed read-only; no new Require; the source module of
   the packed statements deliberately not required.
   References. TempSoftmaxInstantiation, Section TsiMains; the sum_pos slot
   family precedent (D1-5 batch sibling pack, pack-wide no-redeclaration);
   RealInterfaceEnhanced (S01_BaseRing): its Id-form fields are self-declared
   unsatisfiable on concrete reals, hence the universally quantified
   conditional supply form.
   Constructivity. All slots carried on Set (R RI Set-valued, Id the
   Set-level identity, S01_BaseRing), so the record is informative and
   extractable; zero classical reasoning; the closing Print Assumptions must
   report the witness as closed under the global context. RI and Token are
   quantified by the inductive itself, not by the constructor: a type-valued
   constructor argument is erased by the extractor, inserting a cast at every
   application site of the witness; quantified by the inductive, the
   extracted type stays polymorphic and cast-free. Statement faces verbatim
   from the source module; witness = one constructor application.
   Build. rocq c -native-compiler no -q -Q . "" (Rocq 9.1.0).
 *)

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

(* Pack record: the ten statements, transcribed verbatim (source lines 222-241). *)

Inductive uabd1s8_tsi_pack10 (RI : RealInterfaceEnhanced) (Token : Set) : Type :=
| uabd1s8_tsi_pack10_intro :
      forall (neg_log_prob : list Token -> Token -> @S01_BaseRing.R RI),
        forall (temperature : @S01_BaseRing.R RI),
          @S01_BaseRing.lt RI (@S01_BaseRing.zero RI) temperature ->
          forall (sumf : (Token -> @S01_BaseRing.R RI) -> @S01_BaseRing.R RI),
            (forall f g : Token -> @S01_BaseRing.R RI,
                (forall w : Token, Id (f w) (g w)) ->
                Id (sumf f) (sumf g)) ->
            (forall (a : @S01_BaseRing.R RI) (f : Token -> @S01_BaseRing.R RI),
                Id (sumf (fun w : Token => @S01_BaseRing.mult RI a (f w)))
                   (@S01_BaseRing.mult RI a (sumf f))) ->
            (forall f g : Token -> @S01_BaseRing.R RI,
                Id (sumf (fun w : Token => @S01_BaseRing.plus RI (f w) (g w)))
                   (@S01_BaseRing.plus RI (sumf f) (sumf g))) ->
            (forall f : Token -> @S01_BaseRing.R RI,
                (forall w : Token,
                    @S01_BaseRing.lt RI (@S01_BaseRing.zero RI) (f w)) ->
                @S01_BaseRing.lt RI (@S01_BaseRing.zero RI) (sumf f)) ->
            uabd1s8_tsi_pack10 RI Token.

(* Supply module: one arbitrary RI instance fixes the remaining nine slots at once. *)

Theorem uabd1s8_tsi_pack10_supplied : forall RI : RealInterfaceEnhanced, uabd1s8_tsi_pack10 RI unit.
Proof.
  intro RI.
  exact (uabd1s8_tsi_pack10_intro RI unit           (fun (_ : list unit) (_ : unit) => @S01_BaseRing.zero RI)           (@S01_BaseRing.one RI)           (@S01_BaseRing.one_pos RI)           (fun (f : unit -> @S01_BaseRing.R RI) => f tt)           (fun (f g : unit -> @S01_BaseRing.R RI)              (H : forall w : unit, Id (f w) (g w)) => H tt)           (fun (a : @S01_BaseRing.R RI) (f : unit -> @S01_BaseRing.R RI) =>              @id_refl _ (@S01_BaseRing.mult RI a (f tt)))           (fun (f g : unit -> @S01_BaseRing.R RI) =>              @id_refl _ (@S01_BaseRing.plus RI (f tt) (g tt)))           (fun (f : unit -> @S01_BaseRing.R RI)              (H : forall w : unit,                     @S01_BaseRing.lt RI (@S01_BaseRing.zero RI) (f w)) =>              H tt)).
Qed.

(* Assumption audit. *)

Print Assumptions uabd1s8_tsi_pack10_supplied.
