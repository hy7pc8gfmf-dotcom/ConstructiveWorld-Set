(* ConstructiveWorld-Set -- FA-D1S3 D1-5 sum_pos completion over the finite-sum carrier, nine aligned statement faces. *)

(** * UpAblD1S3_sum_pos_AlignIdUnclosed: positivity of finite sums, one statement face per host use site.

    Mission.  The FA-D1S3 D1-5 sum_pos completion: for a nonempty enumeration
      and a pointwise positive function the finite sum is positive.  Nine
      aligned statement faces, each realized by [fa57_sum_carrier_realizes]
      or [sumd_sum_pos]: the carrier pairs [uabd1s3_alignidunclosed],
      [uabd1s3_tempsoftmaxinst] ([_Hsum_pos]), [uabd1s3_upreqalign3],
      [uabd1s3_upreqalignclose], [uabd1s3_upreqattngibbs] (each
      [_carrier]/[_sum_pos]), and the sumf pairs
      [uabd1s3_upreqentropydeficittemp], [uabd1s3_upreqentropymonosplit],
      [uabd1s3_upreqentropyuniquetemp], [uabd1s3_upreqtempdefs] (each
      [_sumf]/[_real_sum_pos_preserved]).

    Dependencies.  [S01_BaseRing] through [S15_TailFEPUp], [fa57_ext],
      [TempSoftmaxInstantiation], [UpReqSumD]; Stdlib [List], [Extraction].

    References.  FA-D1S3 D1-5; this development, statement names carried over
      verbatim from the baseline module in ConstructiveWorld-Main.

    Constructivity.  No axioms and no admitted statements; statements are
      carried at the [Set] layer; [Print Assumptions] reports Closed.

    Build.  [coqc -native-compiler no -q -Q . "" UpAblD1S3_sum_pos_AlignIdUnclosed.v]
      under Rocq 9.1; the artifact starts with [436f7121 000160bc]. *)
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
Require Import fa57_ext.
Require Import TempSoftmaxInstantiation.
From Stdlib Require Import List.
From Stdlib Require Import Extraction.

Definition uabd1s3_alignidunclosed_carrier (RI0 : RealInterfaceEnhanced) (X : Set)
  (enum0 : list X) (Hne : Not (Id enum0 nil))
  : (X -> @S01_BaseRing.R RI0) -> @S01_BaseRing.R RI0 :=
  projT1 (fa57_sum_carrier_realizes X enum0 Hne).

Theorem uabd1s3_alignidunclosed_sum_pos :
  forall (RI0 : RealInterfaceEnhanced) (X : Set) (enum0 : list X)
         (Hne : Not (Id enum0 nil)) (f : X -> @S01_BaseRing.R RI0),
    (forall s : X,
       @S01_BaseRing.lt RI0 (@S01_BaseRing.zero RI0) (f s)) ->
    @S01_BaseRing.lt RI0 (@S01_BaseRing.zero RI0)
      (uabd1s3_alignidunclosed_carrier RI0 X enum0 Hne f).
Proof.
  intros RI0 X enum0 Hne f Hf.
  exact (fst (projT2 (fa57_sum_carrier_realizes X enum0 Hne)) f Hf).
Qed.

Set Extraction Output Directory "_tuabd1s3_g3out".
Extraction "tuabd1s3_G3_alignidunclosed_carrier.ml" uabd1s3_alignidunclosed_carrier.

Print Assumptions uabd1s3_alignidunclosed_sum_pos.

(* ============================ Section 1: FA-D1S3 D1-5 ============================ *)
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
Require Import fa57_ext.
From Stdlib Require Import List.
From Stdlib Require Import Extraction.

Definition uabd1s3_tempsoftmaxinst_carrier (RI0 : RealInterfaceEnhanced)
  (Tok : Set) (enum0 : list Tok) (Hne : Not (Id enum0 nil))
  : (Tok -> @S01_BaseRing.R RI0) -> @S01_BaseRing.R RI0 :=
  projT1 (fa57_sum_carrier_realizes Tok enum0 Hne).

Theorem uabd1s3_tempsoftmaxinst_Hsum_pos :
  forall (RI0 : RealInterfaceEnhanced) (Tok : Set) (enum0 : list Tok)
         (Hne : Not (Id enum0 nil)) (f : Tok -> @S01_BaseRing.R RI0),
    (forall w : Tok, @S01_BaseRing.lt RI0 (@S01_BaseRing.zero RI0) (f w)) ->
    @S01_BaseRing.lt RI0 (@S01_BaseRing.zero RI0)
      (uabd1s3_tempsoftmaxinst_carrier RI0 Tok enum0 Hne f).
Proof.
  intros RI0 Tok enum0 Hne f Hf.
  exact (fst (projT2 (fa57_sum_carrier_realizes Tok enum0 Hne)) f Hf).
Qed.

Set Extraction Output Directory "_tuabd1s3_g3out".
Extraction "tuabd1s3_G3_tempsoftmaxinst_carrier.ml" uabd1s3_tempsoftmaxinst_carrier.

Print Assumptions uabd1s3_tempsoftmaxinst_Hsum_pos.

(* ============================ Section 2: statement face of uabd1s3_upreqalign3_carrier / uabd1s3_upreqalign3_sum_pos ============================ *)
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
Require Import fa57_ext.
Require Import TempSoftmaxInstantiation.
From Stdlib Require Import List.
From Stdlib Require Import Extraction.

Definition uabd1s3_upreqalign3_carrier (RI0 : RealInterfaceEnhanced) (X : Set)
  (enum0 : list X) (Hne : Not (Id enum0 nil))
  : (X -> @S01_BaseRing.R RI0) -> @S01_BaseRing.R RI0 :=
  projT1 (fa57_sum_carrier_realizes X enum0 Hne).

Theorem uabd1s3_upreqalign3_sum_pos :
  forall (RI0 : RealInterfaceEnhanced) (X : Set) (enum0 : list X)
         (Hne : Not (Id enum0 nil)) (f : X -> @S01_BaseRing.R RI0),
    (forall s : X,
       @S01_BaseRing.lt RI0 (@S01_BaseRing.zero RI0) (f s)) ->
    @S01_BaseRing.lt RI0 (@S01_BaseRing.zero RI0)
      (uabd1s3_upreqalign3_carrier RI0 X enum0 Hne f).
Proof.
  intros RI0 X enum0 Hne f Hf.
  exact (fst (projT2 (fa57_sum_carrier_realizes X enum0 Hne)) f Hf).
Qed.

Set Extraction Output Directory "_tuabd1s3_g3out".
Extraction "tuabd1s3_G3_upreqalign3_carrier.ml" uabd1s3_upreqalign3_carrier.

Print Assumptions uabd1s3_upreqalign3_sum_pos.

(* ============================ Section 3: FA-D1S3 D1-5 sum_pos completion (the sum_pos_UpReqAlignClose branch) ============================ *)
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
Require Import fa57_ext.
Require Import TempSoftmaxInstantiation.
From Stdlib Require Import List.
From Stdlib Require Import Extraction.

Definition uabd1s3_upreqalignclose_carrier (RI0 : RealInterfaceEnhanced) (X : Set)
  (enum0 : list X) (Hne : Not (Id enum0 nil))
  : (X -> @S01_BaseRing.R RI0) -> @S01_BaseRing.R RI0 :=
  projT1 (fa57_sum_carrier_realizes X enum0 Hne).

Theorem uabd1s3_upreqalignclose_sum_pos :
  forall (RI0 : RealInterfaceEnhanced) (X : Set) (enum0 : list X)
         (Hne : Not (Id enum0 nil)) (f : X -> @S01_BaseRing.R RI0),
    (forall s : X,
       @S01_BaseRing.lt RI0 (@S01_BaseRing.zero RI0) (f s)) ->
    @S01_BaseRing.lt RI0 (@S01_BaseRing.zero RI0)
      (uabd1s3_upreqalignclose_carrier RI0 X enum0 Hne f).
Proof.
  intros RI0 X enum0 Hne f Hf.
  exact (fst (projT2 (fa57_sum_carrier_realizes X enum0 Hne)) f Hf).
Qed.

Set Extraction Output Directory "_tuabd1s3_g3out".
Extraction "tuabd1s3_G3_upreqalignclose_carrier.ml" uabd1s3_upreqalignclose_carrier.

Print Assumptions uabd1s3_upreqalignclose_sum_pos.

(* ============================ Section 4: statement face of uabd1s3_upreqattngibbs_carrier / uabd1s3_upreqattngibbs_sum_pos ============================ *)
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
Require Import fa57_ext.
Require Import TempSoftmaxInstantiation.
From Stdlib Require Import List.
From Stdlib Require Import Extraction.

Definition uabd1s3_upreqattngibbs_carrier (RI0 : RealInterfaceEnhanced) (X : Set)
  (enum0 : list X) (Hne : Not (Id enum0 nil))
  : (X -> @S01_BaseRing.R RI0) -> @S01_BaseRing.R RI0 :=
  projT1 (fa57_sum_carrier_realizes X enum0 Hne).

Theorem uabd1s3_upreqattngibbs_sum_pos :
  forall (RI0 : RealInterfaceEnhanced) (X : Set) (enum0 : list X)
         (Hne : Not (Id enum0 nil)) (f : X -> @S01_BaseRing.R RI0),
    (forall s : X,
       @S01_BaseRing.lt RI0 (@S01_BaseRing.zero RI0) (f s)) ->
    @S01_BaseRing.lt RI0 (@S01_BaseRing.zero RI0)
      (uabd1s3_upreqattngibbs_carrier RI0 X enum0 Hne f).
Proof.
  intros RI0 X enum0 Hne f Hf.
  exact (fst (projT2 (fa57_sum_carrier_realizes X enum0 Hne)) f Hf).
Qed.

Set Extraction Output Directory "_tuabd1s3_g3out".
Extraction "tuabd1s3_G3_upreqattngibbs_carrier.ml" uabd1s3_upreqattngibbs_carrier.

Print Assumptions uabd1s3_upreqattngibbs_sum_pos.

(* ============================ Section 5: FA-D1S3 D1-5 sum_pos completion (the _pos_UpReqEntropyDeficitTemp branch) ============================ *)
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
From Stdlib Require Import Extraction.
Import RealInterfaceEnhancedMod.

Definition uabd1s3_upreqentropydeficittemp_sumf (S0 : Set) (enum0 : list S0) (f : S0 -> Real) : Real :=
  sumd_sumf S0 enum0 f.

Theorem uabd1s3_upreqentropydeficittemp_real_sum_pos_preserved :
  forall (S0 : Set) (enum0 : list S0) (Hne : Not (enum0 = nil)) (f : S0 -> Real),
    (forall s : S0, real_lt real_zero (f s)) ->
    real_lt real_zero (uabd1s3_upreqentropydeficittemp_sumf S0 enum0 f).
Proof.
  intros S0 enum0 Hne f Hf.
  exact (sumd_sum_pos S0 enum0 f Hne Hf).
Qed.

Set Extraction Output Directory "_tuabd1s3_g3out".
Extraction "tuabd1s3_G3_upreqentropydeficittemp_sumf.ml" uabd1s3_upreqentropydeficittemp_sumf.

Print Assumptions uabd1s3_upreqentropydeficittemp_real_sum_pos_preserved.

(* ============================ Section 6: FA-D1S3 D1-5 sum_pos completion (the um_pos_UpReqEntropyMonoSplit branch) ============================ *)
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
From Stdlib Require Import Extraction.
Import RealInterfaceEnhancedMod.

Definition uabd1s3_upreqentropymonosplit_sumf (S0 : Set) (enum0 : list S0) (f : S0 -> Real) : Real :=
  sumd_sumf S0 enum0 f.

Theorem uabd1s3_upreqentropymonosplit_real_sum_pos_preserved :
  forall (S0 : Set) (enum0 : list S0) (Hne : Not (enum0 = nil)) (f : S0 -> Real),
    (forall s : S0, real_lt real_zero (f s)) ->
    real_lt real_zero (uabd1s3_upreqentropymonosplit_sumf S0 enum0 f).
Proof.
  intros S0 enum0 Hne f Hf.
  exact (sumd_sum_pos S0 enum0 f Hne Hf).
Qed.

Set Extraction Output Directory "_tuabd1s3_g3out".
Extraction "tuabd1s3_G3_upreqentropymonosplit_sumf.ml" uabd1s3_upreqentropymonosplit_sumf.

Print Assumptions uabd1s3_upreqentropymonosplit_real_sum_pos_preserved.

(* ============================ Section 7: FA-D1S3 D1-5 sum_pos completion (the m_pos_UpReqEntropyUniqueTemp branch) ============================ *)
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
From Stdlib Require Import Extraction.
Import RealInterfaceEnhancedMod.

Definition uabd1s3_upreqentropyuniquetemp_sumf (S0 : Set) (enum0 : list S0) (f : S0 -> Real) : Real :=
  sumd_sumf S0 enum0 f.

Theorem uabd1s3_upreqentropyuniquetemp_real_sum_pos_preserved :
  forall (S0 : Set) (enum0 : list S0) (Hne : Not (enum0 = nil)) (f : S0 -> Real),
    (forall s : S0, real_lt real_zero (f s)) ->
    real_lt real_zero (uabd1s3_upreqentropyuniquetemp_sumf S0 enum0 f).
Proof.
  intros S0 enum0 Hne f Hf.
  exact (sumd_sum_pos S0 enum0 f Hne Hf).
Qed.

Set Extraction Output Directory "_tuabd1s3_g3out".
Extraction "tuabd1s3_G3_upreqentropyuniquetemp_sumf.ml" uabd1s3_upreqentropyuniquetemp_sumf.

Print Assumptions uabd1s3_upreqentropyuniquetemp_real_sum_pos_preserved.

(* ============================ Section 8: statement face of uabd1s3_upreqtempdefs_sumf / uabd1s3_upreqtempdefs_real_sum_pos_preserved ============================ *)
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
From Stdlib Require Import Extraction.
Import RealInterfaceEnhancedMod.

Definition uabd1s3_upreqtempdefs_sumf (S0 : Set) (enum0 : list S0) (f : S0 -> Real) : Real :=
  sumd_sumf S0 enum0 f.

Theorem uabd1s3_upreqtempdefs_real_sum_pos_preserved :
  forall (S0 : Set) (enum0 : list S0) (Hne : Not (enum0 = nil)) (f : S0 -> Real),
    (forall s : S0, real_lt real_zero (f s)) ->
    real_lt real_zero (uabd1s3_upreqtempdefs_sumf S0 enum0 f).
Proof.
  intros S0 enum0 Hne f Hf.
  exact (sumd_sum_pos S0 enum0 f Hne Hf).
Qed.

Set Extraction Output Directory "_tuabd1s3_g3out".
Extraction "tuabd1s3_G3_upreqtempdefs_sumf.ml" uabd1s3_upreqtempdefs_sumf.

Print Assumptions uabd1s3_upreqtempdefs_real_sum_pos_preserved.
