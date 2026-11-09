(* ConstructiveWorld-Set -- Gibbs detailed-balance ablation pieces of the free-energy attention family. *)

(** * UpAblD1S3_fep_UpReqAttnGibbs: detailed balance of the Boltzmann attention layer.

    Mission.  Formalizes the detailed balance of the Gibbs attention
      interface: the Boltzmann-Gibbs distribution [uabd1s3_fep_ag_dist] and
      the target-only kernel [uabd1s3_fep_ag_kernel] over a finite state
      space, with the main statement
      [uabd1s3_fep_upreqattngibbs_detailed_balance_r] on the [req] carrier.

    Dependencies.  Stdlib [Lists.List] and [Extraction]; requires
      [S01_BaseRing], [S02_CauchyComplete], [S03_QExp], [S04_RealExpLogConv],
      [S05_AlignmentGRPO], [S06_DiffSamplingGibbs], [S07_RealSetoidExpLog],
      [S08_RealMainlineDPO], [S09_EntropyReal], [S10_KVQuantTrig],
      [S11_TP3B5], [S12_B5RecycleSF], [S13_NLiveAudit], [S14_B5BatchBlock],
      [S15_TailFEPUp], [fa56b_ext], [TempSoftmaxInstantiation] of this development.

    References.  This development, UpAblD1S3_fep_UpReqAttnGibbs.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" UpAblD1S3_fep_UpReqAttnGibbs.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 000160bc]. *)
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
Require Import fa56b_ext.
Require Import TempSoftmaxInstantiation.
From Stdlib Require Import List.
From Stdlib Require Import Extraction.

Definition uabd1s3_fep_ag_dist (RI0 : RealInterfaceEnhanced) (X : Set)
  (enum0 : list X) (base_loss : X -> @S01_BaseRing.R RI0)
  (D : @S01_BaseRing.R RI0)
  (D_pos : @S01_BaseRing.lt RI0 (@S01_BaseRing.zero RI0) D)
  (Hne : Not (Id enum0 nil)) (s : X) : @S01_BaseRing.R RI0 :=
  fa56b_boltzmann_prob X enum0 base_loss D D_pos Hne s.

Definition uabd1s3_fep_ag_kernel (RI0 : RealInterfaceEnhanced) (X : Set)
  (enum0 : list X) (base_loss : X -> @S01_BaseRing.R RI0)
  (D : @S01_BaseRing.R RI0)
  (D_pos : @S01_BaseRing.lt RI0 (@S01_BaseRing.zero RI0) D)
  (Hne : Not (Id enum0 nil)) : X -> X -> @S01_BaseRing.R RI0 :=
  fun _ s' => uabd1s3_fep_ag_dist RI0 X enum0 base_loss D D_pos Hne s'.

(* Tree-face re-anchor (per the in-tree precedent of
   UpAblD1S2_e752_UpReqAttnIter.v / UpAblD1S17_UpReqAttnGibbs.v: the class
   RealInterfaceEnhancedSetoid of S07_RealSetoidExpLog is zero-argument in
   this tree and its per-carrier bridge instance tsi_rie_setoid has no tree
   counterpart, so the argumented Class applications raised both the
   missing reference and the Illegal-application face): the setoid req at
   the interface carrier reads as the interface equality Id, and the setoid
   mult as the interface field @S01_BaseRing.mult RI0; the conclusion is
   supplied verbatim by fa56b_detailed_balance of fa56b_ext (its discharged
   Id face). *)
Theorem uabd1s3_fep_upreqattngibbs_detailed_balance_r :
  forall (RI0 : RealInterfaceEnhanced) (X : Set) (enum0 : list X)
         (base_loss : X -> @S01_BaseRing.R RI0) (D : @S01_BaseRing.R RI0)
         (D_pos : @S01_BaseRing.lt RI0 (@S01_BaseRing.zero RI0) D)
         (Hne : Not (Id enum0 nil)) (s s' : X),
    Id (@S01_BaseRing.mult RI0
          (uabd1s3_fep_ag_dist RI0 X enum0 base_loss D D_pos Hne s)
          (uabd1s3_fep_ag_kernel RI0 X enum0 base_loss D D_pos Hne s s'))
       (@S01_BaseRing.mult RI0
          (uabd1s3_fep_ag_dist RI0 X enum0 base_loss D D_pos Hne s')
          (uabd1s3_fep_ag_kernel RI0 X enum0 base_loss D D_pos Hne s' s)).
Proof.
  intros RI0 X enum0 base_loss D D_pos Hne s s'.
  exact (fa56b_detailed_balance X enum0 base_loss D D_pos Hne s s').
Qed.

Set Extraction Output Directory "_tuabd1s3_g3out".
Extraction "tuabd1s3_G3_fep_ag_dist.ml" uabd1s3_fep_ag_dist.

Print Assumptions uabd1s3_fep_upreqattngibbs_detailed_balance_r.
