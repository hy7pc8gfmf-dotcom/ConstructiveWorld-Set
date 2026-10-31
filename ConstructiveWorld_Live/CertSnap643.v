(* ===================================================================== *)
(* CertSnap643.v — K3 certification snapshot data module (self-contained) *)
(* Mission. Register the tree-level certification fingerprint data of the  *)
(*   643-file tree: the order fingerprint / file count / byte count / line *)
(*   count / the three redline counts / the five evidence-face counts /    *)
(*   the .vo magic number / the previous-generation tree comparison,       *)
(*   encoded as Records and lists, for downstream Require or excerpting.   *)
(* Dependencies. Zero library-tree Require; a single standard-library      *)
(*   import, Stdlib.Strings.String (the Rocq 9.1 prelude does not preload  *)
(*   string; it is required to carry the human-readable fingerprint data); *)
(*   list / nat / bool / option all come from the prelude.                 *)
(* References. Baseline tree ConstructiveWorld_Live/ with its 643 .v files *)
(*   and order.txt with 643 names; all fingerprint values are authoritative*)
(*   in the snapshot/manifest fields of this file.                         *)
(* Constructivity. Pure Set-carried data + all-Defined functions + Boolean *)
(*   self-consistency; no assumption-introducing commands, no unproved     *)
(*   statement closers, no Prop-sort statements.                           *)
(* Build. Standalone compile: rocq c CertSnap643.v (zero library-tree      *)
(*   dependencies; any target pool can embed it). Data sourced file-by-file*)
(*   from cert-snapshot-643.json (nested-comment-stripped scan); the       *)
(*   extraction self-check runs in an isolated-pool probe (Obj.magic = 0). *)
(* ===================================================================== *)

From Stdlib.Strings Require Import String.

(* ---- Redline counts (word-boundary caliber over the statement face after nested-comment stripping) ---- *)
Record RedlineCounts : Set := mkRL {
  rl_axiom : nat;        (* occurrence count recorded by the rl_axiom field, expected 0 *)
  rl_admitted : nat;     (* occurrence count recorded by the rl_admitted field, expected 0 *)
  rl_classical : nat     (* occurrence count of the Classical*/classic/excluded_middle* word family, expected 0 *)
}.

(* ---- Evidence-face counts (line-start lexing, after comment stripping) ---- *)
Record EvidenceFace : Set := mkEV {
  ev_print_assumptions : nat;   (* line-start occurrences of Print Assumptions: 4221 *)
  ev_extraction : nat;          (* line-start occurrences of Extraction commands: 243 *)
  ev_vm_compute : nat;          (* line-start occurrences of vm_compute: 24 *)
  ev_eval_vm_compute : nat;     (* line-start occurrences of Eval vm_compute: 35 *)
  ev_require_extraction : nat   (* line-start occurrences of Require Extraction: 128 *)
}.

(* ---- Per-file fingerprint entries ---- *)
Record FileFP : Set := mkFP {
  fp_file : string;      (* library file name (top level, matching order.txt after stripping the anchor column) *)
  fp_md5 : string;       (* md5 (byte level) *)
  fp_bytes : nat;        (* byte count *)
  fp_lines : nat         (* line count *)
}.

(* ---- Tree-level snapshot ---- *)
Record CertSnapshot643 : Set := mkSnap {
  snap_tree : string;              (* baseline tree *)
  snap_order_md5 : string;         (* order.txt md5 *)
  snap_order_lines : nat;          (* order.txt line count (643 names after stripping the # anchor column) *)
  snap_coqproject_md5 : string;    (* _CoqProject md5 *)
  snap_file_count : nat;           (* .v file count: 643 *)
  snap_total_bytes : nat;          (* total tree bytes *)
  snap_total_lines : nat;          (* total tree lines *)
  snap_redline : RedlineCounts;    (* the three redline counts (expected all zero) *)
  snap_evidence : EvidenceFace;    (* the five evidence-face counts *)
  snap_vo_count : nat;             (* .vo count of the reference vo tree: 643 *)
  snap_vo_magic : string;          (* .vo magic number 436f712100015ff4 *)
  snap_vo_magic_bad : nat;         (* count of files whose magic mismatches (checked file-by-file over the full set): 0 *)
  snap_vo_total_bytes : nat;       (* total bytes of the vo tree *)
  snap_r134_count : nat;           (* previous-generation tree at state #144: 691 files *)
  snap_r134_deleted : nat;         (* deleted files 48 (two waves, 35+13; name-by-name match at K2) *)
  snap_r134_added : nat;           (* added: 0 *)
  snap_r134_changed : nat;         (* rewritten during the disassembly wave: 631 *)
  snap_r134_unchanged : nat;       (* byte-identical untouched: 12 *)
  snap_chain_md5 : string          (* md5 of the per-file md5 chain (single-field tree-fingerprint recheck anchor) *)
}.

Definition snapshot : CertSnapshot643 :=
  mkSnap
    "ConstructiveWorld_Live/"
    "c7ac7a1991ccf9801b4f74240327408a"
    643
    "45c51ca5ee5f942eb1e2cc734093302a"
    643
    21509575
    414400
    (mkRL 0 0 0)
    (mkEV 4221 243 24 35 128)
    643
    "436f712100015ff4"
    0
    26150623
    691
    48
    0
    631
    12
    "75241eb3de81676c9f38493d00733897".

(* ---- 643 per-file fingerprints (generated programmatically, in lexicographic file-name order) ---- *)
Definition manifest : list FileFP :=
  cons (mkFP "AbsLeId.v" "1dc877c64a58277e06f08c48877d51ac" 4751 106) (
  cons (mkFP "AbsLeIdReal53.v" "b69e189cf242fd6137fa4a9fb5434b1d" 6218 134) (
  cons (mkFP "AbsSqClose.v" "98ccf6ee681d9bea03ebc1861269d4de" 14454 326) (
  cons (mkFP "AlignIdUnclosed.v" "38857a18d9589f5ec87e37c5d2c3db9c" 18575 333) (
  cons (mkFP "ArctanGeomTail.v" "e7e44ac2c5a1b46a0de8efde378a7493" 13258 292) (
  cons (mkFP "AttnDoeblin.v" "4af3507b3a9886963ab6e06f74f025b8" 36734 797) (
  cons (mkFP "AttnHardLimit218.v" "2b7d5f82f4e4362ecc4e7edf873efee7" 57164 1269) (
  cons (mkFP "AttnLogSumExpBound.v" "d40680962934485389698ea384bfd1e5" 23673 509) (
  cons (mkFP "AttnSqrt.v" "9e20c4c547df2d7b7996db6beaf9dfeb" 10574 237) (
  cons (mkFP "BBDBridgeSupply.v" "a0699c9308dae32321afd3d7e3f3f679" 8389 159) (
  cons (mkFP "BanachNoHyp.v" "864d8bc5d2a9cca9319930c09cbf0d7f" 27820 535) (
  cons (mkFP "BanachNoHypNorm.v" "eeaf4d0eb54029343cf7895589442425" 6650 111) (
  cons (mkFP "BanachS3Chain.v" "0a34bbb55a629087158535bf21372574" 8513 181) (
  cons (mkFP "BetaLower.v" "a998ed1ed0594e6d831197fa8047799c" 23374 481) (
  cons (mkFP "BeukersIdentity.v" "f0391d996861bc1b69a322a5a387094d" 9179 219) (
  cons (mkFP "BeukersLists.v" "969d08a606973ffb88838be2f396c52a" 19230 520) (
  cons (mkFP "BeukersVariant.v" "ccd4476b3d70f807a5b9197b690bd80d" 24004 493) (
  cons (mkFP "BoltzmannBridgeDischarge.v" "4530db077822e9615c05b89273a40c70" 9934 165) (
  cons (mkFP "CW220_Extensions.v" "7d741062e1d375cd4ad126b471d6a34e" 98251 1663) (
  cons (mkFP "ConcMixSelFeed.v" "82934cee41eb7cbadd346c580d2f100e" 13059 300) (
  cons (mkFP "CurriculumOptTemp.v" "a0989cd21cdc22da179ad09d975e34b3" 9118 175) (
  cons (mkFP "DTPT.v" "c7a354bb254375636511cfb47a07d74a" 154035 3865) (
  cons (mkFP "DTPT_Bridge.v" "53016eed81866faf2d72d8fb1d545b6e" 42148 873) (
  cons (mkFP "DTPT_Bridge_All.v" "e2a4615f560ee48d5477976883354e74" 13641 281) (
  cons (mkFP "DTPT_Bridge_Dep.v" "3db0cb2014ffdc855f1c399021b1955b" 14096 287) (
  cons (mkFP "DTPT_Bridge_Dig.v" "c0aa2b50f81f686bf1017b349e3f3133" 10518 256) (
  cons (mkFP "DTPT_Bridge_Rot.v" "827bd4644fd6812072e87225ca5e070b" 24624 551) (
  cons (mkFP "DTPT_DigTheory.v" "2ed7345d1711219ccca3cce0493f7298" 30070 814) (
  cons (mkFP "DTPT_Entropy.v" "4d6163881c9e16a991a4e1a64ffcbf20" 132847 3307) (
  cons (mkFP "DTPT_Extract.v" "979e89f1efdd12f07215f3f9e64a3b8d" 8001 179) (
  cons (mkFP "DTPT_Rotation.v" "4f6170fb59ab333872dc0631e5266fcf" 123126 2898) (
  cons (mkFP "DTPT_Truth.v" "fe4ab8d0efb39c040230576a57e8ce57" 66159 1603) (
  cons (mkFP "DecBridge6.v" "baecee3965dcdedff0accf0e7811db51" 6217 146) (
  cons (mkFP "DenPosGeneral.v" "bdf72389edd5fe605f81634bf7263015" 5533 126) (
  cons (mkFP "DenPosGeneralClose.v" "a807ad0eba394c7fa419eb67d922a562" 4610 83) (
  cons (mkFP "EnergyTempMonoB.v" "b1e09f49c7e1638a764eecbf272b26bc" 12984 240) (
  cons (mkFP "EngelWeighted.v" "a5355d46207eb3ee7a7ffa131a2c19ad" 26430 622) (
  cons (mkFP "EntropyMonoSplitInst.v" "b46e71f9450da12667d0aa1a0e6a2056" 15515 265) (
  cons (mkFP "EntropyUnsatMark.v" "04df1b064d42cfd2346274e6ccbe3456" 6413 113) (
  cons (mkFP "EpsOptimalReach.v" "461d06059d5be33d3974aedcbd9251d2" 8549 188) (
  cons (mkFP "ExpLinearLower.v" "1cb7a3f7778c52482a22ceb390934eba" 12601 264) (
  cons (mkFP "ExpNegFinale.v" "66fc13c097e5b3cb4edcb516f1dafc61" 6621 138) (
  cons (mkFP "ExpNegPos.v" "fe7134d0a9694f28be9e7eda465a9af9" 14828 323) (
  cons (mkFP "ExpNegPosUp.v" "ea42642d6f4492abf38bcee1b557b79d" 2944 52) (
  cons (mkFP "ExpOneEnvelope.v" "a184373c6608c85b2a92fb5e53a20a70" 19199 468) (
  cons (mkFP "FepIdConsume.v" "34e9477b43aab20cfdaf03b624d90717" 12981 222) (
  cons (mkFP "FepIdentClass.v" "f2707007cf6c8df4e0ad6f07284e6033" 34900 570) (
  cons (mkFP "FirewallReqDischarge.v" "9e528f70f051fe8713e46cccec63aaf5" 13239 219) (
  cons (mkFP "ForwardKLAdjudication.v" "57c11a7dacb5b1a686eb833f7dc1eceb" 9578 125) (
  cons (mkFP "FreeEnergyKLGap.v" "ab5d48c974e4a67914fada4cf27b86e6" 32907 663) (
  cons (mkFP "G01_CoreMicro.v" "da2d8355ad1985f7663817856a37f289" 35099 772) (
  cons (mkFP "G02_Debt.v" "9f0d056fb3f05d89788063af54f2a1dc" 38260 736) (
  cons (mkFP "G04ProjHook.v" "97c30ce8f1831ad7ade54a0a66d0af3b" 12363 258) (
  cons (mkFP "G04_ProjFam.v" "3b803fc863a0cf5844e83268f2b79f1d" 91187 1976) (
  cons (mkFP "G05_LogSmall.v" "7d65535aa212f243d135bd7c470f8105" 70537 1306) (
  cons (mkFP "G06_BForm.v" "156378d858a121b544a8522225f15601" 63284 1187) (
  cons (mkFP "G07_KLWall.v" "3dc75705341c87a54ff0626a73ebf2f2" 165166 2932) (
  cons (mkFP "G08_Gibbs.v" "85afbc59ec864e0c80032efdae9e19cc" 79519 1517) (
  cons (mkFP "G09_MiscSmall.v" "8c57659a8ac09efe02ec0c3ef2b93a15" 54137 960) (
  cons (mkFP "G10_LoebFam.v" "56e25bda5639048d656f8ea12c0cd74a" 165059 3666) (
  cons (mkFP "G11_IDLFam.v" "a1069f33aa5db14e70247d911723059f" 79807 1827) (
  cons (mkFP "G12_ZPosFam.v" "790005d531721e4f842514895bb94642" 142146 2210) (
  cons (mkFP "G13_EvictFam.v" "d7c9cb80f200eab268324b61fe0321d9" 47680 962) (
  cons (mkFP "GibbsAssembly.v" "241ae3cae828da9fe5c8570ad1d1c73b" 30096 486) (
  cons (mkFP "GibbsAttractor.v" "455b9fda8ded90384f9921ffcd95c21d" 19997 364) (
  cons (mkFP "GibbsFamilyExt.v" "89b2259908323332546eebba3357f107" 19434 417) (
  cons (mkFP "Hanson3Pow.v" "f9bea5e861dd53ee829b3710a99e9fc8" 11741 275) (
  cons (mkFP "HansonLcm.v" "515b83f9b318c5882361a4741b4d2475" 12983 254) (
  cons (mkFP "IdSlotTranslate.v" "e7317a94e6318a0cb57a3380d195a2db" 10225 200) (
  cons (mkFP "InstBWdClose.v" "d9704dc39d747d45adc7fcda55fa06ea" 2469 46) (
  cons (mkFP "InvPosLtCompat.v" "73f2178754779b4d0209921c76492443" 7438 144) (
  cons (mkFP "KLWallClosed.v" "2f1b1defdc9973cb796f71fccbda25ac" 21790 460) (
  cons (mkFP "LMCarrierExt.v" "d866c8ebfc62247ebcc8436eaf5ebc89" 17836 346) (
  cons (mkFP "Ln2Bridge.v" "da88ecb16672f0d39d26d757136420bf" 32830 680) (
  cons (mkFP "Ln2Escape.v" "803768601312fdf45e794d6d32b16764" 25168 582) (
  cons (mkFP "Ln2Integrality.v" "558feb0ba638b515d387b0aabff32a02" 17893 448) (
  cons (mkFP "LoHiSqueeze.v" "08e73cccc57c925cb2389d801b87ade8" 10113 192) (
  cons (mkFP "LogTwoBridge.v" "578fe5c4410fbe5e5395c38f8690f40a" 12565 220) (
  cons (mkFP "LogTwoEnvelope.v" "f1f8e98ac58c79c1e9b045cfded83aa9" 26962 600) (
  cons (mkFP "LowRefFeed4.v" "887fbb05ef218aee59b6c5027a25dd66" 7174 136) (
  cons (mkFP "MixTimeChain.v" "f2f37c490adbee8d885c88e7c397521d" 16291 381) (
  cons (mkFP "MixTimeChainIface.v" "66718a3bce884f4023501593c50066bb" 9449 204) (
  cons (mkFP "MixingTimeG2.v" "64c179a54414dfad1d2d62edd3c384f8" 15105 286) (
  cons (mkFP "NatLenPos.v" "564f6c60af79af7606981efe463a3806" 7481 144) (
  cons (mkFP "P7BoundedSoftmaxDeep.v" "546fae8522ea38966d4a12a988f23e75" 24157 490) (
  cons (mkFP "PA_AttnSqrt.v" "719921ec513422532a90efb57a9d711d" 10733 243) (
  cons (mkFP "PA_CW220_Extensions.v" "941907b0fc676a81c0cc2e450f8738a0" 100483 1695) (
  cons (mkFP "PA_DTPT_Bridge_Dep.v" "c166a7f856fb9002204fa704a2b331de" 16030 323) (
  cons (mkFP "PA_ExpOneEnvelope.v" "97cd65b3c64719b0aab1cfc2ff33832e" 19086 491) (
  cons (mkFP "PA_FirewallReqDischarge.v" "c4c6ef71de76cb604abf5bb3bcd5599a" 20619 316) (
  cons (mkFP "PA_PolyIntegral.v" "04acd3da2d06a052bd48508dba0ebffe" 12487 319) (
  cons (mkFP "PA_TempMonoW2Mark.v" "ca241063377f85586817c47f83e8699f" 12113 204) (
  cons (mkFP "PA_TempSoftmaxInstantiation.v" "98bc570c0348686dbcc89740b7e81349" 21000 386) (
  cons (mkFP "PA_ToyR_IdSlotTranslate.v" "603a360ca40accd6de614d036f83ad40" 6296 151) (
  cons (mkFP "PA_ToyR_SecondLawConsume.v" "ccb3d8264dd521534ac23bc56a89838b" 26271 409) (
  cons (mkFP "PA_ToyR_SupplyAssembly.v" "a305337187cd1d65a94b9f131b580220" 11871 282) (
  cons (mkFP "PA_ToyR_fa57_ext.v" "84837f7d7515977e379527ee15e3eaa3" 9828 213) (
  cons (mkFP "PA_UpAblAbsSumLeB.v" "6018d90622299f9059f45b76d4d705f0" 20126 383) (
  cons (mkFP "PA_UpAblD1S3_fep_UpReqSteadyThermo.v" "904fc7ca0ed0af47bcef5e82e57f0221" 10988 182) (
  cons (mkFP "PA_UpAblD1S4_UpReqStepKLEtaInst.v" "1ee4fa706cc8c6fd69868598583133c1" 9644 138) (
  cons (mkFP "PA_UpAblD2_AbsLeId_RI_DO.v" "1dca58d83a0032ae5f46b8d4224b0b89" 9292 158) (
  cons (mkFP "PA_UpAblMetaWindow.v" "a1ffd51783c37c625ed5837d4bafeb16" 12418 248) (
  cons (mkFP "PA_UpAblT1_UpFirewallReq.v" "0ef74df3cacde63046f7500cb7bfcbff" 7280 136) (
  cons (mkFP "PA_UpDissip.v" "aaeb400dc892195e176c82bb02974e3f" 33112 774) (
  cons (mkFP "PA_UpStepKLM3.v" "9d5cd3b10db600c65b22d48ede76b47d" 33803 641) (
  cons (mkFP "PadeDenPosA.v" "00af1eaf7d2b3f37c73b0720b2cd5b89" 20831 397) (
  cons (mkFP "PadeDenPosB12.v" "249381eb557927a05ee1396c20f601f1" 10524 222) (
  cons (mkFP "PadeErrorIntegral.v" "1d7161ca2bc4d918750ea763e4d57ee4" 35317 785) (
  cons (mkFP "Paper1Ablation.v" "99315f838b7df782a53af0d38b39d6f2" 27998 522) (
  cons (mkFP "Paper7Ablation.v" "7c5451c95223c964b922c2602b24ba17" 8013 179) (
  cons (mkFP "PhysPredAblation.v" "3d4b24ce2697a6234f0e085003d8e4fb" 13250 283) (
  cons (mkFP "PiEnvelope.v" "3429311867f37b45d434c7efb2e9e086" 40829 948) (
  cons (mkFP "PinskerTwoPoint.v" "7a2cbb4843aa4b842340a879e2b24d14" 29458 468) (
  cons (mkFP "PintMono.v" "828f4dbb9a1f250c6abd362a39fbe9cf" 20252 452) (
  cons (mkFP "PintPosGrid.v" "cbaf0ef89e117e6051edbf51d10ec3e0" 9372 177) (
  cons (mkFP "PolyIntegral.v" "b256876dc52f9f92072bf0f60f8e3a73" 15822 355) (
  cons (mkFP "PowRealCompat.v" "94b00213819b42b3653beb937ffac82f" 7760 164) (
  cons (mkFP "PsQReindex.v" "532202a3cc7740e49104bcafd16c7549" 28108 565) (
  cons (mkFP "QTailBridge.v" "e66304aa6aa4b63d4c0775a8b7656ba7" 6407 127) (
  cons (mkFP "QstepConvergenceBound.v" "01e26a34cc493eedcb909469d2d6539a" 29493 656) (
  cons (mkFP "QuickDischargeA.v" "7064fc07bd0dff3fc625b2a05be9bb8a" 9832 142) (
  cons (mkFP "R2BishopLogSel.v" "53689957b54ab44a443ceb5bf4276035" 21863 497) (
  cons (mkFP "RMaxSwap.v" "2fcc94a13335b663a3ba297a2962ef7e" 5497 108) (
  cons (mkFP "RateTheoryAblation.v" "4471359a528a0f0c0f82ce1883c9143c" 9769 193) (
  cons (mkFP "RealEnergyTempMono.v" "8879b19c36c7048e500eb0d02eb0263c" 31021 497) (
  cons (mkFP "RealIdentity.v" "b3138d0730b624627dd3ee5e137ff3cf" 13820 314) (
  cons (mkFP "RealKLCorrMark.v" "04ae395037ca2e17dbcc00cd72e00eef" 10029 161) (
  cons (mkFP "RealKLDecomp.v" "893fe7b34fadcf2b6626fb286117daa5" 49903 860) (
  cons (mkFP "S01_BaseRing.v" "0243f08c045d5f3368c2d1d5f2f360bd" 135504 2932) (
  cons (mkFP "S02_CauchyComplete.v" "c1329bcae804818247253a53ee33c376" 189592 3936) (
  cons (mkFP "S03_QExp.v" "d46d9b9556ef774643dea348e14e7e45" 367536 6860) (
  cons (mkFP "S04_RealExpLogConv.v" "e96c4daf1d135f9fdad2f042cb3284e8" 274550 5024) (
  cons (mkFP "S05_AlignmentGRPO.v" "e160bb6603b0edc49d9421f2ea60684d" 330048 5836) (
  cons (mkFP "S06_DiffSamplingGibbs.v" "22a2095ca27efc3e320b75dc1f227190" 428120 7754) (
  cons (mkFP "S07_RealSetoidExpLog.v" "cd3a0919a07d74c50bae467cf444f417" 452427 8717) (
  cons (mkFP "S08_RealMainlineDPO.v" "55aa8d23ad64497b85e389f34c767e6a" 337912 5620) (
  cons (mkFP "S09_EntropyReal.v" "518b1a6df25cad088bc553a8997b3369" 483949 7140) (
  cons (mkFP "S10_KVQuantTrig.v" "5ab5b35aebb9d70f01b6b1b0c34f92fc" 650832 12497) (
  cons (mkFP "S11_TP3B5.v" "d571b0c02b1b8183228789bf10f9a646" 607134 12802) (
  cons (mkFP "S12_B5RecycleSF.v" "841a8a16507a3407b3112d55127f94ed" 696275 14382) (
  cons (mkFP "S13_NLiveAudit.v" "eb7b15608bdb8cb277f0accb4bab37eb" 200649 4610) (
  cons (mkFP "S14_B5BatchBlock.v" "2415a838c333ec32736b4511eab1e117" 740973 14326) (
  cons (mkFP "S15_TailFEPUp.v" "e8de99ee2fc60131cecd2e0f56c47701" 104941 2104) (
  cons (mkFP "S5SlotWire.v" "71e14eb6dfcfc5fd2ce89069d13c9e31" 7459 152) (
  cons (mkFP "SecondLawConsume.v" "ae50e72dbe2805543cbd9d59dd97ca69" 23936 375) (
  cons (mkFP "SecondLawQuantified.v" "6f5b39350ca38f9556bd870daa456962" 33497 660) (
  cons (mkFP "SqWallCorrMark.v" "39f2f3640537b11c115d17284f5bfeed" 12659 244) (
  cons (mkFP "SqrtfCauchy.v" "3a8a65891e1b536235dfbc7a4fe29667" 85645 1386) (
  cons (mkFP "SqrtfCauchyArch.v" "380a6c6b69de137c0c9651c1a7357204" 20420 435) (
  cons (mkFP "SqrtfCauchyDischarge.v" "6884578e840f36d37c1b57257e9bdb54" 14444 240) (
  cons (mkFP "StopTimeConservation.v" "4aea581946ae55118a443d5710afa26f" 14417 295) (
  cons (mkFP "SumDCarrierFeed.v" "6d59ccb7877521245737a9ffabd09e9f" 6772 159) (
  cons (mkFP "SumEqListFeed.v" "071f0a20b2a9223d5659b3cee2394909" 9097 176) (
  cons (mkFP "SumEqListMark.v" "8634001a526e6c556f3db0e20d4863f4" 9026 150) (
  cons (mkFP "SumInvFactEscape.v" "7a2fafebebf7a51d3aa383e28587c0e1" 21593 486) (
  cons (mkFP "SupKLBound.v" "bdc2048758d91c33ff11dfde0ade7116" 8713 172) (
  cons (mkFP "SupKLMonoCompose.v" "02c5fd86124c6f9338c273619b220806" 31771 577) (
  cons (mkFP "SupplyAssembly.v" "c429d144874023193aed8b2f201832c8" 14405 283) (
  cons (mkFP "SymplecticRotationSpec.v" "1eb13451a7b1503b8919477a05a02d79" 14917 342) (
  cons (mkFP "TempMonoW2Mark.v" "f6f10c2d3eea905b5ec1547c1fdf51f6" 11795 198) (
  cons (mkFP "TempSoftmaxInstantiation.v" "867bea164288f56b5bb8a958c324acc0" 32692 549) (
  cons (mkFP "TempUnimodalMax.v" "94b8b7e0cb0ac3e258a837ac21cc8067" 18304 331) (
  cons (mkFP "ToyR_AbsLeId.v" "5659688ed13d5c6aa4d04ae67ce59d94" 3867 86) (
  cons (mkFP "ToyR_BeukersLists.v" "c0cc463b172d585967c8b4f9ac544d58" 18877 519) (
  cons (mkFP "ToyR_BeukersVariant.v" "e3d63cc1a8a8d162f090ea8ef5fb8a64" 22363 471) (
  cons (mkFP "ToyR_EntropyMonoSplitInst.v" "8e0ac88118d73e4d44769996ced69139" 16902 269) (
  cons (mkFP "ToyR_GibbsFamilyExt.v" "f2f8e6b029151605cdbd5d10f7e83659" 24165 468) (
  cons (mkFP "ToyR_Ln2Integrality.v" "3e288684c9355ea7e3a7446c2f3ffc11" 19577 472) (
  cons (mkFP "ToyR_NatLenPos.v" "0386d9001c9a05aee65cd7e079db7a07" 8119 142) (
  cons (mkFP "ToyR_Paper12345Sample.v" "ab21872ee60ab597c3b6f0b017e9f486" 5441 125) (
  cons (mkFP "ToyR_PhysPredAblation.v" "b34967238b83955dad28a30b0c7453f3" 15257 303) (
  cons (mkFP "ToyR_RateTheoryAblation.v" "dc5be7af7f86f6adb4c52fe9fea0368e" 9737 193) (
  cons (mkFP "ToyR_SecondLawConsume.v" "96d171dab280a7cc0496990eb2afdb75" 26746 407) (
  cons (mkFP "ToyR_SumEqListFeed.v" "c0137a2c24593dad93392ca9d560b2b5" 11016 199) (
  cons (mkFP "ToyR_SumEqListMark.v" "3bd3fdc79067c3a353462f9f051856bb" 14319 213) (
  cons (mkFP "ToyR_SupplyAssembly.v" "6306b91e9acd632c34d91e34ac22620b" 17360 344) (
  cons (mkFP "ToyR_UpAblP6_GibbsFamilyExt.v" "6271ebdd21b1a74514f38d1aed535a40" 11128 198) (
  cons (mkFP "ToyR_UpAblP6_UniformLimit.v" "c9215d0dd1a0b8cfb8b0172b9651bcba" 6128 139) (
  cons (mkFP "ToyR_UpAblP7_AbsNonNeg.v" "bedc675ae6bd17b0928adee699be0d0b" 15680 354) (
  cons (mkFP "ToyR_UpAblP7_LoHiCross.v" "9bf75fede124d7e84cfb17e825f38b79" 5646 98) (
  cons (mkFP "ToyR_UpAblP7_LoHiSqueeze.v" "ceb4170d87be9d9160755236fe778e05" 10337 236) (
  cons (mkFP "ToyR_UpAblP7_Paper7Ablation_S1inst.v" "6cd1d9bed524e0266b4e1d64c551ef91" 16093 291) (
  cons (mkFP "ToyR_UpAblP7_UMixSelect.v" "b154f8d721a50980e08eb6fafd9897e8" 11803 221) (
  cons (mkFP "ToyR_ZPosSlotFeed.v" "13f02d0cc8606bd6e6630ff13b31a556" 5388 115) (
  cons (mkFP "ToyR_fa52_dpo_witness.v" "bf728a63283f20c1d8f4b41241618089" 4496 83) (
  cons (mkFP "ToyR_fa52_entropy_diff_unsat.v" "374454970a1464b5e392d237e4344cc8" 4505 82) (
  cons (mkFP "ToyR_fa56b_ext.v" "cd0fb1d718eb92f975d2d17f643c8e8d" 10121 228) (
  cons (mkFP "ToyR_fa57_ext.v" "e68652036b27056112e6dce5dc9b233d" 9578 206) (
  cons (mkFP "TrueNumerator.v" "6d547ae14955852a076c4e475455d7a2" 11996 253) (
  cons (mkFP "UpAblA2_LoInflation.v" "81f27e898a319feaf8d55ec188061ea1" 26456 650) (
  cons (mkFP "UpAblAbsFeed.v" "59fa991a210ba7266ea10d1018037883" 4682 92) (
  cons (mkFP "UpAblAbsQFeed.v" "65156d4fe89b275042b7ccaba2961b4a" 7593 156) (
  cons (mkFP "UpAblAbsQFeedB2.v" "6290adc120f8b17cd67a883a33ada7f0" 12667 223) (
  cons (mkFP "UpAblAbsSumLeB.v" "e6ef270947df8ce6480c81664795b47e" 16962 340) (
  cons (mkFP "UpAblAbsSumLeB2.v" "8c2555f962d5adae0a8d557c3f393261" 22808 460) (
  cons (mkFP "UpAblAbsSumLeB3.v" "6dd1fe2bbc47350c1079ab83636eb111" 30008 625) (
  cons (mkFP "UpAblAbsSumLeEps.v" "d4fdc19fb602157de26231ff50eeaf16" 11249 181) (
  cons (mkFP "UpAblAbsTwoPtAbs.v" "1eb1d090dcd7b2f501272d8cef517bfa" 11145 194) (
  cons (mkFP "UpAblAlmConsumption.v" "a7f61c01223a577c230827b8c800d8f3" 12892 279) (
  cons (mkFP "UpAblArchGeomBatch.v" "e9c17572fc950b90f0faf37cefe575ce" 4360 101) (
  cons (mkFP "UpAblB1_MonoSplit.v" "bff1b29a008077a88b43c90b22bbb6d7" 20974 500) (
  cons (mkFP "UpAblB2WindowTie.v" "f20eec9d38805e9f45df0c3c9c402605" 13900 287) (
  cons (mkFP "UpAblB2_G13.v" "5e169a4beab1b4e8605ee5f57d5e352c" 16220 269) (
  cons (mkFP "UpAblBYDecisionTree.v" "f28d55c2915710a9738c1b2f5d3133bc" 9332 211) (
  cons (mkFP "UpAblBYLowerBound.v" "b975fd31c4846ca8a9b25fd3747d99ad" 11897 275) (
  cons (mkFP "UpAblBYUpperTight.v" "7fcd165c29ef7563274575853e7e8063" 7780 184) (
  cons (mkFP "UpAblCauchyLim.v" "d44a74e369fdd52b85789433563cb1a7" 13135 253) (
  cons (mkFP "UpAblCauchyMod.v" "9ac9f9421e8b147d511da2e0ce07a452" 6742 137) (
  cons (mkFP "UpAblD1PPO_UpReqPPOPlain.v" "897760456d7eeb0a040a4b0c796555a5" 8270 127) (
  cons (mkFP "UpAblD1S10_UpReqConcMixSel.v" "070290b0f1d28e9a58633fadb0d121d3" 7997 138) (
  cons (mkFP "UpAblD1S10_UpReqPPOPlain.v" "7f43d5edfeb1d352b4b811534c4258e8" 6937 127) (
  cons (mkFP "UpAblD1S11_UpReqPPOPlain.v" "9fb8694d61fdd7dcb032f4d55dbea677" 7691 140) (
  cons (mkFP "UpAblD1S12_UpReqAttnMassSplit.v" "e560a77f606b0aced33a360a77ef135a" 5402 98) (
  cons (mkFP "UpAblD1S12_UpReqAttnQ18Tail.v" "3ce6ec9704d6894017a0566177605e81" 5397 98) (
  cons (mkFP "UpAblD1S12_UpReqAttnUniformLimit.v" "201a761b761c62d2cc1a0845dad98b58" 6592 103) (
  cons (mkFP "UpAblD1S13_AlignIdUnclosed.v" "e099dc29e26b7aef8ab10f0712235479" 6370 126) (
  cons (mkFP "UpAblD1S13_UpReqAlignClose.v" "b00a7a7039d7a1986336e3e5cc4049f5" 9583 168) (
  cons (mkFP "UpAblD1S14_UpReqCauchy.v" "b0ce588434e2fac35a07416befe62416" 11456 253) (
  cons (mkFP "UpAblD1S15_GibbsAssembly.v" "fbcb5e1549a2846296889ef17ba99148" 31330 517) (
  cons (mkFP "UpAblD1S15_UpReqAlign3.v" "bd5b3e64c5aad238ba146cd90c5bb2fa" 6112 126) (
  cons (mkFP "UpAblD1S16_UpReqMixTime.v" "0fb1c7529ef4ece5dc8005ae918d4dd6" 8090 134) (
  cons (mkFP "UpAblD1S17_UpReqAttnGibbs.v" "d5891062a18b70256f8ac95f3acc5b21" 6143 123) (
  cons (mkFP "UpAblD1S17_UpReqDpoLoss.v" "c17279b5b2dfa1a8d18272933226765f" 4164 99) (
  cons (mkFP "UpAblD1S2_e752_UpReqAttnIter.v" "c16068dae04a22b025b86f3e52608fd8" 5574 97) (
  cons (mkFP "UpAblD1S2_reqlog_AlignIdUnclosed.v" "40602822eb7f6c3744a771cffd21978d" 4863 81) (
  cons (mkFP "UpAblD1S2_reqlog_GibbsAssembly.v" "e27f7d90539b084990be565fa7c2e5e2" 6327 103) (
  cons (mkFP "UpAblD1S2_reqlog_UpReqAlign3.v" "70d452d7b386983e595273aeeb72b7c2" 5302 86) (
  cons (mkFP "UpAblD1S2_reqlog_UpReqAlignClose.v" "73fef19dc42131a00615fcec143d6ce5" 4543 77) (
  cons (mkFP "UpAblD1S2_reqlog_UpReqCauchy.v" "c0f93c19901e1aa280981ffab556dc8d" 5931 83) (
  cons (mkFP "UpAblD1S2_reqlog_UpReqDpoLoss.v" "ead0dd16a173aad11fd891900953c52b" 4515 77) (
  cons (mkFP "UpAblD1S3_fep_UpReqAttnGibbs.v" "85c27834dee78749578057363d16cec1" 6833 103) (
  cons (mkFP "UpAblD1S3_fep_UpReqSteadyThermo.v" "27cdb3f3d87c3bf71b33cdcaacfe124c" 10830 178) (
  cons (mkFP "UpAblD1S3_sum_pos_AlignIdUnclosed.v" "8a3a33a681b0fbcf8e559e57bf245810" 5779 87) (
  cons (mkFP "UpAblD1S3_sum_pos_SecondLawQuantified.v" "862c558e114c91ef6789c524ab184b0c" 4319 69) (
  cons (mkFP "UpAblD1S3_sum_pos_TempSoftmaxInstantiation.v" "5e15b673ec1798a4a8c1b469a7b2aa3f" 5546 81) (
  cons (mkFP "UpAblD1S3_sum_pos_UpReqAlign3.v" "ac189fdc72018f1ddf3bdfc5ba4c8f28" 4693 78) (
  cons (mkFP "UpAblD1S3_sum_pos_UpReqAlignClose.v" "5ef32b7085011e559bd47e42e3133788" 5779 87) (
  cons (mkFP "UpAblD1S3_sum_pos_UpReqAttnGibbs.v" "5ea41ee4a107d8034d39174ff8d7998e" 4715 78) (
  cons (mkFP "UpAblD1S3_sum_pos_UpReqEntropyDeficitTemp.v" "336f477ca4f009f63881c46fb3baff39" 5387 78) (
  cons (mkFP "UpAblD1S3_sum_pos_UpReqEntropyMaxTemp.v" "61697bab1ebaafc5fe370334d566d602" 4371 69) (
  cons (mkFP "UpAblD1S3_sum_pos_UpReqEntropyMonoSplit.v" "9a487c350d184877572dd12ac45355f4" 5368 78) (
  cons (mkFP "UpAblD1S3_sum_pos_UpReqEntropyUniqueNeg.v" "0e742ac44b6d7ac204caade04751707d" 4387 69) (
  cons (mkFP "UpAblD1S3_sum_pos_UpReqEntropyUniqueTemp.v" "9603042d0a993fadc1370226af49ffbf" 5378 78) (
  cons (mkFP "UpAblD1S3_sum_pos_UpReqTempDefs.v" "870d68ca63e5c86a4a8596a32b7ca7df" 4325 69) (
  cons (mkFP "UpAblD1S4_UpReqStepKLEtaInst.v" "6f512b4aa85a13bf500ef7c66ef114b9" 10477 136) (
  cons (mkFP "UpAblD1S4_UpReqTopKTVChain.v" "18e93c8fa19ef9a10057a4949f4a5e56" 8153 140) (
  cons (mkFP "UpAblD1S5_UpReqDoeblinEntropy.v" "8e4b0c1b5cc4aee805ad8607c3c20228" 37071 634) (
  cons (mkFP "UpAblD1S5_UpReqEntropyMonoSplit.v" "60ff2ce4ed522d5819c31d99c5f5126e" 29298 607) (
  cons (mkFP "UpAblD1S6_SecondLawQuantified.v" "6486032ccde824b070cc8455732a4c9a" 7024 97) (
  cons (mkFP "UpAblD1S6_UpReqMinPKLChain.v" "ced25767659e704e5a2404f54a5d6f0d" 5762 108) (
  cons (mkFP "UpAblD1S6_UpReqRealFEP.v" "15a5071093a54c646156cb5f1dded41c" 7071 98) (
  cons (mkFP "UpAblD1S6_UpReqSteadyThermo.v" "219b3906f16c60b28ddb641bf72978dd" 6384 92) (
  cons (mkFP "UpAblD1S7_UpReqEntropyDeficitTemp.v" "40cf22a1f73ee5c913b43f2b083f14f5" 7335 101) (
  cons (mkFP "UpAblD1S7_UpReqEntropyMaxTemp.v" "d6254493e85b35aff24dde9634e2c5a7" 6634 96) (
  cons (mkFP "UpAblD1S7_UpReqEntropyUniqueNeg.v" "ef8e9e34e67d791d723af48139d84726" 7079 101) (
  cons (mkFP "UpAblD1S7_UpReqEntropyUniqueTemp.v" "9b162aeb570ab2166e07bba30f4b8194" 6105 91) (
  cons (mkFP "UpAblD1S8_TempSoftmaxInstantiation.v" "d5b44b0be98d86e30297693a01d8f5be" 8597 111) (
  cons (mkFP "UpAblD1S8_UpReqPPOPlain.v" "67f55cc8156cd177cb32da4fba75301a" 10071 183) (
  cons (mkFP "UpAblD1S8_UpReqTempDefs.v" "f1d44f5afb873439ca44e79dcd46db07" 7488 105) (
  cons (mkFP "UpAblD1S9_UpReqAttnIter.v" "15155e8c8ac19ffc68287b14c8e17bfe" 14314 220) (
  cons (mkFP "UpAblD1_expf_pack.v" "1a2ff133885a15faf5aefc3e1503f848" 3974 78) (
  cons (mkFP "UpAblD1_fa53_lpc_broadcast.v" "2ef04f7659ffb6f4695d2d4bdec55bb6" 12573 198) (
  cons (mkFP "UpAblD2_AbsLeId_RI_DO.v" "7d268370c0da6068855f8be53080fe4d" 10415 161) (
  cons (mkFP "UpAblDeltaStarGeneral.v" "f272683d580da223167c05bda1785bc2" 25524 577) (
  cons (mkFP "UpAblDeltaStarSuboptimal.v" "4f79c52db7db74c094c797d5ac89fdd2" 6552 160) (
  cons (mkFP "UpAblDistLogEq.v" "bdfdace2dc2ea849057cb838c921b627" 8696 159) (
  cons (mkFP "UpAblDistLogLe.v" "c2515ea68c631e798a9280373ca47941" 13128 238) (
  cons (mkFP "UpAblEps49Body.v" "9bd8af1ac25944128f1199c42ee34045" 18661 258) (
  cons (mkFP "UpAblEps49Fam.v" "df9a5e814c453e94458d1af815250ce0" 23260 414) (
  cons (mkFP "UpAblEps49List.v" "b58b4783fbdafa549e006f9b0d0f428f" 13483 241) (
  cons (mkFP "UpAblEps49Main.v" "109ceb680a421f02b982e088e32877a8" 9641 199) (
  cons (mkFP "UpAblEps49RKDBase.v" "3d0f8a789f33ae3857d3eb24e9d91d02" 55795 928) (
  cons (mkFP "UpAblEps66Body.v" "cb38f738a3bc1a1f1f936ce7ba2dbc5c" 9079 182) (
  cons (mkFP "UpAblEps66Pos.v" "75f82ed8875f036324f7eff5a564bc0e" 9259 205) (
  cons (mkFP "UpAblEps66Sum.v" "54c66dd7a74f74887e4a9801d299d079" 9791 195) (
  cons (mkFP "UpAblGrpEqDecWorld.v" "0ddee9047e1f696bd805d12a47aedd55" 6140 153) (
  cons (mkFP "UpAblGrpEqDischarge.v" "94cc224e2b98c6a2ad91dccdec17e948" 16643 439) (
  cons (mkFP "UpAblHalfPow.v" "6318847e3c832617dc54d15f200a5b0d" 13503 252) (
  cons (mkFP "UpAblHalfPowFeed.v" "108f66a2940666b08c328315d4295f01" 11325 236) (
  cons (mkFP "UpAblKVEpsHalf.v" "a612d4d8d77100661829fa50da76df6e" 11289 254) (
  cons (mkFP "UpAblLeEqCompat.v" "9461c97644e82c328752e775b10b8d7b" 11413 248) (
  cons (mkFP "UpAblLogSelOracle.v" "87a56a2afad556d2fb3db8119ca4bf8f" 29668 547) (
  cons (mkFP "UpAblLogWall.v" "4c3fb5f9b85ba221fd767adc28330615" 14938 298) (
  cons (mkFP "UpAblLogWallEq.v" "ce521442cd4205928784e91ea5d30df2" 20032 397) (
  cons (mkFP "UpAblLogWallFinal.v" "f1665a09fac8f08156d3b7cc7ddc8c2f" 19591 402) (
  cons (mkFP "UpAblMetaConjBridge.v" "a98049ec35fcd49fc295cf9c3babf061" 26128 489) (
  cons (mkFP "UpAblMetaDivQ.v" "70a579d59931ff9a3a0d35ce8ccb5cbe" 18240 379) (
  cons (mkFP "UpAblMetaDivThm.v" "04f8d705158e956611420a9e162f5929" 77252 1583) (
  cons (mkFP "UpAblMetaEngine.v" "fc69e09df612e4b9de798f4a5ce356d5" 43141 850) (
  cons (mkFP "UpAblMetaLow.v" "b0454fdacd0a254846c9e52372d0b8ee" 18113 408) (
  cons (mkFP "UpAblMetaPackage.v" "ad4e64d11bb3997c93fa336b94deefa7" 9211 161) (
  cons (mkFP "UpAblMetaTemp.v" "bc3e8ca01c5fe5ebc22b62a9d09d5799" 34547 632) (
  cons (mkFP "UpAblMetaWindow.v" "ec7cb774d6d05a351eeadba3cd110f80" 9359 207) (
  cons (mkFP "UpAblMetaWorld3.v" "7ad36b92de7627ee3bca9a3e72b62262" 43181 807) (
  cons (mkFP "UpAblMixACount.v" "25af268e5e73865b3be89f83df72fac9" 7171 142) (
  cons (mkFP "UpAblMixBSharp.v" "3885fc61bcb32ae4885cf1b01e0afa4a" 12187 223) (
  cons (mkFP "UpAblP1T1_AlignCert.v" "73bc8ed268d9282ca2a76f195aca2ad0" 7772 150) (
  cons (mkFP "UpAblP1T2_GrpoAuditCert.v" "d297076f919dd56a068b319e69c4fdba" 12264 273) (
  cons (mkFP "UpAblP1_SecondLawQuantified_sumd.v" "58eaf7fe160511c16d08d392e406a9b8" 5584 116) (
  cons (mkFP "UpAblP1_SqrtfCauchyArch_arch.v" "0c1b103f084a60b2891315d4d6649b9d" 3968 65) (
  cons (mkFP "UpAblP1_SqrtfCauchy_four_slots.v" "85f566a120cc2ce6bed0306c0b23c920" 4072 77) (
  cons (mkFP "UpAblP2FeedMix.v" "57fae11f9e65af11773bdee912c9ceee" 15711 317) (
  cons (mkFP "UpAblP2FeedSum.v" "d74dd4c1fe065b0cb291df532093500b" 14784 288) (
  cons (mkFP "UpAblP2FeedSumLe.v" "18570f89986ac7bc9b7f84f11c3b0f0e" 12887 253) (
  cons (mkFP "UpAblP2T1_Cert.v" "559bc6b2530a9d18b3bafbe16a56e782" 28597 569) (
  cons (mkFP "UpAblP2T1_CertB.v" "7a4a503aa1aa18c27c110bbca63f37b7" 7328 147) (
  cons (mkFP "UpAblP2T1_CertC.v" "9aad5a63c4b93cfdd966858bd0e72cfd" 11081 221) (
  cons (mkFP "UpAblP2WByPass.v" "7f70f4bcfcb5640b99d242d4e0536490" 18153 455) (
  cons (mkFP "UpAblP2_FepIdentClass_inst_bundle.v" "071c076d528c175d69d2d18b2495ecc1" 14900 223) (
  cons (mkFP "UpAblP2_SecondLawConsume_sumdis.v" "38d038eaa87c77961bcc963286b204a5" 11287 193) (
  cons (mkFP "UpAblP2_UpMinP_tokens_pack.v" "13f5a6d64f27080f625c5fdb06249c38" 5561 101) (
  cons (mkFP "UpAblP3_UpReqAttnMixTime.v" "ef79f4a4e73cfbf6395aeb423efe9625" 13511 261) (
  cons (mkFP "UpAblP3_UpReqConcMixSel.v" "43de448b92b0318271416e88581b36d9" 13183 234) (
  cons (mkFP "UpAblP4_UpStopTime_PA.v" "4ba3f68e5c2e79e20f11429d7fc422f5" 5292 95) (
  cons (mkFP "UpAblP6_ConcMixSelFeed.v" "650aeb78f6a39378aaf5ab2a68a15c24" 9972 225) (
  cons (mkFP "UpAblP6_EntropyMonoSplit_A.v" "4c27878124c3391b8917fa9a52b18d65" 8411 172) (
  cons (mkFP "UpAblP6_EntropyMonoSplit_B.v" "3a2a7f4d9402051b838e345cdd576b0e" 17440 351) (
  cons (mkFP "UpAblP6_EntropyMonoSplit_C.v" "517c3fe9e5d8b300cf6420e02bd6043d" 26754 539) (
  cons (mkFP "UpAblP6_GibbsFamilyExt.v" "4249e9c19b8db1e93844898282d10a03" 6898 147) (
  cons (mkFP "UpAblP6_Package.v" "2438641799b7ead664be19d74819f778" 42279 817) (
  cons (mkFP "UpAblP6_S5SlotWire.v" "1854cad6f46b0e18da368b8a0d386cc0" 7795 177) (
  cons (mkFP "UpAblP6_SecondLaw_two_state.v" "04b27cc1bb832a3eaa79613af369c7db" 24543 470) (
  cons (mkFP "UpAblP6_StateSpace_inst.v" "ccdebd49c0af4b7bd84af6c2de1542da" 23729 517) (
  cons (mkFP "UpAblP6_TempDefs.v" "1a78a1d5f9dd5d2b66fa785da740d9be" 24145 453) (
  cons (mkFP "UpAblP6_UniformLimit.v" "6c07048d69bea24a978d4f11a8824d6f" 6166 139) (
  cons (mkFP "UpAblP6_ZPosLowRef.v" "1107b1fc1a2bd2e169d6bfc86a80b873" 12370 269) (
  cons (mkFP "UpAblP7_AbsNonNeg.v" "ca8e39c0e48532189a9e0e7a783d2ce2" 15665 354) (
  cons (mkFP "UpAblP7_LoHiBridge.v" "6d85934639fc5ee38458f7bd9f24a8fd" 9779 201) (
  cons (mkFP "UpAblP7_LoHiCross.v" "e7607dff94351c4692f001341dd76e77" 6057 99) (
  cons (mkFP "UpAblP7_LoHiSqueeze.v" "7d426a7c20d07f93b2a7160ee8fef38a" 14238 283) (
  cons (mkFP "UpAblP7_P7FlagshipTail.v" "2894f9b2f9cecd3ef983cefd6c07ce5b" 15255 265) (
  cons (mkFP "UpAblP7_P7KappaFlagship.v" "2a5a341b4501e5835614b33a06f5fdc6" 14378 259) (
  cons (mkFP "UpAblP7_Package.v" "cb43eb219f567705e257127154ad65fa" 12426 225) (
  cons (mkFP "UpAblP7_Paper7Ablation.v" "343c796f2e3a87139b8a5f5fdebaf2a6" 15997 321) (
  cons (mkFP "UpAblP7_Paper7Ablation_S1inst.v" "04d2b3e3bac39e1361e8013753076360" 14888 260) (
  cons (mkFP "UpAblP7_UMixSelect.v" "201fb23457382b3a489cfda99540f308" 10726 209) (
  cons (mkFP "UpAblP7_WallEpsChain_A.v" "dca1f70e36427d6970ffd08f38d07b05" 19926 340) (
  cons (mkFP "UpAblP7_WallEpsChain_B.v" "f5a7f14282b9ae920b392b86c10cdc41" 25521 505) (
  cons (mkFP "UpAblP7_WallEps_CB2.v" "c819c613f44707fc254054d305c30dc2" 19589 383) (
  cons (mkFP "UpAblP7_WallEps_CSM.v" "8f95e416e9d10a2895d0d7d0c91b58d5" 13237 275) (
  cons (mkFP "UpAblQeqBridge.v" "73eb4763ddfee706eaccd2cca6528588" 8109 170) (
  cons (mkFP "UpAblQfloorDepth.v" "b9aa86b226c93ccc7a49e884743708fa" 11091 183) (
  cons (mkFP "UpAblRateAlgPkg.v" "1a952718f8f5989c4fca099680073453" 13858 287) (
  cons (mkFP "UpAblS06AbsFeed.v" "8990f21f0ff49bf81c78b017351dac4e" 13716 270) (
  cons (mkFP "UpAblSlackMix.v" "5b509c7100e49e859275891c3062d276" 13989 267) (
  cons (mkFP "UpAblSlotB0Merge.v" "15b2fe88657ba16eaee20ff884a951e4" 6131 111) (
  cons (mkFP "UpAblSposDirect.v" "264a4e2ff61ab0c5804436cd263b10f5" 8471 224) (
  cons (mkFP "UpAblT10_S04RealExpLogConv.v" "903637e8cf28b34217656e92e717eb9f" 4759 81) (
  cons (mkFP "UpAblT11_S11_TP3B5.v" "0c768cc7292aa0059147a4771743bdd5" 11893 179) (
  cons (mkFP "UpAblT12_G13.v" "544b4a4bc20e503cee7b8f17f5783597" 7245 106) (
  cons (mkFP "UpAblT12_UpRealLeB2.v" "e329fa6b1e37097d0a3d543aa171d81c" 9818 173) (
  cons (mkFP "UpAblT12_UpReqAlignRestA.v" "9d93ca5273e3683dc5e49a8bc0c897c3" 4414 71) (
  cons (mkFP "UpAblT13_UpEntropyGainReq.v" "c9c2352a1fb6bd78a699c30fc95903ff" 4950 78) (
  cons (mkFP "UpAblT13_UpFirewallReq.v" "a04b26367ede7fe6aee5b363eb63f1f4" 3765 66) (
  cons (mkFP "UpAblT13_UpReqAlignRestA.v" "185a1cd313c040437bd1f74ef24067b0" 4949 78) (
  cons (mkFP "UpAblT13_UpReqSampling.v" "43cdda1a5d6dd32bcde32689f3d1f8cb" 4337 88) (
  cons (mkFP "UpAblT13_UpSigMigrate2.v" "b4653d799e3d0ce80661967de17b3f70" 3312 60) (
  cons (mkFP "UpAblT13b_G06_BForm.v" "811ca1b74d73c167873c6149b5bbace8" 9384 191) (
  cons (mkFP "UpAblT13b_G13.v" "c59f86367d9b178da26957dd828399de" 6632 107) (
  cons (mkFP "UpAblT13b_UpReqAlign.v" "70937b18622fdeac08c0c44a6f560f0b" 4180 72) (
  cons (mkFP "UpAblT13b_UpReqAlign2.v" "ca4822d36fbc1f5c57133693ad676658" 5195 83) (
  cons (mkFP "UpAblT13b_UpReqAlignRestA.v" "60834926c1b3c1c7c60bba68bc64f338" 3925 70) (
  cons (mkFP "UpAblT13b_UpReqDist.v" "e08147269c1f4ef2f22581ccf17dc1f4" 4691 69) (
  cons (mkFP "UpAblT13b_UpSigMigrate.v" "8b2c9126862515e01c4f4305600b9913" 5782 105) (
  cons (mkFP "UpAblT13b_UpSigMigrate2.v" "5202d79e10abbdf2756ad030c6a65243" 6501 106) (
  cons (mkFP "UpAblT13b_UpTVDoeblin.v" "c9e201a921bbe08a993dc9dc53691818" 3633 59) (
  cons (mkFP "UpAblT13c_G13.v" "4f87d82d4c7371dbd2104bf54c61343a" 20155 337) (
  cons (mkFP "UpAblT13c_UpReqDist.v" "c24d1f838af6b01e7da0fa57b169b413" 9237 130) (
  cons (mkFP "UpAblT13c_UpSigMigrate2.v" "7dd2d168e045904237e389670598ef78" 8257 137) (
  cons (mkFP "UpAblT1_UpFirewallReq.v" "ae3f630ab378c308ca1758e8a9648ee5" 7404 128) (
  cons (mkFP "UpAblT1_UpReqDist.v" "839008a03d84272a83ad9eae7bd1e39f" 21388 389) (
  cons (mkFP "UpAblT1_UpReqTempEntropy.v" "676fe70a1d141ac07d8a6119b593e8da" 6712 125) (
  cons (mkFP "UpAblT1b_AttnDoeblin.v" "90cb66cc9f3c948551b6180cffa21d04" 9162 186) (
  cons (mkFP "UpAblT1b_S06_DiffSamplingGibbs.v" "222a780e8bb00b7e96c00e61934975f9" 9051 172) (
  cons (mkFP "UpAblT1b_S13_NLiveAudit.v" "a71309b6bf3baa53ce2a99e6ad659cc9" 13635 262) (
  cons (mkFP "UpAblT1c_UpFirewallReq.v" "81c44d6182045ca7b2f84bf437e08448" 13246 248) (
  cons (mkFP "UpAblT2a_UpFirewallReq.v" "7d67d6fdccc4b42c8f31e83d397e6fca" 4607 67) (
  cons (mkFP "UpAblT2a_UpReqAlign.v" "a276d651b24f777a1a4f36577c894926" 3762 66) (
  cons (mkFP "UpAblT2a_UpReqAlign2.v" "f197addcebf9d9be37d55e79b0561745" 4222 64) (
  cons (mkFP "UpAblT2a_UpReqAlignRestA.v" "37315e05ca05672e5feb883d99be279e" 3371 56) (
  cons (mkFP "UpAblT2a_UpReqDist.v" "90163027e41200c2912e587fb7e038fa" 4742 75) (
  cons (mkFP "UpAblT2a_UpReqFEPAttn.v" "d428a675c394c96130427fa8057b6671" 4408 99) (
  cons (mkFP "UpAblT2a_UpReqMisc5.v" "614d61b4b3a9fed5f58d31de8b017c0a" 4175 62) (
  cons (mkFP "UpAblT2a_UpReqPPO.v" "4717ce8cbffc080c4a040301396b6c14" 3293 55) (
  cons (mkFP "UpAblT2a_UpReqTempEntropy.v" "38e5e4bab93c90c7f3881ca43b1cfd9e" 4980 77) (
  cons (mkFP "UpAblT2a_UpSigMigrate2.v" "4732ee0527949b9db0ff3db9d5bc5dfd" 3845 77) (
  cons (mkFP "UpAblT2b_PredRelax5.v" "4948fa610f21c30ce7ddc3abde62f860" 18998 442) (
  cons (mkFP "UpAblT2b_fa53_lpc_broadcast.v" "9132476197fe615ad9a976fdc56b794a" 10419 204) (
  cons (mkFP "UpAblT3_UpReqAlign.v" "bdfb591f27f220d9c6856fa0ce8a750a" 22598 419) (
  cons (mkFP "UpAblT3_UpReqFEPAttn.v" "d6f440ae039cae9dd6bbf8d7f1bad0a1" 11238 221) (
  cons (mkFP "UpAblT4_RLHFkl.v" "00ba169b210dace587ae3f97745503ec" 10216 139) (
  cons (mkFP "UpAblT4_SumCarrier.v" "d077793b433be41a40111c1c7031994c" 9800 170) (
  cons (mkFP "UpAblT5_S04_RealExpLogConv.v" "ab678730f5e905fbf00d2335d378d296" 5189 101) (
  cons (mkFP "UpAblT5_S05_AlignmentGRPO.v" "eab4df7e91e68db81d9617814b355293" 4680 87) (
  cons (mkFP "UpAblT5_S06_DiffSamplingGibbs.v" "870633a9dfe9768fc16b5060a3b607ad" 4992 78) (
  cons (mkFP "UpAblT5_S12_B5RecycleSF.v" "523238df344d8880017e5790f25945dc" 3265 55) (
  cons (mkFP "UpAblT5_UpFirewall.v" "a9b2d7305717c270b50129c6b90aa946" 4243 65) (
  cons (mkFP "UpAblT5_UpReqAlgebra.v" "d41d75976b53ead73feb5df58d5d4b36" 4453 71) (
  cons (mkFP "UpAblT6_UpReqAlign2.v" "f4ee46f4effe1cbde699a1c3935e6583" 6073 103) (
  cons (mkFP "UpAblT6_UpReqPPO.v" "7e69ae50a7730f23aeab6c5409e00e44" 8252 109) (
  cons (mkFP "UpAblT6_UpReqSampling.v" "503f8d9a0a72c7c8f4f4bf966024ca14" 25446 372) (
  cons (mkFP "UpAblT6_UpSigMigrate.v" "eae396d65ae5180ab77849be75869eab" 7737 106) (
  cons (mkFP "UpAblT6_UpSigMigrate2.v" "4de2338d35013248ee1921e46ad15443" 8050 107) (
  cons (mkFP "UpAblT7_two_point_pack.v" "c0b393a7caa4c73af828c45bf0adc32f" 13087 246) (
  cons (mkFP "UpAblT7b_real_two_point_pack.v" "cbb38cde83da8686d353361968d27a05" 20295 398) (
  cons (mkFP "UpAblT9_G09_MiscSmall.v" "57d4d813e972018f3d788f8462468156" 4056 68) (
  cons (mkFP "UpAblT9_UpReqDist.v" "11685188c0f9103e0547d0e920db6ec7" 3209 71) (
  cons (mkFP "UpAblT9_UpReqFEPAttn.v" "3bdc13a3d0bccd77313a7e3bdfb0595e" 2866 68) (
  cons (mkFP "UpAblT9_UpReqSampling.v" "db84338a9357775609fd57bb90577656" 3661 81) (
  cons (mkFP "UpAblT9_UpSigMigrate.v" "e36b92862b88f2b25cd39e72eafcec0c" 3500 61) (
  cons (mkFP "UpAblT9_UpTVDoeblin.v" "e8e075afef4a8d017aec93b2bb69585f" 4389 78) (
  cons (mkFP "UpAblTwLeFeed.v" "e2063c745cd338fef3a1cb10ba8f64f0" 19016 349) (
  cons (mkFP "UpAblZpos.v" "08ef6df80da782284e82616fa7a324f6" 6053 115) (
  cons (mkFP "UpAblZposDirect.v" "e076b7a86638afb9111dcda476df5841" 6433 124) (
  cons (mkFP "UpAblZposReal.v" "3f4bbfdfc7e2287700f2941943ac885a" 5619 115) (
  cons (mkFP "UpAlignId.v" "d9701a172aa4083d87594c295c46928a" 17733 334) (
  cons (mkFP "UpAlignIdReq.v" "47a9dbbb694c52b48300f723f86e6ab4" 32103 583) (
  cons (mkFP "UpArchAttn.v" "c3b3ed2c5fc5029069274a085d15288b" 13124 218) (
  cons (mkFP "UpAuditBridge.v" "5585b84f216e5b6e1d816efe0a0e0646" 65581 1141) (
  cons (mkFP "UpBudgetReal.v" "b33bb2baf001465f4766be7dc3bc2436" 39402 738) (
  cons (mkFP "UpCS.v" "9147a18f5b149ecada961da4e2eb825d" 16910 418) (
  cons (mkFP "UpConstitution.v" "62b166b3578c4fb2e7499d0f9134ab89" 35996 854) (
  cons (mkFP "UpDPOLip.v" "f33569ec82f1c0418cf65c16abe3eee3" 29663 518) (
  cons (mkFP "UpDebtSqrtAbsReq.v" "22c8f545e92c72a2e84062177f9cb041" 7273 162) (
  cons (mkFP "UpDissip.v" "f2eb9ad8221854898a2d0f589097b7ed" 36204 813) (
  cons (mkFP "UpEntropyGain.v" "d0ac8270d4ef444f817a30f457c4bbcc" 24770 428) (
  cons (mkFP "UpEntropyGainReq.v" "1ffea8c5f9101d9ee3b75a52c2bee0b5" 42731 716) (
  cons (mkFP "UpFirewall.v" "342b01de5ef2b801f1e482b2d2f4ab86" 23323 419) (
  cons (mkFP "UpFirewallReq.v" "1ba0f0a26d188402e520d84f5f73a377" 31990 596) (
  cons (mkFP "UpGRPO.v" "0ae8d219c96d464377bcf2ed9ef76b25" 29978 660) (
  cons (mkFP "UpGeomB.v" "c2a393a567913bd01d7cfc8464174fff" 51241 944) (
  cons (mkFP "UpIDL_P2.v" "6e9d60444bf1d86d53c2af8ba9848eca" 59695 1323) (
  cons (mkFP "UpKVDrift.v" "a212f446213dddd483d86180e43fd00b" 109286 2274) (
  cons (mkFP "UpKVDrift_P2.v" "a8660a76b3474825e7a44c3e9a9f3397" 109053 2280) (
  cons (mkFP "UpKVEv.v" "ae1f562c54ced22a5f93b1811843f0bf" 14588 310) (
  cons (mkFP "UpMinP.v" "2827cab9cff3e619839f2c4c3e0d8ccf" 38889 900) (
  cons (mkFP "UpPredRelaxReq.v" "cbaed7ada08dcbe058a08cf4ee03b83b" 15731 319) (
  cons (mkFP "UpQKTVCompose.v" "e44be6f0f942f20494e0e40defed5952" 10559 216) (
  cons (mkFP "UpRealLeB.v" "fde7a958b3da517617533d5764fe86c7" 138529 2045) (
  cons (mkFP "UpRealLeB2.v" "69d34c92cedc2aca1c1782d129a6c6bd" 39591 681) (
  cons (mkFP "UpRealLeB3.v" "a0fb7a8d50753317bb35359e12b824ea" 9393 209) (
  cons (mkFP "UpRecast.v" "479ae489acfe00824046978cd1a7a4fc" 27949 717) (
  cons (mkFP "UpReqAlgebra.v" "cb68c47db4a1e87776b2e6d2259de37b" 96452 1773) (
  cons (mkFP "UpReqAlign.v" "42c521c4f547db67f1e81f23c7110b17" 80056 1470) (
  cons (mkFP "UpReqAlign2.v" "9e9fd5bf5d956ebfb16eb3c2c173ed1f" 81130 1432) (
  cons (mkFP "UpReqAlign3.v" "e3dd881e9bf77179bd2e6281d04c4eb4" 219083 3940) (
  cons (mkFP "UpReqAlign4.v" "8ec0c4ec7920c076492922bd8ec5daba" 74010 1484) (
  cons (mkFP "UpReqAlignClose.v" "11e0174ef0d257fa2671eb755d7dc35f" 37221 636) (
  cons (mkFP "UpReqAlignRestA.v" "a164ed0731804db4fe35031eb9dcf351" 45074 816) (
  cons (mkFP "UpReqAlignRestB.v" "73489a876a8e03154b780c1a19bb82b4" 139128 2663) (
  cons (mkFP "UpReqAltSumPos.v" "eed95c652527d9edc0c350556150bc7f" 31147 694) (
  cons (mkFP "UpReqArgminEngine.v" "77fddd9388d76b8f082f0e0ab8a6974e" 17312 366) (
  cons (mkFP "UpReqAttnGibbs.v" "1963efdd91e88adaab3169a3d374adfb" 129267 2395) (
  cons (mkFP "UpReqAttnIter.v" "e3e4c4a2cecb3ebcd3555420be09eeca" 41227 840) (
  cons (mkFP "UpReqAttnMassSplit.v" "041b703c8e09e2944e27bd604f0a48aa" 44576 860) (
  cons (mkFP "UpReqAttnMixTime.v" "81aaa34913f776c89fee4450629763a5" 12765 341) (
  cons (mkFP "UpReqAttnQ18Tail.v" "4bef8f445761545bb6b4471886032254" 23880 536) (
  cons (mkFP "UpReqAttnUniformLimit.v" "d72c43f4ef5cb1c488fc5a954228547f" 88467 1817) (
  cons (mkFP "UpReqB4TwoStage.v" "724e98bccef18b27e9a648d17e4291f3" 19146 372) (
  cons (mkFP "UpReqBanachAdd.v" "c0dc8afc96eee33a8b6bd9d60ef31709" 37840 756) (
  cons (mkFP "UpReqBanachBinomBridge.v" "0ae15c6dce085ed23d0155867a88d51f" 7461 148) (
  cons (mkFP "UpReqBanachCauchyD.v" "a3a113ebee53b5af735a2606dd022cb5" 68155 1419) (
  cons (mkFP "UpReqBanachClassExt.v" "240609304508ef81841bcd308d0a28f3" 10971 217) (
  cons (mkFP "UpReqBanachDouble.v" "914fd98f72a7b261325441b712484cfa" 15886 304) (
  cons (mkFP "UpReqBanachExp.v" "90f98abe4f100f558cc7d0ccbc14f53f" 22405 477) (
  cons (mkFP "UpReqBanachExpAdd.v" "bd3cf63a13a6735eae4744bfaad143bd" 22572 457) (
  cons (mkFP "UpReqBanachExpAddEq.v" "975069292bd4896e85478245d94d162b" 54269 1149) (
  cons (mkFP "UpReqBanachExpBasic.v" "4c67c7f4b12588818288c7331dc7ae09" 14338 265) (
  cons (mkFP "UpReqBanachExpDef.v" "c442704a581f920ce562f86b9f01dc17" 10542 193) (
  cons (mkFP "UpReqBanachExpNeg.v" "2186730a836709c6e4e36e961fafedce" 14995 297) (
  cons (mkFP "UpReqBanachExpOppOne.v" "75db943bb204ea4b76396b1bc75096fe" 11326 210) (
  cons (mkFP "UpReqBanachInst.v" "3c272743bb3f39510faa1c117cbfccf4" 17471 349) (
  cons (mkFP "UpReqBanachInstB.v" "2be27d9c49071dc1a35036344335d77e" 31295 683) (
  cons (mkFP "UpReqBanachInstEMult.v" "8da16a22947d9b79fa031be2530d8474" 11628 272) (
  cons (mkFP "UpReqBanachInstPre.v" "65ad3b10f840be78c75300c8f1bcc4ec" 34487 837) (
  cons (mkFP "UpReqBanachInstReal.v" "e081bec9142e65b1081f0ccebaa048b6" 35158 845) (
  cons (mkFP "UpReqBanachInvPre.v" "03e11b19ee8aa4184ea07af3b287ecca" 28606 558) (
  cons (mkFP "UpReqBanachLimUniq.v" "d1e28787c7eba06d3aec00521d6a0e6f" 9649 221) (
  cons (mkFP "UpReqBanachNormOpp.v" "1007d6e113c3f32aa232f2d49811c010" 25180 492) (
  cons (mkFP "UpReqBanachProd.v" "87b51e95016edac501b0e73b7d2a3e73" 18842 400) (
  cons (mkFP "UpReqBanachProd2.v" "a17351a3e451c9caa77f844764bbd515" 12209 222) (
  cons (mkFP "UpReqBanachSepThm.v" "86e1e765f757394952dfd0c3cabf3761" 9852 187) (
  cons (mkFP "UpReqBanachStrong.v" "28b01bbbbe9cd19a8897555617378f1d" 9879 173) (
  cons (mkFP "UpReqBishopFull.v" "15190de1853da0f96ce56468ef687bd9" 2729 55) (
  cons (mkFP "UpReqBishopLedger1.v" "f6197b727c4021240075f8c42726759c" 6571 132) (
  cons (mkFP "UpReqBranchPos.v" "e567fd45520e782ae13c0c3463d6a32f" 19627 413) (
  cons (mkFP "UpReqCEqDispersion.v" "f10bdffb7594810d0bb110e9f90b7ad4" 10423 203) (
  cons (mkFP "UpReqCStarDef.v" "fde813913ffef75b01bc21ef5f37c753" 36608 763) (
  cons (mkFP "UpReqCauchy.v" "91ac06a2a04a5f6fb189b1ba0bf6bb59" 90555 1542) (
  cons (mkFP "UpReqCauchyLogBound.v" "1c428f50576987ff5c11bc45d88bdb94" 18017 379) (
  cons (mkFP "UpReqCf2TvGenSupply.v" "be97bb272a314fc9bc6fcd98fbbab71c" 14142 202) (
  cons (mkFP "UpReqCf2TvGenWorld.v" "cf5694738a9c20586d1e2d28ea6853ef" 7936 158) (
  cons (mkFP "UpReqCf2TvW3.v" "f535eb98d0a3f42527c5d58bd6733dd4" 8370 175) (
  cons (mkFP "UpReqConcB1.v" "b970599eb0ab34295540b6766f5b1439" 20439 408) (
  cons (mkFP "UpReqConcB2.v" "9127c91485954bc6c89028d74a4ac6a5" 27351 619) (
  cons (mkFP "UpReqConcB2Time.v" "85beed5b8ea71cdd14b0a36570ab0054" 21963 395) (
  cons (mkFP "UpReqConcFin2.v" "cedf2607af248f436fa0ad3ff4b62354" 81102 1608) (
  cons (mkFP "UpReqConcMixSel.v" "153a79846e9a573327ad93e3a49ec12a" 51918 1133) (
  cons (mkFP "UpReqConcSoftmax.v" "6aac0a17f678102e54b4b5ec496e0c35" 13747 310) (
  cons (mkFP "UpReqConstEnvelope.v" "b4c0bb39511dbd882ae3a703477efee1" 29155 638) (
  cons (mkFP "UpReqDist.v" "f4c88a568de96f618098b78fd711c72e" 224228 3648) (
  cons (mkFP "UpReqDoeblinEntropy.v" "21aaf048ab75d18281fb24f7e5ee8fc9" 47589 1029) (
  cons (mkFP "UpReqDpoLoss.v" "582b4860434ea18628160b4c0f0e2375" 12619 246) (
  cons (mkFP "UpReqDyadicLog.v" "4e4e90d4064cb2515ef30d3c02968031" 29870 611) (
  cons (mkFP "UpReqEngineCeiling.v" "23597e9ff9c5f136ad4c2c484cd3cef6" 49431 1174) (
  cons (mkFP "UpReqEntropyDeficitTemp.v" "08ed3c2f3c2a6a8b5c018f0111475d3f" 29336 557) (
  cons (mkFP "UpReqEntropyMaxTemp.v" "b094f8a03a653c81cb331cfff37fc90a" 19906 380) (
  cons (mkFP "UpReqEntropyMonoSplit.v" "66752af0e1256fdac2f59049d6719d30" 48517 828) (
  cons (mkFP "UpReqEntropyUniqueNeg.v" "4819a2bb0a321dd3df239be3a52be785" 62215 1293) (
  cons (mkFP "UpReqEnvelopeDual.v" "cd52626759943a2056f73ca20bed057c" 37419 774) (
  cons (mkFP "UpReqEqbComplete.v" "f1d08ee2e0fb3aa61260112ce9a1db17" 13471 267) (
  cons (mkFP "UpReqExpPos.v" "eeef336d86954052c73979b0ad0b248e" 7043 137) (
  cons (mkFP "UpReqExpPosQBound.v" "38a7430754a41bcce5ce7ed0390ebec5" 18239 375) (
  cons (mkFP "UpReqExpPosWitness.v" "ad6b4f9341637b7073e92979c59debb4" 5224 101) (
  cons (mkFP "UpReqFEPAttn.v" "bfee2de912e8810c0bec4f750c3f789c" 25347 560) (
  cons (mkFP "UpReqForwardKLFamily.v" "a249d00ab255313fd89914893cdbb13d" 24987 387) (
  cons (mkFP "UpReqG05WallClass.v" "d5092d7c593d0b1fd0a877c594c006d6" 24256 435) (
  cons (mkFP "UpReqGeomD.v" "13231cfd52831f19f7093ad31e28ad3b" 26953 497) (
  cons (mkFP "UpReqGeomIter.v" "3794e73fdee7b979294e854ea4aefc07" 51926 906) (
  cons (mkFP "UpReqGibbsE2.v" "1208322e2087b671e468e8afcec8694e" 52195 1078) (
  cons (mkFP "UpReqGibbsWallEquiv.v" "074dbddb3a54773f4cbcc998644b1db0" 16596 324) (
  cons (mkFP "UpReqI4Bridge.v" "b87195c0deabcd6375493d6961584848" 13046 236) (
  cons (mkFP "UpReqI4Witness.v" "b7fee093e8bd75c50f1328259f95578f" 21424 423) (
  cons (mkFP "UpReqIndex.v" "7dabf643e575960be3785c28c8f41a9c" 277136 3505) (
  cons (mkFP "UpReqInvPosLazy.v" "8d56393761510b52d1cf2492f2885784" 14813 293) (
  cons (mkFP "UpReqIrrationalCriterion.v" "4bd7a42c22c186d8d2391557784f49ac" 35341 778) (
  cons (mkFP "UpReqIrrationalInstances.v" "86e42b32189fdf4795b11e5b7e61c3a7" 61171 1318) (
  cons (mkFP "UpReqIterGeomRate.v" "70f892508430b8028077c2543d4487bf" 85008 1648) (
  cons (mkFP "UpReqKLCocycle.v" "2b9b79f6799a6182a555a1f32f9c4976" 24231 356) (
  cons (mkFP "UpReqKLSTangent.v" "e53978a0ad5b68cccf5d3f06d6639b4e" 9322 186) (
  cons (mkFP "UpReqKLStrict.v" "f313a99e8e469f9daa8bb0847ad278a5" 36469 645) (
  cons (mkFP "UpReqKLStrictB.v" "fd7fc871a87646eaf7f7f108213428a4" 15443 317) (
  cons (mkFP "UpReqLatbMaxList.v" "1e90c47b9e93cae2109e7f573c2ab3c7" 13559 225) (
  cons (mkFP "UpReqLatticeB.v" "45c20440ea164cea5f72d9c4e4148a8e" 25653 521) (
  cons (mkFP "UpReqLn2Irrational.v" "530e1db1080587ef52be0f0daa7bf70e" 16368 379) (
  cons (mkFP "UpReqLogCompD.v" "4bdcd31b223e1f898a0144b15956b11b" 96095 1730) (
  cons (mkFP "UpReqLogCompD2.v" "93b242e72168246aa27c5515463b6c2d" 24904 468) (
  cons (mkFP "UpReqLogRDF.v" "050b2239fa8ff072e880e3bbd30ff445" 144638 1666) (
  cons (mkFP "UpReqLogZWallEquiv.v" "1115c15908bd2dc06b803ca8dc2bcf53" 38709 855) (
  cons (mkFP "UpReqLpoEquiv.v" "16c0909fe457084a896b1aef2eb43c5a" 20951 451) (
  cons (mkFP "UpReqMinPAntitone.v" "617222f90f1a160bd71778dfbde61df4" 15642 280) (
  cons (mkFP "UpReqMinPKLChain.v" "60bad0e2e0fdb19c3f3ceb31d4609722" 48321 1049) (
  cons (mkFP "UpReqMinUniqueTight.v" "940d119c4902b0401e76cfe95a697bc7" 101476 1847) (
  cons (mkFP "UpReqMisc5B.v" "a38172eabdc9a81cf27507af3934cd5e" 82880 1595) (
  cons (mkFP "UpReqMixLazy.v" "53ffebd37644919feb590a94bafd1af0" 23511 457) (
  cons (mkFP "UpReqMixLogA.v" "09320d1d520c90482da13d2e3e64399f" 64724 1340) (
  cons (mkFP "UpReqMixLogB.v" "4ebb577408bf19eefe40063205725cb9" 57558 1297) (
  cons (mkFP "UpReqMixLogD.v" "0c630d8ab28da58da808de39c24a8303" 78217 1757) (
  cons (mkFP "UpReqMixLogE.v" "bdf8def52cd34b46bb20db5c60e0a9c2" 31441 766) (
  cons (mkFP "UpReqMixRationalProxy.v" "4a14fec26d8839d6cd6cd6f7461f0911" 9820 201) (
  cons (mkFP "UpReqMixRationalProxy_R2.v" "84cb11ab464d9bae7ed6372f8b63fe37" 21036 512) (
  cons (mkFP "UpReqMixRationalProxy_R3.v" "1e9a97d3516c4d21204b85c62b9c129a" 44791 1034) (
  cons (mkFP "UpReqMixRealExec.v" "1d8ea9a2b3988e835b23764aeb3b7fc7" 14175 268) (
  cons (mkFP "UpReqMixingTime.v" "1b6ac7cbf9b4472030a3ccfb915fbfc0" 38533 735) (
  cons (mkFP "UpReqMpDomain.v" "0c715dc046a3c97da6c7762a6307bb99" 58555 1040) (
  cons (mkFP "UpReqNegFactorB.v" "0f4eeb4a4346b681a1a90348991461b1" 7991 152) (
  cons (mkFP "UpReqNormConv.v" "4de87458a667f14d8d757ebc435a4829" 42829 868) (
  cons (mkFP "UpReqPPO.v" "1c7d2f1bf0cabda39b943b30573723dd" 86418 1296) (
  cons (mkFP "UpReqPPOB.v" "0ab17dc33cfa6cc59a671e00fe6a1f7f" 12727 237) (
  cons (mkFP "UpReqPPOGapB.v" "bf227b2ec02b4ecc6f17f16e4739b36b" 25003 414) (
  cons (mkFP "UpReqPPOPlain.v" "3b6bf2e3112c3e3b66896c2058e84f83" 38657 681) (
  cons (mkFP "UpReqPadeBetaPos.v" "3a111d872eed037767076754860080e7" 14389 293) (
  cons (mkFP "UpReqPadeConstUnify.v" "b7e166ccd26845877f1aceee28db90ed" 12156 241) (
  cons (mkFP "UpReqPadeDenPos.v" "6f202c04e95113d7d438867776ab3900" 22031 545) (
  cons (mkFP "UpReqPadeDenPos12.v" "0fc8a802876d9f3c6ba24ce8ed93fa54" 16457 300) (
  cons (mkFP "UpReqPadeExp.v" "36098b2a9312c6148fb8e2dce5b82697" 10929 222) (
  cons (mkFP "UpReqPadeFinale.v" "da2918bf4b50c11578e4ea2bcc1e2cd3" 19260 432) (
  cons (mkFP "UpReqPadeLower.v" "ae72f1caab6e95ae7ce86f0e016fe69b" 21231 419) (
  cons (mkFP "UpReqPadeQLeg.v" "9a63eabe2c64090aa8b479ff395cf6db" 10216 206) (
  cons (mkFP "UpReqPadeSign.v" "f12bc86803d13f2c0307aede5b3fd412" 8282 163) (
  cons (mkFP "UpReqPadeSignXfer.v" "b3c02a2bdc8fe16168b9f02ed094176a" 9634 214) (
  cons (mkFP "UpReqPadeTailPos.v" "42d7bedd7b171ffe9feb352d0485ec05" 31192 684) (
  cons (mkFP "UpReqPadeTransport.v" "4573cd13fc7405d15f863e32cd839596" 19379 423) (
  cons (mkFP "UpReqPaperAnchor.v" "4a7890a631c68e6e28addc7bd80222cf" 11199 235) (
  cons (mkFP "UpReqPinWallEquiv.v" "c874ffa777c97895c9ba58e9ebb298e3" 11817 218) (
  cons (mkFP "UpReqPinskerCore.v" "671dad3e84c44b6f76b3bc1737fe2222" 203781 3652) (
  cons (mkFP "UpReqPinskerTransport.v" "50db10300eb815fc0b304ff1ac35ff14" 73575 1400) (
  cons (mkFP "UpReqPowMonoBridge.v" "c2b23b8f3806cfac3402de3a1d03fb73" 19096 360) (
  cons (mkFP "UpReqPropLiftShim.v" "94566ae43ef28dac9c2e97d8c64955c1" 6066 118) (
  cons (mkFP "UpReqQArchSite.v" "def924943ac13a9b14cdd4666313f3a6" 8604 157) (
  cons (mkFP "UpReqQExpTail.v" "bf9c959eedf70e6771019511fe79d724" 32521 755) (
  cons (mkFP "UpReqRDF.v" "20298e56de854714079563a64e402b53" 171497 2782) (
  cons (mkFP "UpReqRatioTail.v" "d5645d800a76313474016f7ca56da693" 40948 897) (
  cons (mkFP "UpReqRealFEP.v" "1bb19a19896c6276ec43b03b878165de" 72189 1174) (
  cons (mkFP "UpReqRealHalf.v" "35eb34d0d10a7582649a20bb11747f94" 7965 171) (
  cons (mkFP "UpReqRealLtShiftBridge.v" "dfb18b0e87fa153ec585a0da89a2ce08" 8471 152) (
  cons (mkFP "UpReqResidWallEquiv.v" "7b640bcc2b82060d2b8c1377712458a9" 24597 470) (
  cons (mkFP "UpReqSLM.v" "fbde0a23c2dcf8c5fdd80238bf118719" 65814 1217) (
  cons (mkFP "UpReqSampling.v" "5cbd84b0312124b3a6f7a3eaaf629fbf" 68464 1251) (
  cons (mkFP "UpReqSamplingFeed.v" "94fb98ec206a3f10d7def85d88b0944f" 12111 306) (
  cons (mkFP "UpReqScTrigEps.v" "f301a4e733382ec4fe030198e3bfbd86" 25868 545) (
  cons (mkFP "UpReqSentinelMother.v" "e5ee67b83d5874997fe85e358edd90fe" 14731 325) (
  cons (mkFP "UpReqSpec2x2.v" "08acedda22918753605b32a571b67b72" 62731 1289) (
  cons (mkFP "UpReqSqrt3Irrational.v" "02b3080bf6e47b6d451f4659416021ea" 53573 1119) (
  cons (mkFP "UpReqSqrtF.v" "6eae05e1656885d3ed65938a03376542" 63105 1119) (
  cons (mkFP "UpReqSqrtOptimal.v" "5f2702a5693d019606ed3dd5d7e9d088" 13831 345) (
  cons (mkFP "UpReqSquareWallEquiv.v" "cbf97b9beebea30d775ddddc45291ae7" 10934 189) (
  cons (mkFP "UpReqSteadyThermo.v" "883f4e890208abbf50d62ab9e7541b0f" 7324 141) (
  cons (mkFP "UpReqStepKLEtaInst.v" "183afdc131d8954409120850f9fa11b6" 55172 1107) (
  cons (mkFP "UpReqStrictBridgeD.v" "7a323696f06eae0c5c03dd87067ac145" 5145 95) (
  cons (mkFP "UpReqStrictStepGen.v" "be7115dfcaa80eabcf66883d284b2cf1" 10236 229) (
  cons (mkFP "UpReqSumB.v" "ea96e438b99080047a8e388322f32f48" 11342 199) (
  cons (mkFP "UpReqSumD.v" "f14545d4d81546a542dec6859af20481" 27887 568) (
  cons (mkFP "UpReqSymplecticBridge.v" "33667d9c401951519d44ae340ccdd0b5" 18828 404) (
  cons (mkFP "UpReqTBNCBridge.v" "81189e3e76a4abd717b0c0da3fc04251" 9724 214) (
  cons (mkFP "UpReqTVAbsEps.v" "53c2eb256adbb474d8e73fe18aa0e947" 11133 215) (
  cons (mkFP "UpReqTailResidual.v" "3704b703846e2c6a1e91e94db96758e9" 69129 1528) (
  cons (mkFP "UpReqTempDefs.v" "5aa563e6c55d32426180291e9d9d28d4" 27255 492) (
  cons (mkFP "UpReqTempDual.v" "3af4dee602916759a11c3c6660fd80d8" 19750 385) (
  cons (mkFP "UpReqTempDualList.v" "b327cf1323e2b5bc0aa04ee8da179212" 30254 558) (
  cons (mkFP "UpReqTempEntropy.v" "2282f36f20a557ce586498ee4222a4c0" 88162 1587) (
  cons (mkFP "UpReqTempInterp.v" "2a298891d0725e89e469a782a7e9d405" 28677 575) (
  cons (mkFP "UpReqTopKTVChain.v" "29cca3f0b7d0868e43465b4d3668a5ce" 65253 1128) (
  cons (mkFP "UpReqTrainingEquiv.v" "3614461356dc0ddf8a66d31a59ec1ece" 22956 441) (
  cons (mkFP "UpReqU2.v" "32b87ee4e529a0a0f743865fa50247c4" 53452 916) (
  cons (mkFP "UpReqUMixSelect.v" "70eebd8ffe31d308a4d234ce95dbd01d" 32925 651) (
  cons (mkFP "UpReqVajdaBound.v" "03db377666a2cb687e39b2d58f0b247d" 42240 852) (
  cons (mkFP "UpReqWeakTriangle.v" "7f4623857e3e659f2f40bc493f841bb4" 26883 555) (
  cons (mkFP "UpSLM.v" "556aa5daef2bc5bd746f0800d93ddaff" 37593 843) (
  cons (mkFP "UpSigMigrate.v" "b5a8e637d6d6e2e95e87760ae2b04777" 42063 626) (
  cons (mkFP "UpSigMigrate2.v" "3703c27456becc694f0bc6fe38418c0e" 116069 1742) (
  cons (mkFP "UpStepKL.v" "bbca7ba99208bcc6bfebc3f798bf3092" 59482 1071) (
  cons (mkFP "UpStepKLM3.v" "1108c12d6473e3936738168da0f412b4" 34815 652) (
  cons (mkFP "UpStopTime.v" "05cf03c1cb20320d4e1cf87eb6c6207a" 38233 903) (
  cons (mkFP "UpTVDoeblin.v" "eeddcb5f8af3143f529208f9ce62a05d" 98483 1982) (
  cons (mkFP "UpTempWindow.v" "3c29dae5e2bfc27fad00e4328fc9b3ef" 76997 1731) (
  cons (mkFP "VajdaClose2.v" "0083a9f8293852ac008da8d6e644276d" 8543 158) (
  cons (mkFP "VandermondePartial.v" "ee1ea00fdde0fcced18f8db89840c228" 32713 691) (
  cons (mkFP "WeakTriangleClose.v" "a6a87d24340f35c35c107a798d3dc758" 32342 487) (
  cons (mkFP "ZPosSlotFeed.v" "60e1843b816052e1eaf1430dbddc0d60" 11305 182) (
  cons (mkFP "fa51_sumpos_id.v" "3ac6cc201e08f24e9d4e3d6bd19964aa" 11390 245) (
  cons (mkFP "fa52_dpo_witness.v" "57e04617cb75cd6a52ebac9a4e42cf06" 5689 101) (
  cons (mkFP "fa52_entropy_diff_unsat.v" "6b0bf4bfc68b7f5ecba850fcd504c080" 4875 88) (
  cons (mkFP "fa53_compat_abs.v" "78aef72e424c2d794a5a63ee17437afc" 8060 179) (
  cons (mkFP "fa56_id_carrier.v" "fdada1ecdd676719674b1e7c674537d1" 18118 321) (
  cons (mkFP "fa56b_ext.v" "831500e99932ecf1399b0e3496c342a1" 14025 277) (
  cons (mkFP "fa56c_ext.v" "03b5d8dfffe2952912699d3a741c0194" 19171 360) (
  cons (mkFP "fa57_ext.v" "7e386cb1afb43c1f2d36de012ed57c6e" 12275 240) (
  cons (mkFP "fka_weak_triangle_ref.v" "8e032b7cfbf294777a9371d105b27934" 1690 23) (
  cons (mkFP "p2a_AttnClimClose.v" "0a8ae2a07af3833c0b99b5d0ea9f786f" 9382 178) (
  cons (mkFP "p3a_TempDualBoolSlots.v" "5269ac6a81b3fa9e48a77f393b3535ae" 8765 183) (
  cons (mkFP "p4a_GradSignQDec.v" "e2f5d18e2ead3ede772508cbc1335cbd" 11885 271) (
  cons (mkFP "uabl_attn_full_instance.v" "70bfa87b62db2b0fbd4669f82dc57810" 6218 149) (
  nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

(* ---- Self-consistency functions (all Defined / recursive Fixpoint) ---- *)
Fixpoint fp_length (l : list FileFP) : nat :=
  match l with
  | nil => 0
  | cons _ t => S (fp_length t)
  end.

Fixpoint fp_sum_bytes (l : list FileFP) : nat :=
  match l with
  | nil => 0
  | cons h t => plus (fp_bytes h) (fp_sum_bytes t)
  end.

Fixpoint fp_sum_lines (l : list FileFP) : nat :=
  match l with
  | nil => 0
  | cons h t => plus (fp_lines h) (fp_sum_lines t)
  end.

(* look up an md5 by file name (string equality via String.eqb) *)
Fixpoint md5_of_file (f : string) (l : list FileFP) : option string :=
  match l with
  | nil => None
  | cons h t => if String.eqb (fp_file h) f then Some (fp_md5 h) else md5_of_file f t
  end.

(* ---- Boolean self-consistency checks (Compute on the consumer side should yield true for all) ---- *)
Definition check_length : bool :=
  Nat.eqb (fp_length manifest) (snap_file_count snapshot).
Definition check_bytes : bool :=
  Nat.eqb (fp_sum_bytes manifest) (snap_total_bytes snapshot).
Definition check_lines : bool :=
  Nat.eqb (fp_sum_lines manifest) (snap_total_lines snapshot).
Definition check_order_lines : bool :=
  Nat.eqb (snap_order_lines snapshot) (fp_length manifest).
Definition check_order_md5 : bool :=
  String.eqb (snap_order_md5 snapshot) "c7ac7a1991ccf9801b4f74240327408a".
Definition check_chain_md5 : bool :=
  String.eqb (snap_chain_md5 snapshot) "75241eb3de81676c9f38493d00733897".
Definition check_redline_zero : bool :=
  andb (Nat.eqb (rl_axiom (snap_redline snapshot)) 0)
    (andb (Nat.eqb (rl_admitted (snap_redline snapshot)) 0)
      (Nat.eqb (rl_classical (snap_redline snapshot)) 0)).
Definition check_vo_magic_bad : bool :=
  Nat.eqb (snap_vo_magic_bad snapshot) 0.
Definition check_r134_delta : bool :=
  andb (Nat.eqb (snap_r134_deleted snapshot) 48)
    (andb (Nat.eqb (snap_r134_added snapshot) 0)
      (andb (Nat.eqb (snap_r134_changed snapshot) 631)
        (Nat.eqb (snap_r134_unchanged snapshot) 12))).
(* spot checks: the md5 of four entries - first in lexicographic order / largest file / last entry / family anchor - is present in the table (independently recomputed against shell md5 -q) *)
Definition check_spot_first : bool :=
  match md5_of_file "AbsLeId.v" manifest with
  | Some m => String.eqb m "1dc877c64a58277e06f08c48877d51ac"
  | None => false
  end.
Definition check_spot_s01 : bool :=
  match md5_of_file "S01_BaseRing.v" manifest with
  | Some m => String.eqb m "0243f08c045d5f3368c2d1d5f2f360bd"
  | None => false
  end.
Definition check_spot_gibbs : bool :=
  match md5_of_file "GibbsAttractor.v" manifest with
  | Some m => String.eqb m "455b9fda8ded90384f9921ffcd95c21d"
  | None => false
  end.
Definition check_spot_last : bool :=
  match md5_of_file "UpDPOLip.v" manifest with
  | Some m => String.eqb m "f33569ec82f1c0418cf65c16abe3eee3"
  | None => false
  end.

(* master gate: conjunction of all check items (Compute all_green on the consumer side should yield true) *)
Definition all_green : bool := andb check_length (andb check_bytes (andb check_lines (andb check_order_lines (andb check_order_md5 (andb check_chain_md5 (andb check_redline_zero (andb check_vo_magic_bad (andb check_r134_delta (andb check_spot_first (andb check_spot_s01 (andb check_spot_gibbs (check_spot_last)))))))))))).

