(* ==========================================================================
   Arch_UpAbl_03.v - statement-family collection and instance carrying.
   Mission. 使命: nine theorems in six sections - uabT2a_fw_dist_log_inv_one_inv,
     uabT9_g09_rss_inst_real, uabT9_g09_pct_truth_real, uabT9_fep_ctx_Zf_pos,
     uabT9_row_ctx_Zrow_pos, uabT9_lz_ctx_Zf_pos,
     uabd1s3_secondlawquantified_sumpos,
     uabd1s3_upreqentropymaxtemp_real_sum_pos_preserved,
     uabd1s3_upreqentropyuniqueneg_real_sum_pos_preserved (the three
     sumf-carrying definitions feed the extraction gate by name).
   Dependencies. 依赖清单: S01_BaseRing..S15_TailFEPUp, G05_LogSmall
     (logd_log_inv_one_inv_real), G09_MiscSmall (reqRealSelfSS /
     reqRealSelfSS_inst / reqPCT_is_truth / req_pct_truth_is_global_min),
     UpReqFEPAttn (Zf_pos / req_Zrow_pos / lz_Zf_pos), UpReqSumD
     (sumd_sumf / sumd_sum_pos) of the -Set lineage world.
   References. 对标: the firewall log identity, the self-setoid instance
     and PCT truth slots, the partition-function positivity slots, and the
     enumerated-sum positivity family. Statement names carried over
     verbatim; adaptation = argument-less-face rebinding: the argument-less
     record and its instance are consumed bare, module-def applications
     drop the carrier/instance leading pair, predicate faces carry
     real_lt / real_eq, and req_Zrow is applied at the world's definition
     face (S sumf temp temp_pos z2 s).
   Constructivity. 构造性注记: all Set-layer statements; every station
     Qed-closed, zero admitted items; each proof consumes one in-register
     supply lemma by exact; no new axioms.
   Build. 编译配方: rocq c -native-compiler no -q -Q <world> ""
     Arch_UpAbl_03.v (cpu_guard thermal wrapper, ulimit -s 65532).
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
Require Import G05_LogSmall.
Require Import G09_MiscSmall.
Require Import UpReqFEPAttn.
Require Import UpReqSumD.
From Stdlib Require Import List.
From Stdlib Require Import Extraction.

(* ================= §1 uabT2a_fw_dist_log_inv_one_i 族 ================= *)
Import RealInterfaceEnhancedMod.

(* ---- the firewall log identity, forwarded from G05_LogSmall;
   the statement carries the supply lemma's own direct faces (the
   interface-module import shadows the notation bridge, so the bare
   names here would resolve to the projections and diverge at the
   extraction gate from the supply's real_* faces) ---- *)
Theorem uabT2a_fw_dist_log_inv_one_inv :
  forall (x : Real) (Hx : real_lt real_zero x)
         (Hi : real_lt real_zero (real_inv_pos x Hx)),
    real_eq (real_log (real_inv_pos x Hx) Hi)
      (real_opp (real_log x Hx)).
Proof.
  intros x Hx Hi.
  exact (logd_log_inv_one_inv_real x Hx Hi).
Qed.

(* ---- assumption audit ---- *)
Print Assumptions uabT2a_fw_dist_log_inv_one_inv.
(* ================= §2 uabT9_g09_rss_inst_real 族 ================= *)
Import RealInterfaceEnhancedMod.

Theorem uabT9_g09_rss_inst_real : reqRealSelfSS.
Proof.
  exact (reqRealSelfSS_inst).
Qed.

Theorem uabT9_g09_pct_truth_real :
  forall (L : Real -> Real) (s : Real),
    (reqPCT_is_truth L s ->
     forall s' : Real, le (L s) (L s')) *
    ((forall s' : Real, le (L s) (L s')) -> reqPCT_is_truth L s).
Proof.
  intros L s.
  exact (@req_pct_truth_is_global_min L s).
Qed.

(* ---- assumption audit ---- *)
Print Assumptions uabT9_g09_rss_inst_real.
Print Assumptions uabT9_g09_pct_truth_real.
(* ================= §3 uabT9_fep_ctx_Zf_pos 族 ================= *)
Import RealInterfaceEnhancedMod.

Theorem uabT9_fep_ctx_Zf_pos :
  forall (S : Set) (sumf : (S -> Real) -> Real) (z : S -> Real) (T : Real)
         (T_pos : real_lt zero T),
    (forall f : S -> Real,
      (forall s : S, real_lt zero (f s)) -> real_lt zero (sumf f)) ->
    real_lt zero (Zf S sumf z T T_pos).
Proof.
  intros S sumf z T T_pos Hsum.
  exact (@Zf_pos S sumf Hsum z T T_pos).
Qed.

Theorem uabT9_row_ctx_Zrow_pos :
  forall (S : Set) (sumf : (S -> Real) -> Real)
         (temp : Real) (temp_pos : real_lt zero temp)
         (z2 : S -> S -> Real) (expf : Real -> Real),
    (forall f : S -> Real,
      (forall s : S, real_lt zero (f s)) -> real_lt zero (sumf f)) ->
    (forall x : Real, real_lt zero (expf x)) ->
    forall s : S, real_lt zero (req_Zrow S sumf temp temp_pos z2 expf s).
Proof.
  intros S sumf temp temp_pos z2 expf Hsum Hexpf s.
  exact (@req_Zrow_pos S sumf Hsum temp temp_pos z2 expf Hexpf s).
Qed.

Theorem uabT9_lz_ctx_Zf_pos :
  forall (S : Set) (sumf : (S -> Real) -> Real) (z : S -> Real) (T : Real)
         (T_pos : real_lt zero T),
    (forall f : S -> Real,
      (forall s : S, real_lt zero (f s)) -> real_lt zero (sumf f)) ->
    real_lt zero (lz_Zf S sumf z T T_pos).
Proof.
  intros S sumf z T T_pos Hsum.
  exact (@lz_Zf_pos S sumf Hsum z T T_pos).
Qed.

(* ---- assumption audit ---- *)
Print Assumptions uabT9_fep_ctx_Zf_pos.
Print Assumptions uabT9_row_ctx_Zrow_pos.
Print Assumptions uabT9_lz_ctx_Zf_pos.
(* ================= §4 uabd1s3_secondlawquantified_ 族 ================= *)
Import RealInterfaceEnhancedMod.

Definition uabd1s3_secondlawquantified_sumf (S0 : Set) (enum0 : list S0) (f : S0 -> Real) : Real :=
  sumd_sumf S0 enum0 f.

Theorem uabd1s3_secondlawquantified_sumpos :
  forall (S0 : Set) (enum0 : list S0) (Hne : Not (enum0 = nil)) (f : S0 -> Real),
    (forall s : S0, real_lt real_zero (f s)) ->
    real_lt real_zero (uabd1s3_secondlawquantified_sumf S0 enum0 f).
Proof.
  intros S0 enum0 Hne f Hf.
  exact (sumd_sum_pos S0 enum0 f Hne Hf).
Qed.

Print Assumptions uabd1s3_secondlawquantified_sumpos.
(* ================= §5 uabd1s3_upreqentropymaxtemp_ 族 ================= *)
Import RealInterfaceEnhancedMod.

Definition uabd1s3_upreqentropymaxtemp_sumf (S0 : Set) (enum0 : list S0) (f : S0 -> Real) : Real :=
  sumd_sumf S0 enum0 f.

Theorem uabd1s3_upreqentropymaxtemp_real_sum_pos_preserved :
  forall (S0 : Set) (enum0 : list S0) (Hne : Not (enum0 = nil)) (f : S0 -> Real),
    (forall s : S0, real_lt real_zero (f s)) ->
    real_lt real_zero (uabd1s3_upreqentropymaxtemp_sumf S0 enum0 f).
Proof.
  intros S0 enum0 Hne f Hf.
  exact (sumd_sum_pos S0 enum0 f Hne Hf).
Qed.

Print Assumptions uabd1s3_upreqentropymaxtemp_real_sum_pos_preserved.
(* ================= §6 uabd1s3_upreqentropyuniquene 族 ================= *)
Import RealInterfaceEnhancedMod.

Definition uabd1s3_upreqentropyuniqueneg_sumf (S0 : Set) (enum0 : list S0) (f : S0 -> Real) : Real :=
  sumd_sumf S0 enum0 f.

Theorem uabd1s3_upreqentropyuniqueneg_real_sum_pos_preserved :
  forall (S0 : Set) (enum0 : list S0) (Hne : Not (enum0 = nil)) (f : S0 -> Real),
    (forall s : S0, real_lt real_zero (f s)) ->
    real_lt real_zero (uabd1s3_upreqentropyuniqueneg_sumf S0 enum0 f).
Proof.
  intros S0 enum0 Hne f Hf.
  exact (sumd_sum_pos S0 enum0 f Hne Hf).
Qed.

Print Assumptions uabd1s3_upreqentropyuniqueneg_real_sum_pos_preserved.
