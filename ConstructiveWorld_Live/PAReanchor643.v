(* ===================================================================== *)
(* PAReanchor643.v -- K1 paper-anchor re-measurement registry              *)
(* (self-contained standalone data module)                                 *)
(*                                                                         *)
(* Mission. Register the re-measurement result data of 1533 anchors of     *)
(*   19 papers against the 643-file tree: five-state anchor-line status    *)
(*   (valid-as-is / shifted / multi-candidate / no-solution / target-      *)
(*   file-deleted), old and new line numbers, and per-entry census /       *)
(*   retrieval / self-consistency functions, for target-side Require or    *)
(*   excerpting.                                                           *)
(* Dependencies. Zero tree Require; only one standard-library module,      *)
(*   Stdlib.Strings.String (the Rocq 9.1 prelude does not preload string,  *)
(*   which is required to host readable registry data); list / nat /       *)
(*   bool / option all come from the prelude.                              *)
(* References. Base ConstructiveWorld_Live 643 .v files and order.txt      *)
(*   643 lines; the anchor-table numbers are authoritative in the in-file  *)
(*   registry field.                                                       *)
(* Constructivity. Pure Set-layer data plus all-Defined functions;         *)
(*   axiom-free at the statement level, no Prop statements.                *)
(* Build. Standalone compile: rocq c -native-compiler no -q                *)
(*   PAReanchor643.v (zero tree dependencies; embeddable in any target     *)
(*   pool). Extraction self-check lives outside this file: an isolated-    *)
(*   pool probe file (Require this file + Extraction plugin) verifies      *)
(*   Obj.magic = 0.                                                        *)
(* ===================================================================== *)

From Stdlib.Strings Require Import String.

Inductive AnchorStatus : Set :=
  | StHit : AnchorStatus          (* anchor line valid as-is *)
  | StShift : AnchorStatus        (* shifted; new line number in ae_new *)
  | StAmbiguous : AnchorStatus    (* multiple candidates in the window; pending manual review *)
  | StNotFound : AnchorStatus     (* no solution / out of range / external file *)
  | StDeadFile : AnchorStatus.    (* target file deleted *)

Record AnchorEntry : Set := mkAnchor {
  ae_paper : string;        (* paper/section (P0-CN/EN/TEX or paper-8-25 titles) *)
  ae_anchor : string;       (* anchor original text (as-mentioned form in the manuscript) *)
  ae_symbol : string;       (* main symbol (empty = symbol-less anchor) *)
  ae_file : string;         (* target tree file *)
  ae_old : nat;             (* old line number (manuscript-claimed / P0=#144 caliber, U3=claimed) *)
  ae_new : option nat;      (* new line number in the 643 tree (None = no solution / deleted) *)
  ae_status : AnchorStatus  (* verdict *)
}.

Definition reanchor_baseline_md5 : string :=
  "c7ac7a1991ccf9801b4f74240327408a".

Definition reanchor_version : string := "20260927-643".

Definition registry : list AnchorEntry :=
  cons (mkAnchor "P0-CN" "S05_AlignmentGRPO.v:326" "rlhf_optimal" "S05_AlignmentGRPO.v" 326 (Some 326) StHit) (
  cons (mkAnchor "P0-CN" "UpReqLpoEquiv.v:245" "SqWall" "UpReqLpoEquiv.v" 245 (Some 245) StHit) (
  cons (mkAnchor "P0-CN" "UpReqLpoEquiv.v:249" "rLPO" "UpReqLpoEquiv.v" 249 (Some 249) StHit) (
  cons (mkAnchor "P0-CN" "UpReqLpoEquiv.v:264" "lpn_forward" "UpReqLpoEquiv.v" 264 (Some 264) StHit) (
  cons (mkAnchor "P0-CN" "UpReqLpoEquiv.v:357" "SqWall" "UpReqLpoEquiv.v" 357 (Some 357) StHit) (
  cons (mkAnchor "P0-CN" "DTPT_Bridge.v:12" "" "DTPT_Bridge.v" 12 (Some 12) StHit) (
  cons (mkAnchor "P0-CN" "UpReqIndex.v:404-413" "" "UpReqIndex.v" 404 (Some 281) StShift) (
  cons (mkAnchor "P0-CN" "UpReqIndex.v:442" "TotalModules_matches" "UpReqIndex.v" 442 (Some 309) StShift) (
  cons (mkAnchor "P0-CN" "UpReqIndex.v:494" "" "UpReqIndex.v" 494 (Some 371) StShift) (
  cons (mkAnchor "P0-CN" "S02_CauchyComplete.v:397" "cauchy" "S02_CauchyComplete.v" 397 (Some 397) StHit) (
  cons (mkAnchor "P0-CN" "S02_CauchyComplete.v:468" "real_lt" "S02_CauchyComplete.v" 468 (Some 468) StHit) (
  cons (mkAnchor "P0-CN" "S02_CauchyComplete.v:472" "Real" "S02_CauchyComplete.v" 472 (Some 472) StHit) (
  cons (mkAnchor "P0-CN" "S01_BaseRing.v:73" "Id" "S01_BaseRing.v" 73 (Some 73) StHit) (
  cons (mkAnchor "P0-CN" "S01_BaseRing.v:78-80" "Not" "S01_BaseRing.v" 78 (Some 80) StShift) (
  cons (mkAnchor "P0-CN" "S01_BaseRing.v:83-84" "ForallT" "S01_BaseRing.v" 83 (Some 84) StShift) (
  cons (mkAnchor "P0-CN" "S04_RealExpLogConv.v:2066" "free_energy" "S04_RealExpLogConv.v" 2066 (Some 2066) StHit) (
  cons (mkAnchor "P0-CN" "S04_RealExpLogConv.v:2817" "relative_entropy" "S04_RealExpLogConv.v" 2817 (Some 2817) StHit) (
  cons (mkAnchor "P0-CN" "S06_DiffSamplingGibbs.v:228" "kl_divergence" "S06_DiffSamplingGibbs.v" 228 (Some 228) StHit) (
  cons (mkAnchor "P0-CN" "S06_DiffSamplingGibbs.v:4018" "tv_dist" "S06_DiffSamplingGibbs.v" 4018 (Some 4018) StHit) (
  cons (mkAnchor "P0-CN" "S05_AlignmentGRPO.v:147" "align_objective" "S05_AlignmentGRPO.v" 147 (Some 147) StHit) (
  cons (mkAnchor "P0-CN" "S05_AlignmentGRPO.v:65" "pi_star" "S05_AlignmentGRPO.v" 65 (Some 65) StHit) (
  cons (mkAnchor "P0-CN" "S01_BaseRing.v:32-55" "Variables" "S01_BaseRing.v" 32 (Some 32) StHit) (
  cons (mkAnchor "P0-CN" "S05_AlignmentGRPO.v:1720" "rlhf_suboptimality_gap" "S05_AlignmentGRPO.v" 1720 (Some 1720) StHit) (
  cons (mkAnchor "P0-CN" "AttnHardLimit218.v:1017" "real_lt" "AttnHardLimit218.v" 1017 (None) StAmbiguous) (
  cons (mkAnchor "P0-CN" "S09_EntropyReal.v:4630" "real_gradient_zero_entropy_max" "S09_EntropyReal.v" 4630 (Some 4630) StHit) (
  cons (mkAnchor "P0-CN" "UpReqIndex.v:4" "req" "UpReqIndex.v" 4 (None) StNotFound) (
  cons (mkAnchor "P0-CN" "DTPT_Extract.v:45" "gate_pass" "DTPT_Extract.v" 45 (Some 45) StHit) (
  cons (mkAnchor "P0-CN" "DTPT_Extract.v:60" "gate_pass" "DTPT_Extract.v" 60 (Some 44) StShift) (
  cons (mkAnchor "P0-CN" "DTPT_Extract.v:64" "freq" "DTPT_Extract.v" 64 (Some 64) StHit) (
  cons (mkAnchor "P0-CN" "DTPT_Extract.v:102" "H_adj" "DTPT_Extract.v" 102 (Some 102) StHit) (
  cons (mkAnchor "P0-CN" "DTPT_Extract.v:115" "bool" "DTPT_Extract.v" 115 (None) StAmbiguous) (
  cons (mkAnchor "P0-CN" "DTPT_Extract.v:130" "u12_gate_chain" "DTPT_Extract.v" 130 (Some 130) StHit) (
  cons (mkAnchor "P0-CN" "DTPT_Truth.v:231" "tarski" "DTPT_Truth.v" 231 (Some 231) StHit) (
  cons (mkAnchor "P0-CN" "UpReqIrrationalCriterion.v:285" "lic_irrational_criterion" "UpReqIrrationalCriterion.v" 285 (Some 285) StHit) (
  cons (mkAnchor "P0-CN" "S02_CauchyComplete.v:3084" "real_cauchy_complete" "S02_CauchyComplete.v" 3084 (Some 3084) StHit) (
  cons (mkAnchor "P0-CN" "S05_AlignmentGRPO.v:359" "dpo_optimal" "S05_AlignmentGRPO.v" 359 (Some 359) StHit) (
  cons (mkAnchor "P0-CN" "S05_AlignmentGRPO.v:386" "rlhf_optimal_unique" "S05_AlignmentGRPO.v" 386 (Some 386) StHit) (
  cons (mkAnchor "P0-CN" "S05_AlignmentGRPO.v:1456" "rlhf_free_energy_kl" "S05_AlignmentGRPO.v" 1456 (Some 1456) StHit) (
  cons (mkAnchor "P0-CN" "S05_AlignmentGRPO.v:1194" "ppo_gap_exact" "S05_AlignmentGRPO.v" 1194 (Some 1194) StHit) (
  cons (mkAnchor "P0-CN" "S05_AlignmentGRPO.v:1269" "ppo_gap_nonneg" "S05_AlignmentGRPO.v" 1269 (Some 1269) StHit) (
  cons (mkAnchor "P0-CN" "S05_AlignmentGRPO.v:763" "ppo_conservative" "S05_AlignmentGRPO.v" 763 (Some 763) StHit) (
  cons (mkAnchor "P0-CN" "S05_AlignmentGRPO.v:857" "dpo_reward_recovers_up_to_baseline" "S05_AlignmentGRPO.v" 857 (Some 857) StHit) (
  cons (mkAnchor "P0-CN" "S05_AlignmentGRPO.v:937" "dpo_reward_relative_exact" "S05_AlignmentGRPO.v" 937 (Some 937) StHit) (
  cons (mkAnchor "P0-CN" "S05_AlignmentGRPO.v:2212" "dpo_loss_pi_star_bounded" "S05_AlignmentGRPO.v" 2212 (Some 2212) StHit) (
  cons (mkAnchor "P0-CN" "S05_AlignmentGRPO.v:4991" "grpo_advantage_zero_mean" "S05_AlignmentGRPO.v" 4991 (Some 4991) StHit) (
  cons (mkAnchor "P0-CN" "S05_AlignmentGRPO.v:4228" "policy_iter_kl_geom_step" "S05_AlignmentGRPO.v" 4228 (Some 4228) StHit) (
  cons (mkAnchor "P0-CN" "S05_AlignmentGRPO.v:4263" "policy_iter_kl_geom_iter" "S05_AlignmentGRPO.v" 4263 (Some 4263) StHit) (
  cons (mkAnchor "P0-CN" "S05_AlignmentGRPO.v:4326" "dpo_loss_iter_step_le" "S05_AlignmentGRPO.v" 4326 (Some 4326) StHit) (
  cons (mkAnchor "P0-CN" "S05_AlignmentGRPO.v:3670" "policy_iter_backward_kl_step_beta" "S05_AlignmentGRPO.v" 3670 (Some 3670) StHit) (
  cons (mkAnchor "P0-CN" "S05_AlignmentGRPO.v:3885" "_le" "S05_AlignmentGRPO.v" 3885 (Some 3885) StHit) (
  cons (mkAnchor "P0-CN" "S05_AlignmentGRPO.v:4654" "u2_fixed_point_unique" "S05_AlignmentGRPO.v" 4654 (Some 4654) StHit) (
  cons (mkAnchor "P0-CN" "S05_AlignmentGRPO.v:4845" "u2_objective_eq_optimal_iff" "S05_AlignmentGRPO.v" 4845 (Some 4845) StHit) (
  cons (mkAnchor "P0-CN" "S15_TailFEPUp.v:1030" "real_step_kl_eta_bound_eps" "S15_TailFEPUp.v" 1030 (Some 1030) StHit) (
  cons (mkAnchor "P0-CN" "S15_TailFEPUp.v:1682" "" "S15_TailFEPUp.v" 1682 (Some 1681) StShift) (
  cons (mkAnchor "P0-CN" "S15_TailFEPUp.v:1721" "grpo_uniform_mass" "S15_TailFEPUp.v" 1721 (Some 1721) StHit) (
  cons (mkAnchor "P0-CN" "S08_RealMainlineDPO.v:2029" "real_attention_is_gibbs" "S08_RealMainlineDPO.v" 2029 (Some 2029) StHit) (
  cons (mkAnchor "P0-CN" "S10_KVQuantTrig.v:12374" "attention_is_gibbs_setoid" "S10_KVQuantTrig.v" 12374 (Some 12374) StHit) (
  cons (mkAnchor "P0-CN" "S08_RealMainlineDPO.v:2120" "real_steady_state_boltzmann_attn" "S08_RealMainlineDPO.v" 2120 (Some 2120) StHit) (
  cons (mkAnchor "P0-CN" "S10_KVQuantTrig.v:12451" "setoid" "S10_KVQuantTrig.v" 12451 (Some 12451) StHit) (
  cons (mkAnchor "P0-CN" "S15_TailFEPUp.v:108" "attention_minimizes_free_energy_unique" "S15_TailFEPUp.v" 108 (Some 108) StHit) (
  cons (mkAnchor "P0-CN" "S15_TailFEPUp.v:1971" "F_attn" "S15_TailFEPUp.v" 1971 (Some 1932) StShift) (
  cons (mkAnchor "P0-CN" "AttnDoeblin.v:318" "u_tv_contraction" "AttnDoeblin.v" 318 (Some 332) StShift) (
  cons (mkAnchor "P0-CN" "AttnDoeblin.v:406" "u_titer" "AttnDoeblin.v" 406 (Some 406) StHit) (
  cons (mkAnchor "P0-CN" "AttnDoeblin.v:724" "delta_star" "AttnDoeblin.v" 724 (Some 716) StShift) (
  cons (mkAnchor "P0-CN" "AttnDoeblin.v:737" "bounded_softmax_tv_contraction" "AttnDoeblin.v" 737 (Some 738) StShift) (
  cons (mkAnchor "P0-CN" "AttnDoeblin.v:757" "real_expf_realizable" "AttnDoeblin.v" 757 (Some 771) StShift) (
  cons (mkAnchor "P0-CN" "S13_NLiveAudit.v:3096" "real_expf_realizable" "S13_NLiveAudit.v" 3096 (Some 3096) StHit) (
  cons (mkAnchor "P0-CN" "S08_RealMainlineDPO.v:2190" "real_minp_markov_kernel_normalized" "S08_RealMainlineDPO.v" 2190 (Some 2190) StHit) (
  cons (mkAnchor "P0-CN" "S08_RealMainlineDPO.v:2285" "real_top_k_majorization" "S08_RealMainlineDPO.v" 2285 (Some 2285) StHit) (
  cons (mkAnchor "P0-CN" "S09_EntropyReal.v:4673" "real_gradient_zero_neg_entropy_truth" "S09_EntropyReal.v" 4673 (Some 4673) StHit) (
  cons (mkAnchor "P0-CN" "S09_EntropyReal.v:4746" "real_gradient_step_contraction" "S09_EntropyReal.v" 4746 (Some 4746) StHit) (
  cons (mkAnchor "P0-CN" "S09_EntropyReal.v:6175" "real_grad_step_abs_contraction_full" "S09_EntropyReal.v" 6175 (Some 6175) StHit) (
  cons (mkAnchor "P0-CN" "S09_EntropyReal.v:5015" "real_grad_decay_positive_iter" "S09_EntropyReal.v" 5015 (Some 5015) StHit) (
  cons (mkAnchor "P0-CN" "S09_EntropyReal.v:6113" "_negative_iter" "S09_EntropyReal.v" 6113 (Some 6113) StHit) (
  cons (mkAnchor "P0-CN" "S15_TailFEPUp.v:280" "ppo_is_decomp" "S15_TailFEPUp.v" 280 (Some 280) StHit) (
  cons (mkAnchor "P0-CN" "S15_TailFEPUp.v:290" "clip_error_nonneg" "S15_TailFEPUp.v" 290 (Some 290) StHit) (
  cons (mkAnchor "P0-CN" "S15_TailFEPUp.v:318" "ppo_clipped_improvement" "S15_TailFEPUp.v" 318 (Some 318) StHit) (
  cons (mkAnchor "P0-CN" "UpReqGibbsWallEquiv.v:172" "gwe_G" "UpReqGibbsWallEquiv.v" 172 (Some 172) StHit) (
  cons (mkAnchor "P0-CN" "UpReqGibbsWallEquiv.v:176" "GibbsWall" "UpReqGibbsWallEquiv.v" 176 (Some 176) StHit) (
  cons (mkAnchor "P0-CN" "UpReqGibbsWallEquiv.v:186" "gwe_diag_zero" "UpReqGibbsWallEquiv.v" 186 (Some 186) StHit) (
  cons (mkAnchor "P0-CN" "UpReqGibbsWallEquiv.v:252" "GibbsWall" "UpReqGibbsWallEquiv.v" 252 (Some 252) StHit) (
  cons (mkAnchor "P0-CN" "UpReqGibbsWallEquiv.v:264" "GibbsWall" "UpReqGibbsWallEquiv.v" 264 (Some 264) StHit) (
  cons (mkAnchor "P0-CN" "UpReqGibbsWallEquiv.v:299" "gmech_wall_lpo" "UpReqGibbsWallEquiv.v" 299 (Some 307) StShift) (
  cons (mkAnchor "P0-CN" "UpReqGibbsWallEquiv.v:307" "gmech_wall_lpo" "UpReqGibbsWallEquiv.v" 307 (Some 307) StHit) (
  cons (mkAnchor "P0-CN" "UpReqLogZWallEquiv.v:326" "lgz_LogZWall" "UpReqLogZWallEquiv.v" 326 (Some 338) StShift) (
  cons (mkAnchor "P0-CN" "UpReqLogZWallEquiv.v:351" "lgmech_wall_zle" "UpReqLogZWallEquiv.v" 351 (Some 363) StShift) (
  cons (mkAnchor "P0-CN" "UpReqLogZWallEquiv.v:500" "lgz_log_z_wall_lpo" "UpReqLogZWallEquiv.v" 500 (Some 512) StShift) (
  cons (mkAnchor "P0-CN" "UpReqLogZWallEquiv.v:655" "lgz_lpo_zle" "UpReqLogZWallEquiv.v" 655 (Some 667) StShift) (
  cons (mkAnchor "P0-CN" "UpReqSquareWallEquiv.v:144" "snw_b_lift" "UpReqSquareWallEquiv.v" 144 (Some 132) StShift) (
  cons (mkAnchor "P0-CN" "UpReqSquareWallEquiv.v:56" "SqWall" "UpReqSquareWallEquiv.v" 56 (None) StAmbiguous) (
  cons (mkAnchor "P0-CN" "UpReqSquareWallEquiv.v:61" "snw_b_lift" "UpReqSquareWallEquiv.v" 61 (None) StAmbiguous) (
  cons (mkAnchor "P0-CN" "UpReqSquareWallEquiv.v:74" "snw_b_lift" "UpReqSquareWallEquiv.v" 74 (None) StAmbiguous) (
  cons (mkAnchor "P0-CN" "UpReqSquareWallEquiv.v:92" "rLPO" "UpReqSquareWallEquiv.v" 92 (None) StAmbiguous) (
  cons (mkAnchor "P0-CN" "PinskerCoreClose.v:138" "pkc_sign_load" "PinskerCoreClose.v" 138 (None) StDeadFile) (
  cons (mkAnchor "P0-CN" "G07_KLWall.v:1615" "Jensen" "G07_KLWall.v" 1615 (Some 1632) StShift) (
  cons (mkAnchor "P0-CN" "G07_KLWall.v:1827" "Jensen" "G07_KLWall.v" 1827 (Some 1844) StShift) (
  cons (mkAnchor "P0-CN" "G07_KLWall.v:1847" "eps" "G07_KLWall.v" 1847 (None) StAmbiguous) (
  cons (mkAnchor "P0-CN" "G07_KLWall.v:1955" "eps" "G07_KLWall.v" 1955 (None) StAmbiguous) (
  cons (mkAnchor "P0-CN" "DTPT_Truth.v:243" "no_uniform_truth" "DTPT_Truth.v" 243 (Some 243) StHit) (
  cons (mkAnchor "P0-CN" "DTPT_Truth.v:326" "layer_self_refutation" "DTPT_Truth.v" 326 (Some 326) StHit) (
  cons (mkAnchor "P0-CN" "DTPT_Truth.v:355" "layered_network_liar_each_layer" "DTPT_Truth.v" 355 (Some 355) StHit) (
  cons (mkAnchor "P0-CN" "DTPT_Truth.v:374" "level_confusion_revives_liar" "DTPT_Truth.v" 374 (Some 374) StHit) (
  cons (mkAnchor "P0-CN" "DTPT_Truth.v:409" "tarski_via_renaming" "DTPT_Truth.v" 409 (Some 409) StHit) (
  cons (mkAnchor "P0-CN" "DTPT_Entropy.v:135" "H_shannon_q_perm_inv_counterex" "DTPT_Entropy.v" 135 (Some 135) StHit) (
  cons (mkAnchor "P0-CN" "DTPT_Entropy.v:481" "H_lam_cross_phase_bounds" "DTPT_Entropy.v" 481 (Some 481) StHit) (
  cons (mkAnchor "P0-CN" "G10_LoebFam.v:719" "Prf_soundness" "G10_LoebFam.v" 719 (Some 719) StHit) (
  cons (mkAnchor "P0-CN" "G10_LoebFam.v:808" "diagonal_lemma" "G10_LoebFam.v" 808 (Some 808) StHit) (
  cons (mkAnchor "P0-CN" "UpReqIrrationalCriterion.v:758" "lic_e_irrational_criterion" "UpReqIrrationalCriterion.v" 758 (Some 758) StHit) (
  cons (mkAnchor "P0-CN" "UpReqIrrationalCriterion.v:769" "exact" "UpReqIrrationalCriterion.v" 769 (Some 769) StHit) (
  cons (mkAnchor "P0-CN" "UpReqIrrationalInstances.v:1301" "ir2_sqrt2_irrational_criterion" "UpReqIrrationalInstances.v" 1301 (Some 1301) StHit) (
  cons (mkAnchor "P0-CN" "UpReqSqrt3Irrational.v:1102" "is3_sqrt3_irrational_criterion" "UpReqSqrt3Irrational.v" 1102 (Some 1102) StHit) (
  cons (mkAnchor "P0-CN" "UpReqLn2Irrational.v:364" "ln2i_irrational_criterion_cond" "UpReqLn2Irrational.v" 364 (Some 364) StHit) (
  cons (mkAnchor "P0-CN" "Ln2Escape.v:253" "lne_beta_value" "Ln2Escape.v" 253 (Some 253) StHit) (
  cons (mkAnchor "P0-CN" "Ln2Escape.v:453" "lne_B_le_p4" "Ln2Escape.v" 453 (Some 453) StHit) (
  cons (mkAnchor "P0-CN" "Ln2Escape.v:477" "lne_B_int" "Ln2Escape.v" 477 (Some 477) StHit) (
  cons (mkAnchor "P0-CN" "Ln2Escape.v:507" "lne_B_posT" "Ln2Escape.v" 507 (Some 507) StHit) (
  cons (mkAnchor "P0-CN" "Ln2Escape.v:559" "lne_ln2_irrational_cond" "Ln2Escape.v" 559 (Some 559) StHit) (
  cons (mkAnchor "P0-CN" "Ln2Integrality.v:257" "pi_Pn_int" "Ln2Integrality.v" 257 (Some 257) StHit) (
  cons (mkAnchor "P0-CN" "Ln2Integrality.v:274" "pi_Qn_le_8pow" "Ln2Integrality.v" 274 (Some 274) StHit) (
  cons (mkAnchor "P0-CN" "Ln2Integrality.v:426" "pi_den_divide" "Ln2Integrality.v" 426 (Some 426) StHit) (
  cons (mkAnchor "P0-CN" "BeukersIdentity.v:62" "bi_norm_factor" "BeukersIdentity.v" 62 (Some 62) StHit) (
  cons (mkAnchor "P0-CN" "S01_BaseRing.v:78" "And" "S01_BaseRing.v" 78 (Some 78) StHit) (
  cons (mkAnchor "P0-CN" "S01_BaseRing.v:79" "Not" "S01_BaseRing.v" 79 (Some 80) StShift) (
  cons (mkAnchor "P0-CN" "S01_BaseRing.v:80" "Not" "S01_BaseRing.v" 80 (Some 80) StHit) (
  cons (mkAnchor "P0-CN" "S01_BaseRing.v:83" "ExistsT" "S01_BaseRing.v" 83 (Some 83) StHit) (
  cons (mkAnchor "P0-CN" "S01_BaseRing.v:84" "ForallT" "S01_BaseRing.v" 84 (Some 84) StHit) (
  cons (mkAnchor "P0-CN" "S06_DiffSamplingGibbs.v:3181" "partition_function" "S06_DiffSamplingGibbs.v" 3181 (Some 3181) StHit) (
  cons (mkAnchor "P0-CN" "S06_DiffSamplingGibbs.v:3334" "softmax_temp" "S06_DiffSamplingGibbs.v" 3334 (Some 3334) StHit) (
  cons (mkAnchor "P0-CN" "S06_DiffSamplingGibbs.v:3823" "Z_thermo" "S06_DiffSamplingGibbs.v" 3823 (Some 3823) StHit) (
  cons (mkAnchor "P0-CN" "S05_AlignmentGRPO.v:353" "dpo_loss" "S05_AlignmentGRPO.v" 353 (Some 353) StHit) (
  cons (mkAnchor "P0-CN" "S05_AlignmentGRPO.v:821" "ppo_surrogate" "S05_AlignmentGRPO.v" 821 (Some 821) StHit) (
  cons (mkAnchor "P0-CN" "S05_AlignmentGRPO.v:2420" "energy_t" "S05_AlignmentGRPO.v" 2420 (Some 2420) StHit) (
  cons (mkAnchor "P0-CN" "UpReqAlgebra.v:89" "req" "UpReqAlgebra.v" 89 (None) StAmbiguous) (
  cons (mkAnchor "P0-CN" "UpReqSquareWallEquiv.v:44" "snw_wall" "UpReqSquareWallEquiv.v" 44 (None) StAmbiguous) (
  cons (mkAnchor "P0-CN" "AttnDoeblin.v:154" "omd" "AttnDoeblin.v" 154 (None) StAmbiguous) (
  cons (mkAnchor "P0-CN" "AttnDoeblin.v:541" "delta_star" "AttnDoeblin.v" 541 (None) StAmbiguous) (
  cons (mkAnchor "P0-CN" "DTPT.v:3" "" "DTPT.v" 3 (Some 3) StHit) (
  cons (mkAnchor "P0-CN" "DTPT_Bridge.v:3" "" "DTPT_Bridge.v" 3 (Some 3) StHit) (
  cons (mkAnchor "P0-CN" "S12_B5RecycleSF.v:15" "b5e_pern_main" "S12_B5RecycleSF.v" 15 (None) StNotFound) (
  cons (mkAnchor "P0-CN" "S12_B5RecycleSF.v:2046" "b5e_pern_main" "S12_B5RecycleSF.v" 2046 (Some 2046) StHit) (
  cons (mkAnchor "P0-CN" "DTPT_Extract.v:31-39" "" "DTPT_Extract.v" 31 (Some 15) StShift) (
  cons (mkAnchor "P0-CN" "UpReqAlgebra.v:30" "req" "UpReqAlgebra.v" 30 (None) StNotFound) (
  cons (mkAnchor "P0-CN" "UpReqDpoLoss.v:5" "rdl_dpo_total_loss_at_star" "UpReqDpoLoss.v" 5 (Some 5) StHit) (
  cons (mkAnchor "P0-CN" "G07_KLWall.v:3" "" "G07_KLWall.v" 3 (Some 3) StHit) (
  cons (mkAnchor "P0-CN" "G10_LoebFam.v:2" "" "G10_LoebFam.v" 2 (Some 2) StHit) (
  cons (mkAnchor "P0-CN" "S15_TailFEPUp.v:1" "" "S15_TailFEPUp.v" 1 (Some 2) StShift) (
  cons (mkAnchor "P0-EN" "S05_AlignmentGRPO.v:326" "rlhf_optimal" "S05_AlignmentGRPO.v" 326 (Some 326) StHit) (
  cons (mkAnchor "P0-EN" "UpReqLpoEquiv.v:245" "SqWall" "UpReqLpoEquiv.v" 245 (Some 245) StHit) (
  cons (mkAnchor "P0-EN" "UpReqLpoEquiv.v:249" "rLPO" "UpReqLpoEquiv.v" 249 (Some 249) StHit) (
  cons (mkAnchor "P0-EN" "UpReqLpoEquiv.v:264" "lpn_forward" "UpReqLpoEquiv.v" 264 (Some 264) StHit) (
  cons (mkAnchor "P0-EN" "UpReqLpoEquiv.v:357" "SqWall" "UpReqLpoEquiv.v" 357 (Some 357) StHit) (
  cons (mkAnchor "P0-EN" "DTPT_Bridge.v:12" "evaluated" "DTPT_Bridge.v" 12 (Some 12) StHit) (
  cons (mkAnchor "P0-EN" "UpReqIndex.v:404-413" "discipline" "UpReqIndex.v" 404 (None) StNotFound) (
  cons (mkAnchor "P0-EN" "UpReqIndex.v:442" "TotalModules_matches" "UpReqIndex.v" 442 (Some 309) StShift) (
  cons (mkAnchor "P0-EN" "UpReqIndex.v:494" "discipline" "UpReqIndex.v" 494 (None) StNotFound) (
  cons (mkAnchor "P0-EN" "S02_CauchyComplete.v:397" "Real" "S02_CauchyComplete.v" 397 (Some 397) StHit) (
  cons (mkAnchor "P0-EN" "S02_CauchyComplete.v:468" "real_lt" "S02_CauchyComplete.v" 468 (Some 468) StHit) (
  cons (mkAnchor "P0-EN" "S02_CauchyComplete.v:472" "real_le" "S02_CauchyComplete.v" 472 (Some 472) StHit) (
  cons (mkAnchor "P0-EN" "S01_BaseRing.v:73" "Id" "S01_BaseRing.v" 73 (None) StAmbiguous) (
  cons (mkAnchor "P0-EN" "S01_BaseRing.v:78-80" "Not" "S01_BaseRing.v" 78 (Some 80) StShift) (
  cons (mkAnchor "P0-EN" "S01_BaseRing.v:83-84" "ForallT" "S01_BaseRing.v" 83 (Some 84) StShift) (
  cons (mkAnchor "P0-EN" "S04_RealExpLogConv.v:2066" "free_energy" "S04_RealExpLogConv.v" 2066 (Some 2066) StHit) (
  cons (mkAnchor "P0-EN" "S04_RealExpLogConv.v:2817" "entropy" "S04_RealExpLogConv.v" 2817 (None) StNotFound) (
  cons (mkAnchor "P0-EN" "S06_DiffSamplingGibbs.v:228" "kl_divergence" "S06_DiffSamplingGibbs.v" 228 (Some 228) StHit) (
  cons (mkAnchor "P0-EN" "S06_DiffSamplingGibbs.v:4018" "tv_dist" "S06_DiffSamplingGibbs.v" 4018 (Some 4018) StHit) (
  cons (mkAnchor "P0-EN" "S05_AlignmentGRPO.v:147" "reward" "S05_AlignmentGRPO.v" 147 (None) StAmbiguous) (
  cons (mkAnchor "P0-EN" "S05_AlignmentGRPO.v:65" "pi_star" "S05_AlignmentGRPO.v" 65 (Some 65) StHit) (
  cons (mkAnchor "P0-EN" "S01_BaseRing.v:32-55" "Variables" "S01_BaseRing.v" 32 (Some 32) StHit) (
  cons (mkAnchor "P0-EN" "S05_AlignmentGRPO.v:1720" "rlhf_suboptimality_gap" "S05_AlignmentGRPO.v" 1720 (Some 1720) StHit) (
  cons (mkAnchor "P0-EN" "AttnHardLimit218.v:1017" "real_lt" "AttnHardLimit218.v" 1017 (None) StAmbiguous) (
  cons (mkAnchor "P0-EN" "S09_EntropyReal.v:4630" "real_eq" "S09_EntropyReal.v" 4630 (None) StAmbiguous) (
  cons (mkAnchor "P0-EN" "UpReqIndex.v:4" "library" "UpReqIndex.v" 4 (None) StNotFound) (
  cons (mkAnchor "P0-EN" "DTPT_Extract.v:45" "gate_pass" "DTPT_Extract.v" 45 (Some 45) StHit) (
  cons (mkAnchor "P0-EN" "DTPT_Extract.v:60" "gate_pass" "DTPT_Extract.v" 60 (Some 60) StHit) (
  cons (mkAnchor "P0-EN" "DTPT_Extract.v:64" "freq" "DTPT_Extract.v" 64 (Some 64) StHit) (
  cons (mkAnchor "P0-EN" "DTPT_Extract.v:102" "H_adj" "DTPT_Extract.v" 102 (Some 102) StHit) (
  cons (mkAnchor "P0-EN" "DTPT_Extract.v:115" "u12_phase_side_bool" "DTPT_Extract.v" 115 (Some 111) StShift) (
  cons (mkAnchor "P0-EN" "DTPT_Extract.v:130" "u12_gate_chain" "DTPT_Extract.v" 130 (Some 130) StHit) (
  cons (mkAnchor "P0-EN" "DTPT_Truth.v:231" "tarski" "DTPT_Truth.v" 231 (Some 231) StHit) (
  cons (mkAnchor "P0-EN" "UpReqIrrationalCriterion.v:285" "lic_irrational_criterion" "UpReqIrrationalCriterion.v" 285 (Some 285) StHit) (
  cons (mkAnchor "P0-EN" "UpReqIrrationalCriterion.v:37" "lic_" "UpReqIrrationalCriterion.v" 37 (None) StAmbiguous) (
  cons (mkAnchor "P0-EN" "S02_CauchyComplete.v:3084" "real_cauchy_complete" "S02_CauchyComplete.v" 3084 (Some 3084) StHit) (
  cons (mkAnchor "P0-EN" "S05_AlignmentGRPO.v:359" "dpo_optimal" "S05_AlignmentGRPO.v" 359 (Some 359) StHit) (
  cons (mkAnchor "P0-EN" "S05_AlignmentGRPO.v:386" "rlhf_optimal_unique" "S05_AlignmentGRPO.v" 386 (Some 386) StHit) (
  cons (mkAnchor "P0-EN" "S05_AlignmentGRPO.v:1456" "rlhf_free_energy_kl" "S05_AlignmentGRPO.v" 1456 (Some 1456) StHit) (
  cons (mkAnchor "P0-EN" "S05_AlignmentGRPO.v:1194" "ppo_gap_exact" "S05_AlignmentGRPO.v" 1194 (Some 1194) StHit) (
  cons (mkAnchor "P0-EN" "S05_AlignmentGRPO.v:1269" "ppo_gap_nonneg" "S05_AlignmentGRPO.v" 1269 (Some 1269) StHit) (
  cons (mkAnchor "P0-EN" "S05_AlignmentGRPO.v:763" "ppo_conservative" "S05_AlignmentGRPO.v" 763 (Some 763) StHit) (
  cons (mkAnchor "P0-EN" "S05_AlignmentGRPO.v:857" "dpo_reward_recovers_up_to_baseline" "S05_AlignmentGRPO.v" 857 (Some 857) StHit) (
  cons (mkAnchor "P0-EN" "S05_AlignmentGRPO.v:937" "dpo_reward_relative_exact" "S05_AlignmentGRPO.v" 937 (Some 937) StHit) (
  cons (mkAnchor "P0-EN" "S05_AlignmentGRPO.v:2212" "dpo_loss_pi_star_bounded" "S05_AlignmentGRPO.v" 2212 (Some 2212) StHit) (
  cons (mkAnchor "P0-EN" "S05_AlignmentGRPO.v:4991" "grpo_advantage_zero_mean" "S05_AlignmentGRPO.v" 4991 (Some 4991) StHit) (
  cons (mkAnchor "P0-EN" "S05_AlignmentGRPO.v:4228" "policy_iter_kl_geom_step" "S05_AlignmentGRPO.v" 4228 (Some 4228) StHit) (
  cons (mkAnchor "P0-EN" "S05_AlignmentGRPO.v:4263" "policy_iter_kl_geom_iter" "S05_AlignmentGRPO.v" 4263 (Some 4263) StHit) (
  cons (mkAnchor "P0-EN" "S05_AlignmentGRPO.v:4326" "dpo_loss_iter_step_le" "S05_AlignmentGRPO.v" 4326 (Some 4326) StHit) (
  cons (mkAnchor "P0-EN" "S05_AlignmentGRPO.v:3670" "policy_iter_backward_kl_step_beta" "S05_AlignmentGRPO.v" 3670 (Some 3670) StHit) (
  cons (mkAnchor "P0-EN" "S05_AlignmentGRPO.v:3885" "one" "S05_AlignmentGRPO.v" 3885 (None) StAmbiguous) (
  cons (mkAnchor "P0-EN" "S05_AlignmentGRPO.v:4654" "u2_fixed_point_unique" "S05_AlignmentGRPO.v" 4654 (Some 4654) StHit) (
  cons (mkAnchor "P0-EN" "S05_AlignmentGRPO.v:4845" "u2_objective_eq_optimal_iff" "S05_AlignmentGRPO.v" 4845 (Some 4845) StHit) (
  cons (mkAnchor "P0-EN" "S15_TailFEPUp.v:1030" "real_step_kl_eta_bound_eps" "S15_TailFEPUp.v" 1030 (Some 1030) StHit) (
  cons (mkAnchor "P0-EN" "S15_TailFEPUp.v:1682" "prerequisites" "S15_TailFEPUp.v" 1682 (Some 1681) StShift) (
  cons (mkAnchor "P0-EN" "S15_TailFEPUp.v:1721" "grpo_uniform_mass" "S15_TailFEPUp.v" 1721 (Some 1721) StHit) (
  cons (mkAnchor "P0-EN" "S08_RealMainlineDPO.v:2029" "real_attention_is_gibbs" "S08_RealMainlineDPO.v" 2029 (Some 2029) StHit) (
  cons (mkAnchor "P0-EN" "S10_KVQuantTrig.v:12374" "attention_is_gibbs_setoid" "S10_KVQuantTrig.v" 12374 (Some 12374) StHit) (
  cons (mkAnchor "P0-EN" "S08_RealMainlineDPO.v:2120" "real_steady_state_boltzmann_attn" "S08_RealMainlineDPO.v" 2120 (Some 2120) StHit) (
  cons (mkAnchor "P0-EN" "S10_KVQuantTrig.v:12451" "setoid" "S10_KVQuantTrig.v" 12451 (Some 12451) StHit) (
  cons (mkAnchor "P0-EN" "S15_TailFEPUp.v:108" "attention_minimizes_free_energy_unique" "S15_TailFEPUp.v" 108 (Some 108) StHit) (
  cons (mkAnchor "P0-EN" "S15_TailFEPUp.v:1971" "F_attn" "S15_TailFEPUp.v" 1971 (Some 1932) StShift) (
  cons (mkAnchor "P0-EN" "AttnDoeblin.v:318" "u_tv_contraction" "AttnDoeblin.v" 318 (Some 332) StShift) (
  cons (mkAnchor "P0-EN" "AttnDoeblin.v:392" "u_titer" "AttnDoeblin.v" 392 (Some 406) StShift) (
  cons (mkAnchor "P0-EN" "AttnDoeblin.v:406" "u_titer" "AttnDoeblin.v" 406 (Some 406) StHit) (
  cons (mkAnchor "P0-EN" "AttnDoeblin.v:724" "bounded_softmax_tv_contraction" "AttnDoeblin.v" 724 (Some 738) StShift) (
  cons (mkAnchor "P0-EN" "AttnDoeblin.v:737" "contraction" "AttnDoeblin.v" 737 (Some 738) StShift) (
  cons (mkAnchor "P0-EN" "AttnDoeblin.v:757" "real_expf_realizable" "AttnDoeblin.v" 757 (Some 771) StShift) (
  cons (mkAnchor "P0-EN" "S13_NLiveAudit.v:3096" "real_expf_realizable" "S13_NLiveAudit.v" 3096 (Some 3096) StHit) (
  cons (mkAnchor "P0-EN" "S08_RealMainlineDPO.v:2190" "real_minp_markov_kernel_normalized" "S08_RealMainlineDPO.v" 2190 (Some 2190) StHit) (
  cons (mkAnchor "P0-EN" "S08_RealMainlineDPO.v:2285" "real_top_k_majorization" "S08_RealMainlineDPO.v" 2285 (Some 2285) StHit) (
  cons (mkAnchor "P0-EN" "S09_EntropyReal.v:4673" "real_gradient_zero_neg_entropy_truth" "S09_EntropyReal.v" 4673 (Some 4673) StHit) (
  cons (mkAnchor "P0-EN" "S09_EntropyReal.v:4746" "real_gradient_step_contraction" "S09_EntropyReal.v" 4746 (Some 4746) StShift) (
  cons (mkAnchor "P0-EN" "S09_EntropyReal.v:6175" "real_grad_step_abs_contraction_full" "S09_EntropyReal.v" 6175 (Some 6175) StShift) (
  cons (mkAnchor "P0-EN" "S09_EntropyReal.v:5015" "real_grad_decay_positive_iter" "S09_EntropyReal.v" 5015 (Some 5015) StShift) (
  cons (mkAnchor "P0-EN" "S09_EntropyReal.v:6113" "decay" "S09_EntropyReal.v" 6113 (Some 6113) StHit) (
  cons (mkAnchor "P0-EN" "S15_TailFEPUp.v:280" "ppo_is_decomp" "S15_TailFEPUp.v" 280 (Some 280) StHit) (
  cons (mkAnchor "P0-EN" "S15_TailFEPUp.v:290" "clip_error_nonneg" "S15_TailFEPUp.v" 290 (Some 290) StHit) (
  cons (mkAnchor "P0-EN" "S15_TailFEPUp.v:318" "ppo_clipped_improvement" "S15_TailFEPUp.v" 318 (Some 318) StHit) (
  cons (mkAnchor "P0-EN" "UpReqGibbsWallEquiv.v:172" "gwe_G" "UpReqGibbsWallEquiv.v" 172 (Some 172) StHit) (
  cons (mkAnchor "P0-EN" "UpReqGibbsWallEquiv.v:176" "GibbsWall" "UpReqGibbsWallEquiv.v" 176 (Some 176) StHit) (
  cons (mkAnchor "P0-EN" "UpReqGibbsWallEquiv.v:186" "gwe_diag_zero" "UpReqGibbsWallEquiv.v" 186 (Some 186) StHit) (
  cons (mkAnchor "P0-EN" "UpReqGibbsWallEquiv.v:252" "GibbsWall" "UpReqGibbsWallEquiv.v" 252 (Some 252) StHit) (
  cons (mkAnchor "P0-EN" "UpReqGibbsWallEquiv.v:264" "GibbsWall" "UpReqGibbsWallEquiv.v" 264 (Some 264) StHit) (
  cons (mkAnchor "P0-EN" "UpReqGibbsWallEquiv.v:299" "gmech_wall_lpo" "UpReqGibbsWallEquiv.v" 299 (Some 307) StShift) (
  cons (mkAnchor "P0-EN" "UpReqGibbsWallEquiv.v:307" "gmech_wall_lpo" "UpReqGibbsWallEquiv.v" 307 (Some 307) StHit) (
  cons (mkAnchor "P0-EN" "UpReqLogZWallEquiv.v:326" "lgz_LogZWall" "UpReqLogZWallEquiv.v" 326 (Some 338) StShift) (
  cons (mkAnchor "P0-EN" "UpReqLogZWallEquiv.v:351" "lgmech_wall_zle" "UpReqLogZWallEquiv.v" 351 (Some 363) StShift) (
  cons (mkAnchor "P0-EN" "UpReqLogZWallEquiv.v:500" "lgz_log_z_wall_lpo" "UpReqLogZWallEquiv.v" 500 (Some 512) StShift) (
  cons (mkAnchor "P0-EN" "UpReqLogZWallEquiv.v:655" "lgz_lpo_zle" "UpReqLogZWallEquiv.v" 655 (Some 667) StShift) (
  cons (mkAnchor "P0-EN" "UpReqSquareWallEquiv.v:144" "snw_b_lift" "UpReqSquareWallEquiv.v" 144 (Some 132) StShift) (
  cons (mkAnchor "P0-EN" "UpReqSquareWallEquiv.v:56" "SqWall" "UpReqSquareWallEquiv.v" 56 (None) StAmbiguous) (
  cons (mkAnchor "P0-EN" "UpReqSquareWallEquiv.v:61" "snw_b_lift" "UpReqSquareWallEquiv.v" 61 (None) StAmbiguous) (
  cons (mkAnchor "P0-EN" "UpReqSquareWallEquiv.v:74" "snw_b_lift" "UpReqSquareWallEquiv.v" 74 (None) StAmbiguous) (
  cons (mkAnchor "P0-EN" "UpReqSquareWallEquiv.v:92" "rLPO" "UpReqSquareWallEquiv.v" 92 (None) StAmbiguous) (
  cons (mkAnchor "P0-EN" "PinskerCoreClose.v:138" "pkc_sign_load" "PinskerCoreClose.v" 138 (None) StDeadFile) (
  cons (mkAnchor "P0-EN" "G07_KLWall.v:1615" "point" "G07_KLWall.v" 1615 (None) StAmbiguous) (
  cons (mkAnchor "P0-EN" "G07_KLWall.v:1827" "point" "G07_KLWall.v" 1827 (Some 1883) StShift) (
  cons (mkAnchor "P0-EN" "G07_KLWall.v:1847" "point" "G07_KLWall.v" 1847 (Some 1883) StShift) (
  cons (mkAnchor "P0-EN" "G07_KLWall.v:1955" "point" "G07_KLWall.v" 1955 (Some 1927) StShift) (
  cons (mkAnchor "P0-EN" "DTPT_Truth.v:243" "no_uniform_truth" "DTPT_Truth.v" 243 (Some 243) StHit) (
  cons (mkAnchor "P0-EN" "DTPT_Truth.v:326" "truth" "DTPT_Truth.v" 326 (None) StAmbiguous) (
  cons (mkAnchor "P0-EN" "DTPT_Truth.v:355" "truth" "DTPT_Truth.v" 355 (None) StAmbiguous) (
  cons (mkAnchor "P0-EN" "DTPT_Truth.v:374" "level_confusion_revives_liar" "DTPT_Truth.v" 374 (Some 374) StHit) (
  cons (mkAnchor "P0-EN" "DTPT_Truth.v:409" "tarski_via_renaming" "DTPT_Truth.v" 409 (Some 409) StHit) (
  cons (mkAnchor "P0-EN" "DTPT_Entropy.v:135" "H_shannon_q_perm_inv_counterex" "DTPT_Entropy.v" 135 (Some 135) StHit) (
  cons (mkAnchor "P0-EN" "DTPT_Entropy.v:481" "H_lam_cross_phase_bounds" "DTPT_Entropy.v" 481 (Some 481) StHit) (
  cons (mkAnchor "P0-EN" "G10_LoebFam.v:719" "Prf_soundness" "G10_LoebFam.v" 719 (Some 719) StHit) (
  cons (mkAnchor "P0-EN" "G10_LoebFam.v:808" "diagonal_lemma" "G10_LoebFam.v" 808 (Some 808) StHit) (
  cons (mkAnchor "P0-EN" "UpReqIrrationalCriterion.v:758" "lic_e_irrational_criterion" "UpReqIrrationalCriterion.v" 758 (Some 758) StHit) (
  cons (mkAnchor "P0-EN" "UpReqIrrationalCriterion.v:769" "step" "UpReqIrrationalCriterion.v" 769 (None) StNotFound) (
  cons (mkAnchor "P0-EN" "UpReqIrrationalInstances.v:1301" "ir2_sqrt2_irrational_criterion" "UpReqIrrationalInstances.v" 1301 (Some 1301) StHit) (
  cons (mkAnchor "P0-EN" "UpReqSqrt3Irrational.v:1102" "is3_sqrt3_irrational_criterion" "UpReqSqrt3Irrational.v" 1102 (Some 1102) StHit) (
  cons (mkAnchor "P0-EN" "UpReqLn2Irrational.v:364" "ln2i_irrational_criterion_cond" "UpReqLn2Irrational.v" 364 (Some 364) StHit) (
  cons (mkAnchor "P0-EN" "Ln2Escape.v:253" "lne_beta_value" "Ln2Escape.v" 253 (Some 253) StHit) (
  cons (mkAnchor "P0-EN" "Ln2Escape.v:453" "lne_B_le_p4" "Ln2Escape.v" 453 (Some 453) StHit) (
  cons (mkAnchor "P0-EN" "Ln2Escape.v:477" "lne_B_int" "Ln2Escape.v" 477 (Some 477) StHit) (
  cons (mkAnchor "P0-EN" "Ln2Escape.v:507" "lne_B_posT" "Ln2Escape.v" 507 (Some 507) StHit) (
  cons (mkAnchor "P0-EN" "Ln2Escape.v:559" "lne_ln2_irrational_cond" "Ln2Escape.v" 559 (Some 559) StHit) (
  cons (mkAnchor "P0-EN" "Ln2Integrality.v:257" "pi_Pn_int" "Ln2Integrality.v" 257 (Some 257) StHit) (
  cons (mkAnchor "P0-EN" "Ln2Integrality.v:274" "pi_Qn_le_8pow" "Ln2Integrality.v" 274 (Some 274) StHit) (
  cons (mkAnchor "P0-EN" "Ln2Integrality.v:426" "pi_den_divide" "Ln2Integrality.v" 426 (Some 426) StHit) (
  cons (mkAnchor "P0-EN" "BeukersIdentity.v:62" "bi_norm_factor" "BeukersIdentity.v" 62 (Some 62) StHit) (
  cons (mkAnchor "P0-EN" "S01_BaseRing.v:78" "And" "S01_BaseRing.v" 78 (Some 78) StHit) (
  cons (mkAnchor "P0-EN" "S01_BaseRing.v:79" "Not" "S01_BaseRing.v" 79 (Some 80) StShift) (
  cons (mkAnchor "P0-EN" "S01_BaseRing.v:80" "Not" "S01_BaseRing.v" 80 (Some 80) StHit) (
  cons (mkAnchor "P0-EN" "S01_BaseRing.v:83" "ExistsT" "S01_BaseRing.v" 83 (Some 83) StHit) (
  cons (mkAnchor "P0-EN" "S01_BaseRing.v:84" "ForallT" "S01_BaseRing.v" 84 (Some 84) StHit) (
  cons (mkAnchor "P0-EN" "S06_DiffSamplingGibbs.v:3181" "partition_function" "S06_DiffSamplingGibbs.v" 3181 (Some 3181) StHit) (
  cons (mkAnchor "P0-EN" "S06_DiffSamplingGibbs.v:3334" "softmax_temp" "S06_DiffSamplingGibbs.v" 3334 (Some 3334) StHit) (
  cons (mkAnchor "P0-EN" "S06_DiffSamplingGibbs.v:3823" "Z_thermo" "S06_DiffSamplingGibbs.v" 3823 (Some 3823) StHit) (
  cons (mkAnchor "P0-EN" "S05_AlignmentGRPO.v:353" "dpo_loss" "S05_AlignmentGRPO.v" 353 (Some 353) StHit) (
  cons (mkAnchor "P0-EN" "S05_AlignmentGRPO.v:821" "ppo_surrogate" "S05_AlignmentGRPO.v" 821 (Some 821) StHit) (
  cons (mkAnchor "P0-EN" "S05_AlignmentGRPO.v:2420" "energy_t" "S05_AlignmentGRPO.v" 2420 (Some 2420) StHit) (
  cons (mkAnchor "P0-EN" "UpReqAlgebra.v:89" "req_minus" "UpReqAlgebra.v" 89 (Some 103) StShift) (
  cons (mkAnchor "P0-EN" "UpReqSquareWallEquiv.v:44" "snw_wall" "UpReqSquareWallEquiv.v" 44 (None) StAmbiguous) (
  cons (mkAnchor "P0-EN" "AttnDoeblin.v:154" "omd" "AttnDoeblin.v" 154 (None) StAmbiguous) (
  cons (mkAnchor "P0-EN" "AttnDoeblin.v:541" "delta_star" "AttnDoeblin.v" 541 (None) StAmbiguous) (
  cons (mkAnchor "P0-EN" "DTPT.v:3" "code" "DTPT.v" 3 (Some 3) StHit) (
  cons (mkAnchor "P0-EN" "DTPT_Bridge.v:3" "level" "DTPT_Bridge.v" 3 (None) StNotFound) (
  cons (mkAnchor "P0-EN" "S12_B5RecycleSF.v:15" "b5e_pern_main" "S12_B5RecycleSF.v" 15 (None) StNotFound) (
  cons (mkAnchor "P0-EN" "S12_B5RecycleSF.v:2046" "b5e_pern_main" "S12_B5RecycleSF.v" 2046 (Some 2046) StHit) (
  cons (mkAnchor "P0-EN" "DTPT_Extract.v:31-39" "statistical" "DTPT_Extract.v" 31 (Some 15) StShift) (
  cons (mkAnchor "P0-EN" "UpReqAlgebra.v:30" "the" "UpReqAlgebra.v" 30 (Some 25) StShift) (
  cons (mkAnchor "P0-EN" "UpReqDpoLoss.v:5" "rdl_dpo_total_loss_at_st" "UpReqDpoLoss.v" 5 (Some 185) StShift) (
  cons (mkAnchor "P0-EN" "G07_KLWall.v:3" "strict" "G07_KLWall.v" 3 (None) StNotFound) (
  cons (mkAnchor "P0-EN" "G10_LoebFam.v:2" "family" "G10_LoebFam.v" 2 (None) StNotFound) (
  cons (mkAnchor "P0-EN" "S15_TailFEPUp.v:1" "five" "S15_TailFEPUp.v" 1 (Some 2) StShift) (
  cons (mkAnchor "P0-TEX" "S05_AlignmentGRPO.v:326" "_optimal" "S05_AlignmentGRPO.v" 326 (Some 326) StHit) (
  cons (mkAnchor "P0-TEX" "UpReqLpoEquiv.v:245" "SqWall" "UpReqLpoEquiv.v" 245 (Some 245) StHit) (
  cons (mkAnchor "P0-TEX" "UpReqLpoEquiv.v:249" "rLPO" "UpReqLpoEquiv.v" 249 (Some 249) StHit) (
  cons (mkAnchor "P0-TEX" "UpReqLpoEquiv.v:264" "rLPO" "UpReqLpoEquiv.v" 264 (Some 264) StHit) (
  cons (mkAnchor "P0-TEX" "UpReqIndex.v:404" "discipline" "UpReqIndex.v" 404 (None) StNotFound) (
  cons (mkAnchor "P0-TEX" "UpReqIndex.v:413" "" "UpReqIndex.v" 413 (Some 413) StHit) (
  cons (mkAnchor "P0-TEX" "UpReqIndex.v:442" "reflexivity" "UpReqIndex.v" 442 (None) StAmbiguous) (
  cons (mkAnchor "P0-TEX" "S01_BaseRing.v:73" "per" "S01_BaseRing.v" 73 (None) StNotFound) (
  cons (mkAnchor "P0-TEX" "S02_CauchyComplete.v:397" "cauchy" "S02_CauchyComplete.v" 397 (Some 397) StHit) (
  cons (mkAnchor "P0-TEX" "S02_CauchyComplete.v:468" "_lt" "S02_CauchyComplete.v" 468 (Some 468) StHit) (
  cons (mkAnchor "P0-TEX" "S02_CauchyComplete.v:472" "real_eq" "S02_CauchyComplete.v" 472 (Some 473) StShift) (
  cons (mkAnchor "P0-TEX" "S02_CauchyComplete.v:3084" "_complete" "S02_CauchyComplete.v" 3084 (Some 3084) StHit) (
  cons (mkAnchor "P0-TEX" "S01_BaseRing.v:78" "And" "S01_BaseRing.v" 78 (Some 78) StHit) (
  cons (mkAnchor "P0-TEX" "S01_BaseRing.v:80" "product" "S01_BaseRing.v" 80 (None) StNotFound) (
  cons (mkAnchor "P0-TEX" "S01_BaseRing.v:83" "ExistsT" "S01_BaseRing.v" 83 (Some 83) StHit) (
  cons (mkAnchor "P0-TEX" "S01_BaseRing.v:84" "ForallT" "S01_BaseRing.v" 84 (Some 84) StHit) (
  cons (mkAnchor "P0-TEX" "S04_RealExpLogConv.v:2066" "free_energy" "S04_RealExpLogConv.v" 2066 (Some 2066) StHit) (
  cons (mkAnchor "P0-TEX" "S04_RealExpLogConv.v:2817" "entropy" "S04_RealExpLogConv.v" 2817 (None) StNotFound) (
  cons (mkAnchor "P0-TEX" "S06_DiffSamplingGibbs.v:228" "kl_divergence" "S06_DiffSamplingGibbs.v" 228 (Some 228) StHit) (
  cons (mkAnchor "P0-TEX" "S06_DiffSamplingGibbs.v:4018" "tv_dist" "S06_DiffSamplingGibbs.v" 4018 (Some 4018) StHit) (
  cons (mkAnchor "P0-TEX" "S05_AlignmentGRPO.v:147" "reward" "S05_AlignmentGRPO.v" 147 (None) StAmbiguous) (
  cons (mkAnchor "P0-TEX" "S05_AlignmentGRPO.v:65" "pi_star" "S05_AlignmentGRPO.v" 65 (Some 65) StHit) (
  cons (mkAnchor "P0-TEX" "S01_BaseRing.v:32" "Variables" "S01_BaseRing.v" 32 (Some 32) StHit) (
  cons (mkAnchor "P0-TEX" "S01_BaseRing.v:55" "self" "S01_BaseRing.v" 55 (None) StNotFound) (
  cons (mkAnchor "P0-TEX" "S08_RealMainlineDPO.v:1898" "non" "S08_RealMainlineDPO.v" 1898 (None) StNotFound) (
  cons (mkAnchor "P0-TEX" "S05_AlignmentGRPO.v:1720" "align_objective" "S05_AlignmentGRPO.v" 1720 (None) StAmbiguous) (
  cons (mkAnchor "P0-TEX" "S08_RealMainlineDPO.v:2604" "varepsilon" "S08_RealMainlineDPO.v" 2604 (Some 2605) StShift) (
  cons (mkAnchor "P0-TEX" "S15_TailFEPUp.v:108" "minimizes" "S15_TailFEPUp.v" 108 (Some 108) StHit) (
  cons (mkAnchor "P0-TEX" "AttnHardLimit218.v:1017" "eps" "AttnHardLimit218.v" 1017 (Some 1031) StShift) (
  cons (mkAnchor "P0-TEX" "AttnDoeblin.v:724" "delta" "AttnDoeblin.v" 724 (None) StNotFound) (
  cons (mkAnchor "P0-TEX" "S09_EntropyReal.v:4615" "real_dynamics" "S09_EntropyReal.v" 4615 (None) StNotFound) (
  cons (mkAnchor "P0-TEX" "S09_EntropyReal.v:4616" "real_dynamics" "S09_EntropyReal.v" 4616 (None) StNotFound) (
  cons (mkAnchor "P0-TEX" "S09_EntropyReal.v:4630" "gradient" "S09_EntropyReal.v" 4630 (Some 4630) StHit) (
  cons (mkAnchor "P0-TEX" "UpReqAlgebra.v:89" "req_minus" "UpReqAlgebra.v" 89 (Some 103) StShift) (
  cons (mkAnchor "P0-TEX" "DTPT_Extract.v:45" "gate_pass" "DTPT_Extract.v" 45 (Some 45) StHit) (
  cons (mkAnchor "P0-TEX" "DTPT_Extract.v:60" "gate_pass" "DTPT_Extract.v" 60 (Some 60) StHit) (
  cons (mkAnchor "P0-TEX" "DTPT_Extract.v:64" "freq" "DTPT_Extract.v" 64 (Some 64) StHit) (
  cons (mkAnchor "P0-TEX" "DTPT_Extract.v:102" "H_adj" "DTPT_Extract.v" 102 (Some 102) StHit) (
  cons (mkAnchor "P0-TEX" "DTPT_Extract.v:115" "u12_phase_side_bool" "DTPT_Extract.v" 115 (Some 111) StShift) (
  cons (mkAnchor "P0-TEX" "DTPT_Extract.v:130" "u12_gate_chain" "DTPT_Extract.v" 130 (Some 130) StHit) (
  cons (mkAnchor "P0-TEX" "DTPT_Truth.v:231" "tarski" "DTPT_Truth.v" 231 (Some 231) StHit) (
  cons (mkAnchor "P0-TEX" "DTPT_Extract.v:31" "surface" "DTPT_Extract.v" 31 (Some 15) StShift) (
  cons (mkAnchor "P0-TEX" "DTPT_Extract.v:39" "" "DTPT_Extract.v" 39 (Some 23) StShift) (
  cons (mkAnchor "P0-TEX" "UpReqIrrationalCriterion.v:285" "lic" "UpReqIrrationalCriterion.v" 285 (Some 285) StHit) (
  cons (mkAnchor "P0-TEX" "UpReqIrrationalCriterion.v:758" "lic_e_irrational_criterion" "UpReqIrrationalCriterion.v" 758 (Some 758) StHit) (
  cons (mkAnchor "P0-TEX" "UpReqIrrationalCriterion.v:769" "assembly" "UpReqIrrationalCriterion.v" 769 (Some 768) StShift) (
  cons (mkAnchor "P0-TEX" "UpReqIrrationalInstances.v:1301" "ir2_sqrt2_irrational_criterion" "UpReqIrrationalInstances.v" 1301 (Some 1301) StHit) (
  cons (mkAnchor "P0-TEX" "UpReqSqrt3Irrational.v:1102" "is3_sqrt3_irrational_criterion" "UpReqSqrt3Irrational.v" 1102 (Some 1102) StHit) (
  cons (mkAnchor "P0-TEX" "UpReqLn2Irrational.v:364" "ln2i_irrational_criterion_cond" "UpReqLn2Irrational.v" 364 (Some 364) StHit) (
  cons (mkAnchor "P0-TEX" "S12_B5RecycleSF.v:21" "zero" "S12_B5RecycleSF.v" 21 (Some 56) StShift) (
  cons (mkAnchor "P0-TEX" "UpReqIrrationalCriterion.v:37" "lic" "UpReqIrrationalCriterion.v" 37 (None) StAmbiguous) (
  cons (mkAnchor "P0-TEX" "S05_AlignmentGRPO.v:359" "_optimal" "S05_AlignmentGRPO.v" 359 (Some 359) StHit) (
  cons (mkAnchor "P0-TEX" "S05_AlignmentGRPO.v:386" "_unique" "S05_AlignmentGRPO.v" 386 (Some 386) StHit) (
  cons (mkAnchor "P0-TEX" "S05_AlignmentGRPO.v:1456" "free_energy" "S05_AlignmentGRPO.v" 1456 (None) StAmbiguous) (
  cons (mkAnchor "P0-TEX" "S05_AlignmentGRPO.v:1194" "_exact" "S05_AlignmentGRPO.v" 1194 (Some 1194) StHit) (
  cons (mkAnchor "P0-TEX" "S05_AlignmentGRPO.v:1269" "_nonneg" "S05_AlignmentGRPO.v" 1269 (Some 1269) StHit) (
  cons (mkAnchor "P0-TEX" "S05_AlignmentGRPO.v:763" "_conservative" "S05_AlignmentGRPO.v" 763 (Some 763) StHit) (
  cons (mkAnchor "P0-TEX" "S05_AlignmentGRPO.v:857" "dpo_reward_explicit" "S05_AlignmentGRPO.v" 857 (Some 844) StShift) (
  cons (mkAnchor "P0-TEX" "S05_AlignmentGRPO.v:937" "implicit" "S05_AlignmentGRPO.v" 937 (None) StAmbiguous) (
  cons (mkAnchor "P0-TEX" "S05_AlignmentGRPO.v:2212" "reward_l" "S05_AlignmentGRPO.v" 2212 (Some 2213) StShift) (
  cons (mkAnchor "P0-TEX" "S05_AlignmentGRPO.v:4991" "zero" "S05_AlignmentGRPO.v" 4991 (None) StAmbiguous) (
  cons (mkAnchor "P0-TEX" "S05_AlignmentGRPO.v:4228" "relative_entropy" "S05_AlignmentGRPO.v" 4228 (None) StAmbiguous) (
  cons (mkAnchor "P0-TEX" "S05_AlignmentGRPO.v:4263" "relative_entropy" "S05_AlignmentGRPO.v" 4263 (None) StAmbiguous) (
  cons (mkAnchor "P0-TEX" "S05_AlignmentGRPO.v:4326" "loss" "S05_AlignmentGRPO.v" 4326 (Some 4326) StHit) (
  cons (mkAnchor "P0-TEX" "S05_AlignmentGRPO.v:3670" "_le" "S05_AlignmentGRPO.v" 3670 (None) StNotFound) (
  cons (mkAnchor "P0-TEX" "S05_AlignmentGRPO.v:3885" "one" "S05_AlignmentGRPO.v" 3885 (None) StAmbiguous) (
  cons (mkAnchor "P0-TEX" "S05_AlignmentGRPO.v:4654" "fixed" "S05_AlignmentGRPO.v" 4654 (Some 4654) StHit) (
  cons (mkAnchor "P0-TEX" "S05_AlignmentGRPO.v:4845" "objective" "S05_AlignmentGRPO.v" 4845 (Some 4845) StHit) (
  cons (mkAnchor "P0-TEX" "S15_TailFEPUp.v:1030" "eps" "S15_TailFEPUp.v" 1030 (None) StAmbiguous) (
  cons (mkAnchor "P0-TEX" "S15_TailFEPUp.v:1721" "_mass" "S15_TailFEPUp.v" 1721 (Some 1721) StHit) (
  cons (mkAnchor "P0-TEX" "S08_RealMainlineDPO.v:2029" "under" "S08_RealMainlineDPO.v" 2029 (Some 2030) StShift) (
  cons (mkAnchor "P0-TEX" "S10_KVQuantTrig.v:12374" "setoid" "S10_KVQuantTrig.v" 12374 (Some 12374) StHit) (
  cons (mkAnchor "P0-TEX" "S08_RealMainlineDPO.v:2120" "attention" "S08_RealMainlineDPO.v" 2120 (Some 2029) StShift) (
  cons (mkAnchor "P0-TEX" "S10_KVQuantTrig.v:12451" "its" "S10_KVQuantTrig.v" 12451 (Some 12354) StShift) (
  cons (mkAnchor "P0-TEX" "S15_TailFEPUp.v:1971" "F_attn" "S15_TailFEPUp.v" 1971 (Some 1932) StShift) (
  cons (mkAnchor "P0-TEX" "AttnDoeblin.v:318" "_contraction" "AttnDoeblin.v" 318 (Some 332) StShift) (
  cons (mkAnchor "P0-TEX" "AttnDoeblin.v:406" "_iter" "AttnDoeblin.v" 406 (Some 420) StShift) (
  cons (mkAnchor "P0-TEX" "AttnDoeblin.v:392" "u_titer" "AttnDoeblin.v" 392 (Some 406) StShift) (
  cons (mkAnchor "P0-TEX" "AttnDoeblin.v:737" "the" "AttnDoeblin.v" 737 (Some 729) StShift) (
  cons (mkAnchor "P0-TEX" "AttnDoeblin.v:757" "_realizable" "AttnDoeblin.v" 757 (Some 771) StShift) (
  cons (mkAnchor "P0-TEX" "S13_NLiveAudit.v:3096" "version" "S13_NLiveAudit.v" 3096 (None) StNotFound) (
  cons (mkAnchor "P0-TEX" "S08_RealMainlineDPO.v:2190" "min" "S08_RealMainlineDPO.v" 2190 (Some 2190) StHit) (
  cons (mkAnchor "P0-TEX" "S08_RealMainlineDPO.v:2285" "top" "S08_RealMainlineDPO.v" 2285 (Some 2285) StHit) (
  cons (mkAnchor "P0-TEX" "S09_EntropyReal.v:4673" "entropy" "S09_EntropyReal.v" 4673 (Some 4673) StHit) (
  cons (mkAnchor "P0-TEX" "S09_EntropyReal.v:4746" "eta" "S09_EntropyReal.v" 4746 (None) StAmbiguous) (
  cons (mkAnchor "P0-TEX" "S09_EntropyReal.v:6175" "all" "S09_EntropyReal.v" 6175 (Some 6175) StHit) (
  cons (mkAnchor "P0-TEX" "S09_EntropyReal.v:5015" "" "S09_EntropyReal.v" 5015 (Some 5015) StHit) (
  cons (mkAnchor "P0-TEX" "S09_EntropyReal.v:6113" "" "S09_EntropyReal.v" 6113 (Some 6113) StHit) (
  cons (mkAnchor "P0-TEX" "S15_TailFEPUp.v:280" "_decomp" "S15_TailFEPUp.v" 280 (Some 280) StHit) (
  cons (mkAnchor "P0-TEX" "S15_TailFEPUp.v:290" "_nonneg" "S15_TailFEPUp.v" 290 (Some 290) StHit) (
  cons (mkAnchor "P0-TEX" "S15_TailFEPUp.v:318" "clipped" "S15_TailFEPUp.v" 318 (Some 318) StHit) (
  cons (mkAnchor "P0-TEX" "UpReqLpoEquiv.v:357" "wall" "UpReqLpoEquiv.v" 357 (None) StNotFound) (
  cons (mkAnchor "P0-TEX" "UpReqGibbsWallEquiv.v:176" "GibbsWall" "UpReqGibbsWallEquiv.v" 176 (Some 176) StHit) (
  cons (mkAnchor "P0-TEX" "UpReqGibbsWallEquiv.v:172" "gwe_G" "UpReqGibbsWallEquiv.v" 172 (Some 172) StHit) (
  cons (mkAnchor "P0-TEX" "UpReqGibbsWallEquiv.v:186" "gwe_diag_zero" "UpReqGibbsWallEquiv.v" 186 (Some 186) StHit) (
  cons (mkAnchor "P0-TEX" "UpReqGibbsWallEquiv.v:252" "" "UpReqGibbsWallEquiv.v" 252 (Some 230) StShift) (
  cons (mkAnchor "P0-TEX" "UpReqGibbsWallEquiv.v:264" "GibbsWall" "UpReqGibbsWallEquiv.v" 264 (Some 264) StHit) (
  cons (mkAnchor "P0-TEX" "UpReqGibbsWallEquiv.v:299" "" "UpReqGibbsWallEquiv.v" 299 (Some 277) StShift) (
  cons (mkAnchor "P0-TEX" "UpReqGibbsWallEquiv.v:307" "" "UpReqGibbsWallEquiv.v" 307 (Some 285) StShift) (
  cons (mkAnchor "P0-TEX" "UpReqLogZWallEquiv.v:326" "lgz" "UpReqLogZWallEquiv.v" 326 (None) StAmbiguous) (
  cons (mkAnchor "P0-TEX" "UpReqLogZWallEquiv.v:351" "lgmech_wall_zle" "UpReqLogZWallEquiv.v" 351 (Some 363) StShift) (
  cons (mkAnchor "P0-TEX" "UpReqLogZWallEquiv.v:500" "lgz_log_z_wall_lpo" "UpReqLogZWallEquiv.v" 500 (Some 512) StShift) (
  cons (mkAnchor "P0-TEX" "UpReqLogZWallEquiv.v:655" "lgz_lpo_zle" "UpReqLogZWallEquiv.v" 655 (Some 667) StShift) (
  cons (mkAnchor "P0-TEX" "UpReqSquareWallEquiv.v:56" "" "UpReqSquareWallEquiv.v" 56 (Some 56) StHit) (
  cons (mkAnchor "P0-TEX" "UpReqSquareWallEquiv.v:61" "snw_b_lift" "UpReqSquareWallEquiv.v" 61 (None) StAmbiguous) (
  cons (mkAnchor "P0-TEX" "UpReqSquareWallEquiv.v:74" "rLPO" "UpReqSquareWallEquiv.v" 74 (None) StAmbiguous) (
  cons (mkAnchor "P0-TEX" "UpReqSquareWallEquiv.v:92" "slot" "UpReqSquareWallEquiv.v" 92 (None) StNotFound) (
  cons (mkAnchor "P0-TEX" "UpReqSquareWallEquiv.v:144" "" "UpReqSquareWallEquiv.v" 144 (Some 132) StShift) (
  cons (mkAnchor "P0-TEX" "PinskerCoreClose.v:138" "extraction" "PinskerCoreClose.v" 138 (None) StDeadFile) (
  cons (mkAnchor "P0-TEX" "G07_KLWall.v:1615" "family" "G07_KLWall.v" 1615 (Some 1632) StShift) (
  cons (mkAnchor "P0-TEX" "G07_KLWall.v:1827" "" "G07_KLWall.v" 1827 (Some 1844) StShift) (
  cons (mkAnchor "P0-TEX" "G07_KLWall.v:1847" "" "G07_KLWall.v" 1847 (Some 1864) StShift) (
  cons (mkAnchor "P0-TEX" "G07_KLWall.v:1955" "point" "G07_KLWall.v" 1955 (Some 1927) StShift) (
  cons (mkAnchor "P0-TEX" "DTPT_Truth.v:243" "_truth" "DTPT_Truth.v" 243 (Some 243) StHit) (
  cons (mkAnchor "P0-TEX" "DTPT_Truth.v:326" "_liar" "DTPT_Truth.v" 326 (Some 355) StShift) (
  cons (mkAnchor "P0-TEX" "DTPT_Truth.v:355" "" "DTPT_Truth.v" 355 (Some 269) StShift) (
  cons (mkAnchor "P0-TEX" "DTPT_Truth.v:374" "the" "DTPT_Truth.v" 374 (Some 288) StShift) (
  cons (mkAnchor "P0-TEX" "DTPT_Truth.v:409" "tarski" "DTPT_Truth.v" 409 (Some 417) StShift) (
  cons (mkAnchor "P0-TEX" "DTPT_Entropy.v:135" "Permutation" "DTPT_Entropy.v" 135 (Some 136) StShift) (
  cons (mkAnchor "P0-TEX" "DTPT_Entropy.v:481" "H_lam" "DTPT_Entropy.v" 481 (None) StAmbiguous) (
  cons (mkAnchor "P0-TEX" "G10_LoebFam.v:719" "Prf" "G10_LoebFam.v" 719 (Some 719) StHit) (
  cons (mkAnchor "P0-TEX" "G10_LoebFam.v:808" "_lemma" "G10_LoebFam.v" 808 (Some 808) StHit) (
  cons (mkAnchor "P0-TEX" "UpReqIrrationalInstances.v:1310" "assembly" "UpReqIrrationalInstances.v" 1310 (Some 1310) StHit) (
  cons (mkAnchor "P0-TEX" "UpReqSqrt3Irrational.v:1111" "assembly" "UpReqSqrt3Irrational.v" 1111 (Some 1089) StShift) (
  cons (mkAnchor "P0-TEX" "Ln2Escape.v:559" "_cond" "Ln2Escape.v" 559 (Some 559) StHit) (
  cons (mkAnchor "P0-TEX" "Ln2Escape.v:253" "closed" "Ln2Escape.v" 253 (None) StNotFound) (
  cons (mkAnchor "P0-TEX" "Ln2Escape.v:453" "gate" "Ln2Escape.v" 453 (Some 455) StShift) (
  cons (mkAnchor "P0-TEX" "Ln2Escape.v:477" "gate" "Ln2Escape.v" 477 (Some 479) StShift) (
  cons (mkAnchor "P0-TEX" "Ln2Escape.v:507" "the" "Ln2Escape.v" 507 (Some 509) StShift) (
  cons (mkAnchor "P0-TEX" "Ln2Integrality.v:257" "" "Ln2Integrality.v" 257 (Some 221) StShift) (
  cons (mkAnchor "P0-TEX" "Ln2Integrality.v:274" "" "Ln2Integrality.v" 274 (Some 238) StShift) (
  cons (mkAnchor "P0-TEX" "Ln2Integrality.v:426" "the" "Ln2Integrality.v" 426 (Some 390) StShift) (
  cons (mkAnchor "P0-TEX" "BeukersIdentity.v:62" "_factor" "BeukersIdentity.v" 62 (Some 62) StHit) (
  cons (mkAnchor "P0-TEX" "S01_BaseRing.v:79" "" "S01_BaseRing.v" 79 (Some 79) StHit) (
  cons (mkAnchor "P0-TEX" "S06_DiffSamplingGibbs.v:3181" "partition_function" "S06_DiffSamplingGibbs.v" 3181 (Some 3181) StHit) (
  cons (mkAnchor "P0-TEX" "S06_DiffSamplingGibbs.v:3334" "softmax_temp" "S06_DiffSamplingGibbs.v" 3334 (Some 3334) StHit) (
  cons (mkAnchor "P0-TEX" "S06_DiffSamplingGibbs.v:3823" "Z_thermo" "S06_DiffSamplingGibbs.v" 3823 (Some 3823) StHit) (
  cons (mkAnchor "P0-TEX" "S05_AlignmentGRPO.v:353" "dpo_loss" "S05_AlignmentGRPO.v" 353 (Some 353) StHit) (
  cons (mkAnchor "P0-TEX" "S05_AlignmentGRPO.v:821" "ppo_surrogate" "S05_AlignmentGRPO.v" 821 (Some 821) StHit) (
  cons (mkAnchor "P0-TEX" "S05_AlignmentGRPO.v:2420" "energy_t" "S05_AlignmentGRPO.v" 2420 (Some 2420) StHit) (
  cons (mkAnchor "P0-TEX" "UpReqSquareWallEquiv.v:44" "_wall" "UpReqSquareWallEquiv.v" 44 (None) StAmbiguous) (
  cons (mkAnchor "P0-TEX" "AttnDoeblin.v:154" "contraction" "AttnDoeblin.v" 154 (None) StNotFound) (
  cons (mkAnchor "P0-TEX" "AttnDoeblin.v:541" "omd" "AttnDoeblin.v" 541 (None) StNotFound) (
  cons (mkAnchor "P0-TEX" "DTPT.v:3" "self" "DTPT.v" 3 (None) StNotFound) (
  cons (mkAnchor "P0-TEX" "DTPT_Bridge.v:3" "mission" "DTPT_Bridge.v" 3 (Some 3) StHit) (
  cons (mkAnchor "P0-TEX" "S12_B5RecycleSF.v:15" "b5e_pern_main" "S12_B5RecycleSF.v" 15 (None) StNotFound) (
  cons (mkAnchor "P0-TEX" "S12_B5RecycleSF.v:2046" "dec" "S12_B5RecycleSF.v" 2046 (None) StAmbiguous) (
  cons (mkAnchor "P0-TEX" "UpReqIndex.v:494" "_Bridge" "UpReqIndex.v" 494 (None) StNotFound) (
  cons (mkAnchor "论文10-ML训练机制的构造性定理化" "L11267" "sf_ewc_pos_eps" "S07_RealSetoidExpLog.v" 11267 (None) StNotFound) (
  cons (mkAnchor "论文10-ML训练机制的构造性定理化" "L11307" "sf_ewc_mono_fisher" "S07_RealSetoidExpLog.v" 11307 (None) StNotFound) (
  cons (mkAnchor "论文10-ML训练机制的构造性定理化" "L11437" "sf_fisher_nonneg" "S07_RealSetoidExpLog.v" 11437 (None) StNotFound) (
  cons (mkAnchor "论文10-ML训练机制的构造性定理化" "L9955" "sf_ewc_pos_eps" "S07_RealSetoidExpLog.v" 9955 (None) StNotFound) (
  cons (mkAnchor "论文10-ML训练机制的构造性定理化" "L9983" "" "S12_B5RecycleSF.v" 9983 (Some 9984) StShift) (
  cons (mkAnchor "论文10-ML训练机制的构造性定理化" "L9985" "" "S12_B5RecycleSF.v" 9985 (Some 9986) StShift) (
  cons (mkAnchor "论文10-ML训练机制的构造性定理化" "L10015" "" "S12_B5RecycleSF.v" 10015 (Some 10016) StShift) (
  cons (mkAnchor "论文10-ML训练机制的构造性定理化" "S07_RealSetoidExpLog.v:5498" "cw_log" "S07_RealSetoidExpLog.v" 5498 (Some 5498) StHit) (
  cons (mkAnchor "论文10-ML训练机制的构造性定理化" "L9693" "sf_path_cmp" "S07_RealSetoidExpLog.v" 9693 (None) StNotFound) (
  cons (mkAnchor "论文10-ML训练机制的构造性定理化" "L1" "" "S12_B5RecycleSF.v" 1 (Some 2) StShift) (
  cons (mkAnchor "论文10-ML训练机制的构造性定理化" "L9699" "" "S12_B5RecycleSF.v" 9699 (Some 9700) StShift) (
  cons (mkAnchor "论文10-ML训练机制的构造性定理化" "L9760" "" "S12_B5RecycleSF.v" 9760 (Some 9761) StShift) (
  cons (mkAnchor "论文10-ML训练机制的构造性定理化" "L9968" "" "S12_B5RecycleSF.v" 9968 (Some 9969) StShift) (
  cons (mkAnchor "论文10-ML训练机制的构造性定理化" "L10050" "" "S12_B5RecycleSF.v" 10050 (Some 10051) StShift) (
  cons (mkAnchor "论文10-ML训练机制的构造性定理化" "L11276" "" "S12_B5RecycleSF.v" 11276 (Some 11277) StShift) (
  cons (mkAnchor "论文10-ML训练机制的构造性定理化" "L11989" "" "S12_B5RecycleSF.v" 11989 (Some 11990) StShift) (
  cons (mkAnchor "论文10-ML训练机制的构造性定理化" "L2" "" "S07_RealSetoidExpLog.v" 2 (Some 3) StShift) (
  cons (mkAnchor "论文10-ML训练机制的构造性定理化" "L3" "" "S07_RealSetoidExpLog.v" 3 (Some 4) StShift) (
  cons (mkAnchor "论文10-ML训练机制的构造性定理化" "L11" "" "S12_B5RecycleSF.v" 11 (Some 12) StShift) (
  cons (mkAnchor "论文10-ML训练机制的构造性定理化" "L10" "" "S12_B5RecycleSF.v" 10 (Some 11) StShift) (
  cons (mkAnchor "论文10-ML训练机制的构造性定理化" "L9224" "" "S12_B5RecycleSF.v" 9224 (Some 9225) StShift) (
  cons (mkAnchor "论文10-ML训练机制的构造性定理化" "L9341" "" "S12_B5RecycleSF.v" 9341 (Some 9342) StShift) (
  cons (mkAnchor "论文10-ML训练机制的构造性定理化" "L9717" "" "S12_B5RecycleSF.v" 9717 (Some 9718) StShift) (
  cons (mkAnchor "论文10-ML训练机制的构造性定理化" "L9756" "" "S12_B5RecycleSF.v" 9756 (Some 9757) StShift) (
  cons (mkAnchor "论文10-ML训练机制的构造性定理化" "L9769" "" "S12_B5RecycleSF.v" 9769 (Some 9770) StShift) (
  cons (mkAnchor "论文10-ML训练机制的构造性定理化" "L9778" "" "S12_B5RecycleSF.v" 9778 (Some 9779) StShift) (
  cons (mkAnchor "论文10-ML训练机制的构造性定理化" "L9799" "" "S12_B5RecycleSF.v" 9799 (Some 9800) StShift) (
  cons (mkAnchor "论文10-ML训练机制的构造性定理化" "L11295" "" "S12_B5RecycleSF.v" 11295 (Some 11296) StShift) (
  cons (mkAnchor "论文10-ML训练机制的构造性定理化" "L11397" "" "S12_B5RecycleSF.v" 11397 (Some 11398) StShift) (
  cons (mkAnchor "论文10-ML训练机制的构造性定理化" "L11425" "" "S12_B5RecycleSF.v" 11425 (Some 11426) StShift) (
  cons (mkAnchor "论文10-ML训练机制的构造性定理化" "L12005" "" "S12_B5RecycleSF.v" 12005 (Some 12006) StShift) (
  cons (mkAnchor "论文10-ML训练机制的构造性定理化" "L12077" "" "S12_B5RecycleSF.v" 12077 (Some 12078) StShift) (
  cons (mkAnchor "论文10-ML训练机制的构造性定理化" "L12009" "" "S12_B5RecycleSF.v" 12009 (Some 12010) StShift) (
  cons (mkAnchor "论文10-ML训练机制的构造性定理化" "L12100" "" "S12_B5RecycleSF.v" 12100 (Some 12101) StShift) (
  cons (mkAnchor "论文10-ML训练机制的构造性定理化" "L12118" "" "S12_B5RecycleSF.v" 12118 (Some 12119) StShift) (
  cons (mkAnchor "论文10-ML训练机制的构造性定理化" "L12125" "" "S12_B5RecycleSF.v" 12125 (Some 12126) StShift) (
  cons (mkAnchor "论文10-ML训练机制的构造性定理化" "S12:13992" "" "S12_B5RecycleSF.v" 13992 (Some 13993) StShift) (
  cons (mkAnchor "论文11-自由能变分原理的构造性同一性" "order L347" "" "order.txt" 347 (Some 347) StHit) (
  cons (mkAnchor "论文11-自由能变分原理的构造性同一性" "L176" "gfe_gibbs_core_temp_eps" "GibbsFamilyExt.v" 176 (Some 159) StShift) (
  cons (mkAnchor "论文11-自由能变分原理的构造性同一性" "L202" "gfe_gibbs_inequality_temp_eps" "GibbsFamilyExt.v" 202 (Some 217) StShift) (
  cons (mkAnchor "论文11-自由能变分原理的构造性同一性" "L234" "gfe_gibbs_inequality_temp_eps" "GibbsFamilyExt.v" 234 (Some 217) StShift) (
  cons (mkAnchor "论文11-自由能变分原理的构造性同一性" "L277" "gfe_gibbs_inequality_temp_eps" "GibbsFamilyExt.v" 277 (Some 276) StShift) (
  cons (mkAnchor "论文11-自由能变分原理的构造性同一性" "L302" "gfe_le_b_mult_pos" "GibbsFamilyExt.v" 302 (Some 284) StShift) (
  cons (mkAnchor "论文11-自由能变分原理的构造性同一性" "L320" "gfe_le_b_mult_pos" "GibbsFamilyExt.v" 320 (Some 284) StShift) (
  cons (mkAnchor "论文11-自由能变分原理的构造性同一性" "L365" "gfe_le_b_mult_pos" "GibbsFamilyExt.v" 365 (None) StAmbiguous) (
  cons (mkAnchor "论文11-自由能变分原理的构造性同一性" "L394" "gfe_gibbs_inequality_temp_eps" "GibbsFamilyExt.v" 394 (Some 411) StShift) (
  cons (mkAnchor "论文11-自由能变分原理的构造性同一性" "L248" "cf2_tv_pos" "UpReqConcFin2.v" 248 (Some 241) StShift) (
  cons (mkAnchor "论文11-自由能变分原理的构造性同一性" "L277" "cf2_tv_pos" "UpReqConcFin2.v" 277 (Some 241) StShift) (
  cons (mkAnchor "论文11-自由能变分原理的构造性同一性" "L57" "fic2_attention_is_gibbs_temp_id_consume" "FepIdConsume.v" 57 (Some 33) StShift) (
  cons (mkAnchor "论文11-自由能变分原理的构造性同一性" "L90" "fic2_identified_boltzmann_dual" "FepIdConsume.v" 90 (Some 66) StShift) (
  cons (mkAnchor "论文11-自由能变分原理的构造性同一性" "L162" "fic2_fep_align_face_consume" "FepIdConsume.v" 162 (Some 145) StShift) (
  cons (mkAnchor "论文11-自由能变分原理的构造性同一性" "L189" "fic2_rlhf_gap_identified_consume" "GibbsFamilyExt.v" 189 (Some 189) StHit) (
  cons (mkAnchor "论文11-自由能变分原理的构造性同一性" "L223" "fic2_real_instance_gibbs_consume" "GibbsFamilyExt.v" 223 (Some 223) StHit) (
  cons (mkAnchor "论文11-自由能变分原理的构造性同一性" "L235" "slc_gain_kl_two_sided_eps" "SecondLawConsume.v" 235 (Some 193) StShift) (
  cons (mkAnchor "论文11-自由能变分原理的构造性同一性" "L261" "slc_kl_boltz_self_zero" "SecondLawConsume.v" 261 (Some 237) StShift) (
  cons (mkAnchor "论文11-自由能变分原理的构造性同一性" "L297" "slc_second_law_kl_floor_eps_list" "SecondLawConsume.v" 297 (Some 290) StShift) (
  cons (mkAnchor "论文11-自由能变分原理的构造性同一性" "L350" "slc_kl_boltz_self_zero" "SecondLawConsume.v" 350 (Some 374) StShift) (
  cons (mkAnchor "论文11-自由能变分原理的构造性同一性" "L321" "g05w_wall_class_lpo" "UpReqG05WallClass.v" 321 (Some 350) StShift) (
  cons (mkAnchor "论文11-自由能变分原理的构造性同一性" "L540" "lgz_log_z_wall_lpo" "UpReqLogZWallEquiv.v" 540 (Some 512) StShift) (
  cons (mkAnchor "论文11-自由能变分原理的构造性同一性" "L695" "lgz_lpo_zle" "UpReqLogZWallEquiv.v" 695 (Some 667) StShift) (
  cons (mkAnchor "论文11-自由能变分原理的构造性同一性" "L419" "rwl_resid_walls_lpo" "UpReqResidWallEquiv.v" 419 (Some 437) StShift) (
  cons (mkAnchor "论文11-自由能变分原理的构造性同一性" "L2106" "real_transition" "S08_RealMainlineDPO.v" 2106 (Some 2107) StShift) (
  cons (mkAnchor "论文11-自由能变分原理的构造性同一性" "L2114" "real_transition_normalization" "S08_RealMainlineDPO.v" 2114 (Some 2115) StShift) (
  cons (mkAnchor "论文11-自由能变分原理的构造性同一性" "L37" "real_transition" "S10_KVQuantTrig.v" 37 (None) StAmbiguous) (
  cons (mkAnchor "论文11-自由能变分原理的构造性同一性" "L109" "real_steady_state_boltzmann" "UpReqSteadyThermo.v" 109 (Some 82) StShift) (
  cons (mkAnchor "论文11-自由能变分原理的构造性同一性" "L309" "vb_vajda_sat_log2" "UpReqVajdaBound.v" 309 (None) StNotFound) (
  cons (mkAnchor "论文11-自由能变分原理的构造性同一性" "L438" "snw_wall" "UpReqLpoEquiv.v" 438 (Some 438) StHit) (
  cons (mkAnchor "论文11-自由能变分原理的构造性同一性" "L70" "snw_b_lift" "UpReqSquareWallEquiv.v" 70 (None) StAmbiguous) (
  cons (mkAnchor "论文11-自由能变分原理的构造性同一性" "L319" "a1622d1" "SecondLawConsume.v" 319 (Some 319) StHit) (
  cons (mkAnchor "论文11-自由能变分原理的构造性同一性" "L322" "a1622d1" "SecondLawConsume.v" 322 (Some 322) StHit) (
  cons (mkAnchor "论文11-自由能变分原理的构造性同一性" "L328" "a1622d1" "SecondLawConsume.v" 328 (Some 328) StHit) (
  cons (mkAnchor "论文11-自由能变分原理的构造性同一性" "L320" "cf2_tv_pos" "UpReqConcFin2.v" 320 (None) StAmbiguous) (
  cons (mkAnchor "论文11-自由能变分原理的构造性同一性" "order L547" "cf2_tv_pos" "order.txt" 547 (Some 547) StHit) (
  cons (mkAnchor "论文11-自由能变分原理的构造性同一性" "L319" "" "UpAblP6_GibbsFamilyExt.v" 319 (None) StNotFound) (
  cons (mkAnchor "论文11-自由能变分原理的构造性同一性" "L322" "" "UpAblP6_GibbsFamilyExt.v" 322 (None) StNotFound) (
  cons (mkAnchor "论文11-自由能变分原理的构造性同一性" "L328" "" "UpAblP6_GibbsFamilyExt.v" 328 (None) StNotFound) (
  cons (mkAnchor "论文11-自由能变分原理的构造性同一性" "L2106" "real_transition" "S10_KVQuantTrig.v" 2106 (None) StAmbiguous) (
  cons (mkAnchor "论文11-自由能变分原理的构造性同一性" "L37" "a1622d1" "SecondLawQuantified.v" 37 (Some 37) StHit) (
  cons (mkAnchor "论文11-自由能变分原理的构造性同一性" "L411" "" "EntropyMonoSplitInst.v" 411 (None) StNotFound) (
  cons (mkAnchor "论文11-自由能变分原理的构造性同一性" "L237" "" "EntropyMonoSplitInst.v" 237 (Some 216) StShift) (
  cons (mkAnchor "论文11-自由能变分原理的构造性同一性" "L715" "" "EntropyMonoSplitInst.v" 715 (None) StNotFound) (
  cons (mkAnchor "论文12-注意力核马尔可夫理论" "UpReqFEPAttn.v:137" "req_fep_partition_condition" "UpReqFEPAttn.v" 137 (Some 149) StShift) (
  cons (mkAnchor "论文12-注意力核马尔可夫理论" "UpReqFEPAttn.v:381" "req_fep_partition_condition_logz" "UpReqFEPAttn.v" 381 (Some 451) StShift) (
  cons (mkAnchor "论文12-注意力核马尔可夫理论" "AttnHardLimit218.v:1031" "hard_attention_limit" "AttnHardLimit218.v" 1031 (Some 1031) StHit) (
  cons (mkAnchor "论文12-注意力核马尔可夫理论" "UpTempWindow.v:1592" "gap_le" "UpTempWindow.v" 1592 (Some 1592) StHit) (
  cons (mkAnchor "论文12-注意力核马尔可夫理论" "AttnDoeblin.v:701" "bs_minorization" "AttnDoeblin.v" 701 (Some 693) StShift) (
  cons (mkAnchor "论文12-注意力核马尔可夫理论" "AttnDoeblin.v:332" "u_tv_contraction" "AttnDoeblin.v" 332 (Some 332) StHit) (
  cons (mkAnchor "论文12-注意力核马尔可夫理论" "L659" "evict_db_breaking" "G13_EvictFam.v" 659 (None) StNotFound) (
  cons (mkAnchor "论文12-注意力核马尔可夫理论" "S01_BaseRing.v:1304" "abs_sum_le" "S01_BaseRing.v" 1304 (Some 1304) StHit) (
  cons (mkAnchor "论文12-注意力核马尔可夫理论" "G13_EvictFam.v:230" "evicted_boltzmann_steady_exact" "G13_EvictFam.v" 230 (Some 204) StShift) (
  cons (mkAnchor "论文12-注意力核马尔可夫理论" "G13_EvictFam.v:184" "eviction_db_breaking_zero" "G13_EvictFam.v" 184 (Some 184) StHit) (
  cons (mkAnchor "论文12-注意力核马尔可夫理论" "UpKVDrift.v:2196" "kev_iter" "UpKVDrift.v" 2196 (None) StAmbiguous) (
  cons (mkAnchor "论文12-注意力核马尔可夫理论" "UpReqAttnMixTime.v:136–157" "amt_attention_mixing_time" "UpReqAttnMixTime.v" 136 (Some 150) StShift) (
  cons (mkAnchor "论文12-注意力核马尔可夫理论" "UpAblMetaWindow.v:174–188" "mtw_window_two_sided" "UpAblMetaWindow.v" 174 (Some 172) StShift) (
  cons (mkAnchor "论文12-注意力核马尔可夫理论" "UpAblMetaTemp.v:308–314" "mtp_anchor_divergence" "UpAblMetaTemp.v" 308 (Some 296) StShift) (
  cons (mkAnchor "论文13-构造性ML对齐统一形式化" "S05:5362" "square_nonneg" "S05_AlignmentGRPO.v" 5362 (Some 5363) StShift) (
  cons (mkAnchor "论文13-构造性ML对齐统一形式化" "S05:5591" "square_nonneg" "S05_AlignmentGRPO.v" 5591 (None) StAmbiguous) (
  cons (mkAnchor "论文13-构造性ML对齐统一形式化" "UpReqDist.v:2323–2325" "reqd_positive_dist" "UpReqDist.v" 2323 (Some 2335) StShift) (
  cons (mkAnchor "论文13-构造性ML对齐统一形式化" "UpReqTempEntropy.v` 现行 1" "reqd_boltzmann_dist" "UpReqTempEntropy.v" 1 (None) StNotFound) (
  cons (mkAnchor "论文13-构造性ML对齐统一形式化" "UpStepKL.v:697" "real_step_kl_eta_bound_eps" "UpStepKL.v" 697 (Some 711) StShift) (
  cons (mkAnchor "论文13-构造性ML对齐统一形式化" "S15_TailFEPUp.v:1031" "real_step_kl_eta_bound_eps" "S15_TailFEPUp.v" 1031 (Some 1030) StShift) (
  cons (mkAnchor "论文13-构造性ML对齐统一形式化" "S15_TailFEPUp.v:1041" "real_step_kl_eta_bound_eps" "S15_TailFEPUp.v" 1041 (Some 1030) StShift) (
  cons (mkAnchor "论文13-构造性ML对齐统一形式化" "L353" "proj_normalized" "G04_ProjFam.v" 353 (Some 301) StShift) (
  cons (mkAnchor "论文13-构造性ML对齐统一形式化" "L339" "proj_keep_ge" "G04_ProjFam.v" 339 (Some 287) StShift) (
  cons (mkAnchor "论文13-构造性ML对齐统一形式化" "L389" "proj_minor_uncond" "G04_ProjFam.v" 389 (Some 337) StShift) (
  cons (mkAnchor "论文13-构造性ML对齐统一形式化" "L668" "proj_kl_cost" "G04_ProjFam.v" 668 (Some 616) StShift) (
  cons (mkAnchor "论文13-构造性ML对齐统一形式化" "L210" "eviction_db_breaking_zero" "G13_EvictFam.v" 210 (Some 184) StShift) (
  cons (mkAnchor "论文13-构造性ML对齐统一形式化" "L230" "evicted_boltzmann_steady_exact" "G13_EvictFam.v" 230 (Some 204) StShift) (
  cons (mkAnchor "论文13-构造性ML对齐统一形式化" "L347" "eviction_partition_increment" "G13_EvictFam.v" 347 (Some 321) StShift) (
  cons (mkAnchor "论文13-构造性ML对齐统一形式化" "AttnDoeblin.v:779" "real_expf_realizable" "AttnDoeblin.v" 779 (Some 771) StShift) (
  cons (mkAnchor "论文13-构造性ML对齐统一形式化" "S13_NLiveAudit.v:3102" "real_expf_realizable" "S13_NLiveAudit.v" 3102 (Some 3096) StShift) (
  cons (mkAnchor "论文13-构造性ML对齐统一形式化" "S05:62" "square_nonneg" "S05_AlignmentGRPO.v" 62 (Some 5363) StShift) (
  cons (mkAnchor "论文13-构造性ML对齐统一形式化" "S05:54" "square_nonneg" "S05_AlignmentGRPO.v" 54 (Some 5363) StShift) (
  cons (mkAnchor "论文13-构造性ML对齐统一形式化" "S15:1436" "grp_eq_dec" "S15_TailFEPUp.v" 1436 (Some 1435) StShift) (
  cons (mkAnchor "论文13-构造性ML对齐统一形式化" "L474" "" "pinsker.v" 474 (None) StNotFound) (
  cons (mkAnchor "论文13-构造性ML对齐统一形式化" "L526" "" "pinsker.v" 526 (None) StNotFound) (
  cons (mkAnchor "论文13-构造性ML对齐统一形式化" "L1" "" "CW220_Extensions.v" 1 (Some 1) StHit) (
  cons (mkAnchor "论文13-构造性ML对齐统一形式化" "L114" "" "CW220_Extensions.v" 114 (Some 96) StShift) (
  cons (mkAnchor "论文14-PPO裁剪的静态结构与GRPO组统计量" "S08_RealMainlineDPO.v:3641" "real_square_nonneg_eps" "S08_RealMainlineDPO.v" 3641 (Some 3642) StShift) (
  cons (mkAnchor "论文14-PPO裁剪的静态结构与GRPO组统计量" "UpGRPO.v:433" "real_sigma_witness" "UpGRPO.v" 433 (Some 428) StShift) (
  cons (mkAnchor "论文14-PPO裁剪的静态结构与GRPO组统计量" "UpGRPO.v:422" "real_sigma_witness" "UpGRPO.v" 422 (Some 428) StShift) (
  cons (mkAnchor "论文15-截断采样三部曲" "G13_EvictFam.v:230" "evicted_boltzmann_steady_exact" "G13_EvictFam.v" 230 (Some 204) StShift) (
  cons (mkAnchor "论文15-截断采样三部曲" "S03_QExp.v:6442" "cauchy_real_exp_pos" "S03_QExp.v" 6442 (Some 6442) StHit) (
  cons (mkAnchor "论文15-截断采样三部曲" "S15_TailFEPUp.v:1410" "grp_eq_dec" "S15_TailFEPUp.v" 1410 (Some 1435) StShift) (
  cons (mkAnchor "论文15-截断采样三部曲" "UpAblGrpEqDecWorld.v:67" "gqc_grp_eq_dec" "UpAblGrpEqDecWorld.v" 67 (Some 56) StShift) (
  cons (mkAnchor "论文15-截断采样三部曲" "S06_DiffSamplingGibbs.v:5951" "token_eq_dec" "S06_DiffSamplingGibbs.v" 5951 (Some 5881) StShift) (
  cons (mkAnchor "论文16-构造性柯西实数的超越函数-指数正性与Banach推广" "S07_RealSetoidExpLog.v:2259" "cauchy_real_exp_plus" "S07_RealSetoidExpLog.v" 2259 (Some 2260) StShift) (
  cons (mkAnchor "论文16-构造性柯西实数的超越函数-指数正性与Banach推广" "UpReqBanachExp.v:470" "exp_add" "UpReqBanachExp.v" 470 (Some 470) StHit) (
  cons (mkAnchor "论文16-构造性柯西实数的超越函数-指数正性与Banach推广" "S03_QExp.v:6443" "cauchy_real_exp_pos" "S03_QExp.v" 6443 (Some 6442) StShift) (
  cons (mkAnchor "论文16-构造性柯西实数的超越函数-指数正性与Banach推广" "L870" "" "UpReqEntropyMonoSplit.v" 870 (None) StNotFound) (
  cons (mkAnchor "论文17-资源受限收敛动力学的显式迭代预算收敛定理-PCT必要条件侧参照" "SqrtfCauchyArch.v:457" "sfcy_arch_decay_slot" "SqrtfCauchyArch.v" 457 (Some 419) StShift) (
  cons (mkAnchor "论文17-资源受限收敛动力学的显式迭代预算收敛定理-PCT必要条件侧参照" "QstepConvergenceBound.v:391" "qstep_iter_geometric_bound" "QstepConvergenceBound.v" 391 (Some 391) StHit) (
  cons (mkAnchor "论文17-资源受限收敛动力学的显式迭代预算收敛定理-PCT必要条件侧参照" "order L546" "qstep_iter_geometric_bound" "order.txt" 546 (Some 546) StHit) (
  cons (mkAnchor "论文17-资源受限收敛动力学的显式迭代预算收敛定理-PCT必要条件侧参照" "order L553" "qstep_iter_geometric_bound" "order.txt" 553 (Some 553) StHit) (
  cons (mkAnchor "论文17-资源受限收敛动力学的显式迭代预算收敛定理-PCT必要条件侧参照" "L546" "qstep_iter_geometric_bound" "QstepConvergenceBound.v" 546 (Some 653) StShift) (
  cons (mkAnchor "论文17-资源受限收敛动力学的显式迭代预算收敛定理-PCT必要条件侧参照" "L553" "qstep_iter_geometric_bound" "QstepConvergenceBound.v" 553 (Some 653) StShift) (
  cons (mkAnchor "论文17-资源受限收敛动力学的显式迭代预算收敛定理-PCT必要条件侧参照" "L539" "qstep_iter_geometric_bound" "QstepConvergenceBound.v" 539 (Some 653) StShift) (
  cons (mkAnchor "论文17-资源受限收敛动力学的显式迭代预算收敛定理-PCT必要条件侧参照" "S07_RealSetoidExpLog.v:5748" "real_weak_trich" "S07_RealSetoidExpLog.v" 5748 (Some 5749) StShift) (
  cons (mkAnchor "论文17-资源受限收敛动力学的显式迭代预算收敛定理-PCT必要条件侧参照" "S02_CauchyComplete.v:3083" "real_cauchy_complete" "S02_CauchyComplete.v" 3083 (Some 3084) StShift) (
  cons (mkAnchor "论文17-资源受限收敛动力学的显式迭代预算收敛定理-PCT必要条件侧参照" "S07_RealSetoidExpLog.v:878" "real_cauchy_complete_metric_natle" "S07_RealSetoidExpLog.v" 878 (Some 879) StShift) (
  cons (mkAnchor "论文17-资源受限收敛动力学的显式迭代预算收敛定理-PCT必要条件侧参照" "L0" "is_attractor" "UpReqPCT.v" 0 (None) StNotFound) (
  cons (mkAnchor "论文17-资源受限收敛动力学的显式迭代预算收敛定理-PCT必要条件侧参照" "L524" "" "S04_RealExpLogConv.v" 524 (Some 522) StShift) (
  cons (mkAnchor "论文18-构造性可达常数" "order L246" "" "order.txt" 246 (Some 246) StHit) (
  cons (mkAnchor "论文18-构造性可达常数" "L245" "p2_kl2" "PinskerTwoPoint.v" 245 (None) StAmbiguous) (
  cons (mkAnchor "论文18-构造性可达常数" "L61" "p2_tvsq" "PinskerTwoPoint.v" 61 (Some 75) StShift) (
  cons (mkAnchor "论文18-构造性可达常数" "L65" "p2_one_minus" "UpReqPinskerCore.v" 65 (Some 324) StShift) (
  cons (mkAnchor "论文18-构造性可达常数" "L69" "p2_one_minus" "UpReqPinskerCore.v" 69 (Some 324) StShift) (
  cons (mkAnchor "论文18-构造性可达常数" "L50" "p2_one_minus" "UpReqPinskerCore.v" 50 (Some 324) StShift) (
  cons (mkAnchor "论文18-构造性可达常数" "L54" "p2_one_minus" "UpReqPinskerCore.v" 54 (Some 324) StShift) (
  cons (mkAnchor "论文18-构造性可达常数" "L58" "p2_one_minus" "UpReqPinskerCore.v" 58 (Some 324) StShift) (
  cons (mkAnchor "论文18-构造性可达常数" "L1727" "pnk_pinsker_frac2" "UpReqPinskerCore.v" 1727 (Some 1722) StShift) (
  cons (mkAnchor "论文18-构造性可达常数" "L1741" "pnk_pinsker_frac2" "UpReqPinskerCore.v" 1741 (Some 1722) StShift) (
  cons (mkAnchor "论文18-构造性可达常数" "L1296" "pnk_kl2_ge_fracsum" "UpReqPinskerCore.v" 1296 (Some 1291) StShift) (
  cons (mkAnchor "论文18-构造性可达常数" "L1310" "pnk_kl2_ge_fracsum" "UpReqPinskerCore.v" 1310 (Some 1291) StShift) (
  cons (mkAnchor "论文18-构造性可达常数" "L2631" "pnk2_sprod_le_one" "UpReqPinskerCore.v" 2631 (Some 2626) StShift) (
  cons (mkAnchor "论文18-构造性可达常数" "L2580" "pnk2_sprod_le_one" "UpReqPinskerCore.v" 2580 (Some 2626) StShift) (
  cons (mkAnchor "论文18-构造性可达常数" "L2680" "pnk2_pinsker_one" "UpReqPinskerCore.v" 2680 (Some 2675) StShift) (
  cons (mkAnchor "论文18-构造性可达常数" "L2629" "pnk2_pinsker_one" "UpReqPinskerCore.v" 2629 (Some 2675) StShift) (
  cons (mkAnchor "论文18-构造性可达常数" "L2515" "pnk2_sprod_le_one" "UpReqPinskerCore.v" 2515 (Some 2510) StShift) (
  cons (mkAnchor "论文18-构造性可达常数" "L2464" "pnk2_sprod_le_one" "UpReqPinskerCore.v" 2464 (Some 2626) StShift) (
  cons (mkAnchor "论文18-构造性可达常数" "L2498" "" "UpReqPinskerCore.v" 2498 (Some 2493) StShift) (
  cons (mkAnchor "论文18-构造性可达常数" "L2447" "" "UpReqPinskerCore.v" 2447 (Some 2442) StShift) (
  cons (mkAnchor "论文18-构造性可达常数" "L2499" "" "UpReqPinskerCore.v" 2499 (Some 2494) StShift) (
  cons (mkAnchor "论文18-构造性可达常数" "L3065" "pnk2_sprod_le_one" "UpReqPinskerCore.v" 3065 (Some 3060) StShift) (
  cons (mkAnchor "论文18-构造性可达常数" "L3066" "pnk2_pinsker_one" "UpReqPinskerCore.v" 3066 (Some 3061) StShift) (
  cons (mkAnchor "论文18-构造性可达常数" "L2265" "pnk_pinsker_frac2" "UpReqPinskerCore.v" 2265 (Some 2260) StShift) (
  cons (mkAnchor "论文18-构造性可达常数" "L3014" "pnk2_sprod_le_one" "UpReqPinskerCore.v" 3014 (Some 2992) StShift) (
  cons (mkAnchor "论文18-构造性可达常数" "L3015" "pnk2_sprod_le_one" "UpReqPinskerCore.v" 3015 (Some 2992) StShift) (
  cons (mkAnchor "论文18-构造性可达常数" "L2279" "pnk_pinsker_frac2" "UpReqPinskerCore.v" 2279 (Some 2260) StShift) (
  cons (mkAnchor "论文18-构造性可达常数" "UpReqPinskerTransport.v:1024" "pnt_dp_two_point" "UpReqPinskerTransport.v" 1024 (Some 1039) StShift) (
  cons (mkAnchor "论文18-构造性可达常数" "order L278" "pnt_dp_two_point" "order.txt" 278 (Some 278) StHit) (
  cons (mkAnchor "论文18-构造性可达常数" "L277" "real_le_b" "UpReqPinskerTransport.v" 277 (None) StAmbiguous) (
  cons (mkAnchor "论文18-构造性可达常数" "L1024" "pnt_dp_two_point" "UpReqPinskerTransport.v" 1024 (Some 1039) StShift) (
  cons (mkAnchor "论文18-构造性可达常数" "order L310" "pnt_dp_two_point" "order.txt" 310 (Some 310) StHit) (
  cons (mkAnchor "论文18-构造性可达常数" "L757" "pnt_mult_one_l" "UpReqVajdaBound.v" 757 (Some 763) StShift) (
  cons (mkAnchor "论文18-构造性可达常数" "L744" "pnk2_pinsker_one" "UpReqVajdaBound.v" 744 (Some 764) StShift) (
  cons (mkAnchor "论文18-构造性可达常数" "L309" "pnk2_pinsker_one" "UpReqVajdaBound.v" 309 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "SecondLawQuantified.v:281" "slq_entropy_gain_kl_lower" "SecondLawQuantified.v" 281 (Some 188) StShift) (
  cons (mkAnchor "论文18-构造性可达常数" "SecondLawQuantified.v:536" "slq_second_law_eps_list" "SecondLawQuantified.v" 536 (Some 443) StShift) (
  cons (mkAnchor "论文18-构造性可达常数" "L243" "slq_entropy_gain_kl_lower" "SecondLawQuantified.v" 243 (Some 292) StShift) (
  cons (mkAnchor "论文18-构造性可达常数" "L498" "slq_second_law_eps_list" "SecondLawQuantified.v" 498 (Some 443) StShift) (
  cons (mkAnchor "论文18-构造性可达常数" "L201" "req_fep_partition_condition" "UpReqFEPAttn.v" 201 (None) StAmbiguous) (
  cons (mkAnchor "论文18-构造性可达常数" "L243" "req_fep_partition_condition" "UpReqFEPAttn.v" 243 (None) StAmbiguous) (
  cons (mkAnchor "论文18-构造性可达常数" "L427" "req_fep_partition_condition" "UpReqFEPAttn.v" 427 (Some 149) StShift) (
  cons (mkAnchor "论文18-构造性可达常数" "L498" "req_fep_partition_condition" "UpReqFEPAttn.v" 498 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L137" "req_fep_partition_condition" "UpReqFEPAttn.v" 137 (Some 149) StShift) (
  cons (mkAnchor "论文18-构造性可达常数" "L72" "req_fep_partition_condition" "UpReqFEPAttn.v" 72 (Some 149) StShift) (
  cons (mkAnchor "论文18-构造性可达常数" "L281" "req_fep_partition_condition" "UpReqFEPAttn.v" 281 (None) StAmbiguous) (
  cons (mkAnchor "论文18-构造性可达常数" "L536" "req_fep_partition_condition" "UpReqFEPAttn.v" 536 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L37" "req_fep_partition_condition" "EpsOptimalReach.v" 37 (Some 37) StHit) (
  cons (mkAnchor "论文18-构造性可达常数" "L243" "req_fep_partition_condition" "EpsOptimalReach.v" 243 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L498" "req_fep_partition_condition" "EpsOptimalReach.v" 498 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L137" "req_fep_partition_condition" "EpsOptimalReach.v" 137 (Some 137) StHit) (
  cons (mkAnchor "论文18-构造性可达常数" "L235" "req_fep_partition_condition" "EpsOptimalReach.v" 235 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L236" "req_fep_partition_condition" "EpsOptimalReach.v" 236 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L72" "req_fep_partition_condition" "EpsOptimalReach.v" 72 (Some 72) StHit) (
  cons (mkAnchor "论文18-构造性可达常数" "order L283" "" "order.txt" 283 (Some 283) StHit) (
  cons (mkAnchor "论文18-构造性可达常数" "L706" "vb_ln2_upper_env" "UpReqVajdaBound.v" 706 (Some 702) StShift) (
  cons (mkAnchor "论文18-构造性可达常数" "L669" "vb_l2sum9_cap" "UpReqVajdaBound.v" 669 (Some 665) StShift) (
  cons (mkAnchor "论文18-构造性可达常数" "L693" "vb_ln2_upper_env" "UpReqVajdaBound.v" 693 (Some 702) StShift) (
  cons (mkAnchor "论文18-构造性可达常数" "L656" "vb_l2sum9_cap" "UpReqVajdaBound.v" 656 (Some 665) StShift) (
  cons (mkAnchor "论文18-构造性可达常数" "L833" "vb_vajda_sat_log2" "UpReqVajdaBound.v" 833 (Some 829) StShift) (
  cons (mkAnchor "论文18-构造性可达常数" "L820" "vb_vajda_sat_log2" "UpReqVajdaBound.v" 820 (Some 829) StShift) (
  cons (mkAnchor "论文18-构造性可达常数" "L188" "vb_l2sum9_cap" "UpReqConstEnvelope.v" 188 (Some 188) StHit) (
  cons (mkAnchor "论文18-构造性可达常数" "L2502" "pnk_pinsker_trunc5" "UpReqTailResidual.v" 2502 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L2453" "pnk_pinsker_trunc5" "UpReqTailResidual.v" 2453 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L2512" "cec_trunc_sup" "UpReqTailResidual.v" 2512 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L2461" "pnk_pinsker_trunc5" "UpReqTailResidual.v" 2461 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L3414" "pnk2_pinsker_trunc5" "UpReqTailResidual.v" 3414 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L3610" "pnk2_pinsker_trunc5_mirror" "UpReqTailResidual.v" 3610 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L3656" "pnk2_pinsker_trunc5_mirror" "UpReqTailResidual.v" 3656 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L853" "w2t_exp_s_le" "UpReqTailResidual.v" 853 (Some 907) StShift) (
  cons (mkAnchor "论文18-构造性可达常数" "L906" "w2t_exp_s_le" "UpReqTailResidual.v" 906 (Some 907) StShift) (
  cons (mkAnchor "论文18-构造性可达常数" "L1121" "w2t_lt_gap_strict" "UpReqTailResidual.v" 1121 (Some 1122) StShift) (
  cons (mkAnchor "论文18-构造性可达常数" "L1274" "w2t_log_lower_quad" "UpReqTailResidual.v" 1274 (Some 1275) StShift) (
  cons (mkAnchor "论文18-构造性可达常数" "L1319" "w2t_log_upper_lin" "UpReqTailResidual.v" 1319 (Some 1320) StShift) (
  cons (mkAnchor "论文18-构造性可达常数" "L1327" "w2t_log_bound" "UpReqTailResidual.v" 1327 (Some 1328) StShift) (
  cons (mkAnchor "论文18-构造性可达常数" "L1336" "w2t_trunc5_bridge" "UpReqTailResidual.v" 1336 (Some 1337) StShift) (
  cons (mkAnchor "论文18-构造性可达常数" "L24" "w2t_log_upper_lin" "UpReqTailResidual.v" 24 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L22" "w2t_log_upper_lin" "UpReqTailResidual.v" 22 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L992" "w2t_trunc5_bridge" "UpReqTailResidual.v" 992 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "order L236" "w2t_trunc5_bridge" "order.txt" 236 (Some 236) StHit) (
  cons (mkAnchor "论文18-构造性可达常数" "L275" "cec_trunc_sup" "UpReqEngineCeiling.v" 275 (Some 230) StShift) (
  cons (mkAnchor "论文18-构造性可达常数" "L1024" "lpn_equivalence" "UpReqLpoEquiv.v" 1024 (Some 444) StShift) (
  cons (mkAnchor "论文18-构造性可达常数" "L438" "lpn_equivalence" "UpReqLpoEquiv.v" 438 (Some 444) StShift) (
  cons (mkAnchor "论文18-构造性可达常数" "L255" "lpn_equivalence" "UpReqLpoEquiv.v" 255 (Some 444) StShift) (
  cons (mkAnchor "论文18-构造性可达常数" "L275" "lpn_equivalence" "UpReqLpoEquiv.v" 275 (Some 444) StShift) (
  cons (mkAnchor "论文18-构造性可达常数" "L234" "slq_entropy_gain_kl_lower" "EpsOptimalReach.v" 234 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L277" "slq_entropy_gain_kl_lower" "EpsOptimalReach.v" 277 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L276" "slq_entropy_gain_kl_lower" "EpsOptimalReach.v" 276 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L186" "slq_entropy_gain_kl_lower" "EpsOptimalReach.v" 186 (Some 186) StHit) (
  cons (mkAnchor "论文18-构造性可达常数" "L289" "slq_entropy_gain_kl_lower" "EpsOptimalReach.v" 289 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L308" "slq_entropy_gain_kl_lower" "EpsOptimalReach.v" 308 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L309" "slq_entropy_gain_kl_lower" "EpsOptimalReach.v" 309 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L310" "slq_entropy_gain_kl_lower" "EpsOptimalReach.v" 310 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L201" "slq_second_law_eps_list" "EpsOptimalReach.v" 201 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L427" "cec_trunc_sup" "EpsOptimalReach.v" 427 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L255" "cec_trunc_sup" "EpsOptimalReach.v" 255 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L275" "cec_trunc_sup" "EpsOptimalReach.v" 275 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L1024" "lpn_equivalence" "EpsOptimalReach.v" 1024 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L438" "req_fep_partition_condition" "EpsOptimalReach.v" 438 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L2453" "req_fep_partition_condition" "EpsOptimalReach.v" 2453 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L2461" "req_fep_partition_condition" "EpsOptimalReach.v" 2461 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L187" "req_fep_partition_condition" "EpsOptimalReach.v" 187 (Some 187) StHit) (
  cons (mkAnchor "论文18-构造性可达常数" "L245" "req_fep_partition_condition" "EpsOptimalReach.v" 245 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L246" "req_fep_partition_condition" "EpsOptimalReach.v" 246 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L278" "cec_trunc_sup" "EpsOptimalReach.v" 278 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L282" "cec_trunc_sup" "EpsOptimalReach.v" 282 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L283" "cec_trunc_sup" "EpsOptimalReach.v" 283 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L291" "cec_trunc_sup" "EpsOptimalReach.v" 291 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L290" "cec_trunc_sup" "EpsOptimalReach.v" 290 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L311" "cec_trunc_sup" "EpsOptimalReach.v" 311 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L448" "pnk_pinsker_frac2" "EpsOptimalReach.v" 448 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L1741" "pnk_kl2_ge_fracsum" "EpsOptimalReach.v" 1741 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L1727" "pnk_kl2_ge_fracsum" "EpsOptimalReach.v" 1727 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L1310" "pnk_pinsker_frac2" "EpsOptimalReach.v" 1310 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L1296" "pnk_pinsker_frac2" "EpsOptimalReach.v" 1296 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L2279" "pnk_pinsker_frac2" "EpsOptimalReach.v" 2279 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L2265" "pnk2_sprod_le_one" "EpsOptimalReach.v" 2265 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L2580" "pnk2_pinsker_one" "EpsOptimalReach.v" 2580 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L2631" "pnk2_pinsker_one" "EpsOptimalReach.v" 2631 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L2629" "pnk2_pinsker_one" "EpsOptimalReach.v" 2629 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L2680" "pnk2_pinsker_one" "EpsOptimalReach.v" 2680 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L3014" "pnk2_pinsker_one" "EpsOptimalReach.v" 3014 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L3015" "pnk2_pinsker_one" "EpsOptimalReach.v" 3015 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L3065" "pnk2_pinsker_one" "EpsOptimalReach.v" 3065 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L3066" "pnk_pinsker_trunc5" "EpsOptimalReach.v" 3066 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L2502" "pnk_pinsker_trunc5" "EpsOptimalReach.v" 2502 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L2512" "pnk_pinsker_trunc5" "EpsOptimalReach.v" 2512 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L2447" "pnk_pinsker_trunc5" "EpsOptimalReach.v" 2447 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L2498" "pnk_pinsker_trunc5" "EpsOptimalReach.v" 2498 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L2464" "slq_entropy_gain_kl_lower" "EpsOptimalReach.v" 2464 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L2515" "slq_entropy_gain_kl_lower" "EpsOptimalReach.v" 2515 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L24" "slq_entropy_gain_kl_lower" "EpsOptimalReach.v" 24 (Some 24) StHit) (
  cons (mkAnchor "论文18-构造性可达常数" "L992" "slq_entropy_gain_kl_lower" "EpsOptimalReach.v" 992 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L281" "slq_second_law_eps_list" "EpsOptimalReach.v" 281 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L536" "slq_second_law_eps_list" "EpsOptimalReach.v" 536 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L182" "vb_vajda_v" "EpsOptimalReach.v" 182 (Some 182) StHit) (
  cons (mkAnchor "论文18-构造性可达常数" "L185" "vb_vajda_v" "EpsOptimalReach.v" 185 (Some 185) StHit) (
  cons (mkAnchor "论文18-构造性可达常数" "L188" "vb_vajda_v" "EpsOptimalReach.v" 188 (Some 188) StHit) (
  cons (mkAnchor "论文18-构造性可达常数" "L191" "vb_vajda_v" "EpsOptimalReach.v" 191 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L230" "vb_vajda_v" "EpsOptimalReach.v" 230 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L82" "vb_dp_kl_exact" "EpsOptimalReach.v" 82 (Some 82) StHit) (
  cons (mkAnchor "论文18-构造性可达常数" "L63" "vb_dp_kl_exact" "EpsOptimalReach.v" 63 (Some 63) StHit) (
  cons (mkAnchor "论文18-构造性可达常数" "L95" "vb_ln_engine" "EpsOptimalReach.v" 95 (Some 95) StHit) (
  cons (mkAnchor "论文18-构造性可达常数" "L76" "vb_ln_engine" "EpsOptimalReach.v" 76 (Some 76) StHit) (
  cons (mkAnchor "论文18-构造性可达常数" "L401" "vb_l2sum9_cap" "EpsOptimalReach.v" 401 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L414" "vb_l2sum9_cap" "EpsOptimalReach.v" 414 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L656" "vb_ln2_upper_env" "EpsOptimalReach.v" 656 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L669" "vb_ln2_upper_env" "EpsOptimalReach.v" 669 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L693" "vb_kl2_lower" "EpsOptimalReach.v" 693 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L706" "vb_kl2_lower" "EpsOptimalReach.v" 706 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L744" "vb_vajda_sat" "EpsOptimalReach.v" 744 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L757" "vb_vajda_sat" "EpsOptimalReach.v" 757 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L767" "vb_node_br" "EpsOptimalReach.v" 767 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L780" "vb_node_br" "EpsOptimalReach.v" 780 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L789" "vb_node_br" "EpsOptimalReach.v" 789 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L802" "vb_node_br" "EpsOptimalReach.v" 802 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L794" "vb_vajda_lower" "EpsOptimalReach.v" 794 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L807" "vb_vajda_lower" "EpsOptimalReach.v" 807 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L800" "vb_vajda_sat_log2" "EpsOptimalReach.v" 800 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L813" "vb_vajda_sat_log2" "EpsOptimalReach.v" 813 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L820" "vb_vajda_sat_log2" "EpsOptimalReach.v" 820 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L833" "vb_vajda_sat_log2" "EpsOptimalReach.v" 833 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L838" "vb_vajda_sat_log2" "EpsOptimalReach.v" 838 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L851" "pnt_dp_two_point" "EpsOptimalReach.v" 851 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L906" "req_fep_partition_condition" "EpsOptimalReach.v" 906 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L1121" "req_fep_partition_condition" "EpsOptimalReach.v" 1121 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L1274" "req_fep_partition_condition" "EpsOptimalReach.v" 1274 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L1319" "cec_pt" "EpsOptimalReach.v" 1319 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L1327" "cec_pt" "EpsOptimalReach.v" 1327 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L1336" "cec_pt" "EpsOptimalReach.v" 1336 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L853" "cec_pt" "EpsOptimalReach.v" 853 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "L76" "vb_dp_kl_exact" "UpReqVajdaBound.v" 76 (Some 73) StShift) (
  cons (mkAnchor "论文18-构造性可达常数" "L95" "vb_kl2" "UpReqVajdaBound.v" 95 (Some 50) StShift) (
  cons (mkAnchor "论文18-构造性可达常数" "L63" "vb_vajda_v" "UpReqVajdaBound.v" 63 (Some 60) StShift) (
  cons (mkAnchor "论文18-构造性可达常数" "L82" "vb_kl2" "UpReqVajdaBound.v" 82 (Some 50) StShift) (
  cons (mkAnchor "论文18-构造性可达常数" "L580" "vb_sharp_endpoint_zero" "UpReqVajdaBound.v" 580 (Some 576) StShift) (
  cons (mkAnchor "论文18-构造性可达常数" "L780" "vb_vajda_sat" "UpReqVajdaBound.v" 780 (Some 776) StShift) (
  cons (mkAnchor "论文18-构造性可达常数" "L767" "pnt_mult_one_l" "UpReqVajdaBound.v" 767 (Some 763) StShift) (
  cons (mkAnchor "论文18-构造性可达常数" "L802" "vb_node_br" "UpReqTailResidual.v" 802 (Some 802) StHit) (
  cons (mkAnchor "论文18-构造性可达常数" "L789" "vb_node_br" "UpReqTailResidual.v" 789 (Some 789) StHit) (
  cons (mkAnchor "论文18-构造性可达常数" "L807" "vb_vajda_lower" "UpReqTailResidual.v" 807 (Some 807) StHit) (
  cons (mkAnchor "论文18-构造性可达常数" "L794" "vb_vajda_lower" "UpReqTailResidual.v" 794 (Some 794) StHit) (
  cons (mkAnchor "论文18-构造性可达常数" "L813" "vb_vajda_lower" "UpReqTailResidual.v" 813 (Some 813) StHit) (
  cons (mkAnchor "论文18-构造性可达常数" "L800" "vb_kl2_lower" "UpReqTailResidual.v" 800 (Some 800) StHit) (
  cons (mkAnchor "论文18-构造性可达常数" "L833" "vb_vajda_sat_log2" "UpReqTailResidual.v" 833 (Some 833) StHit) (
  cons (mkAnchor "论文18-构造性可达常数" "L820" "c3e_ln2_real" "UpReqTailResidual.v" 820 (Some 820) StHit) (
  cons (mkAnchor "论文18-构造性可达常数" "L414" "vb_ln_engine" "UpReqTailResidual.v" 414 (Some 414) StHit) (
  cons (mkAnchor "论文18-构造性可达常数" "L401" "vb_ln_engine" "UpReqTailResidual.v" 401 (Some 401) StHit) (
  cons (mkAnchor "论文18-构造性可达常数" "L851" "vb_dp_kl_exact" "UpReqTailResidual.v" 851 (Some 851) StHit) (
  cons (mkAnchor "论文18-构造性可达常数" "L838" "vb_dp_kl_exact" "UpReqTailResidual.v" 838 (Some 838) StHit) (
  cons (mkAnchor "论文18-构造性可达常数" "L135" "vb_ln_engine" "UpReqTailResidual.v" 135 (Some 135) StHit) (
  cons (mkAnchor "论文18-构造性可达常数" "L620" "vb_ln_engine" "UpReqTailResidual.v" 620 (Some 620) StHit) (
  cons (mkAnchor "论文18-构造性可达常数" "L154" "vb_ln_engine" "UpReqTailResidual.v" 154 (Some 154) StHit) (
  cons (mkAnchor "论文18-构造性可达常数" "L607" "vb_ln_engine" "UpReqTailResidual.v" 607 (Some 607) StHit) (
  cons (mkAnchor "论文18-构造性可达常数" "L310" "vb_ln_engine" "UpReqTailResidual.v" 310 (Some 310) StHit) (
  cons (mkAnchor "论文18-构造性可达常数" "L308" "vb_ln_engine" "UpReqIrrationalInstances.v" 308 (Some 308) StHit) (
  cons (mkAnchor "论文18-构造性可达常数" "L290" "vb_ln_engine" "UpReqIrrationalInstances.v" 290 (Some 290) StHit) (
  cons (mkAnchor "论文18-构造性可达常数" "L310" "vb_ln_engine" "UpReqIrrationalInstances.v" 310 (Some 310) StHit) (
  cons (mkAnchor "论文18-构造性可达常数" "L311" "vb_ln_engine" "UpReqIrrationalInstances.v" 311 (Some 311) StHit) (
  cons (mkAnchor "论文18-构造性可达常数" "L2490" "pnk_conf4_branch" "UpReqPinskerCore.v" 2490 (Some 2486) StShift) (
  cons (mkAnchor "论文18-构造性可达常数" "L2446" "pnk_conf4_branch" "UpReqPinskerCore.v" 2446 (Some 2442) StShift) (
  cons (mkAnchor "论文18-构造性可达常数" "L3414" "pnk2_pinsker_trunc5" "UpReqPinskerCore.v" 3414 (Some 3409) StShift) (
  cons (mkAnchor "论文18-构造性可达常数" "L3610" "pnk2_pinsker_trunc5_mirror" "UpReqPinskerCore.v" 3610 (Some 3605) StShift) (
  cons (mkAnchor "论文18-构造性可达常数" "L3656" "pnk2_pinsker_trunc5_mirror" "UpReqPinskerCore.v" 3656 (Some 3652) StShift) (
  cons (mkAnchor "论文18-构造性可达常数" "L3075" "pnk2_pinsker_trunc5_mirror" "UpReqPinskerCore.v" 3075 (None) StNotFound) (
  cons (mkAnchor "论文18-构造性可达常数" "UpReqArgminEngine.v:160" "rae_pick_optimal" "UpReqArgminEngine.v" 160 (Some 182) StShift) (
  cons (mkAnchor "论文18-构造性可达常数" "order L646" "rae_pick_optimal" "order.txt" 646 (Some 626) StShift) (
  cons (mkAnchor "论文18-构造性可达常数" "order L649" "rae_pick_optimal" "order.txt" 649 (Some 629) StShift) (
  cons (mkAnchor "论文18-构造性可达常数" "L802" "vb_node_br" "UpReqVajdaBound.v" 802 (Some 798) StShift) (
  cons (mkAnchor "论文18-构造性可达常数" "L807" "vb_node_br" "UpReqVajdaBound.v" 807 (Some 803) StShift) (
  cons (mkAnchor "论文18-构造性可达常数" "L813" "vb_vajda_lower" "UpReqVajdaBound.v" 813 (Some 809) StShift) (
  cons (mkAnchor "论文18-构造性可达常数" "L789" "vb_node_br" "UpReqVajdaBound.v" 789 (None) StAmbiguous) (
  cons (mkAnchor "论文18-构造性可达常数" "L794" "vb_node_br" "UpReqVajdaBound.v" 794 (None) StAmbiguous) (
  cons (mkAnchor "论文18-构造性可达常数" "L800" "vb_node_br" "UpReqVajdaBound.v" 800 (None) StAmbiguous) (
  cons (mkAnchor "论文18-构造性可达常数" "L466" "cec_tangent_ceiling" "UpReqEngineCeiling.v" 466 (Some 385) StShift) (
  cons (mkAnchor "论文18-构造性可达常数" "L238" "cec_trunc_sup" "UpReqEngineCeiling.v" 238 (Some 230) StShift) (
  cons (mkAnchor "论文18-构造性可达常数" "L426" "cec_tangent_le" "UpReqEngineCeiling.v" 426 (Some 401) StShift) (
  cons (mkAnchor "论文18-构造性可达常数" "L277" "cec_trunc_sup" "UpReqEngineCeiling.v" 277 (Some 230) StShift) (
  cons (mkAnchor "论文18-构造性可达常数" "L2259" "pnk_conf4_branch" "UpReqPinskerCore.v" 2259 (Some 2442) StShift) (
  cons (mkAnchor "论文18-构造性可达常数" "L61" "" "UpReqPinskerCore.v" 61 (Some 56) StShift) (
  cons (mkAnchor "论文18-构造性可达常数" "L669" "" "UpReqPinskerCore.v" 669 (Some 664) StShift) (
  cons (mkAnchor "论文18-构造性可达常数" "L677" "" "UpReqPinskerCore.v" 677 (Some 672) StShift) (
  cons (mkAnchor "论文18-构造性可达常数" "L643" "" "UpReqPinskerCore.v" 643 (Some 638) StShift) (
  cons (mkAnchor "论文19-构造性熵相" "DTPT_Entropy.v:479" "rotc" "DTPT_Entropy.v" 479 (Some 479) StHit) (
  cons (mkAnchor "论文19-构造性熵相" "DTPT.v:117" "rotc" "DTPT.v" 117 (Some 117) StHit) (
  cons (mkAnchor "论文19-构造性熵相" "DTPT.v:993" "" "DTPT.v" 993 (Some 960) StShift) (
  cons (mkAnchor "论文19-构造性熵相" "DTPT_Rotation.v:1349" "" "DTPT_Rotation.v" 1349 (Some 1170) StShift) (
  cons (mkAnchor "论文19-构造性熵相" "DTPT_Rotation.v:549" "" "DTPT_Rotation.v" 549 (Some 370) StShift) (
  cons (mkAnchor "论文19-构造性熵相" "DTPT.v:512" "" "DTPT.v" 512 (Some 479) StShift) (
  cons (mkAnchor "论文19-构造性熵相" "DTPT_Entropy.v:158" "" "DTPT_Entropy.v" 158 (Some 135) StShift) (
  cons (mkAnchor "论文19-构造性熵相" "DTPT_Entropy.v:1280" "" "DTPT_Entropy.v" 1280 (Some 1255) StShift) (
  cons (mkAnchor "论文19-构造性熵相" "DTPT_Entropy.v:2542" "" "DTPT_Entropy.v" 2542 (Some 2517) StShift) (
  cons (mkAnchor "论文19-构造性熵相" "DTPT_Extract.v:61–177" "" "DTPT_Extract.v" 61 (Some 45) StShift) (
  cons (mkAnchor "论文19-构造性熵相" "DTPT_Bridge.v:314" "" "DTPT_Bridge.v" 314 (Some 292) StShift) (
  cons (mkAnchor "论文19-构造性熵相" "DTPT_DigTheory.v:805" "" "DTPT_DigTheory.v" 805 (Some 739) StShift) (
  cons (mkAnchor "论文19-构造性熵相" "DTPT.v:158" "" "DTPT.v" 158 (Some 125) StShift) (
  cons (mkAnchor "论文19-构造性熵相" "DTPT.v:72" "" "DTPT.v" 72 (Some 39) StShift) (
  cons (mkAnchor "论文19-构造性熵相" "DTPT.v:2104" "" "DTPT.v" 2104 (Some 2071) StShift) (
  cons (mkAnchor "论文19-构造性熵相" "DTPT.v:55" "" "DTPT.v" 55 (Some 22) StShift) (
  cons (mkAnchor "论文19-构造性熵相" "DTPT_DigTheory.v:519" "" "DTPT_DigTheory.v" 519 (Some 453) StShift) (
  cons (mkAnchor "论文19-构造性熵相" "DTPT_Rotation.v:1548" "ev_eqb_leibniz_gap" "DTPT_Rotation.v" 1548 (Some 1548) StHit) (
  cons (mkAnchor "论文19-构造性熵相" "DTPT_Truth.v:1227" "ev_eqb_leibniz_gap" "DTPT_Truth.v" 1227 (Some 1140) StShift) (
  cons (mkAnchor "论文19-构造性熵相" "DTPT_DigTheory.v:403" "" "DTPT_DigTheory.v" 403 (Some 337) StShift) (
  cons (mkAnchor "论文19-构造性熵相" "DTPT_Bridge.v:80" "" "DTPT_Bridge.v" 80 (Some 61) StShift) (
  cons (mkAnchor "论文19-构造性熵相" "DTPT.v:699" "xq_pair_dist_le" "DTPT.v" 699 (Some 688) StShift) (
  cons (mkAnchor "论文19-构造性熵相" "DTPT.v:721" "xq_pair_dist_le" "DTPT.v" 721 (Some 688) StShift) (
  cons (mkAnchor "论文19-构造性熵相" "DTPT.v:754" "xq_pair_dist_le" "DTPT.v" 754 (Some 743) StShift) (
  cons (mkAnchor "论文19-构造性熵相" "DTPT.v:2813" "" "DTPT.v" 2813 (Some 2813) StHit) (
  cons (mkAnchor "论文19-构造性熵相" "DTPT.v:147" "" "DTPT.v" 147 (Some 114) StShift) (
  cons (mkAnchor "论文19-构造性熵相" "DTPT.v:498" "" "DTPT.v" 498 (Some 465) StShift) (
  cons (mkAnchor "论文19-构造性熵相" "DTPT.v:2140" "dedup" "DTPT.v" 2140 (None) StAmbiguous) (
  cons (mkAnchor "论文19-构造性熵相" "DTPT_Bridge.v:217" "mu_total_mass_set" "DTPT_Bridge.v" 217 (Some 195) StShift) (
  cons (mkAnchor "论文19-构造性熵相" "DTPT.v:3535" "mu_fiber_mass_lb" "DTPT.v" 3535 (Some 3502) StShift) (
  cons (mkAnchor "论文19-构造性熵相" "DTPT_Rotation.v:2526" "rotc_supersedes_rot_id" "DTPT_Rotation.v" 2526 (Some 2345) StShift) (
  cons (mkAnchor "论文19-构造性熵相" "DTPT.v:127" "rot_cyclic_cluster_superseded" "DTPT.v" 127 (Some 127) StHit) (
  cons (mkAnchor "论文19-构造性熵相" "DTPT_Rotation.v:1639" "rotc_supersedes_rot_id" "DTPT_Rotation.v" 1639 (Some 2345) StShift) (
  cons (mkAnchor "论文19-构造性熵相" "DTPT_Rotation.v:2590" "deprecated_consumers_map_u12_phase_side_always_zero" "DTPT_Rotation.v" 2590 (Some 2532) StShift) (
  cons (mkAnchor "论文19-构造性熵相" "DTPT_Rotation.v:2732" "lam_opt_cross_phase_real" "DTPT_Rotation.v" 2732 (Some 2868) StShift) (
  cons (mkAnchor "论文19-构造性熵相" "DTPT_Entropy.v:67" "" "DTPT_Entropy.v" 67 (Some 44) StShift) (
  cons (mkAnchor "论文19-构造性熵相" "DTPT_Entropy.v:1274–1277" "" "DTPT_Entropy.v" 1274 (Some 1249) StShift) (
  cons (mkAnchor "论文19-构造性熵相" "DTPT_Entropy.v:1477" "" "DTPT_Entropy.v" 1477 (Some 1452) StShift) (
  cons (mkAnchor "论文19-构造性熵相" "DTPT_Entropy.v:1470–1476" "" "DTPT_Entropy.v" 1470 (Some 1470) StHit) (
  cons (mkAnchor "论文19-构造性熵相" "DTPT_Entropy.v:1950" "collide" "DTPT_Entropy.v" 1950 (Some 1939) StShift) (
  cons (mkAnchor "论文19-构造性熵相" "DTPT_Bridge.v:178" "collide" "DTPT_Bridge.v" 178 (None) StAmbiguous) (
  cons (mkAnchor "论文19-构造性熵相" "DTPT_Bridge.v:192" "" "DTPT_Bridge.v" 192 (Some 170) StShift) (
  cons (mkAnchor "论文19-构造性熵相" "DTPT_Entropy.v:2866" "maxcount_app_ge_l" "DTPT_Entropy.v" 2866 (Some 2798) StShift) (
  cons (mkAnchor "论文19-构造性熵相" "DTPT_Entropy.v:3076" "sqsum_cross_sym" "DTPT_Entropy.v" 3076 (Some 3016) StShift) (
  cons (mkAnchor "论文19-构造性熵相" "DTPT_Rotation.v:382" "" "DTPT_Rotation.v" 382 (Some 203) StShift) (
  cons (mkAnchor "论文19-构造性熵相" "DTPT_Bridge_Rot.v:120" "" "DTPT_Bridge_Rot.v" 120 (Some 64) StShift) (
  cons (mkAnchor "论文19-构造性熵相" "DTPT_Rotation.v:1053" "rotc_periodic" "DTPT_Rotation.v" 1053 (Some 1080) StShift) (
  cons (mkAnchor "论文19-构造性熵相" "DTPT_Rotation.v:1527" "phase_side_cyc_side_degenerate" "DTPT_Rotation.v" 1527 (Some 1346) StShift) (
  cons (mkAnchor "论文19-构造性熵相" "DTPT_Rotation.v:1142" "rotc_spectrum_bound" "DTPT_Rotation.v" 1142 (Some 963) StShift) (
  cons (mkAnchor "论文19-构造性熵相" "DTPT_Bridge_Rot.v:147" "rotc_class_sharp_ub_set" "DTPT_Bridge_Rot.v" 147 (None) StAmbiguous) (
  cons (mkAnchor "论文19-构造性熵相" "DTPT_Bridge_Rot.v:132" "rotc_class_sharp_ub_set" "DTPT_Bridge_Rot.v" 132 (Some 76) StShift) (
  cons (mkAnchor "论文19-构造性熵相" "DTPT.v:91" "" "DTPT.v" 91 (Some 58) StShift) (
  cons (mkAnchor "论文19-构造性熵相" "DTPT_Rotation.v:320" "" "DTPT_Rotation.v" 320 (Some 141) StShift) (
  cons (mkAnchor "论文19-构造性熵相" "DTPT_Rotation.v:2133" "" "DTPT_Rotation.v" 2133 (Some 1952) StShift) (
  cons (mkAnchor "论文19-构造性熵相" "DTPT_Bridge_Rot.v:293" "" "DTPT_Bridge_Rot.v" 293 (Some 237) StShift) (
  cons (mkAnchor "论文19-构造性熵相" "DTPT_Bridge_Rot.v:359" "" "DTPT_Bridge_Rot.v" 359 (Some 303) StShift) (
  cons (mkAnchor "论文19-构造性熵相" "DTPT_Entropy.v:80" "lam_opt" "DTPT_Entropy.v" 80 (Some 80) StHit) (
  cons (mkAnchor "论文19-构造性熵相" "DTPT_Rotation.v:1955" "lam_opt" "DTPT_Rotation.v" 1955 (Some 1887) StShift) (
  cons (mkAnchor "论文19-构造性熵相" "DTPT_Bridge_Rot.v:198" "lam_opt_cross_phase" "DTPT_Bridge_Rot.v" 198 (Some 198) StHit) (
  cons (mkAnchor "论文19-构造性熵相" "DTPT_Rotation.v:2791" "" "DTPT_Rotation.v" 2791 (Some 2610) StShift) (
  cons (mkAnchor "论文19-构造性熵相" "DTPT_Rotation.v:2826" "lam_opt" "DTPT_Rotation.v" 2826 (None) StNotFound) (
  cons (mkAnchor "论文19-构造性熵相" "DTPT_Entropy.v:2901" "align_lambda_opt" "DTPT_Entropy.v" 2901 (Some 2875) StShift) (
  cons (mkAnchor "论文19-构造性熵相" "DTPT.v:890" "" "DTPT.v" 890 (Some 857) StShift) (
  cons (mkAnchor "论文19-构造性熵相" "DTPT_Entropy.v:862" "" "DTPT_Entropy.v" 862 (Some 837) StShift) (
  cons (mkAnchor "论文19-构造性熵相" "DTPT_Rotation.v:1550" "" "DTPT_Rotation.v" 1550 (Some 1369) StShift) (
  cons (mkAnchor "论文19-构造性熵相" "DTPT_Bridge_Rot.v:166" "phase_dev_spec_set" "DTPT_Bridge_Rot.v" 166 (Some 110) StShift) (
  cons (mkAnchor "论文19-构造性熵相" "DTPT_Truth.v:801" "level_le_total" "DTPT_Truth.v" 801 (Some 460) StShift) (
  cons (mkAnchor "论文19-构造性熵相" "DTPT_Truth.v:317" "tarski" "DTPT_Truth.v" 317 (Some 231) StShift) (
  cons (mkAnchor "论文19-构造性熵相" "DTPT_Truth.v:1134" "ev_cong" "DTPT_Truth.v" 1134 (Some 1047) StShift) (
  cons (mkAnchor "论文19-构造性熵相" "DTPT_Bridge_Dig.v:157" "" "DTPT_Bridge_Dig.v" 157 (Some 122) StShift) (
  cons (mkAnchor "论文19-构造性熵相" "DTPT_Bridge.v:539" "sqsum_app_eq2_set" "DTPT_Bridge.v" 539 (Some 787) StShift) (
  cons (mkAnchor "论文19-构造性熵相" "DTPT_Extract.v:50–57" "" "DTPT_Extract.v" 50 (Some 34) StShift) (
  cons (mkAnchor "论文19-构造性熵相" "order L284" "" "order.txt" 284 (Some 284) StHit) (
  cons (mkAnchor "论文19-构造性熵相" "order L329" "" "order.txt" 329 (Some 329) StHit) (
  cons (mkAnchor "论文19-构造性熵相" "order L611" "" "order.txt" 611 (Some 611) StHit) (
  cons (mkAnchor "论文19-构造性熵相" "order L256" "" "order.txt" 256 (Some 256) StHit) (
  cons (mkAnchor "论文19-构造性熵相" "order L660" "" "order.txt" 660 (Some 640) StShift) (
  cons (mkAnchor "论文19-构造性熵相" "DTPT_Rotation.v:2693" "lam_opt_cross_phase_real" "DTPT_Rotation.v" 2693 (Some 2576) StShift) (
  cons (mkAnchor "论文19-构造性熵相" "DTPT.v:38" "" "DTPT.v" 38 (Some 38) StHit) (
  cons (mkAnchor "论文19-构造性熵相" "DTPT.v:1055" "" "DTPT.v" 1055 (Some 1022) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "AttnDoeblin.v:679" "bs_minorization" "AttnDoeblin.v" 679 (Some 693) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "S13_NLiveAudit.v:3018" "bs_minorization" "S13_NLiveAudit.v" 3018 (Some 3018) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "UpReqIndex.v:3695" "real_expf_realizable" "UpReqIndex.v" 3695 (None) StNotFound) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "UpReqMixLogA.v:1198" "mixa_pow_budget_log" "UpReqMixLogA.v" 1198 (Some 1212) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "UpReqMixLogB.v:780" "mixb_sel_scale" "UpReqMixLogB.v" 780 (Some 794) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "UpReqMixLogD.v:1185" "mixd_k_select_log_mulcost" "UpReqMixLogD.v" 1185 (Some 1199) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "UpReqMixLogE.v:566" "mixe_cf_cap" "UpReqMixLogE.v" 566 (Some 566) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "R2BishopLogSel.v:302" "mix_k_select_bishop" "R2BishopLogSel.v" 302 (Some 316) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "UpReqCauchyLogBound.v:324" "cl_bsearch_log_bound" "UpReqCauchyLogBound.v" 324 (Some 324) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "UpReqIndex.v:2421-2445" "mixe_cf_cap" "UpReqIndex.v" 2421 (Some 2421) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "AttnDoeblin.v:757" "real_expf_realizable" "AttnDoeblin.v" 757 (Some 771) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "P7BoundedSoftmaxDeep.v:118" "p7d_swap_of_sum_eq_list" "P7BoundedSoftmaxDeep.v" 118 (Some 132) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L442" "states" "UpTVDoeblin.v" 442 (None) StAmbiguous) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L448" "delta" "UpTVDoeblin.v" 448 (None) StAmbiguous) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L19" "real_le" "KLWallClosed.v" 19 (Some 131) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L262" "klc_one_minus_eta_le_one_weak" "KLWallClosed.v" 262 (Some 243) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L173" "real_mult_zero" "RateTheoryAblation.v" 173 (Some 173) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L197" "real_mult_zero" "RateTheoryAblation.v" 197 (None) StNotFound) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L174" "rta_strict_branch_real" "RateTheoryAblation.v" 174 (Some 124) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L143" "rta_strict_branch_real" "RateTheoryAblation.v" 143 (Some 124) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L169" "rta_strict_branch_real" "RateTheoryAblation.v" 169 (Some 124) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "UpRealLeB.v:116" "real_le_to_le_b" "UpRealLeB.v" 116 (Some 130) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "EnergyTempMonoB.v:49" "real_le" "EnergyTempMonoB.v" 49 (None) StNotFound) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "G01_CoreMicro.v:524" "real_lt_le_bridge" "G01_CoreMicro.v" 524 (Some 558) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L148" "rta_strict_branch_real" "RateTheoryAblation.v" 148 (Some 124) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L215" "rta_strict_branch_real" "RateTheoryAblation.v" 215 (Some 191) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "S07_RealSetoidExpLog.v:5498" "log_lower" "S07_RealSetoidExpLog.v" 5498 (None) StAmbiguous) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "LogTwoEnvelope.v:494" "log_inv_exp_neg_thm" "LogTwoEnvelope.v" 494 (Some 494) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "S07_RealSetoidExpLog.v:2798" "real_arch" "S07_RealSetoidExpLog.v" 2798 (Some 2798) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L507" "real_arch" "UpReqMixingTime.v" 507 (Some 500) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L538" "real_le" "S02_CauchyComplete.v" 538 (Some 472) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L1552" "mix_k_select" "UpTVDoeblin.v" 1552 (Some 1552) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L614" "mix_pow_budget" "UpTVDoeblin.v" 614 (Some 614) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L638" "mix_pow_budget" "UpTVDoeblin.v" 638 (Some 638) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L507" "mix_pow_budget" "UpTVDoeblin.v" 507 (Some 507) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L565" "" "UpReqMixingTime.v" 565 (Some 557) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L364" "mixe_cf_cap_gen" "UpReqMixLogE.v" 364 (Some 538) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L564" "mixe_cf_cap" "UpReqMixLogE.v" 564 (Some 566) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L592" "mixe_cf_cap" "UpReqMixLogE.v" 592 (Some 566) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L607" "mixe_cf_cap" "UpReqMixLogE.v" 607 (Some 602) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L1187" "mixa_k_select_log" "UpReqMixLogA.v" 1187 (Some 1223) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L1209" "mixa_k_select_log" "UpReqMixLogA.v" 1209 (Some 1223) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L830" "" "UpReqMixLogB.v" 830 (Some 792) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L832" "" "UpReqMixLogB.v" 832 (Some 794) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L597" "" "UpReqMixLogD.v" 597 (Some 611) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L601" "" "UpReqMixLogD.v" 601 (Some 615) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L1470" "cf2_mixing_time_le_gen" "UpReqConcFin2.v" 1470 (Some 1434) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L1552" "req_r_pow" "UpReqConcFin2.v" 1552 (None) StAmbiguous) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "AbsSqClose.v:195" "asc_abs_nonneg" "AbsSqClose.v" 195 (Some 195) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "UpAblP7_AbsNonNeg.v:223" "uabp7an_abs_nonneg_uncond" "UpAblP7_AbsNonNeg.v" 223 (Some 225) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L1425" "abs_nonneg" "AbsSqClose.v" 1425 (Some 323) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L574" "" "AbsSqClose.v" 574 (None) StNotFound) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L615" "" "AbsSqClose.v" 615 (None) StNotFound) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L569" "" "AbsSqClose.v" 569 (None) StNotFound) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L610" "" "AbsSqClose.v" 610 (None) StNotFound) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "UpReqIndex.v:2425-2425" "mixa_min_real_below" "UpReqIndex.v" 2425 (Some 2425) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "UpReqIndex.v:2433-2433" "mixb_sel_scale" "UpReqIndex.v" 2433 (Some 2433) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "UpReqIndex.v:2441-2445" "mixd_k_select_log_mulcost" "UpReqIndex.v" 2441 (Some 2441) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "UpReqIndex.v:2421-2421" "mixe_cf_cap" "UpReqIndex.v" 2421 (Some 2421) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "order.txt:635" "" "order.txt" 635 (Some 635) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L704" "" "UpAblDeltaStarSuboptimal.v" 704 (None) StNotFound) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L710" "" "UpAblDeltaStarSuboptimal.v" 710 (None) StNotFound) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L701" "bs_minorization" "AttnDoeblin.v" 701 (Some 693) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L620" "bs_factor_ge_lo" "AttnDoeblin.v" 620 (Some 612) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L647" "z_ub" "AttnDoeblin.v" 647 (Some 626) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L590" "bs_lo_hi_eq" "AttnDoeblin.v" 590 (Some 582) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L561" "expf" "AttnDoeblin.v" 561 (Some 553) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L563" "expf" "AttnDoeblin.v" 563 (None) StAmbiguous) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L452" "enum" "AttnDoeblin.v" 452 (None) StAmbiguous) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L209" "minus" "S01_BaseRing.v" 209 (Some 221) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L293" "minus" "S04_RealExpLogConv.v" 293 (Some 303) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L176" "bs_delta_star_lt_one" "UpReqAttnMixTime.v" 176 (Some 96) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "UpReqMixingTime.v:120" "real_arch" "UpReqMixingTime.v" 120 (None) StNotFound) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "UpReqAttnMixTime.v:190–327" "amtr_" "UpReqAttnMixTime.v" 190 (None) StAmbiguous) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "UpReqUMixSelect.v:532–581" "ums_pow_tail" "UpReqUMixSelect.v" 532 (None) StAmbiguous) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "UpReqMixingTime.v:658–658" "mix_k_compute" "UpReqMixingTime.v" 658 (Some 660) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "S01_BaseRing.v:341" "mix_k_compute" "S01_BaseRing.v" 341 (Some 341) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "UpReqConcB1.v:263" "cb1_arch" "UpReqConcB1.v" 263 (Some 277) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "UpReqConcB1.v:128" "cb1_bs_abs" "UpReqConcB1.v" 128 (Some 142) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "UpAblP7_AbsNonNeg.v:160" "uabp7an_core" "UpAblP7_AbsNonNeg.v" 160 (Some 174) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "UpAblP7_AbsNonNeg.v:243" "uabp7an_uncond_to_eps" "UpAblP7_AbsNonNeg.v" 243 (Some 237) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "S07_RealSetoidExpLog.v:8033" "abs_nonneg" "S07_RealSetoidExpLog.v" 8033 (Some 8034) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "UpReqAlgebra.v:1021" "abs_nonneg" "UpReqAlgebra.v" 1021 (Some 1021) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L68" "bs_kernel" "UpReqAttnMixTime.v" 68 (Some 88) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L285" "bs_kernel" "UpReqAttnMixTime.v" 285 (Some 88) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L61" "destruct" "S01_BaseRing.v" 61 (None) StAmbiguous) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L465" "real_eq" "S02_CauchyComplete.v" 465 (Some 473) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L130" "" "UpReqSampling.v" 130 (Some 142) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L733" "" "UpReqSampling.v" 733 (Some 745) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L319" "csm_abs_sum_le_eps" "UpReqConcSoftmax.v" 319 (Some 294) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L856" "rsq_bounded_softmax_tv_iter" "UpReqConcMixSel.v" 856 (None) StAmbiguous) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L887" "cmk_attention_mixing_time" "UpReqConcMixSel.v" 887 (Some 909) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L23" "cb1_arch" "UpReqConcB1.v" 23 (None) StNotFound) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L141" "cb1_arch" "UpReqConcB1.v" 141 (None) StNotFound) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L352" "csm_b1_unconditional_mixing_time" "UpReqConcB1.v" 352 (Some 366) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L365" "csm_b1_unconditional_mixing_time" "UpReqConcB1.v" 365 (Some 366) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L324" "cbt_unconditional_mixing_time" "UpReqConcB2Time.v" 324 (Some 338) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L336" "cbt_unconditional_mixing_time" "UpReqConcB2Time.v" 336 (Some 338) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L329" "expf" "UpReqConcB2Time.v" 329 (Some 387) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "UpReqConcB1.v:266–267" "real_arch" "UpReqConcB1.v" 266 (Some 280) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "S07_RealSetoidExpLog.v:2805" "real_arch" "S07_RealSetoidExpLog.v" 2805 (Some 2798) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L263" "cb1_arch" "UpReqConcB1.v" 263 (Some 277) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L238" "real_arch" "UpReqConcB1.v" 238 (Some 280) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L96" "cb1_swap_lists" "S07_RealSetoidExpLog.v" 96 (Some 96) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L128" "cb1_bs_abs" "S07_RealSetoidExpLog.v" 128 (Some 128) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L168" "cb1_sum_eq_list" "S07_RealSetoidExpLog.v" 168 (Some 168) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L319" "lhs_" "UpReqConcMixSel.v" 319 (Some 319) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L191" "mtw_rows_ne" "UpAblMetaWindow.v" 191 (Some 191) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L179" "mwi_degenerate_collapse_uniform" "UpAblMetaWindow.v" 179 (Some 160) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L299" "mtp_anchor" "UpAblMetaTemp.v" 299 (Some 289) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L306" "mtp_anchor" "UpAblMetaTemp.v" 306 (Some 289) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "UpAblMetaTemp.v:296" "mtp_anchor_divergence" "UpAblMetaTemp.v" 296 (Some 296) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L57" "" "UpStepKLM3.v" 57 (Some 27) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L515" "" "UpStepKLM3.v" 515 (Some 499) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L78" "" "UpStepKLM3.v" 78 (Some 62) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L258" "lpn_backward" "UpReqLpoEquiv.v" 258 (Some 357) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L351" "lpn_backward" "UpReqLpoEquiv.v" 351 (Some 357) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L438" "lpn_equivalence" "UpReqLpoEquiv.v" 438 (Some 444) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L3" "lpn_equivalence" "UpReqLpoEquiv.v" 3 (None) StNotFound) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L239" "lpn_equivalence" "UpReqLpoEquiv.v" 239 (Some 444) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "UpReqUMixSelect.v:91–622" "ums_" "UpReqUMixSelect.v" 91 (Some 91) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "UpReqConcMixSel.v:30" "lt_plus_compat_lt_le" "UpReqConcMixSel.v" 30 (Some 50) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L284" "cbt_unconditional_mixing_time" "UpReqConcB2Time.v" 284 (Some 338) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L296" "cbt_unconditional_mixing_time" "UpReqConcB2Time.v" 296 (Some 338) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "UpAblP7_WallEpsChain_B.v:74–390" "inv_pos" "UpAblP7_WallEpsChain_B.v" 74 (Some 74) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "ConcMixSelFeed.v:166–241" "inv_pos" "ConcMixSelFeed.v" 166 (Some 166) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "AbsLeId.v:42" "ali_abs_ge_zero_id" "AbsLeId.v" 42 (Some 42) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "AbsSqClose.v:61" "asc_lt_dec_id" "AbsSqClose.v" 61 (Some 38) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "UpAblP7_WallEpsChain_B.v:74" "ubw_b_lt_plus_compat_lt_le" "UpAblP7_WallEpsChain_B.v" 74 (Some 56) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "UpAblP7_UMixSelect.v:143" "lt_plus_compat_lt_le" "UpAblP7_UMixSelect.v" 143 (Some 154) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "S07:6147" "lt_plus_compat_lt_le" "S07_RealSetoidExpLog.v" 6147 (Some 6148) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "S07:6143" "lt_plus_compat_lt_le" "S07_RealSetoidExpLog.v" 6143 (Some 6148) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "UpAblP7_Paper7Ablation.v:221" "uabp7_kappa_in01_package" "UpAblP7_Paper7Ablation.v" 221 (Some 221) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "S07_RealSetoidExpLog.v:6148" "real_lt_plus_compat_lt_le" "S07_RealSetoidExpLog.v" 6148 (Some 6148) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L209" "minus" "S04_RealExpLogConv.v" 209 (Some 207) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "UpAblMetaWindow.v:23" "mtw_no_mixing_below" "UpAblMetaWindow.v" 23 (Some 192) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "UpTVDoeblin.v:1930-1950" "tvd_dstar_instance" "UpTVDoeblin.v" 1930 (Some 1944) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "UpReqConcSoftmax.v:280" "csm_abs_sum_le_eps" "UpReqConcSoftmax.v" 280 (Some 294) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "UpReqMixingTime.v:599–602" "tv_rpow" "UpReqMixingTime.v" 599 (None) StAmbiguous) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "MixingTimeG2.v:28–29" "ums_k_select" "MixingTimeG2.v" 28 (Some 28) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "UpReqMixingTime.v:693-693" "ums_k_select" "UpReqMixingTime.v" 693 (Some 693) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "UpAblMetaLow.v:326" "mte_inv_divergence" "UpAblMetaLow.v" 326 (Some 326) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "order L496" "" "order.txt" 496 (Some 496) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "order L497" "" "order.txt" 497 (Some 497) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "UpReqAttnMixTime.v:136" "amt_attention_mixing_time" "UpReqAttnMixTime.v" 136 (Some 150) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L3" "" "UpReqAttnMixTime.v" 3 (Some 3) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L15" "" "UpReqAttnMixTime.v" 15 (Some 15) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L13" "" "UpReqAttnMixTime.v" 13 (Some 13) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L149" "" "UpReqAttnMixTime.v" 149 (Some 163) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L670" "" "UpReqAttnMixTime.v" 670 (None) StNotFound) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L387" "" "UpReqAttnMixTime.v" 387 (None) StNotFound) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L707" "" "UpReqAttnMixTime.v" 707 (None) StNotFound) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L709" "" "UpReqAttnMixTime.v" 709 (None) StNotFound) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L900" "" "UpReqAttnMixTime.v" 900 (None) StNotFound) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L999" "" "UpReqAttnMixTime.v" 999 (None) StNotFound) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L1003" "" "UpReqAttnMixTime.v" 1003 (None) StNotFound) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L200" "ums_k_select" "UpReqAttnMixTime.v" 200 (None) StAmbiguous) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L532" "ums_k_select" "UpReqUMixSelect.v" 532 (Some 532) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L534" "mixb_gallop" "LoHiSqueeze.v" 534 (None) StNotFound) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L545" "mixb_sel_scale" "LoHiSqueeze.v" 545 (None) StNotFound) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L808" "mixb_sel_scale" "LoHiSqueeze.v" 808 (None) StNotFound) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L832" "mixb_k_select_log" "LoHiSqueeze.v" 832 (None) StNotFound) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L1230" "mixb_k_select_log" "LoHiSqueeze.v" 1230 (None) StNotFound) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L1293" "mixb_k_select_log" "LoHiSqueeze.v" 1293 (None) StNotFound) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L1254" "cf2_mixing_time_le_gen" "LoHiSqueeze.v" 1254 (None) StNotFound) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L1317" "cf2_mixing_time_le_gen" "LoHiSqueeze.v" 1317 (None) StNotFound) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L1397" "cf2_mixing_time_le_gen" "LoHiSqueeze.v" 1397 (None) StNotFound) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L1470" "cf2_mixing_time_le_gen" "LoHiSqueeze.v" 1470 (None) StNotFound) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "UpReqMixingTime.v:619" "" "UpReqMixingTime.v" 619 (Some 611) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "UpReqLpoEquiv.v:249" "" "UpReqLpoEquiv.v" 249 (Some 245) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L981" "" "UpReqMixingTime.v" 981 (None) StNotFound) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L5501" "distrib" "uabl_attn_full_instance.v" 5501 (None) StNotFound) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "S13_NLiveAudit.v:3096" "real_expf_realizable" "S13_NLiveAudit.v" 3096 (Some 3096) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "S13_NLiveAudit.v:2441" "real_expf_realizable" "S13_NLiveAudit.v" 2441 (Some 3096) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L5501" "real_expf_realizable" "UpReqMixingTime.v" 5501 (None) StNotFound) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L7556" "real_expf_realizable" "UpReqMixingTime.v" 7556 (None) StNotFound) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L779" "real_expf_realizable" "AttnDoeblin.v" 779 (Some 771) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L552" "bs_hi_pos" "AttnDoeblin.v" 552 (None) StAmbiguous) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L690" "bs_kernel" "AttnDoeblin.v" 690 (None) StAmbiguous) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L678" "bs_kernel_row" "AttnDoeblin.v" 678 (Some 670) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L568" "bs_hi_pos" "AttnDoeblin.v" 568 (Some 560) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L1990" "n_pos" "UpTVDoeblin.v" 1990 (None) StAmbiguous) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L1621" "tvd_dstar_instance" "UpTVDoeblin.v" 1621 (Some 1944) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L1959" "tvd_dstar_iter_contraction" "UpTVDoeblin.v" 1959 (Some 1964) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L1979" "tvd_dstar_iter_contraction" "UpTVDoeblin.v" 1979 (Some 1964) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "UpAblP7_Paper7Ablation.v:82" "uabp7_expf_wd_mirror" "UpAblP7_Paper7Ablation.v" 82 (Some 82) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "P7BoundedSoftmaxDeep.v:169" "p7d_tv_contraction_no_swap" "P7BoundedSoftmaxDeep.v" 169 (Some 183) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "AttnDoeblin.v:480" "bs_lpc" "AttnDoeblin.v" 480 (Some 483) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "S07_RealSetoidExpLog.v:8029" "abs_nonneg" "S07_RealSetoidExpLog.v" 8029 (Some 8034) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "UpReqAlgebra.v:919-922" "abs_nonneg" "UpReqAlgebra.v" 919 (Some 919) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "UpReqUMixSelect.v:84" "lt_plus_compat_lt_le" "UpReqUMixSelect.v" 84 (Some 84) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "P7BoundedSoftmaxDeep.v:151" "lt_plus_compat_lt_le" "P7BoundedSoftmaxDeep.v" 151 (Some 151) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "UpReqCauchy.v:122" "lt_plus_compat_lt_le" "UpReqCauchy.v" 122 (Some 147) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "UpReqSampling.v:135" "lt_plus_compat_lt_le" "UpReqSampling.v" 135 (None) StAmbiguous) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "UpAblP7_UMixSelect.v:79" "uabm_ums_pow_budget_slot_freeze" "UpAblP7_UMixSelect.v" 79 (Some 91) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "S07_RealSetoidExpLog.v:8596" "real_lt_plus_compat_lt_le" "S07_RealSetoidExpLog.v" 8596 (Some 6689) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "UpReqSampling.v:110" "rsq_u_abs_row" "UpReqSampling.v" 110 (None) StNotFound) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "UpReqSampling.v:493" "rsq_u_abs_row" "UpReqSampling.v" 493 (Some 507) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "UpReqConcSoftmax.v:21-21" "rsq_u_tv_iter" "UpReqConcSoftmax.v" 21 (Some 21) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "UpReqConcB2.v:24" "rsq_u_tv_iter" "UpReqConcB2.v" 24 (Some 24) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "UpAblP7_Paper7Ablation.v:135-190" "uabp7_kappa_in01_package" "UpAblP7_Paper7Ablation.v" 135 (Some 221) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "UpAblP7_LoHiSqueeze.v:64" "delta_pos" "UpAblP7_LoHiSqueeze.v" 64 (Some 64) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L636" "mixe_cf_cap_div" "UpReqMixLogE.v" 636 (Some 581) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L252" "mixa_bsearch" "UpReqMixLogA.v" 252 (Some 287) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L262" "mixa_bsearch_correct" "UpReqMixLogA.v" 262 (Some 297) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L321" "mixa_fuel_log" "UpReqMixLogA.v" 321 (Some 356) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L957" "mixa_sel_accounts" "UpReqMixLogA.v" 957 (Some 993) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L1211" "mixa_k_select_log" "UpReqMixLogA.v" 1211 (Some 1223) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L534" "mixb_bsearch" "UpReqMixLogB.v" 534 (Some 517) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L808" "mixb_sel_scale" "UpReqMixLogB.v" 808 (Some 794) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L1230" "mixb_sel_scale" "UpReqMixLogB.v" 1230 (Some 1199) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L1293" "mixb_k_select_log" "UpReqMixLogB.v" 1293 (Some 1293) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L334" "mixd_ladder" "UpReqMixLogD.v" 334 (Some 362) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L179" "cf2_mu0" "UpReqConcFin2.v" 179 (Some 179) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L248" "cf2_tv_pos" "UpReqConcFin2.v" 248 (Some 241) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L1167" "cf2_omd_form" "UpReqConcFin2.v" 1167 (Some 1196) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L1176" "cf2_tv_iter_mu0" "UpReqConcFin2.v" 1176 (Some 1209) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L1191" "cf2_mixing_time" "UpReqConcFin2.v" 1191 (Some 1357) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L1324" "cf2_mixing_time" "UpReqConcFin2.v" 1324 (Some 1357) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L1397" "cf2_mixing_time" "UpReqConcFin2.v" 1397 (Some 1357) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L981" "" "UpReqLpoEquiv.v" 981 (None) StNotFound) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "AttnDoeblin.v:701" "bs_minorization" "AttnDoeblin.v" 701 (Some 693) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "S13_NLiveAudit.v:3024" "bs_minorization" "S13_NLiveAudit.v" 3024 (Some 3018) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "UpReqMixLogB.v:832" "real_arch" "UpReqMixLogB.v" 832 (None) StAmbiguous) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "UpReqMixLogD.v:1186" "real_arch" "UpReqMixLogD.v" 1186 (Some 1186) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "UpReqMixLogE.v:585" "real_arch" "UpReqMixLogE.v" 585 (Some 585) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "R2BishopLogSel.v:330" "real_arch" "R2BishopLogSel.v" 330 (Some 330) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "UpReqCauchyLogBound.v:157" "real_arch" "UpReqCauchyLogBound.v" 157 (Some 157) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "UpReqIndex.v:2422-2445" "eck_r6_param_k" "UpReqIndex.v" 2422 (Some 2422) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L442" "tv_rpow" "R2BishopLogSel.v" 442 (Some 442) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L1552" "tv_rpow" "R2BishopLogSel.v" 1552 (None) StNotFound) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L465" "tv_rpow" "R2BishopLogSel.v" 465 (Some 465) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L538" "tv_rpow" "R2BishopLogSel.v" 538 (None) StNotFound) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L209" "tv_rpow" "R2BishopLogSel.v" 209 (Some 209) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L293" "tv_rpow" "R2BishopLogSel.v" 293 (Some 293) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L239" "tv_rpow" "R2BishopLogSel.v" 239 (Some 239) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L258" "tv_rpow" "R2BishopLogSel.v" 258 (Some 258) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L351" "tv_rpow" "R2BishopLogSel.v" 351 (Some 351) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L438" "tv_rpow" "R2BishopLogSel.v" 438 (Some 438) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L176" "tv_rpow" "R2BishopLogSel.v" 176 (Some 176) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L200" "tv_rpow" "R2BishopLogSel.v" 200 (Some 200) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L856" "tv_rpow" "R2BishopLogSel.v" 856 (None) StNotFound) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L887" "tv_rpow" "R2BishopLogSel.v" 887 (None) StNotFound) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L191" "tv_rpow" "R2BishopLogSel.v" 191 (Some 191) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L179" "tv_rpow" "R2BishopLogSel.v" 179 (Some 179) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L564" "tv_rpow" "R2BishopLogSel.v" 564 (None) StNotFound) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L592" "tv_rpow" "R2BishopLogSel.v" 592 (None) StNotFound) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L607" "tv_rpow" "R2BishopLogSel.v" 607 (None) StNotFound) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "UpReqConcSoftmax.v:60–324" "asc_lt_dec_id" "UpReqConcSoftmax.v" 60 (None) StNotFound) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L169" "asc_lt_dec_id" "UpReqConcSoftmax.v" 169 (Some 169) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L285" "asc_lt_dec_id" "UpReqConcSoftmax.v" 285 (Some 285) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "UpReqMixLogE.v:613" "" "UpReqMixLogE.v" 613 (Some 566) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "UpReqCauchyLogBound.v:323" "" "UpReqCauchyLogBound.v" 323 (Some 324) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "UpReqMixingTime.v:142" "mix_scale_eq_const" "UpReqMixingTime.v" 142 (Some 134) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "UpReqUMixSelect.v:560-575" "real_arch" "UpReqUMixSelect.v" 560 (Some 560) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "S03_QExp.v:404-418" "q_arch_geom" "S03_QExp.v" 404 (Some 403) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "UpReqPinskerCore.v:1296" "pnk_kl2_ge_fracsum" "UpReqPinskerCore.v" 1296 (Some 1291) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "EngineCeilingK.v:165" "eck_r6_param_k" "EngineCeilingK.v" 165 (None) StDeadFile) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "CurriculumOptTemp.v:128" "cot_optimal_temp_interval" "CurriculumOptTemp.v" 128 (Some 119) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "S02_CauchyComplete.v:467" "real_lt" "S02_CauchyComplete.v" 467 (Some 468) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "MixingTimeG2.v:115" "" "MixingTimeG2.v" 115 (Some 132) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "UpReqMixingTime.v:705-706" "" "UpReqMixingTime.v" 705 (Some 697) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "UpReqPinskerCore.v:1239-1244" "real_inv_pos_correct" "UpReqPinskerCore.v" 1239 (None) StNotFound) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "S03_QExp.v:404" "q_arch_geom" "S03_QExp.v" 404 (Some 403) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "S02:467" "real_lt" "S02_CauchyComplete.v" 467 (Some 468) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "UpReqMixingTime.v:668-674" "mix_k_compute" "UpReqMixingTime.v" 668 (Some 660) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "CurriculumOptTemp.v:145-155" "cot_curriculum_mono_b" "CurriculumOptTemp.v" 145 (Some 155) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "QstepConvergenceBound.v:481" "" "QstepConvergenceBound.v" 481 (Some 481) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "UpAblBYLowerBound.v:260" "bylb_lower_bound" "UpAblBYLowerBound.v" 260 (Some 258) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "UpAblLogWallFinal.v:359" "lgwd_equivalence" "UpAblLogWallFinal.v" 359 (Some 371) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "UpAblMetaLow.v:328" "mtl_refute_lower" "UpAblMetaLow.v" 328 (Some 340) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "UpReqIrrationalCriterion.v:286" "lic_irrational_criterion" "UpReqIrrationalCriterion.v" 286 (Some 285) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L1552" "tv_rpow" "UpAblMetaLow.v" 1552 (None) StNotFound) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L564" "" "UpReqIndex.v" 564 (Some 440) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L592" "" "UpReqIndex.v" 592 (Some 468) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L607" "" "UpReqIndex.v" 607 (Some 482) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L364" "" "UpReqIndex.v" 364 (Some 241) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L1187" "" "UpReqIndex.v" 1187 (Some 1016) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L1209" "" "UpReqIndex.v" 1209 (Some 1046) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L597" "mixd_k_select_log_mulcost" "UpReqIndex.v" 597 (Some 597) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L601" "mixd_k_select_log_mulcost" "UpReqIndex.v" 601 (Some 601) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L1470" "" "UpReqIndex.v" 1470 (Some 1298) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L1552" "" "UpReqIndex.v" 1552 (Some 1552) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L1425" "" "UpReqIndex.v" 1425 (Some 1253) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L176" "" "UpReqIndex.v" 176 (Some 63) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L200" "" "UpReqIndex.v" 200 (Some 87) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L68" "" "UpReqIndex.v" 68 (Some 68) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "S01:341" "" "S01_BaseRing.v" 341 (Some 341) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L856" "" "UpReqIndex.v" 856 (Some 726) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L887" "" "UpReqIndex.v" 887 (Some 755) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L465" "" "UpReqIndex.v" 465 (Some 342) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L538" "" "UpReqIndex.v" 538 (Some 414) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L130" "" "UpReqIndex.v" 130 (Some 130) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L733" "" "UpReqIndex.v" 733 (Some 605) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L191" "" "UpReqIndex.v" 191 (Some 191) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L179" "" "UpReqIndex.v" 179 (Some 66) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L299" "" "UpReqIndex.v" 299 (Some 180) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L306" "" "UpReqIndex.v" 306 (Some 306) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L57" "" "UpReqIndex.v" 57 (Some 57) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L78" "" "UpReqIndex.v" 78 (Some 78) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L515" "" "UpReqIndex.v" 515 (Some 392) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L239" "" "UpReqIndex.v" 239 (Some 126) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L258" "" "UpReqIndex.v" 258 (Some 258) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L351" "" "UpReqIndex.v" 351 (Some 228) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L438" "" "UpReqIndex.v" 438 (Some 315) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L442" "" "UpReqIndex.v" 442 (Some 319) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L448" "" "UpReqIndex.v" 448 (Some 325) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L209" "" "UpReqIndex.v" 209 (Some 95) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L293" "" "UpReqIndex.v" 293 (Some 293) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L159" "" "UpReqIndex.v" 159 (Some 46) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L483" "" "UpReqIndex.v" 483 (Some 360) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L610" "" "UpReqIndex.v" 610 (Some 485) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L569" "" "UpReqIndex.v" 569 (Some 445) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L528" "" "UpReqIndex.v" 528 (Some 528) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L720" "" "UpReqIndex.v" 720 (Some 593) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L745" "" "UpReqIndex.v" 745 (Some 745) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L747" "" "UpReqIndex.v" 747 (Some 618) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L750" "" "UpReqIndex.v" 750 (Some 621) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L863" "" "UpReqIndex.v" 863 (Some 733) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L216" "" "UpReqAttnMixTime.v" 216 (Some 230) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L17" "" "R2BishopLogSel.v" 17 (Some 17) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "UpReqIndex.v:2429-2431" "" "UpReqIndex.v" 2429 (Some 2429) StHit) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "AbsSqClose.v:62" "asc_lt_dec_id" "AbsSqClose.v" 62 (Some 38) StShift) (
  cons (mkAnchor "论文20-率即算法-构造性收敛的显式模量" "L285" "" "AbsSqClose.v" 285 (Some 261) StShift) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT.v:1729" "" "DTPT.v" 1729 (Some 1696) StShift) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Entropy.v:836" "" "DTPT_Entropy.v" 836 (Some 811) StShift) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Rotation.v:1484" "" "DTPT_Rotation.v" 1484 (Some 1303) StShift) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Bridge_Rot.v:142–161" "" "DTPT_Bridge_Rot.v" 142 (Some 86) StShift) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Truth.v:751" "" "DTPT_Truth.v" 751 (Some 664) StShift) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Bridge.v:252" "" "DTPT_Bridge.v" 252 (Some 230) StShift) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Truth.v:292" "" "DTPT_Truth.v" 292 (Some 206) StShift) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Bridge.v:302" "" "DTPT_Bridge.v" 302 (Some 280) StShift) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Extract.v:61–76" "" "DTPT_Extract.v" 61 (Some 45) StShift) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Bridge_All.v:219–243" "" "DTPT_Bridge_All.v" 219 (Some 184) StShift) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Entropy.v:98" "" "DTPT_Entropy.v" 98 (Some 75) StShift) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Rotation.v:1809" "" "DTPT_Rotation.v" 1809 (Some 1628) StShift) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT.v:873" "" "DTPT.v" 873 (Some 840) StShift) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Truth.v:745" "" "DTPT_Truth.v" 745 (Some 658) StShift) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Bridge_Rot.v:170" "" "DTPT_Bridge_Rot.v" 170 (Some 114) StShift) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT.v:38" "gate_pass" "DTPT.v" 38 (Some 857) StShift) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT.v:141" "gate_pass" "DTPT.v" 141 (Some 857) StShift) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT.v:74" "gate_pass" "DTPT.v" 74 (Some 857) StShift) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT.v:64" "gate_pass" "DTPT.v" 64 (Some 857) StShift) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT.v:100" "gate_pass" "DTPT.v" 100 (Some 857) StShift) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Rotation.v:366" "rotc" "DTPT_Rotation.v" 366 (None) StAmbiguous) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT.v:976" "gate_pass" "DTPT.v" 976 (Some 857) StShift) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT.v:1022" "gate_pass" "DTPT.v" 1022 (Some 857) StShift) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Truth.v:93" "level_le_total" "DTPT_Truth.v" 93 (Some 460) StShift) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Truth.v:95" "level_le_total" "DTPT_Truth.v" 95 (Some 460) StShift) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Truth.v:100" "level_le_total" "DTPT_Truth.v" 100 (Some 460) StShift) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Truth.v:107" "level_le_total" "DTPT_Truth.v" 107 (Some 460) StShift) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Truth.v:109" "level_le_total" "DTPT_Truth.v" 109 (Some 460) StShift) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Truth.v:221" "level_le_total" "DTPT_Truth.v" 221 (Some 460) StShift) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Truth.v:513" "level_le_total" "DTPT_Truth.v" 513 (Some 460) StShift) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Bridge.v:68" "" "DTPT_Bridge.v" 68 (Some 68) StHit) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT.v:873–875" "" "DTPT.v" 873 (Some 840) StShift) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT.v:1740" "llm_gate_pass_false_iff" "DTPT.v" 1740 (Some 1724) StShift) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT.v:1755" "llm_gate_pass_mono_thr" "DTPT.v" 1755 (Some 1739) StShift) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT.v:1766" "" "DTPT.v" 1766 (Some 1733) StShift) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Entropy.v:89" "gate_low_entropy" "DTPT_Entropy.v" 89 (Some 81) StShift) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Entropy.v:842" "" "DTPT_Entropy.v" 842 (Some 817) StShift) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Entropy.v:848" "" "DTPT_Entropy.v" 848 (Some 823) StShift) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Extract.v:139" "u12_gate_chain" "DTPT_Extract.v" 139 (Some 123) StShift) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Bridge_Dig.v:146" "u12_gate_chain" "DTPT_Bridge_Dig.v" 146 (None) StAmbiguous) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Bridge_Dig.v:183" "u12_gate_chain" "DTPT_Bridge_Dig.v" 183 (None) StAmbiguous) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Extract.v:146–155" "u12_gate_chain" "DTPT_Extract.v" 146 (Some 130) StShift) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Rotation.v:1484–1486" "phase_dev_true_iff" "DTPT_Rotation.v" 1484 (None) StNotFound) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Rotation.v:1495" "phase_dev_true_iff" "DTPT_Rotation.v" 1495 (None) StNotFound) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Rotation.v:1507" "phase_dev_witness" "DTPT_Rotation.v" 1507 (None) StNotFound) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Rotation.v:1558" "phase_dev_witness" "DTPT_Rotation.v" 1558 (None) StNotFound) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Rotation.v:1489" "phase_dev_witness" "DTPT_Rotation.v" 1489 (None) StNotFound) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Bridge_Rot.v:142" "phase_dev_spec_set" "DTPT_Bridge_Rot.v" 142 (Some 110) StShift) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Bridge_Rot.v:153" "phase_dev_spec_set" "DTPT_Bridge_Rot.v" 153 (None) StAmbiguous) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Bridge_Rot.v:161" "phase_dev_spec_set" "DTPT_Bridge_Rot.v" 161 (None) StAmbiguous) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Rotation.v:511" "rotc" "DTPT_Rotation.v" 511 (None) StAmbiguous) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Rotation.v:520" "rotc" "DTPT_Rotation.v" 520 (Some 341) StShift) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Rotation.v:1461" "phase_side_cyc_side_degenerate" "DTPT_Rotation.v" 1461 (Some 1346) StShift) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT.v:2852" "phase_classify" "DTPT.v" 2852 (Some 2898) StShift) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT.v:2850" "phase_classify" "DTPT.v" 2850 (Some 2898) StShift) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Rotation.v:2248" "phase_classify" "DTPT_Rotation.v" 2248 (None) StAmbiguous) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Truth.v:745–748" "audit_node" "DTPT_Truth.v" 745 (Some 714) StShift) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Truth.v:767" "audit_node" "DTPT_Truth.v" 767 (None) StAmbiguous) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Truth.v:781" "audit_node" "DTPT_Truth.v" 781 (None) StAmbiguous) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Truth.v:792" "audit_node_mono" "DTPT_Truth.v" 792 (Some 761) StShift) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Truth.v:804" "audit_node_mono" "DTPT_Truth.v" 804 (Some 761) StShift) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Truth.v:814" "audit_node_cast" "DTPT_Truth.v" 814 (Some 783) StShift) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Truth.v:822" "audit_node_cast" "DTPT_Truth.v" 822 (Some 783) StShift) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Truth.v:832" "audit_gate_level_combo" "DTPT_Truth.v" 832 (Some 807) StShift) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Truth.v:848" "audit_gate_level_combo" "DTPT_Truth.v" 848 (Some 807) StShift) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Extract.v:20–23" "audit_bridge_iff" "DTPT_Extract.v" 20 (Some 20) StHit) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Truth.v:619" "audit_bridge_iff" "DTPT_Truth.v" 619 (Some 797) StShift) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Truth.v:633" "audit_bridge_iff" "DTPT_Truth.v" 633 (Some 797) StShift) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Truth.v:1041" "ev_eqb" "DTPT_Truth.v" 1041 (None) StAmbiguous) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Truth.v:1054" "ev_eqb" "DTPT_Truth.v" 1054 (None) StAmbiguous) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Truth.v:1119" "ev_eqb" "DTPT_Truth.v" 1119 (None) StAmbiguous) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Truth.v:1134" "ev_case_set" "DTPT_Truth.v" 1134 (Some 1361) StShift) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Truth.v:1319" "ev_case_set" "DTPT_Truth.v" 1319 (Some 1361) StShift) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Truth.v:1367" "ev_case_set" "DTPT_Truth.v" 1367 (Some 1361) StShift) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Truth.v:278" "tarski" "DTPT_Truth.v" 278 (Some 192) StShift) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Truth.v:304" "no_uniform_truth" "DTPT_Truth.v" 304 (Some 243) StShift) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Truth.v:413" "layered_network_liar_each_layer" "DTPT_Truth.v" 413 (Some 355) StShift) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Truth.v:429" "level_confusion_revives_liar" "DTPT_Truth.v" 429 (Some 374) StShift) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Truth.v:256–263" "" "DTPT_Truth.v" 256 (Some 170) StShift) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Extract.v:61–178" "vm_compute" "DTPT_Extract.v" 61 (Some 61) StHit) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT.v:890" "" "DTPT.v" 890 (Some 857) StShift) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Entropy.v:862" "" "DTPT_Entropy.v" 862 (Some 837) StShift) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Rotation.v:1550" "" "DTPT_Rotation.v" 1550 (Some 1369) StShift) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Bridge_Rot.v:166" "phase_dev_spec_set" "DTPT_Bridge_Rot.v" 166 (Some 110) StShift) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Truth.v:801" "level_le_total" "DTPT_Truth.v" 801 (Some 460) StShift) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Truth.v:317" "tarski" "DTPT_Truth.v" 317 (Some 231) StShift) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Bridge.v:314" "tarski_set" "DTPT_Bridge.v" 314 (Some 292) StShift) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Bridge_Dig.v:157" "" "DTPT_Bridge_Dig.v" 157 (Some 122) StShift) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Bridge.v:539" "sqsum_app_eq2_set" "DTPT_Bridge.v" 539 (Some 787) StShift) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Bridge.v:192" "sqsum_app_eq2_set" "DTPT_Bridge.v" 192 (Some 787) StShift) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Bridge_Rot.v:293" "collide_app_eq_set" "DTPT_Bridge_Rot.v" 293 (Some 293) StHit) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Extract.v:50–57" "" "DTPT_Extract.v" 50 (Some 34) StShift) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Rotation.v:1893" "align_lambda" "DTPT_Rotation.v" 1893 (Some 1697) StShift) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Entropy.v:2858" "align_lambda_opt" "DTPT_Entropy.v" 2858 (Some 2875) StShift) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Rotation.v:2791" "align_lambda_opt" "DTPT_Rotation.v" 2791 (None) StNotFound) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "L69" "align_lambda_opt" "DTPT_Entropy.v" 69 (None) StNotFound) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT.v:1828" "llm_gate_pass_false_iff" "DTPT.v" 1828 (Some 1724) StShift) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Bridge.v:180" "" "DTPT_Bridge.v" 180 (Some 158) StShift) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Bridge.v:553" "" "DTPT_Bridge.v" 553 (Some 529) StShift) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Bridge.v:166" "" "DTPT_Bridge.v" 166 (Some 166) StHit) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Bridge_Rot.v:96" "" "DTPT_Bridge_Rot.v" 96 (Some 40) StShift) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Bridge_Rot.v:485" "" "DTPT_Bridge_Rot.v" 485 (Some 429) StShift) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Bridge_Rot.v:253" "" "DTPT_Bridge_Rot.v" 253 (Some 197) StShift) (
  cons (mkAnchor "论文21-可编译的治理规则与提取门控" "DTPT_Bridge_Rot.v:319" "" "DTPT_Bridge_Rot.v" 319 (Some 263) StShift) (
  cons (mkAnchor "论文22-从认证代码库从零构建论文的方法论" "UpReqIrrationalCriterion.v:758" "lic_e_irrational_criterion" "UpReqIrrationalCriterion.v" 758 (Some 758) StHit) (
  cons (mkAnchor "论文23-第二定律的构造性定量化" "SecondLawQuantified.v` 定义行 77" "" "SecondLawQuantified.v" 77 (Some 77) StHit) (
  cons (mkAnchor "论文23-第二定律的构造性定量化" "UpReqEntropyDeficitTemp.v` 语句行 482–492" "" "UpReqEntropyDeficitTemp.v" 482 (Some 428) StShift) (
  cons (mkAnchor "论文23-第二定律的构造性定量化" "SecondLawQuantified.v` 语句行 188–194" "" "SecondLawQuantified.v" 188 (Some 95) StShift) (
  cons (mkAnchor "论文23-第二定律的构造性定量化" "SecondLawQuantified.v` 语句行 252–262" "" "SecondLawQuantified.v" 252 (Some 159) StShift) (
  cons (mkAnchor "论文23-第二定律的构造性定量化" "SecondLawQuantified.v` 定义行 77–89" "slq_entropy" "SecondLawQuantified.v" 77 (Some 77) StHit) (
  cons (mkAnchor "论文23-第二定律的构造性定量化" "SecondLawQuantified.v` 语句行 217–223" "slq_entropy_gain_kl_upper" "SecondLawQuantified.v" 217 (Some 217) StHit) (
  cons (mkAnchor "论文24-审计驱动机器检查理论开发" "DTPT_Entropy.v:460" "" "DTPT_Entropy.v" 460 (Some 437) StShift) (
  cons (mkAnchor "论文24-审计驱动机器检查理论开发" "DTPT.v:100" "" "DTPT.v" 100 (Some 67) StShift) (
  cons (mkAnchor "论文24-审计驱动机器检查理论开发" "DTPT_Rotation.v:511" "" "DTPT_Rotation.v" 511 (Some 332) StShift) (
  cons (mkAnchor "论文24-审计驱动机器检查理论开发" "DTPT_Rotation.v:366" "" "DTPT_Rotation.v" 366 (Some 187) StShift) (
  cons (mkAnchor "论文24-审计驱动机器检查理论开发" "DTPT_Entropy.v:143" "" "DTPT_Entropy.v" 143 (Some 120) StShift) (
  cons (mkAnchor "论文24-审计驱动机器检查理论开发" "DTPT_Rotation.v:1005" "" "DTPT_Rotation.v" 1005 (Some 826) StShift) (
  cons (mkAnchor "论文24-审计驱动机器检查理论开发" "DTPT_Entropy.v:1275" "collide" "DTPT_Entropy.v" 1275 (None) StNotFound) (
  cons (mkAnchor "论文24-审计驱动机器检查理论开发" "DTPT_Entropy.v:1918" "collide" "DTPT_Entropy.v" 1918 (Some 1939) StShift) (
  cons (mkAnchor "论文24-审计驱动机器检查理论开发" "DTPT.v:976" "gate_pass" "DTPT.v" 976 (Some 857) StShift) (
  cons (mkAnchor "论文24-审计驱动机器检查理论开发" "DTPT.v:1022" "gate_pass" "DTPT.v" 1022 (Some 857) StShift) (
  cons (mkAnchor "论文24-审计驱动机器检查理论开发" "DTPT.v:873" "gate_pass" "DTPT.v" 873 (Some 857) StShift) (
  cons (mkAnchor "论文24-审计驱动机器检查理论开发" "DTPT_Rotation.v:1484" "phase_dev" "DTPT_Rotation.v" 1484 (None) StAmbiguous) (
  cons (mkAnchor "论文24-审计驱动机器检查理论开发" "DTPT_Truth.v:751" "audit_node_iff" "DTPT_Truth.v" 751 (Some 720) StShift) (
  cons (mkAnchor "论文24-审计驱动机器检查理论开发" "DTPT_Rotation.v:1461" "phase_side" "DTPT_Rotation.v" 1461 (None) StNotFound) (
  cons (mkAnchor "论文24-审计驱动机器检查理论开发" "DTPT_Rotation.v:2502" "phase_classify" "DTPT_Rotation.v" 2502 (None) StNotFound) (
  cons (mkAnchor "论文24-审计驱动机器检查理论开发" "DTPT_Rotation.v:2248" "phase_classify" "DTPT_Rotation.v" 2248 (None) StAmbiguous) (
  cons (mkAnchor "论文24-审计驱动机器检查理论开发" "DTPT_Rotation.v:2445" "" "DTPT_Rotation.v" 2445 (Some 2264) StShift) (
  cons (mkAnchor "论文24-审计驱动机器检查理论开发" "DTPT.v:100–101" "" "DTPT.v" 100 (Some 67) StShift) (
  cons (mkAnchor "论文24-审计驱动机器检查理论开发" "DTPT_Rotation.v:549" "" "DTPT_Rotation.v" 549 (Some 370) StShift) (
  cons (mkAnchor "论文24-审计驱动机器检查理论开发" "DTPT_Bridge_Rot.v:120" "" "DTPT_Bridge_Rot.v" 120 (Some 64) StShift) (
  cons (mkAnchor "论文24-审计驱动机器检查理论开发" "DTPT_Rotation.v:2526" "rotc_supersedes_rot_id" "DTPT_Rotation.v" 2526 (Some 2345) StShift) (
  cons (mkAnchor "论文24-审计驱动机器检查理论开发" "DTPT_Rotation.v:2515–2625" "rotc_supersedes_rot_id" "DTPT_Rotation.v" 2515 (None) StAmbiguous) (
  cons (mkAnchor "论文24-审计驱动机器检查理论开发" "DTPT_Rotation.v:2675" "rotc_supersedes_rot_id" "DTPT_Rotation.v" 2675 (Some 2854) StShift) (
  cons (mkAnchor "论文24-审计驱动机器检查理论开发" "DTPT_Rotation.v:508–509" "" "DTPT_Rotation.v" 508 (Some 329) StShift) (
  cons (mkAnchor "论文24-审计驱动机器检查理论开发" "DTPT_Rotation.v:558" "rotc" "DTPT_Rotation.v" 558 (None) StAmbiguous) (
  cons (mkAnchor "论文24-审计驱动机器检查理论开发" "DTPT_Rotation.v:2047" "" "DTPT_Rotation.v" 2047 (Some 1866) StShift) (
  cons (mkAnchor "论文24-审计驱动机器检查理论开发" "DTPT_Rotation.v:1014" "" "DTPT_Rotation.v" 1014 (Some 835) StShift) (
  cons (mkAnchor "论文24-审计驱动机器检查理论开发" "DTPT_Rotation.v:1259" "rotc_periodic" "DTPT_Rotation.v" 1259 (Some 1080) StShift) (
  cons (mkAnchor "论文24-审计驱动机器检查理论开发" "DTPT_Rotation.v:1012" "rotc_add_local" "DTPT_Rotation.v" 1012 (Some 833) StShift) (
  cons (mkAnchor "论文24-审计驱动机器检查理论开发" "DTPT_Rotation.v:1349" "rotc_class_sharp_ub" "DTPT_Rotation.v" 1349 (Some 1170) StShift) (
  cons (mkAnchor "论文24-审计驱动机器检查理论开发" "DTPT_Rotation.v:1431" "rotc_class_sharp_attained" "DTPT_Rotation.v" 1431 (Some 1252) StShift) (
  cons (mkAnchor "论文24-审计驱动机器检查理论开发" "DTPT_Entropy.v:158" "" "DTPT_Entropy.v" 158 (Some 135) StShift) (
  cons (mkAnchor "论文24-审计驱动机器检查理论开发" "DTPT_Entropy.v:2499" "" "DTPT_Entropy.v" 2499 (Some 2474) StShift) (
  cons (mkAnchor "论文24-审计驱动机器检查理论开发" "DTPT_Entropy.v:1254" "" "DTPT_Entropy.v" 1254 (Some 1229) StShift) (
  cons (mkAnchor "论文24-审计驱动机器检查理论开发" "DTPT_Entropy.v:617" "" "DTPT_Entropy.v" 617 (Some 592) StShift) (
  cons (mkAnchor "论文24-审计驱动机器检查理论开发" "DTPT_Entropy.v:2866" "collide_app_mono_false" "DTPT_Entropy.v" 2866 (Some 2853) StShift) (
  cons (mkAnchor "论文24-审计驱动机器检查理论开发" "DTPT_Entropy.v:2878" "collide_app_mono_false" "DTPT_Entropy.v" 2878 (Some 2853) StShift) (
  cons (mkAnchor "论文24-审计驱动机器检查理论开发" "DTPT_Entropy.v:3033" "collide_app_eq" "DTPT_Entropy.v" 3033 (Some 3050) StShift) (
  cons (mkAnchor "论文24-审计驱动机器检查理论开发" "DTPT_Truth.v:1227" "ev_eqb_leibniz_gap" "DTPT_Truth.v" 1227 (Some 1140) StShift) (
  cons (mkAnchor "论文24-审计驱动机器检查理论开发" "DTPT_Truth.v:1119" "ev_eqb_true_iff" "DTPT_Truth.v" 1119 (Some 1125) StShift) (
  cons (mkAnchor "论文24-审计驱动机器检查理论开发" "DTPT_Entropy.v:868" "gate_low_entropy_false_le" "DTPT_Entropy.v" 868 (Some 843) StShift) (
  cons (mkAnchor "论文24-审计驱动机器检查理论开发" "DTPT.v:993" "" "DTPT.v" 993 (Some 960) StShift) (
  cons (mkAnchor "论文24-审计驱动机器检查理论开发" "DTPT.v:1039" "" "DTPT.v" 1039 (Some 1006) StShift) (
  cons (mkAnchor "论文24-审计驱动机器检查理论开发" "DTPT.v:1048" "" "DTPT.v" 1048 (Some 1015) StShift) (
  cons (mkAnchor "论文24-审计驱动机器检查理论开发" "DTPT_Rotation.v:304" "" "DTPT_Rotation.v" 304 (Some 125) StShift) (
  cons (mkAnchor "论文24-审计驱动机器检查理论开发" "DTPT_Extract.v:61" "u12_gate_pass_t1_h0" "DTPT_Extract.v" 61 (Some 45) StShift) (
  cons (mkAnchor "论文24-审计驱动机器检查理论开发" "DTPT_Extract.v:146–155" "u12_gate_pass_t1_h0" "DTPT_Extract.v" 146 (Some 45) StShift) (
  cons (mkAnchor "论文25-自由能核与注意力Gibbs桥" "UpAblLeEqCompat.v:62" "lec_eq_le" "UpAblLeEqCompat.v" 62 (Some 38) StShift) (
  cons (mkAnchor "论文25-自由能核与注意力Gibbs桥" "S04_RealExpLogConv.v:2066" "base_loss" "S04_RealExpLogConv.v" 2066 (None) StAmbiguous) (
  cons (mkAnchor "论文25-自由能核与注意力Gibbs桥" "UpAblDistLogEq.v:100" "ydle_dist_log_eq_linear" "UpAblDistLogEq.v" 100 (Some 82) StShift) (
  cons (mkAnchor "论文25-自由能核与注意力Gibbs桥" "UpReqDist.v:1063" "ydle_dist_log_eq_linear" "UpReqDist.v" 1063 (Some 1063) StHit) (
  cons (mkAnchor "论文25-自由能核与注意力Gibbs桥" "UpAblDistLogLe.v:130" "ydll_lpo_barrier" "UpAblDistLogLe.v" 130 (Some 129) StShift) (
  cons (mkAnchor "论文25-自由能核与注意力Gibbs桥" "UpReqFEPAttn.v:137" "req_fep_partition_condition" "UpReqFEPAttn.v" 137 (Some 149) StShift) (
  cons (mkAnchor "论文25-自由能核与注意力Gibbs桥" "UpReqFEPAttn.v:381" "req_fep_partition_condition_logz" "UpReqFEPAttn.v" 381 (Some 451) StShift) (
  cons (mkAnchor "论文25-自由能核与注意力Gibbs桥" "UpReqAttnUniformLimit.v:1416" "alm_uniform" "UpReqAttnUniformLimit.v" 1416 (Some 1435) StShift) (
  cons (mkAnchor "论文25-自由能核与注意力Gibbs桥" "AttnDoeblin.v:693" "bs_minorization" "AttnDoeblin.v" 693 (Some 693) StHit) (
  cons (mkAnchor "论文25-自由能核与注意力Gibbs桥" "AttnDoeblin.v:332" "u_tv_contraction" "AttnDoeblin.v" 332 (Some 332) StHit) (
  cons (mkAnchor "论文25-自由能核与注意力Gibbs桥" "S04_RealExpLogConv.v:3371" "p2fl_le_native_direct" "S04_RealExpLogConv.v" 3371 (Some 3371) StHit) (
  cons (mkAnchor "论文25-自由能核与注意力Gibbs桥" "S06_DiffSamplingGibbs.v:3231" "p2fl_le_native_direct" "S06_DiffSamplingGibbs.v" 3231 (Some 3231) StHit) (
  cons (mkAnchor "论文25-自由能核与注意力Gibbs桥" "UpReqFEPAttn.v:76-106" "p2fl_le_native_direct" "UpReqFEPAttn.v" 76 (Some 76) StHit) (
  cons (mkAnchor "论文25-自由能核与注意力Gibbs桥" "S08_RealMainlineDPO.v:2090-2094" "real_steady_state_boltzmann_attn" "S08_RealMainlineDPO.v" 2090 (Some 2120) StShift) (
  cons (mkAnchor "论文25-自由能核与注意力Gibbs桥" "UpAblP2FeedSum.v:77" "p2f_id_real_eq" "UpAblP2FeedSum.v" 77 (Some 47) StShift) (
  cons (mkAnchor "论文25-自由能核与注意力Gibbs桥" "S08:2119" "real_steady_state_boltzmann_attn" "S08_RealMainlineDPO.v" 2119 (Some 2120) StShift) (
  cons (mkAnchor "论文8-构造性无理数纲领" "UpReqIrrationalCriterion.v:26" "" "UpReqIrrationalCriterion.v" 26 (Some 25) StShift) (
  cons (mkAnchor "论文8-构造性无理数纲领" "order.txt:2" "" "order.txt" 2 (Some 2) StHit) (
  cons (mkAnchor "论文8-构造性无理数纲领" "order.txt:265" "" "order.txt" 265 (Some 265) StHit) (
  cons (mkAnchor "论文8-构造性无理数纲领" "UpReqIrrationalCriterion.v:758" "lic_e_irrational_criterion" "UpReqIrrationalCriterion.v" 758 (Some 758) StHit) (
  cons (mkAnchor "论文8-构造性无理数纲领" "order.txt:226" "lic_e_irrational_criterion" "order.txt" 226 (Some 226) StHit) (
  cons (mkAnchor "论文8-构造性无理数纲领" "L747" "lic_e_irrational_criterion" "UpReqIrrationalCriterion.v" 747 (Some 758) StShift) (
  cons (mkAnchor "论文8-构造性无理数纲领" "L58" "lic_tail_e" "SumInvFactEscape.v" 58 (Some 58) StHit) (
  cons (mkAnchor "论文8-构造性无理数纲领" "UpReqIrrationalInstances.v:1301" "ir2_sqrt2_irrational_criterion" "UpReqIrrationalInstances.v" 1301 (Some 1301) StHit) (
  cons (mkAnchor "论文8-构造性无理数纲领" "L1286" "ir2_x1" "UpReqIrrationalInstances.v" 1286 (Some 1290) StShift) (
  cons (mkAnchor "论文8-构造性无理数纲领" "UpReqSqrt3Irrational.v:1102" "is3_sqrt3_irrational_criterion" "UpReqSqrt3Irrational.v" 1102 (Some 1102) StHit) (
  cons (mkAnchor "论文8-构造性无理数纲领" "Ln2Bridge.v:633" "ln2i_x" "Ln2Bridge.v" 633 (Some 584) StShift) (
  cons (mkAnchor "论文8-构造性无理数纲领" "L64" "ln2i_p2_succ" "UpReqLn2Irrational.v" 64 (Some 74) StShift) (
  cons (mkAnchor "论文8-构造性无理数纲领" "L58" "lic_qltt_comp_r" "UpReqIrrationalCriterion.v" 58 (Some 68) StShift) (
  cons (mkAnchor "论文8-构造性无理数纲领" "order.txt:311" "lic_qltt_comp_r" "order.txt" 311 (Some 311) StHit) (
  cons (mkAnchor "论文8-构造性无理数纲领" "order.txt:315" "lic_qltt_comp_r" "order.txt" 315 (Some 315) StHit) (
  cons (mkAnchor "论文8-构造性无理数纲领" "order.txt:470" "lic_qltt_comp_r" "order.txt" 470 (Some 470) StHit) (
  cons (mkAnchor "论文8-构造性无理数纲领" "Ln2Escape.v:559-563" "" "Ln2Escape.v" 559 (Some 561) StShift) (
  cons (mkAnchor "论文8-构造性无理数纲领" "order.txt:314" "" "order.txt" 314 (Some 314) StHit) (
  cons (mkAnchor "论文8-构造性无理数纲领" "Ln2Bridge.v:608" "ln2b_escape_of_supply" "Ln2Bridge.v" 608 (Some 608) StHit) (
  cons (mkAnchor "论文8-构造性无理数纲领" "SupplyAssembly.v:225" "sa_supply_assemble" "SupplyAssembly.v" 225 (Some 225) StHit) (
  cons (mkAnchor "论文8-构造性无理数纲领" "order.txt:332" "sa_supply_assemble" "order.txt" 332 (Some 332) StHit) (
  cons (mkAnchor "论文8-构造性无理数纲领" "order.txt:469" "sa_supply_assemble" "order.txt" 469 (Some 469) StHit) (
  cons (mkAnchor "论文8-构造性无理数纲领" "order.txt:598" "sa_supply_assemble" "order.txt" 598 (Some 598) StHit) (
  cons (mkAnchor "论文8-构造性无理数纲领" "UpReqPadeExp.v:123" "pade_den_sym" "UpReqPadeExp.v" 123 (Some 139) StShift) (
  cons (mkAnchor "论文8-构造性无理数纲领" "order.txt:148" "pade_den_sym" "order.txt" 148 (Some 148) StHit) (
  cons (mkAnchor "论文8-构造性无理数纲领" "UpReqPadeDenPos.v:503" "" "UpReqPadeDenPos.v" 503 (Some 513) StShift) (
  cons (mkAnchor "论文8-构造性无理数纲领" "order.txt:164" "" "order.txt" 164 (Some 164) StHit) (
  cons (mkAnchor "论文8-构造性无理数纲领" "order.txt:324" "" "order.txt" 324 (Some 324) StHit) (
  cons (mkAnchor "论文8-构造性无理数纲领" "BeukersIdentity.v:38" "bi_norm_factor" "BeukersIdentity.v" 38 (Some 62) StShift) (
  cons (mkAnchor "论文8-构造性无理数纲领" "order.txt:472" "bi_norm_factor" "order.txt" 472 (Some 472) StHit) (
  cons (mkAnchor "论文8-构造性无理数纲领" "PsQReindex.v:68" "" "PsQReindex.v" 68 (Some 39) StShift) (
  cons (mkAnchor "论文8-构造性无理数纲领" "order.txt:474" "" "order.txt" 474 (Some 474) StHit) (
  cons (mkAnchor "论文8-构造性无理数纲领" "TrueNumerator.v:129" "tn_x" "TrueNumerator.v" 129 (Some 129) StHit) (
  cons (mkAnchor "论文8-构造性无理数纲领" "order.txt:477" "tn_x" "order.txt" 477 (Some 477) StHit) (
  cons (mkAnchor "论文8-构造性无理数纲领" "RealIdentity.v:35" "ri_upper_transfer" "RealIdentity.v" 35 (Some 267) StShift) (
  cons (mkAnchor "论文8-构造性无理数纲领" "order.txt:478" "ri_upper_transfer" "order.txt" 478 (Some 478) StHit) (
  cons (mkAnchor "论文8-构造性无理数纲领" "order.txt:473" "ri_upper_transfer" "order.txt" 473 (Some 473) StHit) (
  cons (mkAnchor "论文8-构造性无理数纲领" "order.txt:476" "ri_upper_transfer" "order.txt" 476 (Some 476) StHit) (
  cons (mkAnchor "论文8-构造性无理数纲领" "order.txt:479" "ri_upper_transfer" "order.txt" 479 (Some 479) StHit) (
  cons (mkAnchor "论文8-构造性无理数纲领" "order.txt:621" "ri_upper_transfer" "order.txt" 621 (Some 621) StHit) (
  cons (mkAnchor "论文8-构造性无理数纲领" "order.txt:475" "ri_upper_transfer" "order.txt" 475 (Some 475) StHit) (
  cons (mkAnchor "论文8-构造性无理数纲领" "order.txt:331" "ri_upper_transfer" "order.txt" 331 (Some 331) StHit) (
  cons (mkAnchor "论文8-构造性无理数纲领" "order.txt:660" "ri_upper_transfer" "order.txt" 660 (Some 640) StShift) (
  cons (mkAnchor "论文8-构造性无理数纲领" "SupplyAssembly.v:219" "sa_supply_rem" "SupplyAssembly.v" 219 (Some 219) StHit) (
  cons (mkAnchor "论文8-构造性无理数纲领" "S11_TP3B5.v:1387" "channel_f1" "S11_TP3B5.v" 1387 (Some 1387) StHit) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "UpReqIrrationalCriterion.v:285" "real_lt" "UpReqIrrationalCriterion.v" 285 (None) StAmbiguous) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "L40" "real_le" "S07_RealSetoidExpLog.v" 40 (Some 121) StShift) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "UpReqIrrationalCriterion.v:242" "" "UpReqIrrationalCriterion.v" 242 (Some 241) StShift) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "order.txt:265" "" "order.txt" 265 (Some 265) StHit) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "Ln2Bridge.v:63" "" "Ln2Bridge.v" 63 (Some 14) StShift) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "order.txt:470" "" "order.txt" 470 (Some 470) StHit) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "S10_KVQuantTrig.v:2976" "" "S10_KVQuantTrig.v" 2976 (Some 2983) StShift) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "order.txt:10" "" "order.txt" 10 (Some 10) StHit) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "S10_KVQuantTrig.v:3036" "" "S10_KVQuantTrig.v" 3036 (Some 3043) StShift) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "S10_KVQuantTrig.v:2693-2703" "lp_odd" "S10_KVQuantTrig.v" 2693 (Some 2700) StShift) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "S10_KVQuantTrig.v:2693" "" "S10_KVQuantTrig.v" 2693 (Some 2700) StShift) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "S10_KVQuantTrig.v:2695" "" "S10_KVQuantTrig.v" 2695 (Some 2702) StShift) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "S10_KVQuantTrig.v:2697" "" "S10_KVQuantTrig.v" 2697 (Some 2704) StShift) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "S10_KVQuantTrig.v:2703" "" "S10_KVQuantTrig.v" 2703 (Some 2710) StShift) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "L3036" "" "S10_KVQuantTrig.v" 3036 (Some 3043) StShift) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "L8807" "" "S10_KVQuantTrig.v" 8807 (Some 8814) StShift) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "S10_KVQuantTrig.v:8807" "" "S10_KVQuantTrig.v" 8807 (Some 8814) StShift) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "S10_KVQuantTrig.v:3043" "" "S10_KVQuantTrig.v" 3043 (Some 3050) StShift) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "PiEnvelope.v:913" "" "PiEnvelope.v" 913 (Some 928) StShift) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "order.txt:245" "" "order.txt" 245 (Some 245) StHit) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "PiEnvelope.v:922" "" "PiEnvelope.v" 922 (Some 937) StShift) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "PiEnvelope.v:931" "" "PiEnvelope.v" 931 (Some 946) StShift) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "S10_KVQuantTrig.v:8118-8120" "" "S10_KVQuantTrig.v" 8118 (Some 8125) StShift) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "S10_KVQuantTrig.v:8394-8396" "" "S10_KVQuantTrig.v" 8394 (Some 8401) StShift) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "S10_KVQuantTrig.v:8403-8404" "log_eps" "S10_KVQuantTrig.v" 8403 (None) StAmbiguous) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "S10_KVQuantTrig.v:8543" "" "S10_KVQuantTrig.v" 8543 (Some 8550) StShift) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "S10_KVQuantTrig.v:7982" "" "S10_KVQuantTrig.v" 7982 (Some 7989) StShift) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "S10_KVQuantTrig.v:8610" "" "S10_KVQuantTrig.v" 8610 (Some 8617) StShift) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "S10_KVQuantTrig.v:9459" "" "S10_KVQuantTrig.v" 9459 (Some 9466) StShift) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "S10_KVQuantTrig.v:8425" "" "S10_KVQuantTrig.v" 8425 (Some 8432) StShift) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "S10_KVQuantTrig.v:8555-8558" "" "S10_KVQuantTrig.v" 8555 (Some 8562) StShift) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "S10_KVQuantTrig.v:9386" "" "S10_KVQuantTrig.v" 9386 (Some 9393) StShift) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "L76" "" "S11_TP3B5.v" 76 (Some 73) StShift) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "S11_TP3B5.v:1092" "" "S11_TP3B5.v" 1092 (Some 1088) StShift) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "order.txt:11" "" "order.txt" 11 (Some 11) StHit) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "S11_TP3B5.v:1095" "" "S11_TP3B5.v" 1095 (Some 1091) StShift) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "S11_TP3B5.v:1276-1277" "" "S11_TP3B5.v" 1276 (Some 1272) StShift) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "S11_TP3B5.v:1552" "a3_diag_abs" "S11_TP3B5.v" 1552 (Some 1552) StHit) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "S11_TP3B5.v:1387" "channel_f1" "S11_TP3B5.v" 1387 (Some 1387) StHit) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "L1315" "channel_w_eq_cos_pi_half" "S11_TP3B5.v" 1315 (Some 1370) StShift) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "S11_TP3B5.v:1370" "channel_w_eq_cos_pi_half" "S11_TP3B5.v" 1370 (Some 1370) StHit) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "S10:9770" "" "S10_KVQuantTrig.v" 9770 (Some 9777) StShift) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "S11:1277" "" "S11_TP3B5.v" 1277 (Some 1273) StShift) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "S10_KVQuantTrig.v:9770" "" "S10_KVQuantTrig.v" 9770 (Some 9777) StShift) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "S11_TP3B5.v:37" "w_leib" "S11_TP3B5.v" 37 (None) StNotFound) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "S11_TP3B5.v:1356" "" "S11_TP3B5.v" 1356 (Some 1352) StShift) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "S11_TP3B5.v:1362" "" "S11_TP3B5.v" 1362 (Some 1358) StShift) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "S11_TP3B5.v:1349" "" "S11_TP3B5.v" 1349 (Some 1345) StShift) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "S11_TP3B5.v:1332" "" "S11_TP3B5.v" 1332 (Some 1328) StShift) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "S11_TP3B5.v:1308" "" "S11_TP3B5.v" 1308 (Some 1304) StShift) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "S10:9459" "channel_w_lower" "S10_KVQuantTrig.v" 9459 (Some 9459) StHit) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "S11_TP3B5.v:1378" "" "S11_TP3B5.v" 1378 (Some 1374) StShift) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "S11_TP3B5.v:1577" "" "S11_TP3B5.v" 1577 (Some 1573) StShift) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "S14_B5BatchBlock.v:14141" "qd_hsc_a3" "S14_B5BatchBlock.v" 14141 (Some 14141) StHit) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "QuickDischargeA.v:106" "qd_hsc_a3" "QuickDischargeA.v" 106 (Some 109) StShift) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "S14:13966" "qd_hsc_a3" "S14_B5BatchBlock.v" 13966 (Some 13966) StHit) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "S14:14125" "qd_hsc_a3" "S14_B5BatchBlock.v" 14125 (Some 14125) StHit) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "order.txt:339" "" "order.txt" 339 (Some 339) StHit) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "order.txt:14" "" "order.txt" 14 (Some 14) StHit) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "S11_TP3B5.v:1402" "" "S11_TP3B5.v" 1402 (Some 1398) StShift) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "S11_TP3B5.v:1411" "" "S11_TP3B5.v" 1411 (Some 1407) StShift) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "S11:1577" "a3_h4_value_bridge" "S11_TP3B5.v" 1577 (Some 1577) StHit) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "S11:1552" "a3_diag_abs" "S11_TP3B5.v" 1552 (Some 1552) StHit) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "S11:1387" "channel_f1" "S11_TP3B5.v" 1387 (Some 1387) StHit) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "S11:1370" "channel_w_eq_cos_pi_half" "S11_TP3B5.v" 1370 (Some 1370) StHit) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "S10:8555" "cos_eq_zero_diag_bound" "S10_KVQuantTrig.v" 8555 (Some 8555) StHit) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "S10:8610" "cos_pi_half_unique" "S10_KVQuantTrig.v" 8610 (Some 8610) StHit) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "PiEnvelope.v:41–46" "cos_zero_seq" "PiEnvelope.v" 41 (Some 41) StHit) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "S12_B5RecycleSF.v:8386" "cos_zero_seq" "S12_B5RecycleSF.v" 8386 (Some 8386) StHit) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "S10:2976" "cos_zero_seq" "S10_KVQuantTrig.v" 2976 (None) StAmbiguous) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "S10:8403" "cos_zero_seq" "S10_KVQuantTrig.v" 8403 (None) StAmbiguous) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "S10:8543" "cos_zero_seq" "S10_KVQuantTrig.v" 8543 (None) StAmbiguous) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "PiEnvelope.v:704" "" "PiEnvelope.v" 704 (Some 719) StShift) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "PiEnvelope.v:721" "real_pi_leibniz_proj" "PiEnvelope.v" 721 (Some 721) StHit) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "S10:3036" "real_pi_leibniz_proj" "S10_KVQuantTrig.v" 3036 (Some 3036) StHit) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "PiEnvelope.v:823" "" "PiEnvelope.v" 823 (Some 838) StShift) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "PiEnvelope.v:77" "" "PiEnvelope.v" 77 (Some 92) StShift) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "PiEnvelope.v:81" "" "PiEnvelope.v" 81 (Some 96) StShift) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "PiEnvelope.v:88" "" "PiEnvelope.v" 88 (Some 103) StShift) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "S10:2693" "lp_odd" "S10_KVQuantTrig.v" 2693 (Some 2700) StShift) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "UpReqConstEnvelope.v:19–20" "" "UpReqConstEnvelope.v" 19 (Some 19) StHit) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "order.txt:283" "" "order.txt" 283 (Some 283) StHit) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "UpAblAbsQFeedB2.v:75–76" "" "UpAblAbsQFeedB2.v" 75 (Some 96) StShift) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "order.txt:547" "" "order.txt" 547 (Some 547) StHit) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "S12_B5RecycleSF.v:8374–8390" "b5q_pi_to_four_theta" "S12_B5RecycleSF.v" 8374 (Some 8376) StShift) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "UpReqLn2Irrational.v:360" "lic_escape_window" "UpReqLn2Irrational.v" 360 (Some 360) StHit) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "UpReqSqrt3Irrational.v:915" "lic_escape_window" "UpReqSqrt3Irrational.v" 915 (Some 754) StShift) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "order.txt:660" "lic_escape_window" "order.txt" 660 (Some 640) StShift) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "UpReqPaperAnchor.v:35-42" "" "UpReqPaperAnchor.v" 35 (Some 35) StHit) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "UpReqPaperAnchor.v:80-84" "" "UpReqPaperAnchor.v" 80 (Some 74) StShift) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "S10:8807" "real_eq" "S10_KVQuantTrig.v" 8807 (Some 8953) StShift) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "S10:7982" "real_eq" "S10_KVQuantTrig.v" 7982 (Some 8425) StShift) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "S14:14141" "" "S14_B5BatchBlock.v" 14141 (Some 14139) StShift) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "L1" "" "Rtrigo_def.v" 1 (None) StNotFound) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "L2" "" "Rtrigo_def.v" 2 (None) StNotFound) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "L3" "" "Rtrigo_def.v" 3 (None) StNotFound) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "L4" "" "Rtrigo_def.v" 4 (None) StNotFound) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "L5" "" "Rtrigo_def.v" 5 (None) StNotFound) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "S11:37" "w_leib" "S11_TP3B5.v" 37 (None) StNotFound) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "S14_B5BatchBlock.v:14141-14148" "" "S14_B5BatchBlock.v" 14141 (Some 14139) StShift) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "S14_B5BatchBlock.v:14156-14161" "" "S14_B5BatchBlock.v" 14156 (Some 14154) StShift) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "S11_TP3B5.v:1552-1571" "a3_diag_abs" "S11_TP3B5.v" 1552 (Some 1552) StHit) (
  cons (mkAnchor "论文9-π的构造性三表示定理" "S11_TP3B5.v:1542-1549" "a3_ptw_bound" "S11_TP3B5.v" 1542 (Some 1542) StHit) (
  nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

(* Verdict census: per-status counting (all-Defined recursion, non-trivial *)
(* implementation; the prelude has no list notations, so bare nil/cons      *)
(* patterns are used). *)
Fixpoint count_status (s : AnchorStatus) (l : list AnchorEntry) : nat :=
  match l with
  | nil => 0
  | cons e t =>
      match ae_status e, s with
      | StHit, StHit => S (count_status s t)
      | StShift, StShift => S (count_status s t)
      | StAmbiguous, StAmbiguous => S (count_status s t)
      | StNotFound, StNotFound => S (count_status s t)
      | StDeadFile, StDeadFile => S (count_status s t)
      | _, _ => count_status s t
      end
  end.

(* Retrieval by target file (string equality via String.eqb). *)
Fixpoint anchors_of_file (f : string) (l : list AnchorEntry) : list AnchorEntry :=
  match l with
  | nil => nil
  | cons e t =>
      if String.eqb (ae_file e) f
      then cons e (anchors_of_file f t)
      else anchors_of_file f t
  end.

(* Self-consistency census: sum of the five per-status counts equals the   *)
(* total length (a target-side Compute should yield true). *)
Definition census_sum (l : list AnchorEntry) : nat :=
  count_status StHit l + count_status StShift l + count_status StAmbiguous l +
  count_status StNotFound l + count_status StDeadFile l.

Fixpoint reg_length (l : list AnchorEntry) : nat :=
  match l with
  | nil => 0
  | cons _ t => S (reg_length t)
  end.

Definition registry_selfconsistent : bool :=
  Nat.eqb (census_sum registry) (reg_length registry).

Definition registry_total : nat := reg_length registry.

(* Extraction self-check is not inside this file: see the isolated-pool    *)
(* probe file probe_extract.v (Require this file + Extraction plugin;      *)
(* verifies Obj.magic=0 for the extractability requirement). Keeps the     *)
(* deliverable dependency surface minimal. *)
