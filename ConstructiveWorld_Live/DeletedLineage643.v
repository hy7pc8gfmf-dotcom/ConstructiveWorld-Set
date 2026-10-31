(* ===================================================================== *)
(* DeletedLineage643.v — K2 deleted-file lineage registry                 *)
(* (self-contained standalone data module)                                *)
(*                                                                        *)
(* Mission. Register the four-way disposition data of the 216 top-level   *)
(*   declarations of the 48 deleted files (unique host / multiple hosts / *)
(*   truly gone / renamed), with host file names and host line numbers,   *)
(*   plus per-entry census / retrieval / self-consistency functions,      *)
(*   for target-side Require or excerpting.                               *)
(* Dependencies. Zero tree Require; only one standard-library module,     *)
(*   Stdlib.Strings.String (the Rocq 9.1 prelude does not preload string, *)
(*   which is required to host readable registry data); list / nat /      *)
(*   bool / option all come from the prelude.                             *)
(* References. Predecessor base tree 691 .v files -> current live tree    *)
(*   643 .v files; the baseline numbers are authoritative in the in-file  *)
(*   lineage_baseline field.                                              *)
(* Constructivity. Pure Set-layer data plus fully transparent functions;  *)
(*   axiom-free at the statement level, no Prop statements.               *)
(* Build. Standalone compile: rocq c -native-compiler no -q               *)
(*   DeletedLineage643.v (zero tree dependencies; embeddable in any       *)
(*   target pool). Extraction self-check lives outside this file: an      *)
(*   isolated-pool probe file (Require this file + Extraction plugin)     *)
(*   verifies Obj.magic = 0.                                              *)
(* ===================================================================== *)

From Stdlib.Strings Require Import String.

Inductive DLStatus : Set :=
  | DlMappedUnique : DLStatus   (* exactly one definition site in the live tree *)
  | DlMappedMulti : DLStatus    (* two or more definition sites in the live tree *)
  | DlGone : DLStatus           (* truly gone = hard failure surface on the paper side *)
  | DlRenamed : DLStatus.       (* renamed, per strong evidence from the statement body *)

Definition DLStatus_eqb (a b : DLStatus) : bool :=
  match a, b with
  | DlMappedUnique, DlMappedUnique => true
  | DlMappedMulti, DlMappedMulti => true
  | DlGone, DlGone => true
  | DlRenamed, DlRenamed => true
  | _, _ => false
end.

Record DLDecl : Set := mkDL {
  dld_module : string;      (* deleted file it belongs to (with .v stripped) *)
  dld_name : string;        (* declaration name *)
  dld_kind : string;        (* declaration kind Theorem/Lemma/Definition/... *)
  dld_r134_line : nat;      (* predecessor-tree line number *)
  dld_status : DLStatus;
  dld_host : string;        (* first host file (empty string when GONE) *)
  dld_host_line : option nat; (* first host line number *)
  dld_nhosts : nat          (* number of host files (0 when GONE) *)
}.

Record DLModule : Set := mkM {
  dlm_module : string;
  dlm_wave : string;        (* migration interval: #144->#146 / #146->643 *)
  dlm_r134_lines : nat;
  dlm_decl_count : nat;
  dlm_disposition : string  (* disposition note (zero-declaration items registered here) *)
}.

Definition lineage_baseline : string :=
  "R134=691v -> Live=643v; delta=48; md5 c7ac7a1991ccf9801b4f74240327408a".

Definition lineage_version : string := "20260927-643".

(* ---- Module register (48 entries) ---- *)
Definition modules_registry : list DLModule :=
  cons (mkM "CW_ConstructiveWorld_219" "#144->#146" 16 0 "zero_decl_shell; Export=S01-S15; R134 consumers 471 files 499 lines (stripped) -> Live 0; S01-S15 all alive") (
  cons (mkM "EngineCeilingK" "#146->643" 231 14 "declarative; dominant hosts: UpReqEngineCeiling.v") (
  cons (mkM "EpsTrichotomy" "#146->643" 307 12 "declarative; dominant hosts: UpReqEngineCeiling.v") (
  cons (mkM "Paper12345Sample" "#146->643" 154 10 "declarative; dominant hosts: ToyR_Paper12345Sample.v") (
  cons (mkM "PinskerCoreClose" "#146->643" 355 14 "declarative; dominant hosts: UpReqEngineCeiling.v") (
  cons (mkM "ToyR_fka_weak_triangle_ref" "#144->#146" 42 1 "declarative; dominant hosts: fka_weak_triangle_ref.v") (
  cons (mkM "UpAblT9_UpDebtSqrtAbsReq" "#144->#146" 60 2 "declarative; dominant hosts: none") (
  cons (mkM "UpAblT9_UpEntropyGainReq" "#144->#146" 58 2 "declarative; dominant hosts: UpAblMetaWorld3.v") (
  cons (mkM "UpAblT9_UpFirewallReq" "#144->#146" 61 2 "declarative; dominant hosts: none") (
  cons (mkM "UpAblT9_UpReqSumD" "#144->#146" 50 1 "declarative; dominant hosts: none") (
  cons (mkM "UpAblT9_UpSigMigrate2" "#144->#146" 47 1 "declarative; dominant hosts: none") (
  cons (mkM "UpReqCDispersion" "#146->643" 478 23 "declarative; dominant hosts: UpReqEntropyUniqueNeg.v") (
  cons (mkM "UpReqCSB" "#144->#146" 71 1 "declarative; dominant hosts: none") (
  cons (mkM "UpReqELBOEps" "#146->643" 428 8 "declarative; dominant hosts: UpReqMinUniqueTight.v") (
  cons (mkM "UpReqELBOStrict" "#146->643" 406 7 "declarative; dominant hosts: UpReqMinUniqueTight.v") (
  cons (mkM "UpReqELBOTight" "#146->643" 431 7 "declarative; dominant hosts: UpReqMinUniqueTight.v") (
  cons (mkM "UpReqEntropyUniqueTemp" "#146->643" 406 10 "declarative; dominant hosts: UpReqEntropyUniqueNeg.v") (
  cons (mkM "UpReqFEPCanon" "#146->643" 154 2 "declarative; dominant hosts: UpReqMinUniqueTight.v") (
  cons (mkM "UpReqGibbsD" "#146->643" 586 16 "declarative; dominant hosts: G08_Gibbs.v,UpReqGibbsE2.v") (
  cons (mkM "UpReqMinFreeEps" "#146->643" 279 3 "declarative; dominant hosts: UpReqMinUniqueTight.v") (
  cons (mkM "UpReqMisc5" "#146->643" 1091 63 "declarative; dominant hosts: UpReqMisc5B.v,UpReqRDF.v") (
  cons (mkM "ali_g3_absleid" "#144->#146" 8 0 "zero_decl_probe; at_witness alive 0/0") (
  cons (mkM "eum_g3" "#144->#146" 3 0 "zero_decl_probe; at_witness alive 0/0") (
  cons (mkM "fa51_g3_sumpos" "#144->#146" 4 1 "declarative; dominant hosts: none") (
  cons (mkM "fa52_dpo_witness_g3" "#144->#146" 3 0 "zero_decl_probe; at_witness alive 0/0") (
  cons (mkM "fa52_entropy_diff_unsat_g3" "#144->#146" 3 0 "zero_decl_probe; at_witness alive 0/0") (
  cons (mkM "fa53_compat_abs_g3" "#144->#146" 4 0 "zero_decl_probe; at_witness alive 0/0") (
  cons (mkM "fa56_g3_carrier" "#144->#146" 12 2 "declarative; dominant hosts: none") (
  cons (mkM "fa56_probe_sig" "#144->#146" 9 0 "zero_decl_probe; at_witness alive 0/0") (
  cons (mkM "fa56b_g3" "#144->#146" 19 4 "declarative; dominant hosts: none") (
  cons (mkM "fa56c_g3" "#144->#146" 19 4 "declarative; dominant hosts: none") (
  cons (mkM "fa56c_probe_sig" "#144->#146" 20 0 "zero_decl_probe; at_witness alive 0/0") (
  cons (mkM "fic2_g3" "#144->#146" 6 0 "zero_decl_probe; at_witness alive 0/0") (
  cons (mkM "fic2_g3_ext" "#144->#146" 7 0 "zero_decl_probe; at_witness alive 0/0") (
  cons (mkM "fic_g3" "#144->#146" 3 0 "zero_decl_probe; at_witness alive 0/0") (
  cons (mkM "fic_g3_ext" "#144->#146" 3 0 "zero_decl_probe; at_witness alive 0/0") (
  cons (mkM "g4p_g3" "#144->#146" 5 0 "zero_decl_probe; at_witness alive 0/0") (
  cons (mkM "g4p_probe_sig" "#144->#146" 20 0 "zero_decl_probe; at_witness alive 0/0") (
  cons (mkM "gfe_g3" "#144->#146" 8 0 "zero_decl_probe; at_witness alive 0/0") (
  cons (mkM "ipl_g3" "#144->#146" 5 0 "zero_decl_probe; at_witness alive 0/0") (
  cons (mkM "nlp_g3" "#144->#146" 5 0 "zero_decl_probe; at_witness alive 0/0") (
  cons (mkM "p7a_g3" "#144->#146" 4 0 "zero_decl_probe; at_witness alive 0/0") (
  cons (mkM "pa1_g3" "#144->#146" 3 0 "zero_decl_probe; at_witness alive 0/0") (
  cons (mkM "ppa_g3" "#144->#146" 32 6 "declarative; dominant hosts: none") (
  cons (mkM "r53_g3_absleidreal" "#144->#146" 10 0 "zero_decl_probe; at_witness alive 0/0") (
  cons (mkM "rta_g3" "#144->#146" 4 0 "zero_decl_probe; at_witness alive 0/0") (
  cons (mkM "uac_probe0" "#144->#146" 8 0 "zero_decl_probe; at_witness alive 2/2") (
  cons (mkM "uac_probe1" "#144->#146" 33 0 "zero_decl_probe; at_witness alive 21/21")
  nil))))))))))))))))))))))))))))))))))))))))))))))).

(* ---- Declaration register (216 entries) ---- *)
Definition decls_registry : list DLDecl :=
  cons (mkDL "EngineCeilingK" "eck_z_shift" "Lemma" 51 DlMappedUnique "UpReqEngineCeiling.v" (Some 429) 1) (
  cons (mkDL "EngineCeilingK" "eck_q_pow_neq0" "Lemma" 56 DlMappedUnique "UpReqEngineCeiling.v" (Some 434) 1) (
  cons (mkDL "EngineCeilingK" "eck_gsum" "Fixpoint" 68 DlMappedUnique "UpReqEngineCeiling.v" (Some 446) 1) (
  cons (mkDL "EngineCeilingK" "eck_geom_sum_closed" "Lemma" 75 DlMappedUnique "UpReqEngineCeiling.v" (Some 453) 1) (
  cons (mkDL "EngineCeilingK" "eck_pow_minus_one" "Lemma" 89 DlMappedUnique "UpReqEngineCeiling.v" (Some 467) 1) (
  cons (mkDL "EngineCeilingK" "eck_q_pow_inv" "Lemma" 100 DlMappedUnique "UpReqEngineCeiling.v" (Some 478) 1) (
  cons (mkDL "EngineCeilingK" "eck_r6s_geom" "Lemma" 115 DlMappedUnique "UpReqEngineCeiling.v" (Some 492) 1) (
  cons (mkDL "EngineCeilingK" "eck_r6s_step" "Lemma" 126 DlMappedUnique "UpReqEngineCeiling.v" (Some 503) 1) (
  cons (mkDL "EngineCeilingK" "eck_bcoef_step" "Lemma" 138 DlMappedUnique "UpReqEngineCeiling.v" (Some 515) 1) (
  cons (mkDL "EngineCeilingK" "eck_Wk" "Fixpoint" 150 DlMappedUnique "UpReqEngineCeiling.v" (Some 527) 1) (
  cons (mkDL "EngineCeilingK" "eck_r6_param_k" "Theorem" 165 DlMappedUnique "UpReqEngineCeiling.v" (Some 540) 1) (
  cons (mkDL "EngineCeilingK" "eck_param_sig" "Definition" 182 DlMappedUnique "UpReqEngineCeiling.v" (Some 557) 1) (
  cons (mkDL "EngineCeilingK" "eck_param_pack" "Definition" 189 DlMappedUnique "UpReqEngineCeiling.v" (Some 564) 1) (
  cons (mkDL "EngineCeilingK" "eck_kernel_coef_k" "Theorem" 206 DlMappedUnique "UpReqEngineCeiling.v" (Some 580) 1) (
  cons (mkDL "EpsTrichotomy" "etc_ltT_leT'" "Lemma" 43 DlMappedUnique "UpReqEngineCeiling.v" (Some 612) 1) (
  cons (mkDL "EpsTrichotomy" "etc_qeq_le_r" "Lemma" 58 DlMappedUnique "UpReqEngineCeiling.v" (Some 627) 1) (
  cons (mkDL "EpsTrichotomy" "etc_qeq_lt_r" "Lemma" 81 DlMappedUnique "UpReqEngineCeiling.v" (Some 650) 1) (
  cons (mkDL "EpsTrichotomy" "etc_qabs_zero" "Lemma" 104 DlMappedUnique "UpReqEngineCeiling.v" (Some 673) 1) (
  cons (mkDL "EpsTrichotomy" "etc_eps_half_pos" "Lemma" 123 DlMappedUnique "UpReqEngineCeiling.v" (Some 692) 1) (
  cons (mkDL "EpsTrichotomy" "etc_eps_half_add" "Lemma" 133 DlMappedUnique "UpReqEngineCeiling.v" (Some 702) 1) (
  cons (mkDL "EpsTrichotomy" "etc_trichotomy" "Theorem" 147 DlMappedUnique "UpReqEngineCeiling.v" (Some 716) 1) (
  cons (mkDL "EpsTrichotomy" "etc_apart" "Theorem" 194 DlMappedUnique "UpReqEngineCeiling.v" (Some 763) 1) (
  cons (mkDL "EpsTrichotomy" "etc_compare_tri" "Theorem" 238 DlMappedUnique "UpReqEngineCeiling.v" (Some 806) 1) (
  cons (mkDL "EpsTrichotomy" "etc_sign_tri" "Theorem" 255 DlMappedUnique "UpReqEngineCeiling.v" (Some 823) 1) (
  cons (mkDL "EpsTrichotomy" "etc_one_side" "Theorem" 272 DlMappedUnique "UpReqEngineCeiling.v" (Some 840) 1) (
  cons (mkDL "EpsTrichotomy" "etc_pack" "Definition" 291 DlMappedUnique "UpReqEngineCeiling.v" (Some 859) 1) (
  cons (mkDL "Paper12345Sample" "p12_qpow" "Fixpoint" 43 DlMappedUnique "ToyR_Paper12345Sample.v" (Some 14) 1) (
  cons (mkDL "Paper12345Sample" "p12_s" "Definition" 50 DlMappedUnique "ToyR_Paper12345Sample.v" (Some 21) 1) (
  cons (mkDL "Paper12345Sample" "p12_bcoef" "Definition" 53 DlMappedUnique "ToyR_Paper12345Sample.v" (Some 24) 1) (
  cons (mkDL "Paper12345Sample" "p12_coef" "Definition" 57 DlMappedUnique "ToyR_Paper12345Sample.v" (Some 28) 1) (
  cons (mkDL "Paper12345Sample" "p12_mul_neq0" "Lemma" 62 DlMappedUnique "ToyR_Paper12345Sample.v" (Some 33) 1) (
  cons (mkDL "Paper12345Sample" "p12_div_cancel" "Lemma" 90 DlMappedUnique "ToyR_Paper12345Sample.v" (Some 61) 1) (
  cons (mkDL "Paper12345Sample" "p12_qpow_zero_r" "Lemma" 100 DlMappedUnique "ToyR_Paper12345Sample.v" (Some 71) 1) (
  cons (mkDL "Paper12345Sample" "p12_param_general_k" "Theorem" 110 DlMappedUnique "ToyR_Paper12345Sample.v" (Some 81) 1) (
  cons (mkDL "Paper12345Sample" "p12_param_k1" "Corollary" 140 DlMappedUnique "ToyR_Paper12345Sample.v" (Some 111) 1) (
  cons (mkDL "Paper12345Sample" "p12_coef_fingerprint_one" "Lemma" 151 DlMappedUnique "ToyR_Paper12345Sample.v" (Some 122) 1) (
  cons (mkDL "PinskerCoreClose" "pkc_one_proj" "Lemma" 60 DlMappedUnique "UpReqEngineCeiling.v" (Some 882) 1) (
  cons (mkDL "PinskerCoreClose" "pkc_minus_l_wd" "Lemma" 64 DlMappedUnique "UpReqEngineCeiling.v" (Some 886) 1) (
  cons (mkDL "PinskerCoreClose" "pkc_minus_r_wd" "Lemma" 73 DlMappedUnique "UpReqEngineCeiling.v" (Some 895) 1) (
  cons (mkDL "PinskerCoreClose" "pkc_qeq_lt_l" "Lemma" 83 DlMappedUnique "UpReqEngineCeiling.v" (Some 905) 1) (
  cons (mkDL "PinskerCoreClose" "pkc_half_lt" "Lemma" 107 DlMappedUnique "UpReqEngineCeiling.v" (Some 929) 1) (
  cons (mkDL "PinskerCoreClose" "pkc_sign_load" "Theorem" 141 DlMappedUnique "UpReqEngineCeiling.v" (Some 963) 1) (
  cons (mkDL "PinskerCoreClose" "pkc_half_slack_load" "Theorem" 177 DlMappedUnique "UpReqEngineCeiling.v" (Some 999) 1) (
  cons (mkDL "PinskerCoreClose" "pkc_oneside_far_load" "Theorem" 210 DlMappedUnique "UpReqEngineCeiling.v" (Some 1032) 1) (
  cons (mkDL "PinskerCoreClose" "pkc_oneside_near_load" "Theorem" 244 DlMappedUnique "UpReqEngineCeiling.v" (Some 1066) 1) (
  cons (mkDL "PinskerCoreClose" "pkc_w3_qface" "Theorem" 287 DlMappedUnique "UpReqEngineCeiling.v" (Some 1107) 1) (
  cons (mkDL "PinskerCoreClose" "pkc_pack_sign" "Definition" 314 DlMappedUnique "UpReqEngineCeiling.v" (Some 1134) 1) (
  cons (mkDL "PinskerCoreClose" "pkc_pack_far" "Definition" 318 DlMappedUnique "UpReqEngineCeiling.v" (Some 1138) 1) (
  cons (mkDL "PinskerCoreClose" "pkc_pack_near" "Definition" 322 DlMappedUnique "UpReqEngineCeiling.v" (Some 1142) 1) (
  cons (mkDL "PinskerCoreClose" "pkc_pack_w3" "Definition" 326 DlMappedUnique "UpReqEngineCeiling.v" (Some 1146) 1) (
  cons (mkDL "ToyR_fka_weak_triangle_ref" "fka_weak_triangle_ref" "Theorem" 35 DlMappedUnique "fka_weak_triangle_ref.v" (Some 16) 1) (
  cons (mkDL "UpAblT9_UpDebtSqrtAbsReq" "uabT9_debt_ctxR_premise_le" "Theorem" 41 DlGone "" None 0) (
  cons (mkDL "UpAblT9_UpDebtSqrtAbsReq" "uabT9_debt_ctxRIS_sqrt_witness" "Theorem" 49 DlGone "" None 0) (
  cons (mkDL "UpAblT9_UpEntropyGainReq" "uabT9_eg_ctxR_minus_def" "Theorem" 41 DlGone "" None 0) (
  cons (mkDL "UpAblT9_UpEntropyGainReq" "uabT9_eg_ctxRIS_minus_plus_cancel" "Theorem" 49 DlRenamed "UpAblMetaWorld3.v" (Some 68) 1) (
  cons (mkDL "UpAblT9_UpFirewallReq" "uabT9_fw_ctxR_double_pos" "Theorem" 42 DlGone "" None 0) (
  cons (mkDL "UpAblT9_UpFirewallReq" "uabT9_fw_ctxRIS_lt_double" "Theorem" 50 DlGone "" None 0) (
  cons (mkDL "UpAblT9_UpReqSumD" "uabT9_sumd_ctx_sum_ext_real" "Theorem" 40 DlGone "" None 0) (
  cons (mkDL "UpAblT9_UpSigMigrate2" "uabT9_sigm2_partition_two_state" "Theorem" 39 DlGone "" None 0) (
  cons (mkDL "UpReqCDispersion" "t26_s1_algebra_log_compat" "Theorem" 69 DlMappedUnique "UpReqEntropyUniqueNeg.v" (Some 396) 1) (
  cons (mkDL "UpReqCDispersion" "t26_s2_align_log_compat" "Theorem" 78 DlMappedUnique "UpReqEntropyUniqueNeg.v" (Some 405) 1) (
  cons (mkDL "UpReqCDispersion" "t26_s3_alignklp_log_compat" "Theorem" 87 DlMappedUnique "UpReqEntropyUniqueNeg.v" (Some 414) 1) (
  cons (mkDL "UpReqCDispersion" "t26_s4_align2_log_compat" "Theorem" 96 DlMappedUnique "UpReqEntropyUniqueNeg.v" (Some 423) 1) (
  cons (mkDL "UpReqCDispersion" "t26_s5_align3_log_compat" "Theorem" 105 DlMappedUnique "UpReqEntropyUniqueNeg.v" (Some 432) 1) (
  cons (mkDL "UpReqCDispersion" "t26_s6_u2_log_compat" "Theorem" 114 DlMappedUnique "UpReqEntropyUniqueNeg.v" (Some 441) 1) (
  cons (mkDL "UpReqCDispersion" "t26_s7_fepattn_log_compat" "Theorem" 123 DlMappedUnique "UpReqEntropyUniqueNeg.v" (Some 450) 1) (
  cons (mkDL "UpReqCDispersion" "t26_s8_feplogz_log_compat" "Theorem" 132 DlMappedUnique "UpReqEntropyUniqueNeg.v" (Some 459) 1) (
  cons (mkDL "UpReqCDispersion" "t26_s9_alignid_log_compat" "Theorem" 141 DlMappedUnique "UpReqEntropyUniqueNeg.v" (Some 468) 1) (
  cons (mkDL "UpReqCDispersion" "t26_bsum" "Definition" 155 DlMappedUnique "UpReqEntropyUniqueNeg.v" (Some 482) 1) (
  cons (mkDL "UpReqCDispersion" "t26_s1_req_log_inv_one_inv" "Theorem" 165 DlMappedUnique "UpReqEntropyUniqueNeg.v" (Some 492) 1) (
  cons (mkDL "UpReqCDispersion" "t26_s1_req_log_div" "Theorem" 174 DlMappedUnique "UpReqEntropyUniqueNeg.v" (Some 501) 1) (
  cons (mkDL "UpReqCDispersion" "t26_s2_req_free_energy_align_ext" "Theorem" 188 DlMappedUnique "UpReqEntropyUniqueNeg.v" (Some 515) 1) (
  cons (mkDL "UpReqCDispersion" "t26_s3_rkl_log_inv_one_inv" "Theorem" 210 DlMappedUnique "UpReqEntropyUniqueNeg.v" (Some 537) 1) (
  cons (mkDL "UpReqCDispersion" "t26_s3_req_log_proj_pass" "Theorem" 219 DlMappedUnique "UpReqEntropyUniqueNeg.v" (Some 546) 1) (
  cons (mkDL "UpReqCDispersion" "t26_s4_req2_log_inv_one_inv" "Theorem" 238 DlMappedUnique "UpReqEntropyUniqueNeg.v" (Some 565) 1) (
  cons (mkDL "UpReqCDispersion" "t26_s5_r2_log_inv_opp" "Theorem" 250 DlMappedUnique "UpReqEntropyUniqueNeg.v" (Some 577) 1) (
  cons (mkDL "UpReqCDispersion" "t26_s5_w_F_t_rel_decomp" "Theorem" 259 DlMappedUnique "UpReqEntropyUniqueNeg.v" (Some 586) 1) (
  cons (mkDL "UpReqCDispersion" "t26_s6_r2u_FA_witness_ext" "Theorem" 306 DlMappedUnique "UpReqEntropyUniqueNeg.v" (Some 633) 1) (
  cons (mkDL "UpReqCDispersion" "t26_s7_req_fep_F_ext" "Theorem" 325 DlMappedUnique "UpReqEntropyUniqueNeg.v" (Some 652) 1) (
  cons (mkDL "UpReqCDispersion" "t26_s8_req_fep_F_ext_logz" "Theorem" 346 DlMappedUnique "UpReqEntropyUniqueNeg.v" (Some 673) 1) (
  cons (mkDL "UpReqCDispersion" "t26_s9_w_gap_base" "Theorem" 366 DlMappedUnique "UpReqEntropyUniqueNeg.v" (Some 693) 1) (
  cons (mkDL "UpReqCDispersion" "t26_s9_w_subgap_base" "Theorem" 416 DlMappedUnique "UpReqEntropyUniqueNeg.v" (Some 743) 1) (
  cons (mkDL "UpReqCSB" "real_cauchy_schwarz_B" "Lemma" 59 DlGone "" None 0) (
  cons (mkDL "UpReqELBOEps" "real_elbo" "Definition" 89 DlMappedUnique "UpReqMinUniqueTight.v" (Some 147) 1) (
  cons (mkDL "UpReqELBOEps" "real_evidence" "Definition" 94 DlMappedUnique "UpReqMinUniqueTight.v" (Some 152) 1) (
  cons (mkDL "UpReqELBOEps" "real_elbo_def" "Lemma" 104 DlMappedUnique "UpReqMinUniqueTight.v" (Some 162) 1) (
  cons (mkDL "UpReqELBOEps" "real_evidence_def" "Lemma" 117 DlMappedUnique "UpReqMinUniqueTight.v" (Some 175) 1) (
  cons (mkDL "UpReqELBOEps" "real_evidence_kl_decomp" "Lemma" 145 DlMappedUnique "UpReqMinUniqueTight.v" (Some 203) 1) (
  cons (mkDL "UpReqELBOEps" "elbo_lower_bound_close_eps" "Lemma" 235 DlMappedUnique "UpReqMinUniqueTight.v" (Some 293) 1) (
  cons (mkDL "UpReqELBOEps" "real_elbo_lower_bound_eps" "Theorem" 295 DlMappedUnique "UpReqMinUniqueTight.v" (Some 353) 1) (
  cons (mkDL "UpReqELBOEps" "real_elbo_lower_bound_eps_partition" "Theorem" 361 DlMappedUnique "UpReqMinUniqueTight.v" (Some 419) 1) (
  cons (mkDL "UpReqELBOStrict" "t33_elbo_strict_of_fe_strict" "Lemma" 124 DlMappedUnique "UpReqMinUniqueTight.v" (Some 863) 1) (
  cons (mkDL "UpReqELBOStrict" "t33_fe_strict_of_kl_pos" "Lemma" 148 DlMappedUnique "UpReqMinUniqueTight.v" (Some 887) 1) (
  cons (mkDL "UpReqELBOStrict" "t33_elbo_strict_of_kl_pos" "Lemma" 214 DlMappedUnique "UpReqMinUniqueTight.v" (Some 953) 1) (
  cons (mkDL "UpReqELBOStrict" "t33_elbo_strict_divergence_le" "Theorem" 244 DlMappedUnique "UpReqMinUniqueTight.v" (Some 983) 1) (
  cons (mkDL "UpReqELBOStrict" "t33_elbo_strict_divergence" "Theorem" 274 DlMappedUnique "UpReqMinUniqueTight.v" (Some 1013) 1) (
  cons (mkDL "UpReqELBOStrict" "t33_elbo_strict_divergence_bool" "Theorem" 309 DlMappedUnique "UpReqMinUniqueTight.v" (Some 1048) 1) (
  cons (mkDL "UpReqELBOStrict" "t33_elbo_boundary_bool" "Theorem" 344 DlMappedUnique "UpReqMinUniqueTight.v" (Some 1083) 1) (
  cons (mkDL "UpReqELBOTight" "t12_tangent_eq" "Definition" 109 DlMappedUnique "UpReqMinUniqueTight.v" (Some 515) 1) (
  cons (mkDL "UpReqELBOTight" "t12_tight_kl_zero" "Lemma" 136 DlMappedUnique "UpReqMinUniqueTight.v" (Some 541) 1) (
  cons (mkDL "UpReqELBOTight" "t12_elbo_tight_forward" "Theorem" 219 DlMappedUnique "UpReqMinUniqueTight.v" (Some 623) 1) (
  cons (mkDL "UpReqELBOTight" "t12_elbo_tight_backward" "Theorem" 290 DlMappedUnique "UpReqMinUniqueTight.v" (Some 694) 1) (
  cons (mkDL "UpReqELBOTight" "t12_elbo_tight" "Theorem" 316 DlMappedUnique "UpReqMinUniqueTight.v" (Some 720) 1) (
  cons (mkDL "UpReqELBOTight" "t12_elbo_tight_forward_bool" "Theorem" 370 DlMappedUnique "UpReqMinUniqueTight.v" (Some 774) 1) (
  cons (mkDL "UpReqELBOTight" "t12_elbo_tight_bool" "Theorem" 397 DlMappedUnique "UpReqMinUniqueTight.v" (Some 801) 1) (
  cons (mkDL "UpReqEntropyUniqueTemp" "t22_bool_sumf" "Definition" 96 DlMappedUnique "UpReqEntropyUniqueNeg.v" (Some 52) 1) (
  cons (mkDL "UpReqEntropyUniqueTemp" "t22_bool_sum_pos" "Lemma" 99 DlMappedUnique "UpReqEntropyUniqueNeg.v" (Some 55) 1) (
  cons (mkDL "UpReqEntropyUniqueTemp" "t22_bool_sum_ext" "Lemma" 111 DlMappedUnique "UpReqEntropyUniqueNeg.v" (Some 67) 1) (
  cons (mkDL "UpReqEntropyUniqueTemp" "t22_bool_sum_linear" "Lemma" 121 DlMappedUnique "UpReqEntropyUniqueNeg.v" (Some 77) 1) (
  cons (mkDL "UpReqEntropyUniqueTemp" "t22_bool_sum_add" "Lemma" 131 DlMappedUnique "UpReqEntropyUniqueNeg.v" (Some 87) 1) (
  cons (mkDL "UpReqEntropyUniqueTemp" "t22_tangent_eq" "Definition" 169 DlMappedUnique "UpReqEntropyUniqueNeg.v" (Some 125) 1) (
  cons (mkDL "UpReqEntropyUniqueTemp" "t22_entropy_eq_kl_zero" "Theorem" 195 DlMappedUnique "UpReqEntropyUniqueNeg.v" (Some 151) 1) (
  cons (mkDL "UpReqEntropyUniqueTemp" "t22_entropy_eq_KL_zero" "Theorem" 258 DlMappedUnique "UpReqEntropyUniqueNeg.v" (Some 214) 1) (
  cons (mkDL "UpReqEntropyUniqueTemp" "t22_entropy_max_unique_temp_explicit" "Theorem" 297 DlMappedUnique "UpReqEntropyUniqueNeg.v" (Some 252) 1) (
  cons (mkDL "UpReqEntropyUniqueTemp" "t22_entropy_max_unique_temp_bool" "Theorem" 367 DlMappedUnique "UpReqEntropyUniqueNeg.v" (Some 320) 1) (
  cons (mkDL "UpReqFEPCanon" "real_kl_decomp_full_canon" "Lemma" 79 DlMappedUnique "UpReqMinUniqueTight.v" (Some 47) 1) (
  cons (mkDL "UpReqFEPCanon" "real_kl_decomp_full_canon_partition" "Lemma" 120 DlMappedUnique "UpReqMinUniqueTight.v" (Some 88) 1) (
  cons (mkDL "UpReqGibbsD" "gibbsd_lt_add_opp_r" "Lemma" 62 DlMappedMulti "G08_Gibbs.v" (Some 96) 2) (
  cons (mkDL "UpReqGibbsD" "gibbsd_le_b_opp" "Lemma" 94 DlMappedMulti "G08_Gibbs.v" (Some 128) 2) (
  cons (mkDL "UpReqGibbsD" "gibbsd_le_b_id_l" "Lemma" 110 DlMappedMulti "G08_Gibbs.v" (Some 144) 2) (
  cons (mkDL "UpReqGibbsD" "gibbsd_minus_flip" "Lemma" 120 DlMappedMulti "G08_Gibbs.v" (Some 154) 2) (
  cons (mkDL "UpReqGibbsD" "gibbsd_le_b_mult_pos_r" "Lemma" 140 DlMappedMulti "G08_Gibbs.v" (Some 174) 2) (
  cons (mkDL "UpReqGibbsD" "gibbsd_p_mult_ratio" "Lemma" 198 DlMappedMulti "G08_Gibbs.v" (Some 232) 2) (
  cons (mkDL "UpReqGibbsD" "gibbsd_p_minus_ratio" "Lemma" 229 DlMappedMulti "G08_Gibbs.v" (Some 263) 2) (
  cons (mkDL "UpReqGibbsD" "gibbsd_two_pos" "Lemma" 262 DlMappedMulti "G08_Gibbs.v" (Some 296) 2) (
  cons (mkDL "UpReqGibbsD" "gibbsd_half" "Definition" 267 DlMappedMulti "G08_Gibbs.v" (Some 305) 2) (
  cons (mkDL "UpReqGibbsD" "gibbsd_half_pos" "Lemma" 270 DlMappedMulti "G08_Gibbs.v" (Some 308) 2) (
  cons (mkDL "UpReqGibbsD" "gibbsd_half_sum" "Lemma" 276 DlMappedMulti "G08_Gibbs.v" (Some 314) 2) (
  cons (mkDL "UpReqGibbsD" "gibbsd_list_sum_le_b" "Lemma" 324 DlMappedMulti "G08_Gibbs.v" (Some 362) 2) (
  cons (mkDL "UpReqGibbsD" "gibbsd_list_sum_minus" "Lemma" 374 DlMappedMulti "G08_Gibbs.v" (Some 412) 2) (
  cons (mkDL "UpReqGibbsD" "gibbsd_gibbs_pointwise_B" "Lemma" 405 DlMappedMulti "G08_Gibbs.v" (Some 443) 2) (
  cons (mkDL "UpReqGibbsD" "gibbsd_gibbs_inequality" "Theorem" 440 DlMappedMulti "G08_Gibbs.v" (Some 478) 2) (
  cons (mkDL "UpReqGibbsD" "gibbsd_cross_entropy_decomp" "Theorem" 492 DlMappedMulti "G08_Gibbs.v" (Some 530) 2) (
  cons (mkDL "UpReqMinFreeEps" "min_free_energy_close_eps" "Lemma" 72 DlMappedUnique "UpReqMinUniqueTight.v" (Some 1172) 1) (
  cons (mkDL "UpReqMinFreeEps" "min_free_energy_is_boltzmann_eps" "Theorem" 133 DlMappedUnique "UpReqMinUniqueTight.v" (Some 1233) 1) (
  cons (mkDL "UpReqMinFreeEps" "min_free_energy_is_boltzmann_eps_partition" "Theorem" 205 DlMappedUnique "UpReqMinUniqueTight.v" (Some 1305) 1) (
  cons (mkDL "UpReqMisc5" "reqStateSpace" "Class" 77 DlMappedMulti "UpReqMisc5B.v" (Some 58) 2) (
  cons (mkDL "UpReqMisc5" "rsminus" "Definition" 120 DlMappedUnique "UpReqMisc5B.v" (Some 101) 1) (
  cons (mkDL "UpReqMisc5" "reqStateSpaceExt" "Class" 126 DlMappedUnique "UpReqMisc5B.v" (Some 107) 1) (
  cons (mkDL "UpReqMisc5" "reqHilbertSpace" "Class" 152 DlMappedMulti "UpReqMisc5B.v" (Some 133) 2) (
  cons (mkDL "UpReqMisc5" "reqSumOver" "Class" 174 DlMappedUnique "UpReqMisc5B.v" (Some 155) 1) (
  cons (mkDL "UpReqMisc5" "rboltzmann_factor" "Definition" 213 DlMappedUnique "UpReqMisc5B.v" (Some 194) 1) (
  cons (mkDL "UpReqMisc5" "rboltzmann_prob" "Definition" 216 DlMappedUnique "UpReqMisc5B.v" (Some 197) 1) (
  cons (mkDL "UpReqMisc5" "rpartition_condition" "Definition" 220 DlMappedUnique "UpReqMisc5B.v" (Some 201) 1) (
  cons (mkDL "UpReqMisc5" "rCoreClaim5" "Definition" 226 DlMappedUnique "UpReqMisc5B.v" (Some 207) 1) (
  cons (mkDL "UpReqMisc5" "req_core_claim5_holds" "Theorem" 231 DlMappedUnique "UpReqMisc5B.v" (Some 212) 1) (
  cons (mkDL "UpReqMisc5" "req_boltzmann_factor_pos" "Theorem" 241 DlMappedUnique "UpReqMisc5B.v" (Some 222) 1) (
  cons (mkDL "UpReqMisc5" "req_boltzmann_prob_pos" "Theorem" 248 DlMappedUnique "UpReqMisc5B.v" (Some 229) 1) (
  cons (mkDL "UpReqMisc5" "req_prediction_fluctuation_scale" "Theorem" 259 DlMappedUnique "UpReqMisc5B.v" (Some 240) 1) (
  cons (mkDL "UpReqMisc5" "rE_B" "Definition" 282 DlMappedUnique "UpReqMisc5B.v" (Some 263) 1) (
  cons (mkDL "UpReqMisc5" "rentropy_gradient" "Definition" 290 DlMappedUnique "UpReqMisc5B.v" (Some 271) 1) (
  cons (mkDL "UpReqMisc5" "rCoreClaim3" "Definition" 295 DlMappedUnique "UpReqMisc5B.v" (Some 276) 1) (
  cons (mkDL "UpReqMisc5" "req_thermo_core_claim3_holds" "Theorem" 301 DlMappedUnique "UpReqMisc5B.v" (Some 282) 1) (
  cons (mkDL "UpReqMisc5" "rboltzmann_prob_t" "Definition" 312 DlMappedUnique "UpReqMisc5B.v" (Some 293) 1) (
  cons (mkDL "UpReqMisc5" "rCoreClaim5t" "Definition" 317 DlMappedUnique "UpReqMisc5B.v" (Some 298) 1) (
  cons (mkDL "UpReqMisc5" "req_thermo_core_claim5_holds" "Theorem" 323 DlMappedUnique "UpReqMisc5B.v" (Some 304) 1) (
  cons (mkDL "UpReqMisc5" "req_step_diff_point" "Lemma" 355 DlMappedUnique "UpReqMisc5B.v" (Some 336) 1) (
  cons (mkDL "UpReqMisc5" "req_entropy_gradient_strict_mono" "Theorem" 368 DlMappedUnique "UpReqMisc5B.v" (Some 349) 1) (
  cons (mkDL "UpReqMisc5" "req_gradient_diff_from_zero" "Theorem" 375 DlMappedUnique "UpReqMisc5B.v" (Some 356) 1) (
  cons (mkDL "UpReqMisc5" "req_gradient_step_recurrence" "Theorem" 385 DlMappedUnique "UpReqMisc5B.v" (Some 366) 1) (
  cons (mkDL "UpReqMisc5" "req_sum_exp" "Fixpoint" 426 DlMappedUnique "UpReqMisc5B.v" (Some 407) 1) (
  cons (mkDL "UpReqMisc5" "req_sum_exp_positive" "Lemma" 434 DlMappedUnique "UpReqMisc5B.v" (Some 415) 1) (
  cons (mkDL "UpReqMisc5" "rloss_of_prop" "Definition" 479 DlMappedUnique "UpReqMisc5B.v" (Some 460) 1) (
  cons (mkDL "UpReqMisc5" "rsequence_loss_prefix" "Fixpoint" 483 DlMappedUnique "UpReqMisc5B.v" (Some 464) 1) (
  cons (mkDL "UpReqMisc5" "rsequence_loss" "Definition" 489 DlMappedUnique "UpReqMisc5B.v" (Some 470) 1) (
  cons (mkDL "UpReqMisc5" "rtotal_loss" "Definition" 492 DlMappedUnique "UpReqMisc5B.v" (Some 473) 1) (
  cons (mkDL "UpReqMisc5" "rforce" "Definition" 501 DlMappedUnique "UpReqMisc5B.v" (Some 482) 1) (
  cons (mkDL "UpReqMisc5" "rLangProp" "Definition" 506 DlMappedUnique "UpReqMisc5B.v" (Some 487) 1) (
  cons (mkDL "UpReqMisc5" "rpartition_function" "Definition" 508 DlMappedUnique "UpReqMisc5B.v" (Some 489) 1) (
  cons (mkDL "UpReqMisc5" "rpartition_positive" "Definition" 511 DlMappedUnique "UpReqMisc5B.v" (Some 492) 1) (
  cons (mkDL "UpReqMisc5" "rnormalized_prob" "Definition" 515 DlMappedUnique "UpReqMisc5B.v" (Some 496) 1) (
  cons (mkDL "UpReqMisc5" "req_exp_neg_positive" "Lemma" 520 DlMappedUnique "UpReqMisc5B.v" (Some 501) 1) (
  cons (mkDL "UpReqMisc5" "req_core_claim1_lm_holds" "Theorem" 524 DlMappedUnique "UpReqMisc5B.v" (Some 505) 1) (
  cons (mkDL "UpReqMisc5" "req_core_claim3_lm_holds" "Theorem" 530 DlMappedUnique "UpReqMisc5B.v" (Some 511) 1) (
  cons (mkDL "UpReqMisc5" "req_core_claim5_lm_holds" "Theorem" 549 DlMappedUnique "UpReqMisc5B.v" (Some 530) 1) (
  cons (mkDL "UpReqMisc5" "req_normalized_prob_pos" "Theorem" 558 DlMappedUnique "UpReqMisc5B.v" (Some 539) 1) (
  cons (mkDL "UpReqMisc5" "req_prediction_boltzmann_sampling_holds" "Theorem" 567 DlMappedUnique "UpReqMisc5B.v" (Some 548) 1) (
  cons (mkDL "UpReqMisc5" "rgrp_of_nat_S_pos" "Lemma" 602 DlMappedUnique "UpReqMisc5B.v" (Some 583) 1) (
  cons (mkDL "UpReqMisc5" "rgrp_G_pos_of_nonempty" "Theorem" 619 DlMappedUnique "UpReqMisc5B.v" (Some 600) 1) (
  cons (mkDL "UpReqMisc5" "rgrp_G_pos_of_nonempty_enum" "Theorem" 631 DlMappedUnique "UpReqMisc5B.v" (Some 612) 1) (
  cons (mkDL "UpReqMisc5" "req_grpo_count_one" "Theorem" 638 DlMappedUnique "UpReqMisc5B.v" (Some 619) 1) (
  cons (mkDL "UpReqMisc5" "req_list_sum_g_zero_fn" "Lemma" 645 DlMappedUnique "UpReqMisc5B.v" (Some 626) 1) (
  cons (mkDL "UpReqMisc5" "req_split_count_one" "Lemma" 668 DlMappedUnique "UpReqMisc5B.v" (Some 649) 1) (
  cons (mkDL "UpReqMisc5" "req_grpo_indicator_sum_one" "Theorem" 710 DlMappedUnique "UpReqMisc5B.v" (Some 691) 1) (
  cons (mkDL "UpReqMisc5" "req_grpo_uniform_mass" "Theorem" 750 DlMappedUnique "UpReqMisc5B.v" (Some 731) 1) (
  cons (mkDL "UpReqMisc5" "req_square_expand4" "Lemma" 788 DlMappedUnique "UpReqMisc5B.v" (Some 769) 1) (
  cons (mkDL "UpReqMisc5" "req_plus_cancel_head" "Lemma" 803 DlMappedUnique "UpReqMisc5B.v" (Some 784) 1) (
  cons (mkDL "UpReqMisc5" "req_compose_diff_decomp" "Lemma" 819 DlMappedUnique "UpReqMisc5B.v" (Some 800) 1) (
  cons (mkDL "UpReqMisc5" "req_half_le_one" "Lemma" 881 DlMappedUnique "UpReqMisc5B.v" (Some 862) 1) (
  cons (mkDL "UpReqMisc5" "req_half_le_self" "Lemma" 895 DlMappedUnique "UpReqMisc5B.v" (Some 876) 1) (
  cons (mkDL "UpReqMisc5" "req_minus_plus_zero_r" "Lemma" 905 DlMappedMulti "UpReqMisc5B.v" (Some 886) 2) (
  cons (mkDL "UpReqMisc5" "req_square_diff_expand" "Lemma" 920 DlMappedUnique "UpReqMisc5B.v" (Some 901) 1) (
  cons (mkDL "UpReqMisc5" "req_dpo_logit_denom_pos" "Lemma" 996 DlMappedUnique "UpReqMisc5B.v" (Some 977) 1) (
  cons (mkDL "UpReqMisc5" "req_dpo_sigmoid" "Definition" 1004 DlMappedUnique "UpReqMisc5B.v" (Some 985) 1) (
  cons (mkDL "UpReqMisc5" "req_dpo_loss_diff_decomp" "Theorem" 1013 DlMappedUnique "UpReqMisc5B.v" (Some 994) 1) (
  cons (mkDL "UpReqMisc5" "req_dpo_sigmoid_pos" "Lemma" 1030 DlMappedUnique "UpReqMisc5B.v" (Some 1011) 1) (
  cons (mkDL "UpReqMisc5" "req_dpo_sigmoid_identity" "Theorem" 1036 DlMappedUnique "UpReqMisc5B.v" (Some 1017) 1) (
  cons (mkDL "UpReqMisc5" "req_dpo_sigmoid_complement" "Theorem" 1047 DlMappedUnique "UpReqMisc5B.v" (Some 1028) 1) (
  cons (mkDL "UpReqMisc5" "req_dpo_gradient_alt" "Theorem" 1064 DlMappedUnique "UpReqMisc5B.v" (Some 1045) 1) (
  cons (mkDL "fa51_g3_sumpos" "fa51_g3_witness" "Definition" 3 DlGone "" None 0) (
  cons (mkDL "fa56_g3_carrier" "fa56_g3_witness" "Definition" 6 DlGone "" None 0) (
  cons (mkDL "fa56_g3_carrier" "fa56_g3_witness2" "Definition" 9 DlGone "" None 0) (
  cons (mkDL "fa56b_g3" "fa56b_g3_witness" "Definition" 7 DlGone "" None 0) (
  cons (mkDL "fa56b_g3" "fa56b_g3_witness2" "Definition" 10 DlGone "" None 0) (
  cons (mkDL "fa56b_g3" "fa56b_g3_witness3" "Definition" 13 DlGone "" None 0) (
  cons (mkDL "fa56b_g3" "fa56b_g3_witness4" "Definition" 16 DlGone "" None 0) (
  cons (mkDL "fa56c_g3" "fa56c_g3_witness" "Definition" 7 DlGone "" None 0) (
  cons (mkDL "fa56c_g3" "fa56c_g3_witness2" "Definition" 10 DlGone "" None 0) (
  cons (mkDL "fa56c_g3" "fa56c_g3_witness3" "Definition" 13 DlGone "" None 0) (
  cons (mkDL "fa56c_g3" "fa56c_g3_witness4" "Definition" 16 DlGone "" None 0) (
  cons (mkDL "ppa_g3" "ppa_g3_witness" "Definition" 13 DlGone "" None 0) (
  cons (mkDL "ppa_g3" "ppa_g3_witness2" "Definition" 16 DlGone "" None 0) (
  cons (mkDL "ppa_g3" "ppa_g3_witness3" "Definition" 19 DlGone "" None 0) (
  cons (mkDL "ppa_g3" "ppa_g3_witness4" "Definition" 22 DlGone "" None 0) (
  cons (mkDL "ppa_g3" "ppa_g3_witness5" "Definition" 25 DlGone "" None 0) (
  cons (mkDL "ppa_g3" "ppa_g3_witness6" "Definition" 28 DlGone "" None 0)
  nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

(* ---- Census and retrieval (all transparent, axiom-free) ---- *)
Fixpoint reg_length (l : list DLDecl) : nat :=
  match l with nil => 0 | cons _ t => S (reg_length t) end.

Fixpoint count_status (s : DLStatus) (l : list DLDecl) : nat :=
  match l with
  | nil => 0
  | cons e t => if DLStatus_eqb (dld_status e) s then S (count_status s t)
                else count_status s t
  end.

Fixpoint modules_length (l : list DLModule) : nat :=
  match l with nil => 0 | cons _ t => S (modules_length t) end.

Fixpoint modules_declsum (l : list DLModule) : nat :=
  match l with nil => 0 | cons m t => dlm_decl_count m + modules_declsum t end.

Definition census : list nat :=
  cons (count_status DlMappedUnique decls_registry)
  (cons (count_status DlMappedMulti decls_registry)
  (cons (count_status DlGone decls_registry)
  (cons (count_status DlRenamed decls_registry) nil))).

Definition census_sum : nat :=
  count_status DlMappedUnique decls_registry +
  count_status DlMappedMulti decls_registry +
  count_status DlGone decls_registry +
  count_status DlRenamed decls_registry.

(* Self-consistency three checks: the status counts sum to the total; the module register holds 48 entries; the module declaration counts sum to the declaration register length *)
Definition registry_selfconsistent : bool :=
  andb (Nat.eqb (census_sum) (reg_length decls_registry))
  (andb (Nat.eqb (modules_length modules_registry) 48)
        (Nat.eqb (modules_declsum modules_registry) (reg_length decls_registry))).

Definition decls_total : nat := reg_length decls_registry.
Definition modules_total : nat := modules_length modules_registry.

(* Retrieve by symbol name (string equality via String.eqb) *)
Fixpoint lineage_of (nm : string) (l : list DLDecl) : option DLDecl :=
  match l with
  | nil => None
  | cons e t => if String.eqb (dld_name e) nm then Some e else lineage_of nm t
  end.

(* Retrieve by deleted file *)
Fixpoint decls_of_module (md : string) (l : list DLDecl) : list DLDecl :=
  match l with
  | nil => nil
  | cons e t => if String.eqb (dld_module e) md
                then cons e (decls_of_module md t)
                else decls_of_module md t
  end.

(* Hard failure surface: list of GONE declarations (filter function) *)
Fixpoint gone_list (l : list DLDecl) : list DLDecl :=
  match l with
  | nil => nil
  | cons e t => if DLStatus_eqb (dld_status e) DlGone
                then cons e (gone_list t) else gone_list t
  end.

Definition hard_failure_surface : nat := reg_length (gone_list decls_registry).
