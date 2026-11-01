(* ==========================================================================)
   abl_tbase_sumpos_spp.v - base-region upper-volume assumption-resolution
   supply file, construction group UB12: F8 sum-positivity spp family, ten
   Id-face named per-host feed-form supplies on the fa51 Id-carrier recipe.
   Mission.  Ten named supply theorems close the ten sum-positivity abstract
     interface slots of six hosts, one per slot (anchors in the banners).
     Out-of-scope same-family slots stay untouched (supplied elsewhere):
     sum_eq_list x4 (csm/cmkr/cms), S08 real_sum_pos_preserved
     (UpAblEps66Sum), G02 pos pair (UB5 tspt_), urems_/usrq_/tspps_/tbaf_
     req faces, G05 restatement, Banach/Vajda (zero slots), Arch_UpReq_10
     (UB11), lower-volume 16 slots.
   Dependencies.  S01_BaseRing (RealInterfaceEnhanced class); fa51_sumpos_id
     (engine fa51_sumd :68 / fa51_sumd_nonneg :76 / fa51_lt_le :89 /
     fa51_sumd_pos_cons :96; explicit-form root fa51_sumd_nonnil_pos :111
     in reserve); Stdlib List; Stdlib Extraction (tail); six hosts read-only.
   References.  Supply root fa51_sumd_pos_cons@fa51_sumpos_id.v :96 (five-
     argument export, S explicit, RI implicit, cons form); precedents: fa51
     in-file engine, tbaf_ per-host feed form (RealInterfaceEnhancedSetoid
     carrier) - this file is its Id-carrier counterpart; tbsp_ pool zero-hit.
   Constructivity.  All proofs Qed-closed and genuinely constructive, no
     suspended premises, no classical logic; statement faces all Set-layer
     (lt/le are S01 interface Set-valued order predicates; R/lt/zero by
     explicit @RI projection; zero Prop faces); supplies use only the
     exported root content fa51_sumd_pos_cons; head nonemptiness is the
     enumerated w::rest data (no silent strengthening); per-theorem Print
     Assumptions census plus a tail extraction probe close the file.
   Build.  rocq c -native-compiler no -q -Q . "" (Rocq 9.1, guard-wrapped,
     ulimit -s 65532); green set: EXIT=0, true-error lines 0, .vo head
     8 bytes 436f7121 00015ff4, .vo newer than .v.
   ========================================================================== *)

Require Import S01_BaseRing.
Require Import fa51_sumpos_id.
From Stdlib Require Import List.
Import ListNotations.

(* ============================================================ *)
(* Segment 1: S04_RealExpLogConv.v Section FreeEnergyMinimization *)
(*   sum_over_S_pos slot (current archive :3401-3402 verbatim:    *)
(*   Variable sum_over_S_pos : forall f : S -> R,                 *)
(*     (forall s : S, lt zero (f s)) -> lt zero (sum_over_S f).   *)
(*   Section Context :2044-2046 = {RI : RealInterfaceEnhanced}    *)
(*   {SS : StateSpace RI}{SO : SumOver RI SS}, sum_over_S :2058.  *)
(* ============================================================ *)

Theorem tbsp_s04fem_sum_over_S_pos_cons :
  forall {RI : RealInterfaceEnhanced} (S : Set) (f : S -> @R RI)
         (w : S) (rest : list S),
    (forall s : S, @lt RI (@zero RI) (f s)) ->
    @lt RI (@zero RI) (fa51_sumd S f (w :: rest)).
Proof.
  intros RI S f w rest Hpt.
  exact (fa51_sumd_pos_cons S f w rest Hpt).
Qed.

(* ============================================================ *)
(* Segment 2: S05_AlignmentGRPO.v Section Alignment (from :33).   *)
(*   sum_over_S_pos slot (current archive :2398 single line;      *)
(*   sum_over_S := @sum_over_S RI SS SO :44).  Statement face     *)
(*   identical in form to Segment 1.                              *)
(* ============================================================ *)

Theorem tbsp_s05alg_sum_over_S_pos_cons :
  forall {RI : RealInterfaceEnhanced} (S : Set) (f : S -> @R RI)
         (w : S) (rest : list S),
    (forall s : S, @lt RI (@zero RI) (f s)) ->
    @lt RI (@zero RI) (fa51_sumd S f (w :: rest)).
Proof.
  intros RI S f w rest Hpt.
  exact (fa51_sumd_pos_cons S f w rest Hpt).
Qed.

(* ============================================================ *)
(* Segment 3: S05_AlignmentGRPO.v Section U2FixedPoint (:4361).   *)
(*   sum_over_S_pos slot (current archive :4392 single line).     *)
(*   Statement face identical in form to Segment 1.               *)
(* ============================================================ *)

Theorem tbsp_s05u2_sum_over_S_pos_cons :
  forall {RI : RealInterfaceEnhanced} (S : Set) (f : S -> @R RI)
         (w : S) (rest : list S),
    (forall s : S, @lt RI (@zero RI) (f s)) ->
    @lt RI (@zero RI) (fa51_sumd S f (w :: rest)).
Proof.
  intros RI S f w rest Hpt.
  exact (fa51_sumd_pos_cons S f w rest Hpt).
Qed.

(* ============================================================ *)
(* Segment 4: S06_DiffSamplingGibbs.v Section AttentionGibbsBridge *)
(*   sum_pos_preserved slot (current archive :3185-3186 verbatim: *)
(*   Variable sum_pos_preserved :                                 *)
(*     forall (f : S -> R), (forall s, lt zero (f s)) ->          *)
(*       lt zero (sum_over_S f).                                  *)
(*   Statement face identical in form to Segment 1 (binding name  *)
(*   sum_pos_preserved).                                          *)
(* ============================================================ *)

Theorem tbsp_s06agb_sum_pos_preserved_cons :
  forall {RI : RealInterfaceEnhanced} (S : Set) (f : S -> @R RI)
         (w : S) (rest : list S),
    (forall s : S, @lt RI (@zero RI) (f s)) ->
    @lt RI (@zero RI) (fa51_sumd S f (w :: rest)).
Proof.
  intros RI S f w rest Hpt.
  exact (fa51_sumd_pos_cons S f w rest Hpt).
Qed.

(* ============================================================ *)
(* Segment 5: S15_TailFEPUp.v Section FEPAttention (:47) spp slot *)
(*   (current archive :66-67 verbatim: Variable spp :             *)
(*   forall f : S -> R, (forall s : S, lt zero (f s)) ->          *)
(*   lt zero (sum_over_S f).).  With Segment 8 (G01 FEPLogZ) this *)
(*   pair forms redundancy pair (1) of register card 15; both     *)
(*   sides carry a named placement here (one-pass construction    *)
(*   covering both hosts).                                        *)
(* ============================================================ *)

Theorem tbsp_s15fepattn_spp_cons :
  forall {RI : RealInterfaceEnhanced} (S : Set) (f : S -> @R RI)
         (w : S) (rest : list S),
    (forall s : S, @lt RI (@zero RI) (f s)) ->
    @lt RI (@zero RI) (fa51_sumd S f (w :: rest)).
Proof.
  intros RI S f w rest Hpt.
  exact (fa51_sumd_pos_cons S f w rest Hpt).
Qed.

(* ============================================================ *)
(* Segment 6: S15_TailFEPUp.v Section RowView (:139) spp slot     *)
(*   (current archive :145-146 verbatim; statement face same form *)
(*   as Segment 5; the in-Section enum_nonempty explicit position *)
(*   :147 is on file; explicit-form root fa51_sumd_nonnil_pos     *)
(*   held in reserve for use).                                    *)
(* ============================================================ *)

Theorem tbsp_s15rowview_spp_cons :
  forall {RI : RealInterfaceEnhanced} (S : Set) (f : S -> @R RI)
         (w : S) (rest : list S),
    (forall s : S, @lt RI (@zero RI) (f s)) ->
    @lt RI (@zero RI) (fa51_sumd S f (w :: rest)).
Proof.
  intros RI S f w rest Hpt.
  exact (fa51_sumd_pos_cons S f w rest Hpt).
Qed.

(* ============================================================ *)
(* Segment 7: S15_TailFEPUp.v Section FEPLogZ (:1905) spp slot    *)
(*   (current archive :1922-1923 verbatim; the in-file note       *)
(*   :1921 attests the same-root form of the Section              *)
(*   AttentionGibbsBridge Variable sum_pos_preserved = same root  *)
(*   as Segment 4; statement face same form).                     *)
(* ============================================================ *)

Theorem tbsp_s15feplogz_spp_cons :
  forall {RI : RealInterfaceEnhanced} (S : Set) (f : S -> @R RI)
         (w : S) (rest : list S),
    (forall s : S, @lt RI (@zero RI) (f s)) ->
    @lt RI (@zero RI) (fa51_sumd S f (w :: rest)).
Proof.
  intros RI S f w rest Hpt.
  exact (fa51_sumd_pos_cons S f w rest Hpt).
Qed.

(* ============================================================ *)
(* Segment 8: G01_CoreMicro.v Section FEPLogZ (:150) spp slot     *)
(*   (current archive :167-168 verbatim; statement face same form *)
(*   as Segment 5).                                               *)
(* ============================================================ *)

Theorem tbsp_g01feplogz_spp_cons :
  forall {RI : RealInterfaceEnhanced} (S : Set) (f : S -> @R RI)
         (w : S) (rest : list S),
    (forall s : S, @lt RI (@zero RI) (f s)) ->
    @lt RI (@zero RI) (fa51_sumd S f (w :: rest)).
Proof.
  intros RI S f w rest Hpt.
  exact (fa51_sumd_pos_cons S f w rest Hpt).
Qed.

(* ============================================================ *)
(* Segment 9: G01_CoreMicro.v Section FEPAttention (:385) spp     *)
(*   slot (current archive :404-405 verbatim; statement face same *)
(*   form).                                                       *)
(* ============================================================ *)

Theorem tbsp_g01fepattn_spp_cons :
  forall {RI : RealInterfaceEnhanced} (S : Set) (f : S -> @R RI)
         (w : S) (rest : list S),
    (forall s : S, @lt RI (@zero RI) (f s)) ->
    @lt RI (@zero RI) (fa51_sumd S f (w :: rest)).
Proof.
  intros RI S f w rest Hpt.
  exact (fa51_sumd_pos_cons S f w rest Hpt).
Qed.

(* ============================================================ *)
(* Segment 10: G01_CoreMicro.v Section RowView (:474) spp slot    *)
(*   (current archive :480-481 verbatim; statement face same      *)
(*   form; in-Section enum_nonempty explicit position :482 on     *)
(*   file, note as Segment 6).                                    *)
(* ============================================================ *)

Theorem tbsp_g01rowview_spp_cons :
  forall {RI : RealInterfaceEnhanced} (S : Set) (f : S -> @R RI)
         (w : S) (rest : list S),
    (forall s : S, @lt RI (@zero RI) (f s)) ->
    @lt RI (@zero RI) (fa51_sumd S f (w :: rest)).
Proof.
  intros RI S f w rest Hpt.
  exact (fa51_sumd_pos_cons S f w rest Hpt).
Qed.

(* ============================================================ *)
(* Extraction check area: Print Assumptions all-Closed criterion  *)
(* plus Obj.magic extraction probe.                               *)
(* ============================================================ *)

Print Assumptions tbsp_s04fem_sum_over_S_pos_cons.
Print Assumptions tbsp_s05alg_sum_over_S_pos_cons.
Print Assumptions tbsp_s05u2_sum_over_S_pos_cons.
Print Assumptions tbsp_s06agb_sum_pos_preserved_cons.
Print Assumptions tbsp_s15fepattn_spp_cons.
Print Assumptions tbsp_s15rowview_spp_cons.
Print Assumptions tbsp_s15feplogz_spp_cons.
Print Assumptions tbsp_g01feplogz_spp_cons.
Print Assumptions tbsp_g01fepattn_spp_cons.
Print Assumptions tbsp_g01rowview_spp_cons.

From Stdlib Require Import Extraction.
Recursive Extraction tbsp_s04fem_sum_over_S_pos_cons.
Recursive Extraction tbsp_g01rowview_spp_cons.
