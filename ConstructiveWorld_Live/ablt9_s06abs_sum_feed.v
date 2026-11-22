(* ========================================================================
   ablt9_s06abs_sum_feed.v

   Mission.  Supply certificates for the three sum slots of the abstract
   summation interface section uabS4c_SumOverSlot in UpAblS06AbsFeed,
   specialized to the generic enumerated finite-sum carrier csm_sumf (a
   fold over the enumeration list): extensionality s6f9_sum_ext_csm
   (real_eq face), additivity s6f9_sum_add_csm (real_plus face), and
   Bishop monotonicity s6f9_sum_le_B_csm (per-eps real_le_b face,
   constructed here by half-splitting eps, list induction, and the
   rearrangement helper s6f9_eps_split_move).
   Dependencies.  Stdlib List, Extraction; S01_BaseRing through
   S15_TailFEPUp; UpReqSumD (sumd_list_sum); UpReqConcSoftmax (csm_sumf);
   ConcMixSelFeed (cms_sum_ext, cms_sum_add); UpRealLeB (real_le_b);
   UpAblS06AbsFeed (uabS4c_half, uabS4c_half_eq, uabS4c_half_pos).

   References.  Statement shapes follow the interface slots uabS4c_sum_ext,
   uabS4c_sum_add, uabS4c_sum_le_B of UpAblS06AbsFeed; extensionality and
   additivity forward to cms_sum_ext and cms_sum_add of ConcMixSelFeed;
   two-point carrier counterparts fill the same slots at another carrier.

   Constructivity.  All statements are Set-carried (real_eq, real_lt,
   real_le_b); every member is Defined and each Print Assumptions reports
   Closed under the global context; Separate Extraction of all four
   members reports Obj.magic = 0 on both artifact faces.
   Build.  coqc -Q <world> "" ablt9_s06abs_sum_feed.v; artifact first
   bytes 436f7121 00015ff4.
   ======================================================================== *)

From Stdlib Require Import List.
From Stdlib Require Import Extraction.
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
Require Import UpReqConcSoftmax.
Require Import ConcMixSelFeed.
Require Import UpRealLeB.
Require Import UpAblS06AbsFeed.
Import RealInterfaceEnhancedMod.

(* Four-term rearrangement: a doubled half moved across a sum of two
   terms.  All steps are explicit equality transits over real_plus. *)
Lemma s6f9_eps_split_move : forall gx sg h e : Real,
  real_eq (real_plus h h) e ->
  real_eq (real_plus (real_plus gx h) (real_plus sg h))
          (real_plus (real_plus gx sg) e).
Proof.
  intros gx sg h e Hh.
  apply (real_eq_trans
           (real_plus (real_plus gx h) (real_plus sg h))
           (real_plus gx (real_plus h (real_plus sg h)))
           (real_plus (real_plus gx sg) e)).
  - apply real_eq_sym. apply real_plus_assoc.
  - apply (real_eq_trans
             (real_plus gx (real_plus h (real_plus sg h)))
             (real_plus gx (real_plus sg (real_plus h h)))
             (real_plus (real_plus gx sg) e)).
    + apply (real_eq_trans
               (real_plus gx (real_plus h (real_plus sg h)))
               (real_plus gx (real_plus (real_plus sg h) h))
               (real_plus gx (real_plus sg (real_plus h h)))).
      * exact (RealSetoid.real_eq_plus_compat
                 gx (real_plus h (real_plus sg h))
                 gx (real_plus (real_plus sg h) h)
                 (real_eq_refl gx)
                 (real_eq_trans
                    (real_plus h (real_plus sg h))
                    (real_plus (real_plus h sg) h)
                    (real_plus (real_plus sg h) h)
                    (real_plus_assoc h sg h)
                    (RealSetoid.real_eq_plus_compat (real_plus h sg) h
                       (real_plus sg h) h
                       (real_plus_comm h sg) (real_eq_refl h)))).
      * exact (RealSetoid.real_eq_plus_compat
                 gx (real_plus (real_plus sg h) h)
                 gx (real_plus sg (real_plus h h))
                 (real_eq_refl gx)
                 (real_eq_sym (real_plus sg (real_plus h h))
                    (real_plus (real_plus sg h) h)
                    (real_plus_assoc sg h h))).
    + apply (real_eq_trans
               (real_plus gx (real_plus sg (real_plus h h)))
               (real_plus gx (real_plus sg e))
               (real_plus (real_plus gx sg) e)).
      * exact (RealSetoid.real_eq_plus_compat
                 gx (real_plus sg (real_plus h h))
                 gx (real_plus sg e)
                 (real_eq_refl gx)
                 (RealSetoid.real_eq_plus_compat sg (real_plus h h) sg e
                    (real_eq_refl sg) Hh)).
      * apply real_plus_assoc.
Defined.

(* Slot: extensionality of the enumerated finite sum, real_eq face. *)
Theorem s6f9_sum_ext_csm : forall (S0 : Set) (en : list S0) (f g : S0 -> Real),
  (forall s : S0, real_eq (f s) (g s)) ->
  real_eq (csm_sumf S0 en f) (csm_sumf S0 en g).
Proof. intros S0 en f g H. exact (cms_sum_ext S0 en f g H). Defined.

(* Slot: additivity of the enumerated finite sum, real_plus face. *)
Theorem s6f9_sum_add_csm : forall (S0 : Set) (en : list S0) (f g : S0 -> Real),
  real_eq (csm_sumf S0 en (fun s : S0 => real_plus (f s) (g s)))
          (real_plus (csm_sumf S0 en f) (csm_sumf S0 en g)).
Proof. intros S0 en f g. exact (cms_sum_add S0 en f g). Defined.

(* Slot: Bishop monotonicity of the enumerated finite sum, per-eps face.
   Half of eps is pushed to each summand of the right side; the doubled
   half is moved back by s6f9_eps_split_move. *)
Theorem s6f9_sum_le_B_csm : forall (S0 : Set) (en : list S0) (f g : S0 -> Real),
  (forall s : S0, real_le_b (f s) (g s)) ->
  real_le_b (csm_sumf S0 en f) (csm_sumf S0 en g).
Proof.
  intros S0 en f g Hpt.
  unfold real_le_b, csm_sumf.
  induction en as [| x t IH].
  - intros eps Heps.
    exact (real_lt_plus_r_zero real_zero eps Heps).
  - intros eps Heps.
    specialize (Hpt x (uabS4c_half eps) (uabS4c_half_pos eps Heps)).
    specialize (IH (uabS4c_half eps) (uabS4c_half_pos eps Heps)).
    apply (RealSetoid.real_lt_id_r
             (real_plus (f x) (sumd_list_sum S0 f t))
             (real_plus (real_plus (g x) (uabS4c_half eps))
                        (real_plus (sumd_list_sum S0 g t) (uabS4c_half eps)))
             (real_plus (real_plus (g x) (sumd_list_sum S0 g t)) eps)).
    + exact (s6f9_eps_split_move (g x) (sumd_list_sum S0 g t)
               (uabS4c_half eps) eps (uabS4c_half_eq eps)).
    + exact (real_lt_plus_compat (f x) (real_plus (g x) (uabS4c_half eps))
               (sumd_list_sum S0 f t) (real_plus (sumd_list_sum S0 g t) (uabS4c_half eps))
               Hpt IH).
Defined.

Print Assumptions s6f9_eps_split_move.
Print Assumptions s6f9_sum_ext_csm.
Print Assumptions s6f9_sum_add_csm.
Print Assumptions s6f9_sum_le_B_csm.

Separate Extraction s6f9_eps_split_move s6f9_sum_ext_csm s6f9_sum_add_csm
  s6f9_sum_le_B_csm.
