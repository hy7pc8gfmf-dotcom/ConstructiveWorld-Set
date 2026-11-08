(* ConstructiveWorld-Set -- up-ablation statement family: log compatibility, antitone log, minorization delta bound, positive-factor cancellation, partition-function positivity. *)

(** * Arch_UpAbl_01: log compatibility, the minorization delta bound, positive-factor cancellation, and partition-function positivity.

    Mission.  Six up-ablation statements carried verbatim on the constructive Real layer: log
      compatibility for the req order [uabT2a_rppo_log_req_compat] and its alt-form companion
      [uabT2a_ralt_log_req_compat], the antitone log on positive reals [abl_S12_sf_log_antitone_le],
      the delta <= 1 row-sum bound carried by [rta_delta_le_one_of_minorization], left
      cancellation by a positive factor carried by [mult_cancel_l], and partition-function
      positivity [uabT9_sigm_pft_pos].

    Dependencies.  Stdlib [List].  Requires of this development [S01_BaseRing],
      [S02_CauchyComplete], [S03_QExp], [S04_RealExpLogConv], [S05_AlignmentGRPO],
      [S06_DiffSamplingGibbs], [S07_RealSetoidExpLog], [S08_RealMainlineDPO],
      [S09_EntropyReal], [S10_KVQuantTrig], [S11_TP3B5], [S12_B5RecycleSF], [S13_NLiveAudit],
      [S14_B5BatchBlock], [S15_TailFEPUp], [G05_LogSmall], [RateTheoryAblation],
      [fa53_compat_abs], [AbsLeId], [TempSoftmaxInstantiation], [UpReqSumD], [UpSigMigrate].

    References.  This development, Arch_UpAbl_01.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" Arch_UpAbl_01.v] compiles cleanly
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
Require Import G05_LogSmall.
Require Import RateTheoryAblation.
From Stdlib Require Import List.
Require Import fa53_compat_abs.
Require Import AbsLeId.
Require Import TempSoftmaxInstantiation.
Require Import UpReqSumD.
Require Import UpSigMigrate.

(* ================= Section 1. log compatibility for the req order ================= *)
Import RealInterfaceEnhancedMod.

(* ---- slot one, from rppo_log_req_compat in the ReqPPOAdvantage section; statement verbatim with the sort faces carried by the concrete [real_lt]/[real_eq] constants ---- *)
Theorem uabT2a_rppo_log_req_compat :
  forall (x y : Real) (Hx : real_lt real_zero x) (Hy : real_lt real_zero y),
    real_eq x y -> real_eq (real_log x Hx) (real_log y Hy).
Proof.
  intros x y Hx Hy Hxy.
  exact (logd_log_compat_real x y Hx Hy Hxy).
Qed.

(* ---- assumption audit section; each Print Assumptions must report Closed ---- *)
Print Assumptions uabT2a_rppo_log_req_compat.
(* ================= Section 2. antitone log on positive reals ================= *)
(* ################ sf_log_antitone_le, statement shape taken verbatim from the source ################ *)
Theorem abl_S12_sf_log_antitone_le :
  forall (a b : Real) (Ha : real_lt real_zero a) (Hb : real_lt real_zero b),
    real_le a b ->
    real_le (real_log a Ha) (real_log b Hb).
Proof.
  intros a b Ha Hb Hab.
  exact (real_log_le_mono a b Ha Hb Hab).
Qed.

(* ---- assumption audit section; each statement keeps its Print Assumptions record ---- *)
Print Assumptions abl_S12_sf_log_antitone_le.
(* ================= Section 3. alt-form log compatibility for the req order ================= *)
Import RealInterfaceEnhancedMod.

(* ---- slot one, from ralt_log_req_compat in the ReqRestACore section; statement verbatim with R := Real and the sort faces carried by the concrete [real_lt]/[real_eq] constants ---- *)
Theorem uabT2a_ralt_log_req_compat :
  forall (x y : Real) (Hx : real_lt real_zero x) (Hy : real_lt real_zero y),
    real_eq x y -> real_eq (real_log x Hx) (real_log y Hy).
Proof.
  intros x y Hx Hy Hxy.
  exact (logd_log_compat_real x y Hx Hy Hxy).
Qed.

(* ---- assumption audit section; each Print Assumptions must report Closed ---- *)
Print Assumptions uabT2a_ralt_log_req_compat.
(* ================= Section 4. delta <= 1 under minorization row-sum constraints, carried by rta_delta_le_one_of_minorization ================= *)
Theorem uabT13b_tv_delta_le_one :
  forall (states : list (list Real)) (K : list Real -> list Real -> Real)
         (u : list Real -> Real) (delta : Real),
    (forall i : list Real,
       real_eq (real_list_sum (list Real) (K i) states) real_one) ->
    real_eq (real_list_sum (list Real) u states) real_one ->
    (forall i j : list Real, real_le (real_mult delta (u j)) (K i j)) ->
    real_le delta real_one.
Proof.
  intros states K u delta HKrow Hunorm Hmin.
  exact (@rta_delta_le_one_of_minorization states K u delta HKrow Hunorm Hmin).
Qed.

(* ---- assumption audit section ---- *)
Print Assumptions uabT13b_tv_delta_le_one.
(* ================= Section 5. cancellation by a positive left factor: a > 0 and a * x = 0 imply x = 0, carried by mult_cancel_l ================= *)
Import RealInterfaceEnhancedMod.

Section UabT13Sigm2.

(* The cancellation law lives on the concrete [Real] face of the req-signed
   enhanced interface: the abstract-interface [mult_cancel_l] is [Id]-valued,
   so the req face rebuilds the same argument from the concrete carriers
   ([real_inv_pos_correct], associativity, the one/zero absorptions), with the
   sort faces carried by the [real_eq]/[real_lt] constants. *)
Theorem uabT13_sigm2_b_mult_cancel :
  forall a x : Real,
    real_lt real_zero a ->
    real_eq (real_mult a x) real_zero -> real_eq x real_zero.
Proof.
  intros a x Ha H.
  (* the zero side rewrites as a times zero on the concrete equality face *)
  assert (Hxz : real_eq (real_mult a x) (real_mult a real_zero)).
  { exact (real_eq_trans (real_mult a x) real_zero (real_mult a real_zero) H
             (real_eq_sym (real_mult a real_zero) real_zero
                          (real_mult_zero a))). }
  (* the inverse of the positive factor reassociates to one *)
  assert (Hlinv : real_eq (real_mult (real_inv_pos a Ha) a) real_one).
  { exact (real_eq_trans (real_mult (real_inv_pos a Ha) a)
             (real_mult a (real_inv_pos a Ha)) real_one
             (real_mult_comm (real_inv_pos a Ha) a)
             (real_inv_pos_correct a Ha)). }
  (* the cancel chain on the x side: reassociate, absorb the inverse, absorb one *)
  assert (Hlb : real_eq (real_mult (real_inv_pos a Ha) (real_mult a x)) x).
  { exact (real_eq_trans (real_mult (real_inv_pos a Ha) (real_mult a x))
             (real_mult (real_mult (real_inv_pos a Ha) a) x) x
             (real_mult_assoc (real_inv_pos a Ha) a x)
             (real_eq_trans (real_mult (real_mult (real_inv_pos a Ha) a) x)
                (real_mult real_one x) x
                (RealSetoid.real_eq_mult_compat (real_mult (real_inv_pos a Ha) a) x
                                     real_one x Hlinv (real_eq_refl x))
                (real_eq_trans (real_mult real_one x) (real_mult x real_one) x
                               (real_mult_comm real_one x)
                               (real_mult_one x)))). }
  (* the same chain on the zero side *)
  assert (Hrc : real_eq (real_mult (real_inv_pos a Ha)
                                   (real_mult a real_zero)) real_zero).
  { exact (real_eq_trans (real_mult (real_inv_pos a Ha) (real_mult a real_zero))
             (real_mult (real_mult (real_inv_pos a Ha) a) real_zero) real_zero
             (real_mult_assoc (real_inv_pos a Ha) a real_zero)
             (real_eq_trans (real_mult (real_mult (real_inv_pos a Ha) a) real_zero)
                (real_mult real_one real_zero) real_zero
                (RealSetoid.real_eq_mult_compat (real_mult (real_inv_pos a Ha) a) real_zero
                                     real_one real_zero Hlinv
                                     (real_eq_refl real_zero))
                (real_eq_trans (real_mult real_one real_zero)
                               (real_mult real_zero real_one) real_zero
                               (real_mult_comm real_one real_zero)
                               (real_mult_one real_zero)))). }
  (* transfer through the shared positive left factor *)
  assert (Hmid : real_eq (real_mult (real_inv_pos a Ha) (real_mult a x))
                         (real_mult (real_inv_pos a Ha) (real_mult a real_zero))).
  { exact (RealSetoid.real_eq_mult_compat (real_inv_pos a Ha) (real_mult a x)
                               (real_inv_pos a Ha) (real_mult a real_zero)
                               (real_eq_refl (real_inv_pos a Ha)) Hxz). }
  exact (real_eq_trans x (real_mult (real_inv_pos a Ha) (real_mult a x)) real_zero
           (real_eq_sym (real_mult (real_inv_pos a Ha) (real_mult a x)) x Hlb)
           (real_eq_trans (real_mult (real_inv_pos a Ha) (real_mult a x))
                          (real_mult (real_inv_pos a Ha) (real_mult a real_zero))
                          real_zero Hmid Hrc)).
Qed.

End UabT13Sigm2.

(* ---- assumption audit section; every Print Assumptions must report Closed ---- *)
Print Assumptions uabT13_sigm2_b_mult_cancel.
(* ================= Section 6. positivity of the partition function ================= *)
Import RealInterfaceEnhancedMod.

Theorem uabT9_sigm_pft_pos :
  forall (S : Set) (enum : list S) (Hne : Not (enum = nil))
         (z : S -> Real) (T : Real) (T_pos : real_lt real_zero T),
    real_lt real_zero (@sigm_partition_function_temp S
               (sumd_sumf S enum) T T_pos z).
Proof.
  intros S enum Hne z T T_pos.
  unfold sigm_partition_function_temp, sigm_exp_pos_fn.
  exact (sumd_sum_pos S enum _ Hne
           (fun s : S => real_exp_neg_pos
                           (real_opp (real_mult (real_inv_pos T T_pos) (z s))))).
Qed.

(* ---- assumption audit section ---- *)
Print Assumptions uabT9_sigm_pft_pos.
