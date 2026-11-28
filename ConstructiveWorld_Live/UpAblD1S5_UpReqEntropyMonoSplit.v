(* ========================================================================= *)
(* Module   : UpAblD1S5_UpReqEntropyMonoSplit                              *)
(* Mission. The twelve-slot entropy/KL monotonicity carrier pack of the     *)
(*   source Section EmsEntropyMonoSplit, re-homed as a Set-carried module:  *)
(*   one inductive record uabd1s5_ems_pack13 collects the twelve interface  *)
(*   slots (sum carrier, five sum laws, peak temperature pair, energy pin,  *)
(*   and the two eps-form KL growth/decay certificates around the peak)     *)
(*   plus one carrier-completeness field; the point-mass state space        *)
(*   (S := unit, sum := evaluation at tt, T_star := 1, energy := zero)      *)
(*   realizes every slot constructively, and the pack is inhabited by one   *)
(*   closed transparent term uabd1s5_ems_pack13_supplied.                   *)
(* Dependencies. Stdlib List; this development's landed chain S01_BaseRing, *)
(*   S02_CauchyComplete (Set Real carrier), S03_QExp through S15_TailFEPUp  *)
(*   (the Real-layer modules, incl. S07_RealSetoidExpLog congruences),      *)
(*   UpReqTempDefs (temperature family), UpReqEntropyDeficitTemp (KL).      *)
(* References. Source section EmsEntropyMonoSplit (slots S:90 through       *)
(*   Hkl_left:153-159); UpReqTempDefs Section RealTempDefs;                 *)
(*   UpReqEntropyDeficitTemp real_KL_temp :429.                             *)
(* Constructivity. Every statement face is Set-carried: Real : Set and      *)
(*   real_eq/real_lt/real_le are Set-valued (the S02 sigT/Or family, the    *)
(*   Real-layer counterpart of the QeqT/QltT carrier forms); no Prop atom   *)
(*   enters any statement or embedded pack field. The sole Type-sort        *)
(*   element is the pack constructor's universe field (forall S : Type),    *)
(*   a registered deviation (a Set-sorted inductive cannot take a           *)
(*   universe-sorted field) and the only possible Obj.magic site at         *)
(*   extraction. All exits Defined-transparent (zero Qed); zero axioms,     *)
(*   variables, admits; vm_compute unused.                                  *)
(* Build. coqc -native-compiler no -q -Q <development root> ""              *)
(*   UpAblD1S5_UpReqEntropyMonoSplit.v                                      *)
(* ========================================================================= *)

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
Require Import UpReqTempDefs.
Require Import UpReqEntropyDeficitTemp.

(* ============ Point-mass constants (the single-point instance) ============ *)

Definition uabd1s5_ems_sum : (unit -> Real) -> Real :=
  fun f : unit -> Real => f tt.

Definition uabd1s5_ems_sumpos
  : forall f : unit -> Real,
      (forall s : unit, real_lt real_zero (f s)) ->
      real_lt real_zero (uabd1s5_ems_sum f) :=
  fun (f : unit -> Real)
      (Hf : forall s : unit, real_lt real_zero (f s)) => Hf tt.

Definition uabd1s5_ems_energy : unit -> Real := fun _ : unit => real_zero.

(* ============ Explicit-argument re-forms of the source shorthand ============ *)
(* (delta-expanded bodies; the source Section Let block with the same      *)
(*  definitions under explicit names)                                      *)

Definition uabd1s5_ems_bt (S : Type)
  (sumf : (S -> Real) -> Real)
  (SUP : forall f : S -> Real,
           (forall s : S, real_lt real_zero (f s)) ->
           real_lt real_zero (sumf f))
  (energy : S -> Real) (t : Real) (Ht : real_lt real_zero t) (s : S) : Real :=
  real_boltzmann_dist_temp S sumf SUP t Ht energy s.

Definition uabd1s5_ems_btpos (S : Type)
  (sumf : (S -> Real) -> Real)
  (SUP : forall f : S -> Real,
           (forall s : S, real_lt real_zero (f s)) ->
           real_lt real_zero (sumf f))
  (energy : S -> Real) (t : Real) (Ht : real_lt real_zero t)
  : forall s : S, real_lt real_zero (uabd1s5_ems_bt S sumf SUP energy t Ht s) :=
  fun s : S => real_boltzmann_dist_temp_pos S sumf SUP t Ht energy s.

Definition uabd1s5_ems_et (S : Type)
  (sumf : (S -> Real) -> Real)
  (SUP : forall f : S -> Real,
           (forall s : S, real_lt real_zero (f s)) ->
           real_lt real_zero (sumf f))
  (energy : S -> Real) (t : Real) (Ht : real_lt real_zero t) : Real :=
  real_energy_exp_temp S sumf SUP t Ht energy.

Definition uabd1s5_ems_kl (S : Type)
  (sumf : (S -> Real) -> Real)
  (SUP : forall f : S -> Real,
           (forall s : S, real_lt real_zero (f s)) ->
           real_lt real_zero (sumf f))
  (energy : S -> Real) (t : Real) (Ht : real_lt real_zero t)
  (u : Real) (Hu : real_lt real_zero u) : Real :=
  real_KL_temp S sumf SUP t Ht energy
    (uabd1s5_ems_bt S sumf SUP energy u Hu)
    (uabd1s5_ems_btpos S sumf SUP energy u Hu).

(* ============ Mechanical one-step lemmas ============ *)

Lemma uabd1s5_ems_mult_one_l : forall x : Real,
  real_eq (real_mult real_one x) x.
Proof.
  intro x. exact (real_eq_trans _ _ _ (real_mult_comm real_one x) (real_mult_one x)).
Defined.

Lemma uabd1s5_ems_plus_zero_l : forall x : Real,
  real_eq (real_plus real_zero x) x.
Proof.
  intro x. exact (real_eq_trans _ _ _ (real_plus_comm real_zero x) (real_plus_zero x)).
Defined.

(* Point-mass Boltzmann distribution normalizes pointwise: p_t(tt) == 1
   (the partition collapses to the factor itself, then inv_pos_correct) *)
Lemma uabd1s5_ems_bt_one : forall (t : Real) (Ht : real_lt real_zero t),
  real_eq
    (uabd1s5_ems_bt unit uabd1s5_ems_sum uabd1s5_ems_sumpos uabd1s5_ems_energy
       t Ht tt)
    real_one.
Proof.
  intros t Ht.
  exact (real_eq_trans
           (uabd1s5_ems_bt unit uabd1s5_ems_sum uabd1s5_ems_sumpos
              uabd1s5_ems_energy t Ht tt)
           (real_mult
              (real_boltzmann_factor_temp unit t Ht uabd1s5_ems_energy tt)
              (real_inv_pos
                 (real_Z_temp unit uabd1s5_ems_sum t Ht uabd1s5_ems_energy)
                 (real_Z_temp_pos unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                    t Ht uabd1s5_ems_energy)))
           real_one
           (real_mult_comm
              (real_inv_pos
                 (real_Z_temp unit uabd1s5_ems_sum t Ht uabd1s5_ems_energy)
                 (real_Z_temp_pos unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                    t Ht uabd1s5_ems_energy))
              (real_boltzmann_factor_temp unit t Ht uabd1s5_ems_energy tt))
           (real_inv_pos_correct
              (real_Z_temp unit uabd1s5_ems_sum t Ht uabd1s5_ems_energy)
              (real_Z_temp_pos unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                 t Ht uabd1s5_ems_energy))).
Defined.

(* Point-mass peak-temperature KL vanishes pointwise: kl(t,u) == 0
   (bt_one feeds both log branches, then the additive group law) *)
Lemma uabd1s5_ems_kl_zero :
  forall (t u : Real) (Ht : real_lt real_zero t) (Hu : real_lt real_zero u),
    real_eq
      (uabd1s5_ems_kl unit uabd1s5_ems_sum uabd1s5_ems_sumpos uabd1s5_ems_energy
         t Ht u Hu)
      real_zero.
Proof.
  intros t u Ht Hu.
  assert (Hlu : real_eq
             (real_log
                (uabd1s5_ems_bt unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                   uabd1s5_ems_energy u Hu tt)
                (uabd1s5_ems_btpos unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                   uabd1s5_ems_energy u Hu tt))
             real_zero).
  { exact (real_eq_trans
             (real_log
                (uabd1s5_ems_bt unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                   uabd1s5_ems_energy u Hu tt)
                (uabd1s5_ems_btpos unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                   uabd1s5_ems_energy u Hu tt))
             (real_log real_one real_lt_zero_one)
             real_zero
             (real_log_wd
                (uabd1s5_ems_bt unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                   uabd1s5_ems_energy u Hu tt)
                real_one
                (uabd1s5_ems_btpos unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                   uabd1s5_ems_energy u Hu tt)
                real_lt_zero_one
                (uabd1s5_ems_bt_one u Hu))
             (real_log_one real_lt_zero_one)). }
  assert (Hlt2 : real_eq
              (real_log
                 (uabd1s5_ems_bt unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                    uabd1s5_ems_energy t Ht tt)
                 (uabd1s5_ems_btpos unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                    uabd1s5_ems_energy t Ht tt))
              real_zero).
  { exact (real_eq_trans
             (real_log
                (uabd1s5_ems_bt unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                   uabd1s5_ems_energy t Ht tt)
                (uabd1s5_ems_btpos unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                   uabd1s5_ems_energy t Ht tt))
             (real_log real_one real_lt_zero_one)
             real_zero
             (real_log_wd
                (uabd1s5_ems_bt unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                   uabd1s5_ems_energy t Ht tt)
                real_one
                (uabd1s5_ems_btpos unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                   uabd1s5_ems_energy t Ht tt)
                real_lt_zero_one
                (uabd1s5_ems_bt_one t Ht))
             (real_log_one real_lt_zero_one)). }
  apply (real_eq_trans
           (uabd1s5_ems_kl unit uabd1s5_ems_sum uabd1s5_ems_sumpos
              uabd1s5_ems_energy t Ht u Hu)
           (real_mult
              (uabd1s5_ems_bt unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                 uabd1s5_ems_energy u Hu tt)
              (real_plus
                 (real_log
                    (uabd1s5_ems_bt unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                       uabd1s5_ems_energy u Hu tt)
                    (uabd1s5_ems_btpos unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                       uabd1s5_ems_energy u Hu tt))
                 (real_opp
                    (real_log
                       (uabd1s5_ems_bt unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                          uabd1s5_ems_energy t Ht tt)
                       (uabd1s5_ems_btpos unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                          uabd1s5_ems_energy t Ht tt)))))
           real_zero).
  - exact (real_eq_refl
             (real_mult
                (uabd1s5_ems_bt unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                   uabd1s5_ems_energy u Hu tt)
                (real_plus
                   (real_log
                      (uabd1s5_ems_bt unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                         uabd1s5_ems_energy u Hu tt)
                      (uabd1s5_ems_btpos unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                         uabd1s5_ems_energy u Hu tt))
                   (real_opp
                      (real_log
                         (uabd1s5_ems_bt unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                            uabd1s5_ems_energy t Ht tt)
                         (uabd1s5_ems_btpos unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                            uabd1s5_ems_energy t Ht tt)))))).
  - exact (real_eq_trans
             (real_mult
                (uabd1s5_ems_bt unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                   uabd1s5_ems_energy u Hu tt)
                (real_plus
                   (real_log
                      (uabd1s5_ems_bt unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                         uabd1s5_ems_energy u Hu tt)
                      (uabd1s5_ems_btpos unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                         uabd1s5_ems_energy u Hu tt))
                   (real_opp
                      (real_log
                         (uabd1s5_ems_bt unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                            uabd1s5_ems_energy t Ht tt)
                         (uabd1s5_ems_btpos unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                            uabd1s5_ems_energy t Ht tt)))))
             (real_mult real_one
                (real_plus real_zero (real_opp real_zero)))
             real_zero
             (RealSetoid.real_eq_mult_compat_adapt
                (uabd1s5_ems_bt unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                   uabd1s5_ems_energy u Hu tt)
                real_one
                (real_plus
                   (real_log
                      (uabd1s5_ems_bt unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                         uabd1s5_ems_energy u Hu tt)
                      (uabd1s5_ems_btpos unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                         uabd1s5_ems_energy u Hu tt))
                   (real_opp
                      (real_log
                         (uabd1s5_ems_bt unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                            uabd1s5_ems_energy t Ht tt)
                         (uabd1s5_ems_btpos unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                            uabd1s5_ems_energy t Ht tt))))
                (real_plus real_zero (real_opp real_zero))
                (uabd1s5_ems_bt_one u Hu)
                (RealSetoid.real_eq_plus_compat_adapt
                   (real_log
                      (uabd1s5_ems_bt unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                         uabd1s5_ems_energy u Hu tt)
                      (uabd1s5_ems_btpos unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                         uabd1s5_ems_energy u Hu tt))
                   real_zero
                   (real_opp
                      (real_log
                         (uabd1s5_ems_bt unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                            uabd1s5_ems_energy t Ht tt)
                         (uabd1s5_ems_btpos unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                            uabd1s5_ems_energy t Ht tt)))
                   (real_opp real_zero)
                   Hlu
                   (RealSetoid.real_eq_opp_compat
                      (real_log
                         (uabd1s5_ems_bt unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                            uabd1s5_ems_energy t Ht tt)
                         (uabd1s5_ems_btpos unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                            uabd1s5_ems_energy t Ht tt))
                      real_zero
                      Hlt2)))
             (real_eq_trans
                (real_mult real_one (real_plus real_zero (real_opp real_zero)))
                (real_mult real_one real_zero)
                real_zero
                (RealSetoid.real_eq_mult_compat_adapt
                   real_one real_one
                   (real_plus real_zero (real_opp real_zero))
                   real_zero
                   (real_eq_refl real_one)
                   (real_plus_opp real_zero))
                (uabd1s5_ems_mult_one_l real_zero))).
Defined.

(* Energy pin at the point mass: both sides collapse to zero by mult_zero *)
Lemma uabd1s5_ems_Hpinned_leg :
  forall (u : Real) (Hu : real_lt real_zero u),
    real_eq
      (uabd1s5_ems_sum
         (fun s : unit =>
            real_mult
              (uabd1s5_ems_bt unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                 uabd1s5_ems_energy u Hu s)
              (uabd1s5_ems_energy s)))
      (uabd1s5_ems_et unit uabd1s5_ems_sum uabd1s5_ems_sumpos
         uabd1s5_ems_energy real_one real_lt_zero_one).
Proof.
  intros u Hu.
  exact (real_eq_trans
           (uabd1s5_ems_sum
              (fun s : unit =>
                 real_mult
                   (uabd1s5_ems_bt unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                      uabd1s5_ems_energy u Hu s)
                   (uabd1s5_ems_energy s)))
           real_zero
           (uabd1s5_ems_et unit uabd1s5_ems_sum uabd1s5_ems_sumpos
              uabd1s5_ems_energy real_one real_lt_zero_one)
           (real_mult_zero
              (uabd1s5_ems_bt unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                 uabd1s5_ems_energy u Hu tt))
           (real_eq_sym
              (uabd1s5_ems_et unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                 uabd1s5_ems_energy real_one real_lt_zero_one)
              real_zero
              (real_mult_zero
                 (uabd1s5_ems_bt unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                    uabd1s5_ems_energy real_one real_lt_zero_one tt)))).
Defined.

(* KL growth/decay certificates at the point mass: kl vanishes, so the
   eps inequalities reduce to real_zero <= eps via real_lt_compat *)
Lemma uabd1s5_ems_Hkl_right_leg :
  forall (u v : Real) (Hu : real_lt real_zero u) (Hv : real_lt real_zero v),
    real_le real_one u ->
    real_le u v ->
    forall eps : Real,
      real_lt real_zero eps ->
      real_le real_zero
        (real_plus
           (real_plus
              (uabd1s5_ems_kl unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                 uabd1s5_ems_energy real_one real_lt_zero_one v Hv)
              (real_opp
                 (uabd1s5_ems_kl unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                    uabd1s5_ems_energy real_one real_lt_zero_one u Hu)))
           eps).
Proof.
  intros u v Hu Hv _ _ eps Heps.
  exact (inl
           (RealSetoid.real_lt_compat
              real_zero real_zero
              eps
              (real_plus
                 (real_plus
                    (uabd1s5_ems_kl unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                       uabd1s5_ems_energy real_one real_lt_zero_one v Hv)
                    (real_opp
                       (uabd1s5_ems_kl unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                          uabd1s5_ems_energy real_one real_lt_zero_one u Hu)))
                 eps)
              (real_eq_refl real_zero)
              (real_eq_sym
                 (real_plus
                    (real_plus
                       (uabd1s5_ems_kl unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                          uabd1s5_ems_energy real_one real_lt_zero_one v Hv)
                       (real_opp
                          (uabd1s5_ems_kl unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                             uabd1s5_ems_energy real_one real_lt_zero_one u Hu)))
                    eps)
                 eps
                 (real_eq_trans
                    (real_plus
                       (real_plus
                          (uabd1s5_ems_kl unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                             uabd1s5_ems_energy real_one real_lt_zero_one v Hv)
                          (real_opp
                             (uabd1s5_ems_kl unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                                uabd1s5_ems_energy real_one real_lt_zero_one u Hu)))
                       eps)
                    (real_plus real_zero eps)
                    eps
                    (RealSetoid.real_eq_plus_compat_adapt
                       (real_plus
                          (uabd1s5_ems_kl unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                             uabd1s5_ems_energy real_one real_lt_zero_one v Hv)
                          (real_opp
                             (uabd1s5_ems_kl unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                                uabd1s5_ems_energy real_one real_lt_zero_one u Hu)))
                       real_zero
                       eps eps
                       (RealSetoid.real_eq_plus_compat_adapt
                          (uabd1s5_ems_kl unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                             uabd1s5_ems_energy real_one real_lt_zero_one v Hv)
                          real_zero
                          (real_opp
                             (uabd1s5_ems_kl unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                                uabd1s5_ems_energy real_one real_lt_zero_one u Hu))
                          (real_opp real_zero)
                          (uabd1s5_ems_kl_zero real_one v real_lt_zero_one Hv)
                          (RealSetoid.real_eq_opp_compat
                             (uabd1s5_ems_kl unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                                uabd1s5_ems_energy real_one real_lt_zero_one u Hu)
                             real_zero
                             (uabd1s5_ems_kl_zero real_one u real_lt_zero_one Hu)))
                       (real_eq_refl eps))
                    (uabd1s5_ems_plus_zero_l eps)))
              Heps)).
Defined.

Lemma uabd1s5_ems_Hkl_left_leg :
  forall (u v : Real) (Hu : real_lt real_zero u) (Hv : real_lt real_zero v),
    real_le u v ->
    real_le v real_one ->
    forall eps : Real,
      real_lt real_zero eps ->
      real_le real_zero
        (real_plus
           (real_plus
              (uabd1s5_ems_kl unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                 uabd1s5_ems_energy real_one real_lt_zero_one u Hu)
              (real_opp
                 (uabd1s5_ems_kl unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                    uabd1s5_ems_energy real_one real_lt_zero_one v Hv)))
           eps).
Proof.
  intros u v Hu Hv _ _ eps Heps.
  exact (inl
           (RealSetoid.real_lt_compat
              real_zero real_zero
              eps
              (real_plus
                 (real_plus
                    (uabd1s5_ems_kl unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                       uabd1s5_ems_energy real_one real_lt_zero_one u Hu)
                    (real_opp
                       (uabd1s5_ems_kl unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                          uabd1s5_ems_energy real_one real_lt_zero_one v Hv)))
                 eps)
              (real_eq_refl real_zero)
              (real_eq_sym
                 (real_plus
                    (real_plus
                       (uabd1s5_ems_kl unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                          uabd1s5_ems_energy real_one real_lt_zero_one u Hu)
                       (real_opp
                          (uabd1s5_ems_kl unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                             uabd1s5_ems_energy real_one real_lt_zero_one v Hv)))
                    eps)
                 eps
                 (real_eq_trans
                    (real_plus
                       (real_plus
                          (uabd1s5_ems_kl unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                             uabd1s5_ems_energy real_one real_lt_zero_one u Hu)
                          (real_opp
                             (uabd1s5_ems_kl unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                                uabd1s5_ems_energy real_one real_lt_zero_one v Hv)))
                       eps)
                    (real_plus real_zero eps)
                    eps
                    (RealSetoid.real_eq_plus_compat_adapt
                       (real_plus
                          (uabd1s5_ems_kl unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                             uabd1s5_ems_energy real_one real_lt_zero_one u Hu)
                          (real_opp
                             (uabd1s5_ems_kl unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                                uabd1s5_ems_energy real_one real_lt_zero_one v Hv)))
                       real_zero
                       eps eps
                       (RealSetoid.real_eq_plus_compat_adapt
                          (uabd1s5_ems_kl unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                             uabd1s5_ems_energy real_one real_lt_zero_one u Hu)
                          real_zero
                          (real_opp
                             (uabd1s5_ems_kl unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                                uabd1s5_ems_energy real_one real_lt_zero_one v Hv))
                          (real_opp real_zero)
                          (uabd1s5_ems_kl_zero real_one u real_lt_zero_one Hu)
                          (RealSetoid.real_eq_opp_compat
                             (uabd1s5_ems_kl unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                                uabd1s5_ems_energy real_one real_lt_zero_one v Hv)
                             real_zero
                             (uabd1s5_ems_kl_zero real_one v real_lt_zero_one Hv)))
                       (real_eq_refl eps))
                    (uabd1s5_ems_plus_zero_l eps)))
              Heps)).
Defined.

(* ============ The carrier pack: twelve slots plus one completeness field ============ *)

Inductive uabd1s5_ems_pack13 : Type :=
| uabd1s5_ems_pack13_intro :
    forall S : Type,
      forall real_sum_over_S : (S -> Real) -> Real,
        forall real_sum_pos_preserved :
          forall f : S -> Real,
            (forall s : S, real_lt real_zero (f s)) ->
            real_lt real_zero (real_sum_over_S f),
        (forall f g : S -> Real,
            (forall s : S, real_eq (f s) (g s)) ->
            real_eq (real_sum_over_S f) (real_sum_over_S g)) ->
        (forall f g : S -> Real,
            (forall s : S, real_le (f s) (g s)) ->
            real_le (real_sum_over_S f) (real_sum_over_S g)) ->
        (forall (a : Real) (f : S -> Real),
            real_eq (real_sum_over_S (fun s : S => real_mult a (f s)))
                    (real_mult a (real_sum_over_S f))) ->
        (forall f g : S -> Real,
            real_eq (real_sum_over_S (fun s : S => real_plus (f s) (g s)))
                    (real_plus (real_sum_over_S f) (real_sum_over_S g))) ->
        forall T_star : Real,
          forall T_star_pos : real_lt real_zero T_star,
          forall energy : S -> Real,
            (forall (u : Real) (Hu : real_lt real_zero u),
                real_eq
                  (real_sum_over_S
                     (fun s : S =>
                        real_mult
                          (uabd1s5_ems_bt S real_sum_over_S
                             real_sum_pos_preserved energy u Hu s)
                          (energy s)))
                  (uabd1s5_ems_et S real_sum_over_S
                     real_sum_pos_preserved energy T_star T_star_pos)) ->
            (forall (u v : Real) (Hu : real_lt real_zero u)
                    (Hv : real_lt real_zero v),
                real_le T_star u ->
                real_le u v ->
                forall eps : Real,
                  real_lt real_zero eps ->
                  real_le real_zero
                    (real_plus
                       (real_plus
                          (uabd1s5_ems_kl S real_sum_over_S
                             real_sum_pos_preserved energy T_star T_star_pos v Hv)
                          (real_opp
                             (uabd1s5_ems_kl S real_sum_over_S
                                real_sum_pos_preserved energy T_star T_star_pos
                                u Hu)))
                       eps)) ->
            (forall (u v : Real) (Hu : real_lt real_zero u)
                    (Hv : real_lt real_zero v),
                real_le u v ->
                real_le v T_star ->
                forall eps : Real,
                  real_lt real_zero eps ->
                  real_le real_zero
                    (real_plus
                       (real_plus
                          (uabd1s5_ems_kl S real_sum_over_S
                             real_sum_pos_preserved energy T_star T_star_pos u Hu)
                          (real_opp
                             (uabd1s5_ems_kl S real_sum_over_S
                                real_sum_pos_preserved energy T_star T_star_pos
                                v Hv)))
                       eps)) ->
            uabd1s5_ems_pack13.

(* ============ The pack inhabitant: one closed term, thirteen positions ============ *)

Theorem uabd1s5_ems_pack13_supplied : uabd1s5_ems_pack13.
Proof.
  exact (uabd1s5_ems_pack13_intro
           unit
           uabd1s5_ems_sum
           uabd1s5_ems_sumpos
           (fun (f g : unit -> Real)
                (H : forall s : unit, real_eq (f s) (g s)) => H tt)
           (fun (f g : unit -> Real)
                (H : forall s : unit, real_le (f s) (g s)) => H tt)
           (fun (a : Real) (f : unit -> Real) =>
              real_eq_refl (real_mult a (f tt)))
           (fun (f g : unit -> Real) =>
              real_eq_refl (real_plus (f tt) (g tt)))
           real_one
           real_lt_zero_one
           uabd1s5_ems_energy
           uabd1s5_ems_Hpinned_leg
           uabd1s5_ems_Hkl_right_leg
           uabd1s5_ems_Hkl_left_leg).
Defined.

(* ============ Assumption audit: one line per exit ============ *)

Print Assumptions uabd1s5_ems_mult_one_l.
Print Assumptions uabd1s5_ems_plus_zero_l.
Print Assumptions uabd1s5_ems_bt_one.
Print Assumptions uabd1s5_ems_kl_zero.
Print Assumptions uabd1s5_ems_Hpinned_leg.
Print Assumptions uabd1s5_ems_Hkl_right_leg.
Print Assumptions uabd1s5_ems_Hkl_left_leg.
Print Assumptions uabd1s5_ems_pack13_supplied.
