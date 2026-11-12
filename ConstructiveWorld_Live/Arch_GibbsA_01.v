(* ==========================================================================)
   Arch_GibbsA_01.v -- statement-family aggregation and instantiated
   carriers.
   Mission. this file formalizes the statement family gK, gdst, gomd,
   pi_boltzmann, ga_pi_boltzmann_norm, ga_boltzmann_fixed, ga_titer_fixed,
   ga_attractor_contraction, ga2_rt.
   Dependencies. the library modules listed in this file's Require
   declarations.
   References. UpTVDoeblin (TVDStar variable face, tvd_K / tvd_dstar /
   tv_titer iterator), UpReqSteadyThermo (RealThermoSteady carrier slots,
   steady-state chain), UpReqAlign2 (Req2AlignCore summation interface;
   this world's req2_pos_dist/req2_rel_ent at lines 96/108), UpReqPPOPlain
   (rpl_sum_le shape), S04 (gibbs_pointwise), UpReqU2.v:359 (KLE slot
   statement, Main tree). interface alignment per SigMigrate_core
   precedent (field-wise Abbreviation vernacular, Notation shell
   removed): the Section GibbsAssembly binder pair
   (R : Set)(RIS : RealInterfaceEnhancedSetoid R) is adapted away to this
   world's argument-less RealInterfaceEnhancedSetoid on the global Real
   carrier (S07_RealSetoidExpLog.v:8696/9420), each consumed field
   anchored to its instance twin, the req2_* calls drop the binding
   arguments R RIS, statement names and proof bodies verbatim.
   Constructivity. every proof closes by Qed, zero outstanding proof
   obligations, no classical logic; statements carried at the Set level,
   zero Prop leakage.
   Build. Rocq 9.1, direct coqc -native-compiler no -q -Q . "" under the
   cpu_guard load cap; .vo magic [436f7121 000160bc].
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
Require Import UpTVDoeblin.
Require Import UpReqSteadyThermo.
Require Import UpReqAlgebra.
Require Import UpReqAlign2.

(* ================= section 1: the gK family ================= *)
(* Section GibbsAttr: a discrete state world + Gibbs kernel + a Boltzmann *)
(* carrier, the TVDStar variable face and the RealThermoSteady carrier    *)
(* slots joined in one section.                                           *)
Section GibbsAttr.

(* ---- the UpTVDoeblin TVDStar variable face ---- *)
Variable states : list (list Real).
Variable n_pos : real_lt real_zero (real_of_nat (length states)).
Variable Ttemp : Real.
Variable Ttemp_pos : real_lt real_zero Ttemp.
Variable gamma : Real.
Variable gamma_pos : real_lt real_zero gamma.
Variable z : list Real -> list Real -> Real.
Variable z_lo : forall i j : list Real, real_le (real_opp gamma) (z i j).
Variable z_hi : forall i j : list Real, real_le (z i j) gamma.

(* honest interface (the UpTVDoeblin same-position premise):
   |Σf| ≤ Σ|f| in the list form *)
Variable Labs : forall f : list Real -> Real,
  real_le (real_abs (real_list_sum (list Real) f states))
          (real_list_sum (list Real) (fun w : list Real => real_abs (f w)) states).

(* ---- the Gibbs kernel (the tvd_K instance) and the explicit rate
   (the tvd_dstar instance) ---- *)
Definition gK (i j : list Real) : Real :=
  tvd_K states n_pos Ttemp Ttemp_pos z i j.
Definition gdst : Real := tvd_dstar Ttemp Ttemp_pos gamma.
Definition gomd : Real := tv_omd (tvd_dstar Ttemp Ttemp_pos gamma).

(* ---- the UpReqSteadyThermo RealThermoSteady carrier slots ---- *)
Variable energy : list Real -> Real.
Variable Dcap : Real.
Variable Dcap_pos : real_lt real_zero Dcap.
Variable Zr : Real.
Variable Zr_pos : real_lt real_zero Zr.

(* Boltzmann distribution: the carrier instantiated on the list Real
   enumeration world *)
Definition pi_boltzmann : list Real -> Real :=
  real_boltzmann_prob (list Real) energy Dcap Dcap_pos Zr Zr_pos.

(* honest interface (first UpReqSteadyThermo same-position premise): the
   partition condition Z == Σ e^{−E/T}, the enumerated-sum instance form
   of real_partition_condition *)
Variable part_cond : real_eq Zr
  (real_list_sum (list Real)
     (fun s : list Real =>
        real_exp_neg (real_mult (real_inv_pos Dcap Dcap_pos) (energy s)))
     states).

(* honest interface (second UpReqSteadyThermo same-position premise):
   detailed balance with the kernel equal to the Gibbs kernel gK:
   π(s)·K(s,s') == π(s')·K(s',s), the instance form of
   real_detailed_balance *)
Variable dbalance : forall s s' : list Real,
  real_eq (real_mult (pi_boltzmann s) (gK s s'))
          (real_mult (pi_boltzmann s') (gK s' s)).

(* (1) π is a distribution: Σπ == 1, closed by instantiating the partition *)
(*   premise; the normalization piece of the UpReqSteadyThermo instance.   *)
Lemma ga_pi_boltzmann_norm :
  real_eq (real_list_sum (list Real) pi_boltzmann states) real_one.
Proof.
  apply (real_eq_trans
           (real_list_sum (list Real) pi_boltzmann states)
           (real_mult (real_inv_pos Zr Zr_pos)
              (real_list_sum (list Real)
                 (fun s : list Real =>
                    real_exp_neg
                      (real_mult (real_inv_pos Dcap Dcap_pos) (energy s)))
                 states))
           real_one).
  - (* Σ(inv Z·unnorm) == inv Z·Σ unnorm by real_list_sum_linear; the
       left side is termwise the Σπ defining sum, since pi_boltzmann is
       pointwise exactly that product term. *)
    exact (real_list_sum_linear (list Real) (real_inv_pos Zr Zr_pos)
             (fun s : list Real =>
                real_exp_neg (real_mult (real_inv_pos Dcap Dcap_pos) (energy s)))
             states).
  - apply (real_eq_trans
             (real_mult (real_inv_pos Zr Zr_pos)
                (real_list_sum (list Real)
                   (fun s : list Real =>
                      real_exp_neg
                        (real_mult (real_inv_pos Dcap Dcap_pos) (energy s)))
                   states))
             (real_mult (real_inv_pos Zr Zr_pos) Zr)
             real_one).
    + apply (RealSetoid.real_eq_mult_compat
               (real_inv_pos Zr Zr_pos)
               (real_list_sum (list Real)
                  (fun s : list Real =>
                     real_exp_neg
                       (real_mult (real_inv_pos Dcap Dcap_pos) (energy s)))
                  states)
               (real_inv_pos Zr Zr_pos) Zr
               (real_eq_refl (real_inv_pos Zr Zr_pos))
               (real_eq_sym _ _ part_cond)).
    + apply (real_eq_trans
               (real_mult (real_inv_pos Zr Zr_pos) Zr)
               (real_mult Zr (real_inv_pos Zr Zr_pos))
               real_one).
      * exact (real_mult_comm (real_inv_pos Zr Zr_pos) Zr).
      * exact (real_inv_pos_correct Zr Zr_pos).
Qed.

(* (2) a small connective piece: replaying the steady-state five-step    *)
(*   chain of the UpReqSteadyThermo instance on this carrier gives π a   *)
(*   fixed point of tv_step: Σ_{s'} π(s')·K(s',s) == π(s) pointwise, the *)
(*   fixed-point form of the UpTVDoeblin iterator.                       *)
Theorem ga_boltzmann_fixed : forall s : list Real,
  real_eq (tv_step states gK pi_boltzmann s) (pi_boltzmann s).
Proof.
  intro s.
  unfold tv_step.
  (* stage 1: exchange the axes by the pointwise detailed balance; the
     argument order (w s) follows the UpReqSteadyThermo binding order. *)
  assert (Hdb : forall w : list Real,
           real_eq (real_mult (pi_boltzmann w) (gK w s))
                   (real_mult (pi_boltzmann s) (gK s w))).
  { intro w. exact (dbalance w s). }
  (* stage 2: the extensional sum shell, real_list_sum_ext lifting the
     stage-1 pointwise form. *)
  assert (Hext : real_eq
           (real_list_sum (list Real)
              (fun w : list Real => real_mult (pi_boltzmann w) (gK w s)) states)
           (real_list_sum (list Real)
              (fun w : list Real => real_mult (pi_boltzmann s) (gK s w)) states)).
  { exact (real_list_sum_ext (list Real)
             (fun w : list Real => real_mult (pi_boltzmann w) (gK w s))
             (fun w : list Real => real_mult (pi_boltzmann s) (gK s w))
             states Hdb). }
  (* stage 3: linear extraction of π(s) by real_list_sum_linear. *)
  assert (Hlin : real_eq
           (real_list_sum (list Real)
              (fun w : list Real => real_mult (pi_boltzmann s) (gK s w)) states)
           (real_mult (pi_boltzmann s)
              (real_list_sum (list Real) (fun w : list Real => gK s w) states))).
  { exact (real_list_sum_linear (list Real) (pi_boltzmann s)
             (fun w : list Real => gK s w) states). }
  (* stage 4: kernel row normalization, tvd_K_row on the gK row form,
     read off directly up to delta/eta conversion. *)
  assert (Hnorm : real_eq
           (real_list_sum (list Real) (fun w : list Real => gK s w) states)
           real_one).
  { exact (tvd_K_row states n_pos Ttemp Ttemp_pos z s). }
  (* stage 5: the ext/linear chain joined, then π(s)·1 == π(s) closed on
     the diagonal by mult_compat. *)
  apply (real_eq_trans
           (real_list_sum (list Real)
              (fun w : list Real => real_mult (pi_boltzmann w) (gK w s)) states)
           (real_mult (pi_boltzmann s)
              (real_list_sum (list Real) (fun w : list Real => gK s w) states))
           (pi_boltzmann s)).
  - exact (real_eq_trans
             (real_list_sum (list Real)
                (fun w : list Real => real_mult (pi_boltzmann w) (gK w s)) states)
             (real_list_sum (list Real)
                (fun w : list Real => real_mult (pi_boltzmann s) (gK s w)) states)
             (real_mult (pi_boltzmann s)
                (real_list_sum (list Real) (fun w : list Real => gK s w) states))
             Hext Hlin).
  - apply (real_eq_trans
             (real_mult (pi_boltzmann s)
                (real_list_sum (list Real) (fun w : list Real => gK s w) states))
             (real_mult (pi_boltzmann s) real_one)
             (pi_boltzmann s)).
    + apply (RealSetoid.real_eq_mult_compat
               (pi_boltzmann s)
               (real_list_sum (list Real) (fun w : list Real => gK s w) states)
               (pi_boltzmann s) real_one
               (real_eq_refl (pi_boltzmann s)) Hnorm).
    + exact (real_mult_one (pi_boltzmann s)).
Qed.

(* (3) the fixed point propagates along the UpTVDoeblin iterator:         *)
(*   K·π == π gives Kⁿ·π == π, pointwise.                                 *)
Theorem ga_titer_fixed : forall (n : nat) (s : list Real),
  real_eq (tv_titer states gK n pi_boltzmann s) (pi_boltzmann s).
Proof.
  intro n. induction n as [| n IH]; intro s.
  - (* n = 0: tv_titer 0 π ≡ π, judgmentally. *)
    apply real_eq_refl.
  - (* n+1: tv_titer (S n) π ≡ tv_step (K, tv_titer n π); extensionality
       of the sum (the pointwise IH) plus the fixed-point premise close
       the two-step chain. *)
    apply (real_eq_trans
             (tv_step states gK (tv_titer states gK n pi_boltzmann) s)
             (tv_step states gK pi_boltzmann s)
             (pi_boltzmann s)).
    + unfold tv_step.
      apply (real_list_sum_ext (list Real)
               (fun i : list Real =>
                  real_mult (tv_titer states gK n pi_boltzmann i) (gK i s))
               (fun i : list Real => real_mult (pi_boltzmann i) (gK i s))
               states).
      intro i.
      apply (RealSetoid.real_eq_mult_compat
               (tv_titer states gK n pi_boltzmann i) (gK i s)
               (pi_boltzmann i) (gK i s)
               (IH i) (real_eq_refl (gK i s))).
    + exact (ga_boltzmann_fixed s).
Qed.

(* (4) main theorem: Gibbs/Boltzmann attractiveness, backing the          *)
(*   spec-file bound of the form TV(Kⁿ·μ, π) ≤ ω^k·TV(μ,π): for every n,  *)
(*   TV(Kⁿ·μ, π) ≤ (1 − e^{−2γ/T})ⁿ·TV(μ,π).                              *)
(*   proof = the UpTVDoeblin tvd_dstar_iter_contraction at ν := π, plus   *)
(*   the fixed-point propagation of (3), plus pointwise extensional       *)
(*   transport of the TV functional.                                      *)
Theorem ga_attractor_contraction : forall (n : nat) (mu : list Real -> Real),
  real_eq (real_list_sum (list Real) mu states) real_one ->
  real_le (tv_doeblin states (tv_titer states gK n mu) pi_boltzmann)
          (real_mult (tv_rpow gomd n) (tv_doeblin states mu pi_boltzmann)).
Proof.
  intros n mu Hmu.
  (* step 1: transport of the TV functional; the second slot Kⁿ·π is
     replaced by π (pointwise abs extensionality). *)
  assert (HeqTV : real_eq
           (tv_doeblin states (tv_titer states gK n mu) pi_boltzmann)
           (tv_doeblin states (tv_titer states gK n mu)
                       (tv_titer states gK n pi_boltzmann))).
  { unfold tv_doeblin.
    apply (RealSetoid.real_eq_mult_compat
             tv_half
             (real_list_sum (list Real)
                (fun s : list Real =>
                   real_abs
                     (real_minus_r (tv_titer states gK n mu s)
                                   (pi_boltzmann s)))
                states)
             tv_half
             (real_list_sum (list Real)
                (fun s : list Real =>
                   real_abs
                     (real_minus_r (tv_titer states gK n mu s)
                                   (tv_titer states gK n pi_boltzmann s)))
                states)
             (real_eq_refl tv_half)
             (real_list_sum_ext (list Real)
                (fun s : list Real =>
                   real_abs
                     (real_minus_r (tv_titer states gK n mu s)
                                   (pi_boltzmann s)))
                (fun s : list Real =>
                   real_abs
                     (real_minus_r (tv_titer states gK n mu s)
                                   (tv_titer states gK n pi_boltzmann s)))
                states
                (fun s : list Real =>
                   RealSetoid.real_eq_abs_compat
                     (real_minus_r (tv_titer states gK n mu s)
                                   (pi_boltzmann s))
                     (real_minus_r (tv_titer states gK n mu s)
                                   (tv_titer states gK n pi_boltzmann s))
                     (tvd_eq_minus_compat
                        (tv_titer states gK n mu s)
                        (tv_titer states gK n mu s)
                        (pi_boltzmann s)
                        (tv_titer states gK n pi_boltzmann s)
                        (real_eq_refl (tv_titer states gK n mu s))
                        (real_eq_sym _ _ (ga_titer_fixed n s)))))). }
  (* step 2: the UpTVDoeblin main theorem instantiated at ν := π, linked
     through step 1. *)
  apply (real_le_trans
           (tv_doeblin states (tv_titer states gK n mu) pi_boltzmann)
           (tv_doeblin states (tv_titer states gK n mu)
                       (tv_titer states gK n pi_boltzmann))
           (real_mult (tv_rpow gomd n) (tv_doeblin states mu pi_boltzmann))).
  - apply (RealSetoid.real_eq_le _ _). exact HeqTV.
  - exact (tvd_dstar_iter_contraction
             states n_pos Ttemp Ttemp_pos gamma gamma_pos z z_lo z_hi
             Labs n mu pi_boltzmann Hmu ga_pi_boltzmann_norm).
Qed.

End GibbsAttr.

(* audit ports (>= 1, all expected Closed): *)
Print Assumptions ga_boltzmann_fixed.
Print Assumptions ga_titer_fixed.
Print Assumptions ga_attractor_contraction.
(* ================= section 2: the ga2_rt family ================= *)
Import RealInterfaceEnhancedMod.
(* interface alignment per SigMigrate_core precedent (field-wise
   Abbreviation vernacular, Notation shell removed): this tree's
   RealInterfaceEnhancedSetoid is the argument-less Class on the global
   Real carrier (S07_RealSetoidExpLog.v:8696) with the global Instance
   RealEnhancedReal, so the Main-tree binder pair
   Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}. is removed;
   each consumed interface field is anchored by a transparent
   abbreviation to the concrete twin assigned by that instance
   (S07_RealSetoidExpLog.v:9420ff), so the statement face elaborates on
   the concrete real_* operations and extracts Obj.magic-free.  the
   req2_* calls drop the binding arguments R RIS accordingly;
   statement names and proof bodies are verbatim unchanged apart from
   the dropped binding arguments. *)
Abbreviation R := Real.
Abbreviation req := real_eq.
Abbreviation req_refl := real_eq_refl.
Abbreviation req_sym := real_eq_sym.
Abbreviation req_trans := real_eq_trans.
Abbreviation zero := real_zero.
Abbreviation one := real_one.
Abbreviation plus := real_plus.
Abbreviation mult := real_mult.
Abbreviation opp := real_opp.
Abbreviation lt := real_lt.
Abbreviation le := real_le.
Abbreviation req_plus_compat := RealSetoid.real_eq_plus_compat_adapt.
Abbreviation req_mult_compat := RealSetoid.real_eq_mult_compat_adapt.
Abbreviation req_opp_compat := RealSetoid.real_eq_opp_compat.
Abbreviation plus_assoc := real_plus_assoc.
Abbreviation plus_comm := real_plus_comm.
Abbreviation plus_zero := real_plus_zero.
Abbreviation plus_opp := real_plus_opp.
Abbreviation mult_assoc := real_mult_assoc.
Abbreviation mult_one := real_mult_one.
Abbreviation distrib := real_distrib.
Abbreviation le_refl := real_le_refl.
Abbreviation le_id_l := RealSetoid.real_le_id_l.
Abbreviation le_id_r := RealSetoid.real_le_id_r.
Abbreviation lt_le_iff := RealSetoid.real_lt_le_iff_req.
Abbreviation inv_pos := real_inv_pos.
Abbreviation inv_pos_correct := real_inv_pos_correct.
Abbreviation one_pos := real_lt_zero_one.
Abbreviation le_plus_compat := real_le_plus_compat.
Abbreviation mult_positive := real_mult_positive.
Abbreviation opp_le_compat := real_opp_le_compat.
Abbreviation inv_pos_pos := real_inv_pos_pos.
Abbreviation log := real_log.
Abbreviation log_mult := real_log_mult.
Abbreviation log_one := real_log_one.
Abbreviation log_le_linear_eps :=
  (fun x Hx eps Hepspos => real_log_le_linear_eps x eps Hx Hepspos).

Section GibbsAssembly.

Variable S : Set.

(* ---- summation interface (same position as UpReqAlign2 Req2AlignCore;  *)
(*   this file uses ext/add/linear plus the le-monotone slot ga2_sum_le,  *)
(*   of the UpReqPPOPlain rpl_sum_le shape). sum_pos and                  *)
(*   log_inv_exp_neg_req stay unused, an honest pruning declared on the   *)
(*   section binder face. note: the original UpReqAlign2 section has no   *)
(*   le-monotone slot; this file adds the slot, supplied by the instance  *)
(*   side at use time.                                                    *)
Variable sumf : (S -> R) -> R.
Hypothesis ga2_sum_ext :
  forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g).
Hypothesis ga2_sum_add :
  forall f g : S -> R,
    req (sumf (fun s => plus (f s) (g s))) (plus (sumf f) (sumf g)).
Hypothesis ga2_sum_linear :
  forall (a : R) (f : S -> R),
    req (sumf (fun s => mult a (f s))) (mult a (sumf f)).
Hypothesis ga2_sum_le :
  forall f g : S -> R, (forall s : S, le (f s) (g s)) -> le (sumf f) (sumf g).
Hypothesis ga2_log_req_compat :
  forall (x y : R) (Hx : lt zero x) (Hy : lt zero y),
    req x y -> req (log x Hx) (log y Hy).

(* ---- in-section combinators, implicit-argument form to dodge the
   elaborator placeholder-order pitfall ---- *)
Definition ga2_rt {x y z : R} (H1 : req x y) (H2 : req y z) : req x z :=
  req_trans x y z H1 H2.
Definition ga2_le_id_l {a b c : R} (H1 : req a b) (H2 : le b c) : le a c :=
  le_id_l a b c H1 H2.
Definition ga2_le_id_r {a b c : R} (H1 : req b c) (H2 : le a b) : le a c :=
  le_id_r a b c H1 H2.

(* ---- in-section auxiliary 1: normalization of the opp one product, the
   two steps req_opp_mult_r + mult_one ---- *)
Lemma ga2_mopp_one : forall x : R, req (mult (opp one) x) (opp x).
Proof.
  intro x.
  assert (H1 : req (mult (opp one) x) (opp (mult one x))).
  { exact (req_opp_mult_r one x). }
  assert (H2 : req (mult one x) x).
  { exact (req_mult_one_l x). }
  assert (H3 : req (opp (mult one x)) (opp x)).
  { exact (req_opp_compat (mult one x) x H2). }
  exact (req_trans (mult (opp one) x) (opp (mult one x)) (opp x) H1 H3).
Qed.

(* ---- in-section auxiliary 2 (the pointwise kernel, the req2-face       *)
(*   replay of the S04 gibbs_pointwise inequality):                       *)
(*   p·(1 − q/p − eps) ≤ p·(log p − log q), pointwise in s.               *)
Lemma ga2_ptw_le :
  forall (p q : S -> R) (eps : R) (s : S)
         (Hps : lt zero (p s)) (Hqs : lt zero (q s)),
    lt zero eps ->
    le (plus (p s) (opp (plus (q s) (mult (p s) eps))))
       (mult (p s) (req_minus (log (p s) Hps) (log (q s) Hqs))).
Proof.
  intros p q eps s Hps Hqs Heps.
  assert (Htan : le (log (mult (q s) (inv_pos (p s) Hps))
                          (mult_positive (q s) (inv_pos (p s) Hps) Hqs (inv_pos_pos (p s) Hps)))
                    (plus (plus (mult (q s) (inv_pos (p s) Hps)) (opp one)) eps))
    by exact (log_le_linear_eps (mult (q s) (inv_pos (p s) Hps))
                 (mult_positive (q s) (inv_pos (p s) Hps) Hqs (inv_pos_pos (p s) Hps))
                 eps Heps).
  assert (Hlm : req (log (mult (q s) (inv_pos (p s) Hps))
                         (mult_positive (q s) (inv_pos (p s) Hps) Hqs (inv_pos_pos (p s) Hps)))
                    (plus (log (q s) Hqs) (log (inv_pos (p s) Hps) (inv_pos_pos (p s) Hps))))
    by exact (log_mult (q s) (inv_pos (p s) Hps) Hqs (inv_pos_pos (p s) Hps)).
  (* log(1/p) ≡ −log p: normalization by inv_pos_correct, change of the
     log argument, then cancellation. *)
  assert (Hlip : req (log (inv_pos (p s) Hps) (inv_pos_pos (p s) Hps))
                     (opp (log (p s) Hps))).
  { assert (Ha : req (log (mult (p s) (inv_pos (p s) Hps))
                          (mult_positive (p s) (inv_pos (p s) Hps) Hps (inv_pos_pos (p s) Hps)))
                     (plus (log (p s) Hps) (log (inv_pos (p s) Hps) (inv_pos_pos (p s) Hps))))
      by exact (log_mult (p s) (inv_pos (p s) Hps) Hps (inv_pos_pos (p s) Hps)).
    assert (Hb : req (log (mult (p s) (inv_pos (p s) Hps))
                          (mult_positive (p s) (inv_pos (p s) Hps) Hps (inv_pos_pos (p s) Hps)))
                     (log one one_pos))
      by exact (ga2_log_req_compat (mult (p s) (inv_pos (p s) Hps)) one
                 (mult_positive (p s) (inv_pos (p s) Hps) Hps (inv_pos_pos (p s) Hps))
                 one_pos (inv_pos_correct (p s) Hps)).
    assert (Hc : req (log one one_pos) zero) by exact (log_one one_pos).
    assert (Hd : req (plus (log (p s) Hps)
                           (log (inv_pos (p s) Hps) (inv_pos_pos (p s) Hps))) zero)
      by exact (ga2_rt
                  (req_sym (log (mult (p s) (inv_pos (p s) Hps))
                              (mult_positive (p s) (inv_pos (p s) Hps) Hps
                                (inv_pos_pos (p s) Hps)))
                           (plus (log (p s) Hps)
                                 (log (inv_pos (p s) Hps) (inv_pos_pos (p s) Hps)))
                           Ha)
                  (ga2_rt Hb Hc)).
    exact (req_plus_inv_unique (log (p s) Hps)
             (log (inv_pos (p s) Hps) (inv_pos_pos (p s) Hps))
             (opp (log (p s) Hps)) Hd (plus_opp (log (p s) Hps))). }
  assert (Hstep3 : req (log (mult (q s) (inv_pos (p s) Hps))
                            (mult_positive (q s) (inv_pos (p s) Hps) Hqs (inv_pos_pos (p s) Hps)))
                       (plus (log (q s) Hqs) (opp (log (p s) Hps))))
    by exact (ga2_rt Hlm
              (req_plus_compat (log (q s) Hqs) (log (q s) Hqs)
                (log (inv_pos (p s) Hps) (inv_pos_pos (p s) Hps)) (opp (log (p s) Hps))
                (req_refl (log (q s) Hqs)) Hlip)).
  assert (H4 : le (plus (log (q s) Hqs) (opp (log (p s) Hps)))
                  (plus (plus (mult (q s) (inv_pos (p s) Hps)) (opp one)) eps))
    by exact (ga2_le_id_l
                (req_sym (log (mult (q s) (inv_pos (p s) Hps))
                            (mult_positive (q s) (inv_pos (p s) Hps) Hqs
                              (inv_pos_pos (p s) Hps)))
                         (plus (log (q s) Hqs) (opp (log (p s) Hps)))
                         Hstep3)
                Htan).
  assert (H5 : le (opp (plus (plus (mult (q s) (inv_pos (p s) Hps)) (opp one)) eps))
                  (opp (plus (log (q s) Hqs) (opp (log (p s) Hps)))))
    by exact (opp_le_compat (plus (log (q s) Hqs) (opp (log (p s) Hps)))
                            (plus (plus (mult (q s) (inv_pos (p s) Hps)) (opp one)) eps)
                            H4).
  (* right-arm shape normalization:
     opp (plus (log q) (opp (log p))) ≡ req_minus (log p) (log q) *)
  assert (H6 : req (opp (plus (log (q s) Hqs) (opp (log (p s) Hps))))
                   (req_minus (log (p s) Hps) (log (q s) Hqs))).
  { assert (r1 : req (opp (plus (log (q s) Hqs) (opp (log (p s) Hps))))
                     (plus (opp (log (q s) Hqs)) (opp (opp (log (p s) Hps)))))
      by exact (req_opp_plus (log (q s) Hqs) (opp (log (p s) Hps))).
    assert (r2 : req (plus (opp (log (q s) Hqs)) (opp (opp (log (p s) Hps))))
                     (plus (opp (log (q s) Hqs)) (log (p s) Hps)))
      by exact (req_plus_compat (opp (log (q s) Hqs)) (opp (log (q s) Hqs))
                (opp (opp (log (p s) Hps))) (log (p s) Hps)
                (req_refl (opp (log (q s) Hqs))) (req_double_neg (log (p s) Hps))).
    assert (r3 : req (plus (opp (log (q s) Hqs)) (log (p s) Hps))
                     (plus (log (p s) Hps) (opp (log (q s) Hqs))))
      by exact (plus_comm (opp (log (q s) Hqs)) (log (p s) Hps)).
    exact (ga2_rt (ga2_rt r1 r2) r3). }
  assert (H7 : le (opp (plus (plus (mult (q s) (inv_pos (p s) Hps)) (opp one)) eps))
                  (req_minus (log (p s) Hps) (log (q s) Hqs)))
    by exact (ga2_le_id_r H6 H5).
  assert (Hle0 : le zero (p s)) by exact (lt_le_iff zero (p s) (inl Hps)).
  assert (H8 : le (mult (p s) (opp (plus (plus (mult (q s) (inv_pos (p s) Hps)) (opp one)) eps)))
                  (mult (p s) (req_minus (log (p s) Hps) (log (q s) Hqs))))
    by exact (req_le_mult_compat_r (p s) _ _ Hle0 H7).
  (* left-arm value normalization:
     p·opp(1 − q/p + eps) ≡ plus p (opp (plus q (p·eps))), via
     inv_pos_correct reducing q/p·p = q and the distrib/opp algebra in
     req *)
  assert (H9 : req (mult (p s) (opp (plus (plus (mult (q s) (inv_pos (p s) Hps)) (opp one)) eps)))
                   (plus (p s) (opp (plus (q s) (mult (p s) eps))))).
  { assert (d1 : req (plus (plus (mult (q s) (inv_pos (p s) Hps)) (opp one)) eps)
                     (plus (mult (q s) (inv_pos (p s) Hps)) (plus (opp one) eps)))
      by exact (req_sym (plus (mult (q s) (inv_pos (p s) Hps)) (plus (opp one) eps))
                        (plus (plus (mult (q s) (inv_pos (p s) Hps)) (opp one)) eps)
                        (plus_assoc (mult (q s) (inv_pos (p s) Hps)) (opp one) eps)).
    assert (c1 : req (mult (p s) (plus (plus (mult (q s) (inv_pos (p s) Hps)) (opp one)) eps))
                     (plus (mult (p s) (mult (q s) (inv_pos (p s) Hps)))
                           (mult (p s) (plus (opp one) eps))))
      by exact (ga2_rt
                (req_mult_compat (p s) (p s)
                  (plus (plus (mult (q s) (inv_pos (p s) Hps)) (opp one)) eps)
                  (plus (mult (q s) (inv_pos (p s) Hps)) (plus (opp one) eps))
                  (req_refl (p s)) d1)
                (distrib (p s) (mult (q s) (inv_pos (p s) Hps)) (plus (opp one) eps))).
    assert (c2 : req (mult (p s) (mult (q s) (inv_pos (p s) Hps))) (q s)).
    { exact (ga2_rt (mult_assoc (p s) (q s) (inv_pos (p s) Hps))
              (ga2_rt (req_mult_compat (mult (p s) (q s)) (mult (q s) (p s))
                         (inv_pos (p s) Hps) (inv_pos (p s) Hps)
                         (req_mult_comm_rewrite (p s) (q s))
                         (req_refl (inv_pos (p s) Hps)))
                (ga2_rt (req_sym (mult (q s) (mult (p s) (inv_pos (p s) Hps)))
                                 (mult (mult (q s) (p s)) (inv_pos (p s) Hps))
                                 (mult_assoc (q s) (p s) (inv_pos (p s) Hps)))
                  (ga2_rt (req_mult_compat (q s) (q s)
                             (mult (p s) (inv_pos (p s) Hps)) one
                             (req_refl (q s)) (inv_pos_correct (p s) Hps))
                    (mult_one (q s)))))). }
    assert (c3 : req (mult (p s) (plus (opp one) eps)) (plus (opp (p s)) (mult (p s) eps))).
    { assert (m1 : req (mult (p s) (opp one)) (opp (p s)))
        by exact (ga2_rt (req_opp_mult_l (p s) one)
                  (req_opp_compat (mult (p s) one) (p s) (mult_one (p s)))).
      exact (ga2_rt (distrib (p s) (opp one) eps)
              (req_plus_compat (mult (p s) (opp one)) (opp (p s))
                (mult (p s) eps) (mult (p s) eps) m1 (req_refl (mult (p s) eps)))). }
    assert (t2 : req (mult (p s) (plus (plus (mult (q s) (inv_pos (p s) Hps)) (opp one)) eps))
                     (plus (q s) (plus (opp (p s)) (mult (p s) eps))))
      by exact (ga2_rt c1
                (ga2_rt
                  (req_plus_compat (mult (p s) (mult (q s) (inv_pos (p s) Hps))) (q s)
                    (mult (p s) (plus (opp one) eps)) (mult (p s) (plus (opp one) eps))
                    c2 (req_refl (mult (p s) (plus (opp one) eps))))
                  (req_plus_compat (q s) (q s)
                    (mult (p s) (plus (opp one) eps)) (plus (opp (p s)) (mult (p s) eps))
                    (req_refl (q s)) c3))).
    assert (c5 : req (mult (p s) (opp (plus (plus (mult (q s) (inv_pos (p s) Hps)) (opp one)) eps)))
                     (opp (mult (p s) (plus (mult (q s) (inv_pos (p s) Hps)) (plus (opp one) eps)))))
      by exact (ga2_rt
                (req_opp_mult_l (p s) (plus (plus (mult (q s) (inv_pos (p s) Hps)) (opp one)) eps))
                (req_opp_compat (mult (p s) (plus (plus (mult (q s) (inv_pos (p s) Hps)) (opp one)) eps))
                  (mult (p s) (plus (mult (q s) (inv_pos (p s) Hps)) (plus (opp one) eps)))
                  (req_mult_compat (p s) (p s)
                    (plus (plus (mult (q s) (inv_pos (p s) Hps)) (opp one)) eps)
                    (plus (mult (q s) (inv_pos (p s) Hps)) (plus (opp one) eps))
                    (req_refl (p s)) d1))).
    assert (c6 : req (opp (plus (q s) (plus (opp (p s)) (mult (p s) eps))))
                     (plus (p s) (opp (plus (q s) (mult (p s) eps))))).
    { assert (v1 : req (opp (plus (q s) (plus (opp (p s)) (mult (p s) eps))))
                       (plus (opp (q s)) (opp (plus (opp (p s)) (mult (p s) eps)))))
        by exact (req_opp_plus (q s) (plus (opp (p s)) (mult (p s) eps))).
      assert (v2 : req (opp (plus (opp (p s)) (mult (p s) eps)))
                       (plus (opp (opp (p s))) (opp (mult (p s) eps))))
        by exact (req_opp_plus (opp (p s)) (mult (p s) eps)).
      assert (v3 : req (plus (opp (q s)) (opp (plus (opp (p s)) (mult (p s) eps))))
                       (plus (opp (q s)) (plus (opp (opp (p s))) (opp (mult (p s) eps)))))
        by exact (req_plus_compat (opp (q s)) (opp (q s))
                  (opp (plus (opp (p s)) (mult (p s) eps)))
                  (plus (opp (opp (p s))) (opp (mult (p s) eps)))
                  (req_refl (opp (q s))) v2).
      assert (v4 : req (plus (opp (q s)) (opp (opp (p s)))) (plus (opp (q s)) (p s)))
        by exact (req_plus_compat (opp (q s)) (opp (q s)) (opp (opp (p s))) (p s)
                  (req_refl (opp (q s))) (req_double_neg (p s))).
      assert (v5 : req (plus (opp (q s)) (plus (opp (opp (p s))) (opp (mult (p s) eps))))
                       (plus (plus (opp (q s)) (opp (opp (p s)))) (opp (mult (p s) eps))))
        by exact (plus_assoc (opp (q s)) (opp (opp (p s))) (opp (mult (p s) eps))).
      assert (v6 : req (plus (plus (opp (q s)) (opp (opp (p s)))) (opp (mult (p s) eps)))
                       (plus (plus (opp (q s)) (p s)) (opp (mult (p s) eps))))
        by exact (req_plus_compat (plus (opp (q s)) (opp (opp (p s)))) (plus (opp (q s)) (p s))
                  (opp (mult (p s) eps)) (opp (mult (p s) eps)) v4 (req_refl (opp (mult (p s) eps)))).
      assert (v7 : req (plus (plus (opp (q s)) (p s)) (opp (mult (p s) eps)))
                       (plus (plus (p s) (opp (q s))) (opp (mult (p s) eps))))
        by exact (req_plus_compat (plus (opp (q s)) (p s)) (plus (p s) (opp (q s)))
                  (opp (mult (p s) eps)) (opp (mult (p s) eps))
                  (plus_comm (opp (q s)) (p s)) (req_refl (opp (mult (p s) eps)))).
      assert (v8 : req (plus (plus (p s) (opp (q s))) (opp (mult (p s) eps)))
                       (plus (p s) (plus (opp (q s)) (opp (mult (p s) eps)))))
        by exact (req_sym (plus (p s) (plus (opp (q s)) (opp (mult (p s) eps))))
                          (plus (plus (p s) (opp (q s))) (opp (mult (p s) eps)))
                          (plus_assoc (p s) (opp (q s)) (opp (mult (p s) eps)))).
      assert (v9 : req (plus (p s) (plus (opp (q s)) (opp (mult (p s) eps))))
                       (plus (p s) (opp (plus (q s) (mult (p s) eps)))))
        by exact (req_plus_compat (p s) (p s)
                  (plus (opp (q s)) (opp (mult (p s) eps)))
                  (opp (plus (q s) (mult (p s) eps)))
                  (req_refl (p s))
                  (req_sym (opp (plus (q s) (mult (p s) eps)))
                           (plus (opp (q s)) (opp (mult (p s) eps)))
                           (req_opp_plus (q s) (mult (p s) eps)))).
      exact (ga2_rt v1
              (ga2_rt v3
                (ga2_rt v5
                  (ga2_rt v6 (ga2_rt v7 (ga2_rt v8 v9)))))). }
    exact (ga2_rt c5
              (ga2_rt (req_opp_compat
                        (mult (p s) (plus (mult (q s) (inv_pos (p s) Hps))
                                            (plus (opp one) eps)))
                        (plus (q s) (plus (opp (p s)) (mult (p s) eps)))
                        (ga2_rt (req_sym (mult (p s)
                                           (plus (plus (mult (q s) (inv_pos (p s) Hps))
                                                   (opp one)) eps))
                                         (mult (p s)
                                           (plus (mult (q s) (inv_pos (p s) Hps))
                                                   (plus (opp one) eps)))
                                         (req_mult_compat (p s) (p s)
                                           (plus (plus (mult (q s) (inv_pos (p s) Hps))
                                                   (opp one)) eps)
                                           (plus (mult (q s) (inv_pos (p s) Hps))
                                                   (plus (opp one) eps))
                                           (req_refl (p s)) d1))
                                  t2))
                c6)). }
  exact (ga2_le_id_l
          (req_sym (mult (p s) (opp (plus (plus (mult (q s) (inv_pos (p s) Hps)) (opp one)) eps)))
                   (plus (p s) (opp (plus (q s) (mult (p s) eps)))) H9)
          H8).
Qed.

(* ---- main piece: the req2_gibbs_inequality assembly (norm at the
   argument face, exit in the witnessed eps form). the exit conclusion is
   le zero (plus KL eps), with the KL term = @req2_rel_ent S sumf
   p q Hp Hq, term-for-term the same body as this world's KLE slot
   definition at UpReqAlign2.v:108 (the UpReqU2.v:359 slot of the Main
   tree), transparent up to delta. *)
Lemma ga2_gibbs_eps :
  forall (p q : S -> R)
         (Hp : @req2_pos_dist S p) (Hq : @req2_pos_dist S q)
         (Hnp : req (sumf p) one) (Hnq : req (sumf q) one) (eps : R),
    lt zero eps ->
    le zero (plus (@req2_rel_ent S sumf p q Hp Hq) eps).
Proof.
  intros p q Hp Hq Hnp Hnq eps Heps.
  assert (Hptw : forall s : S,
            le (plus (p s) (opp (plus (q s) (mult (p s) eps))))
               (mult (p s) (req_minus (log (p s) (Hp s)) (log (q s) (Hq s)))))
    by (intro s; exact (ga2_ptw_le p q eps s (Hp s) (Hq s) Heps)).
  assert (Hsum : le (sumf (fun s => plus (p s) (opp (plus (q s) (mult (p s) eps)))))
                    (sumf (fun s => mult (p s)
                              (req_minus (log (p s) (Hp s)) (log (q s) (Hq s))))))
    by exact (ga2_sum_le _ _ Hptw).
  (* summation algebra: ΣG ≡ opp eps, from the zero norm sum, linearity,
     and the opp one scaling. *)
  assert (Tr : req (sumf (fun s => plus (p s) (opp (plus (q s) (mult (p s) eps)))))
                   (opp eps)).
  { assert (T1 : req (sumf (fun s => plus (p s) (opp (plus (q s) (mult (p s) eps)))))
                     (plus (sumf p)
                           (sumf (fun s => opp (plus (q s) (mult (p s) eps))))))
      by exact (ga2_sum_add p (fun s => opp (plus (q s) (mult (p s) eps)))).
    assert (T3e : req (sumf (fun s => opp (plus (q s) (mult (p s) eps))))
                      (plus (opp one) (opp eps))).
    { assert (T3a : req (sumf (fun s => opp (plus (q s) (mult (p s) eps))))
                        (sumf (fun s => plus (opp (q s)) (opp (mult (p s) eps)))))
        by exact (ga2_sum_ext (fun s => opp (plus (q s) (mult (p s) eps)))
                  (fun s => plus (opp (q s)) (opp (mult (p s) eps)))
                  (fun s => req_opp_plus (q s) (mult (p s) eps))).
      assert (T3b : req (sumf (fun s => plus (opp (q s)) (opp (mult (p s) eps))))
                        (plus (sumf (fun s => opp (q s)))
                              (sumf (fun s => opp (mult (p s) eps)))))
        by exact (ga2_sum_add (fun s => opp (q s)) (fun s => opp (mult (p s) eps))).
      assert (A : req (sumf (fun s => opp (q s))) (opp one)).
      { assert (A1 : req (sumf (fun s => opp (q s))) (sumf (fun s => mult (opp one) (q s))))
          by exact (ga2_sum_ext (fun s => opp (q s)) (fun s => mult (opp one) (q s))
                    (fun s => req_sym (mult (opp one) (q s)) (opp (q s))
                                (ga2_mopp_one (q s)))).
        assert (A2 : req (sumf (fun s => mult (opp one) (q s))) (mult (opp one) (sumf q)))
          by exact (ga2_sum_linear (opp one) q).
        assert (A3 : req (mult (opp one) (sumf q)) (mult (opp one) one))
          by exact (req_mult_compat (opp one) (opp one) (sumf q) one
                      (req_refl (opp one)) Hnq).
        assert (A4 : req (mult (opp one) one) (opp one)) by exact (mult_one (opp one)).
        exact (ga2_rt A1 (ga2_rt A2 (ga2_rt A3 A4))). }
      assert (B : req (sumf (fun s => opp (mult (p s) eps))) (opp eps)).
      { assert (B1 : req (sumf (fun s => opp (mult (p s) eps)))
                          (sumf (fun s => mult (opp one) (mult (p s) eps))))
          by exact (ga2_sum_ext (fun s => opp (mult (p s) eps))
                    (fun s => mult (opp one) (mult (p s) eps))
                    (fun s => req_sym (mult (opp one) (mult (p s) eps))
                                (opp (mult (p s) eps))
                                (ga2_mopp_one (mult (p s) eps)))).
        assert (B2 : req (sumf (fun s => mult (opp one) (mult (p s) eps)))
                          (mult (opp one) (sumf (fun s => mult (p s) eps))))
          by exact (ga2_sum_linear (opp one) (fun s => mult (p s) eps)).
        assert (B3 : req (sumf (fun s => mult (p s) eps)) eps).
        { assert (B3a : req (sumf (fun s => mult (p s) eps))
                            (sumf (fun s => mult eps (p s))))
            by exact (ga2_sum_ext (fun s => mult (p s) eps) (fun s => mult eps (p s))
                      (fun s => req_mult_comm_rewrite (p s) eps)).
          assert (B3b : req (sumf (fun s => mult eps (p s))) (mult eps (sumf p)))
            by exact (ga2_sum_linear eps p).
          assert (B3c : req (mult eps (sumf p)) (mult eps one))
            by exact (req_mult_compat eps eps (sumf p) one (req_refl eps) Hnp).
          assert (B3d : req (mult eps one) eps) by exact (mult_one eps).
          exact (ga2_rt B3a (ga2_rt B3b (ga2_rt B3c B3d))). }
        assert (B4 : req (mult (opp one) (sumf (fun s => mult (p s) eps)))
                          (mult (opp one) eps))
          by exact (req_mult_compat (opp one) (opp one)
                    (sumf (fun s => mult (p s) eps)) eps (req_refl (opp one)) B3).
        exact (ga2_rt B1
                (ga2_rt B2 (ga2_rt B4 (ga2_mopp_one eps)))). }
      exact (ga2_rt T3a (ga2_rt T3b
              (req_plus_compat (sumf (fun s => opp (q s))) (opp one)
                (sumf (fun s => opp (mult (p s) eps))) (opp eps) A B))). }
    assert (T4 : req (plus one (plus (opp one) (opp eps))) (opp eps)).
    { assert (e1 : req (plus one (plus (opp one) (opp eps)))
                       (plus (plus one (opp one)) (opp eps)))
        by exact (plus_assoc one (opp one) (opp eps)).
      assert (e2 : req (plus (plus one (opp one)) (opp eps)) (plus zero (opp eps)))
        by exact (req_plus_compat (plus one (opp one)) zero (opp eps) (opp eps)
                  (plus_opp one) (req_refl (opp eps))).
      exact (ga2_rt e1 (ga2_rt e2 (req_plus_zero_l (opp eps)))). }
    exact (ga2_rt T1
            (ga2_rt
              (req_plus_compat (sumf p) one
                (sumf (fun s => opp (plus (q s) (mult (p s) eps))))
                (plus (opp one) (opp eps)) Hnp T3e)
              T4)). }
  assert (HD : le (opp eps)
                  (sumf (fun s => mult (p s)
                            (req_minus (log (p s) (Hp s)) (log (q s) (Hq s))))))
    by exact (ga2_le_id_l
                (req_sym (sumf (fun s => plus (p s) (opp (plus (q s) (mult (p s) eps)))))
                         (opp eps) Tr)
                Hsum).
  apply (le_id_l zero (plus (opp eps) eps)
          (plus (sumf (fun s => mult (p s)
                        (req_minus (log (p s) (Hp s)) (log (q s) (Hq s))))) eps)).
  - exact (ga2_rt (req_sym (plus eps (opp eps)) zero (plus_opp eps))
                  (plus_comm eps (opp eps))).
  - exact (le_plus_compat (opp eps)
            (sumf (fun s => mult (p s)
                      (req_minus (log (p s) (Hp s)) (log (q s) (Hq s)))))
            eps eps HD (le_refl eps)).
Qed.

(* ---- exit twin: the le (opp eps) KL form, the direction commonly used
   for squeezing at use sites; normalization in the req group ---- *)
Corollary ga2_gibbs_eps_opps :
  forall (p q : S -> R)
         (Hp : @req2_pos_dist S p) (Hq : @req2_pos_dist S q)
         (Hnp : req (sumf p) one) (Hnq : req (sumf q) one) (eps : R),
    lt zero eps ->
    le (opp eps) (@req2_rel_ent S sumf p q Hp Hq).
Proof.
  intros p q Hp Hq Hnp Hnq eps Heps.
  assert (Step1 : le (plus zero (opp eps))
                     (plus (plus (@req2_rel_ent S sumf p q Hp Hq) eps)
                           (opp eps)))
    by exact (le_plus_compat zero
                             (plus (@req2_rel_ent S sumf p q Hp Hq) eps)
                             (opp eps) (opp eps)
                             (ga2_gibbs_eps p q Hp Hq Hnp Hnq eps Heps)
                             (le_refl (opp eps))).
  assert (Step3 : req (plus (plus (@req2_rel_ent S sumf p q Hp Hq) eps)
                            (opp eps))
                     (@req2_rel_ent S sumf p q Hp Hq)).
  { exact (ga2_rt
            (req_sym (plus (@req2_rel_ent S sumf p q Hp Hq)
                           (plus eps (opp eps)))
                     (plus (plus (@req2_rel_ent S sumf p q Hp Hq) eps)
                           (opp eps))
                     (plus_assoc (@req2_rel_ent S sumf p q Hp Hq) eps (opp eps)))
            (ga2_rt
              (req_plus_compat (@req2_rel_ent S sumf p q Hp Hq)
                (@req2_rel_ent S sumf p q Hp Hq) (plus eps (opp eps)) zero
                (req_refl (@req2_rel_ent S sumf p q Hp Hq)) (plus_opp eps))
              (plus_zero (@req2_rel_ent S sumf p q Hp Hq)))). }
  exact (le_id_l (opp eps) (plus zero (opp eps))
                 (@req2_rel_ent S sumf p q Hp Hq)
                 (req_sym (plus zero (opp eps)) (opp eps)
                          (req_plus_zero_l (opp eps)))
                 (le_id_r (plus zero (opp eps))
                          (plus (plus (@req2_rel_ent S sumf p q Hp Hq) eps)
                                (opp eps))
                          (@req2_rel_ent S sumf p q Hp Hq) Step3 Step1)).
Qed.

End GibbsAssembly.

Print Assumptions ga2_gibbs_eps.
Print Assumptions ga2_gibbs_eps_opps.
