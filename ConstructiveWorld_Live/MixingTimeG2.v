(* ========================================================================= *)
(* Module   : MixingTimeG2                                                  *)
(* Mission.  Explicit mixing time for a finite Markov chain: for a          *)
(*            row-stochastic kernel K on an enumerated state world with     *)
(*            uniform reference u, minorization K >= delta*u and an         *)
(*            abs-sum face, produce an explicit step count k with           *)
(*            TV(K^k mu, K^k nu) < budget at the geometric rate             *)
(*            kappa := 1 - delta; rate certificate (0 < kappa < 1), the     *)
(*            selector instance, the delta = 1 one-shot branch, a           *)
(*            transparent k-calculator with correctness face, and slack.    *)
(* Dependencies. Stdlib List; S02_CauchyComplete (Real and the Set-valued   *)
(*            order faces real_lt/real_le/real_eq with their setoid         *)
(*            lemmas), S03_QExp (real_abs), S07_RealSetoidExpLog            *)
(*            (RealSetoid.real_eq_le, RealSetoid.real_eq_mult_compat),      *)
(*            S08_RealMainlineDPO (real_list_sum), UpTVDoeblin (tv_doeblin, *)
(*            tv_titer, tv_omd, tv_rpow, tv_omd_pos_of_lt,                  *)
(*            tv_doeblin_iter), UpReqMixingTime (mix_k_select,              *)
(*            mix_omd_lt_one, mix_rpow_one), UpReqIterGeomRate              *)
(*            (igr_le_plus_r).                                              *)
(* References. Baseline MixingTimeG2.v of ConstructiveWorld-Main (statement *)
(*            names carried verbatim; see also theorems 5.10/5.6b there).   *)
(* Constructivity. All conclusions are Set-carried: Real : Set and the      *)
(*            order faces real_lt/real_le/real_eq are Set-valued here;      *)
(*            certificates are stdlib prod and sigT over nat mirroring the  *)
(*            existing mix_k_select shape, zero Prop components inside.     *)
(*            Every constant is Defined: no statement is a pure-Prop        *)
(*            bridge, so no Qed appears and all faces stay extractable;     *)
(*            delta = 1 closes by the real_plus_opp chain, zero axioms.     *)
(* Build. rocq c -native-compiler no -q -Q <live tree root> "" MixingTimeG2.v *)
(* ========================================================================= *)

From Stdlib Require Import List.
Import ListNotations.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import UpTVDoeblin.
Require Import UpReqMixingTime.
Require Import UpReqIterGeomRate.

(* ============================================================ *)
(* Part A. The rate certificate: 0 < delta < 1 gives 0 < 1-delta < 1.        *)
(* ============================================================ *)

Theorem mtg_kappa_cert : forall delta : Real,
  real_lt real_zero delta -> real_lt delta real_one ->
  prod (real_lt real_zero (tv_omd delta)) (real_lt (tv_omd delta) real_one).
Proof.
  intros delta Hd0 Hd1.
  exact (pair (tv_omd_pos_of_lt delta Hd1) (mix_omd_lt_one delta Hd0)).
Defined.

(* ============================================================ *)
(* Part B. The explicit-step selector instance: a rate certificate and      *)
(*    a nonnegative initial TV yield a concrete k with kappa^k*TV0 < budget.*)
(* ============================================================ *)

Theorem mtg_mixing_time_explicit_k : forall (kappa TV0 budget : Real),
  prod (real_lt real_zero kappa) (real_lt kappa real_one) ->
  real_le real_zero TV0 -> real_lt real_zero budget ->
  sigT (fun k : nat => real_lt (real_mult (tv_rpow kappa k) TV0) budget).
Proof.
  intros kappa TV0 budget Hcert Ha Hb.
  exact (mix_k_select kappa TV0 budget (fst Hcert) (snd Hcert) Ha Hb).
Defined.

(* Rate form: kappa instantiated at 1 - delta. *)

Theorem mtg_mixing_time_rate_explicit : forall (delta TV0 budget : Real),
  real_lt real_zero delta -> real_lt delta real_one ->
  real_le real_zero TV0 -> real_lt real_zero budget ->
  sigT (fun k : nat =>
    real_lt (real_mult (tv_rpow (tv_omd delta) k) TV0) budget).
Proof.
  intros delta TV0 budget Hd0 Hd1 Ha Hb.
  destruct (mtg_kappa_cert delta Hd0 Hd1) as [Hk1 Hk2].
  exact (mtg_mixing_time_explicit_k (tv_omd delta) TV0 budget
           (pair Hk1 Hk2) Ha Hb).
Defined.

(* ============================================================ *)
(* Part C. The mixing-time theorem: the kernel interface (row sums one,     *)
(*    uniform reference, minorization, abs-sum face) joined with the        *)
(*    iterate contraction and the selector.  The premise delta <= 1 splits  *)
(*    on the two Or branches of real_le: delta < 1 runs the selector;       *)
(*    delta = 1 gives kappa = 0 and k := 1 closes in one shot.              *)
(* ============================================================ *)

Theorem mtg_mixing_time_TV :
  forall (states : list (list Real))
         (K : list Real -> list Real -> Real)
         (K_row : forall i : list Real,
            real_eq (real_list_sum (list Real) (K i) states) real_one)
         (u : list Real -> Real)
         (u_norm : real_eq (real_list_sum (list Real) u states) real_one)
         (delta : Real)
         (Hd1 : real_le delta real_one)
         (Hmin : forall i j : list Real,
            real_le (real_mult delta (u j)) (K i j))
         (Labs : forall f : list Real -> Real,
            real_le (real_abs (real_list_sum (list Real) f states))
                    (real_list_sum (list Real)
                       (fun w : list Real => real_abs (f w)) states))
         (mu nu : list Real -> Real),
    real_eq (real_list_sum (list Real) mu states) real_one ->
    real_eq (real_list_sum (list Real) nu states) real_one ->
    real_le real_zero (tv_doeblin states mu nu) ->
    real_lt real_zero delta ->
    forall budget : Real,
      real_lt real_zero budget ->
      sigT (fun k : nat =>
        real_lt (tv_doeblin states (tv_titer states K k mu)
                                (tv_titer states K k nu)) budget).
Proof.
  intros states K K_row u u_norm delta Hd1 Hmin Labs mu nu
         Hmu Hnu TV0nn Hd0 budget Hbudget.
  assert (Hd1' : real_le delta real_one) by exact Hd1.
  unfold real_le in Hd1. destruct Hd1 as [Hdlt | Hdeq].
  - (* delta < 1: kappa := 1 - delta lies in (0,1); the selector yields k
       and the iterate contraction closes the chain. *)
    assert (Hk1 : real_lt real_zero (tv_omd delta))
      by exact (tv_omd_pos_of_lt delta Hdlt).
    assert (Hk2 : real_lt (tv_omd delta) real_one)
      by exact (mix_omd_lt_one delta Hd0).
    destruct (mix_k_select (tv_omd delta) (tv_doeblin states mu nu) budget
                Hk1 Hk2 TV0nn Hbudget) as [k Hk].
    exists k.
    apply (real_le_lt_trans
             (tv_doeblin states (tv_titer states K k mu)
                         (tv_titer states K k nu))
             (real_mult (tv_rpow (tv_omd delta) k)
                        (tv_doeblin states mu nu))
             budget).
    + exact (tv_doeblin_iter states K K_row u u_norm delta Hd1' Hmin Labs
               k mu nu Hmu Hnu).
    + exact Hk.
  - (* delta = 1: kappa = 0, so k := 1 closes in one shot:
       kappa^1 * TV0 == 0 < budget. *)
    exists 1%nat.
    assert (Hiter : real_le
              (tv_doeblin states (tv_titer states K 1%nat mu)
                          (tv_titer states K 1%nat nu))
              (real_mult (tv_rpow (tv_omd delta) 1%nat)
                         (tv_doeblin states mu nu)))
      by exact (tv_doeblin_iter states K K_row u u_norm delta Hd1' Hmin Labs
                  1%nat mu nu Hmu Hnu).
    assert (Homd : real_eq (tv_omd delta) real_zero).
    { (* 1 - delta = delta - delta = 0 through the subtraction-compat
         chain; real_one is kept folded throughout. *)
      apply (real_eq_trans (tv_omd delta)
               (real_plus delta (real_opp delta)) real_zero).
      - exact (real_eq_minus_compat real_one delta delta delta
                 (real_eq_sym _ _ Hdeq) (real_eq_refl delta)).
      - exact (real_plus_opp delta). }
    assert (Hpow1 : real_eq (tv_rpow (tv_omd delta) 1%nat) real_zero).
    { exact (real_eq_trans (tv_rpow (tv_omd delta) 1%nat)
               (tv_omd delta) real_zero
               (mix_rpow_one (tv_omd delta)) Homd). }
    assert (Hzero : real_eq
              (real_mult (tv_rpow (tv_omd delta) 1%nat)
                         (tv_doeblin states mu nu))
              real_zero).
    { exact (real_eq_trans
               (real_mult (tv_rpow (tv_omd delta) 1%nat)
                          (tv_doeblin states mu nu))
               (real_mult real_zero (tv_doeblin states mu nu))
               real_zero
               (RealSetoid.real_eq_mult_compat
                  (tv_rpow (tv_omd delta) 1%nat)
                  (tv_doeblin states mu nu)
                  real_zero (tv_doeblin states mu nu)
                  Hpow1 (real_eq_refl (tv_doeblin states mu nu)))
               (real_eq_trans (real_mult real_zero (tv_doeblin states mu nu))
                  (real_mult (tv_doeblin states mu nu) real_zero) real_zero
                  (real_mult_comm real_zero (tv_doeblin states mu nu))
                  (real_mult_zero (tv_doeblin states mu nu)))). }
    apply (real_le_lt_trans
             (tv_doeblin states (tv_titer states K 1%nat mu)
                         (tv_titer states K 1%nat nu))
             real_zero budget).
    + apply (real_le_trans
               (tv_doeblin states (tv_titer states K 1%nat mu)
                           (tv_titer states K 1%nat nu))
               (real_mult (tv_rpow (tv_omd delta) 1%nat)
                          (tv_doeblin states mu nu))
               real_zero).
      * exact Hiter.
      * apply (RealSetoid.real_eq_le). exact Hzero.
    + exact Hbudget.
Defined.

(* ============================================================ *)
(* Part D. The transparent k-calculator and its correctness face.           *)
(* ============================================================ *)

Definition mtg_k_calc (kappa TV0 budget : Real)
  (Hcert : prod (real_lt real_zero kappa) (real_lt kappa real_one))
  (Ha : real_le real_zero TV0)
  (Hb : real_lt real_zero budget) : nat :=
  projT1 (mtg_mixing_time_explicit_k kappa TV0 budget Hcert Ha Hb).

Theorem mtg_k_calc_correct : forall (kappa TV0 budget : Real)
  (Hcert : prod (real_lt real_zero kappa) (real_lt kappa real_one))
  (Ha : real_le real_zero TV0) (Hb : real_lt real_zero budget),
  real_lt (real_mult (tv_rpow kappa (mtg_k_calc kappa TV0 budget Hcert Ha Hb))
                     TV0) budget.
Proof.
  intros kappa TV0 budget Hcert Ha Hb.
  exact (projT2 (mtg_mixing_time_explicit_k kappa TV0 budget Hcert Ha Hb)).
Defined.

(* ============================================================ *)
(* Part E. Budget slack: a positive slack e enlarges the reachable budget.  *)
(* ============================================================ *)

Lemma mtg_budget_slack : forall (a b e : Real),
  real_lt real_zero e -> real_lt a b -> real_lt a (real_plus b e).
Proof.
  intros a b e He Hab.
  exact (real_lt_le_trans a b (real_plus b e) Hab (igr_le_plus_r b e He)).
Defined.

Theorem mtg_k_slack : forall (kappa TV0 budget e : Real),
  prod (real_lt real_zero kappa) (real_lt kappa real_one) ->
  real_le real_zero TV0 -> real_lt real_zero budget ->
  real_lt real_zero e ->
  sigT (fun k : nat =>
    real_lt (real_mult (tv_rpow kappa k) TV0) (real_plus budget e)).
Proof.
  intros kappa TV0 budget e Hcert Ha Hb He.
  destruct (mtg_mixing_time_explicit_k kappa TV0 budget Hcert Ha Hb)
    as [k Hk].
  exists k. exact (mtg_budget_slack _ _ e He Hk).
Defined.

(* ============================================================ *)
(* Assumption audit: one line per theorem, all expected Closed.             *)
(* ============================================================ *)

Print Assumptions mtg_kappa_cert.
Print Assumptions mtg_mixing_time_explicit_k.
Print Assumptions mtg_mixing_time_rate_explicit.
Print Assumptions mtg_mixing_time_TV.
Print Assumptions mtg_k_calc_correct.
Print Assumptions mtg_budget_slack.
Print Assumptions mtg_k_slack.
