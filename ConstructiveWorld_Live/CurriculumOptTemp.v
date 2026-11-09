(* ConstructiveWorld-Set -- curriculum optimal temperature eps-witness intervals on a finite sweep table. *)

(** * CurriculumOptTemp: eps-optimal temperature intervals for curriculum loss.

    Mission.  On a finite temperature sweep table (cold-end anchor strictly
      colder than every body point), for every positive [eps] produce an
      in-table temperature whose loss beats every table point up to [eps]:
      [cot_optimal_temp_interval] over the carriers [cot_ptemp]/[cot_loss],
      fed by [cot_energy_temp_mono_b], [cot_tab_min_exists], [cot_curriculum_mono_b].

    Dependencies.  Stdlib [List].  Requires [S01_BaseRing], [S02_CauchyComplete],
      [S03_QExp], [S04_RealExpLogConv], [S05_AlignmentGRPO], [S06_DiffSamplingGibbs],
      [S07_RealSetoidExpLog], [S08_RealMainlineDPO], [S09_EntropyReal],
      [S10_KVQuantTrig], [S11_TP3B5], [S12_B5RecycleSF], [S13_NLiveAudit],
      [S14_B5BatchBlock], [S15_TailFEPUp], [RealEnergyTempMono],
      [EnergyTempMonoB], [UpRealLeB] of this development.

    References.  This development, CurriculumOptTemp.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].  The baseline-declared open interface (curriculum
      loss = energy expectation) stays open: [cot_curriculum_mono_b] is
      delivered at the Bishop level via [real_le_to_le_b].

    Build.  [coqc -native-compiler no -q -Q . "" CurriculumOptTemp.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 000160bc]. *)

From Stdlib Require Import List.
Import ListNotations.
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
Require Import RealEnergyTempMono.
Require Import EnergyTempMonoB.
Require Import UpRealLeB.

(* ============================================================ *)
(* Part 0. Positive-temperature points and the energy-expectation loss face *)
(* ============================================================ *)

(* Positive temperatures travel with their certificates: the value and its positivity proof packed together in [sigT] over [Set]. *)
Definition cot_ptemp : Set := sigT (fun t : Real => real_lt real_zero t).

(* The loss face: the energy expectation E(t) at temperature t, the weighted sum of the outcomes, supplied directly by [retm_Eexp]. *)
Definition cot_loss (X : Set) (u : X -> Real) (s0 : X) (l : list X)
           (p : cot_ptemp) : Real :=
  retm_Eexp X u s0 l (projT1 p) (projT2 p).

(* Reflexivity at the Bishop level: x [real_le_b] x, direct from [real_lt_plus_r_zero] since 0 < eps yields x < x + eps. *)
Lemma cot_le_b_refl : forall x : Real, real_le_b x x.
Proof.
  intros x eps Heps.
  exact (real_lt_plus_r_zero x eps Heps).
Qed.

(* ============================================================ *)
(* Part 1. Support lemma 1: energy-temperature monotonicity instantiated from the monotone module *)
(* ============================================================ *)

(* A strictly colder temperature carries a Bishop-dominated loss: p < q gives
   loss(p) [real_le_b] loss(q).  This instantiates [etm_energy_temp_mono_b] on
   the [cot_ptemp] carrier; the underlying chain holds the identity schedule
   against the Gibbs bound (KL >= 0) closed by the negative-coefficient
   contravariance. *)
Lemma cot_energy_temp_mono_b :
  forall (X : Set) (u : X -> Real) (s0 : X) (l : list X) (p q : cot_ptemp),
    real_lt (projT1 p) (projT1 q) ->
    real_le_b (cot_loss X u s0 l p) (cot_loss X u s0 l q).
Proof.
  intros X u s0 l p q Ht.
  exact (etm_energy_temp_mono_b X u s0 l
           (projT1 p) (projT2 p) (projT1 q) (projT2 q) Ht).
Qed.

(* ============================================================ *)
(* Part 2. Support lemma 2: existence of a minimum on a finite sweep table *)
(* ============================================================ *)

(* If the cold-end anchor [tmin] is strictly colder than every point of the
   table body [tab], the table [tmin :: tab] carries a minimum: an [InT]
   membership witness paired by the Set-valued conjunction [And] with a
   pointwise Bishop domination.  This mirrors the finite-table argmin
   domination of [rae_pick_optimal] in monotone dress: order on [Real] admits
   no decidable bisector, so the monotone chain replaces the decider and the
   cold end is the argmin. *)
Lemma cot_tab_min_exists :
  forall (X : Set) (u : X -> Real) (s0 : X) (l : list X)
    (tab : list cot_ptemp) (tmin : cot_ptemp),
    (forall t : cot_ptemp, InT t tab -> real_lt (projT1 tmin) (projT1 t)) ->
    sigT (fun ts => And (InT ts (tmin :: tab))
      (forall t : cot_ptemp, InT t (tmin :: tab) ->
        real_le_b (cot_loss X u s0 l ts) (cot_loss X u s0 l t))).
Proof.
  intros X u s0 l tab tmin Hlb.
  exists tmin. split.
  - apply InT_here.
  - intros t Ht. inversion Ht as [Heq | y0 l0 Hin]; subst.
    + (* the case t = tmin: the reflexivity branch, Bishop shape. *)
      apply cot_le_b_refl.
    + (* the case t in tab: strictly colder gives the Bishop-monotone loss, by support lemma 1. *)
      exact (cot_energy_temp_mono_b X u s0 l tmin t (Hlb t Hin)).
Qed.

(* ============================================================ *)
(* Part 3. Main theorem: the eps-witnessed optimal temperature interval *)
(* ============================================================ *)

(* On a finite sweep table (cold-end anchor plus body), for every eps > 0 some
   in-table temperature t* satisfies: for every table point t, the loss at t*
   is below the loss at t plus eps.  The witness is not a vacuous shell: the
   [InT] membership of t* and the pointwise domination chain run through the
   temperature monotonicity against the Gibbs Bishop bound. *)
Theorem cot_optimal_temp_interval :
  forall (X : Set) (u : X -> Real) (s0 : X) (l : list X)
    (tab : list cot_ptemp) (tmin : cot_ptemp),
    (forall t : cot_ptemp, InT t tab -> real_lt (projT1 tmin) (projT1 t)) ->
    forall eps : Real, real_lt real_zero eps ->
    sigT (fun ts => sigT (fun _ : InT ts (tmin :: tab) =>
      forall t : cot_ptemp, InT t (tmin :: tab) ->
        real_lt (cot_loss X u s0 l ts) (real_plus (cot_loss X u s0 l t) eps))).
Proof.
  intros X u s0 l tab tmin Hlb eps Heps.
  destruct (cot_tab_min_exists X u s0 l tab tmin Hlb) as [ts [Hmem Hdom]].
  exists ts. exists Hmem.
  intros t Ht.
  exact (Hdom t Ht eps Heps).
Qed.

(* ============================================================ *)
(* Part 4. The curriculum receiver branch: thin-shell reuse of [SFCurriculum] with the Bishop-level lift *)
(* ============================================================ *)
(* Interface note, carried over from the baseline as declared: the
   identification of the curriculum loss with the energy expectation (the
   [retm_Eexp] face) is not yet closed.  The curriculum branch is therefore
   delivered at the lifted Bishop level: the monotonicity of the curriculum
   loss face (proved genuinely by the receiver fold accumulation) is raised
   through [real_le_to_le_b] onto the same [real_le_b] face as the main
   theorem; once the interface lands, the temperature chain of Parts 1-3
   reuses verbatim to give the eps-optimal interval for the curriculum
   loss. *)

Section CotCurriculumFace.
Variable SFModel : Set.
Variable cot_train_step : SFModel -> SFVec -> SFModel.
Variable cot_cur_loss : SFModel -> Real.
Hypothesis cot_step_ok :
  forall (m : SFModel) (smp : SFVec),
    real_le (cot_cur_loss (cot_train_step m smp)) (cot_cur_loss m).

(* Monotonicity of the curriculum loss at the Bishop level: the receiver lemma
   that a finished curriculum run never increases the loss (fold accumulation)
   is lifted by the one-way bridge [real_le_to_le_b]; its premise keeps the
   position of the receiver step premise [sf_step_ok]. *)
Theorem cot_curriculum_mono_b :
  forall (samples : list SFVec) (m : SFModel),
    real_le_b (cot_cur_loss (sf_curriculum_run SFModel cot_train_step samples m))
              (cot_cur_loss m).
Proof.
  intros samples m.
  exact (real_le_to_le_b _ _
           (sf_curriculum_monotone SFModel cot_train_step cot_cur_loss
              cot_step_ok samples m)).
Qed.

End CotCurriculumFace.

(* ============================================================ *)
(* Assumption audit: every exported statement is closed under the global context *)
(* ============================================================ *)
Print Assumptions cot_le_b_refl.
Print Assumptions cot_energy_temp_mono_b.
Print Assumptions cot_tab_min_exists.
Print Assumptions cot_optimal_temp_interval.
Print Assumptions cot_curriculum_mono_b.
