(* ConstructiveWorld-Set — degenerate and two-sided mixing windows for a two-state kernel. *)

(** * UpAblMetaWindow: degenerate-window and two-sided mixing-window statements
      for a two-state kernel.

    Mission.  [mwi_step], one-step evolution of a kernel over the two-state space;
      [mwi_collapse_row_equal], a kernel with identical rows collapses in one step
      (TV == 0); the uniform-kernel instance [mwi_Kunif] with its collapse
      [mwi_degenerate_collapse_uniform]; and [mtw_window_two_sided], the two-sided
      mixing-window statement (degenerate side plus persistent side: the exact power
      law [mtw_tv_exact_iter] and the budget lower bound [mtw_no_mixing_below]).

    Dependencies.  Stdlib none beyond this development.  Requires [S01_BaseRing],
      [S02_CauchyComplete], [S03_QExp], [S04_RealExpLogConv], [S05_AlignmentGRPO],
      [S06_DiffSamplingGibbs], [S07_RealSetoidExpLog], [S08_RealMainlineDPO],
      [S09_EntropyReal], [S10_KVQuantTrig], [S11_TP3B5], [S12_B5RecycleSF],
      [S13_NLiveAudit], [S14_B5BatchBlock], [S15_TailFEPUp], [UpReqAlgebra],
      [UpReqDist], [UpReqSampling], [UpAblMetaWorld3] of this development.

    References.  This development, UpAblMetaWindow.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here verbatim
      (statement-face Set-carrier completion).  Mixing-time windows for finite Markov
      chains (total-variation distance of the degenerate and uniform kernels).

    Constructivity.  All named statements are carried by [Set]; every proof closes by
      [Qed]/[Defined] with zero admission tokens; the proof bodies introduce no
      additional axiom premises.

    Build.  [coqc -native-compiler no -q -Q . "" UpAblMetaWindow.v] compiles cleanly (exit 0);
      the first eight bytes of the artifact are [436f7121 00015ff4]. *)

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
Require Import UpReqAlgebra.
Require Import UpReqDist.
Require Import UpReqSampling.
Require Import UpAblMetaWorld3.
Import RealInterfaceEnhancedMod.

(* The interface class in this tree is unparameterized (S07_RealSetoidExpLog.v
   Class RealInterfaceEnhancedSetoid + global Instance RealEnhancedReal).  The
   equality and order carriers of the statements below are bound to the
   concrete informative definitions real_eq / real_lt of S02_CauchyComplete.
   These are exactly the bindings that the global RealEnhancedReal instance
   assigns to the interface fields req / lt, so every statement elaborates to
   the same term as before; naming the carriers concretely keeps the extracted
   signatures informative. *)
Local Notation req := real_eq.
Local Notation lt := real_lt.

(* ============================================================ *)
(* Section 1. Degenerate-side machinery: generic one-step kernel     *)
(* evolution plus base algebra bridges.                              *)
(* ============================================================ *)

(* generic one-step evolver: same shape as the donor [mtw_step], with
   the kernel [K] lifted to an explicit argument *)
Definition mwi_step (K : bool -> bool -> Real) (mu : bool -> Real) (s' : bool) : Real :=
  plus (mult (mu true) (K true s')) (mult (mu false) (K false s')).

(* left zero product: 0·a == 0 (the base [mult_zero] has only the
   right-zero form; route through [mult_comm]) *)
Lemma mwi_mult_zero_l : forall a : Real, req (mult zero a) zero.
Proof.
  intro a.
  apply (req_trans (mult zero a) (mult a zero) zero).
  - exact (mult_comm zero a).
  - exact (mult_zero a).
Defined.

(* self-difference vanishes: a - a == 0 *)
Lemma mwi_req_minus_self : forall a : Real, req (req_minus a a) zero.
Proof.
  intro a.
  unfold req_minus.
  exact (plus_opp a).
Defined.

(* absolute value of zero: |0| == 0 *)
Lemma mwi_abs_zero : req (abs zero) zero.
Proof. exact abs_zero. Defined.

(* ============================================================ *)
(* Section 2. Degenerate-face theorem: identical kernel rows imply   *)
(* one-step collapse (TV == 0, the degenerate side of the mixing     *)
(* window).  Note: the row-stochastic premise is a                   *)
(* world-membership premise; the collapse itself needs only          *)
(* identical rows (both rows equal the first row).                   *)
(* ============================================================ *)

Theorem mwi_collapse_row_equal :
  forall K : bool -> bool -> Real,
    (forall s : bool, req (plus (K s true) (K s false)) one) ->
    (forall s s' : bool, req (K s s') (K true s')) ->
    req (mtw_tv (mwi_step K mtw_mu0) (mwi_step K mtw_nu0)) zero.
Proof.
  intros K Hrow Heq.
  (* one step of the mass pair under [K] is pointwise the first row:
     the [mu0] side = 1·K(t,·) + 0·K(f,·) *)
  assert (Ht : forall s' : bool, req (mwi_step K mtw_mu0 s') (K true s')).
  { intro s'.
    apply (req_trans (mwi_step K mtw_mu0 s')
                     (plus (K true s') zero)
                     (K true s')).
    - exact (req_plus_compat
               (mult (mtw_mu0 true) (K true s')) (K true s')
               (mult (mtw_mu0 false) (K false s')) zero
               (req_mult_one_l (K true s'))
               (mwi_mult_zero_l (K false s'))).
    - exact (plus_zero (K true s')). }
  (* the [nu0] side = 0·K(t,·) + 1·K(f,·) = K(f,·) = K(t,·) (identical
     rows) *)
  assert (Hf : forall s' : bool, req (mwi_step K mtw_nu0 s') (K true s')).
  { intro s'.
    apply (req_trans (mwi_step K mtw_nu0 s')
                     (plus zero (K false s'))
                     (K true s')).
    - exact (req_plus_compat
               (mult (mtw_nu0 true) (K true s')) zero
               (mult (mtw_nu0 false) (K false s')) (K false s')
               (mwi_mult_zero_l (K true s'))
               (req_mult_one_l (K false s'))).
    - exact (req_trans (plus zero (K false s')) (K false s') (K true s')
               (req_plus_zero_l (K false s'))
               (Heq false s')). }
  (* a pointwise zero difference has pointwise zero absolute value *)
  assert (Hz : forall s' : bool,
           req (abs (req_minus (mwi_step K mtw_mu0 s')
                               (mwi_step K mtw_nu0 s'))) zero).
  { intro s'.
    apply (req_trans
             (abs (req_minus (mwi_step K mtw_mu0 s')
                             (mwi_step K mtw_nu0 s')))
             (abs zero) zero).
    - exact (req_abs_compat
               (req_minus (mwi_step K mtw_mu0 s') (mwi_step K mtw_nu0 s'))
               zero
               (req_trans
                  (req_minus (mwi_step K mtw_mu0 s') (mwi_step K mtw_nu0 s'))
                  (req_minus (K true s') (K true s'))
                  zero
                  (req_plus_compat
                     (mwi_step K mtw_mu0 s') (K true s')
                     (opp (mwi_step K mtw_nu0 s')) (opp (K true s'))
                     (Ht s')
                     (req_opp_compat (mwi_step K mtw_nu0 s') (K true s')
                               (Hf s')))
                  (mwi_req_minus_self (K true s')))).
    - exact mwi_abs_zero. }
  (* TV = (1/2)·(0+0) = 0 *)
  apply (req_trans (mtw_tv (mwi_step K mtw_mu0) (mwi_step K mtw_nu0))
                   (mult mtw_half zero) zero).
  - exact (req_mult_compat mtw_half mtw_half
             (mtw_sumf (fun s : bool =>
                   abs (req_minus (mwi_step K mtw_mu0 s)
                                  (mwi_step K mtw_nu0 s))))
             zero
             (req_refl mtw_half)
             (req_trans
                (mtw_sumf (fun s : bool =>
                      abs (req_minus (mwi_step K mtw_mu0 s)
                                     (mwi_step K mtw_nu0 s))))
                (plus zero zero) zero
                (req_plus_compat
                   (abs (req_minus (mwi_step K mtw_mu0 true)
                                   (mwi_step K mtw_nu0 true))) zero
                   (abs (req_minus (mwi_step K mtw_mu0 false)
                                   (mwi_step K mtw_nu0 false))) zero
                   (Hz true) (Hz false))
                (req_plus_zero_l zero))).
  - exact (mult_zero mtw_half).
Defined.

(* ============================================================ *)
(* Section 3. Explicit instance of the degenerate world: the uniform *)
(* kernel (every row (1/2,1/2), rows identical) has TV(1) == 0.      *)
(* ============================================================ *)

Definition mwi_Kunif (s s' : bool) : Real := mtw_half.

Lemma mwi_Kunif_row : forall s : bool,
  req (plus (mwi_Kunif s true) (mwi_Kunif s false)) one.
Proof. intro s. unfold mwi_Kunif. exact mtw_hh_one. Defined.

Lemma mwi_Kunif_rows_eq : forall s s' : bool,
  req (mwi_Kunif s s') (mwi_Kunif true s').
Proof. intros s s'. unfold mwi_Kunif. exact (req_refl mtw_half). Defined.

Theorem mwi_degenerate_collapse_uniform :
  req (mtw_tv (mwi_step mwi_Kunif mtw_mu0) (mwi_step mwi_Kunif mtw_nu0)) zero.
Proof.
  exact (mwi_collapse_row_equal mwi_Kunif mwi_Kunif_row mwi_Kunif_rows_eq).
Defined.

(* ============================================================ *)
(* Section 4. Main statement: the two-sided mixing-window theorem    *)
(* (conjunction carried on the S01 base Set layer).                  *)
(*   Left arm = the degenerate side (the degenerate-world window     *)
(*   collapses); right arm = the existence side (a non-degenerate    *)
(*   world window genuinely exists: the conjunction of the exact     *)
(*   power law and the budget lower bound).                          *)
(* ============================================================ *)

Theorem mtw_window_two_sided :
  And
    (* degenerate side: a row-stochastic kernel with identical rows
       collapses in one step, TV == 0 *)
    (forall K : bool -> bool -> Real,
       (forall s : bool, req (plus (K s true) (K s false)) one) ->
       (forall s s' : bool, req (K s s') (K true s')) ->
       req (mtw_tv (mwi_step K mtw_mu0) (mwi_step K mtw_nu0)) zero)
    (* existence side: exact power law plus mixing-window budget lower
       bound in the non-degenerate world (World3) *)
    (And
       (forall n : nat,
          req (mtw_tv (mtw_titer n mtw_mu0) (mtw_titer n mtw_nu0))
              (mult (req_r_pow mtw_half n) (mtw_tv mtw_mu0 mtw_nu0)))
       (forall (n : nat) (B : Real),
          lt B (mult (req_r_pow mtw_half n) (mtw_tv mtw_mu0 mtw_nu0)) ->
          lt B (mtw_tv (mtw_titer n mtw_mu0) (mtw_titer n mtw_nu0)))).
Proof.
  split.
  - exact mwi_collapse_row_equal.
  - split.
    + exact mtw_tv_exact_iter.
    + exact mtw_no_mixing_below.
Defined.

(* ============================================================ *)
(* Assumption audit: everything closes (zero new assumptions).       *)
(* ============================================================ *)

Print Assumptions mwi_step.
Print Assumptions mwi_mult_zero_l.
Print Assumptions mwi_req_minus_self.
Print Assumptions mwi_abs_zero.
Print Assumptions mwi_collapse_row_equal.
Print Assumptions mwi_Kunif_row.
Print Assumptions mwi_Kunif_rows_eq.
Print Assumptions mwi_degenerate_collapse_uniform.
Print Assumptions mtw_window_two_sided.
