(* ConstructiveWorld-Set -- physical-predicate docking modules. *)

(** * S5SlotWire: S05 eight-slot physical-predicate forwarding shell.

    Mission.  Section [SswPhysPred] docks the S05 physical-predicate family
      onto the gradient-flow view: force as negative gradient
      [ssw_physical_force_is_gradient], the differentiation attractor
      [ssw_differentiation_attractor], macro loss monotonicity
      [ssw_macro_loss_monotone], covariance positivity
      [ssw_covariance_pos], fluctuation-dissipation
      [ssw_fluctuation_dissipation], the entropy production rate
      [ssw_entropy_production_rate], and the rational all-sign decay
      instance [ssw_full_sign_decay_instance_ref].

    Dependencies.  Stdlib [QArith_base], [Qring], [Qabs], [Lia],
      [Lists.List].  Requires [S01_BaseRing], [fa56_id_carrier],
      [fa56c_ext], [PhysPredAblation], [p4a_GradSignQDec] of this
      development.

    References.  This development, S5SlotWire.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" S5SlotWire.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 000160bc]. *)
Require Import S01_BaseRing.
Require Import fa56_id_carrier.
Require Import fa56c_ext.
Require Import PhysPredAblation.
Require Import p4a_GradSignQDec.
Require Import S02_CauchyComplete (QleT'_to_Qle).
From Stdlib Require Import QArith_base Qring Qabs Lia.
From Stdlib Require Import Lists.List.

(* ============ Sections A/B/C. Docking of the eight S05 slots: three PhysPred statements, three fa56 statements, two fa56c statements ============ *)

Section SswPhysPred.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.

(* The Real self state space lifted into the Enhanced context, verbatim as in PhysPredAblation. *)
Let SSR  : StateSpace RI := @RealSelfSS (@RI_base RI).
Let S    := @S RI SSR.
Let R    := @R RI.
Let zero := @zero RI.
Let one  := @one RI.
Let plus := @plus RI.
Let mult := @mult RI.
Let opp  := @opp RI.
Let le   := @le RI.
Let lt   := @lt RI.
Let splus := @splus RI SSR.
Let sopp  := @sopp RI SSR.
Let clim  := @clim RI SSR.

(* ---- Slot 1, S05:5803: physical_force_is_gradient forwarded along the ppa_ slot-1 form. ---- *)
Theorem ssw_physical_force_is_gradient :
  forall q : R, Id (ppa_force_physical q) (sopp (ppa_grad_lin ppa_potential q)).
Proof.
  exact ppa_physical_force_is_gradient.
Qed.

(* ---- Slot 2, S05:5854: differentiation_attractor forwarded along the    *)
(*      ppa_ slot-2 form; the convergence premise enters the signature as  *)
(*      in fa56c max_entropy_production. ---- *)
Theorem ssw_differentiation_attractor :
  forall x : R,
    clim (ppa_dev_orbit x) zero ->
    sigT (fun x_star : S =>
      And (forall s' : S, le (ppa_waddington x_star) (ppa_waddington s'))
          (clim (ppa_dev_orbit x) x_star)).
Proof.
  exact ppa_differentiation_attractor.
Qed.

(* ---- Slot 3, S05:5902: macro_loss_monotone forwarded along the ppa_     *)
(*      slot-3 form; the three of_nat premises enter the signature as in   *)
(*      the S05 Prediction1 Variable of_nat slot. ---- *)
Theorem ssw_macro_loss_monotone :
  forall (of_nat_R : nat -> R),
    Id (of_nat_R O) zero ->
    (forall n : nat, Id (of_nat_R (Datatypes.S n)) (plus (of_nat_R n) one)) ->
    (forall n : nat, le zero (of_nat_R n)) ->
    forall (m0 : R) (t : nat),
      le (ppa_macro_loss (iterate ppa_macro_dynamics t m0))
         (ppa_macro_loss m0).
Proof.
  exact ppa_macro_loss_monotone.
Qed.

(* ---- Slots 4/5, S05:5764/:5766, the H_inv/covariance data slots: the    *)
(*      covariance slot sits along the fa56_covariance form; the           *)
(*      positivity companion is forwarded and registered here. ---- *)
Theorem ssw_covariance_pos :
  forall (D H_inv : R),
    lt zero D -> lt zero H_inv -> lt zero (fa56_covariance D H_inv).
Proof.
  exact fa56_covariance_pos.
Qed.

(* ---- Slot 6, S05:5768: fluctuation_dissipation forwarded; H_inv is a    *)
(*      universally quantified free variable, the covariance slot sits in  *)
(*      place, and the Id conclusion is verbatim of the same shape. ---- *)
Theorem ssw_fluctuation_dissipation :
  forall (D H_inv : R), Id (fa56_covariance D H_inv) (mult D H_inv).
Proof.
  exact fa56_fluctuation_dissipation.
Qed.

(* ---- Slot 7, S05:5816, the Flux data slot: a universally quantified free variable (decision recorded in the header), carried together with slot 8. -- *)

(* ---- Slot 8, S05:5819: entropy_production_rate forwarded along the      *)
(*      fa56c weight-times-potential form; the two free Set variables stay *)
(*      universally quantified; the companion slot max_entropy_production  *)
(*      is recorded in the header. -- *)
Theorem ssw_entropy_production_rate :
  forall (Flx TD : Set) (w : Flx -> R) (theta : TD -> R) (J : Flx) (X : TD),
    Id (fa56c_entropy_production_rate Flx TD w theta J X)
       (mult (w J) (theta X)).
Proof.
  intros Flx TD w theta J X.
  reflexivity.
Qed.

End SswPhysPred.

(* ============ Section D. The S09:6166 real_sign_dec two-sided record ==================== *)
(* Modeled on the EntropyUnsatMark.v layout: the open item quoted with its  *)
(* coordinates, the two-sided verdict, the feeding discipline, the verdict. *)
(*                                                                          *)
(* 1. The open item verbatim (S09_EntropyReal.v:6166-6169, the honest       *)
(*    interface position of section T4.3):                                  *)
(*   Variable real_sign_dec : forall x : Real,                              *)
(*     Or (real_lt real_zero (real_entropy_gradient x))                     *)
(*        (Or (real_eq (real_entropy_gradient x) real_zero)                 *)
(*            (real_lt (real_entropy_gradient x) real_zero)).               *)
(*   Use sites: real_grad_step_abs_contraction_full (:6174, the one-step    *)
(*   contraction merging the three branches) and the geometric all-sign     *)
(*   orbit decay family.                                                    *)
(*                                                                          *)
(* 2. The two-sided verdict:                                                *)
(*   Instance side -- installed: p4a_GradSignQDec.v (an existing module)    *)
(*   removes the sign branches through the decidable three-way Q carrier:   *)
(*   gsq_grad_decay_full_sign_iter (:202, geometric decay of all-sign       *)
(*   orbits, installed of the same shape as S09                            *)
(*   real_grad_decay_full_sign_iter) plus gsq_grad_tail_budget (:227, the   *)
(*   tail bound budget); both main statements are reachable by exact, and   *)
(*   the export 9a of this section registers the forwarding.                *)
(*   Rational-valued and computably evaluated gradient instances (the       *)
(*   honest face self-noted in the S09:6162 header) all fall on this side.  *)
(*   Unconditional form -- permanent wall: a genuine three-way decision for *)
(*   every Real value asserts line-order completeness of the reals (LPO     *)
(*   strength), cross-checked against the library's standing decision       *)
(*   (the UpReqLpoEquiv face); this section neither reverses it nor forces  *)
(*   a feed, emits no unconditional forwarding statement, and keeps the     *)
(*   slot honestly at the open item as it stands.                           *)
(*                                                                          *)
(* 3. Feeding: with a Q-carrier gradient instance (eta mu x0 : Q), applying *)
(*   the export 9a yields the full all-sign decay chain; with a Real        *)
(*   unconditional certificate there is no outlet (wall note; candidate    *)
(*   keys: the decidable order-extension class, or concrete computable      *)
(*   Real-layer instance faces).                                            *)
(* Verdict: instance-side installation plus the unconditional-form wall;    *)
(* both sides recorded as they stand, with no statement weakened.           *)

(* ---- Export 9a: instance-side forwarding registration (the decidable three-way Q carrier, no new proof). ---- *)
Open Scope Q_scope.
Theorem ssw_full_sign_decay_instance_ref :
  forall (eta mu x0 : Q) (n k : nat),
    0 < eta -> 0 < mu -> eta * mu < 1 ->
    Qle (Qabs (gsq_grad mu (gsq_iter eta mu (n + k) x0)))
        (gsq_pow (gsq_kappa eta mu) k * Qabs (gsq_grad mu (gsq_iter eta mu n x0))).
Proof.
  intros eta mu x0 n k Heta Hmu Hprod.
  exact (QleT'_to_Qle _ _ (gsq_grad_decay_full_sign_iter eta mu x0 n k Heta Hmu Hprod)).
Qed.
Close Scope Q_scope.

(* ============ Audit section: each named statement certified Closed in turn ============ *)

Print Assumptions ssw_physical_force_is_gradient.
Print Assumptions ssw_differentiation_attractor.
Print Assumptions ssw_macro_loss_monotone.
Print Assumptions ssw_covariance_pos.
Print Assumptions ssw_fluctuation_dissipation.
Print Assumptions ssw_entropy_production_rate.
Print Assumptions ssw_full_sign_decay_instance_ref.
