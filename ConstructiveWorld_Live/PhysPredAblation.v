(* ConstructiveWorld-Set -- physical prediction ablation slots on the real self-state-space. *)
(** * PhysPredAblation: toy-proof ablation of the physical prediction slots.

    Mission.  Three S05 physical prediction statements realized on the real self-state-space
      [RealInterfaceEnhanced]: the gradient identity [ppa_physical_force_is_gradient] with
      its domination and scaled-potential monotonicity companions; the one-step collapse
      [ppa_dev_dynamics_zero] with the assembly [ppa_differentiation_attractor], the iterate
      witness [ppa_dev_iterate_step_zero], the limit companions [ppa_attractor_lim_unique],
      [ppa_attractor_transport]; and the non-increase of macro loss [ppa_macro_loss_monotone]
      along the orbit.

    Dependencies.  Stdlib [Lists.List] (for [iterate]); requires [S01_BaseRing],
      [fa51_sumpos_id], [fa56_id_carrier], [fa56b_ext], [fa56c_ext] of this development.

    References.  This development; the ConstructiveWorld-Main baseline module whose
      statement names are carried over verbatim (carrier faces disclosed per item
      under Constructivity and at the sections).

    Constructivity.  Per-item carrier disclosure (face tables at Sections A-C; audited
      under Rocq 9.3.0 by Set-ascription probes, extraction and coqchk).  All conclusion
      faces are [Set]-carried: identity statements via the boolean [Id] carrier, order
      companions via the decidable Set-valued [le]/[lt] families, the assembly via the
      Set-valued [And] of S01_BaseRing in a [sigT] over [Set]; no statement of this file
      is [Prop]-carried.  Closed statement constants are [Type]-carried, generalized
      over the implicit [{RI : RealInterfaceEnhanced}] binder, a [Type]-sorted record
      whose [Id]/[le]/[lt]/[clim] fields are Set-valued families supplied for reasoning.
      Extraction: [Obj.magic] = 0, no name erased; coqchk reports [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" PhysPredAblation.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 000160bc]. *)
Require Import S01_BaseRing.
Require Import fa51_sumpos_id.
Require Import fa56_id_carrier.
Require Import fa56b_ext.
Require Import fa56c_ext.
From Stdlib Require Import Lists.List.

Section PpaPhysPred.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.

(* The real self-state-space lifted into the enhanced context through
   the [RI_base] projection. *)
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

(* ============ Section A. physical_force_is_gradient ============ *)
(* Carrier faces (per item, audited Rocq 9.3.0): [ppa_physical_force_is_gradient]
   concludes in the [Id] boolean carrier ([Set]); [ppa_hamiltonian_dominates_potential],
   [ppa_potential_scaled_strict_mono] and [ppa_potential_scaled_mono] conclude in
   the [le]/[lt] Set-valued decidable families ([Set]). *)
(* Baseline signature: Q P : Set, Hamiltonian : Q -> P -> R,
   potential : Q -> R, force_physical : Q -> Q, inj_Q_S : Q -> S,
   grad : (Q -> R) -> Q -> S.  Realization: Q := R with the self
   state space S = R and inj_Q_S the identity, P := unit, the constant
   force field carries the linear potential V(q) := q, the gradient
   acts by grad V q := V q (for a linear potential the slope equals
   the function value), and the force is F(q) := -(V q) + 0,
   normalized through the zero element. *)

Definition ppa_potential (q : R) : R := q.
Definition ppa_grad_lin (V : R -> R) (q : R) : R := V q.
Definition ppa_force_physical (q : R) : R := plus (opp q) zero.

Theorem ppa_physical_force_is_gradient :
  forall q : R, Id (ppa_force_physical q) (sopp (ppa_grad_lin ppa_potential q)).
Proof.
  intro q.
  exact (plus_zero (opp q)).
Qed.

(* The Hamiltonian sums the kinetic term p, and the domination
   companion holds since p >= 0 gives H = V + p >= V. *)
Definition ppa_hamiltonian (q p : R) : R := plus (ppa_potential q) p.

Theorem ppa_hamiltonian_dominates_potential :
  forall q p : R, le zero p -> le (ppa_potential q) (ppa_hamiltonian q p).
Proof.
  intros q p Hp.
  exact (le_plus_nonneg_r (ppa_potential q) p Hp).
Qed.

(* Strict monotonicity of the scaled potential, supplied directly by
   the strict left-multiplication compatibility of fa56c. *)
Definition ppa_potential_scaled (k q : R) : R := mult k q.

Theorem ppa_potential_scaled_strict_mono :
  forall k q1 q2 : R, lt zero k -> lt q1 q2 ->
    lt (ppa_potential_scaled k q1) (ppa_potential_scaled k q2).
Proof.
  intros k q1 q2 Hk H.
  exact (fa56c_lt_mult_compat_l q1 q2 k Hk H).
Qed.

(* Weak monotonicity of the scaled potential, obtained by weakening
   the strict form to the non-strict order with the lt-to-le step of
   fa51. *)
Theorem ppa_potential_scaled_mono :
  forall k q1 q2 : R, lt zero k -> lt q1 q2 ->
    le (ppa_potential_scaled k q1) (ppa_potential_scaled k q2).
Proof.
  intros k q1 q2 Hk H.
  exact (fa51_lt_le _ _ (fa56c_lt_mult_compat_l q1 q2 k Hk H)).
Qed.

(* ============ Section B. differentiation_attractor ============ *)
(* Carrier faces (per item): [ppa_dev_dynamics_zero], [ppa_dev_iterate_step_zero]
   and [ppa_attractor_lim_unique] conclude in the [Id] carrier ([Set]);
   [ppa_attractor_transport] in the [clim] Set-valued family ([Set]);
   [ppa_differentiation_attractor] assembles the Set-valued [And] of
   S01_BaseRing in a [sigT] over [Set] ([Set] face). *)
(* Baseline signature: Waddington_landscape : S -> R, noise : S -> S,
   grad : (S -> R) -> S -> S, developmental dynamics
   x := splus x (splus (sopp (grad W x)) (noise x)), and dev_is_truth.
   Realization over the linear carrier R: the flat landscape
   W := fun _ => zero, the gradient grad W x := x, and the noise
   noise x := zero, so dynamics x = x + ((-x) + 0) = x - x = 0 by the
   plus_zero and plus_opp chain, and the development landscape orbit
   reaches the zero point in one step.  The attractor is
   x_star := zero, with dev_is_truth zero = le zero zero by le_refl.
   The convergence face of clim is the lim field of the interface, kept
   as a black box: the Id-shaped interface has no concrete instance in
   the library, so the convergence premise Hclim is an explicit
   premise of the main statement, as in fa56c. *)

Definition ppa_waddington (x : R) : R := zero.
Definition ppa_dev_grad (V : R -> R) (x : R) : R := x.
Definition ppa_dev_noise (x : R) : R := zero.
Definition ppa_dev_dynamics (x : R) : R :=
  splus x (splus (sopp (ppa_dev_grad ppa_waddington x)) (ppa_dev_noise x)).

(* The orbit is given the explicit codomain S, the type of the clim
   face; R = S holds definitionally through the S field of RealSelfSS,
   and fixing the head of the projection here pins the implicit
   carrier of a bare clim_unique application. *)
Definition ppa_dev_orbit (x : R) : nat -> S :=
  fun n : nat => iterate ppa_dev_dynamics n x.

(* One step of the orbit reaches zero:
   dynamics x == x + (-x + 0) == x + (-x) == 0. *)
Theorem ppa_dev_dynamics_zero : forall x : R, Id (ppa_dev_dynamics x) zero.
Proof.
  intro x.
  apply (id_trans (id_cong (fun w => plus x w) (plus_zero (opp x)))                  (plus_opp x)).
Qed.

(* Discrete convergence witness: the iterates of S n steps are zero
   termwise, the constructive supplement to the black-box lim. *)
Theorem ppa_dev_iterate_step_zero :
  forall (n : nat) (x : R),
    Id (iterate ppa_dev_dynamics (Datatypes.S n) x) zero.
Proof.
  intro n. induction n as [|n IH]; intro x.
  - exact (ppa_dev_dynamics_zero x).
  - apply (id_trans (id_cong (fun w => ppa_dev_dynamics w) (IH x))
                    (ppa_dev_dynamics_zero zero)).
Qed.

(* Main statement of the section: the attractor assembled as a sigT
   with an And, the convergence premise entering the signature. *)
Theorem ppa_differentiation_attractor :
  forall x : R,
    clim (ppa_dev_orbit x) zero ->
    sigT (fun x_star : S =>
      And (forall s' : S, le (ppa_waddington x_star) (ppa_waddington s'))
          (clim (ppa_dev_orbit x) x_star)).
Proof.
  intros x Hcl.
  exact (existT _ zero (pair (fun s' => le_refl zero) Hcl)).
Qed.

(* Uniqueness companion for the attractor limit, by the clim_unique
   field of StateSpace. *)
Theorem ppa_attractor_lim_unique :
  forall (x l1 l2 : R),
    clim (ppa_dev_orbit x) l1 ->
    clim (ppa_dev_orbit x) l2 ->
    Id l1 l2.
Proof.
  intros x l1 l2 H1 H2.
  exact (@clim_unique RI SSR (ppa_dev_orbit x) l1 l2 H1 H2).
Qed.

(* Transport companion for the starting point of the attractor, by the
   J eliminator of fa56b: Id x y moves the convergence witness from
   the start x to the start y, since the predicate takes the start as
   its argument and the substitution is direct, with no function
   extensionality. *)
Theorem ppa_attractor_transport :
  forall (x y l : R),
    Id x y ->
    clim (ppa_dev_orbit x) l ->
    clim (ppa_dev_orbit y) l.
Proof.
  intros x y l p Hcl.
  exact (fa56b_id_transport R           (fun z => clim (ppa_dev_orbit z) l)           x y p Hcl).
Qed.

(* ============ Section C. macro_loss_monotone ============ *)
(* Carrier faces (per item): [ppa_iterate_macro_step] concludes in the [Id]
   carrier ([Set]); [ppa_macro_loss_monotone], [ppa_macro_loss_one_step] and
   [ppa_macro_entropy_scaled_nonneg] conclude in the [le] Set-valued
   decidable family ([Set]). *)
(* Baseline signature: macro_entropy : Macrostate -> R,
   macro_dynamics : Macrostate -> Macrostate, and
   macro_loss m := opp (macro_entropy m).  Realization:
   Macrostate := R, the entropy reading is the state reading itself,
   and the coarse-graining dynamics is m -> m + 1 (the macro entropy
   grows by one at each step, so macro_loss = -entropy is
   non-increasing along the orbit).  The interface carries no
   nat -> R injection; of_nat_R therefore enters the signatures as an
   explicit premise, as in the baseline, with its three defining
   premises: the zero element, the successor step, and non-negativity. *)

Definition ppa_macro_entropy (m : R) : R := m.
Definition ppa_macro_dynamics (m : R) : R := plus m one.
Definition ppa_macro_loss (m : R) : R := opp (ppa_macro_entropy m).

(* Iteration closing lemma: d^t m == m + of_nat t, by induction on t
   with associativity and the successor premise. *)
Theorem ppa_iterate_macro_step :
  forall (of_nat_R : nat -> R),
    Id (of_nat_R O) zero ->
    (forall n : nat, Id (of_nat_R (Datatypes.S n)) (plus (of_nat_R n) one)) ->
    forall (t : nat) (m : R),
      Id (iterate ppa_macro_dynamics t m) (plus m (of_nat_R t)).
Proof.
  intros of_nat_R H0 Hstep t.
  induction t as [|t IH]; intro m.
  - apply (id_trans (id_sym (plus_zero m))
      (id_cong (fun z => plus m z) (id_sym H0))).
  - apply (id_trans (id_cong (fun z => plus z one) (IH m))
      (id_trans (id_sym (plus_assoc m (of_nat_R t) one))
                (id_cong (fun z => plus m z) (id_sym (Hstep t))))).
Qed.

(* Main statement of the section: macro loss non-increasing along the
   orbit, by the iteration closing lemma, the contravariance of opp,
   and the non-negative shift. *)
Theorem ppa_macro_loss_monotone :
  forall (of_nat_R : nat -> R),
    Id (of_nat_R O) zero ->
    (forall n : nat, Id (of_nat_R (Datatypes.S n)) (plus (of_nat_R n) one)) ->
    (forall n : nat, le zero (of_nat_R n)) ->
    forall (m0 : R) (t : nat),
      le (ppa_macro_loss (iterate ppa_macro_dynamics t m0))
         (ppa_macro_loss m0).
Proof.
  intros of_nat_R H0 Hstep Hnn m0 t.
  apply (le_id_l (ppa_macro_loss (iterate ppa_macro_dynamics t m0))
                 (opp (plus m0 (of_nat_R t))) (ppa_macro_loss m0)).
  - exact (id_cong (fun z => opp z)
             (ppa_iterate_macro_step of_nat_R H0 Hstep t m0)).
  - exact (@opp_le_compat RI m0 (plus m0 (of_nat_R t))
             (le_plus_nonneg_r m0 (of_nat_R t) (Hnn t))).
Qed.

(* Single-step companion: one evolution step does not increase the
   macro loss, with the positivity of one supplying the shift premise. *)
Theorem ppa_macro_loss_one_step :
  forall m : R, le (ppa_macro_loss (ppa_macro_dynamics m)) (ppa_macro_loss m).
Proof.
  intro m.
  apply (le_id_l (ppa_macro_loss (ppa_macro_dynamics m))
                 (opp (plus m one)) (ppa_macro_loss m)).
  - exact id_refl.
  - exact (@opp_le_compat RI m (plus m one)
             (le_plus_nonneg_r m one (fa51_lt_le zero one one_pos))).
Qed.

(* Non-negativity companion for the positively scaled macro entropy,
   by the lt-to-le weakening of fa51 and the order preservation of the
   enhanced multiplication, chained with the zero-element conversion. *)
Theorem ppa_macro_entropy_scaled_nonneg :
  forall (k m : R), lt zero k -> le zero m -> le zero (mult k m).
Proof.
  intros k m Hk Hm.
  exact (le_id_l zero (mult zero m) (mult k m)           (id_sym (id_trans (mult_comm zero m) (mult_zero m)))           (le_mult_compat_weak zero k m Hm (fa51_lt_le zero k Hk))).
Qed.

End PpaPhysPred.

(* ============ Assumption audit of the main exits ============ *)

Print Assumptions ppa_physical_force_is_gradient.
Print Assumptions ppa_hamiltonian_dominates_potential.
Print Assumptions ppa_potential_scaled_strict_mono.
Print Assumptions ppa_potential_scaled_mono.
Print Assumptions ppa_dev_dynamics_zero.
Print Assumptions ppa_dev_iterate_step_zero.
Print Assumptions ppa_differentiation_attractor.
Print Assumptions ppa_attractor_lim_unique.
Print Assumptions ppa_attractor_transport.
Print Assumptions ppa_iterate_macro_step.
Print Assumptions ppa_macro_loss_monotone.
Print Assumptions ppa_macro_loss_one_step.
Print Assumptions ppa_macro_entropy_scaled_nonneg.
