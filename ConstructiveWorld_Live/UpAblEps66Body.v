(* ConstructiveWorld-Set -- statement-family collection and instance carriers for the eps-0.66 ablation body. *)

(** * UpAblEps66Body: statement family and concrete instances for the eps-0.66 ablation body.

    Mission.  Statement family of the eps-0.66 ablation body over the abstract
      reals: the Boltzmann carrier [e66p_pi_old_boltzmann] with pointwise
      positivity [e66p_pi_old_pos]; the two-point sum [e66p_sum2] over [bool]
      with [e66p_sum2_ext], [e66p_sum2_le], [e66p_sum2_add], [e66p_sum2_linear];
      the term bound [e66p_term_le_of_lt]; the strict positivity
      [e66p_res_weight_pos] of the residual weight and its marginal composition
      [e66p_res_weight_pos_margin] over [e66p_real_advantage_pos_margin]; the
      instances [tx2_ppo66_enum], [tx2_ppo66_flag], [tx2_ppo66_flag_closed].

    Dependencies.  Stdlib [Extraction].  Requires [S01_BaseRing], [S02_CauchyComplete],
      [S03_QExp], [S04_RealExpLogConv], [S05_AlignmentGRPO], [S06_DiffSamplingGibbs],
      [S07_RealSetoidExpLog], [S08_RealMainlineDPO], [UpAblEps66Sum] of this development.

    References.  This development, UpAblEps66Body.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" UpAblEps66Body.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 00015ff4]. *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
From Stdlib Require Import Extraction.
Require Import S08_RealMainlineDPO.
Require Import UpAblEps66Sum.

(* ================== Section 1. The e66p_pi_old_boltzmann family ================== *)
(* Statement one: an instance of the real_pi_old_pos slot in Boltzmann form, the
   pointwise positivity of the policy.  It mirrors real_boltzmann_dist_r
   (inv(Z) * e^{-e(s)/D}) of S08_RealMainlineDPO together with its positivity
   conclusion real_boltzmann_dist_r_pos; this file states and proves it
   independently on its own carrier. *)

Section E66PPiOldPos.

Variable S : Type.

Definition e66p_pi_old_boltzmann (energy : S -> Real) (D Z : Real)
           (D_pos : real_lt real_zero D) (Z_pos : real_lt real_zero Z)
           (s : S) : Real :=
  real_mult (real_inv_pos Z Z_pos)
            (real_exp_neg (real_mult (real_inv_pos D D_pos) (energy s))).

Theorem e66p_pi_old_pos :
  forall (energy : S -> Real) (D Z : Real)
         (D_pos : real_lt real_zero D) (Z_pos : real_lt real_zero Z) (s : S),
    real_lt real_zero (e66p_pi_old_boltzmann energy D Z D_pos Z_pos s).
Proof.
  intros energy D Z D_pos Z_pos s.
  unfold e66p_pi_old_boltzmann.
  apply real_mult_positive.
  - apply real_inv_pos_pos.
  - apply real_exp_neg_pos.
Qed.

End E66PPiOldPos.

(* A two-point concrete sum: a finite sum over the bool carrier, enumerating
   true and false.  It mirrors the four-field summation interface of Section
   RealPPOMain of S08_RealMainlineDPO (extensionality, monotonicity,
   additivity, homogeneity): e66p_sum2 gives its concrete instance on the
   two-point carrier. *)

Definition e66p_sum2 (f : bool -> Real) : Real :=
  real_plus (f true) (f false).

Lemma e66p_sum2_ext : forall f g : bool -> Real,
  (forall s : bool, real_eq (f s) (g s)) ->
  real_eq (e66p_sum2 f) (e66p_sum2 g).
Proof.
  intros f g H. unfold e66p_sum2.
  apply (RealSetoid.real_eq_plus_compat (f true) (f false) (g true) (g false)).
  - apply H.
  - apply H.
Qed.

Lemma e66p_sum2_le : forall f g : bool -> Real,
  (forall s : bool, real_le (f s) (g s)) ->
  real_le (e66p_sum2 f) (e66p_sum2 g).
Proof.
  intros f g H. unfold e66p_sum2.
  apply real_le_plus_compat.
  - apply H.
  - apply H.
Qed.

(* Additivity: associativity and commutativity rearrange (a+b)+(c+d) into
   (a+c)+(b+d). *)
Lemma e66p_sum2_add : forall f g : bool -> Real,
  real_eq (e66p_sum2 (fun s : bool => real_plus (f s) (g s)))
          (real_plus (e66p_sum2 f) (e66p_sum2 g)).
Proof.
  intros f g. unfold e66p_sum2.
  assert (H2 : real_eq (real_plus (real_plus (f true) (g true)) (f false))
                       (real_plus (real_plus (f true) (f false)) (g true))).
  { apply (real_eq_trans _
             (real_plus (f true) (real_plus (g true) (f false)))).
    - apply real_eq_sym. apply real_plus_assoc.
    - apply (real_eq_trans _
               (real_plus (f true) (real_plus (f false) (g true)))).
      + apply (RealSetoid.real_eq_plus_compat (f true)
                 (real_plus (g true) (f false)) (f true)
                 (real_plus (f false) (g true))).
        * apply real_eq_refl.
        * apply real_plus_comm.
      + apply real_plus_assoc. }
  apply (real_eq_trans _
           (real_plus (real_plus (real_plus (f true) (g true)) (f false)) (g false))).
  - apply real_plus_assoc.
  - apply (real_eq_trans _
             (real_plus (real_plus (real_plus (f true) (f false)) (g true)) (g false))).
    + apply (RealSetoid.real_eq_plus_compat _ _ _ _ H2 (real_eq_refl (g false))).
    + apply real_eq_sym. apply real_plus_assoc.
Qed.

Lemma e66p_sum2_linear : forall (a : Real) (f : bool -> Real),
  real_eq (e66p_sum2 (fun s : bool => real_mult a (f s)))
          (real_mult a (e66p_sum2 f)).
Proof.
  intros a f. unfold e66p_sum2.
  apply real_eq_sym. apply real_distrib.
Qed.

(* Statement three: the strict positivity of the residual weight
   E := sum pi_old*adv.  The construction combines a single-point lower bound,
   pointwise non-negativity of the terms, monotonicity of the sum, the
   zero-sum identity rearrangement, and the composition of the order
   relations.  It supplies the instance for the premise
   real_lt real_zero real_ppo_res_weight of real_ppo_conservative_B of
   UpRealLeB. *)

Lemma e66p_term_le_of_lt : forall x : Real,
  real_lt real_zero x -> real_le real_zero x.
Proof.
  intros x H. left. exact H.
Qed.

Theorem e66p_res_weight_pos :
  forall (pi_old adv : bool -> Real),
    (forall s : bool, real_lt real_zero (pi_old s)) ->
    (forall s : bool, real_lt real_zero (adv s)) ->
    real_lt real_zero (e66p_sum2 (fun s : bool => real_mult (pi_old s) (adv s))).
Proof.
  intros pi_old adv Hpi Hadv.
  assert (Hft : real_lt real_zero (real_mult (pi_old true) (adv true))).
  { apply real_mult_positive; [apply Hpi | apply Hadv]. }
  assert (Hterm : forall s : bool, real_le real_zero (real_mult (pi_old s) (adv s))).
  { intro s. apply e66p_term_le_of_lt.
    apply real_mult_positive; [apply Hpi | apply Hadv]. }
  (* Single-point lower bound: 0 <= f(false) with the monotonicity of the sum
     gives f(true)+0 <= f(true)+f(false). *)
  assert (Hstep : real_le (real_plus (real_mult (pi_old true) (adv true)) real_zero)
                          (e66p_sum2 (fun s : bool => real_mult (pi_old s) (adv s)))).
  { unfold e66p_sum2. apply real_le_plus_compat.
    - apply real_le_refl.
    - apply Hterm. }
  assert (Hge : real_le (real_mult (pi_old true) (adv true))
                        (e66p_sum2 (fun s : bool => real_mult (pi_old s) (adv s)))).
  { apply (RealSetoid.real_le_id_l
             (real_mult (pi_old true) (adv true))
             (real_plus (real_mult (pi_old true) (adv true)) real_zero)
             (e66p_sum2 (fun s : bool => real_mult (pi_old s) (adv s)))).
    - apply real_eq_sym. apply real_plus_zero.
    - exact Hstep. }
  apply (real_lt_le_trans real_zero
           (real_mult (pi_old true) (adv true))
           (e66p_sum2 (fun s : bool => real_mult (pi_old s) (adv s)))).
  - exact Hft.
  - exact Hge.
Qed.

(* Statement two: the marginal-condition form of the real_advantage_pos slot.
   The conclusion is the source-file shape of the real_advantage_pos slot
   conditioned on the explicit margin premise beta*eps; the pointwise strict
   positivity of adv fails for an arbitrary adv, so the conditional form is
   its constructive reading.  The proof takes two steps: the positivity of
   multiplication gives 0 < beta*eps, and the transitivity composition of
   real_lt and real_le concludes. *)

Theorem e66p_real_advantage_pos_margin :
  forall (S : Type) (adv : S -> Real) (beta eps : Real),
    real_lt real_zero beta ->
    real_lt real_zero eps ->
    (forall s : S, real_le (real_mult beta eps) (adv s)) ->
    forall s : S, real_lt real_zero (adv s).
Proof.
  intros S adv beta eps Hbeta Heps Hm s.
  apply (real_lt_le_trans real_zero (real_mult beta eps) (adv s)).
  - apply real_mult_positive; [exact Hbeta | exact Heps].
  - exact (Hm s).
Qed.

(* Statement four: E > 0 under the full margin-premise chain, composing
   statements two and three: the pointwise margin premise beta*eps implies the
   pointwise strict positivity of adv, which in turn implies the strict
   positivity of the residual weight E := sum pi_old*adv; this is the
   reachable supply form of statement three under the margin premise. *)

Theorem e66p_res_weight_pos_margin :
  forall (pi_old adv : bool -> Real) (beta eps : Real),
    (forall s : bool, real_lt real_zero (pi_old s)) ->
    real_lt real_zero beta ->
    real_lt real_zero eps ->
    (forall s : bool, real_le (real_mult beta eps) (adv s)) ->
    real_lt real_zero (e66p_sum2 (fun s : bool => real_mult (pi_old s) (adv s))).
Proof.
  intros pi_old adv beta eps Hpi Hbeta Heps Hm.
  apply e66p_res_weight_pos.
  - exact Hpi.
  - intro s. apply (e66p_real_advantage_pos_margin bool adv beta eps Hbeta Heps Hm s).
Qed.

(* Extraction audit: the computational content of e66p_sum2 and
   e66p_pi_old_boltzmann. *)

Set Extraction Output Directory "attn/ab6ex".
Extraction "e66p_ab6_sum2" e66p_sum2.
Extraction "e66p_ab6_boltz" e66p_pi_old_boltzmann.

(* Assumption-closure audit: the assumption closure of each theorem below
   should be empty (Closed under the global context). *)

Print Assumptions e66p_pi_old_pos.
Print Assumptions e66p_sum2_ext.
Print Assumptions e66p_sum2_le.
Print Assumptions e66p_sum2_add.
Print Assumptions e66p_sum2_linear.
Print Assumptions e66p_res_weight_pos.
Print Assumptions e66p_real_advantage_pos_margin.
Print Assumptions e66p_res_weight_pos_margin.
(* ================== Section 2. The tx2_pi_old family ================== *)
(* Instance definitions: Boltzmann-form instances of the policy pi_old and of
   the importance ratio. *)

(* Instance of pi_old: the Boltzmann-form carrier e66p_pi_old_boltzmann, with
   positivity supplied by e66p_pi_old_pos. *)
Definition tx2_pi_old (energy : bool -> Real) (D Z : Real)
           (D_pos : real_lt real_zero D) (Z_pos : real_lt real_zero Z)
           (s : bool) : Real :=
  e66p_pi_old_boltzmann bool energy D Z D_pos Z_pos s.

(* Instance of the importance ratio rho: the real_importance_ratio_ of S08
   applied to the instance above (pi_old taken as e66p_pi_old_boltzmann, with
   its positivity premise taken as e66p_pi_old_pos). *)
Definition tx2_rho (pi_star energy : bool -> Real) (D Z : Real)
           (D_pos : real_lt real_zero D) (Z_pos : real_lt real_zero Z)
           (s : bool) : Real :=
  real_importance_ratio_ bool pi_star
    (e66p_pi_old_boltzmann bool energy D Z D_pos Z_pos)
    (e66p_pi_old_pos bool energy D Z D_pos Z_pos) s.

(* Main statement one: the instance over an arbitrary Set carrier with an
   arbitrary enumeration list.  The remaining premises: D > 0 and Z > 0 (the
   witnesses of the positivity of pi_old); beta > 0, eps > 0 and the pointwise
   margin beta*eps <= adv(s) (the beta*eps margin premise of the advantage
   slot). *)

Theorem tx2_ppo66_enum :
  forall (S0 : Set) (enum0 : list S0) (pi_star energy adv : S0 -> Real)
         (D Z beta epsR : Real)
         (D_pos : real_lt real_zero D) (Z_pos : real_lt real_zero Z)
         (Hbeta : real_lt real_zero beta),
    real_lt real_zero epsR ->
    (forall s : S0, real_le (real_mult beta epsR) (adv s)) ->
    real_le
      (e66s_sumf S0 enum0
         (fun s : S0 =>
            real_mult (e66p_pi_old_boltzmann S0 energy D Z D_pos Z_pos s)
              (real_mult
                 (real_min
                    (real_importance_ratio_ S0 pi_star
                       (e66p_pi_old_boltzmann S0 energy D Z D_pos Z_pos)
                       (e66p_pi_old_pos S0 energy D Z D_pos Z_pos) s)
                    (real_ppo_clip_ epsR
                       (real_importance_ratio_ S0 pi_star
                          (e66p_pi_old_boltzmann S0 energy D Z D_pos Z_pos)
                          (e66p_pi_old_pos S0 energy D Z D_pos Z_pos) s)))
                 (adv s))))
      (real_plus
         (e66s_sumf S0 enum0
            (fun s : S0 =>
               real_mult (e66p_pi_old_boltzmann S0 energy D Z D_pos Z_pos s)
                 (real_mult (real_importance_ratio_ S0 pi_star
                               (e66p_pi_old_boltzmann S0 energy D Z D_pos Z_pos)
                               (e66p_pi_old_pos S0 energy D Z D_pos Z_pos) s)
                            (adv s))))
         (e66s_sumf S0 enum0
            (fun s : S0 =>
               real_mult (e66p_pi_old_boltzmann S0 energy D Z D_pos Z_pos s)
                 (real_mult epsR (adv s))))).
Proof.
  intros S0 enum0 pi_star energy adv D Z beta epsR D_pos Z_pos Hbeta Heps Hm.
  exact (real_ppo_conservative_eps S0 (e66s_sumf S0 enum0)
           (e66s_real_sum_over_S_ext S0 enum0)
           (e66s_real_sum_over_S_le S0 enum0)
           (e66s_real_sum_over_S_add S0 enum0)
           pi_star (e66p_pi_old_boltzmann S0 energy D Z D_pos Z_pos)
           (e66p_pi_old_pos S0 energy D Z D_pos Z_pos)
           adv (e66p_real_advantage_pos_margin S0 adv beta epsR Hbeta Heps Hm)
           epsR epsR Heps).
Qed.

(* Main statement two: the instance on the two-point bool carrier.  The
   remaining premises take the same shape as in main statement one (the
   beta*eps margin premise). *)

Theorem tx2_ppo66_flag :
  forall (pi_star energy adv : bool -> Real) (D Z beta epsR : Real)
         (D_pos : real_lt real_zero D) (Z_pos : real_lt real_zero Z)
         (Hbeta : real_lt real_zero beta),
    real_lt real_zero epsR ->
    (forall s : bool, real_le (real_mult beta epsR) (adv s)) ->
    real_le
      (e66s_flag_sumf
         (fun s : bool =>
            real_mult (tx2_pi_old energy D Z D_pos Z_pos s)
              (real_mult
                 (real_min (tx2_rho pi_star energy D Z D_pos Z_pos s)
                           (real_ppo_clip_ epsR (tx2_rho pi_star energy D Z D_pos Z_pos s)))
                 (adv s))))
      (real_plus
         (e66s_flag_sumf
            (fun s : bool =>
               real_mult (tx2_pi_old energy D Z D_pos Z_pos s)
                 (real_mult (tx2_rho pi_star energy D Z D_pos Z_pos s) (adv s))))
         (e66s_flag_sumf
            (fun s : bool =>
               real_mult (tx2_pi_old energy D Z D_pos Z_pos s)
                 (real_mult epsR (adv s))))).
Proof.
  intros pi_star energy adv D Z beta epsR D_pos Z_pos Hbeta Heps Hm.
  exact (real_ppo_conservative_eps bool e66s_flag_sumf
           e66s_flag_ext e66s_flag_le e66s_flag_add
           pi_star (e66p_pi_old_boltzmann bool energy D Z D_pos Z_pos)
           (e66p_pi_old_pos bool energy D Z D_pos Z_pos)
           adv (e66p_real_advantage_pos_margin bool adv beta epsR Hbeta Heps Hm)
           epsR epsR Heps).
Qed.

(* Main statement three: the version with no premise slot, adv fixed to the
   Boltzmann form.  No premise remains at the advantage slot:
   adv := Boltzmann(energy2, D2, Z2), whose pointwise positivity is supplied
   unconditionally by e66p_pi_old_pos.  The remaining premises are only data
   positivity: D > 0, Z > 0, D2 > 0, Z2 > 0 and eps > 0, with no interface
   premise slots. *)

Theorem tx2_ppo66_flag_closed :
  forall (pi_star energy1 energy2 : bool -> Real) (D Z D2 Z2 epsR : Real)
         (D_pos : real_lt real_zero D) (Z_pos : real_lt real_zero Z)
         (D2_pos : real_lt real_zero D2) (Z2_pos : real_lt real_zero Z2),
    real_lt real_zero epsR ->
    real_le
      (e66s_flag_sumf
         (fun s : bool =>
            real_mult (tx2_pi_old energy1 D Z D_pos Z_pos s)
              (real_mult
                 (real_min (tx2_rho pi_star energy1 D Z D_pos Z_pos s)
                           (real_ppo_clip_ epsR (tx2_rho pi_star energy1 D Z D_pos Z_pos s)))
                 (e66p_pi_old_boltzmann bool energy2 D2 Z2 D2_pos Z2_pos s))))
      (real_plus
         (e66s_flag_sumf
            (fun s : bool =>
               real_mult (tx2_pi_old energy1 D Z D_pos Z_pos s)
                 (real_mult (tx2_rho pi_star energy1 D Z D_pos Z_pos s)
                            (e66p_pi_old_boltzmann bool energy2 D2 Z2 D2_pos Z2_pos s))))
         (e66s_flag_sumf
            (fun s : bool =>
               real_mult (tx2_pi_old energy1 D Z D_pos Z_pos s)
                 (real_mult epsR
                            (e66p_pi_old_boltzmann bool energy2 D2 Z2 D2_pos Z2_pos s))))).
Proof.
  intros pi_star energy1 energy2 D Z D2 Z2 epsR D_pos Z_pos D2_pos Z2_pos Heps.
  exact (real_ppo_conservative_eps bool e66s_flag_sumf
           e66s_flag_ext e66s_flag_le e66s_flag_add
           pi_star (e66p_pi_old_boltzmann bool energy1 D Z D_pos Z_pos)
           (e66p_pi_old_pos bool energy1 D Z D_pos Z_pos)
           (e66p_pi_old_boltzmann bool energy2 D2 Z2 D2_pos Z2_pos)
           (e66p_pi_old_pos bool energy2 D2 Z2 D2_pos Z2_pos)
           epsR epsR Heps).
Qed.

(* Concrete residual weight: the instance of sum pi_old*(eps*adv) on the bool
   carrier (supplied for extraction). *)

Definition tx2_flag_resid_weight (energy adv : bool -> Real) (D Z epsR : Real)
           (D_pos : real_lt real_zero D) (Z_pos : real_lt real_zero Z)
           : Real :=
  e66s_flag_sumf (fun s : bool =>
    real_mult (tx2_pi_old energy D Z D_pos Z_pos s) (real_mult epsR (adv s))).

(* Extraction audit: the computational content of tx2_pi_old, tx2_rho and
   tx2_flag_resid_weight. *)

Set Extraction Output Directory "attn/tx2ex".
Extraction "tx2_66body" tx2_pi_old tx2_rho tx2_flag_resid_weight.

(* Assumption-closure audit: the assumption closure of each theorem below
   should be empty (Closed under the global context). *)

Print Assumptions tx2_ppo66_enum.
Print Assumptions tx2_ppo66_flag.
Print Assumptions tx2_ppo66_flag_closed.
Print Assumptions tx2_flag_resid_weight.
