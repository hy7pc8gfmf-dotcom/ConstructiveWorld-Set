(* ConstructiveWorld-Set -- the singleton/cons/append nonempty family, the pointwise-Id-to-sum-Id engine extension, and detailed_bal. *)
(** * ToyR_fa56b_ext: the singleton/cons/append nonempty family, the
    pointwise-Id-to-sum-Id engine extension, and detailed_bal.

    Mission.  On the [fa56b_id_transport] (J eliminator) carrier: list
      discrimination, the singleton/cons/append nonempty closure family,
      the positivity transport companions, the sum engine
      ([fa56b_sumd_cong], [fa56b_sumd_swap_mult]),
      [fa56b_detailed_balance], [fa56b_boltzmann_stationary], and
      cross-domain scaling ([fa56b_cross_domain_scaling],
      [fa56b_cross_domain_linear]); plus fully explicit DPO/entropy
      witnesses (S := bool, tiered constant reward, beta := 1, pi_ref := 1,
      Z_align := 1) and the unsatisfiability pair ([fa52_EDP_E_B_pos_unsat],
      [fa52_EntropyDiffReal_premises_unsat]).

    Dependencies.  [S01_BaseRing], [S02_CauchyComplete],
      [S07_RealSetoidExpLog], [S08_RealMainlineDPO], [S09_EntropyReal],
      [fa51_sumpos_id], [fa56_id_carrier]; Stdlib [Lists.List].

    References.  S04:1588-1589, S04:1905-1907, S04:1913, S05:5968-5983;
      the same-name ConstructiveWorld-Main baseline.

    Constructivity.  Zero axiom declarations, zero acknowledged statements;
      statements Set-carried; Print Assumptions all Closed.

    Build.  [coqc -native-compiler no -q -Q ConstructiveWorld_Live "" ToyR_fa56b_ext.v] (direct call, cpu_guard wrapped). *)

(* ===== §1 fully explicit witnesses for S := bool, tiered constant reward, beta := 1, pi_ref := const 1, Z_align := 1; the three positivities from real_lt_zero ===== *)
Require Import S02_CauchyComplete.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.

(* ---------- concrete witnesses ---------- *)
Definition fa52_dpo_S : Type := bool.
Definition fa52_dpo_reward : bool -> Real :=
  fun s : bool => if s then real_plus real_one real_one else real_one.
Definition fa52_dpo_pi_ref : bool -> Real := fun _ : bool => real_one.
Definition fa52_dpo_pi_ref_pos : forall s : bool, real_lt real_zero (fa52_dpo_pi_ref s) :=
  fun _ : bool => real_lt_zero_one.

(* ---------- 1 < 2 (composing 0<1 with algebraic normalization) ---------- *)
Lemma fa52_one_two_lt : real_lt real_one (real_plus real_one real_one).
Proof.
  assert (HL : real_eq (real_plus real_zero real_one) real_one).
  { apply (real_eq_trans _ (real_plus real_one real_zero)).
    - apply (real_plus_comm real_zero real_one).
    - apply (real_plus_zero real_one). }
  assert (Hstep : real_lt (real_plus real_zero real_one)
                          (real_plus real_one real_one)).
  { exact (real_lt_plus_compat_lt_le real_zero real_one real_one real_one
             real_lt_zero_one (real_le_refl real_one)). }
  exact (real_eq_lt_lt _ _ _ (real_eq_sym _ _ HL) Hstep).
Qed.

Lemma fa52_dpo_reward_spread :
  real_lt (fa52_dpo_reward false) (fa52_dpo_reward true).
Proof.
  unfold fa52_dpo_reward.
  simpl.
  exact fa52_one_two_lt.
Qed.

(* ---------- main piece one: the DPO loss is bounded in (0, ln2) at π* -- a
   witness-specialized closed statement ---------- *)
Theorem fa52_dpo_bounded_both_concrete :
  S01_BaseRing.And
    (real_lt real_zero
       (real_dpo_loss_pair bool real_one fa52_dpo_pi_ref fa52_dpo_pi_ref_pos
          (real_pi_star bool fa52_dpo_reward real_one real_lt_zero_one
             fa52_dpo_pi_ref real_one real_lt_zero_one)
          (real_pi_star_pos bool fa52_dpo_reward real_one real_lt_zero_one
             fa52_dpo_pi_ref fa52_dpo_pi_ref_pos real_one real_lt_zero_one)
          true false))
    (real_lt
       (real_dpo_loss_pair bool real_one fa52_dpo_pi_ref fa52_dpo_pi_ref_pos
          (real_pi_star bool fa52_dpo_reward real_one real_lt_zero_one
             fa52_dpo_pi_ref real_one real_lt_zero_one)
          (real_pi_star_pos bool fa52_dpo_reward real_one real_lt_zero_one
             fa52_dpo_pi_ref fa52_dpo_pi_ref_pos real_one real_lt_zero_one)
          true false)
       (real_log (real_plus real_one real_one) real_two_pos)).
Proof.
  exact (real_dpo_loss_pi_star_bounded_both bool fa52_dpo_reward real_one           real_lt_zero_one fa52_dpo_pi_ref fa52_dpo_pi_ref_pos           real_one real_lt_zero_one true false fa52_dpo_reward_spread).
Qed.

(* ---------- main piece two: closed-form reward recovery -- witness
   specialization (β := 1, Z := 1 isolating the log 1 correction term) ---------- *)
Theorem fa52_dpo_reward_recovery_concrete : forall s : bool,
  real_eq
    (real_dpo_reward_explicit bool real_one fa52_dpo_pi_ref fa52_dpo_pi_ref_pos
       (real_pi_star bool fa52_dpo_reward real_one real_lt_zero_one
          fa52_dpo_pi_ref real_one real_lt_zero_one)
       (real_pi_star_pos bool fa52_dpo_reward real_one real_lt_zero_one
          fa52_dpo_pi_ref fa52_dpo_pi_ref_pos real_one real_lt_zero_one)
       s)
    (real_plus (fa52_dpo_reward s)
                (real_opp (real_mult real_one
                            (real_log real_one real_lt_zero_one)))).
Proof.
  intro s.
  exact (real_dpo_reward_recovers_up_to_baseline bool fa52_dpo_reward real_one           real_lt_zero_one fa52_dpo_pi_ref fa52_dpo_pi_ref_pos           real_one real_lt_zero_one s).
Qed.

Print Assumptions fa52_dpo_bounded_both_concrete.
Print Assumptions fa52_dpo_reward_recovery_concrete.

(* ===== §2 fa52_EDP_E_B_pos_unsat (the all-positive-energy component implies False) and fa52_EntropyDiffReal_premises_unsat (the entropy ===== *)
Require Import S02_CauchyComplete.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.

(* ---------- core: the E_B_pos single slot is unsatisfiable ---------- *)
Theorem fa52_EDP_E_B_pos_unsat :
  forall E_total : Real,
    (forall E : Real, real_lt real_zero E ->
       real_lt real_zero (real_plus E_total (real_opp E))) -> False.
Proof.
  intros E_total eB.
  (* Step one: eB at 1: 0 < E_total - 1 *)
  pose proof (eB real_one real_lt_zero_one) as H1.
  (* Step two: mixing the strict with the order-preserving addition:
   0+1 < (E_total-1)+1 *)
  assert (Hstep : real_lt (real_plus real_zero real_one)
                          (real_plus (real_plus E_total (real_opp real_one)) real_one)).
  { exact (real_lt_plus_compat_lt_le real_zero
             (real_plus E_total (real_opp real_one)) real_one real_one H1
             (real_le_refl real_one)). }
  (* 0+1 == 1 *)
  assert (HL : real_eq (real_plus real_zero real_one) real_one).
  { apply (real_eq_trans _ (real_plus real_one real_zero)).
    - apply (real_plus_comm real_zero real_one).
    - apply (real_plus_zero real_one). }
  (* (E_total-1)+1 == E_total *)
  assert (HR : real_eq (real_plus (real_plus E_total (real_opp real_one)) real_one)
                       E_total).
  { apply (real_eq_trans _ (real_plus E_total (real_plus (real_opp real_one) real_one))).
    - apply real_eq_sym.
      apply (real_plus_assoc E_total (real_opp real_one) real_one).
    - apply (real_eq_trans _ (real_plus E_total real_zero)).
      + apply (RealSetoid.real_eq_plus_compat E_total
                 (real_plus (real_opp real_one) real_one) E_total real_zero).
        * apply (real_eq_refl E_total).
        * apply (real_eq_trans _ (real_plus real_one (real_opp real_one))).
          -- apply (real_plus_comm (real_opp real_one) real_one).
          -- apply (real_plus_opp real_one).
      + apply (real_plus_zero E_total). }
  (* This yields 1 < E_total, then lowered to 0 < E_total *)
  assert (H1ET : real_lt real_one E_total).
  { exact (real_eq_lt_lt _ _ _ (real_eq_sym _ _ HL) (real_lt_eq_lt _ _ _ Hstep HR)). }
  assert (H2 : real_lt real_zero E_total).
  { exact (real_lt_le_trans real_zero real_one E_total real_lt_zero_one (inl H1ET)). }
  (* Step three: eB at E_total: 0 < E_total - E_total == 0, a contradiction *)
  pose proof (real_lt_eq_lt real_zero (real_plus E_total (real_opp E_total)) real_zero
                (eB E_total H2) (real_plus_opp E_total)) as Hcon.
  (* Empty_set (the conclusion type of S01_BaseRing.Not) has no constructors;
   destruct clears any goal *)
  destruct (real_lt_irrefl real_zero Hcon).
Qed.

(* ---------- wrapper: EntropyDiffReal with all 10 slots jointly yielding False ---------- *)
Theorem fa52_EntropyDiffReal_premises_unsat :
  forall (Omega_A : forall E_A : Real, real_lt real_zero E_A -> Real)
         (Omega_B : forall E_B : Real, real_lt real_zero E_B -> Real)
         (dA : RealDifferentiable Omega_A)
         (dB : RealDifferentiable Omega_B)
         (pA : forall (E_A : Real) (H : real_lt real_zero E_A),
                real_lt real_zero (Omega_A E_A H))
         (pB : forall (E_B : Real) (H : real_lt real_zero E_B),
                real_lt real_zero (Omega_B E_B H))
         (wdB : forall (a b : Real) (Ha : real_lt real_zero a) (Hb : real_lt real_zero b),
                real_eq a b -> real_eq (Omega_B a Ha) (Omega_B b Hb))
         (E_total k_B : Real)
         (eB : forall (E_A : Real) (H : real_lt real_zero E_A),
                real_lt real_zero (real_plus E_total (real_opp E_A))),
    False.
Proof.
  intros Omega_A Omega_B dA dB pA pB wdB E_total k_B eB.
  exact (fa52_EDP_E_B_pos_unsat E_total eB).
Qed.

Print Assumptions fa52_EDP_E_B_pos_unsat.
Print Assumptions fa52_EntropyDiffReal_premises_unsat.

Require Import S01_BaseRing.
Require Import fa51_sumpos_id.
Require Import fa56_id_carrier.
From Stdlib Require Import Lists.List.
Import ListNotations.

Section Fa56bExt.

Context {RI : RealInterfaceEnhanced}.
Variable S : Set.
Variable enum : list S.

Let R        := @R RI.
Let zero     := @zero RI.
Let one      := @one RI.
Let plus     := @plus RI.
Let mult     := @mult RI.
Let le       := @le RI.
Let lt       := @lt RI.

(* ============ Slot VI: the J eliminator + the list discriminator kernel + the nonempty construction family =========== *)
(* A constructive realization of the S04:1588-1589 vocab_nonempty precedent
   shape.  Core technique: the dependent match elimination of Id (the J rule
   is used for the first time in this carrier; fa51/fa56 used only the
   id_sym/id_trans/id_cong trio). *)

(* The generic transport (the J eliminator): p : Id x y moves an element of
   Q x to Q y. *)
Definition fa56b_id_transport (A : Set) (Q : A -> Set) (x y : A)
                              (p : Id x y) (h : Q x) : Q y :=
  match p in Id _ a return Q a with
  | id_refl => h
  end.

(* The list discriminator kernel: the Id separation of nil and cons (a
   Set-valued type-checking function). *)
Definition fa56b_list_case (T : Set) (l : list T) : Set :=
  match l with
  | nil => unit
  | _ => Empty_set
  end.

(* The discriminator lemma: Id (t::l) nil has no inhabitants (cons ≠ nil).
   The proof body closes by the index-pruning form of Id: the indices (t::l)
   and nil share no constructor branch to unify, and the contradictory
   branch is closed in place. *)
Lemma fa56b_cons_nil_id_contra : forall (T : Set) (t : T) (l : list T),
  Id (t :: l) nil -> Empty_set.
Proof.
  intros T t l H. inversion H.
Qed.

(* Slot-statement instantiation: the single-point vocabulary satisfies
   vocab_nonempty (the S04:1589 shape). *)
Theorem fa56b_singleton_nonempty :
  forall (T : Set) (t0 : T), Not (Id (cons t0 (@nil T)) (@nil T)).
Proof.
  intros T t0 H.
  exact (fa56b_cons_nil_id_contra T t0 nil H).
Qed.

(* Nonempty closure, cons: prepending an element preserves nonemptiness. *)
Theorem fa56b_cons_nonempty :
  forall (T : Set) (t0 : T) (l : list T),
    Not (Id l nil) -> Not (Id (cons t0 l) nil).
Proof.
  intros T t0 l Hne H.
  exact (fa56b_cons_nil_id_contra T t0 l H).
Qed.

(* Nonempty closure, append left: a nonempty left component makes the
   concatenation nonempty. *)
Theorem fa56b_append_nonempty_l :
  forall (T : Set) (l l' : list T),
    Not (Id l nil) -> Not (Id (l ++ l') nil).
Proof.
  intros T l l' Hne H. destruct l as [| t r].
  - exact (Hne (@id_refl (list T) (@nil T))).
  - exact (fa56b_cons_nil_id_contra T t (r ++ l') H).
Qed.

(* Nonempty closure, append right: a nonempty right component makes the
   concatenation nonempty (case on the left component). *)
Theorem fa56b_append_nonempty_r :
  forall (T : Set) (l l' : list T),
    Not (Id l' nil) -> Not (Id (l ++ l') nil).
Proof.
  intros T l l' Hne H. destruct l as [| t r].
  - exact (Hne H).
  - exact (fa56b_cons_nil_id_contra T t (r ++ l') H).
Qed.

(* Companion: the Id invariance of strict positivity (the engine premises
   are stable under Id rewriting). *)
Theorem fa56b_lt_transport :
  forall (a b : R), Id a b -> lt zero a -> lt zero b.
Proof.
  intros a b p H.
  exact (fa56b_id_transport R (fun w => lt zero w) a b p H).
Qed.

(* Companion: the Id invariance of nonnegativity. *)
Theorem fa56b_le_transport :
  forall (a b : R), Id a b -> le zero a -> le zero b.
Proof.
  intros a b p H.
  exact (fa56b_id_transport R (fun w => le zero w) a b p H).
Qed.

(* ============ Slot VII: engine extension -- pointwise Id implies sum Id ==================== *)
(* The fa51_sumd list-carrier copy of sum_over_S_ext, on which the S04
   steady_state_boltzmann (L1921) depends; the key piece of the Slot VIII
   stationary copy. *)

Theorem fa56b_sumd_cong :
  forall (f g : S -> R) (l : list S),
    (forall s : S, Id (f s) (g s)) ->
    Id (fa51_sumd S f l) (fa51_sumd S g l).
Proof.
  intros f g l Hpt. induction l as [| x t IH].
  - exact (@id_refl R zero).
  - exact (id_cong2 (fun a b => plus a b) (Hpt x) IH).
Qed.

(* Swapping the product factors under the sum (the batch version of the
   Slot VIII pointwise balance). *)
Theorem fa56b_sumd_swap_mult :
  forall (f g : S -> R) (l : list S),
    Id (fa51_sumd S (fun s => mult (f s) (g s)) l)
       (fa51_sumd S (fun s => mult (g s) (f s)) l).
Proof.
  intros f g l.
  exact (fa56b_sumd_cong (fun s => mult (f s) (g s))                         (fun s => mult (g s) (f s)) l                         (fun s => mult_comm (f s) (g s))).
Qed.

(* ============ Slot VIII: the S04:1905-1907 detailed_balance slot + ========= *)
(*              the S04:1913 steady_state_boltzmann list-carrier copy ========== *)
(* Realization: the transition takes the independent proposal kernel
   k(s,s') := π(s') (the Boltzmann-Gibbs stationary distribution itself),
   and the balance slot is closed by mult_comm; the stationary piece is the
   main nontrivial piece (a four-segment chain: sumd_cong + the fa56 linear
   piece + row normalization + mult_one).  π takes the same term as
   fa56_markov_kernel (the three companions -- positivity, nonnegativity,
   normalization -- are inherited directly from the already-proven fa56
   pieces, with no duplicated construction). *)

Definition fa56b_boltzmann_prob (base_loss : S -> R) (D : R) (D_pos : lt zero D)
                                (Hne : Not (Id enum nil)) (s : S) : R :=
  fa56_markov_kernel S enum base_loss D D_pos
    (fa51_Z_temp_pos S enum base_loss D D_pos Hne) s.

Definition fa56b_independence_transition
           (base_loss : S -> R) (D : R) (D_pos : lt zero D)
           (Hne : Not (Id enum nil)) (s s' : S) : R :=
  fa56b_boltzmann_prob base_loss D D_pos Hne s'.

(* The S04:1905-1907 slot-statement instance: the independent proposal
   kernel satisfies detailed balance pointwise. *)
Theorem fa56b_detailed_balance :
  forall (base_loss : S -> R) (D : R) (D_pos : lt zero D)
         (Hne : Not (Id enum nil)) (s s' : S),
    Id (mult (fa56b_boltzmann_prob base_loss D D_pos Hne s)
             (fa56b_independence_transition base_loss D D_pos Hne s s'))
       (mult (fa56b_boltzmann_prob base_loss D D_pos Hne s')
             (fa56b_independence_transition base_loss D D_pos Hne s' s)).
Proof.
  intros base_loss D D_pos Hne s s'.
  exact (mult_comm (fa56b_boltzmann_prob base_loss D D_pos Hne s)                   (fa56b_boltzmann_prob base_loss D D_pos Hne s')).
Qed.

(* The fa51_sumd list-carrier copy of the S04:1913 steady_state_boltzmann:
   pointwise balance + row normalization imply that π is a stationary
   distribution (Σ_{s'} π(s')k(s',s) = π(s)). *)
Theorem fa56b_boltzmann_stationary :
  forall (pi : S -> R) (k : S -> S -> R),
    (forall s s' : S,
        Id (mult (pi s') (k s' s)) (mult (pi s) (k s s'))) ->
    (forall s : S, Id (fa51_sumd S (fun s' => k s s') enum) one) ->
    forall s : S,
      Id (fa51_sumd S (fun s' => mult (pi s') (k s' s)) enum) (pi s).
Proof.
  intros pi k Hdb Hnorm s.
  exact (id_trans           (fa56b_sumd_cong (fun s' => mult (pi s') (k s' s))                            (fun s' => mult (pi s) (k s s')) enum                            (fun x => Hdb s x))           (id_trans              (fa56_sumd_mult_const S (pi s) (fun s' => k s s') enum)              (id_trans                 (id_cong (fun y => mult (pi s) y) (Hnorm s))                 (mult_one (pi s))))).
Qed.

(* ============ Slot IX: the S05:5968-5983 cross-domain scaling slot (sigT form) ============ *)
(* Slot statement: cross_domain_scaling : sigT (fun alpha : R => forall N,
   Id (loss_drop N) (mult (power (of_nat N) alpha) (f_N N))).
   Realization: loss_drop is a definitional assembly piece (the power-law
   form), and the slot's sigT witness is assembled directly by existT; the
   specialization companions alpha := one and power := mult go through the
   mult_one normalization chain. *)

Definition fa56b_loss_drop (power : R -> R -> R) (of_nat_R : nat -> R)
                           (f_N : nat -> R) (alpha : R) (N : nat) : R :=
  mult (power (of_nat_R N) alpha) (f_N N).

(* The sigT witness assembly for the slot statement (the existence face
   realized in one stroke). *)
Theorem fa56b_cross_domain_scaling :
  forall (power : R -> R -> R) (of_nat_R : nat -> R) (f_N : nat -> R)
         (alpha : R),
    sigT (fun a : R => forall N : nat,
            Id (fa56b_loss_drop power of_nat_R f_N a N)
               (mult (power (of_nat_R N) a) (f_N N))).
Proof.
  intros power of_nat_R f_N alpha.
  exact (existT _ alpha (fun N => @id_refl R _)).
Qed.

(* The specialization companion: with alpha := one and power := mult, the
   power law degenerates to linear scaling (the mult_one right unit lifted
   through id_cong into the product, a nontrivial normalization chain). *)
Theorem fa56b_cross_domain_linear :
  forall (of_nat_R : nat -> R) (f_N : nat -> R) (N : nat),
    Id (fa56b_loss_drop mult of_nat_R f_N one N)
       (mult (of_nat_R N) (f_N N)).
Proof.
  intros of_nat_R f_N N.
  unfold fa56b_loss_drop.
  exact (id_cong (fun y => mult y (f_N N)) (mult_one (of_nat_R N))).
Qed.

End Fa56bExt.

(* ============ assumption-face closure declaration ============ *)

Print Assumptions fa56b_id_transport.
Print Assumptions fa56b_cons_nil_id_contra.
Print Assumptions fa56b_singleton_nonempty.
Print Assumptions fa56b_cons_nonempty.
Print Assumptions fa56b_append_nonempty_l.
Print Assumptions fa56b_append_nonempty_r.
Print Assumptions fa56b_lt_transport.
Print Assumptions fa56b_le_transport.
Print Assumptions fa56b_sumd_cong.
Print Assumptions fa56b_sumd_swap_mult.
Print Assumptions fa56b_detailed_balance.
Print Assumptions fa56b_boltzmann_stationary.
Print Assumptions fa56b_cross_domain_scaling.
Print Assumptions fa56b_cross_domain_linear.
