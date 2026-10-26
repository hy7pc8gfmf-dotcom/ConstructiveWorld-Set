(* Convergence step calculator for the S06 differentiable-sampling
   contraction face (sdc_ prefix). *)

(** * abl_s06_step_calc: from accuracy to step count on the Gibbs
      contraction face.

    Mission.  (1) A nat-level fixed-point part: the decay enumerator
      [sdc_k_enum] with its first-break stop, correctness on the
      strict and the exact face, minimality witnesses, and
      fuel-sufficiency companions.  (2) An Id-face mirror section over
      the host certificate subset: the rate, the contraction
      projections, the honest archimedes-slot calculator, and the
      end-to-end convergence projections.  (3) Smoke evaluations.

    Dependencies.  Stdlib [List], [PeanoNat], [Arith], [Lia],
      [Extraction]; requires [S01_BaseRing], [S02_CauchyComplete],
      [S03_QExp], [S04_RealExpLogConv] and [S06_DiffSamplingGibbs]
      (the last without import; uses fully qualified).

    References.  ConstructiveWorld-Main, module [abl_s06_step_calc].

    Constructivity.  Set-level carriers throughout: step witnesses on
      nat in sigT form, no Prop pushed into Set goals.  The archimedes
      slot is an honest-interface premise mirroring the host
      certificate; the executable face is carried by the nat-level
      part.  Extraction with [Obj.magic] = 0; the trailing
      [Print Assumptions] audit reports [Closed].

    Build.  [coqc -native-compiler no -Q . "" abl_s06_step_calc.v];
      artifact magic [436f7121 00015ff4]. *)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Extraction.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S06_DiffSamplingGibbs.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lia.

(* ============================================================ *)
(* Part 2: the fixed-point enumerator for the contraction rate (genuine
   fixpoints, strict first-break face, Set carriers).  The contraction
   rate [kappa = p/q] (with [p < q]), the initial value [A] and the
   budget [E] are given in fixed-point form; the enumerator returns the
   first [N] with the iterated value strictly below [E].  Order bounds
   travel on the NatLe carrier, strict bounds as [NatLe (S n)]. *)
(* ============================================================ *)

(* Ceiling division [(a+q-1)/q] for [q >= 1]; ceiling keeps the
   upper-bound direction. *)
Definition sdc_ceil_div (a q : nat) : nat := Nat.div (a + q - 1) q.

Lemma sdc_ceil_div_le : forall a q,
  NatLe 1 q -> NatLe a (sdc_ceil_div a q * q).
Proof.
  intros a q Hq. pose proof (NatLe_drop 1 q Hq) as Hq'.
  unfold sdc_ceil_div.
  assert (Hq1 : (0 < q)%nat) by lia.
  pose proof (Nat.div_mod_eq (a + q - 1) q) as Hdm.
  pose proof (Nat.mod_upper_bound (a + q - 1) q (proj2 (Nat.neq_0_lt_0 q) Hq1)) as Hmb.
  apply (NatLe_lift _ _). lia.
Qed.

(* Decay step: one fixed-point multiplication of [x] by [kappa = p/q]
   (with ceiling). *)
Definition sdc_iter (p q x : nat) : nat := sdc_ceil_div (x * p) q.

Lemma sdc_iter_step_bound : forall p q x,
  NatLe 1 q -> NatLe (x * p) (sdc_iter p q x * q).
Proof.
  intros p q x Hq. unfold sdc_iter. apply (sdc_ceil_div_le (x * p) q Hq).
Qed.

(* Iterated power: the [k]-fold composition of [sdc_iter] (the ceiling
   face of the geometric decay sequence). *)
Fixpoint sdc_pow_iter (p q x k : nat) : nat :=
  match k with
  | O => x
  | Datatypes.S k' => sdc_iter p q (sdc_pow_iter p q x k')
  end.

(* Composition swap: one step then [k] iterations equals [k] iterations
   then one step ([S k] compositions either way). *)
Lemma sdc_pow_iter_comm : forall p q x k,
  Id (sdc_pow_iter p q (sdc_iter p q x) k)
     (sdc_iter p q (sdc_pow_iter p q x k)).
Proof.
  intros p q x k. induction k as [| k IH].
  - simpl. apply id_refl.
  - simpl. exact (id_cong (sdc_iter p q) IH).
Qed.

(* Enumerator: a fuel-bounded fixpoint stopping at the first step where
   [x] is strictly below [e] (returning the steps taken), otherwise
   taking a decay step and searching on ([Nat.ltb] test, strict
   termination face). *)
Fixpoint sdc_k_enum (fuel p q x e : nat) : nat :=
  match fuel with
  | O => O
  | Datatypes.S f =>
      if Nat.ltb x e then O else Datatypes.S (sdc_k_enum f p q (sdc_iter p q x) e)
  end.

(* Exact-face invariant: the ceiling value always dominates the exact
   geometric value ([x * p^k <= iter^k(x) * q^k]). *)
Lemma sdc_pow_iter_exact_ge : forall p q x k,
  NatLe 1 p -> NatLe 1 q -> NatLe (x * p ^ k) (sdc_pow_iter p q x k * q ^ k).
Proof.
  intros p q x k Hp Hq. induction k as [| k IH].
  - apply (NatLe_lift _ _). simpl. lia.
  - pose proof (NatLe_drop _ _ IH) as IH'.
    apply (NatLe_lift _ _). simpl.
    apply (Nat.le_trans _ (sdc_pow_iter p q x k * q ^ k * p)).
    + rewrite (Nat.mul_comm p (p ^ k)).
      rewrite (Nat.mul_assoc x (p ^ k) p).
      apply (Nat.mul_le_mono_r _ _ p). exact IH'.
    + pose proof (sdc_iter_step_bound p q (sdc_pow_iter p q x k) Hq) as Hstep.
      pose proof (NatLe_drop _ _ Hstep) as Hstep'.
      rewrite <- (Nat.mul_assoc (sdc_pow_iter p q x k) (q ^ k) p).
      rewrite (Nat.mul_comm (q ^ k) p).
      rewrite (Nat.mul_assoc (sdc_pow_iter p q x k) p (q ^ k)).
      apply (Nat.le_trans _ (sdc_iter p q (sdc_pow_iter p q x k) * q * q ^ k)).
      * apply (Nat.mul_le_mono_r _ _ (q ^ k)). exact Hstep'.
      * rewrite (Nat.mul_assoc (sdc_iter p q (sdc_pow_iter p q x k)) q (q ^ k)).
        apply (Nat.le_refl _).
Qed.

(* Correctness (strict first-break face): whenever the break is
   reachable within the fuel, the returned step has its ceiling value
   strictly below [e] (strict order bound carried by [NatLe (S n) e]).
   The reachability witness sits on sigT, prod and NatLe carriers. *)
Theorem sdc_k_enum_correct : forall fuel p q x e,
  (sigT (fun k : nat =>
    prod (NatLe k fuel) (NatLe (Datatypes.S (sdc_pow_iter p q x k)) e))) ->
  NatLe (Datatypes.S (sdc_pow_iter p q x (sdc_k_enum fuel p q x e))) e.
Proof.
  intros fuel. induction fuel as [| f IH]; intros p q x e Hterm.
  - destruct Hterm as [k [Hk Hbound]].
    pose proof (NatLe_drop k 0 Hk) as Hk'.
    assert (Hk0 : k = 0%nat) by lia. subst k. simpl. exact Hbound.
  - simpl. destruct (Nat.ltb x e) eqn:Hlt.
    + apply (NatLe_lift _ _). exact (proj1 (Nat.ltb_lt x e) Hlt).
    + assert (Hge : (e <= x)%nat) by (apply (proj1 (Nat.ltb_ge x e)); exact Hlt).
      destruct Hterm as [k [Hk Hbound]].
      pose proof (NatLe_drop k (Datatypes.S f) Hk) as Hk'.
      destruct k as [| k'].
      * pose proof (NatLe_drop (Datatypes.S (sdc_pow_iter p q x 0)) e Hbound)
          as Hb'.
        simpl in Hb'. lia.
      * simpl in Hbound.
        revert Hbound. destruct (sdc_pow_iter_comm p q x k'). intros Hbound.
        assert (Hk2 : (k' <= f)%nat) by lia.
        assert (Hterm' : sigT (fun k0 : nat =>
                          prod (NatLe k0 f)
                               (NatLe (Datatypes.S
                                  (sdc_pow_iter p q (sdc_iter p q x) k0)) e))).
        { exact (existT _ k' (pair (NatLe_lift k' f Hk2) Hbound)). }
        specialize (IH p q (sdc_iter p q x) e Hterm').
        simpl.
        destruct (sdc_pow_iter_comm p q x
                    (sdc_k_enum f p q (sdc_iter p q x) e)).
        exact IH.
Qed.

(* First-break minimality witness: whenever the break is reachable,
   every step [j] before the returned [N] (with [S j <= N]) still has
   its ceiling value at least [e] - the readout is the first step below
   the budget. *)
Theorem sdc_k_enum_minimal : forall fuel p q x e,
  (sigT (fun k : nat =>
    prod (NatLe k fuel) (NatLe (Datatypes.S (sdc_pow_iter p q x k)) e))) ->
  forall j : nat, NatLe (Datatypes.S j) (sdc_k_enum fuel p q x e) ->
  NatLe e (sdc_pow_iter p q x j).
Proof.
  intros fuel. induction fuel as [| f IH]; intros p q x e Hterm j Hj.
  - exfalso. pose proof (NatLe_drop (Datatypes.S j) 0 Hj) as Hj'. lia.
  - simpl. destruct (Nat.ltb x e) eqn:Hlt.
    + simpl in Hj. rewrite Hlt in Hj.
      exfalso. pose proof (NatLe_drop (Datatypes.S j) 0 Hj) as Hj'. lia.
    + simpl in Hj. rewrite Hlt in Hj.
      assert (Hge : (e <= x)%nat) by (apply (proj1 (Nat.ltb_ge x e)); exact Hlt).
      pose proof (NatLe_drop (Datatypes.S j)
                    (Datatypes.S (sdc_k_enum f p q (sdc_iter p q x) e)) Hj)
        as Hj'.
      destruct j as [| j'].
      * simpl. apply (NatLe_lift e x). exact Hge.
      * simpl in Hj'.
        assert (Hj2 : NatLe (Datatypes.S j')
                        (sdc_k_enum f p q (sdc_iter p q x) e))
          by (apply (NatLe_lift _ _); lia).
        assert (Hterm' : sigT (fun k0 : nat =>
                          prod (NatLe k0 f)
                               (NatLe (Datatypes.S
                                  (sdc_pow_iter p q (sdc_iter p q x) k0)) e))).
        { destruct Hterm as [k [Hk Hbound]].
          pose proof (NatLe_drop k (Datatypes.S f) Hk) as Hk'.
          destruct k as [| k'].
          - pose proof (NatLe_drop (Datatypes.S (sdc_pow_iter p q x 0)) e Hbound)
              as Hb'.
            simpl in Hb'. lia.
          - simpl in Hbound.
            revert Hbound. destruct (sdc_pow_iter_comm p q x k'). intros Hbound.
            assert (Hk2 : (k' <= f)%nat) by lia.
            exact (existT _ k' (pair (NatLe_lift k' f Hk2) Hbound)). }
        specialize (IH p q (sdc_iter p q x) e Hterm' j' Hj2).
        simpl. destruct (sdc_pow_iter_comm p q x j'). exact IH.
Qed.

(* First-break witness packaging: whenever reachable, the readout [N]
   carries both certificates - step [N] strictly below the budget and
   every earlier step still at or above it (sigT, prod and forall-nat
   carriers). *)
Theorem sdc_k_enum_first_break : forall fuel p q x e,
  (sigT (fun k : nat =>
    prod (NatLe k fuel) (NatLe (Datatypes.S (sdc_pow_iter p q x k)) e))) ->
  sigT (fun N : nat =>
    prod (NatLe (Datatypes.S (sdc_pow_iter p q x N)) e)
         (forall j : nat, NatLe (Datatypes.S j) N ->
                          NatLe e (sdc_pow_iter p q x j))).
Proof.
  intros fuel p q x e H.
  exists (sdc_k_enum fuel p q x e). split.
  - exact (sdc_k_enum_correct fuel p q x e H).
  - exact (sdc_k_enum_minimal fuel p q x e H).
Qed.

(* Nat form of the log-modulus equation: termination gives
   [x * p^N <= e * q^N] (equivalent under log monotonicity); a strict
   first break [y < e] drops to [y <= e] via [NatLe (S y) e]. *)
Theorem sdc_k_enum_logface : forall fuel p q x e,
  NatLe 1 p -> NatLe 1 q ->
  (sigT (fun k : nat =>
    prod (NatLe k fuel) (NatLe (Datatypes.S (sdc_pow_iter p q x k)) e))) ->
  NatLe (x * p ^ sdc_k_enum fuel p q x e)
        (e * q ^ sdc_k_enum fuel p q x e).
Proof.
  intros fuel p q x e Hp Hq Hterm.
  pose proof (sdc_k_enum_correct fuel p q x e Hterm) as H1.
  pose proof (sdc_pow_iter_exact_ge p q x (sdc_k_enum fuel p q x e) Hp Hq) as H2.
  pose proof (NatLe_drop _ _ H1) as H1'.
  pose proof (NatLe_drop _ _ H2) as H2'.
  apply (NatLe_lift _ _).
  apply (Nat.le_trans _
           (sdc_pow_iter p q x (sdc_k_enum fuel p q x e)
              * q ^ sdc_k_enum fuel p q x e)).
  - exact H2'.
  - apply (Nat.mul_le_mono_r _ _ (q ^ sdc_k_enum fuel p q x e)).
    lia.
Qed.

(* Strict decay companions and fuel-sufficiency witnesses (closing the
   decay premise at call sites). *)

(* Decay kernel: when [x*p + q <= x*q], the ceiling step strictly
   decreases (floor criterion [d*q <= a] below [x*q]). *)
Lemma sdc_iter_lt_decay : forall p q x,
  NatLe 1 q -> NatLe (x * p + q) (x * q) ->
  NatLe (Datatypes.S (sdc_iter p q x)) x.
Proof.
  intros p q x Hq Hdecay.
  pose proof (NatLe_drop 1 q Hq) as Hq'.
  pose proof (NatLe_drop (x * p + q) (x * q) Hdecay) as Hdecay'.
  unfold sdc_iter, sdc_ceil_div.
  assert (Hq1 : (0 < q)%nat) by lia.
  assert (Hcore : (Nat.div (x * p + q - 1) q < x)%nat).
  { destruct (Nat.lt_ge_cases (Nat.div (x * p + q - 1) q) x) as [Hlt | Hge].
    - exact Hlt.
    - exfalso.
      assert (Hmon : (x * q <= Nat.div (x * p + q - 1) q * q)%nat)
        by (apply Nat.mul_le_mono_r; exact Hge).
      pose proof (Nat.div_mod_eq (x * p + q - 1) q) as Hdm.
      pose proof (Nat.mod_upper_bound (x * p + q - 1) q (proj2 (Nat.neq_0_lt_0 q) Hq1)) as Hmb.
      lia. }
  apply (NatLe_lift _ _). lia.
Qed.

(* Halving-domain decay: for [2*p <= q] and [x >= 2] the step strictly
   decreases ([x*(q-p) >= 2*(q-p) >= q]). *)
Lemma sdc_iter_lt_half : forall p q x,
  NatLe 1 p -> NatLe (2 * p) q -> NatLe 2 x ->
  NatLe (Datatypes.S (sdc_iter p q x)) x.
Proof.
  intros p q x Hp H2p Hx.
  pose proof (NatLe_drop 1 p Hp) as Hp'.
  pose proof (NatLe_drop (2 * p) q H2p) as H2p'.
  pose proof (NatLe_drop 2 x Hx) as Hx'.
  apply (sdc_iter_lt_decay p q x).
  - apply (NatLe_lift 1 q). lia.
  - apply (NatLe_lift (x * p + q) (x * q)).
    assert (Hsplit : (x * q = x * p + x * (q - p))%nat).
    { rewrite <- (Nat.mul_add_distr_l x p (q - p)). f_equal. lia. }
    assert (H2le : (2 * (q - p) <= x * (q - p))%nat)
      by (apply Nat.mul_le_mono_r; exact Hx').
    rewrite Hsplit. lia.
Qed.

(* Q-bound-domain decay: for [p < q] and [x >= q] the step strictly
   decreases ([x*(q-p) >= q]). *)
Lemma sdc_iter_lt_q : forall p q x,
  NatLe 1 p -> NatLe (Datatypes.S p) q -> NatLe q x ->
  NatLe (Datatypes.S (sdc_iter p q x)) x.
Proof.
  intros p q x Hp Hpq Hx.
  pose proof (NatLe_drop 1 p Hp) as Hp'.
  pose proof (NatLe_drop (Datatypes.S p) q Hpq) as Hpq'.
  pose proof (NatLe_drop q x Hx) as Hx'.
  apply (sdc_iter_lt_decay p q x).
  - apply (NatLe_lift 1 q). lia.
  - apply (NatLe_lift (x * p + q) (x * q)).
    assert (Hsplit : (x * q = x * p + x * (q - p))%nat).
    { rewrite <- (Nat.mul_add_distr_l x p (q - p)). f_equal. lia. }
    assert (H1 : (1 <= q - p)%nat) by lia.
    assert (H2le : (q * 1 <= x * (q - p))%nat)
      by (apply Nat.mul_le_mono; lia).
    rewrite Nat.mul_1_r in H2le.
    rewrite Hsplit. lia.
Qed.

(* Fuel sufficiency (general, strict form): whenever the step strictly
   decreases at and above the budget, [fuel := x] always yields a first
   break (strict bound carried by [NatLe (S n) e]).  Structural
   induction; the witness sits on sigT, prod and NatLe carriers. *)
Theorem sdc_fuel_sufficient_gen : forall fuel p q x E,
  NatLe x fuel ->
  (forall y : nat, NatLe E y ->
                   NatLe (Datatypes.S (sdc_iter p q y)) y) ->
  sigT (fun k : nat => prod (NatLe k fuel)
                            (NatLe (Datatypes.S (sdc_pow_iter p q x k)) E)).
Proof.
  intros fuel.
  induction fuel as [| f IH].
  - intros p q x E Hx Hdecay.
    pose proof (NatLe_drop x 0 Hx) as Hx'.
    assert (Hx0 : x = 0%nat) by lia. subst x.
    destruct E as [| E'].
    + exfalso.
      pose proof (Hdecay 0%nat (NatLe_lift 0 0 (Nat.le_refl 0))) as Hd.
      pose proof (NatLe_drop (Datatypes.S (sdc_iter p q 0)) 0 Hd) as Hd'.
      lia.
    + exists 0%nat. split.
      * apply (NatLe_lift 0 (Datatypes.S E')). apply Nat.le_0_l.
      * simpl. apply (NatLe_lift 1 (Datatypes.S E')). lia.
  - intros p q x E Hx Hdecay.
    destruct (Nat.ltb x E) eqn:Hlt.
    + exists 0%nat. split.
      * apply (NatLe_lift 0 (Datatypes.S f)). apply Nat.le_0_l.
      * simpl. apply (NatLe_lift _ _). exact (proj1 (Nat.ltb_lt x E) Hlt).
    + assert (Hge : (E <= x)%nat) by (apply (proj1 (Nat.ltb_ge x E)); exact Hlt).
      pose proof (NatLe_drop x (Datatypes.S f) Hx) as Hx'.
      assert (Hdec : NatLe (Datatypes.S (sdc_iter p q x)) x).
      { apply Hdecay. apply (NatLe_lift E x). exact Hge. }
      pose proof (NatLe_drop (Datatypes.S (sdc_iter p q x)) x Hdec) as Hdec'.
      assert (Hiterf : (sdc_iter p q x <= f)%nat) by lia.
      destruct (IH p q (sdc_iter p q x) E (NatLe_lift _ _ Hiterf) Hdecay)
        as [k0 [Hk0 Hb0]].
      exists (Datatypes.S k0). split.
      * pose proof (NatLe_drop k0 f Hk0) as Hk0'.
        apply (NatLe_lift _ _). lia.
      * simpl. destruct (sdc_pow_iter_comm p q x k0). exact Hb0.
Qed.

(* Halving-domain fuel sufficiency: for [2*p <= q] and [E >= 2],
   [fuel := x] suffices (strict first-break face). *)
Theorem sdc_fuel_sufficient_half : forall fuel p q x E,
  NatLe 1 p -> NatLe (2 * p) q -> NatLe 2 E -> NatLe x fuel ->
  sigT (fun k : nat => prod (NatLe k fuel)
                            (NatLe (Datatypes.S (sdc_pow_iter p q x k)) E)).
Proof.
  intros fuel p q x E Hp H2p HE Hx.
  apply (sdc_fuel_sufficient_gen fuel p q x E).
  - exact Hx.
  - intros y Hy. apply (sdc_iter_lt_half p q y).
    + exact Hp.
    + exact H2p.
    + apply (NatLe_lift 2 y).
      pose proof (NatLe_drop 2 E HE).
      pose proof (NatLe_drop E y Hy). lia.
Qed.

(* Q-bound-domain fuel sufficiency: for [E >= q] and any [p < q],
   [fuel := x] suffices (strict first-break face). *)
Theorem sdc_fuel_sufficient_qbound : forall fuel p q x E,
  NatLe 1 p -> NatLe (Datatypes.S p) q -> NatLe q E -> NatLe x fuel ->
  sigT (fun k : nat => prod (NatLe k fuel)
                            (NatLe (Datatypes.S (sdc_pow_iter p q x k)) E)).
Proof.
  intros fuel p q x E Hp Hpq HqE Hx.
  apply (sdc_fuel_sufficient_gen fuel p q x E).
  - exact Hx.
  - intros y Hy. apply (sdc_iter_lt_q p q y).
    + exact Hp.
    + exact Hpq.
    + apply (NatLe_lift q y).
      pose proof (NatLe_drop q E HqE).
      pose proof (NatLe_drop E y Hy). lia.
Qed.

(* Automatic fuel at call sites: on the halving domain the enumerator
   readout is the first-break step. *)
Theorem sdc_k_enum_auto_half : forall p q A E,
  NatLe 1 p -> NatLe (2 * p) q -> NatLe 2 E -> NatLe (Datatypes.S E) A ->
  NatLe (Datatypes.S (sdc_pow_iter p q A (sdc_k_enum A p q A E))) E.
Proof.
  intros p q A E Hp H2p HE HAE.
  apply (sdc_k_enum_correct A p q A E).
  apply (sdc_fuel_sufficient_half A p q A E).
  - exact Hp.
  - exact H2p.
  - exact HE.
  - apply (NatLe_lift A A). pose proof (NatLe_drop (Datatypes.S E) A HAE). lia.
Qed.

(* Smoke evaluation one: halving first-break enumeration at
   [kappa = 1/2], [A = 1000], [E = 5]; the decay chain reaches 4 at
   step 8, strictly below 5. *)
Eval vm_compute in (sdc_k_enum 50 1 2 1000 5).

(* Smoke evaluation two: strict first-break at [kappa = 3/4], [A = 50],
   [E = 4]; the chain reaches 4 at step 10 (no strict break) and 3 at
   step 11 (first break) - the strict reading differs by one from the
   non-strict reading on the same data. *)
Eval vm_compute in (sdc_k_enum 50 3 4 50 4).

(* Id-face mirror section over the host certificate subset: the rate
   [omd := 1 - delta] with its two certificates (each host export used
   with exactly the arguments it declares), the power-monotonicity leg
   restated on [NatLe], the one-step Doeblin contraction projection,
   the honest archimedes-slot calculator, the uniform TV contraction
   on the NatLe face with its sigT modulus witness, and the
   end-to-end projections. *)

Section SdcGibbsCalc.

Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpace RI}.
Context {SO : SumOver RI SS}.

Let R := @R RI.
Let S := @S RI SS.
Let zero := @zero RI.
Let one  := @one RI.
Let plus := @plus RI.
Let mult := @mult RI.
Let minus := @minus RI.
Let opp  := @opp RI.
Let abs  := @abs RI.
Let lt   := @lt RI.
Let le   := @le RI.
Let sum_over_S := @sum_over_S RI SS SO.

(* ---- Boltzmann-side certificate subset ---- *)
Variable sum_pos_preserved :
  forall (f : S -> R), (forall s : S, lt zero (f s)) -> lt zero (sum_over_S f).
Variable D : R.
Variable D_pos : lt zero D.
Variable energy : S -> R.

Let bdist := @S06_DiffSamplingGibbs.boltzmann_dist_attn RI SS SO
               sum_pos_preserved D D_pos energy.
Let tv := @S06_DiffSamplingGibbs.tv_dist RI SS SO.

(* ---- Markov-side certificate subset ---- *)
Variable transition : S -> S -> R.
Variable transition_normalization :
  forall s : S, Id (sum_over_S (fun s' : S => transition s s')) one.

Let astepf := @S06_DiffSamplingGibbs.attention_step RI SS SO transition.

Variable detailed_balance :
  forall s s' : S,
    Id (mult (bdist s) (transition s s')) (mult (bdist s') (transition s' s)).

Variable delta : R.
Variable delta_pos : lt zero delta.
Variable delta_lt_one : lt delta one.

Let omd := minus one delta.

Variable minorization :
  forall s s' : S, le (mult delta (bdist s')) (transition s s').
Variable lt_plus_compat_lt_le :
  forall a b c d : R, lt a b -> le c d -> lt (plus a c) (plus b d).
Variable lt_plus_compat_le_lt :
  forall a b c d : R, le a b -> lt c d -> lt (plus a c) (plus b d).
Variable sum_swap_cc : forall f : S -> S -> R,
  Id (sum_over_S (fun s : S => sum_over_S (fun s' : S => f s s')))
     (sum_over_S (fun s' : S => sum_over_S (fun s : S => f s s'))).
Variable abs_ge_zero_id_cc : forall a : R, le zero a -> Id (abs a) a.

(* Honest-interface slot for the geometric break (mirrors the host
   archimedes premise slot). *)
Variable r_arch_pow_i :
  forall (a : R), lt zero a -> forall eps : R, lt zero eps ->
    sigT (fun N : nat => lt (mult a (r_pow omd N)) eps).

(* The two rate certificates: the host exports are used directly, each
   with exactly the arguments it declares. *)

Lemma sdc_rate_pos : lt zero omd.
Proof.
  exact (@S06_DiffSamplingGibbs.one_minus_delta_pos RI delta delta_lt_one
           lt_plus_compat_lt_le).
Qed.

Lemma sdc_rate_lt_one : lt omd one.
Proof.
  exact (@S06_DiffSamplingGibbs.one_minus_delta_lt_one RI delta delta_pos
           lt_plus_compat_le_lt).
Qed.

(* Power monotonicity restated on the Set carrier: the host lemma's
   nat-order premise is restated as [NatLe] in the statement face and
   only enters the proof through [NatLe_drop]. *)

Lemma sdc_r_pow_dec_iter_set : forall m n : nat,
  NatLe m n -> le (r_pow omd n) (r_pow omd m).
Proof.
  intros m n Hmn.
  exact (@S06_DiffSamplingGibbs.r_pow_dec_iter_attn RI delta delta_pos
           delta_lt_one lt_plus_compat_lt_le lt_plus_compat_le_lt
           m n (NatLe_drop m n Hmn)).
Qed.

(* One-step Doeblin contraction projection (the host contraction
   theorem used directly, with exactly the arguments it declares). *)

Theorem sdc_tv_single_proj : forall mu : S -> R,
  Id (sum_over_S mu) one ->
  (forall s : S, le zero (mu s)) ->
  le (tv (astepf mu) bdist) (mult omd (tv mu bdist)).
Proof.
  intros mu Hmu_norm Hmu_nonneg.
  exact (@S06_DiffSamplingGibbs.attention_tv_contraction RI SS SO
           sum_pos_preserved D D_pos energy transition
           transition_normalization detailed_balance delta delta_lt_one
           minorization lt_plus_compat_lt_le sum_swap_cc abs_ge_zero_id_cc
           mu Hmu_norm Hmu_nonneg).
Qed.

(* Geometric-iteration leg used directly: the rate [r_pow omd n] is
   explicit in the statement face. *)

Theorem sdc_tv_iter_proj : forall (mu : S -> R) (n : nat),
  Id (sum_over_S mu) one ->
  (forall s : S, le zero (mu s)) ->
  le (tv (iterate astepf n mu) bdist) (mult (r_pow omd n) (tv mu bdist)).
Proof.
  intros mu n Hmu_norm Hmu_nonneg.
  exact (@S06_DiffSamplingGibbs.attention_tv_iter_contraction RI SS SO
           sum_pos_preserved D D_pos energy transition
           transition_normalization detailed_balance delta delta_pos
           delta_lt_one minorization lt_plus_compat_lt_le sum_swap_cc
           abs_ge_zero_id_cc mu n Hmu_norm Hmu_nonneg).
Qed.

(* TV non-negativity projection (the host lemma used directly). *)

Theorem sdc_tv_nonneg : forall mu nu : S -> R, le zero (tv mu nu).
Proof.
  intros mu nu. exact (@S06_DiffSamplingGibbs.tv_dist_nonneg RI SS SO mu nu).
Qed.

(* Honest archimedes-slot calculator (reads the step witness). *)

Definition sdc_arch_k (a : R) (Ha : lt zero a)
  (eps : R) (Heps : lt zero eps) : nat :=
  projT1 (r_arch_pow_i a Ha eps Heps).

Theorem sdc_arch_k_budget : forall (a : R) (Ha : lt zero a)
  (eps : R) (Heps : lt zero eps),
  lt (mult a (r_pow omd (sdc_arch_k a Ha eps Heps))) eps.
Proof.
  intros a Ha eps Heps. exact (projT2 (r_arch_pow_i a Ha eps Heps)).
Qed.

(* Main assembly: the accuracy-to-step calculator and the uniform
   contraction correctness.  [sdc_step_calc] reads the archimedes-slot
   witness of the strictly positive initial TV distance;
   [sdc_step_calc_correct] shows the iterated TV distance drops
   strictly below the budget for every [n] beyond the read step
   (geometric-iteration leg, power-monotonicity leg and archimedes
   budget leg joined by the order transitivity). *)

Definition sdc_step_calc (mu0 : S -> R) (Hmu : Id (sum_over_S mu0) one)
  (Hmu0 : forall s : S, le zero (mu0 s))
  (eps : R) (Heps : lt zero eps) (Htv0 : lt zero (tv mu0 bdist))
  : nat :=
  projT1 (r_arch_pow_i (tv mu0 bdist) Htv0 eps Heps).

Theorem sdc_step_calc_correct : forall (mu0 : S -> R)
  (Hmu : Id (sum_over_S mu0) one) (Hmu0 : forall s : S, le zero (mu0 s))
  (eps : R) (Heps : lt zero eps) (Htv0 : lt zero (tv mu0 bdist)) (n : nat),
  NatLe (sdc_step_calc mu0 Hmu Hmu0 eps Heps Htv0) n ->
  lt (tv (iterate astepf n mu0) bdist) eps.
Proof.
  intros mu0 Hmu Hmu0 eps Heps Htv0. unfold sdc_step_calc.
  destruct (r_arch_pow_i (tv mu0 bdist) Htv0 eps Heps) as [N HN].
  intros n Hn.
  apply (le_lt_trans _ (mult (r_pow omd n) (tv mu0 bdist)) _).
  - exact (sdc_tv_iter_proj mu0 n Hmu Hmu0).
  - apply (le_lt_trans _ (mult (r_pow omd N) (tv mu0 bdist)) _).
    + apply (le_mult_compat_weak (r_pow omd n) (r_pow omd N)
               (tv mu0 bdist)).
      * exact (sdc_tv_nonneg mu0 bdist).
      * exact (sdc_r_pow_dec_iter_set N n Hn).
    + exact (lt_id_l _ _ _
               (mult_comm (r_pow omd N) (tv mu0 bdist)) HN).
Qed.

(* sigT packaging of the uniform contraction modulus witness (the host
   conclusion face restated on the NatLe carrier). *)
Theorem sdc_mixing_modulus_sigT : forall (mu0 : S -> R)
  (Hmu : Id (sum_over_S mu0) one) (Hmu0 : forall s : S, le zero (mu0 s))
  (eps : R) (Heps : lt zero eps) (Htv0 : lt zero (tv mu0 bdist)),
  sigT (fun N : nat =>
    forall n : nat, NatLe N n ->
      lt (tv (iterate astepf n mu0) bdist) eps).
Proof.
  intros mu0 Hmu Hmu0 eps Heps Htv0.
  exists (sdc_step_calc mu0 Hmu Hmu0 eps Heps Htv0).
  intros n Hn. exact (sdc_step_calc_correct mu0 Hmu Hmu0 eps Heps Htv0 n Hn).
Defined.

(* End-to-end projections of the host main theorem: the step readout
   via [projT1], the uniform contraction correctness through the
   NatLe bridge, and the sigT packaging. *)

Definition sdc_conv_step_calc (mu0 : S -> R) (Hmu : Id (sum_over_S mu0) one)
  (Hmu0 : forall s : S, le zero (mu0 s))
  (eps : R) (Heps : lt zero eps) (Htv0 : lt zero (tv mu0 bdist))
  : nat :=
  projT1 (@S06_DiffSamplingGibbs.attention_iterate_converges RI SS SO
            sum_pos_preserved D D_pos energy transition
            transition_normalization detailed_balance delta delta_pos
            delta_lt_one minorization lt_plus_compat_lt_le
            lt_plus_compat_le_lt sum_swap_cc abs_ge_zero_id_cc r_arch_pow_i
            mu0 Hmu Hmu0 eps Heps Htv0).

Theorem sdc_conv_step_correct : forall (mu0 : S -> R)
  (Hmu : Id (sum_over_S mu0) one) (Hmu0 : forall s : S, le zero (mu0 s))
  (eps : R) (Heps : lt zero eps) (Htv0 : lt zero (tv mu0 bdist)) (n : nat),
  NatLe (sdc_conv_step_calc mu0 Hmu Hmu0 eps Heps Htv0) n ->
  lt (tv (iterate astepf n mu0) bdist) eps.
Proof.
  intros mu0 Hmu Hmu0 eps Heps Htv0. unfold sdc_conv_step_calc.
  destruct (@S06_DiffSamplingGibbs.attention_iterate_converges RI SS SO
              sum_pos_preserved D D_pos energy transition
              transition_normalization detailed_balance delta delta_pos
              delta_lt_one minorization lt_plus_compat_lt_le
              lt_plus_compat_le_lt sum_swap_cc abs_ge_zero_id_cc r_arch_pow_i
              mu0 Hmu Hmu0 eps Heps Htv0) as [N HN].
  intros n Hn.
  exact (HN n Hn).
Qed.

(* sigT packaging of the end-to-end uniform contraction modulus
   witness. *)
Theorem sdc_conv_modulus_sigT : forall (mu0 : S -> R)
  (Hmu : Id (sum_over_S mu0) one) (Hmu0 : forall s : S, le zero (mu0 s))
  (eps : R) (Heps : lt zero eps) (Htv0 : lt zero (tv mu0 bdist)),
  sigT (fun N : nat =>
    forall n : nat, NatLe N n ->
      lt (tv (iterate astepf n mu0) bdist) eps).
Proof.
  intros mu0 Hmu Hmu0 eps Heps Htv0.
  exists (sdc_conv_step_calc mu0 Hmu Hmu0 eps Heps Htv0).
  intros n Hn. exact (sdc_conv_step_correct mu0 Hmu Hmu0 eps Heps Htv0 n Hn).
Defined.

End SdcGibbsCalc.

(* Audit port: the assumption audit (all entries expected [Closed]) and
   the extraction witness, following the series template. *)

Print Assumptions sdc_k_enum_correct.
Print Assumptions sdc_k_enum_minimal.
Print Assumptions sdc_k_enum_first_break.
Print Assumptions sdc_k_enum_logface.
Print Assumptions sdc_fuel_sufficient_half.
Print Assumptions sdc_fuel_sufficient_qbound.
Print Assumptions sdc_k_enum_auto_half.
Print Assumptions sdc_rate_pos.
Print Assumptions sdc_rate_lt_one.
Print Assumptions sdc_r_pow_dec_iter_set.
Print Assumptions sdc_tv_nonneg.
Print Assumptions sdc_tv_single_proj.
Print Assumptions sdc_tv_iter_proj.
Print Assumptions sdc_arch_k_budget.
Print Assumptions sdc_step_calc_correct.
Print Assumptions sdc_mixing_modulus_sigT.
Print Assumptions sdc_conv_step_correct.
Print Assumptions sdc_conv_modulus_sigT.

(* Extraction port: the four nat-level calculators (genuine fixpoints,
   no stubs, no truncation). *)
Separate Extraction sdc_ceil_div sdc_iter sdc_pow_iter sdc_k_enum.
