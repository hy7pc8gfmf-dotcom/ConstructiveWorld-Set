(* Convergence step calculator for the CW220 contraction face (cw2_
   prefix). *)

(** * abl_cw220_step_calc: from accuracy to step count on the CW220
      contraction face.

    Mission.  (1) A nat-level fixed-point part: the decay enumerator
      [cw2_k_enum] with its first-break stop and its correctness,
      minimality and fuel-sufficiency companions.  (2) A Real-carrier
      part over the host contraction face: the rate
      [cw2_kappa delta := 1 - delta], the contraction projections on
      the NatLe face, the closed archimedes-slot readout, the host
      decay chain, the geometric-decay assembly with its sigT
      witnesses, and the tail-budget projections.

    Dependencies.  Stdlib [List], [PeanoNat], [Arith], [Lia],
      [Extraction]; requires [S01], [S02], [S07], [S14] of this
      development and [CW220_Extensions].

    References.  ConstructiveWorld-Main, module
      [abl_cw220_step_calc].

    Constructivity.  Set-level carriers throughout: step witnesses on
      nat in sigT form, no Prop pushed into Set goals (host nat-order
      premises enter the proofs only through [NatLe_drop]).  Genuine
      fixpoints; extraction with [Obj.magic] = 0; the trailing
      [Print Assumptions] audit reports [Closed].

    Build.  [coqc -native-compiler no -Q . "" abl_cw220_step_calc.v];
      artifact magic [436f7121 00015ff4]. *)

From Stdlib Require Import PeanoNat.
From Stdlib Require Import Extraction.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S07_RealSetoidExpLog.
Require Import S14_B5BatchBlock.
Require Import CW220_Extensions.
Import CW220_Extensions.BudgetReal.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lia.

(* Part 2: the fixed-point enumerator for the contraction rate (genuine
   fixpoints, strict face, Set carriers), host-independent.  The rate
   [kappa = p/q] (with [p < q]), the initial value [A] and the budget
   [E] are given in fixed-point form; the enumerator returns the first
   [N] with the iterated value strictly below [E].  Order bounds travel
   on the NatLe carrier, strict bounds as [NatLe (S n)]. *)

(* Ceiling division [(a+q-1)/q] for [q >= 1]; ceiling keeps the
   upper-bound direction. *)
Definition cw2_ceil_div (a q : nat) : nat := Nat.div (a + q - 1) q.

Lemma cw2_ceil_div_le : forall a q,
  NatLe 1 q -> NatLe a (cw2_ceil_div a q * q).
Proof.
  intros a q Hq. pose proof (NatLe_drop 1 q Hq) as Hq'.
  unfold cw2_ceil_div.
  assert (Hq1 : (0 < q)%nat) by lia.
  pose proof (Nat.div_mod_eq (a + q - 1) q) as Hdm.
  pose proof (Nat.mod_upper_bound (a + q - 1) q (proj2 (Nat.neq_0_lt_0 q) Hq1)) as Hmb.
  apply (NatLe_lift _ _). lia.
Qed.

(* Decay step: one fixed-point multiplication of [x] by [kappa = p/q]
   (with ceiling). *)
Definition cw2_iter (p q x : nat) : nat := cw2_ceil_div (x * p) q.

Lemma cw2_iter_step_bound : forall p q x,
  NatLe 1 q -> NatLe (x * p) (cw2_iter p q x * q).
Proof.
  intros p q x Hq. unfold cw2_iter. apply (cw2_ceil_div_le (x * p) q Hq).
Qed.

(* Iterated power: the [k]-fold composition of [cw2_iter] (the ceiling
   face of the geometric decay sequence). *)
Fixpoint cw2_pow_iter (p q x k : nat) : nat :=
  match k with
  | O => x
  | Datatypes.S k' => cw2_iter p q (cw2_pow_iter p q x k')
  end.

(* Composition swap: one step then [k] iterations equals [k] iterations
   then one step ([S k] compositions either way). *)
Lemma cw2_pow_iter_comm : forall p q x k,
  Id (cw2_pow_iter p q (cw2_iter p q x) k)
     (cw2_iter p q (cw2_pow_iter p q x k)).
Proof.
  intros p q x k. induction k as [| k IH].
  - simpl. apply id_refl.
  - simpl. exact (id_cong (cw2_iter p q) IH).
Qed.

(* Enumerator: a fuel-bounded fixpoint stopping at the first step where
   [x < e] (returning the steps taken), otherwise taking a decay step
   and searching on ([Nat.ltb] test, strict termination face). *)
Fixpoint cw2_k_enum (fuel p q x e : nat) : nat :=
  match fuel with
  | O => O
  | Datatypes.S f =>
      if Nat.ltb x e then O else Datatypes.S (cw2_k_enum f p q (cw2_iter p q x) e)
  end.

(* Exact-face invariant: the ceiling value always dominates the exact
   geometric value ([x * p^k <= iter^k(x) * q^k]). *)
Lemma cw2_pow_iter_exact_ge : forall p q x k,
  NatLe 1 p -> NatLe 1 q -> NatLe (x * p ^ k) (cw2_pow_iter p q x k * q ^ k).
Proof.
  intros p q x k Hp Hq. induction k as [| k IH].
  - apply (NatLe_lift _ _). simpl. lia.
  - pose proof (NatLe_drop _ _ IH) as IH'.
    apply (NatLe_lift _ _). simpl.
    apply (Nat.le_trans _ (cw2_pow_iter p q x k * q ^ k * p)).
    + rewrite (Nat.mul_comm p (p ^ k)).
      rewrite (Nat.mul_assoc x (p ^ k) p).
      apply (Nat.mul_le_mono_r _ _ p). exact IH'.
    + pose proof (cw2_iter_step_bound p q (cw2_pow_iter p q x k) Hq) as Hstep.
      pose proof (NatLe_drop _ _ Hstep) as Hstep'.
      rewrite <- (Nat.mul_assoc (cw2_pow_iter p q x k) (q ^ k) p).
      rewrite (Nat.mul_comm (q ^ k) p).
      rewrite (Nat.mul_assoc (cw2_pow_iter p q x k) p (q ^ k)).
      apply (Nat.le_trans _ (cw2_iter p q (cw2_pow_iter p q x k) * q * q ^ k)).
      * apply (Nat.mul_le_mono_r _ _ (q ^ k)). exact Hstep'.
      * rewrite (Nat.mul_assoc (cw2_iter p q (cw2_pow_iter p q x k)) q (q ^ k)).
        apply (Nat.le_refl _).
Qed.

(* Correctness (strict first-break face): whenever the break is
   reachable within the fuel, the returned step has its ceiling value
   strictly below [e] (strict order bound carried by [NatLe (S n) e]).
   The reachability witness sits on sigT, prod and NatLe carriers. *)
Theorem cw2_k_enum_correct : forall fuel p q x e,
  (sigT (fun k : nat =>
    prod (NatLe k fuel) (NatLe (Datatypes.S (cw2_pow_iter p q x k)) e))) ->
  NatLe (Datatypes.S (cw2_pow_iter p q x (cw2_k_enum fuel p q x e))) e.
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
      * pose proof (NatLe_drop (Datatypes.S (cw2_pow_iter p q x 0)) e Hbound)
          as Hb'.
        simpl in Hb'. lia.
      * simpl in Hbound.
        revert Hbound. destruct (cw2_pow_iter_comm p q x k'). intros Hbound.
        assert (Hk2 : (k' <= f)%nat) by lia.
        assert (Hterm' : sigT (fun k0 : nat =>
                          prod (NatLe k0 f)
                               (NatLe (Datatypes.S
                                  (cw2_pow_iter p q (cw2_iter p q x) k0)) e))).
        { exact (existT _ k' (pair (NatLe_lift k' f Hk2) Hbound)). }
        specialize (IH p q (cw2_iter p q x) e Hterm').
        simpl.
        destruct (cw2_pow_iter_comm p q x
                    (cw2_k_enum f p q (cw2_iter p q x) e)).
        exact IH.
Qed.

(* First-break minimality witness: whenever the break is reachable,
   every step [j] before the returned [N] (with [S j <= N]) still has
   its ceiling value at least [e] - the readout is the first step
   below the budget. *)
Theorem cw2_k_enum_minimal : forall fuel p q x e,
  (sigT (fun k : nat =>
    prod (NatLe k fuel) (NatLe (Datatypes.S (cw2_pow_iter p q x k)) e))) ->
  forall j : nat, NatLe (Datatypes.S j) (cw2_k_enum fuel p q x e) ->
  NatLe e (cw2_pow_iter p q x j).
Proof.
  intros fuel. induction fuel as [| f IH]; intros p q x e Hterm j Hj.
  - exfalso. pose proof (NatLe_drop (Datatypes.S j) 0 Hj) as Hj'. lia.
  - simpl. destruct (Nat.ltb x e) eqn:Hlt.
    + simpl in Hj. rewrite Hlt in Hj.
      exfalso. pose proof (NatLe_drop (Datatypes.S j) 0 Hj) as Hj'. lia.
    + simpl in Hj. rewrite Hlt in Hj.
      assert (Hge : (e <= x)%nat) by (apply (proj1 (Nat.ltb_ge x e)); exact Hlt).
      pose proof (NatLe_drop (Datatypes.S j)
                    (Datatypes.S (cw2_k_enum f p q (cw2_iter p q x) e)) Hj)
        as Hj'.
      destruct j as [| j'].
      * simpl. apply (NatLe_lift e x). exact Hge.
      * simpl in Hj'.
        assert (Hj2 : NatLe (Datatypes.S j')
                        (cw2_k_enum f p q (cw2_iter p q x) e))
          by (apply (NatLe_lift _ _); lia).
        assert (Hterm' : sigT (fun k0 : nat =>
                          prod (NatLe k0 f)
                               (NatLe (Datatypes.S
                                  (cw2_pow_iter p q (cw2_iter p q x) k0)) e))).
        { destruct Hterm as [k [Hk Hbound]].
          pose proof (NatLe_drop k (Datatypes.S f) Hk) as Hk'.
          destruct k as [| k'].
          - pose proof (NatLe_drop (Datatypes.S (cw2_pow_iter p q x 0)) e Hbound)
              as Hb'.
            simpl in Hb'. lia.
          - simpl in Hbound.
            revert Hbound. destruct (cw2_pow_iter_comm p q x k'). intros Hbound.
            assert (Hk2 : (k' <= f)%nat) by lia.
            exact (existT _ k' (pair (NatLe_lift k' f Hk2) Hbound)). }
        specialize (IH p q (cw2_iter p q x) e Hterm' j' Hj2).
        simpl. destruct (cw2_pow_iter_comm p q x j'). exact IH.
Qed.

(* First-break witness packaging: whenever reachable, the readout [N]
   carries both certificates - step [N] strictly below the budget and
   every earlier step still at or above it (sigT, prod and forall-nat
   carriers). *)
Theorem cw2_k_enum_first_break : forall fuel p q x e,
  (sigT (fun k : nat =>
    prod (NatLe k fuel) (NatLe (Datatypes.S (cw2_pow_iter p q x k)) e))) ->
  sigT (fun N : nat =>
    prod (NatLe (Datatypes.S (cw2_pow_iter p q x N)) e)
         (forall j : nat, NatLe (Datatypes.S j) N ->
                          NatLe e (cw2_pow_iter p q x j))).
Proof.
  intros fuel p q x e H.
  exists (cw2_k_enum fuel p q x e). split.
  - exact (cw2_k_enum_correct fuel p q x e H).
  - exact (cw2_k_enum_minimal fuel p q x e H).
Qed.

(* Nat form of the log-modulus equation: termination gives
   [x * p^N <= e * q^N] (equivalent under log monotonicity); a strict
   first break [y < e] drops to [y <= e] via [NatLe (S y) e]. *)
Theorem cw2_k_enum_logface : forall fuel p q x e,
  NatLe 1 p -> NatLe 1 q ->
  (sigT (fun k : nat =>
    prod (NatLe k fuel) (NatLe (Datatypes.S (cw2_pow_iter p q x k)) e))) ->
  NatLe (x * p ^ cw2_k_enum fuel p q x e)
        (e * q ^ cw2_k_enum fuel p q x e).
Proof.
  intros fuel p q x e Hp Hq Hterm.
  pose proof (cw2_k_enum_correct fuel p q x e Hterm) as H1.
  pose proof (cw2_pow_iter_exact_ge p q x (cw2_k_enum fuel p q x e) Hp Hq) as H2.
  pose proof (NatLe_drop _ _ H1) as H1'.
  pose proof (NatLe_drop _ _ H2) as H2'.
  apply (NatLe_lift _ _).
  apply (Nat.le_trans _
           (cw2_pow_iter p q x (cw2_k_enum fuel p q x e)
              * q ^ cw2_k_enum fuel p q x e)).
  - exact H2'.
  - apply (Nat.mul_le_mono_r _ _ (q ^ cw2_k_enum fuel p q x e)).
    lia.
Qed.

(* Strict decay companions and fuel-sufficiency witnesses (closing the
   decay premise at call sites). *)

(* Decay kernel: when [x*p + q <= x*q], the ceiling step strictly
   decreases (floor criterion [d*q <= a < x*q]). *)
Lemma cw2_iter_lt_decay : forall p q x,
  NatLe 1 q -> NatLe (x * p + q) (x * q) ->
  NatLe (Datatypes.S (cw2_iter p q x)) x.
Proof.
  intros p q x Hq Hdecay.
  pose proof (NatLe_drop 1 q Hq) as Hq'.
  pose proof (NatLe_drop (x * p + q) (x * q) Hdecay) as Hdecay'.
  unfold cw2_iter, cw2_ceil_div.
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
Lemma cw2_iter_lt_half : forall p q x,
  NatLe 1 p -> NatLe (2 * p) q -> NatLe 2 x ->
  NatLe (Datatypes.S (cw2_iter p q x)) x.
Proof.
  intros p q x Hp H2p Hx.
  pose proof (NatLe_drop 1 p Hp) as Hp'.
  pose proof (NatLe_drop (2 * p) q H2p) as H2p'.
  pose proof (NatLe_drop 2 x Hx) as Hx'.
  apply (cw2_iter_lt_decay p q x).
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
Lemma cw2_iter_lt_q : forall p q x,
  NatLe 1 p -> NatLe (Datatypes.S p) q -> NatLe q x ->
  NatLe (Datatypes.S (cw2_iter p q x)) x.
Proof.
  intros p q x Hp Hpq Hx.
  pose proof (NatLe_drop 1 p Hp) as Hp'.
  pose proof (NatLe_drop (Datatypes.S p) q Hpq) as Hpq'.
  pose proof (NatLe_drop q x Hx) as Hx'.
  apply (cw2_iter_lt_decay p q x).
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
Theorem cw2_fuel_sufficient_gen : forall fuel p q x E,
  NatLe x fuel ->
  (forall y : nat, NatLe E y ->
                   NatLe (Datatypes.S (cw2_iter p q y)) y) ->
  sigT (fun k : nat => prod (NatLe k fuel)
                            (NatLe (Datatypes.S (cw2_pow_iter p q x k)) E)).
Proof.
  intros fuel.
  induction fuel as [| f IH].
  - intros p q x E Hx Hdecay.
    pose proof (NatLe_drop x 0 Hx) as Hx'.
    assert (Hx0 : x = 0%nat) by lia. subst x.
    destruct E as [| E'].
    + exfalso.
      pose proof (Hdecay 0%nat (NatLe_lift 0 0 (Nat.le_refl 0))) as Hd.
      pose proof (NatLe_drop (Datatypes.S (cw2_iter p q 0)) 0 Hd) as Hd'.
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
      assert (Hdec : NatLe (Datatypes.S (cw2_iter p q x)) x).
      { apply Hdecay. apply (NatLe_lift E x). exact Hge. }
      pose proof (NatLe_drop (Datatypes.S (cw2_iter p q x)) x Hdec) as Hdec'.
      assert (Hiterf : (cw2_iter p q x <= f)%nat) by lia.
      destruct (IH p q (cw2_iter p q x) E (NatLe_lift _ _ Hiterf) Hdecay)
        as [k0 [Hk0 Hb0]].
      exists (Datatypes.S k0). split.
      * pose proof (NatLe_drop k0 f Hk0) as Hk0'.
        apply (NatLe_lift _ _). lia.
      * simpl. destruct (cw2_pow_iter_comm p q x k0). exact Hb0.
Qed.

(* Halving-domain fuel sufficiency: for [2*p <= q] and [E >= 2],
   [fuel := x] suffices (strict first-break face). *)
Theorem cw2_fuel_sufficient_half : forall fuel p q x E,
  NatLe 1 p -> NatLe (2 * p) q -> NatLe 2 E -> NatLe x fuel ->
  sigT (fun k : nat => prod (NatLe k fuel)
                            (NatLe (Datatypes.S (cw2_pow_iter p q x k)) E)).
Proof.
  intros fuel p q x E Hp H2p HE Hx.
  apply (cw2_fuel_sufficient_gen fuel p q x E).
  - exact Hx.
  - intros y Hy. apply (cw2_iter_lt_half p q y).
    + exact Hp.
    + exact H2p.
    + apply (NatLe_lift 2 y).
      pose proof (NatLe_drop 2 E HE).
      pose proof (NatLe_drop E y Hy). lia.
Qed.

(* Q-bound-domain fuel sufficiency: for [E >= q] and any [p < q],
   [fuel := x] suffices (strict first-break face). *)
Theorem cw2_fuel_sufficient_qbound : forall fuel p q x E,
  NatLe 1 p -> NatLe (Datatypes.S p) q -> NatLe q E -> NatLe x fuel ->
  sigT (fun k : nat => prod (NatLe k fuel)
                            (NatLe (Datatypes.S (cw2_pow_iter p q x k)) E)).
Proof.
  intros fuel p q x E Hp Hpq HqE Hx.
  apply (cw2_fuel_sufficient_gen fuel p q x E).
  - exact Hx.
  - intros y Hy. apply (cw2_iter_lt_q p q y).
    + exact Hp.
    + exact Hpq.
    + apply (NatLe_lift q y).
      pose proof (NatLe_drop q E HqE).
      pose proof (NatLe_drop E y Hy). lia.
Qed.

(* Automatic fuel at call sites: on the halving domain the enumerator
   readout is the first-break step. *)
Theorem cw2_k_enum_auto_half : forall p q A E,
  NatLe 1 p -> NatLe (2 * p) q -> NatLe 2 E -> NatLe (Datatypes.S E) A ->
  NatLe (Datatypes.S (cw2_pow_iter p q A (cw2_k_enum A p q A E))) E.
Proof.
  intros p q A E Hp H2p HE HAE.
  apply (cw2_k_enum_correct A p q A E).
  apply (cw2_fuel_sufficient_half A p q A E).
  - exact Hp.
  - exact H2p.
  - exact HE.
  - apply (NatLe_lift A A). pose proof (NatLe_drop (Datatypes.S E) A HAE). lia.
Qed.

(* Smoke evaluation one: halving first-break enumeration at
   [kappa = 1/2], [A = 1000], [E = 5]; the decay chain reaches 4 at
   step 8, strictly below 5. *)
Eval vm_compute in (cw2_k_enum 50 1 2 1000 5).

(* Smoke evaluation two: strict first-break at [kappa = 3/4], [A = 50],
   [E = 4]; the chain reaches 4 at step 10 (no strict break) and 3 at
   step 11 (first break) - the strict reading differs by one from the
   non-strict reading on the same data. *)
Eval vm_compute in (cw2_k_enum 50 3 4 50 4).

(* Real-carrier parallel part over the host contraction face (used
   directly).  The rate [cw2_kappa delta := 1 - delta] is explicit in
   the statement face; the two rate certificates use the host exports
   directly; the power-monotonicity leg is restated on the NatLe
   carrier; the archimedes-slot step readout is closed (the host
   archimedes theorem is fully proved, with no honest-interface slot);
   the host decay chain is used directly; the main assembly pairs the
   uniform geometric decay on the NatLe face with its sigT modulus
   witnesses; and the tail-budget projections close the part. *)

(* The carrier definition of the rate ([1 - delta], matching the host
   statement face). *)
Definition cw2_kappa (delta : Real) : Real :=
  real_plus real_one (real_opp delta).

(* The two rate certificates (the host root-level certificates used
   directly). *)

Lemma cw2_rate_pos : forall delta : Real,
  real_lt delta real_one -> real_lt real_zero (cw2_kappa delta).
Proof.
  intros delta Hd. exact (one_minus_delta_pos_real delta Hd).
Qed.

Lemma cw2_rate_lt_one : forall delta : Real,
  real_lt real_zero delta -> real_lt (cw2_kappa delta) real_one.
Proof.
  intros delta Hd. exact (one_minus_delta_lt_one_real delta Hd).
Qed.

(* Power anti-monotonicity restated on the Set carrier: the host
   lemma's nat-order premise is restated as [NatLe] in the statement
   face and only enters the proof through [NatLe_drop]. *)

Lemma cw2_r_pow_anti_mono_set : forall (delta : Real)
  (Hd1 : real_lt real_zero delta) (Hd2 : real_lt delta real_one)
  (m n : nat),
  NatLe m n ->
  real_le (real_pow (cw2_kappa delta) n) (real_pow (cw2_kappa delta) m).
Proof.
  intros delta Hd1 Hd2 m n Hmn.
  exact (real_pow_anti_mono (cw2_kappa delta)
           (cw2_rate_pos delta Hd2)
           (real_lt_le_bridge (cw2_kappa delta) real_one
              (cw2_rate_lt_one delta Hd1))
           m n (NatLe_drop m n Hmn)).
Qed.

(* Closed archimedes-slot step readout: the host archimedes theorem is
   fully proved (via the Bernoulli bound and the real archimedes
   property), so this face has no honest-interface slot. *)

Definition cw2_arch_k (delta : Real) (Hd1 : real_lt real_zero delta)
  (Hd2 : real_lt delta real_one) (a : Real) (Ha : real_lt real_zero a)
  (eps : Real) (Heps : real_lt real_zero eps) : nat :=
  projT1 (r_arch_pow_attn_real delta Hd1 Hd2 a Ha eps Heps).

Theorem cw2_arch_k_budget : forall (delta : Real)
  (Hd1 : real_lt real_zero delta) (Hd2 : real_lt delta real_one)
  (a : Real) (Ha : real_lt real_zero a) (eps : Real)
  (Heps : real_lt real_zero eps),
  real_lt (real_mult a
             (real_pow (cw2_kappa delta) (cw2_arch_k delta Hd1 Hd2 a Ha eps Heps)))
          eps.
Proof.
  intros delta Hd1 Hd2 a Ha eps Heps.
  exact (projT2 (r_arch_pow_attn_real delta Hd1 Hd2 a Ha eps Heps)).
Qed.

(* The host decay chain used directly (the per-step contraction premise
   is explicit, matching the host signature; the conclusion carries the
   rate as [cw2_kappa delta]). *)

Lemma cw2_tv_decay : forall (delta : Real)
  (Hd1 : real_lt real_zero delta) (Hd2 : real_lt delta real_one)
  (tv_seq : nat -> Real),
  (forall n : nat,
    real_le (tv_seq (Datatypes.S n))
            (real_mult (cw2_kappa delta) (tv_seq n))) ->
  forall n : nat,
    real_le (tv_seq n)
            (real_mult (real_pow (cw2_kappa delta) n) (tv_seq Datatypes.O)).
Proof.
  intros delta Hd1 Hd2 tv_seq Hstep n.
  exact (tv_iter_decay_real delta Hd1 Hd2 tv_seq Hstep n).
Qed.

(* Main assembly: the accuracy-to-step calculator and the uniform
   geometric-decay correctness.  [cw2_step_calc] reads the closed
   archimedes witness at amplitude [tv 0] under the budget [eps];
   [cw2_step_calc_correct] shows the sequence drops strictly below
   [eps] for every [n] beyond the read step (decay-chain leg,
   power-monotonicity leg and archimedes budget leg joined by the
   order transitivity). *)

Definition cw2_step_calc (delta : Real) (Hd1 : real_lt real_zero delta)
  (Hd2 : real_lt delta real_one) (tv_seq : nat -> Real)
  (Hstep : forall n : nat,
             real_le (tv_seq (Datatypes.S n))
                     (real_mult (cw2_kappa delta) (tv_seq n)))
  (eps : Real) (Heps : real_lt real_zero eps)
  (Htv0 : real_lt real_zero (tv_seq Datatypes.O)) : nat :=
  projT1 (r_arch_pow_attn_real delta Hd1 Hd2 (tv_seq Datatypes.O) Htv0
            eps Heps).

Theorem cw2_step_calc_correct : forall (delta : Real)
  (Hd1 : real_lt real_zero delta) (Hd2 : real_lt delta real_one)
  (tv_seq : nat -> Real)
  (Hstep : forall n : nat,
             real_le (tv_seq (Datatypes.S n))
                     (real_mult (cw2_kappa delta) (tv_seq n)))
  (eps : Real) (Heps : real_lt real_zero eps)
  (Htv0 : real_lt real_zero (tv_seq Datatypes.O)) (n : nat),
  NatLe (cw2_step_calc delta Hd1 Hd2 tv_seq Hstep eps Heps Htv0) n ->
  real_lt (tv_seq n) eps.
Proof.
  intros delta Hd1 Hd2 tv_seq Hstep eps Heps Htv0.
  unfold cw2_step_calc.
  destruct (r_arch_pow_attn_real delta Hd1 Hd2 (tv_seq Datatypes.O) Htv0
              eps Heps) as [N HN].
  intros n Hn.
  apply (real_le_lt_trans (tv_seq n)
           (real_mult (real_pow (cw2_kappa delta) n) (tv_seq Datatypes.O))
           eps).
  - exact (cw2_tv_decay delta Hd1 Hd2 tv_seq Hstep n).
  - apply (real_le_lt_trans
             (real_mult (real_pow (cw2_kappa delta) n) (tv_seq Datatypes.O))
             (real_mult (real_pow (cw2_kappa delta) N) (tv_seq Datatypes.O))
             eps).
    + exact (real_le_mult_compat (real_pow (cw2_kappa delta) n)
               (real_pow (cw2_kappa delta) N) (tv_seq Datatypes.O)
               Htv0 (cw2_r_pow_anti_mono_set delta Hd1 Hd2 N n Hn)).
    + exact (real_eq_lt_lt
               (real_mult (real_pow (cw2_kappa delta) N) (tv_seq Datatypes.O))
               (real_mult (tv_seq Datatypes.O) (real_pow (cw2_kappa delta) N))
               eps
               (real_mult_comm (real_pow (cw2_kappa delta) N)
                  (tv_seq Datatypes.O))
               HN).
Qed.

(* sigT packaging of the uniform geometric-decay modulus witness (the
   host conclusion face restated on the NatLe carrier). *)
Theorem cw2_mixing_modulus_sigT : forall (delta : Real)
  (Hd1 : real_lt real_zero delta) (Hd2 : real_lt delta real_one)
  (tv_seq : nat -> Real)
  (Hstep : forall n : nat,
             real_le (tv_seq (Datatypes.S n))
                     (real_mult (cw2_kappa delta) (tv_seq n)))
  (eps : Real) (Heps : real_lt real_zero eps)
  (Htv0 : real_lt real_zero (tv_seq Datatypes.O)),
  sigT (fun N : nat =>
    forall n : nat, NatLe N n -> real_lt (tv_seq n) eps).
Proof.
  intros delta Hd1 Hd2 tv_seq Hstep eps Heps Htv0.
  exists (cw2_step_calc delta Hd1 Hd2 tv_seq Hstep eps Heps Htv0).
  intros n Hn.
  exact (cw2_step_calc_correct delta Hd1 Hd2 tv_seq Hstep eps Heps Htv0 n Hn).
Defined.

(* End-to-end projections of the host main theorem: the step readout
   via [projT1], the uniform contraction correctness via [projT2]
   through the NatLe bridge, and the sigT packaging (the host nat-order
   premise enters the proofs only through [NatLe_drop]). *)

Definition cw2_conv_step_calc (delta : Real) (Hd1 : real_lt real_zero delta)
  (Hd2 : real_lt delta real_one) (tv_seq : nat -> Real)
  (Hstep : forall n : nat,
             real_le (tv_seq (Datatypes.S n))
                     (real_mult (cw2_kappa delta) (tv_seq n)))
  (eps : Real) (Heps : real_lt real_zero eps)
  (Htv0 : real_lt real_zero (tv_seq Datatypes.O)) : nat :=
  projT1 (attention_iterate_converges_real delta Hd1 Hd2 tv_seq Hstep
            eps Heps Htv0).

Theorem cw2_conv_step_correct : forall (delta : Real)
  (Hd1 : real_lt real_zero delta) (Hd2 : real_lt delta real_one)
  (tv_seq : nat -> Real)
  (Hstep : forall n : nat,
             real_le (tv_seq (Datatypes.S n))
                     (real_mult (cw2_kappa delta) (tv_seq n)))
  (eps : Real) (Heps : real_lt real_zero eps)
  (Htv0 : real_lt real_zero (tv_seq Datatypes.O)) (n : nat),
  NatLe (cw2_conv_step_calc delta Hd1 Hd2 tv_seq Hstep eps Heps Htv0) n ->
  real_lt (tv_seq n) eps.
Proof.
  intros delta Hd1 Hd2 tv_seq Hstep eps Heps Htv0.
  unfold cw2_conv_step_calc.
  destruct (attention_iterate_converges_real delta Hd1 Hd2 tv_seq Hstep
              eps Heps Htv0) as [N HN].
  intros n Hn.
  exact (HN n (NatLe_drop _ _ Hn)).
Qed.

(* sigT packaging of the end-to-end uniform geometric-decay modulus
   witness. *)
Theorem cw2_conv_modulus_sigT : forall (delta : Real)
  (Hd1 : real_lt real_zero delta) (Hd2 : real_lt delta real_one)
  (tv_seq : nat -> Real)
  (Hstep : forall n : nat,
             real_le (tv_seq (Datatypes.S n))
                     (real_mult (cw2_kappa delta) (tv_seq n)))
  (eps : Real) (Heps : real_lt real_zero eps)
  (Htv0 : real_lt real_zero (tv_seq Datatypes.O)),
  sigT (fun N : nat =>
    forall n : nat, NatLe N n -> real_lt (tv_seq n) eps).
Proof.
  intros delta Hd1 Hd2 tv_seq Hstep eps Heps Htv0.
  exists (cw2_conv_step_calc delta Hd1 Hd2 tv_seq Hstep eps Heps Htv0).
  intros n Hn.
  exact (cw2_conv_step_correct delta Hd1 Hd2 tv_seq Hstep eps Heps Htv0 n Hn).
Defined.

(* Tail-budget projections (the host budget theorem used directly): the
   budget [N] is simultaneously valid for both tails once
   [min p q >= N] (restated on the NatLe face). *)

Definition cw2_min_tail_k (delta : Real) (Hd1 : real_lt real_zero delta)
  (Hd2 : real_lt delta real_one) (a : Real) (Ha : real_lt real_zero a)
  (eps : Real) (Heps : real_lt real_zero eps) : nat :=
  projT1 (budget_min_tail (cw2_kappa delta) a eps (cw2_rate_pos delta Hd2)
            (cw2_rate_lt_one delta Hd1) Ha Heps).

Theorem cw2_min_tail_correct : forall (delta : Real)
  (Hd1 : real_lt real_zero delta) (Hd2 : real_lt delta real_one)
  (a : Real) (Ha : real_lt real_zero a) (eps : Real)
  (Heps : real_lt real_zero eps) (p q : nat),
  NatLe (cw2_min_tail_k delta Hd1 Hd2 a Ha eps Heps) (Nat.min p q) ->
  real_lt (real_mult a
             (real_pow (cw2_kappa delta) (Nat.min p q))) eps.
Proof.
  intros delta Hd1 Hd2 a Ha eps Heps p q Hpq.
  exact (projT2 (budget_min_tail (cw2_kappa delta) a eps
                   (cw2_rate_pos delta Hd2) (cw2_rate_lt_one delta Hd1)
                   Ha Heps)
           p q (NatLe_drop _ _ Hpq)).
Qed.

(* sigT packaging of the tail-budget modulus witness. *)
Theorem cw2_min_tail_modulus_sigT : forall (delta : Real)
  (Hd1 : real_lt real_zero delta) (Hd2 : real_lt delta real_one)
  (a : Real) (Ha : real_lt real_zero a) (eps : Real)
  (Heps : real_lt real_zero eps),
  sigT (fun N : nat =>
    forall p q : nat, NatLe N (Nat.min p q) ->
      real_lt (real_mult a
                 (real_pow (cw2_kappa delta) (Nat.min p q))) eps).
Proof.
  intros delta Hd1 Hd2 a Ha eps Heps.
  exists (cw2_min_tail_k delta Hd1 Hd2 a Ha eps Heps).
  intros p q Hpq.
  exact (cw2_min_tail_correct delta Hd1 Hd2 a Ha eps Heps p q Hpq).
Defined.

(* Audit port: the assumption audit (all entries expected [Closed]) and
   the extraction witness, following the series template. *)

Print Assumptions cw2_k_enum_correct.
Print Assumptions cw2_k_enum_minimal.
Print Assumptions cw2_k_enum_first_break.
Print Assumptions cw2_k_enum_logface.
Print Assumptions cw2_fuel_sufficient_half.
Print Assumptions cw2_fuel_sufficient_qbound.
Print Assumptions cw2_k_enum_auto_half.
Print Assumptions cw2_rate_pos.
Print Assumptions cw2_rate_lt_one.
Print Assumptions cw2_r_pow_anti_mono_set.
Print Assumptions cw2_arch_k_budget.
Print Assumptions cw2_tv_decay.
Print Assumptions cw2_step_calc_correct.
Print Assumptions cw2_mixing_modulus_sigT.
Print Assumptions cw2_conv_step_correct.
Print Assumptions cw2_conv_modulus_sigT.
Print Assumptions cw2_min_tail_correct.
Print Assumptions cw2_min_tail_modulus_sigT.

(* Extraction port: the four nat-level calculators (genuine fixpoints,
   no stubs, no truncation). *)
Separate Extraction cw2_ceil_div cw2_iter cw2_pow_iter cw2_k_enum.
