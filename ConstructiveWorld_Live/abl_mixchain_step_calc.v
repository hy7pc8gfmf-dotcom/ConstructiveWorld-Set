(* ConstructiveWorld-Set -- abl_mixchain_step_calc: step-count
   calculators for the mtc_ mixing-time chain. *)
(** * abl_mixchain_step_calc: step-count calculators for the
    MixTimeChain chain, carried on Set.

    Mission.  The nat fixed-point enumerator of the log-modulus
      equation ([mtc2_ceil_div]/[mtc2_iter]/[mtc2_pow_iter]/
      [mtc2_k_enum] with the correctness halves [mtc2_k_enum_correct]
      and [mtc2_k_enum_logface] and the decay and fuel witnesses);
      the real-face bridge ([mtc2_rpow_mult], [mtc2_nat_r_pow],
      [mtc2_rpow_inv], [mtc2_nat_le_embed], [mtc2_enum_real_correct]);
      the concrete-rate calculators and the [sigT] modulus witnesses
      [mtc2_kappa_modulus_sigT], [mtc2_mixing_modulus_sigT] and
      [mtc2_cauchy_exp_modulus_sigT].
    Dependencies.  [S01_BaseRing], [S02_CauchyComplete], [S03_QExp],
      [S04_RealExpLogConv], [Arch_PA_02], [UpTVDoeblin],
      [UpReqMixingTime], [MixTimeChain]; Stdlib [List], [PeanoNat],
      [Arith.Arith], [Lia].
    References.  ConstructiveWorld-Main [abl_mixchain_step_calc]; the
      geometric-drift mixing-time bound (the calculator companion of
      [MixTimeChain]).
    Constructivity.  All statements are Set-carried ([sigT] witnesses,
      [prod] conjunctions, [NatLe] order bounds, [real_lt]/[real_le]
      comparisons; zero Prop statement faces); [mtc2_k_enum] is a
      genuine fuel-bounded [Fixpoint]; no axioms; [Print Assumptions]
      reports Closed and the nat calculators extract with zero
      [Obj.magic].
    Build.  [rocq c -native-compiler no -q -Q . ""
      abl_mixchain_step_calc.v] on Rocq 9.3.0, cpu_guard wrapped. *)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import Arch_PA_02.
Require Import UpTVDoeblin.
Require Import UpReqMixingTime.
Require Import MixTimeChain.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lia.

(* ================= Section 1. The nat fixed-point enumerator of the
   log-modulus equation (genuine Fixpoint, ceiling-division form) ================= *)

(* The nat face of the modulus equation log (a * kappa^N) <= log eps:
   with kappa = p/q (0 < p < q), the initial value a = A and the
   budget eps = E written over a common fixed-point scale, enumerate N
   such that A * p^N <= E * q^N.  The enumerator walks ceiling-division
   decay steps (ceiling division keeps the upper-bound direction).  All
   order bounds travel on the NatLe Set carrier (the decidable leb
   form); strict bounds are expressed as [NatLe (S _)].  This section
   holds the strict-decay lemmas and the fuel-sufficiency witnesses
   (the termination premise is closed on the caller side). *)

(* Ceiling division: the round-up quotient (a + q - 1) / q for q >= 1;
   rounding up keeps the upper-bound direction. *)
Definition mtc2_ceil_div (a q : nat) : nat := Nat.div (a + q - 1) q.

Lemma mtc2_ceil_div_le : forall a q,
  NatLe 1 q -> NatLe a (mtc2_ceil_div a q * q).
Proof.
  intros a q Hq. pose proof (NatLe_drop 1 q Hq) as Hq'.
  unfold mtc2_ceil_div.
  assert (Hq1 : (0 < q)%nat) by lia.
  pose proof (Nat.div_mod_eq (a + q - 1) q) as Hdm.
  pose proof (Nat.mod_upper_bound (a + q - 1) q (proj2 (Nat.neq_0_lt_0 q) Hq1)) as Hmb.
  apply (NatLe_lift _ _). lia.
Qed.

(* Decay step: x walks one fixed-point multiplication step of
   kappa = p/q (ceiling form). *)
Definition mtc2_iter (p q x : nat) : nat := mtc2_ceil_div (x * p) q.

Lemma mtc2_iter_step_bound : forall p q x,
  NatLe 1 q -> NatLe (x * p) (mtc2_iter p q x * q).
Proof.
  intros p q x Hq. unfold mtc2_iter. apply (mtc2_ceil_div_le (x * p) q Hq).
Qed.

(* Iterated power: the k-fold composition of [mtc2_iter] (the ceiling
   face of the geometric decay sequence). *)
Fixpoint mtc2_pow_iter (p q x k : nat) : nat :=
  match k with
  | O => x
  | Datatypes.S k' => mtc2_iter p q (mtc2_pow_iter p q x k')
  end.

(* Composition swap: one step followed by k iterations equals k
   iterations followed by one step (the same S+1-fold composition). *)
Lemma mtc2_pow_iter_comm : forall p q x k,
  mtc2_pow_iter p q (mtc2_iter p q x) k = mtc2_iter p q (mtc2_pow_iter p q x k).
Proof.
  intros p q x k. induction k as [| k IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. simpl. reflexivity.
Qed.

(* Enumerator: a fuel-bounded Fixpoint; stop once x <= E (returning the
   steps taken), otherwise walk a decay step and search on. *)
Fixpoint mtc2_k_enum (fuel p q x e : nat) : nat :=
  match fuel with
  | O => O
  | Datatypes.S f =>
      if Nat.leb x e then O else Datatypes.S (mtc2_k_enum f p q (mtc2_iter p q x) e)
  end.

(* Correctness (ceiling face): whenever the budget is reachable within
   the fuel, the ceiling value at the enumerated step N is at most e.
   The reachability witness is a sigT pair with a prod of NatLe
   bounds, all on Set carriers. *)
Theorem mtc2_k_enum_correct : forall fuel p q x e,
  (sigT (fun k : nat =>
    prod (NatLe k fuel) (NatLe (mtc2_pow_iter p q x k) e))) ->
  NatLe (mtc2_pow_iter p q x (mtc2_k_enum fuel p q x e)) e.
Proof.
  intros fuel. induction fuel as [| f IH]; intros p q x e Hterm.
  - destruct Hterm as [k [Hk Hbound]].
    pose proof (NatLe_drop k 0 Hk) as Hk'.
    assert (Hk0 : k = 0%nat) by lia. subst k. simpl. exact Hbound.
  - simpl. destruct (Nat.leb x e) eqn:Hle.
    + simpl. apply (NatLe_lift x e). exact (proj1 (Nat.leb_le x e) Hle).
    + assert (Hgt : (e < x)%nat) by (apply (proj1 (Nat.leb_gt x e)); exact Hle).
      destruct Hterm as [k [Hk Hbound]].
      pose proof (NatLe_drop k (Datatypes.S f) Hk) as Hk'.
      destruct k as [| k'].
      * pose proof (NatLe_drop (mtc2_pow_iter p q x 0) e Hbound) as Hb'.
        simpl in Hb'. lia.
      * simpl in Hbound.
        rewrite <- (mtc2_pow_iter_comm p q x k') in Hbound.
        assert (Hk2 : (k' <= f)%nat) by lia.
        assert (Hterm' : sigT (fun k0 : nat =>
                          prod (NatLe k0 f)
                               (NatLe (mtc2_pow_iter p q (mtc2_iter p q x) k0) e))).
        { exact (existT _ k' (pair (NatLe_lift k' f Hk2) Hbound)). }
        specialize (IH p q (mtc2_iter p q x) e Hterm').
        simpl.
        rewrite <- (mtc2_pow_iter_comm p q x (mtc2_k_enum f p q (mtc2_iter p q x) e)).
        exact IH.
Qed.

(* Exact-face invariant: the ceiling value always covers the exact
   geometric value, x * p^k <= iter^k(x) * q^k. *)
Lemma mtc2_pow_iter_exact_ge : forall p q x k,
  NatLe 1 p -> NatLe 1 q -> NatLe (x * p ^ k) (mtc2_pow_iter p q x k * q ^ k).
Proof.
  intros p q x k Hp Hq. induction k as [| k IH].
  - apply (NatLe_lift _ _). simpl. lia.
  - pose proof (NatLe_drop _ _ IH) as IH'.
    apply (NatLe_lift _ _). simpl.
    apply (Nat.le_trans _ (mtc2_pow_iter p q x k * q ^ k * p)).
    + rewrite (Nat.mul_comm p (p ^ k)).
      rewrite (Nat.mul_assoc x (p ^ k) p).
      apply (Nat.mul_le_mono_r _ _ p). exact IH'.
    + pose proof (mtc2_iter_step_bound p q (mtc2_pow_iter p q x k) Hq) as Hstep.
      pose proof (NatLe_drop _ _ Hstep) as Hstep'.
      rewrite <- (Nat.mul_assoc (mtc2_pow_iter p q x k) (q ^ k) p).
      rewrite (Nat.mul_comm (q ^ k) p).
      rewrite (Nat.mul_assoc (mtc2_pow_iter p q x k) p (q ^ k)).
      apply (Nat.le_trans _ (mtc2_iter p q (mtc2_pow_iter p q x k) * q * q ^ k)).
      * apply (Nat.mul_le_mono_r _ _ (q ^ k)). exact Hstep'.
      * rewrite (Nat.mul_assoc (mtc2_iter p q (mtc2_pow_iter p q x k)) q (q ^ k)).
        apply (Nat.le_refl _).
Qed.

(* The nat form of the log-modulus equation: at the enumerated N,
   x * p^N <= e * q^N (the equivalent face under log monotonicity). *)
Theorem mtc2_k_enum_logface : forall fuel p q x e,
  NatLe 1 p -> NatLe 1 q ->
  (sigT (fun k : nat =>
    prod (NatLe k fuel) (NatLe (mtc2_pow_iter p q x k) e))) ->
  NatLe (x * p ^ mtc2_k_enum fuel p q x e)
        (e * q ^ mtc2_k_enum fuel p q x e).
Proof.
  intros fuel p q x e Hp Hq Hterm.
  pose proof (mtc2_k_enum_correct fuel p q x e Hterm) as H1.
  pose proof (mtc2_pow_iter_exact_ge p q x (mtc2_k_enum fuel p q x e) Hp Hq) as H2.
  pose proof (NatLe_drop _ _ H1) as H1'.
  pose proof (NatLe_drop _ _ H2) as H2'.
  apply (NatLe_lift _ _).
  apply (Nat.le_trans _
           (mtc2_pow_iter p q x (mtc2_k_enum fuel p q x e)
              * q ^ mtc2_k_enum fuel p q x e)).
  - exact H2'.
  - apply (Nat.mul_le_mono_r _ _ (q ^ mtc2_k_enum fuel p q x e)). exact H1'.
Qed.

(* ---------- Strict decay and fuel sufficiency (the termination
   premise closed on the caller side) ---------- *)

(* Decay core: when x * p + q <= x * q, the ceiling step strictly
   decreases (the floor criterion d * q <= a < x * q). *)
Lemma mtc2_iter_lt_decay : forall p q x,
  NatLe 1 q -> NatLe (x * p + q) (x * q) ->
  NatLe (Datatypes.S (mtc2_iter p q x)) x.
Proof.
  intros p q x Hq Hdecay.
  pose proof (NatLe_drop 1 q Hq) as Hq'.
  pose proof (NatLe_drop (x * p + q) (x * q) Hdecay) as Hdecay'.
  unfold mtc2_iter, mtc2_ceil_div.
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

(* Half-domain decay: when 2 * p <= q and x >= 2, the step strictly
   decreases (x * (q - p) >= 2 * (q - p) >= q). *)
Lemma mtc2_iter_lt_half : forall p q x,
  NatLe 1 p -> NatLe (2 * p) q -> NatLe 2 x ->
  NatLe (Datatypes.S (mtc2_iter p q x)) x.
Proof.
  intros p q x Hp H2p Hx.
  pose proof (NatLe_drop 1 p Hp) as Hp'.
  pose proof (NatLe_drop (2 * p) q H2p) as H2p'.
  pose proof (NatLe_drop 2 x Hx) as Hx'.
  apply (mtc2_iter_lt_decay p q x).
  - apply (NatLe_lift 1 q). lia.
  - apply (NatLe_lift (x * p + q) (x * q)).
    assert (Hsplit : (x * q = x * p + x * (q - p))%nat).
    { rewrite <- (Nat.mul_add_distr_l x p (q - p)). f_equal. lia. }
    assert (H2le : (2 * (q - p) <= x * (q - p))%nat)
      by (apply Nat.mul_le_mono_r; exact Hx').
    rewrite Hsplit. lia.
Qed.

(* Qbound-domain decay: when p < q and x >= q, the step strictly
   decreases (x * (q - p) >= q * 1 >= q). *)
Lemma mtc2_iter_lt_q : forall p q x,
  NatLe 1 p -> NatLe (Datatypes.S p) q -> NatLe q x ->
  NatLe (Datatypes.S (mtc2_iter p q x)) x.
Proof.
  intros p q x Hp Hpq Hx.
  pose proof (NatLe_drop 1 p Hp) as Hp'.
  pose proof (NatLe_drop (Datatypes.S p) q Hpq) as Hpq'.
  pose proof (NatLe_drop q x Hx) as Hx'.
  apply (mtc2_iter_lt_decay p q x).
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

(* Fuel sufficiency (general form): whenever every step above the
   budget strictly decays, fuel of A steps always reaches the budget.
   Structural induction on the fuel; the witness is a sigT pair with a
   prod of NatLe bounds, all on Set carriers. *)
Lemma mtc2_fuel_sufficient_gen : forall fuel p q x E,
  NatLe 1 q -> NatLe 1 E -> NatLe x fuel ->
  (forall y : nat, NatLe (Datatypes.S E) y ->
                   NatLe (Datatypes.S (mtc2_iter p q y)) y) ->
  sigT (fun k : nat => prod (NatLe k fuel)
                            (NatLe (mtc2_pow_iter p q x k) E)).
Proof.
  intros fuel.
  induction fuel as [| f IH].
  - intros p q x E Hq HE Hx Hdecay.
    pose proof (NatLe_drop x 0 Hx) as Hx'.
    assert (Hx0 : x = 0%nat) by lia. subst x.
    exists 0%nat. split.
    + apply (NatLe_lift 0 0). apply Nat.le_refl.
    + simpl. apply (NatLe_lift 0 E). apply Nat.le_0_l.
  - intros p q x E Hq HE Hx Hdecay.
    destruct (Nat.leb x E) eqn:Hle.
    + exists 0%nat. split.
      * apply (NatLe_lift 0 (Datatypes.S f)). apply Nat.le_0_l.
      * simpl. apply (NatLe_lift x E). exact (proj1 (Nat.leb_le x E) Hle).
    + assert (Hgt : (E < x)%nat) by (apply (proj1 (Nat.leb_gt x E)); exact Hle).
      pose proof (NatLe_drop x (Datatypes.S f) Hx) as Hx'.
      assert (Hdec : NatLe (Datatypes.S (mtc2_iter p q x)) x).
      { apply Hdecay. apply (NatLe_lift (Datatypes.S E) x). lia. }
      pose proof (NatLe_drop (Datatypes.S (mtc2_iter p q x)) x Hdec) as Hdec'.
      assert (Hiterf : (mtc2_iter p q x <= f)%nat) by lia.
      destruct (IH p q (mtc2_iter p q x) E Hq HE (NatLe_lift _ _ Hiterf) Hdecay)
        as [k0 [Hk0 Hb0]].
      exists (Datatypes.S k0). split.
      * pose proof (NatLe_drop k0 f Hk0) as Hk0'.
        apply (NatLe_lift _ _). lia.
      * simpl. rewrite <- (mtc2_pow_iter_comm p q x k0). exact Hb0.
Qed.

(* Half-domain fuel sufficiency: for 2 * p <= q and budget E >= 1,
   fuel := x is enough. *)
Theorem mtc2_fuel_sufficient_half : forall fuel p q x E,
  NatLe 1 p -> NatLe (2 * p) q -> NatLe 1 E -> NatLe x fuel ->
  sigT (fun k : nat => prod (NatLe k fuel)
                            (NatLe (mtc2_pow_iter p q x k) E)).
Proof.
  intros fuel p q x E Hp H2p HE Hx.
  apply (mtc2_fuel_sufficient_gen fuel p q x E).
  - apply (NatLe_lift 1 q).
    pose proof (NatLe_drop 1 p Hp). pose proof (NatLe_drop (2 * p) q H2p). lia.
  - exact HE.
  - exact Hx.
  - intros y Hy. apply (mtc2_iter_lt_half p q y).
    + exact Hp.
    + exact H2p.
    + apply (NatLe_lift 2 y).
      pose proof (NatLe_drop 1 E HE).
      pose proof (NatLe_drop (Datatypes.S E) y Hy). lia.
Qed.

(* Qbound-domain fuel sufficiency: for budget E >= q - 1 and any
   p < q, fuel := x is enough. *)
Theorem mtc2_fuel_sufficient_qbound : forall fuel p q x E,
  NatLe 1 p -> NatLe (Datatypes.S p) q -> NatLe q E -> NatLe x fuel ->
  sigT (fun k : nat => prod (NatLe k fuel)
                            (NatLe (mtc2_pow_iter p q x k) E)).
Proof.
  intros fuel p q x E Hp Hpq HqE Hx.
  apply (mtc2_fuel_sufficient_gen fuel p q x E).
  - apply (NatLe_lift 1 q).
    pose proof (NatLe_drop 1 p Hp). pose proof (NatLe_drop (Datatypes.S p) q Hpq). lia.
  - apply (NatLe_lift 1 E).
    pose proof (NatLe_drop (Datatypes.S p) q Hpq).
    pose proof (NatLe_drop q E HqE). lia.
  - exact Hx.
  - intros y Hy. apply (mtc2_iter_lt_q p q y).
    + exact Hp.
    + exact Hpq.
    + apply (NatLe_lift q y).
      pose proof (NatLe_drop q E HqE).
      pose proof (NatLe_drop (Datatypes.S E) y Hy). lia.
Qed.

(* Caller-side automatic fuel: on the half domain the enumerator
   reading is the correct step count (the termination premise
   supplied). *)
Theorem mtc2_k_enum_auto_half : forall p q A E,
  NatLe 1 p -> NatLe (2 * p) q -> NatLe 1 E -> NatLe (Datatypes.S E) A ->
  NatLe (mtc2_pow_iter p q A (mtc2_k_enum A p q A E)) E.
Proof.
  intros p q A E Hp H2p HE HAE.
  apply (mtc2_k_enum_correct A p q A E).
  apply (mtc2_fuel_sufficient_half A p q A E).
  - exact Hp.
  - exact H2p.
  - exact HE.
  - apply (NatLe_lift A A). pose proof (NatLe_drop (Datatypes.S E) A HAE). lia.
Qed.

(* Fixed-point check one (evaluated at compile time): the halving
   enumeration for kappa = 1/2, A = 1000, E = 5. *)
Eval vm_compute in (mtc2_k_enum 30 1 2 1000 5).

(* Fixed-point check two: kappa = 3/4 (qbound domain with E = 4 >=
   q - 1 = 3), A = 50, E = 4. *)
Eval vm_compute in (mtc2_k_enum 30 3 4 50 4).

(* ================= Section 2. The real-face bridge: real-face
   correctness of the fixed-point calculator on concrete rational data ================= *)

(* Generic real-interface section; the nat order bounds stay on the
   NatLe Set carrier and are not dissolved into real-face goals.  The
   embedding bridge follows the template of the calculator series:
   decidable leb split plus difference-equality replacement, the nat
   induction walking a Set-level addition helper, no Prop elimination. *)

Section Mtc2EnumReal.

Context {RI : RealInterfaceEnhanced}.

Let R := @R RI.
Let zero := @zero RI.
Let one := @one RI.
Let plus := @plus RI.
Let mult := @mult RI.
Let lt := @lt RI.
Let le := @le RI.

(* Left-unit bridge (one Id-face hop). *)
Lemma mtc2_mult_one_l : forall t : R, Id (mult one t) t.
Proof.
  intros t. apply (id_trans (mult_comm one t)). apply (mult_one t).
Qed.

(* Inverse uniqueness: if y * z == 1 then z == inv y. *)
Lemma mtc2_inv_unique : forall (y z : R) (Hy : lt zero y),
  Id (mult y z) one -> Id z (inv_pos y Hy).
Proof.
  intros y z Hy Hz.
  exact (id_trans (id_sym (mult_one z))
         (id_trans (id_cong (fun t => mult z t) (id_sym (inv_pos_correct y Hy)))
         (id_trans (mult_assoc z y (inv_pos y Hy))
         (id_trans (id_cong (fun t => mult t (inv_pos y Hy)) (mult_comm z y))
         (id_trans (id_cong (fun t => mult t (inv_pos y Hy)) Hz)
         (mtc2_mult_one_l (inv_pos y Hy))))))).
Qed.

(* Power split over multiplication: r_pow (a * b) n == r_pow a n *
   r_pow b n (absent from the library and supplied here; rewrite
   matching on the Id face is unreliable, so the chain is term-mode). *)
Lemma mtc2_rpow_mult : forall (a b : R) (n : nat),
  Id (r_pow (mult a b) n) (mult (r_pow a n) (r_pow b n)).
Proof.
  intros a b n. induction n as [| n IH].
  - simpl. exact (id_sym (mult_one one)).
  - simpl.
    exact (id_trans
             (id_cong (fun t => mult (mult a b) t) IH)
             (id_trans (id_sym (mult_assoc a b (mult (r_pow a n) (r_pow b n))))
             (id_trans (id_cong (fun t => mult a t) (mult_assoc b (r_pow a n) (r_pow b n)))
             (id_trans (id_cong (fun t => mult a t)
                                (id_cong (fun t => mult t (r_pow b n)) (mult_comm b (r_pow a n))))
             (id_trans (id_cong (fun t => mult a t) (id_sym (mult_assoc (r_pow a n) b (r_pow b n))))
                       (mult_assoc a (r_pow a n) (mult b (r_pow b n)))))))).
Qed.

(* nat_to_R commutes with powers: r_pow (nat_to_R k) n ==
   nat_to_R (k ^ n) (induction on the multiplicative homomorphism). *)
Lemma mtc2_nat_r_pow : forall k n : nat,
  Id (r_pow (nat_to_R k) n) (nat_to_R (k ^ n)%nat).
Proof.
  intros k n. induction n as [| n IH].
  - exact (id_sym (plus_zero one)).
  - exact (id_trans
             (id_cong (fun t => mult (nat_to_R k) t) IH)
             (id_sym (nat_to_R_mult_hom k (k ^ n)%nat))).
Qed.

(* Power split over inverses: r_pow (inv_pos x Hx) n ==
   inv_pos (r_pow x n) Hp (induction on inverse uniqueness; the
   positivity certificate Hp of the inverse is an explicit argument,
   guarding against reshaping over opaque constants). *)
Lemma mtc2_rpow_inv : forall (x : R) (Hx : lt zero x) (n : nat) (Hp : lt zero (r_pow x n)),
  Id (r_pow (inv_pos x Hx) n) (inv_pos (r_pow x n) Hp).
Proof.
  intros x Hx n. induction n as [| n IH]; intros Hp.
  - exact (id_sym (id_trans (id_sym (mtc2_mult_one_l (inv_pos one Hp)))
                            (inv_pos_correct one Hp))).
  - specialize (IH (r_pow_pos x n Hx)).
    exact (id_trans
             (id_cong (fun t => mult (inv_pos x Hx) t) IH)
             (mtc2_inv_unique (mult x (r_pow x n))
                             (mult (inv_pos x Hx)
                                   (inv_pos (r_pow x n) (r_pow_pos x n Hx)))
                             Hp
                             (id_trans
                                (id_sym (mult_assoc x (r_pow x n)
                                           (mult (inv_pos x Hx)
                                                 (inv_pos (r_pow x n) (r_pow_pos x n Hx)))))
                             (id_trans
                                (id_cong (fun t => mult x t)
                                         (mult_assoc (r_pow x n) (inv_pos x Hx)
                                                     (inv_pos (r_pow x n) (r_pow_pos x n Hx))))
                             (id_trans
                                (id_cong (fun t => mult x t)
                                         (id_cong (fun t => mult t (inv_pos (r_pow x n) (r_pow_pos x n Hx)))
                                                  (mult_comm (r_pow x n) (inv_pos x Hx))))
                             (id_trans
                                (id_cong (fun t => mult x t)
                                         (id_sym (mult_assoc (inv_pos x Hx) (r_pow x n)
                                                        (inv_pos (r_pow x n) (r_pow_pos x n Hx)))))
                             (id_trans
                                (id_cong (fun t => mult x t)
                                         (id_cong (fun t => mult (inv_pos x Hx) t)
                                                  (inv_pos_correct (r_pow x n) (r_pow_pos x n Hx))))
                             (id_trans
                                (id_cong (fun t => mult x t) (mult_one (inv_pos x Hx)))
                                (inv_pos_correct x Hx))))))))).
Qed.

(* The monotone embedding bridge from nat order bounds to real-face
   le (absent from the library and supplied here).  Elimination
   discipline: the NatLe carrier is not dissolved into real-face
   goals; the decidable leb split plus difference-equality replacement
   carry the argument, the nat induction walks a Set-level addition
   helper, and no Prop elimination appears. *)
Lemma mtc2_nat_le_plus_aux : forall n m : nat, le (nat_to_R m) (nat_to_R (n + m)%nat).
Proof.
  intros n m. induction n as [| n IH].
  - simpl. apply le_refl.
  - simpl.
    apply (le_trans _ (nat_to_R (n + m)%nat)).
    + exact IH.
    + apply (le_id_l (nat_to_R (n + m)) (plus (nat_to_R (n + m)) zero)
              (plus one (nat_to_R (n + m)))
              (id_sym (plus_zero (nat_to_R (n + m))))).
      apply (le_id_r (plus (nat_to_R (n + m)) zero) (plus (nat_to_R (n + m)) one)
              (plus one (nat_to_R (n + m))) (plus_comm (nat_to_R (n + m)) one)).
      apply (le_plus_compat (nat_to_R (n + m)) (nat_to_R (n + m)) zero one
               (le_refl (nat_to_R (n + m)))).
      exact (lt_le_iff zero one (inl one_pos)).
Qed.

Lemma mtc2_nat_le_embed : forall m n : nat,
  NatLe m n -> le (nat_to_R m) (nat_to_R n).
Proof.
  intros m n Hmn. destruct (Nat.leb n m) eqn:E.
  - assert (Hle : (n <= m)%nat) by (apply (proj1 (Nat.leb_le n m)); exact E).
    pose proof (NatLe_drop m n Hmn) as Hmn'.
    assert (Heq : n = m%nat).
    { apply (Nat.le_antisymm n m).
      - exact Hle.
      - exact Hmn'. }
    rewrite Heq. apply le_refl.
  - destruct n as [| n'].
    + assert (Hc : (m < 0)%nat) by (apply (proj1 (Nat.leb_gt 0 m)); exact E).
      destruct (Nat.nlt_0_r m Hc).
    + assert (Hlt : (m < Datatypes.S n')%nat)
        by (apply (proj1 (Nat.leb_gt (Datatypes.S n') m)); exact E).
      pose proof (NatLe_drop m (Datatypes.S n') Hmn) as HmnD.
      assert (Hmn' : (m <= n')%nat) by (apply (proj1 (Nat.lt_succ_r m n')); exact Hlt).
      replace (Datatypes.S n')%nat with ((Datatypes.S (n' - m)) + m)%nat by lia.
      apply (mtc2_nat_le_plus_aux (Datatypes.S (n' - m)) m).
Qed.

(* The fixed-point main statement: on rational data kappa := p/q,
   a := A and eps := E, the real-face correctness of the enumerated N
   (the le form, no arch dependence; the whole bridge is closed by the
   power-split laws above). *)
Theorem mtc2_enum_real_correct : forall (fuel p q A E : nat)
  (Hqr : lt zero (nat_to_R q)),
  NatLe 1 p -> NatLe 1 q -> NatLe 1 A -> NatLe 1 E ->
  (sigT (fun k : nat =>
    prod (NatLe k fuel) (NatLe (mtc2_pow_iter p q A k) E))) ->
  le (mult (nat_to_R A)
            (r_pow (mult (nat_to_R p) (inv_pos (nat_to_R q) Hqr))
                   (mtc2_k_enum fuel p q A E)))
     (nat_to_R E).
Proof.
  intros fuel p q A E Hqr Hp Hq HA HE Hterm.
  set (N := mtc2_k_enum fuel p q A E).
  set (w := inv_pos (r_pow (nat_to_R q) N) (r_pow_pos (nat_to_R q) N Hqr)).
  pose proof (mtc2_k_enum_logface fuel p q A E Hp Hq Hterm) as Hlog.
  pose proof (mtc2_nat_le_embed (A * p ^ N) (E * q ^ N) Hlog) as Hemb.
  assert (Hsplit : le (mult (nat_to_R A) (nat_to_R (p ^ N)))
                      (mult (nat_to_R E) (nat_to_R (q ^ N)))).
  { apply (le_id_l (mult (nat_to_R A) (nat_to_R (p ^ N)))
                   (nat_to_R (A * p ^ N))).
    - exact (id_sym (nat_to_R_mult_hom A (p ^ N))).
    - apply (le_id_r (nat_to_R (A * p ^ N))
                     (nat_to_R (E * q ^ N))
                     (mult (nat_to_R E) (nat_to_R (q ^ N)))
                     (nat_to_R_mult_hom E (q ^ N))).
      exact Hemb. }
  assert (H3 : le (mult (mult (nat_to_R A) (nat_to_R (p ^ N))) w)
                  (mult (mult (nat_to_R E) (nat_to_R (q ^ N))) w))
    by exact (le_mult_compat (mult (nat_to_R A) (nat_to_R (p ^ N)))
                             (mult (nat_to_R E) (nat_to_R (q ^ N))) w
                             (inv_pos_pos (r_pow (nat_to_R q) N)
                                (r_pow_pos (nat_to_R q) N Hqr))
                             Hsplit).
  assert (HL : Id (mult (nat_to_R A)
                        (r_pow (mult (nat_to_R p) (inv_pos (nat_to_R q) Hqr)) N))
                  (mult (mult (nat_to_R A) (nat_to_R (p ^ N))) w)).
  { pose proof (mtc2_rpow_mult (nat_to_R p) (inv_pos (nat_to_R q) Hqr) N) as Hpm.
    pose proof (mtc2_nat_r_pow p N) as Hpo.
    pose proof (mtc2_rpow_inv (nat_to_R q) Hqr N (r_pow_pos (nat_to_R q) N Hqr)) as Hpi.
    assert (Hs2 : Id (mult (r_pow (nat_to_R p) N)
                           (r_pow (inv_pos (nat_to_R q) Hqr) N))
                     (mult (nat_to_R (p ^ N)) w)).
    { apply (id_trans
               (id_cong (fun u => mult u (r_pow (inv_pos (nat_to_R q) Hqr) N)) Hpo)).
      exact (id_cong (fun u => mult (nat_to_R (p ^ N)) u) Hpi). }
    apply (id_trans (id_cong (fun t => mult (nat_to_R A) t) Hpm)).
    apply (id_trans (id_cong (fun t => mult (nat_to_R A) t) Hs2)).
    exact (mult_assoc (nat_to_R A) (nat_to_R (p ^ N)) w). }
  assert (HR : Id (mult (mult (nat_to_R E) (nat_to_R (q ^ N))) w) (nat_to_R E)).
  { exact (id_trans
             (id_sym (mult_assoc (nat_to_R E) (nat_to_R (q ^ N)) w))
             (id_trans
                (id_cong (fun t => mult (nat_to_R E) t)
                         (id_trans
                            (id_cong (fun u => mult u w)
                                     (id_sym (mtc2_nat_r_pow q N)))
                            (inv_pos_correct (r_pow (nat_to_R q) N)
                                             (r_pow_pos (nat_to_R q) N Hqr))))
                (mult_one (nat_to_R E)))). }
  apply (le_id_l (mult (nat_to_R A)
                         (r_pow (mult (nat_to_R p) (inv_pos (nat_to_R q) Hqr)) N))
                 (mult (mult (nat_to_R A) (nat_to_R (p ^ N))) w)
                 (nat_to_R E) HL).
  apply (le_id_r (mult (mult (nat_to_R A) (nat_to_R (p ^ N))) w)
                 (mult (mult (nat_to_R E) (nat_to_R (q ^ N))) w)
                 (nat_to_R E) HR H3).
Qed.

End Mtc2EnumReal.

(* ================= Section 3. The concrete-face counterparts of the
   MixTimeChain MtcCauchySoftmax certificate subset ================= *)

(* The rate extraction kappa := tv_omd delta_star with
   delta_star := lo * lo and lo := expf (invT * opp Delta); the two
   generations of the generic rate-face calculator (the mix_k_select
   form and the witness/proof separated mix_k_compute form); the
   concrete-rate calculators with sigT modulus witnesses; the
   projT1/projT2 double projections of the host main statement. *)

Section Mtc2FaceCalc.

Variable invT : Real.
Variable invT_pos : real_lt real_zero invT.
Variable Delta : Real.
Variable Delta_pos : real_lt real_zero Delta.
Variable expf : Real -> Real.
Variable expf_pos : forall x : Real, real_lt real_zero (expf x).
Variable expf_zero : real_eq (expf real_zero) real_one.
Variable expf_mono_lt : forall a b : Real, real_lt a b -> real_lt (expf a) (expf b).

Let lo := expf (real_mult invT (real_opp Delta)).
Let delta_star := real_mult lo lo.
Let kappa := tv_omd delta_star.

(* ==== The rate-extraction certificate pair (the discharged host
   lemmas consumed directly; the argument orders are as verified
   against the host forms: eight arguments for [mtc_kappa_pos] and
   four for the minimized [mtc_kappa_lt_one]) ==== *)

Lemma mtc2_rate_pos : real_lt real_zero kappa.
Proof.
  exact (mtc_kappa_pos invT invT_pos Delta Delta_pos
           expf expf_pos expf_zero expf_mono_lt).
Qed.

Lemma mtc2_rate_lt_one : real_lt kappa real_one.
Proof.
  exact (mtc_kappa_lt_one invT Delta expf expf_pos).
Qed.

(* ==== The two generations of the generic rate-face calculator ====

   Generation one, the mtg_k_calc-isomorphic form: mix_k_select with
   its seven arguments wired directly, decided on the Or encoding of
   the le face.  Generation two, the witness/proof separated form:
   mix_k_compute returns a transparent reading as an explicit nat via
   real_arch, while mix_k_spec carries the correctness certificate
   opaquely and the runtime never forces it. *)

Definition mtc2_rate_step_calc (krate TV0 budget : Real)
  (Hk1 : real_lt real_zero krate) (Hk2 : real_lt krate real_one)
  (Ha : real_le real_zero TV0) (Hb : real_lt real_zero budget) : nat :=
  projT1 (mix_k_select krate TV0 budget Hk1 Hk2 Ha Hb).

Theorem mtc2_rate_step_calc_correct : forall (krate TV0 budget : Real)
  (Hk1 : real_lt real_zero krate) (Hk2 : real_lt krate real_one)
  (Ha : real_le real_zero TV0) (Hb : real_lt real_zero budget),
  real_lt (real_mult
             (tv_rpow krate (mtc2_rate_step_calc krate TV0 budget Hk1 Hk2 Ha Hb))
             TV0)
          budget.
Proof.
  intros krate TV0 budget Hk1 Hk2 Ha Hb.
  exact (projT2 (mix_k_select krate TV0 budget Hk1 Hk2 Ha Hb)).
Qed.

Definition mtc2_rate_step_compute (krate TV0 budget : Real)
  (Hk1 : real_lt real_zero krate) (Hk2 : real_lt krate real_one)
  (Hb : real_lt real_zero budget) : nat :=
  mix_k_compute krate TV0 budget Hk1 Hk2 Hb.

Theorem mtc2_rate_step_compute_correct : forall (krate TV0 budget : Real)
  (Hk1 : real_lt real_zero krate) (Hk2 : real_lt krate real_one)
  (Ha : real_lt real_zero TV0) (Hb : real_lt real_zero budget),
  real_lt (real_mult
             (tv_rpow krate (mtc2_rate_step_compute krate TV0 budget Hk1 Hk2 Hb))
             TV0)
          budget.
Proof.
  intros krate TV0 budget Hk1 Hk2 Ha Hb.
  exact (mix_k_spec krate TV0 budget Hk1 Hk2 Ha Hb).
Qed.

(* ==== The concrete calculators on the extracted rate:
   kappa := tv_omd (lo * lo) ====

   The product lo * lo is the Cauchy face of e^(-2 * Delta * invT)
   (delta_star); the rate certificate pair [mtc2_rate_pos] and
   [mtc2_rate_lt_one] is closed by consuming the discharged host
   lemmas directly. *)

Definition mtc2_kappa_step_compute (TV0 budget : Real)
  (Hb : real_lt real_zero budget) : nat :=
  mix_k_compute kappa TV0 budget mtc2_rate_pos mtc2_rate_lt_one Hb.

Theorem mtc2_kappa_step_compute_correct : forall (TV0 : Real)
  (Ha : real_lt real_zero TV0) (budget : Real) (Hb : real_lt real_zero budget),
  real_lt (real_mult
             (tv_rpow kappa (mtc2_kappa_step_compute TV0 budget Hb))
             TV0)
          budget.
Proof.
  intros TV0 Ha budget Hb.
  exact (mix_k_spec kappa TV0 budget mtc2_rate_pos mtc2_rate_lt_one Ha Hb).
Qed.

(* The sigT packaging on the rate face: the witness type from a
   precision budget to a step count (the packaging is isomorphic to
   the mix_k_select_r1 form; the first component is the calculator
   reading, the second the correctness certificate, and the projT1
   reduction is pinned). *)
Theorem mtc2_kappa_modulus_sigT : forall (TV0 : Real)
  (Ha : real_lt real_zero TV0) (budget : Real) (Hb : real_lt real_zero budget),
  sigT (fun k : nat => real_lt (real_mult (tv_rpow kappa k) TV0) budget).
Proof.
  intros TV0 Ha budget Hb.
  exists (mtc2_kappa_step_compute TV0 budget Hb).
  exact (mtc2_kappa_step_compute_correct TV0 Ha budget Hb).
Defined.

(* ==== The double projection of the host main statement: the le-face
   calculator (mtc_attention_mixing_time_local) ==== *)

Definition mtc2_mix_step_calc (TV0 budget : Real)
  (Ha : real_le real_zero TV0) (Hb : real_lt real_zero budget) : nat :=
  projT1 (mtc_attention_mixing_time_local invT invT_pos Delta Delta_pos
            expf expf_pos expf_zero expf_mono_lt TV0 budget Ha Hb).

Theorem mtc2_mix_step_correct : forall (TV0 budget : Real)
  (Ha : real_le real_zero TV0) (Hb : real_lt real_zero budget),
  real_lt (real_mult
             (tv_rpow kappa (mtc2_mix_step_calc TV0 budget Ha Hb))
             TV0)
          budget.
Proof.
  intros TV0 budget Ha Hb.
  exact (projT2 (mtc_attention_mixing_time_local invT invT_pos Delta Delta_pos
                   expf expf_pos expf_zero expf_mono_lt TV0 budget Ha Hb)).
Qed.

(* The sigT packaging on the TV face: the mixing-time modulus witness
   type. *)
Theorem mtc2_mixing_modulus_sigT : forall (TV0 budget : Real)
  (Ha : real_le real_zero TV0) (Hb : real_lt real_zero budget),
  sigT (fun k : nat => real_lt (real_mult (tv_rpow kappa k) TV0) budget).
Proof.
  intros TV0 budget Ha Hb.
  exists (mtc2_mix_step_calc TV0 budget Ha Hb).
  exact (mtc2_mix_step_correct TV0 budget Ha Hb).
Defined.

End Mtc2FaceCalc.

(* ==== The end-to-end Cauchy instance: a calculator reading with no
   expf premises (the double projection of the host corollary) ====

   The expf mini-interface is discharged by the cauchy_real_exp
   carrier (the same construction as the host
   mtc_mixing_time_cauchy_exp): positivity of the temperature
   reciprocal and of the logit diameter alone suffices for the
   calculator to return a step count. *)

Definition mtc2_cauchy_exp_step_calc (invT : Real)
  (HinvT : real_lt real_zero invT) (Delta : Real)
  (HDelta : real_lt real_zero Delta) (TV0 : Real)
  (Ha : real_le real_zero TV0) (budget : Real)
  (Hb : real_lt real_zero budget) : nat :=
  projT1 (mtc_mixing_time_cauchy_exp invT Delta HinvT HDelta TV0 budget Ha Hb).

Theorem mtc2_cauchy_exp_step_correct : forall (invT : Real)
  (HinvT : real_lt real_zero invT) (Delta : Real)
  (HDelta : real_lt real_zero Delta) (TV0 : Real)
  (Ha : real_le real_zero TV0) (budget : Real)
  (Hb : real_lt real_zero budget),
  real_lt (real_mult
             (tv_rpow
                (tv_omd (real_mult
                            (cauchy_real_exp (real_mult invT (real_opp Delta)))
                            (cauchy_real_exp (real_mult invT (real_opp Delta)))))
                (mtc2_cauchy_exp_step_calc invT HinvT Delta HDelta TV0 Ha budget Hb))
             TV0)
          budget.
Proof.
  intros invT HinvT Delta HDelta TV0 Ha budget Hb.
  exact (projT2 (mtc_mixing_time_cauchy_exp invT Delta HinvT HDelta TV0 budget Ha Hb)).
Qed.

(* The sigT packaging on the end-to-end Cauchy face: the mixing-time
   modulus witness type. *)
Theorem mtc2_cauchy_exp_modulus_sigT : forall (invT : Real)
  (HinvT : real_lt real_zero invT) (Delta : Real)
  (HDelta : real_lt real_zero Delta) (TV0 : Real)
  (Ha : real_le real_zero TV0) (budget : Real)
  (Hb : real_lt real_zero budget),
  sigT (fun k : nat =>
    real_lt (real_mult
               (tv_rpow
                  (tv_omd (real_mult
                              (cauchy_real_exp (real_mult invT (real_opp Delta)))
                              (cauchy_real_exp (real_mult invT (real_opp Delta)))))
                  k)
               TV0)
            budget).
Proof.
  intros invT HinvT Delta HDelta TV0 Ha budget Hb.
  exists (mtc2_cauchy_exp_step_calc invT HinvT Delta HDelta TV0 Ha budget Hb).
  exact (mtc2_cauchy_exp_step_correct invT HinvT Delta HDelta TV0 Ha budget Hb).
Defined.

(* ================= Section 4. Audit: the assumption face (Closed
   expected throughout) and the extraction face ================= *)

Print Assumptions mtc2_k_enum_correct.
Print Assumptions mtc2_k_enum_logface.
Print Assumptions mtc2_fuel_sufficient_half.
Print Assumptions mtc2_fuel_sufficient_qbound.
Print Assumptions mtc2_enum_real_correct.
Print Assumptions mtc2_rate_step_calc_correct.
Print Assumptions mtc2_rate_step_compute_correct.
Print Assumptions mtc2_kappa_step_compute_correct.
Print Assumptions mtc2_kappa_modulus_sigT.
Print Assumptions mtc2_mix_step_correct.
Print Assumptions mtc2_mixing_modulus_sigT.
Print Assumptions mtc2_cauchy_exp_step_correct.
Print Assumptions mtc2_cauchy_exp_modulus_sigT.

(* The extraction face: the four nat-face calculators (genuine
   Fixpoints, no stubs, no truncation). *)
Separate Extraction mtc2_ceil_div mtc2_iter mtc2_pow_iter mtc2_k_enum.
