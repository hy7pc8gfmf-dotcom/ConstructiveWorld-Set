(* ========================================================================= *)
(* Module   : abl_dyn_step_calc                                              *)
(* Mission.  An explicit step-count calculator for the entropy-gradient      *)
(*   dynamics rate: from the budget certificate N of the log-modulus         *)
(*   equation log(a*kappa^N) <= log(eps), a := |eta|*|g(x0)|/(1-kappa),      *)
(*   0 < kappa < 1, produce N as nat data.  (1) A calculator projecting the  *)
(*   certified N with its two correctness halves (log budget, Cauchy         *)
(*   modulus) plus a sigT modulus packaging; (2) a combiner from a limit     *)
(*   point and the Cauchy modulus to a rate witness for the distance to      *)
(*   the limit; (3) a fixed-point enumerator for the nat face: for rational  *)
(*   data kappa = p/q (0 < p < q), start a = A, budget eps = E, it returns   *)
(*   the least N with A*p^N <= E*q^N by ceiling-division decay steps and     *)
(*   transfers N to the real face A*(p/q)^N <= E via the nat-to-R            *)
(*   embedding and power laws.                                               *)
(* Dependencies. S01_BaseRing (Id/NatLe/And carriers, NatLe_lift/_drop,      *)
(*   two_pos/half_pos/half_twice, iterate), S02_CauchyComplete, S03_QExp,    *)
(*   S04_RealExpLogConv (iterate_cauchy_explicit_N, r_pow, r_pow_pos,        *)
(*   one_minus_kappa_pos, nat_to_R, natle_of_le), Arch_PA_02; Stdlib         *)
(*   Arith.Arith, Lia.                                                       *)
(* References. S04_RealExpLogConv iterate_cauchy_explicit_N (the projected   *)
(*   budget certificate); S01_BaseRing NatLe := Id (Nat.leb) true carrier.   *)
(* Constructivity. Statement faces are Set-carried: real order on the        *)
(*   interface lt/le : R -> R -> Set, nat order on NatLe, equality on the    *)
(*   Set-level Id, existence on sigT, conjunction on And; zero Prop in       *)
(*   statements.  Constructive Prop reasoning stays inside proof bodies      *)
(*   (lia and stdlib Nat lemmas via NatLe_lift/NatLe_drop); all faces close  *)
(*   Defined (transparent), zero Qed; vm_compute confined to one concrete    *)
(*   numeric pin; extraction units: the four nat Fixpoints.  No Q face.      *)
(* Build. coqc -native-compiler no -q -Q <Set Live root> "" after seeding.  *)
(* ========================================================================= *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import Arch_PA_02.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lia.

(* ============================================================ *)
(* Part 2: nat-face fixed-point enumerator for the modulus        *)
(*   equation.  With kappa = p/q (0 < p < q), start value a = A  *)
(*   and budget eps = E, enumerate the least N satisfying        *)
(*   A * p^N <= E * q^N.  The decay step is the ceiling form of  *)
(*   x |-> x * p / q, so every iterate upper-bounds the exact    *)
(*   geometric value (ceiling division keeps the upper-bound     *)
(*   direction).                                                 *)
(* ============================================================ *)

(* Ceiling division: ceil(a/q) := (a + q - 1) / q for q >= 1. *)
Definition dsc_ceil_div (a q : nat) : nat := Nat.div (a + q - 1) q.

Lemma dsc_ceil_div_le : forall a q, NatLe 1 q -> NatLe a (dsc_ceil_div a q * q).
Proof.
  intros a q Hq. apply NatLe_lift. unfold dsc_ceil_div.
  pose proof (NatLe_drop 1 q Hq) as Hq0.
  pose proof (Nat.div_mod_eq (a + q - 1) q) as Hdm.
  assert (Hne : q <> 0%nat) by lia.
  pose proof (Nat.mod_upper_bound (a + q - 1) q Hne) as Hmb.
  lia.
Defined.

(* Decay step: x |-> ceil(x * p / q), the fixed-point multiply step of kappa = p/q. *)
Definition dsc_iter (p q x : nat) : nat := dsc_ceil_div (x * p) q.

Lemma dsc_iter_step_bound : forall p q x, NatLe 1 q -> NatLe (x * p) (dsc_iter p q x * q).
Proof.
  intros p q x Hq. unfold dsc_iter.
  exact (dsc_ceil_div_le (x * p) q Hq).
Defined.

(* k-fold composition of the decay step (the ceiling face of the geometric decay sequence). *)
Fixpoint dsc_pow_iter (p q x k : nat) : nat :=
  match k with
  | O => x
  | Datatypes.S k' => dsc_iter p q (dsc_pow_iter p q x k')
  end.

(* Composition interchange: iterating k steps from the first iterate is the
   first iterate of the k-step run (the same S+1-fold composition). *)
Lemma dsc_pow_iter_comm : forall p q x k,
  Id (dsc_pow_iter p q (dsc_iter p q x) k) (dsc_iter p q (dsc_pow_iter p q x k)).
Proof.
  intros p q x k. induction k as [| k IH].
  - apply id_refl.
  - change (Id (dsc_iter p q (dsc_pow_iter p q (dsc_iter p q x) k))
                 (dsc_iter p q (dsc_iter p q (dsc_pow_iter p q x k)))).
    exact (id_cong (fun t => dsc_iter p q t) IH).
Defined.

(* Set-level transport of the nat order carrier along a value equality. *)
Lemma dsc_natle_id_cong : forall u v e : nat, Id u v -> NatLe v e -> NatLe u e.
Proof.
  intros u v e Huv Hv. unfold NatLe in *.
  exact (id_trans (id_cong (fun t => Nat.leb t e) Huv) Hv).
Defined.

(* Bounded-fuel enumerator: stop (returning the steps taken) once the
   current value is within budget e; otherwise take one decay step. *)
Fixpoint dsc_k_enum (fuel p q x e : nat) : nat :=
  match fuel with
  | O => O
  | Datatypes.S f =>
      if Nat.leb x e then O else Datatypes.S (dsc_k_enum f p q (dsc_iter p q x) e)
  end.

(* Correctness (ceiling face): whenever the decay sequence reaches the
   budget within the fuel, the enumerator's return value N is a step count
   at which the ceiling iterate is within budget. *)
Theorem dsc_k_enum_correct : forall fuel p q x e,
  sigT (fun k : nat => And (NatLe k fuel) (NatLe (dsc_pow_iter p q x k) e)) ->
  NatLe (dsc_pow_iter p q x (dsc_k_enum fuel p q x e)) e.
Proof.
  intros fuel. induction fuel as [| f IH]; intros p q x e Hreach.
  - destruct Hreach as [k [Hk Hb]].
    pose proof (NatLe_drop k 0 Hk) as Hk0.
    assert (Hkz : k = 0%nat) by lia. subst k.
    simpl. exact Hb.
  - simpl. destruct (Nat.leb x e) eqn:E.
    + exact (NatLe_lift x e (proj1 (Nat.leb_le x e) E)).
    + assert (Hgt : (e < x)%nat) by (apply (proj1 (Nat.leb_gt x e)); exact E).
      destruct Hreach as [k [Hk Hb]].
      destruct k as [| k'].
      * change (NatLe x e) in Hb.
        exfalso. pose proof (NatLe_drop x e Hb) as Hb0. lia.
      * change (NatLe (dsc_iter p q (dsc_pow_iter p q x k')) e) in Hb.
        assert (Hreach' : sigT (fun k0 : nat =>
                          And (NatLe k0 f)
                              (NatLe (dsc_pow_iter p q (dsc_iter p q x) k0) e))).
        { exists k'. split.
          - apply NatLe_lift.
            pose proof (NatLe_drop (Datatypes.S k') (Datatypes.S f) Hk) as Hk0.
            lia.
          - exact (dsc_natle_id_cong _ _ _ (dsc_pow_iter_comm p q x k') Hb). }
        change (NatLe (dsc_iter p q
                        (dsc_pow_iter p q x (dsc_k_enum f p q (dsc_iter p q x) e)))
                   e).
        exact (dsc_natle_id_cong _ _ _
                 (id_sym (dsc_pow_iter_comm p q x
                            (dsc_k_enum f p q (dsc_iter p q x) e)))
                 (IH p q (dsc_iter p q x) e Hreach')).
Defined.

(* Exact-face invariant: the ceiling iterate always covers the exact
   geometric value: x * p^k <= iter^k(x) * q^k. *)
Lemma dsc_pow_iter_exact_ge : forall p q x k,
  NatLe 1 p -> NatLe 1 q -> NatLe (x * p ^ k) (dsc_pow_iter p q x k * q ^ k).
Proof.
  intros p q x k Hp1 Hq1. induction k as [| k IH].
  - simpl. apply NatLe_refl.
  - pose proof (NatLe_drop (x * p ^ k) (dsc_pow_iter p q x k * q ^ k) IH) as IHp.
    pose proof (NatLe_drop (dsc_pow_iter p q x k * p)
                  (dsc_iter p q (dsc_pow_iter p q x k) * q)
                  (dsc_iter_step_bound p q (dsc_pow_iter p q x k) Hq1)) as Hstep.
    apply NatLe_lift. simpl.
    apply (Nat.le_trans _ (dsc_pow_iter p q x k * q ^ k * p)).
    + rewrite (Nat.mul_comm p (p ^ k)).
      rewrite (Nat.mul_assoc x (p ^ k) p).
      apply (Nat.mul_le_mono_r _ _ p). exact IHp.
    + rewrite <- (Nat.mul_assoc (dsc_pow_iter p q x k) (q ^ k) p).
      rewrite (Nat.mul_comm (q ^ k) p).
      rewrite (Nat.mul_assoc (dsc_pow_iter p q x k) p (q ^ k)).
      apply (Nat.le_trans _ (dsc_iter p q (dsc_pow_iter p q x k) * q * q ^ k)).
      * apply (Nat.mul_le_mono_r _ _ (q ^ k)). exact Hstep.
      * rewrite (Nat.mul_assoc (dsc_iter p q (dsc_pow_iter p q x k)) q (q ^ k)).
        apply (Nat.le_refl _).
Defined.

(* The nat face of the log-modulus equation: once the enumerator terminates
   within the fuel, its N satisfies x * p^N <= e * q^N. *)
Theorem dsc_k_enum_logface : forall fuel p q x e,
  NatLe 1 p -> NatLe 1 q ->
  sigT (fun k : nat => And (NatLe k fuel) (NatLe (dsc_pow_iter p q x k) e)) ->
  NatLe (x * p ^ dsc_k_enum fuel p q x e) (e * q ^ dsc_k_enum fuel p q x e).
Proof.
  intros fuel p q x e Hp1 Hq1 Hterm.
  pose proof (NatLe_drop (dsc_pow_iter p q x (dsc_k_enum fuel p q x e)) e
                (dsc_k_enum_correct fuel p q x e Hterm)) as H1.
  pose proof (NatLe_drop (x * p ^ dsc_k_enum fuel p q x e)
                (dsc_pow_iter p q x (dsc_k_enum fuel p q x e)
                   * q ^ dsc_k_enum fuel p q x e)
                (dsc_pow_iter_exact_ge p q x (dsc_k_enum fuel p q x e) Hp1 Hq1)) as H2.
  apply NatLe_lift.
  apply (Nat.le_trans _
           (dsc_pow_iter p q x (dsc_k_enum fuel p q x e)
              * q ^ dsc_k_enum fuel p q x e)).
  - exact H2.
  - apply (Nat.mul_le_mono_r _ _ (q ^ dsc_k_enum fuel p q x e)). exact H1.
Defined.

(* Numeric pin (smoke face): kappa = 7/10, a = 1000, eps = 10. *)
Eval vm_compute in (dsc_k_enum 50 7 10 1000 10).

(* ============================================================ *)
(* Part 1 + Part 3: the real face.  A generic section over the    *)
(*   real-number interface mirrors the S04 convergence section:   *)
(*   the calculator projects the certified step count, the two    *)
(*   correctness halves read the budget certificate, and the      *)
(*   fixed-point enumerator is transferred to the real face on    *)
(*   concrete rational data.                                      *)
(* ============================================================ *)

Section DscDynStepCalc.

Context {RI : RealInterfaceEnhanced}.

(* Unpack the interface fields (same shape as the S04 convergence section). *)
Let R := @R RI.
Let zero := @zero RI.
Let one := @one RI.
Let plus := @plus RI.
Let mult := @mult RI.
Let opp := @opp RI.
Let abs := @abs RI.
Let lt := @lt RI.
Let le := @le RI.
Let minus := @minus RI.
Let lim := @lim RI.
Let metric := @metric RI.

(* Honest-interface certificates (mirroring the S04 convergence section). *)
Variable entropy_gradient : R -> R.
Variable dynamics : R -> R.
Variable eta : R.
Variable dynamics_gradient_step : forall x : R,
  Id (dynamics x) (plus x (mult eta (entropy_gradient x))).
Variable metric_abs : forall a b : R, Id (metric a b) (abs (minus a b)).
Variable kappa : R.
Variable kappa_pos : lt zero kappa.
Variable kappa_lt_one : lt kappa one.
Variable gradient_abs_decay : forall (E_A : R) (n : nat),
  le (abs (entropy_gradient (iterate dynamics (Datatypes.S n) E_A)))
     (mult kappa (abs (entropy_gradient (iterate dynamics n E_A)))).
Variable lt_plus_compat_lt_le : forall a b c d : R, lt a b -> le c d -> lt (plus a c) (plus b d).
Variable r_arch_pow : forall (a : R), lt zero a -> forall eps : R, lt zero eps ->
  sigT (fun n : nat => lt (mult a (r_pow kappa n)) eps).
Variable eta_abs_pos : lt zero (abs eta).
Variable log_lt_mono_cc : forall a b : R, lt zero a -> lt zero b -> lt a b -> lt (log a) (log b).

(* ===== Part 1: the step-count calculator and its correctness halves ===== *)

Definition dsc_step_calc (E_A : R)
  (Hg0 : lt zero (abs (entropy_gradient (iterate dynamics 0 E_A))))
  (eps : R) (Heps : lt zero eps) : nat :=
  projT1 (@iterate_cauchy_explicit_N RI entropy_gradient dynamics eta
            dynamics_gradient_step metric_abs kappa kappa_pos kappa_lt_one
            gradient_abs_decay lt_plus_compat_lt_le r_arch_pow eta_abs_pos
            log_lt_mono_cc E_A Hg0 eps Heps).

(* Correctness half 1: the log-budget face log(a * kappa^N) <= log eps
   at the calculator's reading N. *)
Theorem dsc_step_calc_log_budget : forall (E_A : R)
  (Hg0 : lt zero (abs (entropy_gradient (iterate dynamics 0 E_A))))
  (eps : R) (Heps : lt zero eps),
  le (log (mult
        (mult (mult (abs eta)
                    (abs (entropy_gradient (iterate dynamics 0 E_A))))
              (inv_pos (minus one kappa)
                       (one_minus_kappa_pos kappa kappa_lt_one lt_plus_compat_lt_le)))
        (r_pow kappa (dsc_step_calc E_A Hg0 eps Heps))))
     (log eps).
Proof.
  intros E_A Hg0 eps Heps.
  exact (fst (@projT2 _ _
          (@iterate_cauchy_explicit_N RI entropy_gradient dynamics eta
             dynamics_gradient_step metric_abs kappa kappa_pos kappa_lt_one
             gradient_abs_decay lt_plus_compat_lt_le r_arch_pow eta_abs_pos
             log_lt_mono_cc E_A Hg0 eps Heps))).
Defined.

(* Correctness half 2: the Cauchy face -- for all m, n >= N the iterates
   are within eps in the metric (order certificates on the decidable
   nat carrier). *)
Theorem dsc_step_calc_cauchy_correct : forall (E_A : R)
  (Hg0 : lt zero (abs (entropy_gradient (iterate dynamics 0 E_A))))
  (eps : R) (Heps : lt zero eps) (m n : nat),
  NatLe (dsc_step_calc E_A Hg0 eps Heps) m ->
  NatLe (dsc_step_calc E_A Hg0 eps Heps) n ->
  lt (metric (iterate dynamics m E_A) (iterate dynamics n E_A)) eps.
Proof.
  intros E_A Hg0 eps Heps m n Hm Hn.
  exact (snd (@projT2 _ _
          (@iterate_cauchy_explicit_N RI entropy_gradient dynamics eta
             dynamics_gradient_step metric_abs kappa kappa_pos kappa_lt_one
             gradient_abs_decay lt_plus_compat_lt_le r_arch_pow eta_abs_pos
             log_lt_mono_cc E_A Hg0 eps Heps)) m n Hm Hn).
Defined.

(* sigT packaging: {N | for all m, n >= N, metric(x_m, x_n) < eps}. *)
Theorem dsc_cauchy_modulus_sigT : forall (E_A : R)
  (Hg0 : lt zero (abs (entropy_gradient (iterate dynamics 0 E_A))))
  (eps : R) (Heps : lt zero eps),
  sigT (fun N : nat => forall m n : nat, NatLe N m -> NatLe N n ->
        lt (metric (iterate dynamics m E_A) (iterate dynamics n E_A)) eps).
Proof.
  intros E_A Hg0 eps Heps.
  exists (dsc_step_calc E_A Hg0 eps Heps).
  exact (dsc_step_calc_cauchy_correct E_A Hg0 eps Heps).
Defined.

(* ===== Rate combiner: limit point + Cauchy modulus imply a rate witness
   for the distance to the limit (eps/2 + eps/2 <= eps). ===== *)

Theorem dsc_limit_rate_witness : forall (E_A : R)
  (Hg0 : lt zero (abs (entropy_gradient (iterate dynamics 0 E_A))))
  (E_star : R)
  (Hlim : lim (fun n => iterate dynamics n E_A) E_star)
  (Happrox : forall eps : R, lt zero eps ->
              sigT (fun N : nat => forall n : nat, NatLe N n ->
                    lt (metric (iterate dynamics n E_A) E_star) eps))
  (eps : R), lt zero eps ->
  sigT (fun N : nat => forall n : nat, NatLe N n ->
        lt (metric (iterate dynamics n E_A) E_star) eps).
Proof.
  intros E_A Hg0 E_star Hlim Happrox eps Heps.
  pose (eps2 := mult (inv_pos (plus one one) two_pos) eps).
  assert (Heps2 : lt zero eps2) by exact (half_pos eps Heps).
  destruct (Happrox eps2 Heps2) as [N1 HN1].
  destruct (dsc_cauchy_modulus_sigT E_A Hg0 eps2 Heps2) as [N2 HN2].
  exists (Nat.max N1 N2).
  intros n Hn.
  assert (Hn2n : NatLe N2 n)
    by (apply NatLe_lift;
        pose proof (NatLe_drop (Nat.max N1 N2) n Hn); lia).
  apply (lt_id_r _ (plus eps2 eps2) eps (half_twice eps)).
  apply (le_lt_trans _
           (plus (metric (iterate dynamics n E_A)
                          (iterate dynamics (Nat.max N1 N2) E_A))
                 (metric (iterate dynamics (Nat.max N1 N2) E_A) E_star))).
  - exact (metric_triangle (iterate dynamics n E_A)
             (iterate dynamics (Nat.max N1 N2) E_A) E_star).
  - exact (lt_plus_compat _ _ _ _
              (HN2 n (Nat.max N1 N2) Hn2n
                 (natle_of_le N2 (Nat.max N1 N2) (Nat.le_max_r N1 N2)))
              (HN1 (Nat.max N1 N2)
                 (natle_of_le N1 (Nat.max N1 N2) (Nat.le_max_l N1 N2)))).
Defined.

(* ===== Part 3: real-face bridges for the fixed-point calculator ===== *)

(* Left unit law (one Id step). *)
Lemma dsc_mult_one_l : forall t : R, Id (mult one t) t.
Proof.
  intros t. apply (id_trans (mult_comm one t)). apply (mult_one t).
Defined.

(* Inverse uniqueness: y * z == 1 implies z == inv y. *)
Lemma dsc_inv_unique : forall (y z : R) (Hy : lt zero y),
  Id (mult y z) one -> Id z (inv_pos y Hy).
Proof.
  intros y z Hy Hz.
  exact (id_trans (id_sym (mult_one z))
         (id_trans (id_cong (fun t => mult z t) (id_sym (inv_pos_correct y Hy)))
         (id_trans (mult_assoc z y (inv_pos y Hy))
         (id_trans (id_cong (fun t => mult t (inv_pos y Hy)) (mult_comm z y))
         (id_trans (id_cong (fun t => mult t (inv_pos y Hy)) Hz)
         (dsc_mult_one_l (inv_pos y Hy))))))).
Defined.

(* Powers split over multiplication: r_pow(a*b, n) == r_pow(a,n) * r_pow(b,n)
   (absent from the library; supplied here; the Id face is handled in
   term mode end to end). *)
Lemma dsc_r_pow_mult : forall (a b : R) (n : nat),
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
             (id_trans (id_cong (fun t => mult a t)
                                (id_sym (mult_assoc (r_pow a n) b (r_pow b n))))
                       (mult_assoc a (r_pow a n) (mult b (r_pow b n)))))))).
Defined.

(* The embedding and powers: r_pow(nat_to_R k, n) == nat_to_R(k^n)
   (multiplicative homomorphism by induction). *)
Lemma dsc_nat_r_pow : forall k n : nat,
  Id (r_pow (nat_to_R k) n) (nat_to_R (k ^ n)%nat).
Proof.
  intros k n. induction n as [| n IH].
  - exact (id_sym (plus_zero one)).
  - exact (id_trans
             (id_cong (fun t => mult (nat_to_R k) t) IH)
             (id_sym (nat_to_R_mult_hom k (k ^ n)%nat))).
Defined.

(* Powers split over inverses: r_pow(inv x, n) == inv(r_pow x, n)
   (by inverse uniqueness; the positivity certificate Hp is an explicit
   slot so no opaque constant blocks the Id rewriting). *)
Lemma dsc_r_pow_inv : forall (x : R) (Hx : lt zero x) (n : nat) (Hp : lt zero (r_pow x n)),
  Id (r_pow (inv_pos x Hx) n) (inv_pos (r_pow x n) Hp).
Proof.
  intros x Hx n. induction n as [| n IH]; intros Hp.
  - exact (id_sym (id_trans (id_sym (dsc_mult_one_l (inv_pos one Hp)))
                            (inv_pos_correct one Hp))).
  - specialize (IH (r_pow_pos x n Hx)).
    exact (id_trans
             (id_cong (fun t => mult (inv_pos x Hx) t) IH)
             (dsc_inv_unique (mult x (r_pow x n))
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
Defined.

(* Embedding monotonicity bridge: m <= n in nat gives nat_to_R m <= nat_to_R n.
   Elimination discipline: the nat order is consumed only through the
   decidable NatLe carrier; the proof body runs a nat addition helper and
   the boolean comparison, with no Prop elimination into the Set goal. *)
Lemma dsc_nat_le_plus_aux : forall n m : nat, le (nat_to_R m) (nat_to_R (n + m)%nat).
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
Defined.

Lemma dsc_nat_le_embed : forall m n : nat, NatLe m n -> le (nat_to_R m) (nat_to_R n).
Proof.
  intros m n Hmn. pose proof (NatLe_drop m n Hmn) as Hmn0.
  destruct (Nat.leb n m) eqn:E.
  - assert (Heq : n = m%nat).
    { apply (Nat.le_antisymm n m).
      - exact (proj1 (Nat.leb_le n m) E).
      - exact Hmn0. }
    rewrite Heq. apply le_refl.
  - destruct n as [| n'].
    + assert (Hc : (m < 0)%nat) by (apply (proj1 (Nat.leb_gt 0 m)); exact E).
      destruct (Nat.nlt_0_r m Hc).
    + assert (Hlt : (m < Datatypes.S n')%nat)
        by (apply (proj1 (Nat.leb_gt (Datatypes.S n') m)); exact E).
      assert (Hmn' : (m <= n')%nat) by (apply (proj1 (Nat.lt_succ_r m n')); exact Hlt).
      replace (Datatypes.S n')%nat with ((Datatypes.S (n' - m)) + m)%nat by lia.
      apply (dsc_nat_le_plus_aux (Datatypes.S (n' - m)) m).
Defined.

(* Main fixed-point face: on rational data kappa := p/q, a := A, eps := E,
   the enumerated N satisfies a * (p/q)^N <= eps as a real le (a Set-faced
   statement; the certificate-free dual of the Part 1 calculator). *)
Theorem dsc_enum_real_correct : forall (fuel p q A E : nat)
  (Hqr : lt zero (nat_to_R q)),
  NatLe 1 p -> NatLe 1 q -> NatLe 1 A -> NatLe 1 E ->
  sigT (fun k : nat => And (NatLe k fuel) (NatLe (dsc_pow_iter p q A k) E)) ->
  le (mult (nat_to_R A)
            (r_pow (mult (nat_to_R p) (inv_pos (nat_to_R q) Hqr))
                   (dsc_k_enum fuel p q A E)))
     (nat_to_R E).
Proof.
  intros fuel p q A E Hqr Hp1 Hq1 HA1 HE1 Hterm.
  set (N := dsc_k_enum fuel p q A E).
  set (w := inv_pos (r_pow (nat_to_R q) N) (r_pow_pos (nat_to_R q) N Hqr)).
  pose proof (dsc_nat_le_embed (A * p ^ N) (E * q ^ N)
                (dsc_k_enum_logface fuel p q A E Hp1 Hq1 Hterm)) as Hemb.
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
  { pose proof (dsc_r_pow_mult (nat_to_R p) (inv_pos (nat_to_R q) Hqr) N) as Hpm.
    pose proof (dsc_nat_r_pow p N) as Hpo.
    pose proof (dsc_r_pow_inv (nat_to_R q) Hqr N (r_pow_pos (nat_to_R q) N Hqr)) as Hpi.
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
                                     (id_sym (dsc_nat_r_pow q N)))
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
Defined.

End DscDynStepCalc.

(* ============================================================ *)
(* Assumption audit: one Print Assumptions per theorem (all       *)
(* expected to report the closed global context).                 *)
(* ============================================================ *)

Print Assumptions dsc_step_calc_log_budget.
Print Assumptions dsc_step_calc_cauchy_correct.
Print Assumptions dsc_cauchy_modulus_sigT.
Print Assumptions dsc_limit_rate_witness.
Print Assumptions dsc_ceil_div_le.
Print Assumptions dsc_iter_step_bound.
Print Assumptions dsc_pow_iter_comm.
Print Assumptions dsc_natle_id_cong.
Print Assumptions dsc_k_enum_correct.
Print Assumptions dsc_pow_iter_exact_ge.
Print Assumptions dsc_k_enum_logface.
Print Assumptions dsc_mult_one_l.
Print Assumptions dsc_inv_unique.
Print Assumptions dsc_r_pow_mult.
Print Assumptions dsc_nat_r_pow.
Print Assumptions dsc_r_pow_inv.
Print Assumptions dsc_nat_le_plus_aux.
Print Assumptions dsc_nat_le_embed.
Print Assumptions dsc_enum_real_correct.

(* Extraction units: the four nat Fixpoint faces of the calculator. *)
Separate Extraction dsc_ceil_div dsc_iter dsc_pow_iter dsc_k_enum.
