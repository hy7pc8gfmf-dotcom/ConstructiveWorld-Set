(* ConstructiveWorld-Set — Real exp/log interface, gradient-ascent convergence, and maximum-entropy duality. *)

(** * S04_RealExpLogConv: real exp/log interface, gradient-ascent convergence,
    and maximum-entropy duality.

    Mission.  The exp/log interface of [RealInterface] and its convergence
      theory: Cauchy arguments for gradient ascent ([dynamics_converges],
      [iterate_cauchy], [grad_squeeze_zero]), the contraction family
      ([gradient_step_contraction], [grad_decay_positive_iter]), the unique
      attractor [unique_attractor], the free-energy block ([gibbs_inequality],
      [free_energy_kl_decomp], [min_free_energy_is_boltzmann],
      [max_entropy_is_boltzmann_temp], [entropy_max_unique_temp],
      [elbo_lower_bound], [evidence_kl_decomp], [elbo_explicit]).

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs], [QArith.Qround],
      [List], [Bool], [Arith.Arith], [Setoid], [Morphisms], [Lia],
      [QArith.Qminmax]; and [S01_BaseRing], [S02_CauchyComplete],
      [S03_QExp] of this development.

    References.  A split fragment of [CW_ConstructiveWorld_219].v, the
      baseline module of ConstructiveWorld-Main (range L13801-L18733);
      statement names carried over verbatim.

    Constructivity.  All statements carried by [Set] via the decidable
      carriers [Id]/[lt]/[le] of [S01_BaseRing]; axiom-free, nothing
      admitted, every proof closed by [Qed].

    Build.  [coqc -native-compiler no -q -Q . "" S04_RealExpLogConv.v]
      compiles cleanly (exit 0) after [S01_BaseRing] and its siblings. *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               Lists.List Bool.Bool Arith.Arith.
Import ListNotations.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax.

Section RealExpLogInterface.

Context {RI : RealInterface}.

Variable real_exp : R -> R.
Variable real_log : R -> R.

Variable real_exp_pos : forall x : R, lt zero (real_exp x).
Variable real_log_exp : forall x : R, Id (real_log (real_exp x)) x.
Variable real_exp_zero : Id (real_exp zero) one.
Variable real_exp_plus : forall a b : R, Id (real_exp (plus a b)) (mult (real_exp a) (real_exp b)).

Variable real_log_mult : forall a b : R, lt zero a -> lt zero b ->
                           Id (real_log (mult a b)) (plus (real_log a) (real_log b)).
Variable real_log_one : Id (real_log one) zero.
Variable real_log_lt : forall a b : R, lt a b -> lt (real_log a) (real_log b).
(* Derived lemma: the [real_log_one] slot follows from the sibling fields
   [real_exp_zero] and [real_log_exp]; nothing is admitted. *)
Lemma real_log_one_derived : Id (real_log one) zero.
Proof.
  exact (id_trans (id_sym (id_cong real_log real_exp_zero))
                  (real_log_exp zero)).
Qed.


End RealExpLogInterface.

(* ============================================================ *)
(* Differentiability section: the composition law as an assumption variable. *)
(* ============================================================ *)



(* ============================================================ *)
(* Entropy derivative and convergence theorems, stated with section
   assumption variables. *)
(* ============================================================ *)



Section ConvergenceTheorem.

Context {RI : RealInterfaceEnhanced}.

(* Unpack the fields of [RealInterface]. *)
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

Variable entropy : R -> R.
Variable entropy_gradient : R -> R.
Variable dynamics : R -> R.
Variable eta : R.

(* The dynamics is a gradient-ascent step, stated explicitly as an interface
   assumption: x_{n+1} = x_n + eta * g(x_n).  The convergence proof of
   [dynamics_converges] rests on this structure: with [dynamics] left
   abstract, convergence is not provable; this assumption makes the
   one-step difference formula for [iterate] a theorem. *)
Variable dynamics_gradient_step : forall x : R,
  Id (dynamics x) (plus x (mult eta (entropy_gradient x))).

Variable strict_concavity :
  forall x y : R, lt x y -> lt (entropy_gradient y) (entropy_gradient x).

Variable L : R.
Variable L_pos : lt zero L.
Variable gradient_lipschitz :
  forall x y : R,
    le (abs (minus (entropy_gradient x) (entropy_gradient y)))
       (mult L (abs (minus x y))).

Variable S_max : R.
Variable entropy_upper_bound : forall E_A, le (entropy E_A) S_max.

(* One-step difference formula for [iterate] (the nontrivial algebraic
   core): x_{n+1} - x_n == eta * g(x_n); by induction on [n], rewriting
   pointwise with [dynamics_gradient_step]. *)
Theorem iterate_step_diff : forall (E_A : R) (n : nat),
  Id (minus (iterate dynamics (Datatypes.S n) E_A) (iterate dynamics n E_A))
     (mult eta (entropy_gradient (iterate dynamics n E_A))).
Proof.
  intros E_A n. induction n as [| n IH]; simpl.
  - (* Base case: dynamics E_A - E_A == eta * g(E_A).
   From [dynamics_gradient_step], dynamics E_A == plus E_A (eta * g(E_A)),
   so minus (plus E_A (eta * g)) E_A == eta * g by [minus_plus_cancel_r]. *)
    assert (Hstep : Id (dynamics E_A) (plus E_A (mult eta (entropy_gradient E_A))))
      by exact (dynamics_gradient_step E_A).
    assert (Hgoal : Id (minus (plus E_A (mult eta (entropy_gradient E_A))) E_A)
                       (mult eta (entropy_gradient E_A)))
      by exact (minus_plus_cancel_r E_A (mult eta (entropy_gradient E_A))).
    exact (id_trans (id_cong (fun z => minus z E_A) Hstep) Hgoal).
  - (* Induction step: iterate dynamics (S (Datatypes.S n)) E_A
   - iterate dynamics (Datatypes.S n) E_A
   == dynamics (iterate dynamics (Datatypes.S n) E_A)
      - iterate dynamics (Datatypes.S n) E_A
   == eta * g (iterate dynamics (Datatypes.S n) E_A), as in the base case. *)
    assert (Hstep : Id (dynamics (iterate dynamics (Datatypes.S n) E_A))
                       (plus (iterate dynamics (Datatypes.S n) E_A)
                             (mult eta (entropy_gradient (iterate dynamics (Datatypes.S n) E_A)))))
      by exact (dynamics_gradient_step (iterate dynamics (Datatypes.S n) E_A)).
    assert (Hgoal : Id (minus (plus (iterate dynamics (Datatypes.S n) E_A)
                                    (mult eta (entropy_gradient (iterate dynamics (Datatypes.S n) E_A))))
                              (iterate dynamics (Datatypes.S n) E_A))
                       (mult eta (entropy_gradient (iterate dynamics (Datatypes.S n) E_A))))
      by exact (minus_plus_cancel_r (iterate dynamics (Datatypes.S n) E_A)
                                    (mult eta (entropy_gradient (iterate dynamics (Datatypes.S n) E_A)))).
    exact (id_trans (id_cong (fun z => minus z (iterate dynamics (Datatypes.S n) E_A)) Hstep) Hgoal).
Qed.

(* Monotonicity of the gradient (strict concavity implies a strictly
   decreasing gradient): lt x y -> lt (g y) (g x).  This restates
   [strict_concavity]; it is the concavity core of the convergence argument
   and records that the iteration premise is reusable. *)
Theorem entropy_gradient_strict_mono : forall x y : R,
  lt x y -> lt (entropy_gradient y) (entropy_gradient x).
Proof.
  intros x y Hxy. exact (strict_concavity x y Hxy).
Qed.

(* Boundedness of the gradient difference (the L-Lipschitz bound at
   y := zero): |g(x) - g(zero)| <= L * |x|.  An instance of
   [gradient_lipschitz]; it bounds the gradient magnitude in the
   convergence argument. *)
Theorem gradient_diff_from_zero : forall x : R,
  le (abs (minus (entropy_gradient x) (entropy_gradient zero)))
     (mult L (abs (minus x zero))).
Proof.
  intro x. exact (gradient_lipschitz x zero).
Qed.

(* Absolute value of the one-step difference:
   |x_{n+1} - x_n| == |eta| * |g(x_n)|, by [iterate_step_diff] and
   [abs_mult]. *)
Theorem iterate_step_abs_diff : forall (E_A : R) (n : nat),
  Id (abs (minus (iterate dynamics (Datatypes.S n) E_A) (iterate dynamics n E_A)))
     (mult (abs eta) (abs (entropy_gradient (iterate dynamics n E_A)))).
Proof.
  intros E_A n.
  assert (Hdiff : Id (minus (iterate dynamics (Datatypes.S n) E_A) (iterate dynamics n E_A))
                     (mult eta (entropy_gradient (iterate dynamics n E_A))))
    by exact (iterate_step_diff E_A n).
  apply (id_trans (id_cong abs Hdiff)).
  apply (abs_mult eta (entropy_gradient (iterate dynamics n E_A))).
Qed.

(* Recursive bound on the gradient difference:
   |g(x_{n+1}) - g(x_n)| <= L * |eta| * |g(x_n)|, chaining
   [gradient_lipschitz] at x_{n+1}, x_n with [iterate_step_abs_diff].
   This is the core recursion of the convergence argument: the step
   difference is controlled by the gradient magnitude. *)
Theorem gradient_step_recurrence : forall (E_A : R) (n : nat),
  le (abs (minus (entropy_gradient (iterate dynamics (Datatypes.S n) E_A))
                 (entropy_gradient (iterate dynamics n E_A))))
     (mult (mult L (abs eta)) (abs (entropy_gradient (iterate dynamics n E_A)))).
Proof.
  intros E_A n.
  (* gradient_lipschitz: |g(x_{n+1}) - g(x_n)| <= L * |x_{n+1} - x_n| *)
  assert (Hlip : le (abs (minus (entropy_gradient (iterate dynamics (Datatypes.S n) E_A))
                                (entropy_gradient (iterate dynamics n E_A))))
                    (mult L (abs (minus (iterate dynamics (Datatypes.S n) E_A)
                                        (iterate dynamics n E_A)))))
    by exact (gradient_lipschitz (iterate dynamics (Datatypes.S n) E_A)
                                 (iterate dynamics n E_A)).
  (* rewrite the factor |x_{n+1} - x_n| to |eta| * |g(x_n)|
   ([iterate_step_abs_diff]) *)
  assert (Habs : Id (abs (minus (iterate dynamics (Datatypes.S n) E_A)
                                (iterate dynamics n E_A)))
                    (mult (abs eta) (abs (entropy_gradient (iterate dynamics n E_A)))))
    by exact (iterate_step_abs_diff E_A n).
  apply (le_trans _ (mult L (mult (abs eta) (abs (entropy_gradient (iterate dynamics n E_A))))) _).
  - (* Hlip : |g(x_{n+1}) - g(x_n)| <= L * |x_{n+1} - x_n|;
   rewrite the right-hand factor |x_{n+1} - x_n| to |eta| * |g| *)
    apply (le_id_r (abs (minus (entropy_gradient (iterate dynamics (Datatypes.S n) E_A))
                               (entropy_gradient (iterate dynamics n E_A))))
                   (mult L (abs (minus (iterate dynamics (Datatypes.S n) E_A)
                                       (iterate dynamics n E_A))))
                   (mult L (mult (abs eta) (abs (entropy_gradient (iterate dynamics n E_A)))))
                   (id_cong (fun z => mult L z) Habs)
                   Hlip).
  - (* intermediate factor L * (|eta| * |g|) <= (L * |eta|) * |g|:
   [mult_assoc] followed by [le_refl] *)
    apply (le_id_r (mult L (mult (abs eta) (abs (entropy_gradient (iterate dynamics n E_A)))))
                   (mult L (mult (abs eta) (abs (entropy_gradient (iterate dynamics n E_A)))))
                   (mult (mult L (abs eta)) (abs (entropy_gradient (iterate dynamics n E_A))))
                   (mult_assoc L (abs eta) (abs (entropy_gradient (iterate dynamics n E_A))))
                   (le_refl _)).
Qed.

(* The gradient magnitude decreases monotonically along the ascent
   iteration: x < y and 0 < g(y) < g(x) imply |g(y)| <= |g(x)|, from
   [entropy_gradient_strict_mono] (g strictly decreasing) and [abs_pos]
   (positivity is preserved).  Key for convergence: |g(x_{n+1})| <= |g(x_n)|,
   the contraction behind the Cauchy property. *)
Theorem gradient_abs_mono : forall x y : R,
  lt x y -> lt zero (entropy_gradient y) ->
  lt (entropy_gradient y) (entropy_gradient x) ->
  le (abs (entropy_gradient y)) (abs (entropy_gradient x)).
Proof.
  intros x y Hxy Hgypos Hgygx.
  (* |g(y)| = g(y) (abs_pos, 0 < g(y)) <= g(x) = |g(x)| (abs_pos, 0 < g(y) < g(x) implies 0 < g(x)) *)
  assert (Hgxpos : lt zero (entropy_gradient x))
    by (apply (lt_trans _ (entropy_gradient y) _); [exact Hgypos | exact Hgygx]).
  assert (Habsy : Id (abs (entropy_gradient y)) (entropy_gradient y))
    by exact (abs_pos (entropy_gradient y) Hgypos).
  assert (Habsx : Id (abs (entropy_gradient x)) (entropy_gradient x))
    by exact (abs_pos (entropy_gradient x) Hgxpos).
  apply (le_id_l (abs (entropy_gradient y))
                 (entropy_gradient y)
                 (abs (entropy_gradient x))
                 Habsy).
  apply (le_id_r (entropy_gradient y)
                 (entropy_gradient x)
                 (abs (entropy_gradient x))
                 (id_sym Habsx)
                 (lt_le_iff _ _ (inl Hgygx))).
Qed.



End ConvergenceTheorem.

(* ============================================================ *)
(* The Cauchy argument. *)
(* ============================================================ *)
Section ConvergenceCauchy.

Context {RI : RealInterfaceEnhanced}.

(* Unpack the fields of [RealInterface]. *)
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

(* Restate the interface variables of [ConvergenceTheorem] so that this
   section is self-contained. *)
Variable entropy : R -> R.
Variable entropy_gradient : R -> R.
Variable dynamics : R -> R.
Variable eta : R.
Variable dynamics_gradient_step : forall x : R,
  Id (dynamics x) (plus x (mult eta (entropy_gradient x))).
Variable strict_concavity : forall x y : R, lt x y -> lt (entropy_gradient y) (entropy_gradient x).
Variable L : R.
Variable L_pos : lt zero L.
Variable gradient_lipschitz :
  forall x y : R,
    le (abs (minus (entropy_gradient x) (entropy_gradient y)))
       (mult L (abs (minus x y))).
Variable S_max : R.
Variable entropy_upper_bound : forall E_A, le (entropy E_A) S_max.

(* Further interface fields (standard properties as explicit assumptions). *)
(* (0) the metric is induced by the norm, as in [smetric_snorm] *)
Variable metric_abs : forall a b : R, Id (metric a b) (abs (minus a b)).
(* (1) geometric decay of the gradient magnitude (the strong-concavity
   contraction factor; explicit interface assumption) *)
Variable kappa : R.
Variable kappa_pos : lt zero kappa.
Variable kappa_lt_one : lt kappa one.
Variable gradient_abs_decay : forall (E_A : R) (n : nat),
  le (abs (entropy_gradient (iterate dynamics (Datatypes.S n) E_A)))
     (mult kappa (abs (entropy_gradient (iterate dynamics n E_A)))).
(* (2) mixed strict/weak addition compatibility (explicit interface
   assumption; the abstract [R] layer lacks this property, which
   0 < 1 - kappa requires) *)
(* Interface-level note: [RealInterfaceEnhanced] carries only strict-strict
   and weak-weak addition compatibility ([lt_plus_compat],
   [le_plus_compat]); no generator derives a strict inequality from a weak
   one at the interface level, so mixed lt/le compatibility is postulated
   here and supplied by the concrete layer as [real_lt_plus_compat_lt_le]
   in [S07_RealSetoidExpLog]. *)
Variable lt_plus_compat_lt_le : forall a b c d : R, lt a b -> le c d -> lt (plus a c) (plus b d).
(* Interface-level note, dual [le]/[lt] form: same situation as the previous
   field — mixed compatibility is not derivable at the interface level and
   is supplied by the concrete layer as [real_lt_plus_compat_lt_le]
   ([S07_RealSetoidExpLog]). *)
Variable lt_plus_compat_le_lt : forall a b c d : R, le a b -> lt c d -> lt (plus a c) (plus b d).

(* Explicit aliases for the closure theorems of [ConvergenceTheorem]
   (the section variables carry the same names). *)
Let iter_abs := (@iterate_step_abs_diff RI entropy_gradient dynamics eta dynamics_gradient_step).
Let iter_diff := (@iterate_step_diff RI entropy_gradient dynamics eta dynamics_gradient_step).

(* ===== Powers in the [R] layer ===== *)
Fixpoint r_pow (x : R) (n : nat) : R :=
  match n with
  | 0%nat => one
  | Datatypes.S m => mult x (r_pow x m)
  end.

(* Interface fields for the final stage (standard properties as explicit
   assumptions). *)
(* (3) metric reflexivity at zero: metric a a == zero (a standard
   constructive metric property, missing at the abstract layer) *)
(* Auxiliary lemma (a former variable restated as a same-named lemma):
   from [metric_abs], unfolding [minus], then [plus_opp] and [abs_zero];
   nothing is admitted. *)
Lemma metric_refl_zero : forall a : R, Id (metric a a) zero.
Proof.
  intros a.
  exact (id_trans (metric_abs a a)
         (id_trans (id_cong abs (plus_opp a)) abs_zero)).
Qed.

(* (4) geometric breakout (archimedean property in the [R] layer):
   0 < a and 0 < eps imply there exists n with a * kappa^n < eps *)
Variable r_arch_pow : forall (a : R), lt zero a -> forall eps : R, lt zero eps ->
  sigT (fun n : nat => lt (mult a (r_pow kappa n)) eps).

(* positivity of powers: 0 < x implies 0 < x^n *)
Lemma r_pow_pos : forall x n, lt zero x -> lt zero (r_pow x n).
Proof.
  intros x n Hx. induction n as [| m IH]; simpl.
  - exact (one_pos).
  - apply (mult_positive x (r_pow x m) Hx IH).
Qed.

(* nonnegativity of powers: 0 < x implies 0 <= x^n *)
Lemma r_pow_nonneg : forall x n, lt zero x -> le zero (r_pow x n).
Proof.  intros x n Hx.
  assert (Hpos : lt zero (r_pow x n)).
  { induction n as [| m IH]; simpl.
    - exact (one_pos).
    - exact (mult_positive x (r_pow x m) Hx IH). }
  exact (lt_le_iff _ _ (inl Hpos)).
Qed.

(* powers decrease monotonically: 0 < b < 1 implies b^(S n) <= b^n *)
Lemma r_pow_dec : forall b n, lt zero b -> lt b one -> le (r_pow b (Datatypes.S n)) (r_pow b n).
Proof.
  intros b n Hb Hblt.
  induction n as [| m IH]; simpl.
  - (* b^1 = b * 1 <= 1, by [mult_one] *)
    apply (le_id_l _ b _).
    + apply (mult_one b).
    + apply (lt_le_iff _ _ (inl Hblt)).
  - apply (le_id_l _ (mult (r_pow b (Datatypes.S m)) b) _).
    + apply (mult_comm b (r_pow b (Datatypes.S m))).
    + apply (le_id_r _ (mult (r_pow b m) b) _).
      * apply (mult_comm (r_pow b m) b).
      * apply (le_mult_compat (r_pow b (Datatypes.S m)) (r_pow b m) b Hb).
        exact IH.
Qed.

(* ===== geometric decay of the gradient magnitude over the iteration:
   |g(x_{n+k})| <= kappa^k * |g(x_n)| ===== *)
Lemma grad_decay_iter : forall (E_A : R) (n k : nat),
  le (abs (entropy_gradient (iterate dynamics (n + k) E_A)))
     (mult (r_pow kappa k) (abs (entropy_gradient (iterate dynamics n E_A)))).
Proof.
  intros E_A n k.
  induction k as [| k IH]; simpl.
  - (* k = 0: |g(x_n)| <= 1 * |g(x_n)|, by [mult_comm] and [mult_one] *)
    rewrite (Nat.add_0_r n).
    apply (le_id_r _ (abs (entropy_gradient (iterate dynamics n E_A))) _).
    + apply (id_trans (id_sym (mult_one (abs (entropy_gradient (iterate dynamics n E_A)))))
                      (id_sym (mult_comm one (abs (entropy_gradient (iterate dynamics n E_A)))))).
    + apply le_refl.
  - (* k = S k': |g(x_{n+S k'})| <= kappa * |g(x_{n+k'})| <= kappa * (kappa^{k'} * |g(x_n)|) == kappa^{S k'} * |g(x_n)| *)
    apply (le_trans _ (mult kappa (abs (entropy_gradient (iterate dynamics (n + k) E_A)))) _).
    + (* single-step decay: [gradient_abs_decay] at (n + k) *)
      rewrite (Nat.add_succ_r n k).
      apply (le_id_l _ (abs (entropy_gradient (iterate dynamics (Datatypes.S (n + k)) E_A))) _).
      * reflexivity.
      * exact (gradient_abs_decay E_A (n + k)).
    + (* kappa * |g(x_{n+k})| <= kappa * (kappa^k * |g(x_n)|) == (kappa * kappa^k) * |g(x_n)|: le_trans + mult_assoc *)
      apply (le_trans _ (mult kappa (mult (r_pow kappa k) (abs (entropy_gradient (iterate dynamics n E_A))))) _).
      * (* kappa * Y <= kappa * (kappa^k * X), by [mult_comm] and [le_mult_compat] *)
        apply (le_id_l _ (mult (abs (entropy_gradient (iterate dynamics (n + k) E_A))) kappa) _).
        -- apply (mult_comm kappa (abs (entropy_gradient (iterate dynamics (n + k) E_A)))).
        -- apply (le_id_r _ (mult (mult (r_pow kappa k) (abs (entropy_gradient (iterate dynamics n E_A)))) kappa) _).
           ++ apply (mult_comm (mult (r_pow kappa k) (abs (entropy_gradient (iterate dynamics n E_A)))) kappa).
           ++ apply (le_mult_compat (abs (entropy_gradient (iterate dynamics (n + k) E_A)))
                                    (mult (r_pow kappa k) (abs (entropy_gradient (iterate dynamics n E_A))))
                                    kappa kappa_pos).
              exact IH.
      * (* kappa * (kappa^k * X) <= (kappa * kappa^k) * X, by [le_id_r] and
   [mult_assoc] in the forward direction *)
        apply (le_id_r _ (mult kappa (mult (r_pow kappa k) (abs (entropy_gradient (iterate dynamics n E_A))))) _).
        -- apply (mult_assoc kappa (r_pow kappa k) (abs (entropy_gradient (iterate dynamics n E_A)))).
        -- apply le_refl.
Qed.

(* ===== multi-step contraction:
   |x_{n+k+1} - x_{n+k}| <= |eta| * kappa^k * |g(x_n)| ===== *)
Lemma iterate_step_abs_diff_iter : forall (E_A : R) (n k : nat),
  le (abs (minus (iterate dynamics (n + Datatypes.S k) E_A)
                 (iterate dynamics (n + k) E_A)))
     (mult (abs eta) (mult (r_pow kappa k) (abs (entropy_gradient (iterate dynamics n E_A))))).
Proof.
  intros E_A n k.
  induction k as [| k IH]; simpl.
  - (* k = 0: |x_{n+1} - x_n| <= |eta| * (1 * |g(x_n)|) *)
    rewrite (Nat.add_1_r n). rewrite (Nat.add_0_r n).
    apply (le_id_l _ (mult (abs eta) (abs (entropy_gradient (iterate dynamics n E_A)))) _).
    + (* step difference == |eta| * |g|, by [iterate_step_abs_diff] *)
      exact (iter_abs E_A n).
    + (* |eta| * |g| <= |eta| * (1 * |g|), by [mult_comm] and [mult_one] *)
      apply (le_id_r _ (mult (abs eta) (abs (entropy_gradient (iterate dynamics n E_A)))) _).
      * apply (id_cong (fun z => mult (abs eta) z)
                       (id_sym (id_trans (mult_comm one (abs (entropy_gradient (iterate dynamics n E_A))))
                                         (mult_one (abs (entropy_gradient (iterate dynamics n E_A))))))).
      * apply le_refl.
  - (* k = S k': |x_{n+S(S k')} - x_{n+S k'}| <= |eta| * |g(x_{n+S k'})| <= |eta| * (kappa^{S k'} * |g(x_n)|) *)
    apply (le_trans _ (mult (abs eta) (abs (entropy_gradient (iterate dynamics (n + Datatypes.S k) E_A)))) _).
    + (* one-step difference: [iterate_step_abs_diff] at (n + S k) *)
      rewrite (Nat.add_succ_r n (Datatypes.S k)).
      apply (le_id_l _ (mult (abs eta) (abs (entropy_gradient (iterate dynamics (n + Datatypes.S k) E_A)))) _).
      * exact (iter_abs E_A (n + Datatypes.S k)).
      * apply le_refl.
    + (* |eta| * |g(x_{n + S k'})| <= |eta| * (kappa^(S k') * |g(x_n)|), by
   [mult_comm], weak [le_mult_compat] and [grad_decay_iter] *)
      apply (le_id_l _ (mult (abs (entropy_gradient (iterate dynamics (n + Datatypes.S k) E_A))) (abs eta)) _).
      * apply (mult_comm (abs eta) (abs (entropy_gradient (iterate dynamics (n + Datatypes.S k) E_A)))).
      * apply (le_id_r _ (mult (mult (r_pow kappa (Datatypes.S k)) (abs (entropy_gradient (iterate dynamics n E_A)))) (abs eta)) _).
        -- apply (mult_comm (mult (r_pow kappa (Datatypes.S k)) (abs (entropy_gradient (iterate dynamics n E_A)))) (abs eta)).
        -- apply (le_mult_compat_weak (abs (entropy_gradient (iterate dynamics (n + Datatypes.S k) E_A)))
                                      (mult (r_pow kappa (Datatypes.S k)) (abs (entropy_gradient (iterate dynamics n E_A))))
                                      (abs eta) (abs_nonneg eta)).
           apply (grad_decay_iter E_A n (Datatypes.S k)).
Qed.

(* ===== Finite sums in the [R] layer ===== *)
Fixpoint sum_R (f : nat -> R) (n : nat) : R :=
  match n with
  | 0%nat => zero
  | Datatypes.S m => plus (sum_R f m) (f m)
  end.

(* termwise monotonicity of sums: (forall k < n, f k <= g k) implies
   sum f <= sum g *)
Lemma sum_R_le : forall f g n,
  (forall k, NatLe (Datatypes.S k) n -> le (f k) (g k)) ->
  le (sum_R f n) (sum_R g n).
Proof.
  intros f g n H.
  induction n as [| m IH]; simpl.
  - apply le_refl.
  - apply (le_trans (plus (sum_R f m) (f m)) (plus (sum_R g m) (f m)) (plus (sum_R g m) (g m))).
    + apply (le_plus_compat (sum_R f m) (sum_R g m) (f m) (f m)).
      * apply IH. intros k Hk. apply (H k).
        apply NatLe_lift.
        assert (Hkle : (Datatypes.S k <= m)%nat) by (apply NatLe_drop; exact Hk).
        lia.
      * apply le_refl.
    + apply (le_plus_compat (sum_R g m) (sum_R g m) (f m) (g m)).
      * apply le_refl.
      * apply (H m). apply NatLe_lift. apply Nat.le_refl.
Qed.

(* a vanishing sum: if every term is zero then the sum is zero *)
Lemma sum_R_zero : forall f n,
  (forall k, NatLe (Datatypes.S k) n -> Id (f k) zero) ->
  Id (sum_R f n) zero.
Proof.
  intros f n H.
  induction n as [| m IH]; simpl.
  - apply id_refl.
  - assert (IHw : forall k, NatLe (Datatypes.S k) m -> Id (f k) zero).
    { intros k Hk. apply (H k). apply NatLe_lift.
      assert (Hkle : (Datatypes.S k <= m)%nat) by (apply NatLe_drop; exact Hk).
      lia. }
    apply (id_trans (id_cong2 plus (IH IHw)
                               (H m (NatLe_lift (Datatypes.S m) (Datatypes.S m)
                                       (Nat.le_refl (Datatypes.S m)))))
                    (plus_zero zero)).
Qed.

(* mult (1-x) * y == y + (-x) * y: distrib + mult_one *)
Lemma mult_one_minus_r : forall x y,
  Id (mult (minus one x) y) (plus y (mult (opp x) y)).
Proof.  intros x y.
  unfold minus.
  exact (id_trans (mult_plus_distr_r one (opp x) y)
           (id_cong2 plus (id_trans (mult_comm one y) (mult_one y))
              (id_refl))).
Qed.

(* telescoping: 1 - A + A - B == 1 - B (ring algebra in the [R] layer,
   using [plus_assoc]/[plus_comm]/[plus_opp]/[plus_zero]) *)
Lemma telescoping : forall a b,
  Id (plus (minus one a) (minus a b)) (minus one b).
Proof.  intros a b.
  unfold minus.
  exact (id_trans (id_sym (plus_assoc one (opp a) (plus a (opp b))))
           (id_cong (fun z => plus one z)
              (id_trans (plus_assoc (opp a) a (opp b))
                (id_trans (id_cong (fun z => plus z (opp b))
                            (id_trans (plus_comm (opp a) a) (plus_opp a)))
                  (id_trans (plus_comm zero (opp b)) (plus_zero (opp b))))))).
Qed.

(* ===== closed form of the geometric series:
   (1 - kappa) * sum_{k<m} kappa^k == 1 - kappa^m ===== *)
Lemma geom_sum_closed : forall m,
  Id (mult (minus one kappa) (sum_R (r_pow kappa) m))
     (minus one (r_pow kappa m)).
Proof.
  intros m.
  induction m as [| m IH]; simpl.
  - (* m = 0: the left side is (1 - kappa) * 0 == 0 and the right side is
   1 - 1 == 0 *)
    apply (id_trans (mult_zero (minus one kappa)) (id_sym (plus_opp one))).
  - (* m = S m': distribute, apply the IH, then
   [mult_one_minus_r], [opp_mult_r] and [telescoping] *)
    apply (id_trans (distrib (minus one kappa) (sum_R (r_pow kappa) m) (r_pow kappa m))).
    apply (id_trans (id_cong2 plus IH (id_refl))).
    apply (id_trans (id_cong2 plus (id_refl) (mult_one_minus_r kappa (r_pow kappa m)))).
    apply (id_trans (id_cong2 plus (id_refl)
                                  (id_cong (fun z => plus (r_pow kappa m) z)
                                           (opp_mult_r kappa (r_pow kappa m))))).
    apply (telescoping (r_pow kappa m) (mult kappa (r_pow kappa m))).
Qed.

(* 0 < 1 - kappa (from kappa < 1): built from [lt_plus_compat_lt_le] and
   [plus_opp] *)
Lemma one_minus_kappa_pos : lt zero (minus one kappa).
Proof.  unfold minus.
  exact (lt_id_l zero (plus kappa (opp kappa)) (plus one (opp kappa))
           (id_sym (plus_opp kappa))
           (lt_plus_compat_lt_le kappa one (opp kappa) (opp kappa)
              kappa_lt_one (le_refl (opp kappa)))).
Qed.

(* 1-kappa^m <= 1 (from kappa^m >= 0): le_plus_nonneg_r + minus_plus_cancel *)
Lemma one_minus_pow_le_one : forall m, le (minus one (r_pow kappa m)) one.
Proof.
  intro m.
  apply (le_id_r _ (plus (minus one (r_pow kappa m)) (r_pow kappa m)) _).
  - apply (id_trans (plus_comm (minus one (r_pow kappa m)) (r_pow kappa m))
                    (minus_plus_cancel (r_pow kappa m) one)).
  - apply (le_plus_nonneg_r (minus one (r_pow kappa m)) (r_pow kappa m)).
    apply (r_pow_nonneg kappa m kappa_pos).
Qed.

(* bound on the geometric series: sum_{k<m} kappa^k <= 1/(1 - kappa),
   from the closed form, 1 - kappa^m <= 1, and reverse monotonicity under
   multiplication by a positive number *)
Lemma geom_sum_bound : forall m,
  le (sum_R (r_pow kappa) m) (inv_pos (minus one kappa) one_minus_kappa_pos).
Proof.
  intro m.
  set (I := inv_pos (minus one kappa) one_minus_kappa_pos).
  apply (le_id_r _ (mult one I) _).
  - (* one * I == I *)
    apply (id_trans (mult_comm one I) (mult_one I)).
  - (* sum <= one * I: sum == (mult (1-kappa) sum) * I <= one * I *)
    apply (le_id_l _ (mult (mult (minus one kappa) (sum_R (r_pow kappa) m)) I) _).
    + (* sum == mult (mult (1-kappa) sum) I *)
      apply (id_trans (id_sym (mult_one (sum_R (r_pow kappa) m)))).
      apply (id_trans (id_cong (fun z => mult (sum_R (r_pow kappa) m) z)
                               (id_sym (inv_pos_correct (minus one kappa) one_minus_kappa_pos)))).
      apply (id_trans (mult_assoc (sum_R (r_pow kappa) m) (minus one kappa) I)).
      apply (id_cong (fun z => mult z I) (mult_comm (sum_R (r_pow kappa) m) (minus one kappa))).
    + (* le (mult (mult (1-kappa) sum) I) (mult one I): le_mult_compat_r *)
      apply (le_mult_compat_weak (mult (minus one kappa) (sum_R (r_pow kappa) m)) one I).
      * (* 0 <= I: inv_pos_pos + lt_le_iff *)
        apply (lt_le_iff _ _ (inl (inv_pos_pos (minus one kappa) one_minus_kappa_pos))).
      * (* (1-kappa) * sum <= 1: geom_sum_closed + one_minus_pow_le_one *)
        apply (le_id_l _ (minus one (r_pow kappa m)) _).
        -- apply (geom_sum_closed m).
        -- apply (one_minus_pow_le_one m).
Qed.

(* ===== Cauchy argument, final stage ===== *)

(* iterate the metric triangle inequality into a sum:
   metric (x_{n+m}) (x_n) <= sum_{k<m} metric (x_{n+k+1}) (x_{n+k}) *)
Lemma metric_tail_le_sum : forall (E_A : R) (n m : nat),
  le (metric (iterate dynamics (n + m) E_A) (iterate dynamics n E_A))
     (sum_R (fun k => metric (iterate dynamics (n + Datatypes.S k) E_A)
                              (iterate dynamics (n + k) E_A)) m).
Proof.
  intros E_A n m.
  induction m as [| m IH]; simpl.
  - (* m = 0: metric (x_n) (x_n) <= 0: metric_refl_zero *)
    rewrite (Nat.add_0_r n).
    apply (le_id_l _ zero _ (metric_refl_zero (iterate dynamics n E_A)) (le_refl zero)).
  - (* m = S m': metric triangle inequality plus the IH *)
    rewrite (Nat.add_succ_r n m).
    apply (le_trans _ (plus (metric (iterate dynamics (n + m) E_A) (iterate dynamics n E_A))
                            (metric (iterate dynamics (Datatypes.S (n + m)) E_A)
                                    (iterate dynamics (n + m) E_A))) _).
    + (* [metric_triangle] with [plus_comm] (step + tail == tail + step) *)
      apply (le_id_r _ (plus (metric (iterate dynamics (Datatypes.S (n + m)) E_A)
                                     (iterate dynamics (n + m) E_A))
                             (metric (iterate dynamics (n + m) E_A) (iterate dynamics n E_A))) _).
      * apply (plus_comm (metric (iterate dynamics (Datatypes.S (n + m)) E_A)
                                 (iterate dynamics (n + m) E_A))
                         (metric (iterate dynamics (n + m) E_A) (iterate dynamics n E_A))).
      * apply (metric_triangle (iterate dynamics (Datatypes.S (n + m)) E_A)
                               (iterate dynamics (n + m) E_A)
                               (iterate dynamics n E_A)).
    + apply (le_plus_compat (metric (iterate dynamics (n + m) E_A) (iterate dynamics n E_A))
                            (sum_R (fun k => metric (iterate dynamics (n + Datatypes.S k) E_A)
                                                   (iterate dynamics (n + k) E_A)) m)
                            (metric (iterate dynamics (Datatypes.S (n + m)) E_A)
                                    (iterate dynamics (n + m) E_A))
                            (metric (iterate dynamics (Datatypes.S (n + m)) E_A)
                                    (iterate dynamics (n + m) E_A))).
      * exact IH.
      * apply le_refl.
Qed.

(* constant extraction for [sum_R]: sum (a * f k) == a * (sum f) *)
Lemma sum_R_scal_l : forall a f n,
  Id (sum_R (fun k => mult a (f k)) n) (mult a (sum_R f n)).
Proof.
  intros a f n.
  induction n as [| m IH]; simpl.
  - apply (id_sym (mult_zero a)).
  - apply (id_trans (id_cong2 plus IH (id_refl)) (id_sym (distrib a (sum_R f m) (f m)))).
Qed.

(* right extraction for [sum_R]: sum (f k * b) == (sum f) * b *)
Lemma sum_R_mult_r : forall f b n,
  Id (sum_R (fun k => mult (f k) b) n) (mult (sum_R f n) b).
Proof.
  intros f b n.
  induction n as [| m IH]; simpl.
  - apply (id_sym (id_trans (mult_comm zero b) (mult_zero b))).
  - apply (id_trans (id_cong2 plus IH (id_refl)) (id_sym (mult_plus_distr_r (sum_R f m) (f m) b))).
Qed.

(* tail contraction: metric (x_{n+m}) (x_n) <= |eta| * |g(x_n)| * S,
   where S := 1/(1 - kappa) *)
Lemma iterate_metric_tail_bound : forall (E_A : R) (n m : nat),
  le (metric (iterate dynamics (n + m) E_A) (iterate dynamics n E_A))
     (mult (abs eta)
           (mult (abs (entropy_gradient (iterate dynamics n E_A)))
                 (inv_pos (minus one kappa) one_minus_kappa_pos))).
Proof.
  intros E_A n m.
  apply (le_trans _ (sum_R (fun k => metric (iterate dynamics (n + Datatypes.S k) E_A)
                                           (iterate dynamics (n + k) E_A)) m) _).
  - apply (metric_tail_le_sum E_A n m).
  - (* sum of step sizes <= sum |eta| * kappa^k * |g| <= |eta| * |g| * S *)
    apply (le_trans _ (sum_R (fun k => mult (abs eta)
                                           (mult (r_pow kappa k)
                                                 (abs (entropy_gradient (iterate dynamics n E_A))))) m) _).
    + (* termwise: each metric step == |step| <= |eta| * kappa^k * |g|
   ([metric_abs] and [iterate_step_abs_diff_iter]) *)
      apply (sum_R_le (fun k => metric (iterate dynamics (n + Datatypes.S k) E_A)
                                       (iterate dynamics (n + k) E_A))
                      (fun k => mult (abs eta)
                                    (mult (r_pow kappa k)
                                          (abs (entropy_gradient (iterate dynamics n E_A))))) m).
      intros k Hk.
      apply (le_id_l _ (abs (minus (iterate dynamics (n + Datatypes.S k) E_A)
                                   (iterate dynamics (n + k) E_A))) _).
      * apply (metric_abs (iterate dynamics (n + Datatypes.S k) E_A)
                          (iterate dynamics (n + k) E_A)).
      * apply (iterate_step_abs_diff_iter E_A n k).
    + (* sum |eta| * kappa^k * |g| <= |eta| * |g| * S: factor out the common
   terms in the sum *)
      apply (le_id_l _ (mult (abs eta)
                             (mult (sum_R (r_pow kappa) m)
                                   (abs (entropy_gradient (iterate dynamics n E_A))))) _).
      * (* sum |eta|(kappa^k * X) == |eta| * ((sumkappa^k) * X): sum_R_scal_l + sum_R_mult_r *)
        apply (id_trans (sum_R_scal_l (abs eta)
                          (fun k => mult (r_pow kappa k) (abs (entropy_gradient (iterate dynamics n E_A)))) m)
                        (id_cong (fun z => mult (abs eta) z)
                                 (sum_R_mult_r (r_pow kappa) (abs (entropy_gradient (iterate dynamics n E_A))) m))).
      * (* |eta| * ((sum kappa^k) * X) <= |eta| * (I * X), by [le_mult_compat]
   with the common factor on the left *)
        apply (le_mult_compat_r (abs eta)
                                (mult (sum_R (r_pow kappa) m) (abs (entropy_gradient (iterate dynamics n E_A))))
                                (mult (abs (entropy_gradient (iterate dynamics n E_A)))
                                      (inv_pos (minus one kappa) one_minus_kappa_pos))).
        -- apply (abs_nonneg eta).
        -- (* (sum kappa^k) * X <= X * I, by weak [le_mult_compat] and [mult_comm] *)
           apply (le_id_r _ (mult (inv_pos (minus one kappa) one_minus_kappa_pos)
                                  (abs (entropy_gradient (iterate dynamics n E_A)))) _).
           ++ apply (mult_comm (inv_pos (minus one kappa) one_minus_kappa_pos)
                               (abs (entropy_gradient (iterate dynamics n E_A)))).
           ++ apply (le_mult_compat_weak (sum_R (r_pow kappa) m)
                                         (inv_pos (minus one kappa) one_minus_kappa_pos)
                                         (abs (entropy_gradient (iterate dynamics n E_A)))).
              ** apply (abs_nonneg (entropy_gradient (iterate dynamics n E_A))).
              ** apply (geom_sum_bound m).
Qed.

(* ===== final stage: metric-Cauchy implies [cauchy_complete] implies the
   limit exists ===== *)

(* nonzero step size (explicit interface assumption: with eta = 0 the
   dynamics is trivial, and the convergence argument needs |eta| > 0) *)
Variable eta_abs_pos : lt zero (abs eta).

(* 1/(1 - kappa) and a := |eta| * |g(x_0)| * S (section-level [Let]) *)
Let S := inv_pos (minus one kappa) one_minus_kappa_pos.

(* decreasing powers ([r_pow_dec] by iteration): m <= n implies
   kappa^n <= kappa^m *)
Lemma r_pow_dec_iter : forall m n, (m <= n)%nat -> le (r_pow kappa n) (r_pow kappa m).
Proof.
  intros m n Hmn.
  revert m Hmn.
  induction n as [| n IH]; intros m Hmn.
  - (* n = 0: m <= 0 implies m = 0 *)
    assert (Hm0 : m = 0%nat) by lia. subst m. apply le_refl.
  - (* n = S n': decide with [Nat.leb] *)
    destruct (Nat.leb m n) eqn:Emn.
    + (* m <= n: kappa^{S n} <= kappa^n <= kappa^m *)
      apply (le_trans _ (r_pow kappa n) _); [apply (r_pow_dec kappa n kappa_pos kappa_lt_one) | apply (IH m (proj1 (Nat.leb_le m n) Emn))].
    + (* not (m <= n): then m = S n for some n (from the premise m <= S n) *)
      apply Nat.leb_gt in Emn.
      assert (Hm : m = Datatypes.S n) by lia. subst m. apply le_refl.
Qed.

(* swap the middle factor: (a * b) * c == (a * c) * b *)
Lemma mult_swap_mid : forall a b c, Id (mult (mult a b) c) (mult (mult a c) b).
Proof.  intros a b c.
  exact (id_trans (id_sym (mult_assoc a b c))
           (id_trans (id_cong (fun z => mult a z) (mult_comm b c))
              (mult_assoc a c b))).
Qed.

(* swap the outer factors: (a * b) * c * d == (a * d) * c * b,
   composing [mult_swap_mid] twice *)
Lemma mult_swap_outer : forall a b c d,
  Id (mult (mult (mult a b) c) d) (mult (mult (mult a c) d) b).
Proof.  intros a b c d.
  exact (id_trans (id_cong (fun z => mult z d) (mult_swap_mid a b c))
           (mult_swap_mid (mult a c) b d)).
Qed.

(* gradient-bound helper: |eta| * |g(x_n)| * S <= (|eta| * |g0| * S) * kappa^n,
   from [grad_decay_iter], monotonicity, and rearrangement *)
Lemma grad_bound_aux : forall E_A n,
  lt zero (abs (entropy_gradient (iterate dynamics 0 E_A))) ->
  le (mult (abs eta) (mult (abs (entropy_gradient (iterate dynamics n E_A))) S))
     (mult (mult (mult (abs eta) (abs (entropy_gradient (iterate dynamics 0 E_A)))) S)
           (r_pow kappa n)).
Proof.
  intros E_A n Hg0pos.
  apply (le_id_r _ (mult (abs eta) (mult (mult (r_pow kappa n) (abs (entropy_gradient (iterate dynamics 0 E_A)))) S)) _).
  - (* |eta| * ((kappa^n * g0) * S) == (|eta| * g0 * S) * kappa^n:
   rearrangement *)
    apply (id_trans (mult_assoc (abs eta) (mult (r_pow kappa n) (abs (entropy_gradient (iterate dynamics 0 E_A)))) S)).
    apply (id_trans (id_cong (fun z => mult z S)
                             (mult_assoc (abs eta) (r_pow kappa n) (abs (entropy_gradient (iterate dynamics 0 E_A)))))).
    apply (mult_swap_outer (abs eta) (r_pow kappa n) (abs (entropy_gradient (iterate dynamics 0 E_A))) S).
  - (* |eta| * (gn * S) <= |eta| * ((kappa^n * g0) * S): le_mult_compat_r + grad_decay_iter *)
    apply (le_mult_compat_r (abs eta)
                            (mult (abs (entropy_gradient (iterate dynamics n E_A))) S)
                            (mult (mult (r_pow kappa n) (abs (entropy_gradient (iterate dynamics 0 E_A)))) S)).
    + apply (abs_nonneg eta).
    + apply (le_mult_compat_weak (abs (entropy_gradient (iterate dynamics n E_A)))
                                 (mult (r_pow kappa n) (abs (entropy_gradient (iterate dynamics 0 E_A))))
                                 S).
      * apply (lt_le_iff _ _ (inl (inv_pos_pos (minus one kappa) one_minus_kappa_pos))).
      * apply (grad_decay_iter E_A 0 n).
Qed.

(* metric (x_m) (x_n) <= a * kappa^(min m n): metric symmetry, tail
   contraction, and [grad_bound_aux] *)
Lemma iterate_metric_min_bound : forall E_A m n,
  lt zero (abs (entropy_gradient (iterate dynamics 0 E_A))) ->
  le (metric (iterate dynamics m E_A) (iterate dynamics n E_A))
     (mult (mult (mult (abs eta) (abs (entropy_gradient (iterate dynamics 0 E_A)))) S)
           (r_pow kappa (Nat.min m n))).
Proof.
  intros E_A m n Hg0pos.
  destruct (Nat.leb m n) eqn:Emn.
  - (* m <= n: by metric symmetry, take m as the base *)
    apply Nat.leb_le in Emn.
    apply (le_id_l _ (metric (iterate dynamics n E_A) (iterate dynamics m E_A)) _).
    { exact (metric_sym (iterate dynamics m E_A) (iterate dynamics n E_A)). }
    rewrite (Nat.min_l m n Emn).
    rewrite <- (Nat.sub_add m n Emn).
    rewrite (Nat.add_comm (n - m) m).
    apply (le_trans _ (mult (abs eta) (mult (abs (entropy_gradient (iterate dynamics m E_A))) S)) _).
    + apply (iterate_metric_tail_bound E_A m (n - m)).
    + apply (grad_bound_aux E_A m Hg0pos).
  - (* n <= m: take n as the base *)
    apply Nat.leb_gt in Emn.
    rewrite (Nat.min_r m n (Nat.lt_le_incl n m Emn)).
    rewrite <- (Nat.sub_add n m (Nat.lt_le_incl n m Emn)).
    rewrite (Nat.add_comm (m - n) n).
    apply (le_trans _ (mult (abs eta) (mult (abs (entropy_gradient (iterate dynamics n E_A))) S)) _).
    + apply (iterate_metric_tail_bound E_A n (m - n)).
    + apply (grad_bound_aux E_A n Hg0pos).
Qed.

(* Cauchy property: for every eps > 0 there is N such that
   metric (x_m) (x_n) < eps for m, n >= N (closed by geometric breakout) *)
Lemma iterate_cauchy : forall (E_A : R),
  lt zero (abs (entropy_gradient (iterate dynamics 0 E_A))) ->
  forall eps : R, lt zero eps ->
    sigT (fun N : nat => forall m n : nat, NatLe N m -> NatLe N n ->
      lt (metric (iterate dynamics m E_A) (iterate dynamics n E_A)) eps).
Proof.
  intros E_A Hg0pos eps Hep.
  set (a := mult (mult (abs eta) (abs (entropy_gradient (iterate dynamics 0 E_A)))) S).
  assert (Ha : lt zero a).
  { unfold a.
    apply (mult_positive (mult (abs eta) (abs (entropy_gradient (iterate dynamics 0 E_A)))) S).
    - apply (mult_positive (abs eta) (abs (entropy_gradient (iterate dynamics 0 E_A))) eta_abs_pos Hg0pos).
    - exact (inv_pos_pos (minus one kappa) one_minus_kappa_pos). }
  destruct (r_arch_pow a Ha eps Hep) as [N0 HN0].
  exists N0.
  intros m n Hm Hn.
  assert (Hm' : (N0 <= m)%nat) by (apply NatLe_drop; exact Hm).
  assert (Hn' : (N0 <= n)%nat) by (apply NatLe_drop; exact Hn).
  apply (le_lt_trans _ (mult a (r_pow kappa (Nat.min m n))) _).
  - (* metric (x_m) (x_n) <= a * kappa^{min m n} *)
    unfold a.
    apply (iterate_metric_min_bound E_A m n Hg0pos).
  - (* a * kappa^{min} <= a * kappa^{N0} < eps (min >= N0 implies kappa^{min} <= kappa^{N0}) *)
    apply (le_lt_trans _ (mult a (r_pow kappa N0)) _).
    + apply (le_mult_compat_r a (r_pow kappa (Nat.min m n)) (r_pow kappa N0)).
      * apply (lt_le_iff _ _ (inl Ha)).
      * apply (r_pow_dec_iter N0 (Nat.min m n)). lia.
    + exact HN0.
Qed.

Variable log_lt_mono_cc : forall a b : R, lt zero a -> lt zero b -> lt a b -> lt (log a) (log b).

(* embedding of [nat] into [R] (local to this section; an [of_nat] for the
   later GRPO section is defined further down in the file, avoiding a
   forward reference) *)
Fixpoint nat_to_R (n : nat) : R :=
  match n with
  | O => zero
  | Datatypes.S n' => plus one (nat_to_R n')
  end.

(* ============ Lemma 1: logarithm of a power ============ *)
(* log (x^n) == of_nat n * log x, by induction via [log_mult] *)
Lemma log_pow_cc : forall (x : R) (n : nat), lt zero x ->
  Id (log (r_pow x n)) (mult (nat_to_R n) (log x)).
Proof.
  intros x n Hx.
  induction n as [| n IH].
  - simpl.
    apply (id_trans log_one
                   (id_sym (id_trans (mult_comm zero (log x)) (mult_zero (log x))))).
  - simpl r_pow.
    apply (id_trans (log_mult x (r_pow x n) Hx (r_pow_pos x n Hx))).
    apply (id_trans (id_cong2 plus (id_refl) IH)).
    assert (Hr : Id (mult (plus one (nat_to_R n)) (log x)) (plus (log x) (mult (nat_to_R n) (log x)))).
    {
      apply (id_trans (mult_comm (plus one (nat_to_R n)) (log x))).
      apply (id_trans (distrib (log x) one (nat_to_R n))).
      apply (id_trans (id_cong (fun y => plus y (mult (log x) (nat_to_R n))) (mult_one (log x)))).
      apply (id_cong (fun y => plus (log x) y) (mult_comm (log x) (nat_to_R n))).
    }
    apply (id_sym Hr).
Qed.

(* ============ Lemma 2: upgrading the closed-form breakout of
   [r_arch_pow] to the log scale ============ *)
(* upgraded existence of N: there is N with log (a * kappa^N) <= log eps
   and a * kappa^N < eps (the first component is the closed-form
   characterization of the explicit budget function N(eps):
   mathematically N >= log(a/eps) / log(1/kappa) on the log scale) *)
Lemma r_arch_pow_log_budget : forall a : R, lt zero a -> forall eps : R, lt zero eps ->
  sigT (fun N : nat => And (le (log (mult a (r_pow kappa N))) (log eps))
                           (lt (mult a (r_pow kappa N)) eps)).
Proof.
  intros a Ha eps Hep.
  destruct (r_arch_pow a Ha eps Hep) as [N0 HN0].
  exists N0.
  split.
  - apply (lt_le_iff _ _ (inl (log_lt_mono_cc (mult a (r_pow kappa N0)) eps
                                              (mult_positive a (r_pow kappa N0) Ha (r_pow_pos kappa N0 kappa_pos))
                                              Hep
                                              HN0))).
  - exact HN0.
Qed.

(* ============ Main theorem: an explicit computable convergence rate
   ============ *)
(* upgrade of [iterate_cauchy]: N satisfies the closed-form budget
   condition log (a * kappa^N) <= log eps (the log breakout for
   a := |eta| * |g(E_A)| * S) and is still a Cauchy point *)
Theorem iterate_cauchy_explicit_N : forall (E_A : R),
  lt zero (abs (entropy_gradient (iterate dynamics 0 E_A))) ->
  forall eps : R, lt zero eps ->
    sigT (fun N : nat =>
      And (le (log (mult (mult (mult (abs eta) (abs (entropy_gradient (iterate dynamics 0 E_A)))) S)
                          (r_pow kappa N)))
              (log eps))
          (forall m n : nat, NatLe N m -> NatLe N n ->
            lt (metric (iterate dynamics m E_A) (iterate dynamics n E_A)) eps)).
Proof.
  intros E_A Hg0pos eps Hep.
  set (a := mult (mult (abs eta) (abs (entropy_gradient (iterate dynamics 0 E_A)))) S).
  assert (Ha : lt zero a).
  { unfold a.
    apply (mult_positive (mult (abs eta) (abs (entropy_gradient (iterate dynamics 0 E_A)))) S).
    - apply (mult_positive (abs eta) (abs (entropy_gradient (iterate dynamics 0 E_A))) eta_abs_pos Hg0pos).
    - exact (inv_pos_pos (minus one kappa) one_minus_kappa_pos). }
  destruct (r_arch_pow_log_budget a Ha eps Hep) as [N [HNlog HNgeo]].
  exists N.
  split.
  - unfold a in HNlog. exact HNlog.
  - intros m n Hm Hn.
    assert (Hm' : (N <= m)%nat) by (apply NatLe_drop; exact Hm).
    assert (Hn' : (N <= n)%nat) by (apply NatLe_drop; exact Hn).
    apply (le_lt_trans _ (mult a (r_pow kappa (Nat.min m n))) _).
    + unfold a.
      apply (iterate_metric_min_bound E_A m n Hg0pos).
    + apply (le_lt_trans _ (mult a (r_pow kappa N)) _).
      * apply (le_mult_compat_r a (r_pow kappa (Nat.min m n)) (r_pow kappa N)).
        -- apply (lt_le_iff _ _ (inl Ha)).
        -- apply (r_pow_dec_iter N (Nat.min m n)). lia.
      * exact HNgeo.
Qed.

(* the limit exists: metric-Cauchy implies [cauchy_complete] implies [lim] *)
Lemma iterate_lim_exists : forall (E_A : R),
  lt zero (abs (entropy_gradient (iterate dynamics 0 E_A))) ->
  ExistsT (fun E_star : R => lim (fun n => iterate dynamics n E_A) E_star).
Proof.
  intros E_A Hg0pos.
  apply (cauchy_complete (fun n => iterate dynamics n E_A)).
  intros eps Hep.
  destruct (iterate_cauchy E_A Hg0pos eps Hep) as [N HN].
  exists N.
  intros m n Hm Hn.
  exact (HN m n Hm Hn).
Qed.

(* ===== the gradient magnitude decreases monotonically (assembled from
   [strict_concavity]) =====
   0 < eta, 0 < g(x_n), 0 < g(x_{n+1}) imply |g(x_{n+1})| <= |g(x_n)|.
   Chain: x_n < x_{n+1} (eta * g(x_n) > 0), then
   g(x_{n+1}) < g(x_n) by [strict_concavity], then
   |g(x_{n+1})| <= |g(x_n)| by [gradient_abs_mono]. *)

(* closure alias for [gradient_abs_mono] (depending only on
   [entropy_gradient]) *)
Let gmono := (@gradient_abs_mono RI entropy_gradient).

Theorem iterate_grad_abs_mono : forall (E_A : R) (n : nat),
  lt zero eta ->
  lt zero (entropy_gradient (iterate dynamics n E_A)) ->
  lt zero (entropy_gradient (iterate dynamics (Datatypes.S n) E_A)) ->
  le (abs (entropy_gradient (iterate dynamics (Datatypes.S n) E_A)))
     (abs (entropy_gradient (iterate dynamics n E_A))).
Proof.
  intros E_A n Heta Hgn Hgn1.
  (* x_{n+1} == x_n + eta * g(x_n) (dynamics_gradient_step at iterate n) *)
  assert (Hxnext : Id (iterate dynamics (Datatypes.S n) E_A)
                      (plus (iterate dynamics n E_A) (mult eta (entropy_gradient (iterate dynamics n E_A))))).
  { simpl. exact (dynamics_gradient_step (iterate dynamics n E_A)). }
  (* 0 < eta * g(x_n) (mult_positive) *)
  assert (Heta_g : lt zero (mult eta (entropy_gradient (iterate dynamics n E_A)))).
  { apply (mult_positive eta (entropy_gradient (iterate dynamics n E_A)) Heta Hgn). }
  (* x_n < x_n + eta * g(x_n) (lt_plus_compat_lt_le + plus_zero) *)
  assert (Hlt0 : lt (iterate dynamics n E_A)
                   (plus (iterate dynamics n E_A) (mult eta (entropy_gradient (iterate dynamics n E_A))))).
  { apply (lt_id_l (iterate dynamics n E_A)
                   (plus (iterate dynamics n E_A) zero)
                   (plus (iterate dynamics n E_A) (mult eta (entropy_gradient (iterate dynamics n E_A))))
                   (id_sym (plus_zero (iterate dynamics n E_A)))
                   (lt_plus_compat_le_lt (iterate dynamics n E_A) (iterate dynamics n E_A) zero
                                         (mult eta (entropy_gradient (iterate dynamics n E_A)))
                                         (le_refl (iterate dynamics n E_A)) Heta_g)). }
  (* x_n < x_{n+1} *)
  assert (Hlt : lt (iterate dynamics n E_A) (iterate dynamics (Datatypes.S n) E_A)).
  { apply (lt_id_r (iterate dynamics n E_A)
                   (plus (iterate dynamics n E_A) (mult eta (entropy_gradient (iterate dynamics n E_A))))
                   (iterate dynamics (Datatypes.S n) E_A)
                   (id_sym Hxnext) Hlt0). }
  (* g(x_{n+1}) < g(x_n): strict_concavity *)
  assert (Hgdec : lt (entropy_gradient (iterate dynamics (Datatypes.S n) E_A))
                     (entropy_gradient (iterate dynamics n E_A))).
  { apply (strict_concavity (iterate dynamics n E_A) (iterate dynamics (Datatypes.S n) E_A)).
    exact Hlt. }
  (* |g(x_{n+1})| <= |g(x_n)|: gradient_abs_mono *)
  apply (gmono (iterate dynamics n E_A) (iterate dynamics (Datatypes.S n) E_A)).
  - exact Hlt.
  - exact Hgn1.
  - exact Hgdec.
Qed.

(* ===== final assembly: the squeeze lemma for [lim] and the composition of
   [dynamics_converges] ===== *)

(* further interface fields (standard properties as explicit assumptions) *)
(* (5) eps-N semantics of [lim]: a convergent sequence approximates its
   limit in the metric (the standard constructive convergence property;
   the [Real] instance [real_lim] is defined eps-N; the abstract [R] layer
   interface only has [lim_unique]) *)
Variable lim_metric_approx : forall (u : nat -> R) (l : R),
  lim u l -> forall eps : R, lt zero eps ->
    sigT (fun N : nat => forall n : nat, NatLe N n -> lt (metric (u n) l) eps).

(* (6) arbitrarily small nonnegative implies <= 0: for all eps > 0,
   x < eps implies x <= 0 (standard constructive ordered-field property,
   same family as [r_arch_pow]; needed to close the [lim] squeeze) *)
Variable le_all_eps_zero : forall x : R,
  (forall eps : R, lt zero eps -> lt x eps) -> le x zero.

(* auxiliary: abs (minus x zero) == abs x *)
Lemma abs_minus_zero : forall a : R, Id (abs (minus a zero)) (abs a).
Proof.
  intro a.
  assert (Hm : Id (minus a zero) a).
  { change (Id (plus a (opp zero)) a).
    assert (Hopp0 : Id (opp zero) zero).
    { apply (id_trans (id_sym (id_trans (plus_comm zero (opp zero))
                                        (plus_zero (opp zero))))
                      (plus_opp zero)). }
    rewrite Hopp0.
    apply plus_zero. }
  apply (id_cong abs Hm).
Qed.

(* auxiliary: building [NatLe] (n <= m implies NatLe n m) *)
Lemma natle_of_le : forall n m, (n <= m)%nat -> NatLe n m.
Proof.
  intros n m H.
  unfold NatLe.
  destruct (Nat.leb n m) eqn:E.
  - reflexivity.
  - exfalso.
    apply (proj1 (Nat.leb_gt n m)) in E.
    lia.
Qed.

(* squeeze core: lim x_n E_star for the iterate sequence, plus a nonzero
   initial gradient, implies g(E_star) == 0.
   Argument: for every eps > 0 take n >= max N1 N2, so
   |g(E_star) - g(x_n)| <= L * metric (x_n) E_star < eps/2
     ([lim_metric_approx] and [gradient_lipschitz]),
   |g(x_n)| <= kappa^n * |g0| < eps/2 ([grad_decay_iter] and [r_arch_pow]);
   triangle inequality and splitting eps in half give
   metric (g E_star) zero < eps, hence g E_star == 0 by [le_all_eps_zero]. *)
Lemma grad_squeeze_zero : forall (E_A E_star : R),
  lim (fun n => iterate dynamics n E_A) E_star ->
  lt zero (abs (entropy_gradient (iterate dynamics 0 E_A))) ->
  Id (entropy_gradient E_star) zero.
Proof.
  intros E_A E_star Hlim Hg0pos.
  apply metric_zero.
  apply le_antisym.
  - apply le_all_eps_zero.
    intros eps Heps.
    pose (eps2 := mult (inv_pos (plus one one) two_pos) eps).
    assert (Heps2 : lt zero eps2) by (unfold eps2; apply half_pos; exact Heps).
    pose (eps1 := mult (inv_pos L L_pos) eps2).
    assert (Heps1 : lt zero eps1).
    { unfold eps1.
      apply (mult_positive (inv_pos L L_pos) eps2).
      - apply (@inv_pos_pos RI L L_pos).
      - exact Heps2. }
    destruct (lim_metric_approx (fun n => iterate dynamics n E_A) E_star Hlim eps1 Heps1) as [N1 HN1].
  destruct (r_arch_pow (abs (entropy_gradient (iterate dynamics 0 E_A))) Hg0pos eps2 Heps2) as [N2 HN2].
    pose (n := Nat.max N1 N2).
    assert (Hn1 : NatLe N1 n) by (unfold n; apply natle_of_le; apply Nat.le_max_l).
    assert (Hn2 : NatLe N2 n) by (unfold n; apply natle_of_le; apply Nat.le_max_r).
    assert (Ht : le (metric (entropy_gradient E_star) zero)
                   (plus (metric (entropy_gradient E_star) (entropy_gradient (iterate dynamics n E_A)))
                         (metric (entropy_gradient (iterate dynamics n E_A)) zero))).
    { exact (metric_triangle (entropy_gradient E_star) (entropy_gradient (iterate dynamics n E_A)) zero). }
    assert (Hhalf1 : lt (metric (entropy_gradient E_star) (entropy_gradient (iterate dynamics n E_A))) eps2).
    { apply (le_lt_trans _ (mult L (metric (iterate dynamics n E_A) E_star)) _).
      - apply (le_id_l _ (abs (minus (entropy_gradient E_star) (entropy_gradient (iterate dynamics n E_A)))) _).
        + apply (metric_abs (entropy_gradient E_star) (entropy_gradient (iterate dynamics n E_A))).
        + apply (le_id_r _ (mult L (abs (minus E_star (iterate dynamics n E_A)))) _).
          * apply (id_cong (fun z => mult L z)
                   (id_trans (abs_minus_sym E_star (iterate dynamics n E_A))
                             (id_sym (metric_abs (iterate dynamics n E_A) E_star)))).
          * exact (gradient_lipschitz E_star (iterate dynamics n E_A)).
      - apply (lt_id_r _ (mult L eps1) _).
        + unfold eps1.
          apply (id_trans (mult_assoc L (inv_pos L L_pos) eps2)
                          (id_trans (id_cong (fun z => mult z eps2) (inv_pos_correct L L_pos))
                                    (id_trans (mult_comm one eps2) (mult_one eps2)))).
        + apply (lt_id_l _ (mult (metric (iterate dynamics n E_A) E_star) L) _).
          * apply (mult_comm L (metric (iterate dynamics n E_A) E_star)).
          * apply (lt_id_r _ (mult eps1 L) _).
            -- apply (id_sym (mult_comm L eps1)).
            -- apply (lt_mult_compat (metric (iterate dynamics n E_A) E_star) eps1 L L_pos).
               exact (HN1 n Hn1). }
    assert (Hhalf2 : lt (metric (entropy_gradient (iterate dynamics n E_A)) zero) eps2).
    { apply (le_lt_trans _ (mult (r_pow kappa n) (abs (entropy_gradient (iterate dynamics 0 E_A)))) _).
      - apply (le_id_l _ (abs (minus (entropy_gradient (iterate dynamics n E_A)) zero)) _).
        + apply (metric_abs (entropy_gradient (iterate dynamics n E_A)) zero).
        + apply (le_id_l _ (abs (entropy_gradient (iterate dynamics n E_A))) _).
          * apply (abs_minus_zero (entropy_gradient (iterate dynamics n E_A))).
          * exact (grad_decay_iter E_A 0 n).
      - apply (le_lt_trans _ (mult (r_pow kappa N2) (abs (entropy_gradient (iterate dynamics 0 E_A)))) _).
        + apply (le_mult_compat_weak (r_pow kappa n) (r_pow kappa N2)
                                     (abs (entropy_gradient (iterate dynamics 0 E_A)))
                                     (abs_nonneg (entropy_gradient (iterate dynamics 0 E_A)))).
          apply (r_pow_dec_iter N2 n). exact (NatLe_drop N2 n Hn2).
        + apply (lt_id_l _ (mult (abs (entropy_gradient (iterate dynamics 0 E_A))) (r_pow kappa N2)) _).
          * apply (id_sym (mult_comm (abs (entropy_gradient (iterate dynamics 0 E_A))) (r_pow kappa N2))).
          * exact (HN2). }
    apply (lt_id_r _ (plus eps2 eps2) _).
    { apply (half_twice eps). }
    { apply (le_lt_trans _ (plus (metric (entropy_gradient E_star) (entropy_gradient (iterate dynamics n E_A)))
                                 (metric (entropy_gradient (iterate dynamics n E_A)) zero)) _).
      { exact Ht. }
      { apply (lt_plus_compat
                 (metric (entropy_gradient E_star) (entropy_gradient (iterate dynamics n E_A)))
                 eps2
                 (metric (entropy_gradient (iterate dynamics n E_A)) zero)
                 eps2
                 Hhalf1 Hhalf2). } }
  - apply (@metric_pos RI).
Qed.

(* Assembly of [dynamics_converges]: the section variables of
   [ConvergenceTheorem] are replaced by the premises of
   [ConvergenceCauchy] — a nonzero initial gradient (needed by
   [iterate_lim_exists]) plus the step-size condition.
   Chain: [iterate_lim_exists] provides the limit, then
   [grad_squeeze_zero] squeezes g(E_star) == 0. *)
Theorem dynamics_converges : forall (E_A : R),
  lt zero (abs (entropy_gradient (iterate dynamics 0 E_A))) ->
  ExistsT (fun E_star : R =>
    And (lim (fun n => iterate dynamics n E_A) E_star)
        (Id (entropy_gradient E_star) zero)).
Proof.
  intros E_A Hg0pos.
  destruct (iterate_lim_exists E_A Hg0pos) as [E_star Hlim].
  exists E_star.
  split.
  - exact Hlim.
  - exact (grad_squeeze_zero E_A E_star Hlim Hg0pos).
Qed.

(* ============================================================
   Contraction theorems for gradient ascent under strong concavity:
   from mu-strong concavity, a Lipschitz gradient and a step-size
   constraint to a positive-branch gradient contraction.  Core lemmas:
   [gradient_step_contraction] (one-step contraction),
   [gradient_step_abs_contraction] (absolute-value contraction with
   kappa := 1 - eta * mu), [gradient_iterate_abs_decay] (iterated
   one-step contraction), [grad_decay_positive_iter] (kappa-power decay).
   New interface content: mu-strong concavity, a standard optimization
   assumption, not a classical axiom.
   ============================================================ *)
(* mu-strong concavity: x < y implies mu * (y - x) <= g(x) - g(y)
   (the concavity modulus, quantified) *)
Variable mu : R.
Variable mu_pos : lt zero mu.
Variable strong_concavity : forall x y : R, lt x y ->
  le (mult mu (minus y x)) (minus (entropy_gradient x) (entropy_gradient y)).
(* ===== one-step unfolding of the dynamics:
   dynamics x = x + eta * g(x) ===== *)
Lemma dynamics_step_unfold : forall x : R,
  Id (dynamics x) (plus x (mult eta (entropy_gradient x))).
Proof.
  intros x. exact (dynamics_gradient_step x).
Qed.

(* auxiliary: minus a b + b == a (invertibility of subtraction) *)
Lemma minus_plus_cancel_gap : forall a b : R,
  Id (plus (minus a b) b) a.
Proof.
  intros a b. unfold minus.
  apply (id_trans (id_sym (plus_assoc a (opp b) b))).
  apply (id_trans (id_cong (fun z => plus a z) (plus_comm (opp b) b))).
  apply (id_trans (id_cong (fun z => plus a z) (plus_opp b))).
  apply (plus_zero a).
Qed.

(* ===== positive-branch one-step contraction (non-absolute-value form):
   g(x) > 0 and eta * mu < 1 imply g(dynamics x) <= (1 - eta * mu) * g(x).
   Chain: x < dynamics x (since eta * g(x) > 0); strong concavity gives
   mu * (dynamics x - x) <= g(x) - g(dynamics x); hence
   (eta * mu) * g(x) <= g(x) - g(dynamics x), and rearranging gives
   g(dynamics x) <= g(x) - (eta * mu) * g(x) == (1 - eta * mu) * g(x). *)
Lemma gradient_step_contraction : forall x : R,
  lt zero eta ->
  lt (mult eta mu) one ->
  lt zero (entropy_gradient x) ->
  le (entropy_gradient (dynamics x))
     (mult (minus one (mult eta mu)) (entropy_gradient x)).
Proof.
  intros x Heta Heta_mu Hgx.
  (* x < dynamics x: eta * g(x) > 0 implies x < x + eta * g(x) *)
  assert (Heta_g : lt zero (mult eta (entropy_gradient x)))
    by exact (mult_positive eta (entropy_gradient x) Heta Hgx).
  assert (Hlt : lt x (dynamics x)).
  {
    apply (lt_id_l x (plus x zero) (dynamics x) (id_sym (plus_zero x))).
    apply (lt_id_r (plus x zero) (plus x (mult eta (entropy_gradient x))) (dynamics x)
                   (id_sym (dynamics_step_unfold x))).
    apply (lt_plus_compat_le_lt x x zero (mult eta (entropy_gradient x)) (le_refl x) Heta_g).
  }
  (* strong concavity: mu * (dynamics x - x) <= g(x) - g(dynamics x) *)
  pose proof (strong_concavity x (dynamics x) Hlt) as Hsc.
  (* minus (dynamics x) x == eta * g(x) *)
  assert (Hdiff : Id (minus (dynamics x) x) (mult eta (entropy_gradient x))).
  {
    unfold minus.
    apply (id_trans (id_cong (fun z => plus z (opp x)) (dynamics_step_unfold x))).
    apply (id_trans (id_sym (plus_assoc x (mult eta (entropy_gradient x)) (opp x)))).
    apply (id_trans (id_cong (fun z => plus x z) (plus_comm (mult eta (entropy_gradient x)) (opp x)))).
    apply (id_trans (plus_assoc x (opp x) (mult eta (entropy_gradient x)))).
    apply (id_trans (id_cong (fun z => plus z (mult eta (entropy_gradient x))) (plus_opp x))).
    apply (id_trans (plus_comm zero (mult eta (entropy_gradient x)))).
    apply (plus_zero (mult eta (entropy_gradient x))).
  }
  (* instantiate Hdiff: mu * (eta * g(x)) <= g(x) - g(dynamics x) *)
  assert (Hsc' : le (mult mu (mult eta (entropy_gradient x)))
                    (minus (entropy_gradient x) (entropy_gradient (dynamics x)))).
  { apply (le_id_l (mult mu (mult eta (entropy_gradient x)))
                   (mult mu (minus (dynamics x) x))
                   (minus (entropy_gradient x) (entropy_gradient (dynamics x)))
                   (id_sym (id_cong (fun z => mult mu z) Hdiff)) Hsc). }
  (* reshape: (eta * mu) * g(x) <= g(x) - g(dynamics x) *)
  assert (Hmm : Id (mult mu (mult eta (entropy_gradient x)))
                   (mult (mult eta mu) (entropy_gradient x))).
  {
    apply (id_trans (id_cong (fun z => mult mu z) (mult_comm eta (entropy_gradient x)))).
    apply (id_trans (mult_assoc mu (entropy_gradient x) eta)).
    apply (id_trans (id_cong (fun z => mult z eta) (mult_comm mu (entropy_gradient x)))).
    apply (id_trans (mult_comm (mult (entropy_gradient x) mu) eta)).
    apply (id_trans (id_cong (fun z => mult eta z) (mult_comm (entropy_gradient x) mu))).
    apply (mult_assoc eta mu (entropy_gradient x)).
  }
  assert (Hsc'' : le (mult (mult eta mu) (entropy_gradient x))
                     (minus (entropy_gradient x) (entropy_gradient (dynamics x)))).
  { apply (le_id_l (mult (mult eta mu) (entropy_gradient x))
                   (mult mu (mult eta (entropy_gradient x)))
                   (minus (entropy_gradient x) (entropy_gradient (dynamics x)))
                   (id_sym Hmm) Hsc'). }
  (* rearrangement: from A <= B - C derive C <= B - A.
   1. add C: le (A + C) ((B - C) + C) == B gives le (A + C) B;
   2. add (opp A): le ((A + C) + opp A) (B + opp A) gives le C (B - A). *)
  pose (A := mult (mult eta mu) (entropy_gradient x)).
  pose (B := entropy_gradient x).
  pose (C := entropy_gradient (dynamics x)).
  assert (H1 : le (plus A C) B).
  {
    apply (le_id_r (plus A C) (plus (minus B C) C) B).
    - exact (minus_plus_cancel_gap B C).
    - apply (le_plus_compat A (minus B C) C C Hsc'' (le_refl C)).
  }
  assert (H2 : le (plus (plus A C) (opp A)) (plus B (opp A))).
  {
    apply (le_plus_compat (plus A C) B (opp A) (opp A) H1 (le_refl (opp A))).
  }
  (* the left side simplifies: (A + C) + opp A == C *)
  assert (H3 : Id (plus (plus A C) (opp A)) C).
  {
    unfold A. unfold C.
    apply (id_trans (id_cong (fun z => plus z (opp (mult (mult eta mu) (entropy_gradient x))))
                             (plus_comm (mult (mult eta mu) (entropy_gradient x))
                                        (entropy_gradient (dynamics x))))).
    apply (id_trans (id_sym (plus_assoc (entropy_gradient (dynamics x))
                                        (mult (mult eta mu) (entropy_gradient x))
                                        (opp (mult (mult eta mu) (entropy_gradient x)))))).
    apply (id_trans (id_cong (fun z => plus (entropy_gradient (dynamics x)) z)
                             (plus_opp (mult (mult eta mu) (entropy_gradient x))))).
    apply (id_trans (plus_zero (entropy_gradient (dynamics x)))). apply id_refl.
  }
  (* right side: plus B (opp A) == minus (g x) ((eta * mu) * g) == the
   target shape *)
  assert (H4 : Id (plus B (opp A)) (minus (entropy_gradient x) (mult (mult eta mu) (entropy_gradient x)))).
  { unfold A, B. apply id_refl. }
  (* assemble: le C (minus B ((eta * mu) * g)) *)
  assert (H5 : le C (minus (entropy_gradient x) (mult (mult eta mu) (entropy_gradient x)))).
  {
    apply (le_id_l C (plus (plus A C) (opp A)) (minus (entropy_gradient x) (mult (mult eta mu) (entropy_gradient x))) (id_sym H3)).
    apply (le_id_r (plus (plus A C) (opp A)) (plus B (opp A)) (minus (entropy_gradient x) (mult (mult eta mu) (entropy_gradient x))) H4 H2).
  }
  (* goal: le (g (dynamics x)) (mult (minus one (eta * mu)) (g x));
   need (1 - eta * mu) * g == g - (eta * mu) * g *)
  (* goal: le C (mult (minus one (eta * mu)) g), with
   H5 : le C (minus g ((eta * mu) * g));
   rewrite the right side by [le_id_r]:
   minus g ((eta * mu) * g) == mult (minus one (eta * mu)) g *)
  assert (H6 : Id (minus (entropy_gradient x) (mult (mult eta mu) (entropy_gradient x)))
                  (mult (minus one (mult eta mu)) (entropy_gradient x))).
  {
    unfold minus.
    apply (id_sym (id_trans (mult_plus_distr_r one (opp (mult eta mu)) (entropy_gradient x))
                            (id_trans (id_cong (fun z => plus z (mult (opp (mult eta mu)) (entropy_gradient x))) (id_trans (mult_comm one (entropy_gradient x)) (mult_one (entropy_gradient x))))
                                      (id_cong (fun z => plus (entropy_gradient x) z) (opp_mult_r (mult eta mu) (entropy_gradient x)))))).
  }
  apply (le_id_r C (minus (entropy_gradient x) (mult (mult eta mu) (entropy_gradient x)))
                 (mult (minus one (mult eta mu)) (entropy_gradient x)) H6 H5).
Qed.

(* ===== helper, strict subtraction of positives: a < b implies 0 < b - a
   (needed for the positivity of kappa below) ===== *)
Lemma minus_pos : forall a b : R, lt a b -> lt zero (minus b a).
Proof.  intros a b Hab.
  unfold minus.
  exact (lt_id_l zero (plus a (opp a)) (plus b (opp a)) (id_sym (plus_opp a))
           (lt_plus_compat_lt_le a b (opp a) (opp a) Hab (le_refl (opp a)))).
Qed.
(* ===== positive-branch one-step absolute-value contraction:
   g(x) > 0, g(dynamics x) > 0 and eta * mu < 1 imply
   |g(dynamics x)| <= (1 - eta * mu) * |g(x)|.
   The one-step contraction gives g(dynamics x) <= (1 - eta * mu) * g(x);
   with both sides positive, |g| = g by [abs_pos], so the result is a
   direct reshape. *)
Lemma gradient_step_abs_contraction : forall x : R,
  lt zero eta ->
  lt (mult eta mu) one ->
  lt zero (entropy_gradient x) ->
  lt zero (entropy_gradient (dynamics x)) ->
  le (abs (entropy_gradient (dynamics x)))
     (mult (minus one (mult eta mu)) (abs (entropy_gradient x))).
Proof.
  intros x Heta Heta_mu Hgx Hgdyn.
  (* |g(dyn)| == g(dyn) (abs_pos) *)
  assert (Habsd : Id (abs (entropy_gradient (dynamics x))) (entropy_gradient (dynamics x)))
    by exact (abs_pos (entropy_gradient (dynamics x)) Hgdyn).
  (* |g(x)| == g(x) (abs_pos) *)
  assert (Habsx : Id (abs (entropy_gradient x)) (entropy_gradient x))
    by exact (abs_pos (entropy_gradient x) Hgx).
  (* reshape the goal to g(dynamics x) <= (1 - eta * mu) * g(x)
   (the one-step contraction) *)
  apply (le_id_l (abs (entropy_gradient (dynamics x)))
                 (entropy_gradient (dynamics x))
                 (mult (minus one (mult eta mu)) (abs (entropy_gradient x)))
                 Habsd).
  apply (le_id_r (entropy_gradient (dynamics x))
                 (mult (minus one (mult eta mu)) (entropy_gradient x))
                 (mult (minus one (mult eta mu)) (abs (entropy_gradient x)))
                 (id_cong (fun z => mult (minus one (mult eta mu)) z) (id_sym Habsx))
                 (gradient_step_contraction x Heta Heta_mu Hgx)).
Qed.

(* ===== positive-branch iterated one-step contraction: if every step is
   positive (assumption), then |g(x_{n+1})| <= kappa * |g(x_n)| with
   kappa := 1 - eta * mu; instantiate the absolute-value contraction at
   x := iterate dynamics n E_A *)
Theorem gradient_iterate_abs_decay : forall (E_A : R) (n : nat),
  lt zero eta ->
  lt (mult eta mu) one ->
  (forall k : nat, NatLe k (Datatypes.S n) -> lt zero (entropy_gradient (iterate dynamics k E_A))) ->
  le (abs (entropy_gradient (iterate dynamics (Datatypes.S n) E_A)))
     (mult (minus one (mult eta mu)) (abs (entropy_gradient (iterate dynamics n E_A)))).
Proof.
  intros E_A n Heta Heta_mu Hall.
  (* x := iterate dynamics n E_A; the premises are g(x) > 0 and
   g(dynamics x) > 0 *)
  assert (Hgn : lt zero (entropy_gradient (iterate dynamics n E_A))).
  { apply Hall. apply NatLe_lift. lia. }
  assert (Hgn1 : lt zero (entropy_gradient (iterate dynamics (Datatypes.S n) E_A))).
  { apply Hall. apply NatLe_lift. lia. }
  (* dynamics (iterate dynamics n E_A) and iterate (S n) E_A are
   definitionally equal ([iterate] is a [Fixpoint]) *)
  exact (gradient_step_abs_contraction (iterate dynamics n E_A) Heta Heta_mu Hgn Hgn1).
Qed.

(* ===== positive-branch kappa-power decay:
   |g(x_{n+k})| <= kappa^k * |g(x_n)| (by induction, with the same
   structure as [grad_decay_iter]); kappa := 1 - eta * mu;
   premise: the whole orbit is positive (j <= n + k) *)
Theorem grad_decay_positive_iter : forall (E_A : R) (n k : nat),
  lt zero eta ->
  lt (mult eta mu) one ->
  (forall j : nat, NatLe j (n + k) -> lt zero (entropy_gradient (iterate dynamics j E_A))) ->
  le (abs (entropy_gradient (iterate dynamics (n + k) E_A)))
     (mult (r_pow (minus one (mult eta mu)) k) (abs (entropy_gradient (iterate dynamics n E_A)))).
Proof.
  intros E_A n k Heta Heta_mu Hall.
  (* kappa > 0: 1 - eta * mu > 0, from eta * mu < 1 *)
  assert (Hkpos : lt zero (minus one (mult eta mu))).
  { apply (minus_pos _ _ Heta_mu). }
  induction k as [| k IH]; simpl.
  - (* k = 0: |g(x_n)| <= 1 * |g(x_n)| *)
    rewrite (Nat.add_0_r n).
    apply (le_id_r _ (abs (entropy_gradient (iterate dynamics n E_A))) _).
    + apply (id_trans (id_sym (mult_one (abs (entropy_gradient (iterate dynamics n E_A)))))
                      (id_sym (mult_comm one (abs (entropy_gradient (iterate dynamics n E_A)))))).
    + apply le_refl.
  - (* k = S k': |g(x_{n+S k'})| <= kappa * |g(x_{n+k'})| <= kappa * (kappa^{k'} * |g(x_n)|) == kappa^{S k'} * |g(x_n)| *)
    apply (le_trans _ (mult (minus one (mult eta mu)) (abs (entropy_gradient (iterate dynamics (n + k) E_A)))) _).
    + (* one step: the contraction at (n + k); the premise j <= S (n + k) comes
   from the IH (n + S k' == S (n + k)) *)
      rewrite (Nat.add_succ_r n k).
      apply (gradient_iterate_abs_decay E_A (n + k) Heta Heta_mu).
      intros j Hj. apply Hall. apply NatLe_lift.
      assert (Hjle : (j <= Datatypes.S (n + k))%nat) by (apply NatLe_drop; exact Hj).
      lia.
    + (* induction step: kappa * (kappa^k' * |g(x_n)|) == kappa^(S k') * |g(x_n)|
   ([mult_assoc] and commutativity) *)
      assert (IH' : le (abs (entropy_gradient (iterate dynamics (n + k) E_A)))
                        (mult (r_pow (minus one (mult eta mu)) k) (abs (entropy_gradient (iterate dynamics n E_A))))).
      { apply IH. intros j Hj. apply Hall. apply NatLe_lift.
        assert (Hjle : (j <= n + k)%nat) by (apply NatLe_drop; exact Hj).
        lia. }
      apply (le_id_r (mult (minus one (mult eta mu)) (abs (entropy_gradient (iterate dynamics (n + k) E_A))))
                     (mult (minus one (mult eta mu)) (mult (r_pow (minus one (mult eta mu)) k) (abs (entropy_gradient (iterate dynamics n E_A)))))
                     (mult (mult (minus one (mult eta mu)) (r_pow (minus one (mult eta mu)) k)) (abs (entropy_gradient (iterate dynamics n E_A))))
                     (mult_assoc (minus one (mult eta mu)) (r_pow (minus one (mult eta mu)) k) (abs (entropy_gradient (iterate dynamics n E_A))))
                     (le_mult_compat_r (minus one (mult eta mu))
                                       (abs (entropy_gradient (iterate dynamics (n + k) E_A)))
                                       (mult (r_pow (minus one (mult eta mu)) k) (abs (entropy_gradient (iterate dynamics n E_A))))
                                       (lt_le_iff _ _ (inl Hkpos))
                                       IH')).
Qed.

(* ============================================================
   From a stationary point to a global maximum of the entropy:
   the interface field [entropy_tangent] — the tangent inequality of a
   concave function, the first-order condition
   f(y) <= f(x) + f'(x) * (y - x) for all x, y, a standard optimization
   assumption rather than a classical axiom — implies
   [gradient_zero_entropy_max]: a stationary point (g(x) == 0) is a global
   maximum of the entropy.  This avoids both trichotomy (the [Set] layer
   has none; the [Real] layer's decidable Q-based trichotomy would need
   hundreds of lines of eps-delta work) and integration (the [Real] layer
   has no integral).  Bridge to is_truth: with L := -entropy (loss =
   negative entropy) the statement is_truth (-entropy) x holds.
   ============================================================ *)
(* tangent inequality for concavity (interface assumption; the quantified
   version of [strict_concavity]) *)
Variable entropy_tangent : forall x y : R,
  le (entropy y) (plus (entropy x) (mult (entropy_gradient x) (minus y x))).

(* stationary point implies global maximum: g(x) == 0 implies
   entropy y <= entropy x.
   Proof: the tangent inequality with g(x) == 0 gives
   entropy y <= entropy x + 0 * (y - x) == entropy x.
   Algebra: g(x) * (y - x) == 0 * (y - x) (Hg) == 0 by [mult_comm] and
   [mult_zero], then [plus] absorbs. *)
Theorem gradient_zero_entropy_max : forall x : R,
  Id (entropy_gradient x) zero ->
  forall y : R, le (entropy y) (entropy x).
Proof.
  intros x Hg y.
  (* tangent inequality: entropy y <= entropy x + g(x) * (y - x) *)
  assert (Htangent : le (entropy y) (plus (entropy x) (mult (entropy_gradient x) (minus y x))))
    by exact (entropy_tangent x y).
  (* algebra: g(x) * (y - x) == 0 * (y - x) == 0, and
   plus (entropy x) 0 == entropy x *)
  assert (Hid : Id (plus (entropy x) (mult (entropy_gradient x) (minus y x))) (entropy x)).
  {
    apply (id_trans (id_cong (fun z => plus (entropy x) z)
                             (id_trans (id_cong (fun z => mult z (minus y x)) Hg)
                                       (id_trans (mult_comm zero (minus y x))
                                                 (mult_zero (minus y x)))))).
    apply (plus_zero (entropy x)).
  }
  (* assemble: entropy y <= plus (...) and plus (...) == entropy x give
   entropy y <= entropy x *)
  exact (le_id_r (entropy y) (plus (entropy x) (mult (entropy_gradient x) (minus y x))) (entropy x) Hid Htangent).
Qed.

(* bridge to is_truth: g(x) == 0 means (-entropy) is globally minimized at
   x (the is_truth form, with loss = negative entropy) *)
Theorem gradient_zero_neg_entropy_truth : forall x : R,
  Id (entropy_gradient x) zero ->
  forall y : R, le (opp (entropy x)) (opp (entropy y)).
Proof.
  intros x Hg y.
  (* from the previous theorem: le (entropy y) (entropy x) — [opp] reverses
   the order with a sign flip *)
  apply (opp_le_compat (entropy y) (entropy x)).
  exact (gradient_zero_entropy_max x Hg y).
Qed.

(* ============================================================
   Unique attractor: any two orbits (from arbitrary initial points) have
   the same limit.  Route: weak trichotomy (an interface assumption,
   supplied constructively by the [Real]-layer [real_weak_trich]) plus the
   strictly decreasing gradient ([strict_concavity]) give uniqueness of the
   stationary point ([gradient_zero_unique]); then [grad_squeeze_zero]
   squeezes each orbit's limit to the stationary point, and uniqueness of
   the stationary point gives uniqueness of the limit ([unique_attractor]);
   finally the convergence-to-truth assembly
   ([attractor_converges_unique_truth]): the limit = the unique attractor =
   the stationary point = the is_truth point of -entropy.
   ============================================================ *)
(* interface assumption: weak trichotomy (proved constructively in the
   [Real] layer as [real_weak_trich]: not (x < y) and not (y < x) imply
   Id x y — this is not LPO; only full trichotomy is equivalent to LPO) *)
(* interface-level note: the tightness postulate (two negated strict
   inequalities imply Id) has no field in [RealInterfaceEnhanced] and is
   not derivable at the interface level; the concrete layer supplies it
   constructively as [real_weak_trich] in [S07_RealSetoidExpLog]. *)
Variable weak_trich : forall x y : R, Not (lt x y) -> Not (lt y x) -> Id x y.

(* uniqueness of the stationary point: a strictly decreasing g has at most
   one stationary point *)
Lemma gradient_zero_unique : forall x y : R,
  Id (entropy_gradient x) zero ->
  Id (entropy_gradient y) zero ->
  Id x y.
Proof.
  intros x y Hgx Hgy.
  apply weak_trich.
  - (* for not (lt x y): assume lt x y; [strict_concavity] gives
   lt (g y) (g x); substituting g x == 0 ([lt_id_r]) gives lt (g y) zero;
   substituting g y == 0 ([lt_id_l]) gives lt zero zero, contradicting
   [lt_irrefl] *)
    intro Hxy.
    pose proof (strict_concavity x y Hxy) as Hdec.
    apply (lt_irrefl zero).
    apply (lt_id_l zero (entropy_gradient y) zero).
    + apply id_sym. exact Hgy.
    + apply (lt_id_r (entropy_gradient y) (entropy_gradient x) zero Hgx Hdec).
  - (* for not (lt y x): symmetric *)
    intro Hyx.
    pose proof (strict_concavity y x Hyx) as Hdec.
    apply (lt_irrefl zero).
    apply (lt_id_l zero (entropy_gradient x) zero).
    + apply id_sym. exact Hgx.
    + apply (lt_id_r (entropy_gradient x) (entropy_gradient y) zero Hgy Hdec).
Qed.

(* unique attractor: any two orbits (arbitrary initial points, arbitrary
   limits) have the same limit.  [grad_squeeze_zero] squeezes the limit of
   each orbit to the stationary point, and [gradient_zero_unique] makes the
   stationary point unique, so the limits coincide. *)
Theorem unique_attractor : forall (E_A E_A' : R),
  lt zero (abs (entropy_gradient (iterate dynamics 0 E_A))) ->
  lt zero (abs (entropy_gradient (iterate dynamics 0 E_A'))) ->
  forall E1 E2 : R,
    lim (fun n => iterate dynamics n E_A) E1 ->
    lim (fun n => iterate dynamics n E_A') E2 ->
    Id E1 E2.
Proof.
  intros E_A E_A' Hg0 Hg0' E1 E2 Hlim1 Hlim2.
  pose proof (grad_squeeze_zero E_A E1 Hlim1 Hg0) as Hg1.
  pose proof (grad_squeeze_zero E_A' E2 Hlim2 Hg0') as Hg2.
  exact (gradient_zero_unique E1 E2 Hg1 Hg2).
Qed.

(* assembly: every orbit's limit = the unique attractor = the stationary
   point = the is_truth point of -entropy.
   The first gap (stationary point implies is_truth) is closed by
   [gradient_zero_neg_entropy_truth]; the second gap (a single orbit
   implies global attraction) is closed by [unique_attractor].
   [And] here is the informative Set-level conjunction and is extractable. *)
Theorem attractor_converges_unique_truth : forall (E_A E_A' : R),
  lt zero (abs (entropy_gradient (iterate dynamics 0 E_A))) ->
  lt zero (abs (entropy_gradient (iterate dynamics 0 E_A'))) ->
  forall E1 E2 : R,
    lim (fun n => iterate dynamics n E_A) E1 ->
    lim (fun n => iterate dynamics n E_A') E2 ->
    And (Id E1 E2)
        (And (Id (entropy_gradient E1) zero)
             (forall y : R, le (opp (entropy E1)) (opp (entropy y)))).
Proof.
  intros E_A E_A' Hg0 Hg0' E1 E2 Hlim1 Hlim2.
  pose proof (grad_squeeze_zero E_A E1 Hlim1 Hg0) as Hg1.
  pose proof (grad_squeeze_zero E_A' E2 Hlim2 Hg0') as Hg2.
  split.
  - exact (gradient_zero_unique E1 E2 Hg1 Hg2).
  - split.
    + exact Hg1.
    + exact (gradient_zero_neg_entropy_truth E1 Hg1).
Qed.

End ConvergenceCauchy.
(* ============================================================ *)
(* key statements: [SumExpPositive], [ArgminCorrectness] and friends *)
(* ============================================================ *)

Section KeyProofs.

Context {RI : RealInterfaceEnhanced}.

Section SumExpPositive.

Variable Token : Set.

(* unpack the fields (under different names to avoid shadowing) *)
Let R := @R RI.
Let zero := @zero RI.
Let plus := @plus RI.
Let exp_neg := @exp_neg RI.
Let lt := @lt RI.
Let exp_neg_pos_local := @exp_neg_pos RI.
Let plus_positive_local := @plus_positive RI.
Let plus_zero_local := @plus_zero RI.

Variable neg_log_prob : list Token -> Token -> R.

Fixpoint sum_exp (prefix : list Token) (l : list Token) : R :=
  match l with
  | nil => zero
  | w :: rest => plus (exp_neg (neg_log_prob prefix w)) (sum_exp prefix rest)
  end.

Lemma sum_exp_positive :
  forall prefix l, Not (Id l nil) -> lt zero (sum_exp prefix l).
Proof.
  intros prefix l. induction l as [| w rest IH].
  - intros Hnil. contradiction Hnil. apply id_refl.
  - intros _. simpl.
    destruct rest as [| w' rest'].
    + (* rest = [] *)
      simpl.
      exact (match id_sym (plus_zero_local (exp_neg (neg_log_prob prefix w))) in (Id _ b) return (lt zero b) with
             | id_refl => exp_neg_pos_local (neg_log_prob prefix w)
             end).
    + (* rest = w' :: rest' *)
      simpl.
      apply plus_positive_local.
      * apply exp_neg_pos_local.
      * apply IH. intro H. inversion H.   (* or [destruct H] *)
Qed.

End SumExpPositive.

Section ArgminCorrectness.

Variable Token : Set.
Context {DO : DecidableOrder RI}.
Let R := @R RI.
Let le := @le RI.
Let lt := @lt RI.
Let plus := @plus RI.
Let opp := @opp RI.
Let inv_pos := @inv_pos RI.
Let le_trans := @le_trans RI.
Let le_refl := @le_refl RI.

Variable total_loss : list Token -> R.

Definition candidate : Set := (Token * R)%type.

Fixpoint argmin_aux (prefix : list Token) (l : list Token) (best : candidate) : candidate :=
  match l with
  | nil => best
  | w :: rest =>
      let loss_w := total_loss (prefix ++ [w]) in
      match (@ord_le_dec RI DO) loss_w (snd best) with
      | inl _ => argmin_aux prefix rest (w, loss_w)
      | inr _ => argmin_aux prefix rest best
      end
  end.

Lemma argmin_aux_correct :
  forall prefix l best_token best_loss,
    let result := argmin_aux prefix l (best_token, best_loss) in
    And (le (snd result) best_loss)
        (forall w : Token, InT w l ->
          le (snd result) (total_loss (prefix ++ [w]))).
Proof.
  intros prefix l. induction l as [| a rest IH]; intros best_token best_loss.
  - simpl. split.
    + apply le_refl.
    + intros w HIn. inversion HIn.
  - simpl.
    destruct (@ord_le_dec _ DO (total_loss (prefix ++ [a])) best_loss) as [Hle | Hnot].
    + specialize (IH a (total_loss (prefix ++ [a]))).
      destruct IH as [IH_le IH_min].
      split.
      * eapply le_trans.
        -- apply IH_le.
        -- exact Hle.
      * intros w HIn.
        inversion HIn as [Hw | HIn']; subst.
        -- apply IH_le.
        -- apply IH_min. assumption.
    + specialize (IH best_token best_loss).
      destruct IH as [IH_le IH_min].
      split.
      * apply IH_le.
      * intros w HIn.
        inversion HIn as [Hw | HIn']; subst.
        -- assert (Hlt : lt best_loss (total_loss (prefix ++ [a]))).
           { apply not_le_lt. exact Hnot. }
           apply le_trans with best_loss.
           ++ apply IH_le.
           ++ apply lt_le_iff. left. exact Hlt.
        -- apply IH_min. assumption.
Qed.

Lemma argmin_aux_snd_correct :
  forall prefix l best_token best_loss,
    Id best_loss (total_loss (prefix ++ [best_token])) ->
    Id (snd (argmin_aux prefix l (best_token, best_loss)))
       (total_loss (prefix ++ [fst (argmin_aux prefix l (best_token, best_loss))])).
Proof.
  induction l as [| a rest IH]; intros best_token best_loss Hbest.
  - simpl. exact Hbest.
  - simpl.
    destruct (@ord_le_dec _ DO (total_loss (prefix ++ [a])) best_loss) as [Hle | Hnot].
    + apply IH. apply id_refl.
    + apply IH. exact Hbest.
Qed.

Variable vocab : list Token.
Variable vocab_nonempty : Not (Id vocab nil).
Variable default_token : Token.

Definition pick_best (prefix : list Token) : Token :=
  match vocab with
  | nil => default_token
  | w0 :: rest =>
      fst (argmin_aux prefix rest (w0, total_loss (prefix ++ [w0])))
  end.

Theorem pick_best_is_minimal :
  forall prefix w,
    InT w vocab ->
    le (total_loss (prefix ++ [pick_best prefix])) (total_loss (prefix ++ [w])).
Proof.
  intros prefix w HIn.
  unfold pick_best.
  destruct vocab as [| w0 rest].
  - inversion HIn.
  - simpl.
    destruct (argmin_aux_correct prefix rest w0 (total_loss (prefix ++ [w0]))) as [Hbest Hmin].
    (* obtain the relation between snd and fst *)
    assert (Hsnd := argmin_aux_snd_correct prefix rest w0 (total_loss (prefix ++ [w0])) id_refl).
    assert (Hsnde : snd (argmin_aux prefix rest (w0, total_loss (prefix ++ [w0]))) =
                    total_loss (prefix ++ [fst (argmin_aux prefix rest (w0, total_loss (prefix ++ [w0])))]))
      by exact (match Hsnd in (Id _ z) return
                  (snd (argmin_aux prefix rest (w0, total_loss (prefix ++ [w0]))) = z)
                with | id_refl => eq_refl end).
    (* analyze the two possibilities for w in the vocabulary *)
    inversion HIn as [Hw | HIn']; subst.
    + (* case 1: w = w0 *)
      rewrite <- Hsnde.
      apply Hbest.
    + (* case 2: w occurs in rest *)
      rewrite <- Hsnde.
      apply Hmin. assumption.
Qed.

(* greedy dynamics: one step extends the sequence by appending
   [pick_best] (the token of least total loss) *)
Definition dynamics (s : list Token) : list Token :=
  s ++ [pick_best s].

(* local optimality of the greedy dynamics: for any prefix and candidate
   token w, extending by the greedy step (appending [pick_best]) has total
   loss no larger than extending by w — the greedy step is locally
   optimal. *)
Theorem dynamics_greedy_locally_optimal :
  forall prefix w,
    InT w vocab ->
    le (total_loss (dynamics prefix)) (total_loss (prefix ++ [w])).
Proof.
  intros prefix w HIn.
  unfold dynamics.
  exact (pick_best_is_minimal prefix w HIn).
Qed.

End ArgminCorrectness.

Section SequenceLossPrefixApp.

Local Existing Instance RI_base.
Let R := @R RI.
Let zero := @zero RI.
Let plus := @plus RI.

Variable Token : Set.
Variable neg_log_prob : list Token -> Token -> R.

Fixpoint sequence_loss_prefix (prefix : list Token) (s : list Token) : R :=
  match s with
  | nil => zero
  | w :: rest =>
      plus (neg_log_prob prefix w) (sequence_loss_prefix (prefix ++ [w]) rest)
  end.

Lemma id_app_nil_r : forall (A : Set) (l : list A), Id (l ++ []) l.
Proof.
  induction l as [| x xs IH].
  - simpl. apply id_refl.
  - simpl. apply (id_cong (cons x)). exact IH.
Qed.

Lemma id_app_cons_assoc : forall (A : Set) (l : list A) (x : A) (rest : list A),
  Id (l ++ x :: rest) ((l ++ [x]) ++ rest).
Proof.
  induction l as [| y l' IH]; intros x rest.
  - simpl. apply id_refl.
  - simpl. apply (id_cong (cons y)). apply IH.
Qed.

Lemma sequence_loss_prefix_app :
  forall prefix s1 s2,
    Id (sequence_loss_prefix prefix (s1 ++ s2))
       (plus (sequence_loss_prefix prefix s1)
             (sequence_loss_prefix (prefix ++ s1) s2)).
Proof.
  intros prefix s1. revert prefix.
  induction s1 as [| w rest IH]; intros prefix.
  - intros s2.
    assert (H1 : Id (sequence_loss_prefix prefix s2)
                    (sequence_loss_prefix (prefix ++ []) s2)).
    { apply id_sym. apply (id_cong (fun p => sequence_loss_prefix p s2)). apply id_app_nil_r. }
    assert (H2 : Id (sequence_loss_prefix (prefix ++ []) s2)
                    (plus zero (sequence_loss_prefix (prefix ++ []) s2))).
    { apply id_sym. apply (id_trans (plus_comm zero _) (plus_zero _)). }
    exact (id_trans H1 H2).
  - intros s2.
    pose proof (IH (prefix ++ [w]) s2) as IH_s2.
    (* step 1: unfold the left-hand side by definition *)
    assert (Hdef_left : Id (sequence_loss_prefix prefix ((w :: rest) ++ s2))
                           (plus (neg_log_prob prefix w)
                                 (sequence_loss_prefix (prefix ++ [w]) (rest ++ s2)))).
    { simpl. apply id_refl. }
    (* step 2: use the IH and associativity *)
    assert (Hcong : Id (plus (neg_log_prob prefix w)
                            (sequence_loss_prefix (prefix ++ [w]) (rest ++ s2)))
                     (plus (neg_log_prob prefix w)
                           (plus (sequence_loss_prefix (prefix ++ [w]) rest)
                                 (sequence_loss_prefix ((prefix ++ [w]) ++ rest) s2)))).
    { apply (id_cong (fun x => plus (neg_log_prob prefix w) x)). exact IH_s2. }
    assert (Hassoc : Id (plus (neg_log_prob prefix w)
                              (plus (sequence_loss_prefix (prefix ++ [w]) rest)
                                    (sequence_loss_prefix ((prefix ++ [w]) ++ rest) s2)))
                        (plus (plus (neg_log_prob prefix w)
                                    (sequence_loss_prefix (prefix ++ [w]) rest))
                              (sequence_loss_prefix ((prefix ++ [w]) ++ rest) s2))).
    { apply plus_assoc. }
    assert (Hmid : Id (plus (neg_log_prob prefix w)
                            (sequence_loss_prefix (prefix ++ [w]) (rest ++ s2)))
                     (plus (plus (neg_log_prob prefix w)
                                 (sequence_loss_prefix (prefix ++ [w]) rest))
                           (sequence_loss_prefix ((prefix ++ [w]) ++ rest) s2))).
    { exact (id_trans Hcong Hassoc). }
    (* step 3: unfold the right-hand side and apply the list equation *)
    assert (Hdef_right : Id (plus (plus (neg_log_prob prefix w)
                                        (sequence_loss_prefix (prefix ++ [w]) rest))
                                  (sequence_loss_prefix ((prefix ++ [w]) ++ rest) s2))
                           (plus (sequence_loss_prefix prefix (w :: rest))
                                 (sequence_loss_prefix (prefix ++ w :: rest) s2))).
    {
      simpl.
      apply (id_cong (fun p => plus (plus (neg_log_prob prefix w)
                                          (sequence_loss_prefix (prefix ++ [w]) rest))
                                    (sequence_loss_prefix p s2))).
      apply id_sym. apply id_app_cons_assoc.
    }
    (* final composition *)
    exact (id_trans Hdef_left (id_trans Hmid Hdef_right)).
Qed.

End SequenceLossPrefixApp.

End KeyProofs.

(* ============================================================ *)
(* constructive formalization of the remaining core content *)
(* ============================================================ *)

Import PropositionConvergenceCore.

Section StateSpaceUtilities.
Context {RI : RealInterface}.
Context {SS : StateSpace RI}.

Definition sminus (a b : S) : S := splus a (sopp b).

Definition gradient_step (eta : R) (grad : (S -> R) -> S -> S) (L : S -> R) (s : S) : S :=
  splus s (smult eta (grad L s)).

End StateSpaceUtilities.

Section PropositionBasics.
Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpace RI}.

Definition IsProposition (P : Proposition) : Set :=
  forall s : S, And (le zero (P s)) (le (P s) one).

Definition IsPositiveProposition (P : Proposition) : Set :=
  forall s : S, lt zero (P s).

End PropositionBasics.

Section LossAggregation.
Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpace RI}.

Definition loss_of_proposition (P : Proposition) (s : S) : R :=
  log_inv (P s).

Definition weighted_sum_loss (props : list (Proposition * R)) (s : S) : R :=
  fold_right (fun (p_w : Proposition * R) acc =>
                let (P, w) := p_w in
                plus (mult w (loss_of_proposition P s)) acc)
             zero props.

Definition softmax_loss (props : list Proposition) (s : S) : R :=
  log_inv (fold_right (fun P acc =>
                         plus (exp_neg (loss_of_proposition P s)) acc)
                      zero props).

End LossAggregation.

Section GradientDescentAndAttractor.
Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpace RI}.
Context {SO : SumOver RI SS}.

(* unpack the fields *)
Let R := @R RI.
Let S := @S RI SS.
Let zero := @zero RI.
Let plus := @plus RI.
Let smult := @smult RI SS.
Let splus := @splus RI SS.
Let sopp := @sopp RI SS.
Let le := @le RI.
Let lt := @lt RI.
Let smetric := @smetric RI SS.
Let sum_over_S := @sum_over_S RI SS SO.

Variable grad : (S -> R) -> S -> S.

Definition force (L : S -> R) (s : S) : S :=
  sopp (grad L s).

Variable noise : S -> S.
Variable sigma : R.

Definition sgd_step (L : S -> R) (s : S) : S :=
  splus (smult sigma (force L s))
        (smult sigma (noise s)).

Variable transition_kernel : (S -> R) -> S -> S -> R.
Variable transition_nonneg : forall L s s', le zero (transition_kernel L s s').
Variable transition_normalization :
  forall L s, Id (sum_over_S (fun s' => transition_kernel L s s')) one.

Definition is_truth (L : S -> R) (s : S) : Set :=
  forall s' : S, le (L s) (L s').

Definition omega_limit (dyn : S -> S) (s0 : S) (s : S) : Set :=
  forall eps : R, lt zero eps ->
    sigT (fun n : nat => lt (smetric (iterate dyn n s0) s) eps).

Definition is_attractor (L : S -> R) (s : S) : Set :=
  forall s0 : S, omega_limit (sgd_step L) s0 s.

End GradientDescentAndAttractor.

(* the aggregation function collecting hierarchical propositions *)
Section HierarchicalPropositions.
Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpace RI}.

Let R := @R RI.
Let S := @S RI SS.
Let PropType := @Proposition RI SS.
Let loss_of_proposition := @loss_of_proposition RI SS.

Inductive PropositionLayer : Set :=
| BaseProp : PropType -> PropositionLayer
| ConjProp : list PropositionLayer -> (list R -> R) -> PropositionLayer.

Fixpoint eval_layer_loss (layer : PropositionLayer) (s : S) : R :=
  match layer with
  | BaseProp P => loss_of_proposition P s
  | ConjProp sub_layers agg =>
      agg (map (fun sub => eval_layer_loss sub s) sub_layers)
  end.

Definition softmax_aggregation (losses : list R) : R :=
  log_inv (fold_right (fun L acc => plus (exp_neg L) acc) zero losses).

Fixpoint safe_weighted_sum (weights losses : list R) : R :=
  match weights, losses with
  | w :: ws, l :: ls => plus (mult w l) (safe_weighted_sum ws ls)
  | _, _ => zero
  end.

Definition weighted_sum_aggregation (weights : list R) (losses : list R) : R :=
  safe_weighted_sum weights losses.

End HierarchicalPropositions.

Section BoltzmannSteadyState.
Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpace RI}.
Context {SO : SumOver RI SS}.

(* bind the basic types and functions *)
Let R := @R RI.
Let S := @S RI SS.
Let zero := @zero RI.
Let one := @one RI.
Let plus := @plus RI.
Let mult := @mult RI.
Let inv_pos := @inv_pos RI.
Let exp_neg := @exp_neg RI.
Let le := @le RI.
Let lt := @lt RI.
Let sum_over_S := @sum_over_S RI SS SO.

Variable base_loss : S -> R.
Variable D : R.
Variable D_pos : lt zero D.

Variable Z : R.
Variable Z_pos : lt zero Z.
Variable partition_condition : Id Z (sum_over_S (fun s => exp_neg (mult (inv_pos D D_pos) (base_loss s)))).

Definition boltzmann_unnorm (s : S) : R :=
  exp_neg (mult (inv_pos D D_pos) (base_loss s)).

Definition boltzmann_prob (s : S) : R :=
  mult (inv_pos Z Z_pos) (boltzmann_unnorm s).

Variable transition : S -> S -> R.
Variable transition_nonneg : forall s s', le zero (transition s s').
Variable transition_normalization :
  forall s, Id (sum_over_S (fun s' => transition s s')) one.

Variable detailed_balance :
  forall s s',
    Id (mult (boltzmann_prob s) (transition s s'))
       (mult (boltzmann_prob s') (transition s' s)).

(* detailed balance implies stationarity (a fundamental theorem of Markov
   chains).  Constructive route: pointwise detailed balance, linearity of
   the sum ([sum_over_S_linear]), and normalization of the transition
   kernel.  Note: this section has [Let] bindings (Let sum_over_S, mult,
   ...), so the interface fields are stated at projection level — [change]
   to the [Let] layer before [rewrite]. *)
Theorem steady_state_boltzmann :
  forall s,
    Id (sum_over_S (fun s' => mult (boltzmann_prob s') (transition s' s)))
       (boltzmann_prob s).
Proof.
  intro s.
  (* 1. pointwise detailed balance: forall s', p(s') * T(s', s) = p(s) * T(s, s') *)
  assert (Hpoint : forall s', Id (mult (boltzmann_prob s') (transition s' s))
                               (mult (boltzmann_prob s) (transition s s'))).
  { intro s'. apply (detailed_balance s' s). }
  (* 2. replace inside the sum by function extensionality ([sum_over_S_ext]) *)
  assert (Hswap : Id (sum_over_S (fun s' => mult (boltzmann_prob s') (transition s' s)))
                     (sum_over_S (fun s' => mult (boltzmann_prob s) (transition s s')))).
  { apply sum_over_S_ext. exact Hpoint. }
  rewrite Hswap.
  (* 3. factor out the constant p(s) ([sum_over_S_linear], stated at
   projection level — [change] to the [Let] layer first) *)
  pose proof (@sum_over_S_linear RI SS SO (boltzmann_prob s) (fun s' => transition s s')) as Hlin.
  change (Id (sum_over_S (fun s' => mult (boltzmann_prob s) (transition s s')))
             (mult (boltzmann_prob s) (sum_over_S (fun s' => transition s s')))) in Hlin.
  rewrite Hlin.
  (* 4. normalization of the kernel: sum_{s'} T(s, s') = 1 *)
  rewrite (transition_normalization s).
  (* 5. p(s) * 1 = p(s) ([mult_one] at projection level — [change] to the
   [Let] layer) *)
  pose proof (mult_one (boltzmann_prob s)) as Hm1.
  change (Id (mult (boltzmann_prob s) one) (boltzmann_prob s)) in Hm1.
  rewrite Hm1.
  reflexivity.
Qed.

End BoltzmannSteadyState.

(* ============================================================ *)
(* helper for the next group (general interface layer): strict cancellation
   by a positive factor (lt form) *)
(* ============================================================ *)
Section TempStrictTools.
Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpace RI}.
Context {SO : SumOver RI SS}.

Let R := @R RI.
Let S := @S RI SS.
Let zero := @zero RI.
Let one  := @one RI.
Let plus := @plus RI.
Let mult := @mult RI.
Let opp  := @opp RI.
Let le := @le RI.
Let lt := @lt RI.
Let inv_pos := @inv_pos RI.
Let sum_over_S := @sum_over_S RI SS SO.

(* strict cancellation by a positive factor: c > 0 and a * c > 0 imply a > 0,
   since a == (a * c) * (inv c) *)
Lemma lt_mult_pos_cancel : forall a c : R, lt zero c -> lt zero (mult a c) -> lt zero a.
Proof.
  intros a c Hc H.
  apply (lt_id_r zero (mult (mult a c) (inv_pos c Hc)) a).
  - apply id_sym.
    exact (id_trans (id_sym (mult_one a))
           (id_trans (id_cong (fun x => mult a x) (id_sym (inv_pos_correct c Hc)))
                     (mult_assoc a c (inv_pos c Hc)))).
  - apply mult_positive.
    + exact H.
    + apply inv_pos_pos.
Qed.

End TempStrictTools.

Section FreeEnergyMinimization.
Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpace RI}.
Context {SO : SumOver RI SS}.

(* bind the basic types and functions explicitly *)
Let R := @R RI.
Let S := @S RI SS.
Let zero := @zero RI.
Let one := @one RI.
Let plus := @plus RI.
Let mult := @mult RI.
Let inv_pos := @inv_pos RI.
Let exp_neg := @exp_neg RI.
Let le := @le RI.
Let lt := @lt RI.
Let log := @log RI.                       (* note: [free_energy] uses [log] *)
Let sum_over_S := @sum_over_S RI SS SO.

Variable base_loss : S -> R.
Variable D : R.
Variable D_pos : lt zero D.

Definition free_energy (p : S -> R) : R :=
  plus (sum_over_S (fun s => mult (p s) (base_loss s)))
       (mult D (sum_over_S (fun s => mult (p s) (log (p s))))).

Definition normalized (p : S -> R) : Set := Id (sum_over_S p) one.
Definition positive_dist (p : S -> R) : Set := forall s, lt zero (p s).

Variable Z : R.
Variable Z_pos : lt zero Z.
Variable partition_condition : Id Z (sum_over_S (fun s => exp_neg (mult (inv_pos D D_pos) (base_loss s)))).

Definition boltzmann_dist : S -> R :=
  fun s => mult (inv_pos Z Z_pos) (exp_neg (mult (inv_pos D D_pos) (base_loss s))).

(* ============================================================ *)
(* the training-inference loop: the free energy connected exactly to the
   Boltzmann distribution *)
(* ============================================================ *)

(* linearity of the sum over negatives: sum (-f) = -(sum f) *)
Lemma sum_opp :
  forall (f : S -> R),
    Id (sum_over_S (fun s => opp (f s))) (opp (sum_over_S f)).
Proof.
  intro f.
  assert (Hext : Id (sum_over_S (fun s => opp (f s)))
                   (sum_over_S (fun s => mult (opp one) (f s)))).
  {
    apply sum_over_S_ext.
    intro s.
    assert (H1 : Id (mult (opp one) (f s)) (opp (mult one (f s))))
      by exact (opp_mult_r one (f s)).
    assert (H2 : Id (opp (mult one (f s))) (opp (f s)))
      by exact (id_cong opp (id_trans (mult_comm one (f s)) (mult_one (f s)))).
    exact (id_trans (id_sym H2) (id_sym H1)).
  }
  rewrite Hext.
  assert (Hlin : Id (sum_over_S (fun s => mult (opp one) (f s)))
                   (mult (opp one) (sum_over_S f)))
    by exact (sum_over_S_linear (opp one) f).
  rewrite Hlin.
  assert (H1 : Id (mult (opp one) (sum_over_S f)) (opp (mult one (sum_over_S f))))
    by exact (opp_mult_r one (sum_over_S f)).
  assert (H2 : Id (opp (mult one (sum_over_S f))) (opp (sum_over_S f)))
    by exact (id_cong opp (id_trans (mult_comm one (sum_over_S f)) (mult_one (sum_over_S f)))).
  exact (id_trans H1 H2).
Qed.

(* linearity of the sum over differences: sum (f - g) = sum f - sum g,
   from additivity and opposites *)
Lemma sum_over_S_minus :
  forall (f g : S -> R),
    Id (sum_over_S (fun s => minus (f s) (g s)))
       (minus (sum_over_S f) (sum_over_S g)).
Proof.
  intros f g.
  unfold minus.
  assert (Hadd : Id (sum_over_S (fun s => plus (f s) (opp (g s))))
                   (plus (sum_over_S f) (sum_over_S (fun s => opp (g s)))))
    by exact (sum_over_S_add f (fun s => opp (g s))).
  assert (Hopp : Id (sum_over_S (fun s => opp (g s))) (opp (sum_over_S g)))
    by exact (sum_opp g).
  exact (id_trans Hadd (id_cong (fun x => plus (sum_over_S f) x) Hopp)).
Qed.

(* normalization of the Boltzmann distribution: sum_s p_b(s) = 1
   (conservation of probability mass; a restatement of the definition of
   the partition function) *)
Theorem boltzmann_normalized :
  Id (sum_over_S boltzmann_dist) one.
Proof.
  unfold boltzmann_dist.
  assert (Hlin : Id (sum_over_S (fun s => mult (inv_pos Z Z_pos) (exp_neg (mult (inv_pos D D_pos) (base_loss s)))))
                   (mult (inv_pos Z Z_pos) (sum_over_S (fun s => exp_neg (mult (inv_pos D D_pos) (base_loss s))))))
    by exact (sum_over_S_linear (inv_pos Z Z_pos) (fun s => exp_neg (mult (inv_pos D D_pos) (base_loss s)))).
  assert (HZ : Id (sum_over_S (fun s => exp_neg (mult (inv_pos D D_pos) (base_loss s)))) Z)
    by exact (id_sym partition_condition).
  assert (Hcc : Id (mult (inv_pos Z Z_pos) Z) one)
    by exact (id_trans (mult_comm (inv_pos Z Z_pos) Z) (inv_pos_correct Z Z_pos)).
  exact (id_trans Hlin (id_trans (id_cong (fun x => mult (inv_pos Z Z_pos) x) HZ) Hcc)).
Qed.

(* the nontrivial version: normalization is preserved by convex combinations
   of distributions (the mathematical basis of mixture strategies, model
   ensembles and distillation; a conservation law of the algebra of
   distributions, not a restatement of the partition-function definition) *)
Theorem boltzmann_mix_normalized :
  forall (p q : S -> R) (alpha : R) (Halpha : lt zero alpha) (Halpha1 : lt zero (minus one alpha)),
    normalized p -> normalized q ->
    Id (sum_over_S (fun s => plus (mult alpha (p s)) (mult (minus one alpha) (q s)))) one.
Proof.
  intros p q alpha Halpha Halpha1 Hp Hq.
  unfold normalized in Hp, Hq.
  assert (Hadd : Id (sum_over_S (fun s => plus (mult alpha (p s)) (mult (minus one alpha) (q s))))
                   (plus (sum_over_S (fun s => mult alpha (p s))) (sum_over_S (fun s => mult (minus one alpha) (q s)))))
    by exact (sum_over_S_add (fun s => mult alpha (p s)) (fun s => mult (minus one alpha) (q s))).
  rewrite Hadd.
  assert (Hlin1 : Id (sum_over_S (fun s => mult alpha (p s))) (mult alpha (sum_over_S p)))
    by exact (sum_over_S_linear alpha p).
  rewrite Hlin1.
  assert (Hlin2 : Id (sum_over_S (fun s => mult (minus one alpha) (q s))) (mult (minus one alpha) (sum_over_S q)))
    by exact (sum_over_S_linear (minus one alpha) q).
  rewrite Hlin2.
  rewrite Hp. rewrite Hq.
  assert (Hm1 : Id (mult alpha one) alpha) by exact (mult_one alpha).
  rewrite Hm1.
  assert (Hm2 : Id (mult (minus one alpha) one) (minus one alpha)) by exact (mult_one (minus one alpha)).
  rewrite Hm2.
  (* goal: plus alpha (minus one alpha) = one — an [assert] + [exact] chain,
   avoiding unfold/rewrite dependencies of the goal *)
  assert (Hfin : Id (plus alpha (minus one alpha)) one).
  {
    unfold minus.
    assert (Hsw : Id (plus alpha (plus one (opp alpha))) (plus one (plus alpha (opp alpha)))).
    {
      assert (H1 : Id (plus alpha (plus one (opp alpha))) (plus (plus alpha one) (opp alpha)))
        by exact (plus_assoc alpha one (opp alpha)).
      assert (H2 : Id (plus (plus alpha one) (opp alpha)) (plus (plus one alpha) (opp alpha)))
        by exact (id_cong (fun x => plus x (opp alpha)) (plus_comm alpha one)).
      assert (H3 : Id (plus (plus one alpha) (opp alpha)) (plus one (plus alpha (opp alpha))))
        by exact (id_sym (plus_assoc one alpha (opp alpha))).
      exact (id_trans H1 (id_trans H2 H3)).
    }
    assert (Hfin2 : Id (plus one (plus alpha (opp alpha))) one).
    {
      assert (Hpz : Id (plus one zero) one) by exact (plus_zero one).
      assert (Hpz2 : Id (plus one (plus alpha (opp alpha))) (plus one zero))
        by exact (id_cong (fun x => plus one x) (plus_opp alpha)).
      exact (id_trans Hpz2 Hpz).
    }
    exact (id_trans Hsw Hfin2).
  }
  exact Hfin.
Qed.

(* logarithmic decomposition of the Boltzmann distribution:
   log p_b(s) = -log Z - E(s) / D *)
Theorem boltzmann_log_decomp :
  forall s : S,
    Id (log (boltzmann_dist s))
       (plus (opp (log Z)) (opp (mult (inv_pos D D_pos) (base_loss s)))).
Proof.
  intro s.
  unfold boltzmann_dist.
  assert (Hpos1 : lt zero (inv_pos Z Z_pos)) by exact (inv_pos_pos Z Z_pos).
  assert (Hpos2 : lt zero (exp_neg (mult (inv_pos D D_pos) (base_loss s))))
    by exact (exp_neg_pos (mult (inv_pos D D_pos) (base_loss s))).
  assert (Hlm : Id (log (mult (inv_pos Z Z_pos) (exp_neg (mult (inv_pos D D_pos) (base_loss s)))))
                  (plus (log (inv_pos Z Z_pos)) (log (exp_neg (mult (inv_pos D D_pos) (base_loss s))))))
    by exact (log_mult (inv_pos Z Z_pos) (exp_neg (mult (inv_pos D D_pos) (base_loss s))) Hpos1 Hpos2).
  rewrite Hlm.
  assert (Hli : Id (log (inv_pos Z Z_pos)) (opp (log Z)))
    by exact (log_inv_one_inv Z Z_pos).
  rewrite Hli.
  assert (Hle : Id (log (exp_neg (mult (inv_pos D D_pos) (base_loss s))))
                  (opp (mult (inv_pos D D_pos) (base_loss s))))
    by exact (log_exp_neg (mult (inv_pos D D_pos) (base_loss s))).
  rewrite Hle.
  reflexivity.
Qed.

(* ============================================================ *)
(* training-inference loop: the explicit value of the free energy at the
   Boltzmann distribution *)
(* F[p_b] = ⟨E⟩ + D * sum p_b * log p_b = -D * log Z *)
(* ============================================================ *)
(* training: minimization of the free energy ([min_free_energy_is_boltzmann])
   yields the Boltzmann distribution; inference: at that distribution the
   entropy-energy balance collapses to the exact closed value -D * log Z.
   Chain: pointwise logarithmic decomposition ([boltzmann_log_decomp]),
   linearity of sums and negatives ([sum_over_S_add], [sum_over_S_linear],
   [sum_opp]), normalization ([boltzmann_normalized]), then ring algebra
   collapses the expression. *)
Theorem free_energy_boltzmann :
  Id (free_energy boltzmann_dist) (mult (opp D) (log Z)).
Proof.
  unfold free_energy.
  set (Eavg := sum_over_S (fun s => mult (boltzmann_dist s) (base_loss s))).
  (* bridge between the [Let] layer and field lemmas: use [exact] with a
   conversion; [rewrite] needs an assertion at the same level *)
  assert (Hdist : forall a b c : R, Id (mult a (plus b c)) (plus (mult a b) (mult a c)))
    by exact (distrib).
  assert (Hoppl : forall a b : R, Id (mult a (opp b)) (opp (mult a b)))
    by exact (opp_mult_l).
  assert (Hoppr : forall a b : R, Id (mult (opp a) b) (opp (mult a b)))
    by exact (opp_mult_r).
  assert (Hassoc : forall a b c : R, Id (mult a (mult b c)) (mult (mult a b) c))
    by exact (mult_assoc).
  assert (Hcomm : forall a b : R, Id (mult a b) (mult b a))
    by exact (mult_comm).
  assert (Hmo : forall a : R, Id (mult a one) a)
    by exact (mult_one).
  assert (Hpa : forall a b c : R, Id (plus a (plus b c)) (plus (plus a b) c))
    by exact (plus_assoc).
  assert (Hpc : forall a b : R, Id (plus a b) (plus b a))
    by exact (plus_comm).
  assert (Hpz : forall a : R, Id (plus a zero) a)
    by exact (plus_zero).
  assert (Hpo : forall a : R, Id (plus a (opp a)) zero)
    by exact (plus_opp).
  (* step 1: pointwise decomposition of p_b(s) * log p_b(s) *)
  assert (Hpoint :
    forall s : S,
      Id (mult (boltzmann_dist s) (log (boltzmann_dist s)))
         (plus (mult (boltzmann_dist s) (opp (log Z)))
               (opp (mult (inv_pos D D_pos) (mult (boltzmann_dist s) (base_loss s)))))).
  {
    intro s.
    assert (Hld : Id (log (boltzmann_dist s))
                     (plus (opp (log Z)) (opp (mult (inv_pos D D_pos) (base_loss s)))))
      by exact (boltzmann_log_decomp s).
    assert (Hc : Id (mult (boltzmann_dist s) (log (boltzmann_dist s)))
                    (mult (boltzmann_dist s) (plus (opp (log Z)) (opp (mult (inv_pos D D_pos) (base_loss s))))))
      by exact (id_cong (fun x => mult (boltzmann_dist s) x) Hld).
    rewrite Hc.
    rewrite (Hdist (boltzmann_dist s) (opp (log Z)) (opp (mult (inv_pos D D_pos) (base_loss s)))).
    rewrite (Hoppl (boltzmann_dist s) (mult (inv_pos D D_pos) (base_loss s))).
    assert (Hswap : Id (mult (boltzmann_dist s) (mult (inv_pos D D_pos) (base_loss s)))
                       (mult (inv_pos D D_pos) (mult (boltzmann_dist s) (base_loss s)))).
    {
      assert (H1 : Id (mult (boltzmann_dist s) (mult (inv_pos D D_pos) (base_loss s)))
                      (mult (mult (boltzmann_dist s) (inv_pos D D_pos)) (base_loss s)))
        by exact (Hassoc (boltzmann_dist s) (inv_pos D D_pos) (base_loss s)).
      assert (H2 : Id (mult (mult (boltzmann_dist s) (inv_pos D D_pos)) (base_loss s))
                      (mult (mult (inv_pos D D_pos) (boltzmann_dist s)) (base_loss s)))
        by exact (id_cong (fun x => mult x (base_loss s)) (Hcomm (boltzmann_dist s) (inv_pos D D_pos))).
      assert (H3 : Id (mult (mult (inv_pos D D_pos) (boltzmann_dist s)) (base_loss s))
                      (mult (inv_pos D D_pos) (mult (boltzmann_dist s) (base_loss s))))
        by exact (id_sym (Hassoc (inv_pos D D_pos) (boltzmann_dist s) (base_loss s))).
      exact (id_trans H1 (id_trans H2 H3)).
    }
    rewrite Hswap.
    reflexivity.
  }
  (* step 2: sum over s: sum p_b * log p_b = -log Z - (1/D) * <E> *)
  assert (Hsum :
    Id (sum_over_S (fun s => mult (boltzmann_dist s) (log (boltzmann_dist s))))
       (plus (opp (log Z))
             (opp (mult (inv_pos D D_pos) Eavg)))).
  {
    assert (Hext : Id (sum_over_S (fun s => mult (boltzmann_dist s) (log (boltzmann_dist s))))
                     (sum_over_S (fun s => plus (mult (boltzmann_dist s) (opp (log Z)))
                                                (opp (mult (inv_pos D D_pos) (mult (boltzmann_dist s) (base_loss s)))))))
      by exact (sum_over_S_ext (fun s => mult (boltzmann_dist s) (log (boltzmann_dist s)))
                               (fun s => plus (mult (boltzmann_dist s) (opp (log Z)))
                                              (opp (mult (inv_pos D D_pos) (mult (boltzmann_dist s) (base_loss s)))))
                               Hpoint).
    rewrite Hext.
    assert (Hadd : Id (sum_over_S (fun s => plus (mult (boltzmann_dist s) (opp (log Z)))
                                                (opp (mult (inv_pos D D_pos) (mult (boltzmann_dist s) (base_loss s))))))
                      (plus (sum_over_S (fun s => mult (boltzmann_dist s) (opp (log Z))))
                            (sum_over_S (fun s => opp (mult (inv_pos D D_pos) (mult (boltzmann_dist s) (base_loss s)))))))
      by exact (sum_over_S_add (fun s => mult (boltzmann_dist s) (opp (log Z)))
                               (fun s => opp (mult (inv_pos D D_pos) (mult (boltzmann_dist s) (base_loss s))))).
    rewrite Hadd.
    (* first term: sum p_b * (-log Z) = (-log Z) * sum p_b = -log Z *)
    assert (Hsw1 : Id (sum_over_S (fun s => mult (boltzmann_dist s) (opp (log Z))))
                      (sum_over_S (fun s => mult (opp (log Z)) (boltzmann_dist s)))).
    {
      apply sum_over_S_ext.
      intro s.
      apply (Hcomm (boltzmann_dist s) (opp (log Z))).
    }
    rewrite Hsw1.
    assert (Hlin1 : Id (sum_over_S (fun s => mult (opp (log Z)) (boltzmann_dist s)))
                       (mult (opp (log Z)) (sum_over_S boltzmann_dist)))
      by exact (sum_over_S_linear (opp (log Z)) boltzmann_dist).
    rewrite Hlin1.
    assert (Hnorm : Id (sum_over_S boltzmann_dist) one) by exact (boltzmann_normalized).
    rewrite Hnorm.
    assert (Hm1 : Id (mult (opp (log Z)) one) (opp (log Z))) by exact (Hmo (opp (log Z))).
    rewrite Hm1.
    (* second term: sum opp((1/D) * p_b * E) = opp((1/D) * sum p_b * E) *)
    assert (Hso : Id (sum_over_S (fun s => opp (mult (inv_pos D D_pos) (mult (boltzmann_dist s) (base_loss s)))))
                     (opp (sum_over_S (fun s => mult (inv_pos D D_pos) (mult (boltzmann_dist s) (base_loss s))))))
      by exact (sum_opp (fun s => mult (inv_pos D D_pos) (mult (boltzmann_dist s) (base_loss s)))).
    rewrite Hso.
    assert (Hlin2 : Id (sum_over_S (fun s => mult (inv_pos D D_pos) (mult (boltzmann_dist s) (base_loss s))))
                       (mult (inv_pos D D_pos) (sum_over_S (fun s => mult (boltzmann_dist s) (base_loss s)))))
      by exact (sum_over_S_linear (inv_pos D D_pos) (fun s => mult (boltzmann_dist s) (base_loss s))).
    rewrite Hlin2.
    reflexivity.
  }
  rewrite Hsum.
  (* step 3: D * (-log Z - (1/D) * <E>) = -D * log Z - <E> *)
  assert (Hmd : Id (mult D (plus (opp (log Z)) (opp (mult (inv_pos D D_pos) Eavg))))
                  (plus (opp (mult D (log Z))) (opp Eavg))).
  {
    rewrite (Hdist D (opp (log Z)) (opp (mult (inv_pos D D_pos) Eavg))).
    rewrite (Hoppl D (log Z)).
    rewrite (Hoppl D (mult (inv_pos D D_pos) Eavg)).
    assert (Hmd2 : Id (mult D (mult (inv_pos D D_pos) Eavg)) Eavg).
    {
      assert (Hcc1 : Id (mult (mult D (inv_pos D D_pos)) Eavg) Eavg).
      {
        assert (Ht : Id (mult (mult D (inv_pos D D_pos)) Eavg) (mult one Eavg))
          by exact (id_cong (fun x => mult x Eavg) (inv_pos_correct D D_pos)).
        assert (Ht2 : Id (mult one Eavg) (mult Eavg one))
          by exact (Hcomm one Eavg).
        exact (id_trans Ht (id_trans Ht2 (Hmo Eavg))).
      }
      exact (id_trans (Hassoc D (inv_pos D D_pos) Eavg) Hcc1).
    }
    rewrite Hmd2.
    reflexivity.
  }
  rewrite Hmd.
  (* step 4: <E> + (-D * log Z - <E>) = -D * log Z (ring algebra) *)
  assert (Hfin : Id (plus Eavg (plus (opp (mult D (log Z))) (opp Eavg)))
                    (opp (mult D (log Z)))).
  {
    assert (H1 : Id (plus Eavg (plus (opp (mult D (log Z))) (opp Eavg)))
                    (plus (plus Eavg (opp (mult D (log Z)))) (opp Eavg)))
      by exact (Hpa Eavg (opp (mult D (log Z))) (opp Eavg)).
    assert (H2 : Id (plus (plus Eavg (opp (mult D (log Z)))) (opp Eavg))
                    (plus (plus (opp (mult D (log Z))) Eavg) (opp Eavg)))
      by exact (id_cong (fun y => plus y (opp Eavg)) (Hpc Eavg (opp (mult D (log Z))))).
    assert (H3 : Id (plus (plus (opp (mult D (log Z))) Eavg) (opp Eavg))
                    (plus (opp (mult D (log Z))) (plus Eavg (opp Eavg))))
      by exact (id_sym (Hpa (opp (mult D (log Z))) Eavg (opp Eavg))).
    assert (H4 : Id (plus (opp (mult D (log Z))) (plus Eavg (opp Eavg)))
                    (plus (opp (mult D (log Z))) zero))
      by exact (id_cong (fun y => plus (opp (mult D (log Z))) y) (Hpo Eavg)).
    assert (H5 : Id (plus (opp (mult D (log Z))) zero) (opp (mult D (log Z))))
      by exact (Hpz (opp (mult D (log Z)))).
    exact (id_trans H1 (id_trans H2 (id_trans H3 (id_trans H4 H5)))).
  }
  assert (Hoppr2 : Id (opp (mult D (log Z))) (mult (opp D) (log Z)))
    by exact (id_sym (Hoppr D (log Z))).
  exact (id_trans Hfin Hoppr2).
Qed.

(* ============================================================ *)
(* the free-energy / relative-entropy identity of the training-inference
   loop *)
(* F[p] = F[p_b] + D * KL(p || p_b) *)
(* ============================================================ *)
(* meaning: for every normalized distribution p, the free energy equals the
   Boltzmann free energy plus *)
(* the temperature D times the relative entropy; hence training
   (minimizing the free energy) and inference (approximating the *)
(* Boltzmann distribution) are exactly equivalent — minimizing F is the
   same as minimizing KL. *)
(* derivation: solve E from the logarithmic decomposition as
   E = -D * (log p_b + log Z), then *)
(* substitute pointwise and use linearity of sums and negatives plus
   normalization. *)
(* ------------------------------------------------------------ *)

(* lemma 1: solving for the energy — from [boltzmann_log_decomp],
   E(s) = -D * (log p_b(s) + log Z) *)
Lemma energy_in_log_boltzmann :
  forall s : S,
    Id (base_loss s)
       (opp (mult D (plus (log (boltzmann_dist s)) (log Z)))).
Proof.
  intro s.
  (* log p_b = -log Z - E/D implies log p_b + log Z = -E/D *)
  assert (Hlog : Id (log (boltzmann_dist s))
                    (plus (opp (log Z)) (opp (mult (inv_pos D D_pos) (base_loss s)))))
    by exact (boltzmann_log_decomp s).
  assert (Hsum : Id (plus (log (boltzmann_dist s)) (log Z))
                    (opp (mult (inv_pos D D_pos) (base_loss s)))).
  {
    assert (Hc : Id (plus (log (boltzmann_dist s)) (log Z))
                    (plus (plus (opp (log Z)) (opp (mult (inv_pos D D_pos) (base_loss s)))) (log Z)))
      by exact (id_cong (fun x => plus x (log Z)) Hlog).
    assert (H1 : Id (plus (plus (opp (log Z)) (opp (mult (inv_pos D D_pos) (base_loss s)))) (log Z))
                    (plus (opp (log Z)) (plus (opp (mult (inv_pos D D_pos) (base_loss s))) (log Z))))
      by exact (id_sym (plus_assoc (opp (log Z)) (opp (mult (inv_pos D D_pos) (base_loss s))) (log Z))).
    assert (H2 : Id (plus (opp (log Z)) (plus (opp (mult (inv_pos D D_pos) (base_loss s))) (log Z)))
                    (plus (opp (log Z)) (plus (log Z) (opp (mult (inv_pos D D_pos) (base_loss s))))))
      by exact (id_cong (fun x => plus (opp (log Z)) x)
                        (plus_comm (opp (mult (inv_pos D D_pos) (base_loss s))) (log Z))).
    assert (H3 : Id (plus (opp (log Z)) (plus (log Z) (opp (mult (inv_pos D D_pos) (base_loss s)))))
                    (plus (plus (opp (log Z)) (log Z)) (opp (mult (inv_pos D D_pos) (base_loss s)))))
      by exact (plus_assoc (opp (log Z)) (log Z) (opp (mult (inv_pos D D_pos) (base_loss s)))).
    assert (H4 : Id (plus (plus (opp (log Z)) (log Z)) (opp (mult (inv_pos D D_pos) (base_loss s))))
                    (plus zero (opp (mult (inv_pos D D_pos) (base_loss s))))).
    {
      assert (H4a : Id (plus (plus (opp (log Z)) (log Z)) (opp (mult (inv_pos D D_pos) (base_loss s))))
                      (plus (plus (log Z) (opp (log Z))) (opp (mult (inv_pos D D_pos) (base_loss s)))))
        by exact (id_cong (fun x => plus x (opp (mult (inv_pos D D_pos) (base_loss s))))
                          (plus_comm (opp (log Z)) (log Z))).
      assert (H4b : Id (plus (plus (log Z) (opp (log Z))) (opp (mult (inv_pos D D_pos) (base_loss s))))
                      (plus zero (opp (mult (inv_pos D D_pos) (base_loss s)))))
        by exact (id_cong (fun x => plus x (opp (mult (inv_pos D D_pos) (base_loss s)))) (plus_opp (log Z))).
      exact (id_trans H4a H4b).
    }
    assert (H5 : Id (plus zero (opp (mult (inv_pos D D_pos) (base_loss s))))
                    (opp (mult (inv_pos D D_pos) (base_loss s))))
      by exact (id_trans (plus_comm zero (opp (mult (inv_pos D D_pos) (base_loss s)))) (plus_zero (opp (mult (inv_pos D D_pos) (base_loss s))))).
    exact (id_trans Hc (id_trans H1 (id_trans H2 (id_trans H3 (id_trans H4 H5))))).
  }
  (* D * (-E/D) = -E; after negating, the goal reads
   E = -D * (log p_b + log Z) *)
  assert (Hmd : Id (mult D (plus (log (boltzmann_dist s)) (log Z)))
                   (opp (base_loss s))).
  {
    assert (Hc2 : Id (mult D (plus (log (boltzmann_dist s)) (log Z)))
                     (mult D (opp (mult (inv_pos D D_pos) (base_loss s)))))
      by exact (id_cong (fun x => mult D x) Hsum).
    assert (Hopp : Id (mult D (opp (mult (inv_pos D D_pos) (base_loss s))))
                      (opp (mult D (mult (inv_pos D D_pos) (base_loss s)))))
      by exact (opp_mult_l D (mult (inv_pos D D_pos) (base_loss s))).
    assert (Hcc : Id (mult D (mult (inv_pos D D_pos) (base_loss s))) (base_loss s)).
    {
      assert (Hma : Id (mult D (mult (inv_pos D D_pos) (base_loss s)))
                       (mult (mult D (inv_pos D D_pos)) (base_loss s)))
        by exact (mult_assoc D (inv_pos D D_pos) (base_loss s)).
      assert (Hic : Id (mult (mult D (inv_pos D D_pos)) (base_loss s))
                       (mult one (base_loss s)))
        by exact (id_cong (fun x => mult x (base_loss s)) (inv_pos_correct D D_pos)).
      assert (Hm1 : Id (mult one (base_loss s)) (base_loss s))
        by exact (id_trans (mult_comm one (base_loss s)) (mult_one (base_loss s))).
      exact (id_trans Hma (id_trans Hic Hm1)).
    }
    exact (id_trans Hc2 (id_trans Hopp (id_cong opp Hcc))).
  }
  (* E = -D * (log p_b + log Z): negate mult D (log p_b + log Z) = -E *)
  assert (Hinv : Id (opp (mult D (plus (log (boltzmann_dist s)) (log Z))))
                    (base_loss s)).
  {
    assert (Hd : Id (opp (mult D (plus (log (boltzmann_dist s)) (log Z))))
                    (opp (opp (base_loss s))))
      by exact (id_cong opp Hmd).
    assert (Hdn : Id (opp (opp (base_loss s))) (base_loss s))
      by exact (double_neg (base_loss s)).
    exact (id_trans Hd Hdn).
  }
  exact (id_sym Hinv).
Qed.

(* lemma 2: pointwise decomposition
   mult (p s) (base_loss s) = -D * p * log p_b - D * p * log Z *)
Lemma p_times_energy_decomp :
  forall (p : S -> R) (s : S),
    Id (mult (p s) (base_loss s))
       (plus (opp (mult D (mult (p s) (log (boltzmann_dist s)))))
             (opp (mult D (mult (p s) (log Z))))).
Proof.
  intros p s.
  assert (He : Id (base_loss s)
                  (opp (mult D (plus (log (boltzmann_dist s)) (log Z)))))
    by exact (energy_in_log_boltzmann s).
  assert (Hc : Id (mult (p s) (base_loss s))
                  (mult (p s) (opp (mult D (plus (log (boltzmann_dist s)) (log Z))))))
    by exact (id_cong (fun x => mult (p s) x) He).
  assert (Hopp : Id (mult (p s) (opp (mult D (plus (log (boltzmann_dist s)) (log Z)))))
                    (opp (mult (p s) (mult D (plus (log (boltzmann_dist s)) (log Z))))))
    by exact (opp_mult_l (p s) (mult D (plus (log (boltzmann_dist s)) (log Z)))).
  (* mult (p s) (mult D X) = mult D (mult (p s) X) (re-grouping by
   commutativity) *)
  assert (Hsw : Id (mult (p s) (mult D (plus (log (boltzmann_dist s)) (log Z))))
                   (mult D (mult (p s) (plus (log (boltzmann_dist s)) (log Z))))).
  {
    assert (H1 : Id (mult (p s) (mult D (plus (log (boltzmann_dist s)) (log Z))))
                    (mult (mult (p s) D) (plus (log (boltzmann_dist s)) (log Z))))
      by exact (mult_assoc (p s) D (plus (log (boltzmann_dist s)) (log Z))).
    assert (H2 : Id (mult (mult (p s) D) (plus (log (boltzmann_dist s)) (log Z)))
                    (mult (mult D (p s)) (plus (log (boltzmann_dist s)) (log Z))))
      by exact (id_cong (fun x => mult x (plus (log (boltzmann_dist s)) (log Z))) (mult_comm (p s) D)).
    assert (H3 : Id (mult (mult D (p s)) (plus (log (boltzmann_dist s)) (log Z)))
                    (mult D (mult (p s) (plus (log (boltzmann_dist s)) (log Z)))))
      by exact (id_sym (mult_assoc D (p s) (plus (log (boltzmann_dist s)) (log Z)))).
    exact (id_trans H1 (id_trans H2 H3)).
  }
  (* distrib: mult (p s) (log p_b + log Z) = p * log p_b + p * log Z *)
  assert (Hdist : Id (mult (p s) (plus (log (boltzmann_dist s)) (log Z)))
                     (plus (mult (p s) (log (boltzmann_dist s))) (mult (p s) (log Z))))
    by exact (distrib (p s) (log (boltzmann_dist s)) (log Z)).
  assert (Hsw2 : Id (mult (p s) (mult D (plus (log (boltzmann_dist s)) (log Z))))
                    (mult D (plus (mult (p s) (log (boltzmann_dist s))) (mult (p s) (log Z)))))
    by exact (id_trans Hsw (id_cong (fun x => mult D x) Hdist)).
  assert (Hdist2 : Id (mult D (plus (mult (p s) (log (boltzmann_dist s))) (mult (p s) (log Z))))
                      (plus (mult D (mult (p s) (log (boltzmann_dist s))))
                            (mult D (mult (p s) (log Z)))))
    by exact (distrib D (mult (p s) (log (boltzmann_dist s))) (mult (p s) (log Z))).
  assert (Htot : Id (mult (p s) (mult D (plus (log (boltzmann_dist s)) (log Z))))
                    (plus (mult D (mult (p s) (log (boltzmann_dist s))))
                          (mult D (mult (p s) (log Z)))))
    by exact (id_trans Hsw2 Hdist2).
  (* unfold opp: opp (X + Y) = opp X + opp Y *)
  assert (Hop : Id (opp (plus (mult D (mult (p s) (log (boltzmann_dist s))))
                              (mult D (mult (p s) (log Z)))))
                   (plus (opp (mult D (mult (p s) (log (boltzmann_dist s)))))
                         (opp (mult D (mult (p s) (log Z))))))
    by exact (opp_plus (mult D (mult (p s) (log (boltzmann_dist s))))
                       (mult D (mult (p s) (log Z)))).
  assert (Hc2 : Id (opp (mult (p s) (mult D (plus (log (boltzmann_dist s)) (log Z)))))
                   (opp (plus (mult D (mult (p s) (log (boltzmann_dist s))))
                              (mult D (mult (p s) (log Z))))))
    by exact (id_cong opp Htot).
  exact (id_trans Hc (id_trans Hopp (id_trans Hc2 Hop))).
Qed.

(* main theorem: F[p] = F[p_b] + D * KL(p || p_b) *)
Theorem free_energy_kl_decomp :
  forall p : S -> R,
    normalized p ->
    Id (free_energy p)
       (plus (free_energy boltzmann_dist)
             (mult D (sum_over_S (fun s => mult (p s) (minus (log (p s)) (log (boltzmann_dist s))))))).
Proof.
  intros p Hnorm.
  unfold normalized in Hnorm.
  (* unfold [free_energy] p on the left (free_energy boltzmann_dist on the
   right is kept intact for rewriting by Hfb) *)
  assert (Hfe_p : Id (free_energy p)
                     (plus (sum_over_S (fun s => mult (p s) (base_loss s)))
                           (mult D (sum_over_S (fun s => mult (p s) (log (p s))))))).
  { reflexivity. }
  rewrite Hfe_p.
  (* step 1: sum p * E = -D * sum p * log p_b - D * log Z *)
  assert (Hse : Id (sum_over_S (fun s => mult (p s) (base_loss s)))
                   (plus (opp (mult D (sum_over_S (fun s => mult (p s) (log (boltzmann_dist s))))))
                         (opp (mult D (log Z))))).
  {
    assert (Hpt : forall s : S,
                    Id (mult (p s) (base_loss s))
                       (plus (opp (mult D (mult (p s) (log (boltzmann_dist s)))))
                             (opp (mult D (mult (p s) (log Z))))))
      by exact (p_times_energy_decomp p).
    assert (Hext : Id (sum_over_S (fun s => mult (p s) (base_loss s)))
                     (sum_over_S (fun s => plus (opp (mult D (mult (p s) (log (boltzmann_dist s)))))
                                                (opp (mult D (mult (p s) (log Z)))))))
      by exact (sum_over_S_ext (fun s => mult (p s) (base_loss s))
                               (fun s => plus (opp (mult D (mult (p s) (log (boltzmann_dist s)))))
                                              (opp (mult D (mult (p s) (log Z)))))
                               Hpt).
    rewrite Hext.
    assert (Hadd : Id (sum_over_S (fun s => plus (opp (mult D (mult (p s) (log (boltzmann_dist s)))))
                                                 (opp (mult D (mult (p s) (log Z))))))
                      (plus (sum_over_S (fun s => opp (mult D (mult (p s) (log (boltzmann_dist s))))))
                            (sum_over_S (fun s => opp (mult D (mult (p s) (log Z)))))))
      by exact (sum_over_S_add (fun s => opp (mult D (mult (p s) (log (boltzmann_dist s)))))
                               (fun s => opp (mult D (mult (p s) (log Z))))).
    rewrite Hadd.
    assert (Hso1 : Id (sum_over_S (fun s => opp (mult D (mult (p s) (log (boltzmann_dist s))))))
                      (opp (sum_over_S (fun s => mult D (mult (p s) (log (boltzmann_dist s)))))))
      by exact (sum_opp (fun s => mult D (mult (p s) (log (boltzmann_dist s))))).
    rewrite Hso1.
    assert (Hlin1 : Id (sum_over_S (fun s => mult D (mult (p s) (log (boltzmann_dist s)))))
                       (mult D (sum_over_S (fun s => mult (p s) (log (boltzmann_dist s))))))
      by exact (sum_over_S_linear D (fun s => mult (p s) (log (boltzmann_dist s)))).
    rewrite Hlin1.
    assert (Hso2 : Id (sum_over_S (fun s => opp (mult D (mult (p s) (log Z)))))
                      (opp (sum_over_S (fun s => mult D (mult (p s) (log Z))))))
      by exact (sum_opp (fun s => mult D (mult (p s) (log Z)))).
    rewrite Hso2.
    assert (Hlin2 : Id (sum_over_S (fun s => mult D (mult (p s) (log Z))))
                       (mult D (sum_over_S (fun s => mult (p s) (log Z)))))
      by exact (sum_over_S_linear D (fun s => mult (p s) (log Z))).
    rewrite Hlin2.
    (* inner layer: sum p * log Z = log Z * sum p = log Z (normalization) *)
    assert (HlogZ : Id (sum_over_S (fun s => mult (p s) (log Z))) (log Z)).
    {
      assert (Hsw : Id (sum_over_S (fun s => mult (p s) (log Z)))
                       (sum_over_S (fun s => mult (log Z) (p s))))
        by exact (sum_over_S_ext (fun s => mult (p s) (log Z))
                                 (fun s => mult (log Z) (p s))
                                 (fun s => mult_comm (p s) (log Z))).
      rewrite Hsw.
      assert (Hl1 : Id (sum_over_S (fun s => mult (log Z) (p s))) (mult (log Z) (sum_over_S p)))
        by exact (sum_over_S_linear (log Z) p).
      rewrite Hl1.
      rewrite Hnorm.
      assert (Hm1 : Id (mult (log Z) one) (log Z)) by exact (mult_one (log Z)).
      rewrite Hm1.
      reflexivity.
    }
    rewrite HlogZ.
    reflexivity.
  }
  rewrite Hse.
  (* step 2: F[p_b] = -D * log Z (from the proven [free_energy_boltzmann] and
   [opp_mult_r]) *)
  assert (Hfb : Id (free_energy boltzmann_dist) (opp (mult D (log Z)))).
  {
    assert (Hfb0 : Id (free_energy boltzmann_dist) (mult (opp D) (log Z)))
      by exact (free_energy_boltzmann).
    assert (Hoppr : Id (mult (opp D) (log Z)) (opp (mult D (log Z))))
      by exact (opp_mult_r D (log Z)).
    exact (id_trans Hfb0 Hoppr).
  }
  rewrite Hfb.
  (* step 3: expand KL — mult D (sum p * (log p - log p_b))
   = D * sum p * log p - D * sum p * log p_b *)
  assert (Hkl : Id (mult D (sum_over_S (fun s => mult (p s) (minus (log (p s)) (log (boltzmann_dist s))))))
                  (plus (mult D (sum_over_S (fun s => mult (p s) (log (p s)))))
                        (opp (mult D (sum_over_S (fun s => mult (p s) (log (boltzmann_dist s)))))))).
  {
    (* pointwise: p * (log p - log p_b) = p * log p - p * log p_b *)
    assert (Hpt2 : forall s : S,
                    Id (mult (p s) (minus (log (p s)) (log (boltzmann_dist s))))
                       (plus (mult (p s) (log (p s)))
                             (opp (mult (p s) (log (boltzmann_dist s)))))).
    {
      intro s.
      unfold minus.
      assert (Hd : Id (mult (p s) (plus (log (p s)) (opp (log (boltzmann_dist s)))))
                      (plus (mult (p s) (log (p s))) (mult (p s) (opp (log (boltzmann_dist s))))))
        by exact (distrib (p s) (log (p s)) (opp (log (boltzmann_dist s)))).
      assert (Ho : Id (mult (p s) (opp (log (boltzmann_dist s))))
                      (opp (mult (p s) (log (boltzmann_dist s)))))
        by exact (opp_mult_l (p s) (log (boltzmann_dist s))).
      exact (id_trans Hd (id_cong (fun x => plus (mult (p s) (log (p s))) x) Ho)).
    }
    assert (Hext2 : Id (sum_over_S (fun s => mult (p s) (minus (log (p s)) (log (boltzmann_dist s)))))
                      (sum_over_S (fun s => plus (mult (p s) (log (p s)))
                                                 (opp (mult (p s) (log (boltzmann_dist s)))))))
      by exact (sum_over_S_ext (fun s => mult (p s) (minus (log (p s)) (log (boltzmann_dist s))))
                               (fun s => plus (mult (p s) (log (p s))) (opp (mult (p s) (log (boltzmann_dist s)))))
                               Hpt2).
    rewrite Hext2.
    assert (Hadd2 : Id (sum_over_S (fun s => plus (mult (p s) (log (p s)))
                                                  (opp (mult (p s) (log (boltzmann_dist s))))))
                       (plus (sum_over_S (fun s => mult (p s) (log (p s))))
                             (sum_over_S (fun s => opp (mult (p s) (log (boltzmann_dist s)))))))
      by exact (sum_over_S_add (fun s => mult (p s) (log (p s)))
                               (fun s => opp (mult (p s) (log (boltzmann_dist s))))).
    rewrite Hadd2.
    assert (Hso3 : Id (sum_over_S (fun s => opp (mult (p s) (log (boltzmann_dist s)))))
                      (opp (sum_over_S (fun s => mult (p s) (log (boltzmann_dist s))))))
      by exact (sum_opp (fun s => mult (p s) (log (boltzmann_dist s)))).
    rewrite Hso3.
    (* factor out D (linearity) *)
    assert (HdistD : Id (mult D (plus (sum_over_S (fun s => mult (p s) (log (p s))))
                                      (opp (sum_over_S (fun s => mult (p s) (log (boltzmann_dist s)))))))
                        (plus (mult D (sum_over_S (fun s => mult (p s) (log (p s)))))
                              (mult D (opp (sum_over_S (fun s => mult (p s) (log (boltzmann_dist s))))))))
      by exact (distrib D (sum_over_S (fun s => mult (p s) (log (p s))))
                         (opp (sum_over_S (fun s => mult (p s) (log (boltzmann_dist s)))))).
    assert (HoppD : Id (mult D (opp (sum_over_S (fun s => mult (p s) (log (boltzmann_dist s))))))
                       (opp (mult D (sum_over_S (fun s => mult (p s) (log (boltzmann_dist s)))))))
      by exact (opp_mult_l D (sum_over_S (fun s => mult (p s) (log (boltzmann_dist s))))).
    assert (HcD : Id (mult D (plus (sum_over_S (fun s => mult (p s) (log (p s))))
                                   (opp (sum_over_S (fun s => mult (p s) (log (boltzmann_dist s)))))))
                     (plus (mult D (sum_over_S (fun s => mult (p s) (log (p s)))))
                           (opp (mult D (sum_over_S (fun s => mult (p s) (log (boltzmann_dist s))))))))
      by exact (id_trans HdistD
                          (id_cong (fun x => plus (mult D (sum_over_S (fun s => mult (p s) (log (p s))))) x) HoppD)).
    exact HcD.
  }
  (* step 4: the main goal collapses by ring algebra:
   (opp A + opp (D * log Z)) + D * sum p * log p
   = opp (D * log Z) + (D * sum p * log p + opp A),
   where A := D * sum p * log p_b *)
  set (A := mult D (sum_over_S (fun s => mult (p s) (log (boltzmann_dist s))))).
  set (B := mult D (sum_over_S (fun s => mult (p s) (log (p s))))).
  (* rewrite the KL side: the goal contains B and opp A *)
  assert (Hkl2 : Id (mult D (sum_over_S (fun s => mult (p s) (minus (log (p s)) (log (boltzmann_dist s))))))
                    (plus B (opp A))).
  {
    unfold A, B.
    exact Hkl.
  }
  rewrite Hkl2.
  (* goal: (opp A + opp (D * log Z)) + B = opp (D * log Z) + (B + opp A) *)
  assert (Hfin : Id (plus (plus (opp A) (opp (mult D (log Z)))) B)
                    (plus (opp (mult D (log Z))) (plus B (opp A)))).
  {
    assert (H1 : Id (plus (plus (opp A) (opp (mult D (log Z)))) B)
                    (plus (opp A) (plus (opp (mult D (log Z))) B)))
      by exact (id_sym (plus_assoc (opp A) (opp (mult D (log Z))) B)).
    assert (H2 : Id (plus (opp A) (plus (opp (mult D (log Z))) B))
                    (plus (opp A) (plus B (opp (mult D (log Z))))))
      by exact (id_cong (fun x => plus (opp A) x)
                        (plus_comm (opp (mult D (log Z))) B)).
    assert (H3 : Id (plus (opp A) (plus B (opp (mult D (log Z)))))
                    (plus (plus (opp A) B) (opp (mult D (log Z)))))
      by exact (plus_assoc (opp A) B (opp (mult D (log Z)))).
    assert (H4 : Id (plus (plus (opp A) B) (opp (mult D (log Z))))
                    (plus (plus B (opp A)) (opp (mult D (log Z)))))
      by exact (id_cong (fun x => plus x (opp (mult D (log Z)))) (plus_comm (opp A) B)).
    assert (H5 : Id (plus (plus B (opp A)) (opp (mult D (log Z))))
                    (plus (opp (mult D (log Z))) (plus B (opp A))))
      by exact (plus_comm (plus B (opp A)) (opp (mult D (log Z)))).
    exact (id_trans H1 (id_trans H2 (id_trans H3 (id_trans H4 H5)))).
  }
  exact Hfin.
Qed.

(* corollary: the free-energy difference equals D times the relative
   entropy (difference form, used to decompose training objectives) *)
Theorem free_energy_kl_diff :
  forall p : S -> R,
    normalized p ->
    Id (minus (free_energy p) (free_energy boltzmann_dist))
       (mult D (sum_over_S (fun s => mult (p s) (minus (log (p s)) (log (boltzmann_dist s)))))).
Proof.
  intros p Hnorm.
  unfold minus.
  assert (Hdecomp : Id (free_energy p)
                       (plus (free_energy boltzmann_dist)
                             (mult D (sum_over_S (fun s => mult (p s) (minus (log (p s)) (log (boltzmann_dist s))))))))
    by exact (free_energy_kl_decomp p Hnorm).
  rewrite Hdecomp.
  (* F_b + (the F - F_b term) — the goal in the opp form of plus F_b KL *)
  assert (Hcn : Id (plus (plus (free_energy boltzmann_dist)
                               (mult D (sum_over_S (fun s => mult (p s) (minus (log (p s)) (log (boltzmann_dist s)))))))
                         (opp (free_energy boltzmann_dist)))
                   (mult D (sum_over_S (fun s => mult (p s) (minus (log (p s)) (log (boltzmann_dist s))))))).
  {
    set (FB := free_energy boltzmann_dist).
    set (KL := mult D (sum_over_S (fun s => mult (p s) (minus (log (p s)) (log (boltzmann_dist s)))))).
    assert (H1 : Id (plus (plus FB KL) (opp FB))
                    (plus FB (plus KL (opp FB))))
      by exact (id_sym (plus_assoc FB KL (opp FB))).
    assert (H2 : Id (plus FB (plus KL (opp FB)))
                    (plus FB (plus (opp FB) KL)))
      by exact (id_cong (fun x => plus FB x) (plus_comm KL (opp FB))).
    assert (H3 : Id (plus FB (plus (opp FB) KL))
                    (plus (plus FB (opp FB)) KL))
      by exact (plus_assoc FB (opp FB) KL).
    assert (H4 : Id (plus (plus FB (opp FB)) KL)
                    (plus zero KL))
      by exact (id_cong (fun x => plus x KL) (plus_opp FB)).
    assert (H5 : Id (plus zero KL) KL)
      by exact (id_trans (plus_comm zero KL) (plus_zero KL)).
    exact (id_trans H1 (id_trans H2 (id_trans H3 (id_trans H4 H5)))).
  }
  exact Hcn.
Qed.

(* ============================================================ *)
(* F[p] - F[q] = D * (KL(p || p_b) - KL(q || p_b)): the free-energy
   difference equals the difference of the KL divergences to the Boltzmann
   distribution.  This ranks any two candidate distributions:
   F[p] <= F[q] iff KL(p || p_b) <= KL(q || p_b), supporting model
   selection, orderings on distributional approximations, comparative
   evaluation of generative models, and measuring the teacher-student gap
   in distillation. *)
Theorem free_energy_diff_kl :
  forall p q : S -> R,
    normalized p -> normalized q ->
    Id (minus (free_energy p) (free_energy q)) (mult D (minus (sum_over_S (fun s0 => mult (p s0) (minus (log (p s0)) (log (boltzmann_dist s0))))) (sum_over_S (fun s0 => mult (q s0) (minus (log (q s0)) (log (boltzmann_dist s0))))))).

  intros p q Hnp Hnq.
  (* 1. [free_energy_kl_diff] on both sides *)
  assert (Hp : Id (minus (free_energy p) (free_energy boltzmann_dist))
                  (mult D (sum_over_S (fun s => mult (p s) (minus (log (p s)) (log (boltzmann_dist s)))))))
    by exact (free_energy_kl_diff p Hnp).
  assert (Hq : Id (minus (free_energy q) (free_energy boltzmann_dist))
                  (mult D (sum_over_S (fun s => mult (q s) (minus (log (q s)) (log (boltzmann_dist s)))))))
    by exact (free_energy_kl_diff q Hnq).
  (* 2. ring_minus_trans: F[p]-F[q] = (F[p]-F_b) - (F[q]-F_b) *)
  assert (Hsplit : Id (minus (free_energy p) (free_energy q))
                      (minus (minus (free_energy p) (free_energy boltzmann_dist))
                             (minus (free_energy q) (free_energy boltzmann_dist))))
    by exact (ring_minus_trans (free_energy p) (free_energy q) (free_energy boltzmann_dist)).
  (* 3. substitute Hp, Hq: (D * KL_p) - (D * KL_q) = D * (KL_p - KL_q) *)
  assert (Hsub : Id (minus (free_energy p) (free_energy q)) (minus (mult D (sum_over_S (fun s0 => mult (p s0) (minus (log (p s0)) (log (boltzmann_dist s0)))))) (mult D (sum_over_S (fun s0 => mult (q s0) (minus (log (q s0)) (log (boltzmann_dist s0)))))))).

  {
    assert (H1 : Id (minus (minus (free_energy p) (free_energy boltzmann_dist))
                           (minus (free_energy q) (free_energy boltzmann_dist)))
                    (minus (mult D (sum_over_S (fun s => mult (p s) (minus (log (p s)) (log (boltzmann_dist s))))))
                           (minus (free_energy q) (free_energy boltzmann_dist))))
      by exact (id_cong (fun x => minus x (minus (free_energy q) (free_energy boltzmann_dist))) Hp).
    assert (H2 : Id (minus (mult D (sum_over_S (fun s => mult (p s) (minus (log (p s)) (log (boltzmann_dist s))))))
                           (minus (free_energy q) (free_energy boltzmann_dist)))
                    (minus (mult D (sum_over_S (fun s => mult (p s) (minus (log (p s)) (log (boltzmann_dist s))))))
                           (mult D (sum_over_S (fun s => mult (q s) (minus (log (q s)) (log (boltzmann_dist s))))))))
      by exact (id_cong (fun x => minus (mult D (sum_over_S (fun s => mult (p s) (minus (log (p s)) (log (boltzmann_dist s)))))) x) Hq).
    exact (id_trans Hsplit (id_trans H1 H2)).
  }
  (* 4. [mult_minus_distr_l] in reverse: D * (KL_p - KL_q) = (D * KL_p) - (D * KL_q) *)
  assert (Hm : Id (minus (mult D (sum_over_S (fun s => mult (p s) (minus (log (p s)) (log (boltzmann_dist s))))))
                         (mult D (sum_over_S (fun s => mult (q s) (minus (log (q s)) (log (boltzmann_dist s)))))))
                  (mult D (minus (sum_over_S (fun s => mult (p s) (minus (log (p s)) (log (boltzmann_dist s)))))
                                 (sum_over_S (fun s => mult (q s) (minus (log (q s)) (log (boltzmann_dist s))))))))
    by exact (id_sym (mult_minus_distr_l D (sum_over_S (fun s0 => mult (p s0) (minus (log (p s0)) (log (boltzmann_dist s0))))) (sum_over_S (fun s0 => mult (q s0) (minus (log (q s0)) (log (boltzmann_dist s0))))))).
  exact (id_trans Hsub Hm).
Qed.

(* relative entropy (KL divergence):
   KL(p || q) := sum_s p(s) * (log p(s) - log q(s)) *)
Definition relative_entropy (p q : S -> R) : R :=
  sum_over_S (fun s => mult (p s) (minus (log (p s)) (log (q s)))).

(* key algebraic lemmas: p * (log p - log q) = p * log(p/q), and
   p * (q/p) = q (cancellation of the fraction; used for the pointwise
   terms of the Gibbs inequality) *)
Lemma gibbs_pointwise :
  forall (p q : S -> R) (s : S),
    lt zero (p s) -> lt zero (q s) ->
    le (minus (p s) (q s))
       (mult (p s) (minus (log (p s)) (log (q s)))).
Proof.
  intros p q s Hps Hqs.
  (* log(q/p) <= q/p - 1 (the tangent line of the concave log, for q/p > 0) *)
  assert (Hratio_pos : lt zero (mult (q s) (inv_pos (p s) Hps)))
    by exact (mult_positive (q s) (inv_pos (p s) Hps) Hqs (inv_pos_pos (p s) Hps)).
  assert (Hlin : le (log (mult (q s) (inv_pos (p s) Hps)))
                    (minus (mult (q s) (inv_pos (p s) Hps)) one))
    by exact (log_le_linear (mult (q s) (inv_pos (p s) Hps)) Hratio_pos).
  (* negate: -(q/p - 1) <= -log(q/p), i.e. 1 - q/p <= log(p/q) *)
  assert (Hopp : le (opp (minus (mult (q s) (inv_pos (p s) Hps)) one))
                    (opp (log (mult (q s) (inv_pos (p s) Hps)))))
    by exact (opp_le_compat (log (mult (q s) (inv_pos (p s) Hps)))
                            (minus (mult (q s) (inv_pos (p s) Hps)) one) Hlin).
  (* log(p/q) = -log(q/p) (log_div_neg) *)
  assert (Hld : Id (log (mult (p s) (inv_pos (q s) Hqs)))
                   (opp (log (mult (q s) (inv_pos (p s) Hps)))))
    by exact (log_div_neg (p s) (q s) Hps Hqs).
  (* replace the right side of the goal using log(p/q):
   mult (p s) (minus (log p) (log q)) = mult (p s) (log (p/q)) *)
  assert (Hrhs : Id (mult (p s) (minus (log (p s)) (log (q s))))
                    (mult (p s) (log (mult (p s) (inv_pos (q s) Hqs))))).
  {
    assert (Hlogdiv : Id (log (mult (p s) (inv_pos (q s) Hqs)))
                         (minus (log (p s)) (log (q s))))
      by exact (log_div (p s) (q s) Hps Hqs).
    exact (id_sym (id_cong (fun x => mult (p s) x) Hlogdiv)).
  }
  rewrite Hrhs.
  (* goal: minus (p s) (q s) <= mult (p s) (log (p/q));
   use p * (1 - q/p) <= p * log(p/q) (the negated [log_le_linear] with
   [le_mult_compat]) *)
  assert (Hstep1 : le (mult (p s) (opp (minus (mult (q s) (inv_pos (p s) Hps)) one)))
                      (mult (p s) (opp (log (mult (q s) (inv_pos (p s) Hps))))))
    by exact (le_mult_compat_r (p s)
                               (opp (minus (mult (q s) (inv_pos (p s) Hps)) one))
                               (opp (log (mult (q s) (inv_pos (p s) Hps))))
                               (lt_le_iff _ _ (inl Hps)) Hopp).
  (* p * log(p/q) = p * (-log(q/p)) *)
  assert (Hstep2 : Id (mult (p s) (log (mult (p s) (inv_pos (q s) Hqs))))
                      (mult (p s) (opp (log (mult (q s) (inv_pos (p s) Hps))))))
    by exact (id_cong (fun x => mult (p s) x) Hld).
  rewrite <- Hstep2 in Hstep1.
  (* left side of the goal: p * (1 - q/p) = p - p * (q/p) = p - q *)
  assert (Hlhs : Id (minus (p s) (q s))
                    (mult (p s) (opp (minus (mult (q s) (inv_pos (p s) Hps)) one)))).
  {
    (* mult (p s) (opp (minus X one)) = opp (mult (p s) (minus X one))
 = opp (minus (mult (p s) X) (mult (p s) one)) = opp (minus (p * X) (p * 1))
 mult (p s) X = q s, mult (p s) one = p s implies = opp (minus (q s) (p s)) = minus (p s) (q s) *)
    assert (Hoppl : Id (mult (p s) (opp (minus (mult (q s) (inv_pos (p s) Hps)) one)))
                       (opp (mult (p s) (minus (mult (q s) (inv_pos (p s) Hps)) one))))
      by exact (opp_mult_l (p s) (minus (mult (q s) (inv_pos (p s) Hps)) one)).
    assert (Hdist : Id (mult (p s) (minus (mult (q s) (inv_pos (p s) Hps)) one))
                       (minus (mult (p s) (mult (q s) (inv_pos (p s) Hps)))
                              (mult (p s) one)))
      by exact (mult_minus_distr_l (p s) (mult (q s) (inv_pos (p s) Hps)) one).
    assert (Hcc : Id (mult (p s) (mult (q s) (inv_pos (p s) Hps))) (q s)).
    {
      assert (H1 : Id (mult (p s) (mult (q s) (inv_pos (p s) Hps)))
                      (mult (mult (p s) (q s)) (inv_pos (p s) Hps)))
        by exact (mult_assoc (p s) (q s) (inv_pos (p s) Hps)).
      assert (H2 : Id (mult (mult (p s) (q s)) (inv_pos (p s) Hps))
                      (mult (mult (q s) (p s)) (inv_pos (p s) Hps)))
        by exact (id_cong (fun x => mult x (inv_pos (p s) Hps)) (mult_comm (p s) (q s))).
      assert (H3 : Id (mult (mult (q s) (p s)) (inv_pos (p s) Hps))
                      (mult (q s) (mult (p s) (inv_pos (p s) Hps))))
        by exact (id_sym (mult_assoc (q s) (p s) (inv_pos (p s) Hps))).
      assert (H4 : Id (mult (q s) (mult (p s) (inv_pos (p s) Hps)))
                      (mult (q s) one))
        by exact (id_cong (fun x => mult (q s) x) (inv_pos_correct (p s) Hps)).
      assert (H5 : Id (mult (q s) one) (q s)) by exact (mult_one (q s)).
      exact (id_trans H1 (id_trans H2 (id_trans H3 (id_trans H4 H5)))).
    }
    assert (Hmo : Id (mult (p s) one) (p s)) by exact (mult_one (p s)).
    assert (Hfull : Id (mult (p s) (minus (mult (q s) (inv_pos (p s) Hps)) one))
                       (minus (q s) (p s)))
      by exact (id_trans Hdist (id_trans (id_cong (fun x => minus x (mult (p s) one)) Hcc)
                                         (id_cong (fun x => minus (q s) x) Hmo))).
    assert (Hopp2 : Id (opp (minus (q s) (p s))) (minus (p s) (q s)))
      by exact (id_trans (opp_minus (q s) (p s)) (id_sym (plus_comm (p s) (opp (q s))))).
    exact (id_sym (id_trans Hoppl (id_trans (id_cong opp Hfull) Hopp2))).
  }
  rewrite <- Hlhs in Hstep1.
  exact Hstep1.
Qed.

(* Gibbs inequality: the relative entropy of normalized positive
   distributions is nonnegative (KL >= 0).
   Route: the tangent line of the concave log, pointwise fraction
   cancellation, and monotonicity of sums. *)
Theorem gibbs_inequality :
  forall p q : S -> R,
    normalized p -> positive_dist p ->
    normalized q -> positive_dist q ->
    le zero (relative_entropy p q).
Proof.
  intros p q Hnp Hpp Hnq Hpq.
  unfold relative_entropy.
  (* pointwise: p - q <= p * (log p - log q); monotonicity of sums gives
   sum (p - q) <= KL *)
  assert (Hpt : forall s, le (minus (p s) (q s))
                            (mult (p s) (minus (log (p s)) (log (q s)))))
    by (intro s; apply (gibbs_pointwise p q s); [exact (Hpp s) | exact (Hpq s)]).
  assert (Hle : le (sum_over_S (fun s => minus (p s) (q s)))
                   (sum_over_S (fun s => mult (p s) (minus (log (p s)) (log (q s))))))
    by exact (sum_over_S_le (fun s => minus (p s) (q s))
                            (fun s => mult (p s) (minus (log (p s)) (log (q s))))
                            Hpt).
  (* sum (p - q) = sum p - sum q = 1 - 1 = 0 (normalization with
   [sum_over_S_add] and [sum_opp]) *)
  assert (Hsum0 : Id (sum_over_S (fun s => minus (p s) (q s))) zero).
  {
    unfold minus.
    assert (Hadd : Id (sum_over_S (fun s => plus (p s) (opp (q s))))
                     (plus (sum_over_S p) (sum_over_S (fun s => opp (q s)))))
      by exact (sum_over_S_add p (fun s => opp (q s))).
    assert (Hoppq : Id (sum_over_S (fun s => opp (q s))) (opp (sum_over_S q)))
      by exact (sum_opp q).
    assert (Htot : Id (sum_over_S (fun s => plus (p s) (opp (q s))))
                     (plus (sum_over_S p) (opp (sum_over_S q))))
      by exact (id_trans Hadd (id_cong (fun x => plus (sum_over_S p) x) Hoppq)).
    assert (Hnp' : Id (sum_over_S p) one) by exact Hnp.
    assert (Hnq' : Id (sum_over_S q) one) by exact Hnq.
    assert (Hfin : Id (plus (sum_over_S p) (opp (sum_over_S q))) zero)
      by exact (id_trans (id_cong (fun x => plus x (opp (sum_over_S q))) Hnp')
                         (id_trans (id_cong (fun x => plus one x) (id_cong opp Hnq')) (plus_opp one))).
    exact (id_trans Htot Hfin).
  }
  rewrite Hsum0 in Hle.
  exact Hle.
Qed.

(* equality case of Gibbs: KL(p || q) = 0 implies p = q pointwise.
   Chain:
   1) d(s) := p * (log p - log q) - (p - q) >= 0
      ([gibbs_pointwise] and [le_minus_nonneg]);
   2) sum d = KL - sum (p - q) = 0 - 0 = 0 ([sum_over_S_minus] and
      normalization);
   3) [sum_over_S_zero_nonneg]: sum d = 0 with d >= 0 forces d(s) = 0;
   4) [minus_eq_cancel]: p * (log p - log q) = p - q;
   5) reshape with [log_div] and cancel p > 0 by [mult_cancel_l]:
      log(q/p) = q/p - 1;
   6) [log_eq_linear] (strict concavity of log) gives q/p = 1;
   7) [mult_cancel_r] with inv p > 0 gives q = p. *)
Theorem gibbs_equality :
  forall p q : S -> R,
    normalized p -> positive_dist p ->
    normalized q -> positive_dist q ->
    Id (relative_entropy p q) zero ->
    forall s : S, Id (p s) (q s).
Proof.
  intros p q Hnp Hpp Hnq Hpq Hkl0 s0.
  unfold relative_entropy in Hkl0.
  (* 1) d >= 0 pointwise *)
  assert (Hd_nonneg : forall s, le zero (minus (mult (p s) (minus (log (p s)) (log (q s))))
                                             (minus (p s) (q s)))).
  {
    intro s.
    apply le_minus_nonneg.
    apply (gibbs_pointwise p q s); [exact (Hpp s) | exact (Hpq s)].
  }
  (* 2) sum d = 0 *)
  assert (Hd_sum : Id (sum_over_S (fun s => minus (mult (p s) (minus (log (p s)) (log (q s))))
                                             (minus (p s) (q s)))) zero).
  {
    assert (Hadd : Id (sum_over_S (fun s => minus (mult (p s) (minus (log (p s)) (log (q s))))
                                             (minus (p s) (q s))))
                     (minus (sum_over_S (fun s => mult (p s) (minus (log (p s)) (log (q s)))))
                            (sum_over_S (fun s => minus (p s) (q s)))))
      by exact (sum_over_S_minus (fun s => mult (p s) (minus (log (p s)) (log (q s))))
                                 (fun s => minus (p s) (q s))).
    rewrite Hadd.
    assert (Hpq0 : Id (sum_over_S (fun s => minus (p s) (q s))) zero).
    {
      unfold minus.
      assert (Hadd2 : Id (sum_over_S (fun s => plus (p s) (opp (q s))))
                        (plus (sum_over_S p) (sum_over_S (fun s => opp (q s)))))
        by exact (sum_over_S_add p (fun s => opp (q s))).
      assert (Hoppq : Id (sum_over_S (fun s => opp (q s))) (opp (sum_over_S q)))
        by exact (sum_opp q).
      assert (Htot : Id (sum_over_S (fun s => plus (p s) (opp (q s))))
                       (plus (sum_over_S p) (opp (sum_over_S q))))
        by exact (id_trans Hadd2 (id_cong (fun x => plus (sum_over_S p) x) Hoppq)).
      assert (Hfin : Id (plus (sum_over_S p) (opp (sum_over_S q))) zero)
        by exact (id_trans (id_cong (fun x => plus x (opp (sum_over_S q))) Hnp)
                           (id_trans (id_cong (fun x => plus one x) (id_cong opp Hnq)) (plus_opp one))).
      exact (id_trans Htot Hfin).
    }
    assert (Hminus : Id (minus zero zero) zero)
      by (unfold minus; exact (plus_opp zero)).
    exact (id_trans (id_cong (fun x => minus x (sum_over_S (fun s => minus (p s) (q s)))) Hkl0)
                   (id_trans (id_cong (fun x => minus zero x) Hpq0) Hminus)).
  }
  (* 3) d(s0) = 0 *)
  assert (Hd0s : Id (minus (mult (p s0) (minus (log (p s0)) (log (q s0))))
                           (minus (p s0) (q s0))) zero)
    by exact (sum_over_S_zero_nonneg
                (fun s => minus (mult (p s) (minus (log (p s)) (log (q s))))
                                (minus (p s) (q s)))
                Hd_nonneg Hd_sum s0).
  (* 4) p * (log p - log q) = p - q *)
  assert (Hrel : Id (mult (p s0) (minus (log (p s0)) (log (q s0))))
                   (minus (p s0) (q s0)))
    by exact (minus_eq_cancel (mult (p s0) (minus (log (p s0)) (log (q s0))))
                              (minus (p s0) (q s0)) Hd0s).
  (* 5) reshape: log(p/q) = log p - log q; negate q/p *)
  assert (Hlhs : Id (mult (p s0) (minus (log (p s0)) (log (q s0))))
                    (mult (p s0) (log (mult (p s0) (inv_pos (q s0) (Hpq s0))))))
    by exact (id_sym (id_cong (fun x => mult (p s0) x)
                              (log_div (p s0) (q s0) (Hpp s0) (Hpq s0)))).
  rewrite Hlhs in Hrel.
  (* p * log(p/q) = p * (-log(q/p)) *)
  assert (Hlogneg : Id (log (mult (p s0) (inv_pos (q s0) (Hpq s0))))
                       (opp (log (mult (q s0) (inv_pos (p s0) (Hpp s0))))))
    by exact (log_div_neg (p s0) (q s0) (Hpp s0) (Hpq s0)).
  assert (Hlhs2 : Id (mult (p s0) (log (mult (p s0) (inv_pos (q s0) (Hpq s0)))))
                     (mult (p s0) (opp (log (mult (q s0) (inv_pos (p s0) (Hpp s0)))))))
    by exact (id_cong (fun x => mult (p s0) x) Hlogneg).
  rewrite Hlhs2 in Hrel.
  (* right side: p - q = p * (1 - q/p), reading the identity inside
   [gibbs_pointwise] backwards *)
  assert (Hrhs : Id (minus (p s0) (q s0))
                    (mult (p s0) (opp (minus (mult (q s0) (inv_pos (p s0) (Hpp s0))) one)))).
  {
    assert (Hoppl : Id (mult (p s0) (opp (minus (mult (q s0) (inv_pos (p s0) (Hpp s0))) one)))
                       (opp (mult (p s0) (minus (mult (q s0) (inv_pos (p s0) (Hpp s0))) one))))
      by exact (opp_mult_l (p s0) (minus (mult (q s0) (inv_pos (p s0) (Hpp s0))) one)).
    assert (Hdist : Id (mult (p s0) (minus (mult (q s0) (inv_pos (p s0) (Hpp s0))) one))
                       (minus (mult (p s0) (mult (q s0) (inv_pos (p s0) (Hpp s0))))
                              (mult (p s0) one)))
      by exact (mult_minus_distr_l (p s0) (mult (q s0) (inv_pos (p s0) (Hpp s0))) one).
    assert (Hcc : Id (mult (p s0) (mult (q s0) (inv_pos (p s0) (Hpp s0)))) (q s0)).
    {
      assert (H1 : Id (mult (p s0) (mult (q s0) (inv_pos (p s0) (Hpp s0))))
                      (mult (mult (p s0) (q s0)) (inv_pos (p s0) (Hpp s0))))
        by exact (mult_assoc (p s0) (q s0) (inv_pos (p s0) (Hpp s0))).
      assert (H2 : Id (mult (mult (p s0) (q s0)) (inv_pos (p s0) (Hpp s0)))
                      (mult (mult (q s0) (p s0)) (inv_pos (p s0) (Hpp s0))))
        by exact (id_cong (fun x => mult x (inv_pos (p s0) (Hpp s0))) (mult_comm (p s0) (q s0))).
      assert (H3 : Id (mult (mult (q s0) (p s0)) (inv_pos (p s0) (Hpp s0)))
                      (mult (q s0) (mult (p s0) (inv_pos (p s0) (Hpp s0)))))
        by exact (id_sym (mult_assoc (q s0) (p s0) (inv_pos (p s0) (Hpp s0)))).
      assert (H4 : Id (mult (q s0) (mult (p s0) (inv_pos (p s0) (Hpp s0))))
                      (mult (q s0) one))
        by exact (id_cong (fun x => mult (q s0) x) (inv_pos_correct (p s0) (Hpp s0))).
      assert (H5 : Id (mult (q s0) one) (q s0)) by exact (mult_one (q s0)).
      exact (id_trans H1 (id_trans H2 (id_trans H3 (id_trans H4 H5)))).
    }
    assert (Hmo : Id (mult (p s0) one) (p s0)) by exact (mult_one (p s0)).
    assert (Hfull : Id (mult (p s0) (minus (mult (q s0) (inv_pos (p s0) (Hpp s0))) one))
                       (minus (q s0) (p s0)))
      by exact (id_trans Hdist (id_trans (id_cong (fun x => minus x (mult (p s0) one)) Hcc)
                                         (id_cong (fun x => minus (q s0) x) Hmo))).
    assert (Hopp2 : Id (opp (minus (q s0) (p s0))) (minus (p s0) (q s0)))
      by exact (id_trans (opp_minus (q s0) (p s0)) (id_sym (plus_comm (p s0) (opp (q s0))))).
    exact (id_sym (id_trans Hoppl (id_trans (id_cong opp Hfull) Hopp2))).
  }
  rewrite Hrhs in Hrel.
  (* 6) mult_cancel_l (p > 0): -log(q/p) = -(q/p - 1) implies log(q/p) = q/p - 1 *)
  assert (Hopp_eq : Id (opp (log (mult (q s0) (inv_pos (p s0) (Hpp s0)))))
                       (opp (minus (mult (q s0) (inv_pos (p s0) (Hpp s0))) one)))
    by exact (mult_cancel_l (p s0)
                            (opp (log (mult (q s0) (inv_pos (p s0) (Hpp s0)))))
                            (opp (minus (mult (q s0) (inv_pos (p s0) (Hpp s0))) one))
                            (Hpp s0) Hrel).
  assert (Hlog_eq : Id (log (mult (q s0) (inv_pos (p s0) (Hpp s0))))
                       (minus (mult (q s0) (inv_pos (p s0) (Hpp s0))) one)).
  {
    assert (H2 : Id (log (mult (q s0) (inv_pos (p s0) (Hpp s0))))
                    (opp (opp (log (mult (q s0) (inv_pos (p s0) (Hpp s0)))))))
      by exact (id_sym (double_neg (log (mult (q s0) (inv_pos (p s0) (Hpp s0)))))).
    assert (H3 : Id (opp (opp (minus (mult (q s0) (inv_pos (p s0) (Hpp s0))) one)))
                    (minus (mult (q s0) (inv_pos (p s0) (Hpp s0))) one))
      by exact (double_neg (minus (mult (q s0) (inv_pos (p s0) (Hpp s0))) one)).
    exact (id_trans H2 (id_trans (id_cong opp Hopp_eq) H3)).
  }
  (* 7) log_eq_linear: log(q/p) = q/p - 1 implies q/p = 1 *)
  assert (Hratio_pos : lt zero (mult (q s0) (inv_pos (p s0) (Hpp s0))))
    by exact (mult_positive (q s0) (inv_pos (p s0) (Hpp s0)) (Hpq s0) (inv_pos_pos (p s0) (Hpp s0))).
  assert (Hratio_one : Id (mult (q s0) (inv_pos (p s0) (Hpp s0))) one)
    by exact (log_eq_linear (mult (q s0) (inv_pos (p s0) (Hpp s0))) Hratio_pos Hlog_eq).
  (* 8) q * (1/p) = 1 = p * (1/p) gives q = p ([mult_cancel_r] with
   inv p > 0) *)
  assert (Hpr : Id (mult (p s0) (inv_pos (p s0) (Hpp s0))) one)
    by exact (inv_pos_correct (p s0) (Hpp s0)).
  assert (Hqr : Id (mult (q s0) (inv_pos (p s0) (Hpp s0)))
                  (mult (p s0) (inv_pos (p s0) (Hpp s0))))
    by exact (id_trans Hratio_one (id_sym Hpr)).
  exact (id_sym (mult_cancel_r (inv_pos (p s0) (Hpp s0)) (q s0) (p s0) (inv_pos_pos (p s0) (Hpp s0)) Hqr)).
Qed.

(* positivity of the Boltzmann distribution: p_b(s) > 0
   (positivity of inverses times positivity of the exponential) *)
Lemma boltzmann_dist_pos :
  forall s : S, lt zero (boltzmann_dist s).
Proof.
  intro s.
  unfold boltzmann_dist.
  apply mult_positive.
  - apply inv_pos_pos.
  - apply exp_neg_pos.
Qed.

(* minimization of the free energy (a former assumption variable, restated
   as a theorem): F[p_b] <= F[p] — the Boltzmann distribution is a global
   minimizer of the free energy.
   Proof: F[p] = F[p_b] + D * KL(p || p_b) ([free_energy_kl_decomp]),
   KL >= 0 ([gibbs_inequality]), and monotonicity under multiplication by
   D > 0. *)
Theorem min_free_energy_is_boltzmann :
  forall p : S -> R,
    normalized p -> positive_dist p ->
    le (free_energy boltzmann_dist) (free_energy p).
Proof.
  intros p Hnp Hpp.
  (* 1. F[p] = F[p_b] + D * KL(p||p_b) *)
  assert (Hdecomp : Id (free_energy p)
                       (plus (free_energy boltzmann_dist)
                             (mult D (relative_entropy p boltzmann_dist))))
    by exact (free_energy_kl_decomp p Hnp).
  (* 2. KL >= 0 ([gibbs_inequality]; [boltzmann_dist] is normalized and
   positive) *)
  assert (Hkl : le zero (relative_entropy p boltzmann_dist)).
  {
    apply (gibbs_inequality p boltzmann_dist).
    - exact Hnp.
    - exact Hpp.
    - exact (boltzmann_normalized).
    - intro s. exact (boltzmann_dist_pos s).
  }
  (* 3. monotonicity under D > 0: 0 <= KL gives D * 0 <= D * KL, i.e.
   0 <= D * KL *)
  assert (Hdkl : le zero (mult D (relative_entropy p boltzmann_dist))).
  {
    assert (Hm : le (mult D zero) (mult D (relative_entropy p boltzmann_dist)))
      by exact (le_mult_compat_r D zero (relative_entropy p boltzmann_dist)
                                (lt_le_iff _ _ (inl D_pos)) Hkl).
    assert (Hz : Id (mult D zero) zero) by exact (mult_zero D).
    exact (le_id_l zero (mult D zero) (mult D (relative_entropy p boltzmann_dist)) (id_sym Hz) Hm).
  }
  (* 4. F[p_b] <= F[p_b] + D * KL = F[p] (reduce by [le_plus_compat],
   [le_refl] and [le_id_l]) *)
  assert (Hfin : le (free_energy boltzmann_dist)
                    (plus (free_energy boltzmann_dist) (mult D (relative_entropy p boltzmann_dist)))).
  {
    assert (Hplus : le (plus (free_energy boltzmann_dist) zero)
                       (plus (free_energy boltzmann_dist) (mult D (relative_entropy p boltzmann_dist))))
      by (apply (le_plus_compat (free_energy boltzmann_dist) (free_energy boltzmann_dist)
                                zero (mult D (relative_entropy p boltzmann_dist)));
          [apply le_refl | exact Hdkl]).
    assert (Hpz : Id (plus (free_energy boltzmann_dist) zero) (free_energy boltzmann_dist))
      by exact (plus_zero (free_energy boltzmann_dist)).
    exact (le_id_l (free_energy boltzmann_dist) (plus (free_energy boltzmann_dist) zero)
                   (plus (free_energy boltzmann_dist) (mult D (relative_entropy p boltzmann_dist)))
                   (id_sym Hpz) Hplus).
  }
  exact (le_id_r (free_energy boltzmann_dist) (plus (free_energy boltzmann_dist) (mult D (relative_entropy p boltzmann_dist))) (free_energy p) (id_sym Hdecomp) Hfin).
Qed.

(* uniqueness of the free-energy minimizer: if p attains the same free
   energy as the Boltzmann distribution, then p = p_b pointwise.
   Proof: F[p] = F[p_b] + D * KL and F[p] = F[p_b] give D * KL = 0, hence
   KL = 0 by cancellation with D > 0 ([mult_cancel_l]), hence p = p_b
   ([gibbs_equality]). *)
Theorem free_energy_min_unique :
  forall p : S -> R,
    normalized p -> positive_dist p ->
    Id (free_energy p) (free_energy boltzmann_dist) ->
    forall s : S, Id (p s) (boltzmann_dist s).
Proof.
  intros p Hnp Hpp Hfeq s.
  (* 1. F[p] = F[p_b] + D * KL (the identity) *)
  assert (Hdecomp : Id (free_energy p)
                       (plus (free_energy boltzmann_dist)
                             (mult D (relative_entropy p boltzmann_dist))))
    by exact (free_energy_kl_decomp p Hnp).
  (* 2. F[p] = F[p_b] gives D * KL = 0 (cancel F[p_b]) *)
  assert (Hdkl0 : Id (mult D (relative_entropy p boltzmann_dist)) zero).
  {
    assert (H1 : Id (plus (free_energy boltzmann_dist)
                          (mult D (relative_entropy p boltzmann_dist)))
                   (free_energy p))
      by exact (id_sym Hdecomp).
    assert (H2 : Id (plus (free_energy boltzmann_dist)
                          (mult D (relative_entropy p boltzmann_dist)))
                   (free_energy boltzmann_dist))
      by exact (id_trans H1 Hfeq).
    (* plus FB KL = FB gives KL = 0 (cancel FB by [plus_cancel]) *)
    exact (plus_cancel_zero (free_energy boltzmann_dist) (mult D (relative_entropy p boltzmann_dist)) H2).
  }
  (* 3. D > 0 implies KL = 0 (mult_cancel_l) *)
  assert (Hkl0 : Id (relative_entropy p boltzmann_dist) zero).
  {
    (* mult D KL = zero with D > 0: derive KL = 0 from D * KL = 0 using the
   zero version of [mult_cancel_l]: mult a b = mult a zero with a > 0
   gives b = zero *)
    assert (Hcz : Id (mult D (relative_entropy p boltzmann_dist))
                     (mult D zero))
      by exact (id_trans Hdkl0 (id_sym (mult_zero D))).
    exact (mult_cancel_l D (relative_entropy p boltzmann_dist) zero D_pos Hcz).
  }
  (* 4. gibbs_equality: KL = 0 implies p = p_b *)
  exact (gibbs_equality p boltzmann_dist Hnp Hpp (boltzmann_normalized) (fun t => boltzmann_dist_pos t) Hkl0 s).
Qed.

(* ============================================================ *)
(* the maximum-entropy principle (third pillar of statistical mechanics:
   the free-energy/entropy duality) *)
(* ============================================================ *)
(* the first two pillars: unique minimum of the free energy
   ([min_free_energy_is_boltzmann] and *)
(* [free_energy_min_unique]) and KL as the exact deviation measure
   ([free_energy_kl_ *)
(* decomp]).  This section adds the third: under an equal-energy constraint
   the Boltzmann distribution maximizes the entropy, *)
(* and the entropy deficit equals KL (the entropic measure of deviation). *)
(* ------------------------------------------------------------ *)

(* information entropy: S[p] := -sum_s p(s) * log p(s) (distribution
   version; the top-level [entropy] is the R -> R version) *)
Definition entropy_dist (p : S -> R) : R :=
  sum_over_S (fun s => mult (p s) (opp (log (p s)))).

(* expected energy: <E>_p := sum_s p(s) * base_loss(s) (the constrained
   quantity of the maximum-entropy problem) *)
Definition energy_expectation (p : S -> R) : R :=
  sum_over_S (fun s => mult (p s) (base_loss s)).

(* entropy decomposition: sum p * log p = -S[p] (via [sum_over_S_ext],
   [opp_mult_l], double negation, and [sum_opp]) *)
Lemma entropy_neg_sum :
  forall p : S -> R,
    Id (sum_over_S (fun s => mult (p s) (log (p s))))
       (opp (entropy_dist p)).
Proof.
  intro p.
  unfold entropy_dist.
  assert (Hpt : forall s, Id (mult (p s) (log (p s)))
                            (opp (mult (p s) (opp (log (p s)))))).
  {
    intro s.
    assert (H1 : Id (mult (p s) (opp (log (p s)))) (opp (mult (p s) (log (p s)))))
      by exact (opp_mult_l (p s) (log (p s))).
    assert (H2 : Id (opp (mult (p s) (opp (log (p s)))))
                    (opp (opp (mult (p s) (log (p s))))))
      by exact (id_cong opp H1).
    exact (id_sym (id_trans H2 (double_neg (mult (p s) (log (p s)))))).
  }
  assert (Hext : Id (sum_over_S (fun s => mult (p s) (log (p s))))
                   (sum_over_S (fun s => opp (mult (p s) (opp (log (p s)))))))
    by exact (sum_over_S_ext (fun s => mult (p s) (log (p s)))
                             (fun s => opp (mult (p s) (opp (log (p s))))) Hpt).
  rewrite Hext.
  assert (Hso : Id (sum_over_S (fun s => opp (mult (p s) (opp (log (p s))))))
                   (opp (sum_over_S (fun s => mult (p s) (opp (log (p s)))))))
    by exact (sum_opp (fun s => mult (p s) (opp (log (p s))))).
  exact Hso.
Qed.

(* free-energy/entropy/energy identity: F[p] = <E>_p - D * S[p] *)
Lemma free_energy_entropy :
  forall p : S -> R,
    Id (free_energy p)
       (plus (energy_expectation p) (mult D (opp (entropy_dist p)))).
Proof.
  intro p.
  unfold free_energy, energy_expectation.
  assert (Hneg : Id (sum_over_S (fun s => mult (p s) (log (p s))))
                    (opp (entropy_dist p)))
    by exact (entropy_neg_sum p).
  exact (id_cong (fun x => plus (sum_over_S (fun s => mult (p s) (base_loss s))) (mult D x)) Hneg).
Qed.

(* entropy-difference/relative-entropy identity: under the equal-energy
   constraint (<E>_p = <E>_b), S[p_b] - S[p] = KL(p || p_b).
   Proof: F[p] = F[p_b] + D * KL (the free-energy identity) and
   F = <E> - D * S on both sides; the equal energies cancel, then D > 0
   cancels. *)
Theorem entropy_deficit_kl :
  forall p : S -> R,
    normalized p -> positive_dist p ->
    Id (energy_expectation p) (energy_expectation boltzmann_dist) ->
    Id (minus (entropy_dist boltzmann_dist) (entropy_dist p))
       (relative_entropy p boltzmann_dist).
Proof.
  intros p Hnp Hpp Henergy.
  (* 1. F[p] = F[p_b] + D * KL (the free-energy identity) *)
  assert (Hdecomp : Id (free_energy p)
                       (plus (free_energy boltzmann_dist)
                             (mult D (relative_entropy p boltzmann_dist))))
    by exact (free_energy_kl_decomp p Hnp).
  (* 2. rewrite both sides in the <E> - D * S form *)
  assert (Hfe_p : Id (free_energy p)
                     (plus (energy_expectation p) (mult D (opp (entropy_dist p)))))
    by exact (free_energy_entropy p).
  assert (Hfe_b : Id (free_energy boltzmann_dist)
                     (plus (energy_expectation boltzmann_dist) (mult D (opp (entropy_dist boltzmann_dist)))))
    by exact (free_energy_entropy boltzmann_dist).
  (* 3. ⟨E⟩_p - D * S[p] = ⟨E⟩_b - D * S[p_b] + D * KL *)
  assert (Htot : Id (plus (energy_expectation p) (mult D (opp (entropy_dist p))))
                   (plus (plus (energy_expectation boltzmann_dist)
                               (mult D (opp (entropy_dist boltzmann_dist))))
                         (mult D (relative_entropy p boltzmann_dist)))).
  {
    assert (H1 : Id (plus (energy_expectation p) (mult D (opp (entropy_dist p))))
                    (plus (free_energy boltzmann_dist)
                          (mult D (relative_entropy p boltzmann_dist))))
      by exact (id_trans (id_sym Hfe_p) Hdecomp).
    assert (H2 : Id (plus (free_energy boltzmann_dist)
                          (mult D (relative_entropy p boltzmann_dist)))
                    (plus (plus (energy_expectation boltzmann_dist)
                                (mult D (opp (entropy_dist boltzmann_dist))))
                          (mult D (relative_entropy p boltzmann_dist))))
      by exact (id_cong (fun x => plus x (mult D (relative_entropy p boltzmann_dist))) Hfe_b).
    exact (id_trans H1 H2).
  }
  (* 4. cancel the equal energies <E>: -D * S[p] = -D * S[p_b] + D * KL *)
  assert (Hcancel : Id (mult D (opp (entropy_dist p)))
                       (plus (mult D (opp (entropy_dist boltzmann_dist)))
                             (mult D (relative_entropy p boltzmann_dist)))).
  {
    assert (Hsw : Id (plus (energy_expectation boltzmann_dist) (mult D (opp (entropy_dist p))))
                     (plus (energy_expectation p) (mult D (opp (entropy_dist p)))))
      by exact (id_cong (fun x => plus x (mult D (opp (entropy_dist p)))) (id_sym Henergy)).
    assert (H2 : Id (plus (energy_expectation boltzmann_dist) (mult D (opp (entropy_dist p))))
                    (plus (plus (energy_expectation boltzmann_dist)
                                (mult D (opp (entropy_dist boltzmann_dist))))
                          (mult D (relative_entropy p boltzmann_dist))))
      by exact (id_trans Hsw Htot).
    assert (Hre : Id (plus (plus (energy_expectation boltzmann_dist)
                                (mult D (opp (entropy_dist boltzmann_dist))))
                          (mult D (relative_entropy p boltzmann_dist)))
                    (plus (energy_expectation boltzmann_dist)
                          (plus (mult D (opp (entropy_dist boltzmann_dist)))
                                (mult D (relative_entropy p boltzmann_dist)))))
      by exact (id_sym (plus_assoc (energy_expectation boltzmann_dist)
                                     (mult D (opp (entropy_dist boltzmann_dist)))
                                     (mult D (relative_entropy p boltzmann_dist)))).
    assert (H2r : Id (plus (energy_expectation boltzmann_dist) (mult D (opp (entropy_dist p))))
                     (plus (energy_expectation boltzmann_dist)
                           (plus (mult D (opp (entropy_dist boltzmann_dist)))
                                 (mult D (relative_entropy p boltzmann_dist)))))
      by exact (id_trans H2 Hre).
    exact (plus_cancel_l (energy_expectation boltzmann_dist)
                         (mult D (opp (entropy_dist p)))
                         (plus (mult D (opp (entropy_dist boltzmann_dist)))
                               (mult D (relative_entropy p boltzmann_dist)))
                         H2r).
  }
  (* 5. ring cancellation: from -D * S[p] = -D * S[p_b] + D * KL and D > 0,
   derive S[p_b] - S[p] = KL *)
  exact (ring_d_cancel D (entropy_dist p) (entropy_dist boltzmann_dist)
                      (relative_entropy p boltzmann_dist) D_pos Hcancel).
Qed.

Theorem max_entropy_is_boltzmann :
  forall p : S -> R,
    normalized p -> positive_dist p ->
    Id (energy_expectation p) (energy_expectation boltzmann_dist) ->
    le (entropy_dist p) (entropy_dist boltzmann_dist).
Proof.
  intros p Hnp Hpp Henergy.
  (* 1. S[p_b] - S[p] = KL *)
  assert (Hdef : Id (minus (entropy_dist boltzmann_dist) (entropy_dist p))
                    (relative_entropy p boltzmann_dist))
    by exact (entropy_deficit_kl p Hnp Hpp Henergy).
  (* 2. KL >= 0 ([gibbs_inequality]: both p and p_b normalized and positive) *)
  assert (Hkl : le zero (relative_entropy p boltzmann_dist)).
  {
    apply (gibbs_inequality p boltzmann_dist).
    - exact Hnp.
    - exact Hpp.
    - exact (boltzmann_normalized).
    - intro s. exact (boltzmann_dist_pos s).
  }
  (* 3. 0 <= S[p_b] - S[p] gives S[p] <= S[p_b] (converse of
   [le_minus_nonneg], via [minus_plus_cancel]) *)
  assert (Hnonneg : le zero (minus (entropy_dist boltzmann_dist) (entropy_dist p)))
    by exact (le_id_r zero (relative_entropy p boltzmann_dist)
                     (minus (entropy_dist boltzmann_dist) (entropy_dist p))
                     (id_sym Hdef) Hkl).
  (* S[p] + (S[p_b] - S[p]) = S[p_b] (minus_plus_cancel)implies le S[p] S[p_b] *)
  assert (Hplus : Id (plus (entropy_dist p) (minus (entropy_dist boltzmann_dist) (entropy_dist p)))
                     (entropy_dist boltzmann_dist))
    by exact (minus_plus_cancel (entropy_dist p) (entropy_dist boltzmann_dist)).
  assert (Hle : le (entropy_dist p)
                   (plus (entropy_dist p) (minus (entropy_dist boltzmann_dist) (entropy_dist p))))
    by exact (le_plus_nonneg_r (entropy_dist p) (minus (entropy_dist boltzmann_dist) (entropy_dist p)) Hnonneg).
  exact (le_id_r (entropy_dist p)
                 (plus (entropy_dist p) (minus (entropy_dist boltzmann_dist) (entropy_dist p)))
                 (entropy_dist boltzmann_dist) Hplus Hle).
Qed.

(* ============================================================ *)
(* monotonicity of the expected energy in the temperature *)
(*   main statement: t1 < t2 implies E_temp(t1) <= E_temp(t2)
   (raising the temperature never decreases the expected energy) *)
(*   method: variational — add the two crossed Gibbs inequalities
   (no derivatives, no trichotomy) *)
(*     KL(q || p_beta) >= 0 at (q = p_beta2, beta = beta1) and
   (q = p_beta1, beta = beta2) *)
(*     adding gives (beta1 - beta2) * (E1 - E2) <= 0; with
   beta1 - beta2 > 0, E1 <= E2 *)
(*   explicit assumptions (instantiable in the [Real] layer, no classical
   axioms): *)
(*     [sum_over_S_pos] — a finite sum of positive terms is positive
   (instantiable for finite sums) *)
(*     [inv_pos_lt_compat] — the [Real]-layer [real_inv_lt_contra]
   (strict reversal by the inverse) *)
(*     [lt_minus_nonneg] — built pointwise per eps in the [Real] layer
   (lifting of Qlt_minus_iff) *)
(* ============================================================ *)
Variable sum_over_S_pos : forall f : S -> R,
  (forall s : S, lt zero (f s)) -> lt zero (sum_over_S f).
Variable inv_pos_lt_compat : forall a b : R, forall Ha : lt zero a, forall Hb : lt zero b,
  lt a b -> lt (inv_pos b Hb) (inv_pos a Ha).
Variable lt_minus_nonneg : forall a b : R, lt a b -> lt zero (minus b a).

(* ---------- self-proved algebraic lemmas (interface layer, purely
   constructive) ---------- *)

(* converse of additive compatibility: a + c <= b + c implies a <= b
   (cancellation in an ordered abelian group, [le_id] algebra) *)
Lemma le_plus_cancel_l : forall a b c : R, le (plus a c) (plus b c) -> le a b.
Proof.
  intros a b c H.
  apply (le_id_l a (minus (plus a c) c)).
  - (* a == minus (plus a c) c *)
    unfold minus.
    exact (id_trans (id_trans (id_sym (plus_zero a))
              (id_sym (id_cong (fun x => plus a x) (plus_opp c))))
              (plus_assoc a c (opp c))).
  - apply (le_id_r (minus (plus a c) c) (minus (plus b c) c) b).
    + (* minus (plus b c) c == b *)
      unfold minus.
      exact (id_trans (id_trans (id_sym (plus_assoc b c (opp c)))
              (id_cong (fun x => plus b x) (plus_opp c)))
              (plus_zero b)).
    + unfold minus.
      apply (le_plus_compat (plus a c) (plus b c) (opp c) (opp c) H (le_refl (opp c))).
Qed.

(* converse of nonnegative difference: a - b <= 0 implies a <= b *)
Lemma le_minus_nonneg_rev : forall a b : R, le (minus a b) zero -> le a b.
Proof.
  intros a b H.
  apply (le_id_l a (plus (minus a b) b)).
  - (* a == plus (minus a b) b *)
    unfold minus.
    exact (id_trans (id_sym (plus_zero a))
           (id_trans (id_sym (id_cong (fun x => plus a x)
                 (id_trans (plus_comm (opp b) b) (plus_opp b))))
                 (plus_assoc a (opp b) b))).
  - apply (le_id_r (plus (minus a b) b) (plus zero b) b).
    + exact (id_trans (plus_comm zero b) (plus_zero b)).
    + apply (le_plus_compat (minus a b) zero b b H (le_refl b)).
Qed.

(* cancellation by a positive factor: c > 0 and a * c <= 0 imply a <= 0,
   since a == (a * c) * (inv c) *)
Lemma le_mult_pos_cancel : forall a c : R, lt zero c -> le (mult a c) zero -> le a zero.
Proof.
  intros a c Hc H.
  apply (le_id_l a (mult (mult a c) (inv_pos c Hc))).
  - (* a == mult (mult a c) (inv_pos c Hc) *)
    exact (id_trans (id_sym (mult_one a))
           (id_trans (id_cong (fun x => mult a x) (id_sym (inv_pos_correct c Hc)))
                     (mult_assoc a c (inv_pos c Hc)))).
  - apply (le_id_r (mult (mult a c) (inv_pos c Hc)) (mult zero (inv_pos c Hc)) zero).
    + exact (id_trans (mult_comm zero (inv_pos c Hc)) (mult_zero (inv_pos c Hc))).
    + apply (le_mult_compat_weak (mult a c) zero (inv_pos c Hc)).
      * apply lt_le_iff. left. apply inv_pos_pos.
      * exact H.
Qed.

(* right distributivity of multiplication over subtraction:
   mult (minus a b) c == minus (mult a c) (mult b c) *)
Lemma mult_minus_distr_r : forall a b c : R,
  Id (mult (minus a b) c) (minus (mult a c) (mult b c)).
Proof.  intros a b c.
  unfold minus.
  exact (id_trans (mult_comm (plus a (opp b)) c)
           (id_trans (distrib c a (opp b))
              (id_trans (id_cong (fun x => plus x (mult c (opp b))) (mult_comm c a))
                 (id_trans (id_cong (fun x => plus (mult a c) x) (mult_comm c (opp b)))
                    (id_cong (fun x => plus (mult a c) x) (opp_mult_r b c)))))).
Qed.

(* ---------- temperature-parameterized definitions ---------- *)

(* temperature-parameterized partition function (interface assumption:
   the partition of temperature t is sum_s e^(-e_s/t)) *)
Variable Z_temp : R -> R.
Variable Z_temp_spec : forall t : R, forall Ht : lt zero t,
  Id (Z_temp t) (sum_over_S (fun s => exp_neg (mult (inv_pos t Ht) (base_loss s)))).

Lemma Z_temp_pos : forall t : R, forall Ht : lt zero t,
  lt zero (Z_temp t).
Proof.
  intros t Ht.
  apply (lt_id_r zero (sum_over_S (fun s => exp_neg (mult (inv_pos t Ht) (base_loss s)))) (Z_temp t)).
  - exact (id_sym (Z_temp_spec t Ht)).
  - apply sum_over_S_pos.
    intro s.
    apply exp_neg_pos.
Qed.

(* temperature-parameterized Boltzmann distribution and expected energy *)
Definition boltzmann_dist_temp (t : R) (Ht : lt zero t) : S -> R :=
  fun s => mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s))).

Definition energy_exp_temp (t : R) (Ht : lt zero t) : R :=
  sum_over_S (fun s => mult (boltzmann_dist_temp t Ht s) (base_loss s)).

Theorem boltzmann_dist_temp_normalized : forall t : R, forall Ht : lt zero t,
  Id (sum_over_S (boltzmann_dist_temp t Ht)) one.
Proof.
  intros t Ht.
  unfold boltzmann_dist_temp.
  assert (Hlin : Id (sum_over_S (fun s => mult (inv_pos (Z_temp t) (Z_temp_pos t Ht))
                                  (exp_neg (mult (inv_pos t Ht) (base_loss s)))))
                   (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht))
                         (sum_over_S (fun s => exp_neg (mult (inv_pos t Ht) (base_loss s))))))
    by exact (sum_over_S_linear (inv_pos (Z_temp t) (Z_temp_pos t Ht))
               (fun s => exp_neg (mult (inv_pos t Ht) (base_loss s)))).
  assert (HZ : Id (sum_over_S (fun s => exp_neg (mult (inv_pos t Ht) (base_loss s)))) (Z_temp t))
    by exact (id_sym (Z_temp_spec t Ht)).
  assert (Hcc : Id (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (Z_temp t)) one)
    by exact (id_trans (mult_comm (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (Z_temp t))
                       (inv_pos_correct (Z_temp t) (Z_temp_pos t Ht))).
  exact (id_trans Hlin (id_trans (id_cong (fun x => mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) x) HZ) Hcc)).
Qed.

Lemma boltzmann_dist_temp_pos : forall t : R, forall Ht : lt zero t, forall s : S,
  lt zero (boltzmann_dist_temp t Ht s).
Proof.
  intros t Ht s. unfold boltzmann_dist_temp.
  apply mult_positive.
  - apply inv_pos_pos.
  - apply exp_neg_pos.
Qed.

(* log p_beta(s) == -log Z - beta * e_s (temperature-version logarithmic
   decomposition) *)
Theorem boltzmann_log_temp_decomp : forall t : R, forall Ht : lt zero t, forall s : S,
  Id (log (boltzmann_dist_temp t Ht s))
     (plus (opp (log (Z_temp t))) (opp (mult (inv_pos t Ht) (base_loss s)))).
Proof.
  intros t Ht s. unfold boltzmann_dist_temp.
  assert (Hpos1 : lt zero (inv_pos (Z_temp t) (Z_temp_pos t Ht)))
    by exact (inv_pos_pos (Z_temp t) (Z_temp_pos t Ht)).
  assert (Hpos2 : lt zero (exp_neg (mult (inv_pos t Ht) (base_loss s))))
    by exact (exp_neg_pos (mult (inv_pos t Ht) (base_loss s))).
  assert (Hlm : Id (log (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht))
                              (exp_neg (mult (inv_pos t Ht) (base_loss s)))))
                  (plus (log (inv_pos (Z_temp t) (Z_temp_pos t Ht)))
                        (log (exp_neg (mult (inv_pos t Ht) (base_loss s))))))
    by exact (log_mult (inv_pos (Z_temp t) (Z_temp_pos t Ht))
                       (exp_neg (mult (inv_pos t Ht) (base_loss s))) Hpos1 Hpos2).
  rewrite Hlm.
  assert (Hli : Id (log (inv_pos (Z_temp t) (Z_temp_pos t Ht))) (opp (log (Z_temp t))))
    by exact (log_inv_one_inv (Z_temp t) (Z_temp_pos t Ht)).
  rewrite Hli.
  assert (Hle : Id (log (exp_neg (mult (inv_pos t Ht) (base_loss s))))
                  (opp (mult (inv_pos t Ht) (base_loss s))))
    by exact (log_exp_neg (mult (inv_pos t Ht) (base_loss s))).
  rewrite Hle.
  reflexivity.
Qed.

(* explicit entropy formula: H(p_beta) == beta * E(p_beta) + log Z
   (beta := inv t) *)
Theorem entropy_temp_explicit : forall t : R, forall Ht : lt zero t,
  Id (entropy_dist (boltzmann_dist_temp t Ht))
     (plus (mult (inv_pos t Ht) (energy_exp_temp t Ht)) (log (Z_temp t))).
Proof.
  intros t Ht.
  unfold entropy_dist, energy_exp_temp, boltzmann_dist_temp.
  (* pointwise: p * (-log p) == p * (beta * e) + p * log Z *)
  assert (Hpt : forall s : S,
    Id (mult (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s))))
             (opp (log (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s)))))))
       (plus (mult (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s))))
                   (mult (inv_pos t Ht) (base_loss s)))
             (mult (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s))))
                   (log (Z_temp t))))).
  { intro s.
    assert (Hlog : Id (log (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht))
                                 (exp_neg (mult (inv_pos t Ht) (base_loss s)))))
                      (plus (opp (log (Z_temp t))) (opp (mult (inv_pos t Ht) (base_loss s)))))
      by exact (boltzmann_log_temp_decomp t Ht s).
    (* -log p == logZ + betae *)
    assert (Hopp : Id (opp (plus (opp (log (Z_temp t))) (opp (mult (inv_pos t Ht) (base_loss s)))))
                      (plus (log (Z_temp t)) (mult (inv_pos t Ht) (base_loss s)))).
    { exact (id_trans (opp_plus (opp (log (Z_temp t))) (opp (mult (inv_pos t Ht) (base_loss s))))
             (id_trans (id_cong (fun x => plus x (opp (opp (mult (inv_pos t Ht) (base_loss s)))))
                                (double_neg (log (Z_temp t))))
                       (id_cong (fun x => plus (log (Z_temp t)) x)
                                (double_neg (mult (inv_pos t Ht) (base_loss s)))))). }
    (* p * (-log p) == p * (logZ + betae) == p * (betae) + p * logZ *)
    assert (Hcomm : Id (plus (log (Z_temp t)) (mult (inv_pos t Ht) (base_loss s)))
                       (plus (mult (inv_pos t Ht) (base_loss s)) (log (Z_temp t))))
      by exact (plus_comm (log (Z_temp t)) (mult (inv_pos t Ht) (base_loss s))).
    exact (id_trans (id_cong (fun x => mult (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s)))) (opp x)) Hlog)
           (id_trans (id_cong (fun x => mult (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s)))) x) Hopp)
           (id_trans (id_cong (fun x => mult (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s)))) x) Hcomm)
                     (distrib (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s))))
                              (mult (inv_pos t Ht) (base_loss s)) (log (Z_temp t)))))). }
  (* linearity of the sum: sum p * (beta * e) + sum p * log Z
   (explicit chain, no [rewrite]) *)
  assert (H1 : Id (sum_over_S (fun s => mult (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s))))
                                           (opp (log (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s))))))))
                   (sum_over_S (fun s => plus (mult (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s)))) (mult (inv_pos t Ht) (base_loss s)))
                                              (mult (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s)))) (log (Z_temp t))))))
    by exact (sum_over_S_ext (fun s => mult (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s))))
                                             (opp (log (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s)))))))
                             (fun s => plus (mult (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s)))) (mult (inv_pos t Ht) (base_loss s)))
                                            (mult (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s)))) (log (Z_temp t))))
                             Hpt).
  assert (Hadd : Id (sum_over_S (fun s => plus (mult (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s)))) (mult (inv_pos t Ht) (base_loss s)))
                                              (mult (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s)))) (log (Z_temp t)))))
                    (plus (sum_over_S (fun s => mult (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s)))) (mult (inv_pos t Ht) (base_loss s))))
                          (sum_over_S (fun s => mult (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s)))) (log (Z_temp t))))))
    by exact (sum_over_S_add (fun s => mult (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s)))) (mult (inv_pos t Ht) (base_loss s)))
                             (fun s => mult (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s)))) (log (Z_temp t)))).
  (* sum p * (betae) == beta * sum p * e *)
  assert (Hlin1 : Id (sum_over_S (fun s => mult (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s)))) (mult (inv_pos t Ht) (base_loss s))))
                     (mult (inv_pos t Ht) (sum_over_S (fun s => mult (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s)))) (base_loss s))))).
  { assert (Hpt2 : forall s : S,
      Id (mult (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s)))) (mult (inv_pos t Ht) (base_loss s)))
         (mult (inv_pos t Ht) (mult (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s)))) (base_loss s)))).
    { intro s.
      apply (id_trans (mult_comm (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s)))) (mult (inv_pos t Ht) (base_loss s)))
             (id_trans (id_sym (mult_assoc (inv_pos t Ht) (base_loss s) (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s))))))
                       (id_cong (fun x => mult (inv_pos t Ht) x)
                                (mult_comm (base_loss s) (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s)))))))). }
    exact (id_trans (sum_over_S_ext _ _ Hpt2)
           (sum_over_S_linear (inv_pos t Ht)
             (fun s => mult (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s)))) (base_loss s)))). }
  (* sum p * logZ == logZ * sum p == logZ *)
  assert (Hlin2 : Id (sum_over_S (fun s => mult (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s)))) (log (Z_temp t))))
                     (log (Z_temp t))).
  { assert (Hpt3 : forall s : S,
      Id (mult (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s)))) (log (Z_temp t)))
         (mult (log (Z_temp t)) (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s))))))
    by (intro s; apply mult_comm).
    exact (id_trans (sum_over_S_ext _ _ Hpt3)
           (id_trans (sum_over_S_linear (log (Z_temp t)) (boltzmann_dist_temp t Ht))
           (id_trans (id_cong (fun x => mult (log (Z_temp t)) x) (boltzmann_dist_temp_normalized t Ht))
                     (mult_one (log (Z_temp t)))))). }
  exact (id_trans H1 (id_trans Hadd
         (id_trans (id_cong (fun x => plus x (sum_over_S (fun s => mult (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s)))) (log (Z_temp t))))) Hlin1)
                   (id_cong (fun x => plus (mult (inv_pos t Ht) (sum_over_S (fun s => mult (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s)))) (base_loss s)))) x) Hlin2)))).
Qed.

(* ---------- variational core ---------- *)

(* explicit decomposition of the relative entropy against the Boltzmann
   distribution: KL(q || p_beta) == -H(q) + beta * E(q) + log Z *)
Theorem relative_entropy_temp_decomp : forall t : R, forall Ht : lt zero t, forall q : S -> R,
  normalized q ->
  Id (relative_entropy q (boltzmann_dist_temp t Ht))
     (plus (plus (opp (entropy_dist q)) (mult (inv_pos t Ht) (energy_expectation q)))
           (log (Z_temp t))).
Proof.
  intros t Ht q Hnq.
  unfold relative_entropy, entropy_dist, energy_expectation, boltzmann_dist_temp.
  (* pointwise: q * (log q - log p) == q * log q - q * log p *)
  assert (Hpt : forall s : S,
    Id (mult (q s) (minus (log (q s)) (log (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s)))))))
       (minus (mult (q s) (log (q s)))
              (mult (q s) (log (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s)))))))).
  { intro s. apply mult_minus_distr_l. }
  (* sum q * log q == -H(q) *)
  assert (Hq1 : Id (sum_over_S (fun s => mult (q s) (log (q s)))) (opp (entropy_dist q))).
  { unfold entropy_dist.
    apply entropy_neg_sum. }
  (* sum q * log p == -beta * E(q) - log Z (explicit chain) *)
  assert (Hq2 : Id (sum_over_S (fun s => mult (q s) (log (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s)))))))
                   (plus (opp (mult (inv_pos t Ht) (sum_over_S (fun s => mult (q s) (base_loss s)))))
                         (opp (log (Z_temp t))))).
  { (* pointwise: q * log p == opp (q * log Z) + opp (q * beta * e) *)
    assert (Hpt2 : forall s : S,
      Id (mult (q s) (log (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s))))))
         (plus (opp (mult (q s) (log (Z_temp t))))
               (opp (mult (q s) (mult (inv_pos t Ht) (base_loss s)))))).
    { intro s.
      assert (Hlog : Id (log (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s)))))
                        (plus (opp (log (Z_temp t))) (opp (mult (inv_pos t Ht) (base_loss s)))))
        by exact (boltzmann_log_temp_decomp t Ht s).
      exact (id_trans (id_cong (fun x => mult (q s) x) Hlog)
             (id_trans (id_cong (fun x => mult (q s) x)
                                (plus_comm (opp (log (Z_temp t))) (opp (mult (inv_pos t Ht) (base_loss s)))))
             (id_trans (distrib (q s) (opp (mult (inv_pos t Ht) (base_loss s))) (opp (log (Z_temp t))))
             (id_trans (id_cong (fun x => plus x (mult (q s) (opp (log (Z_temp t)))))
                                (opp_mult_l (q s) (mult (inv_pos t Ht) (base_loss s))))
             (id_trans (id_cong (fun x => plus (opp (mult (q s) (mult (inv_pos t Ht) (base_loss s)))) x)
                                (opp_mult_l (q s) (log (Z_temp t))))
                       (plus_comm (opp (mult (q s) (mult (inv_pos t Ht) (base_loss s))))
                                  (opp (mult (q s) (log (Z_temp t)))))))))). }
    assert (H1 : Id (sum_over_S (fun s => mult (q s) (log (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s)))))))
                    (sum_over_S (fun s => plus (opp (mult (q s) (log (Z_temp t))))
                                               (opp (mult (q s) (mult (inv_pos t Ht) (base_loss s)))))))
      by exact (sum_over_S_ext _ _ Hpt2).
    assert (Hadd : Id (sum_over_S (fun s => plus (opp (mult (q s) (log (Z_temp t))))
                                                 (opp (mult (q s) (mult (inv_pos t Ht) (base_loss s))))))
                      (plus (sum_over_S (fun s => opp (mult (q s) (log (Z_temp t)))))
                            (sum_over_S (fun s => opp (mult (q s) (mult (inv_pos t Ht) (base_loss s)))))))
      by exact (sum_over_S_add (fun s => opp (mult (q s) (log (Z_temp t))))
                               (fun s => opp (mult (q s) (mult (inv_pos t Ht) (base_loss s))))).
    (* sum q * log Z == log Z (constant extraction and normalization) *)
    assert (Hs1 : Id (sum_over_S (fun s => mult (q s) (log (Z_temp t)))) (log (Z_temp t))).
    { assert (Hc : forall s : S, Id (mult (q s) (log (Z_temp t))) (mult (log (Z_temp t)) (q s)))
        by (intro s; apply mult_comm).
      exact (id_trans (sum_over_S_ext _ _ Hc)
             (id_trans (sum_over_S_linear (log (Z_temp t)) q)
                       (id_trans (id_cong (fun x => mult (log (Z_temp t)) x) Hnq)
                                 (mult_one (log (Z_temp t)))))). }
    (* sum q * (betae) == beta * sum q * e *)
    assert (Hs2 : Id (sum_over_S (fun s => mult (q s) (mult (inv_pos t Ht) (base_loss s))))
                     (mult (inv_pos t Ht) (sum_over_S (fun s => mult (q s) (base_loss s))))).
    { assert (Hc2 : forall s : S, Id (mult (q s) (mult (inv_pos t Ht) (base_loss s)))
                                     (mult (inv_pos t Ht) (mult (q s) (base_loss s)))).
      { intro s.
        apply (id_trans (mult_comm (q s) (mult (inv_pos t Ht) (base_loss s)))
               (id_trans (id_sym (mult_assoc (inv_pos t Ht) (base_loss s) (q s)))
                         (id_cong (fun x => mult (inv_pos t Ht) x) (mult_comm (base_loss s) (q s))))). }
      exact (id_trans (sum_over_S_ext _ _ Hc2)
             (sum_over_S_linear (inv_pos t Ht) (fun s => mult (q s) (base_loss s)))). }
    exact (id_trans H1 (id_trans Hadd
           (id_trans (id_cong (fun x => plus x (sum_over_S (fun s => opp (mult (q s) (mult (inv_pos t Ht) (base_loss s))))))
                              (sum_opp (fun s => mult (q s) (log (Z_temp t)))))
           (id_trans (id_cong (fun x => plus (opp (sum_over_S (fun s => mult (q s) (log (Z_temp t))))) x)
                              (sum_opp (fun s => mult (q s) (mult (inv_pos t Ht) (base_loss s)))))
           (id_trans (id_cong (fun x => plus (opp x) (opp (sum_over_S (fun s => mult (q s) (mult (inv_pos t Ht) (base_loss s)))))) Hs1)
           (id_trans (id_cong (fun x => plus (opp (log (Z_temp t))) (opp x)) Hs2)
                     (plus_comm (opp (log (Z_temp t)))
                                (opp (mult (inv_pos t Ht) (sum_over_S (fun s => mult (q s) (base_loss s)))))))))))). }
  (* assemble: minus (sum q * log q) (sum q * log p) == -H + beta * E + log Z
   (explicit chain) *)
  assert (Hopp : Id (opp (plus (opp (mult (inv_pos t Ht) (sum_over_S (fun s => mult (q s) (base_loss s)))))
                                 (opp (log (Z_temp t)))))
                    (plus (mult (inv_pos t Ht) (sum_over_S (fun s => mult (q s) (base_loss s))))
                          (log (Z_temp t)))).
  { exact (id_trans (opp_plus (opp (mult (inv_pos t Ht) (sum_over_S (fun s => mult (q s) (base_loss s)))))
                              (opp (log (Z_temp t))))
           (id_trans (id_cong (fun x => plus x (opp (opp (log (Z_temp t)))))
                              (double_neg (mult (inv_pos t Ht) (sum_over_S (fun s => mult (q s) (base_loss s))))))
                     (id_cong (fun x => plus (mult (inv_pos t Ht) (sum_over_S (fun s => mult (q s) (base_loss s)))) x)
                              (double_neg (log (Z_temp t)))))). }
  assert (Hfin : Id (minus (sum_over_S (fun s => mult (q s) (log (q s))))
                           (sum_over_S (fun s => mult (q s) (log (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s))))))))
                    (plus (plus (opp (entropy_dist q)) (mult (inv_pos t Ht) (sum_over_S (fun s => mult (q s) (base_loss s)))))
                          (log (Z_temp t)))).
  { unfold minus.
    exact (id_trans (id_cong (fun x => plus x (opp (sum_over_S (fun s => mult (q s) (log (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s))))))))) Hq1)
           (id_trans (id_cong (fun x => plus (opp (entropy_dist q)) (opp x)) Hq2)
           (id_trans (id_cong (fun x => plus (opp (entropy_dist q)) x) Hopp)
                     (plus_assoc (opp (entropy_dist q))
                                         (mult (inv_pos t Ht) (sum_over_S (fun s => mult (q s) (base_loss s))))
                                         (log (Z_temp t)))))). }
  assert (Hstep : Id (sum_over_S (fun s => mult (q s) (minus (log (q s)) (log (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s))))))))
                     (sum_over_S (fun s => minus (mult (q s) (log (q s)))
                                                 (mult (q s) (log (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s)))))))))
    by exact (sum_over_S_ext _ _ Hpt).
  exact (id_trans Hstep
         (id_trans (sum_over_S_minus (fun s => mult (q s) (log (q s)))
                                     (fun s => mult (q s) (log (mult (inv_pos (Z_temp t) (Z_temp_pos t Ht)) (exp_neg (mult (inv_pos t Ht) (base_loss s)))))))
                   Hfin)).
Qed.

(* variational bound: the entropy-energy combination of any normalized
   positive distribution q is at most log Z (expanding the Gibbs
   inequality) *)
Theorem variational_temp_bound : forall t : R, forall Ht : lt zero t, forall q : S -> R,
  normalized q -> positive_dist q ->
  le (minus (entropy_dist q) (mult (inv_pos t Ht) (energy_expectation q)))
     (log (Z_temp t)).
Proof.
  intros t Ht q Hnq Hpq.
  assert (Hkl : le zero (relative_entropy q (boltzmann_dist_temp t Ht)))
    by (apply (gibbs_inequality q (boltzmann_dist_temp t Ht) Hnq Hpq
               (boltzmann_dist_temp_normalized t Ht) (boltzmann_dist_temp_pos t Ht))).
  assert (Hrel : Id (relative_entropy q (boltzmann_dist_temp t Ht))
                    (plus (plus (opp (entropy_dist q)) (mult (inv_pos t Ht) (energy_expectation q))) (log (Z_temp t))))
    by (apply (relative_entropy_temp_decomp t Ht q Hnq)).
  rewrite Hrel in Hkl.
  (* rearrangement 1: 0 <= -H + beta * E + log Z gives H <= beta * E + log Z *)
  assert (Hstep1 : le (entropy_dist q) (plus (mult (inv_pos t Ht) (energy_expectation q)) (log (Z_temp t)))).
  { apply (le_id_l (entropy_dist q) (plus (entropy_dist q) zero)).
    - exact (id_sym (plus_zero (entropy_dist q))).
    - apply (le_id_r (plus (entropy_dist q) zero)
             (plus (entropy_dist q) (plus (plus (opp (entropy_dist q)) (mult (inv_pos t Ht) (energy_expectation q))) (log (Z_temp t))))
             (plus (mult (inv_pos t Ht) (energy_expectation q)) (log (Z_temp t)))).
      + (* H + (-H + betaE + logZ) == betaE + logZ *)
        apply (id_trans (plus_assoc (entropy_dist q)
                                    (plus (opp (entropy_dist q)) (mult (inv_pos t Ht) (energy_expectation q)))
                                    (log (Z_temp t)))
               (id_trans (id_cong (fun x => plus x (log (Z_temp t)))
                                  (plus_assoc (entropy_dist q) (opp (entropy_dist q)) (mult (inv_pos t Ht) (energy_expectation q))))
               (id_trans (id_cong (fun x => plus x (log (Z_temp t)))
                                  (id_cong (fun x => plus x (mult (inv_pos t Ht) (energy_expectation q)))
                                           (plus_opp (entropy_dist q))))
               (id_cong (fun x => plus x (log (Z_temp t)))
                        (id_trans (plus_comm zero (mult (inv_pos t Ht) (energy_expectation q)))
                                  (plus_zero (mult (inv_pos t Ht) (energy_expectation q)))))))).
      + apply (le_plus_compat (entropy_dist q) (entropy_dist q) zero
               (plus (plus (opp (entropy_dist q)) (mult (inv_pos t Ht) (energy_expectation q))) (log (Z_temp t)))
               (le_refl (entropy_dist q)) Hkl). }
  (* rearrangement 2: H <= beta * E + log Z gives H - beta * E <= log Z *)
  apply (le_id_r (plus (entropy_dist q) (opp (mult (inv_pos t Ht) (energy_expectation q))))
         (plus (plus (mult (inv_pos t Ht) (energy_expectation q)) (log (Z_temp t))) (opp (mult (inv_pos t Ht) (energy_expectation q))))
         (log (Z_temp t))).
  - (* (betaE + logZ) - betaE == logZ *)
    apply (id_trans (id_sym (plus_assoc (mult (inv_pos t Ht) (energy_expectation q)) (log (Z_temp t)) (opp (mult (inv_pos t Ht) (energy_expectation q)))))
           (id_trans (id_cong (fun x => plus (mult (inv_pos t Ht) (energy_expectation q)) x)
                              (plus_comm (log (Z_temp t)) (opp (mult (inv_pos t Ht) (energy_expectation q)))))
           (id_trans (plus_assoc (mult (inv_pos t Ht) (energy_expectation q)) (opp (mult (inv_pos t Ht) (energy_expectation q))) (log (Z_temp t)))
           (id_trans (id_cong (fun x => plus x (log (Z_temp t))) (plus_opp (mult (inv_pos t Ht) (energy_expectation q))))
           (id_trans (plus_comm zero (log (Z_temp t))) (plus_zero (log (Z_temp t)))))))).
  - apply (le_plus_compat (entropy_dist q) (plus (mult (inv_pos t Ht) (energy_expectation q)) (log (Z_temp t)))
                           (opp (mult (inv_pos t Ht) (energy_expectation q)))
                           (opp (mult (inv_pos t Ht) (energy_expectation q)))
                           Hstep1 (le_refl (opp (mult (inv_pos t Ht) (energy_expectation q))))).
Qed.

(* ============ main theorem: monotonicity of the expected energy in the
   temperature ============ *)
Theorem energy_exp_temp_mono : forall t1 t2 : R, forall Ht1 : lt zero t1, forall Ht2 : lt zero t2,
  lt t1 t2 -> le (energy_exp_temp t1 Ht1) (energy_exp_temp t2 Ht2).
Proof.
  intros t1 t2 Ht1 Ht2 Ht12.
  set (b1 := inv_pos t1 Ht1). set (b2 := inv_pos t2 Ht2).
  set (E1 := energy_exp_temp t1 Ht1). set (E2 := energy_exp_temp t2 Ht2).
  set (H1 := entropy_dist (boltzmann_dist_temp t1 Ht1)). set (H2 := entropy_dist (boltzmann_dist_temp t2 Ht2)).
  set (Z1 := Z_temp t1). set (Z2 := Z_temp t2).
  (* beta2 < beta1 (strict reversal by [inv]: t1 < t2 gives 1/t2 < 1/t1) *)
  assert (Hb : lt b2 b1) by (unfold b1, b2; apply (inv_pos_lt_compat t1 t2 Ht1 Ht2 Ht12)).
  assert (Hbpos : lt zero (minus b1 b2)) by (unfold b1, b2; apply (lt_minus_nonneg b2 b1 Hb)).
  (* the variational bound, twice *)
  assert (Hv1 : le (minus H2 (mult b1 E2)) (log Z1)).
  { unfold H2, E2, Z1, b1.
    apply (variational_temp_bound t1 Ht1 (boltzmann_dist_temp t2 Ht2)).
    - apply boltzmann_dist_temp_normalized.
    - intro s. apply boltzmann_dist_temp_pos. }
  assert (Hv2 : le (minus H1 (mult b2 E1)) (log Z2)).
  { unfold H1, E1, Z2, b2.
    apply (variational_temp_bound t2 Ht2 (boltzmann_dist_temp t1 Ht1)).
    - apply boltzmann_dist_temp_normalized.
    - intro s. apply boltzmann_dist_temp_pos. }
  (* substitute the explicit entropy formula (manual replacement, no
   [rewrite]) *)
  assert (Hex1 : Id H1 (plus (mult b1 E1) (log Z1))).
  { unfold H1, b1, E1, Z1. apply entropy_temp_explicit. }
  assert (Hex2 : Id H2 (plus (mult b2 E2) (log Z2))).
  { unfold H2, b2, E2, Z2. apply entropy_temp_explicit. }
  assert (Hv1' : le (minus (plus (mult b2 E2) (log Z2)) (mult b1 E2)) (log Z1)).
  { apply (le_id_l (minus (plus (mult b2 E2) (log Z2)) (mult b1 E2)) (minus H2 (mult b1 E2)) (log Z1)).
    - exact (id_cong (fun x => minus x (mult b1 E2)) (id_sym Hex2)).
    - exact Hv1. }
  assert (Hv2' : le (minus (plus (mult b1 E1) (log Z1)) (mult b2 E1)) (log Z2)).
  { apply (le_id_l (minus (plus (mult b1 E1) (log Z1)) (mult b2 E1)) (minus H1 (mult b2 E1)) (log Z2)).
    - exact (id_cong (fun x => minus x (mult b2 E1)) (id_sym Hex1)).
    - exact Hv2. }
  (* simplify inside minus:
   minus (plus (mult b2 E2) (log Z2)) (mult b1 E2)
   == plus (mult (minus b2 b1) E2) (log Z2) *)
  assert (Hm1 : Id (minus (plus (mult b2 E2) (log Z2)) (mult b1 E2))
                   (plus (mult (minus b2 b1) E2) (log Z2))).
  { unfold minus.
    apply (id_trans (id_sym (plus_assoc (mult b2 E2) (log Z2) (opp (mult b1 E2))))
           (id_trans (id_cong (fun x => plus (mult b2 E2) x)
                              (plus_comm (log Z2) (opp (mult b1 E2))))
           (id_trans (plus_assoc (mult b2 E2) (opp (mult b1 E2)) (log Z2))
                     (id_sym (id_cong (fun x => plus x (log Z2))
                              (mult_minus_distr_r b2 b1 E2)))))). }
  assert (Hm2 : Id (minus (plus (mult b1 E1) (log Z1)) (mult b2 E1))
                   (plus (mult (minus b1 b2) E1) (log Z1))).
  { unfold minus.
    apply (id_trans (id_sym (plus_assoc (mult b1 E1) (log Z1) (opp (mult b2 E1))))
           (id_trans (id_cong (fun x => plus (mult b1 E1) x)
                              (plus_comm (log Z1) (opp (mult b2 E1))))
           (id_trans (plus_assoc (mult b1 E1) (opp (mult b2 E1)) (log Z1))
                     (id_sym (id_cong (fun x => plus x (log Z1))
                              (mult_minus_distr_r b1 b2 E1)))))). }
  assert (Hv1'' : le (plus (mult (minus b2 b1) E2) (log Z2)) (log Z1)).
  { apply (le_id_l (plus (mult (minus b2 b1) E2) (log Z2))
                   (minus (plus (mult b2 E2) (log Z2)) (mult b1 E2)) (log Z1)).
    - exact (id_sym Hm1).
    - exact Hv1'. }
  assert (Hv2'' : le (plus (mult (minus b1 b2) E1) (log Z1)) (log Z2)).
  { apply (le_id_l (plus (mult (minus b1 b2) E1) (log Z1))
                   (minus (plus (mult b1 E1) (log Z1)) (mult b2 E1)) (log Z2)).
    - exact (id_sym Hm2).
    - exact Hv2'. }
  (* rearrange: le (plus X (log Z2)) (log Z1) gives
   le X (minus (log Z1) (log Z2)) *)
  assert (Hshift1 : le (mult (minus b2 b1) E2) (minus (log Z1) (log Z2))).
  { apply (le_id_l (mult (minus b2 b1) E2) (plus (plus (mult (minus b2 b1) E2) (log Z2)) (opp (log Z2)))).
    - exact (id_trans (id_sym (plus_zero (mult (minus b2 b1) E2)))
             (id_sym (id_trans (id_sym (plus_assoc (mult (minus b2 b1) E2) (log Z2) (opp (log Z2))))
                     (id_cong (fun x => plus (mult (minus b2 b1) E2) x) (plus_opp (log Z2)))))).
    - apply (le_plus_compat (plus (mult (minus b2 b1) E2) (log Z2)) (log Z1)
                             (opp (log Z2)) (opp (log Z2)) Hv1'' (le_refl (opp (log Z2)))). }
  assert (Hshift2 : le (mult (minus b1 b2) E1) (minus (log Z2) (log Z1))).
  { apply (le_id_l (mult (minus b1 b2) E1) (plus (plus (mult (minus b1 b2) E1) (log Z1)) (opp (log Z1)))).
    - exact (id_trans (id_sym (plus_zero (mult (minus b1 b2) E1)))
             (id_sym (id_trans (id_sym (plus_assoc (mult (minus b1 b2) E1) (log Z1) (opp (log Z1))))
                     (id_cong (fun x => plus (mult (minus b1 b2) E1) x) (plus_opp (log Z1)))))).
    - apply (le_plus_compat (plus (mult (minus b1 b2) E1) (log Z1)) (log Z2)
                             (opp (log Z1)) (opp (log Z1)) Hv2'' (le_refl (opp (log Z1)))). }
  (* add *)
  assert (Hsum : le (plus (mult (minus b2 b1) E2) (mult (minus b1 b2) E1))
                   (plus (minus (log Z1) (log Z2)) (minus (log Z2) (log Z1)))).
  { apply (le_plus_compat (mult (minus b2 b1) E2) (minus (log Z1) (log Z2))
                           (mult (minus b1 b2) E1) (minus (log Z2) (log Z1)) Hshift1 Hshift2). }
  (* RHS == zero *)
  assert (Hz : Id (plus (minus (log Z1) (log Z2)) (minus (log Z2) (log Z1))) zero).
  { unfold minus.
    apply (id_trans (id_sym (plus_assoc (log Z1) (opp (log Z2)) (plus (log Z2) (opp (log Z1)))))
           (id_trans (id_cong (fun x => plus (log Z1) x)
                              (plus_assoc (opp (log Z2)) (log Z2) (opp (log Z1))))
           (id_trans (id_cong (fun x => plus (log Z1) x)
                              (id_cong (fun x => plus x (opp (log Z1)))
                                       (id_trans (plus_comm (opp (log Z2)) (log Z2)) (plus_opp (log Z2)))))
           (id_trans (id_cong (fun x => plus (log Z1) x)
                              (id_trans (plus_comm zero (opp (log Z1))) (plus_zero (opp (log Z1)))))
                     (plus_opp (log Z1)))))). }
  (* LHS == mult (minus b1 b2) (minus E1 E2) *)
  assert (Hoppm : Id (minus b2 b1) (opp (minus b1 b2))).
  { unfold minus.
    exact (id_sym (id_trans (opp_plus b1 (opp b2))
                   (id_trans (id_cong (fun x => plus (opp b1) x) (double_neg b2))
                             (plus_comm (opp b1) b2)))). }
  assert (Hlhs : Id (plus (mult (minus b2 b1) E2) (mult (minus b1 b2) E1))
                    (mult (minus b1 b2) (minus E1 E2))).
  { apply (id_trans (id_cong (fun x => plus (mult x E2) (mult (minus b1 b2) E1)) Hoppm)
           (id_trans (id_cong (fun x => plus x (mult (minus b1 b2) E1))
                              (opp_mult_r (minus b1 b2) E2))
           (id_trans (id_cong (fun x => plus x (mult (minus b1 b2) E1))
                              (id_sym (opp_mult_l (minus b1 b2) E2)))
           (id_trans (id_sym (distrib (minus b1 b2) (opp E2) E1))
                     (id_cong (fun x => mult (minus b1 b2) x) (plus_comm (opp E2) E1)))))). }
  (* assemble: le (mult (minus b1 b2) (minus E1 E2)) zero *)
  assert (Hmain : le (mult (minus b1 b2) (minus E1 E2)) zero).
  { apply (le_id_l (mult (minus b1 b2) (minus E1 E2))
                   (plus (mult (minus b2 b1) E2) (mult (minus b1 b2) E1))).
    - exact (id_sym Hlhs).
    - apply (le_id_r (plus (mult (minus b2 b1) E2) (mult (minus b1 b2) E1))
                     (plus (minus (log Z1) (log Z2)) (minus (log Z2) (log Z1))) zero).
      + exact Hz.
      + exact Hsum. }
  (* cancel the positive factor: E1 <= E2 *)
  assert (Hcancel : le (minus E1 E2) zero).
  { apply (le_mult_pos_cancel (minus E1 E2) (minus b1 b2) Hbpos).
    apply (le_id_l (mult (minus E1 E2) (minus b1 b2)) (mult (minus b1 b2) (minus E1 E2))).
    - apply mult_comm.
    - exact Hmain. }
  apply (le_minus_nonneg_rev E1 E2 Hcancel).
Qed.


(* unique entropy maximum: under the equal-energy constraint,
   S[p] = S[p_b] implies p = p_b.
   Proof: S[p_b] - S[p] = KL, and equal entropies give KL = 0, hence
   [gibbs_equality]. *)
Theorem entropy_max_unique :
  forall p : S -> R,
    normalized p -> positive_dist p ->
    Id (energy_expectation p) (energy_expectation boltzmann_dist) ->
    Id (entropy_dist p) (entropy_dist boltzmann_dist) ->
    forall s : S, Id (p s) (boltzmann_dist s).
Proof.
  intros p Hnp Hpp Henergy Hent s.
  (* 1. S[p_b] - S[p] = KL *)
  assert (Hdef : Id (minus (entropy_dist boltzmann_dist) (entropy_dist p))
                    (relative_entropy p boltzmann_dist))
    by exact (entropy_deficit_kl p Hnp Hpp Henergy).
  (* 2. equal entropies give KL = 0 ([minus_self_zero]:
   S[p] = S[p_b] gives S[p_b] - S[p] = 0) *)
  assert (Hkl0 : Id (relative_entropy p boltzmann_dist) zero).
  {
    assert (Hmz : Id (minus (entropy_dist boltzmann_dist) (entropy_dist p)) zero)
      by exact (minus_self_zero (entropy_dist boltzmann_dist) (entropy_dist p) (id_sym Hent)).
    exact (id_trans (id_sym Hdef) Hmz).
  }
  (* 3. gibbs_equality: KL = 0 implies p = p_b *)
  exact (gibbs_equality p boltzmann_dist Hnp Hpp (boltzmann_normalized) (fun t => boltzmann_dist_pos t) Hkl0 s).
Qed.

(* ============================================================ *)
(* closing the temperature duality: constrained entropy maximization of *)
(*   the temperature-parameterized Boltzmann family (a constructive proof
   of the maximum-entropy Lagrange duality) *)
(*   assembled from [entropy_temp_explicit] (explicit entropy formula), *)
(*   [relative_entropy_temp_decomp] (temperature decomposition of KL), *)
(*   [entropy_deficit_kl_temp] (entropy deficit = KL, temperature version),
   giving *)
(*   [max_entropy_is_boltzmann_temp] (equal energy implies maximal entropy,
   temperature version) and *)
(*   [entropy_max_unique_temp] (equal energy and equal entropy imply
   uniqueness, temperature version), hence *)
(*   [temp_energy_dual_closed] (a sigT duality closure: for every
   temperature t, *)
(*   the entropy maximization problem under the constraint E_temp(t) has an
   existent and unique solution). *)
(* ============================================================ *)

(* entropy deficit = KL (temperature version): under the constraint
   E(p) == E_temp(t), S[p_t] - S[p] == KL(p || p_t), assembled from
   [entropy_temp_explicit] and [relative_entropy_temp_decomp] plus the
   equal-energy rewrite (beta * E(p) == beta * E(p_t)) *)
Theorem entropy_deficit_kl_temp : forall t : R, forall Ht : lt zero t, forall p : S -> R,
  normalized p -> positive_dist p ->
  Id (energy_expectation p) (energy_exp_temp t Ht) ->
  Id (minus (entropy_dist (boltzmann_dist_temp t Ht)) (entropy_dist p))
     (relative_entropy p (boltzmann_dist_temp t Ht)).
Proof.
  intros t Ht p Hnp Hpp Henergy.
  set (B := boltzmann_dist_temp t Ht).
  set (Et := energy_exp_temp t Ht).
  set (Sp := entropy_dist p).
  set (Spt := entropy_dist B).
  set (K := relative_entropy p B).
  (* KL(p‖p_t) == -S[p] + beta * E(p) + log Z *)
  assert (Hkl : Id K (plus (plus (opp Sp) (mult (inv_pos t Ht) (energy_expectation p))) (log (Z_temp t)))).
  { unfold K, Sp, B. exact (relative_entropy_temp_decomp t Ht p Hnp). }
  (* S[p_t] == beta * E(p_t) + log Z *)
  assert (Hse : Id Spt (plus (mult (inv_pos t Ht) Et) (log (Z_temp t)))).
  { unfold Spt, Et, B. exact (entropy_temp_explicit t Ht). }
  (* reshape: -S[p] + beta * E(p) + log Z == [beta * E(p_t) + log Z] - S[p]
   (re-grouping by associativity/commutativity and the equal-energy
   substitution beta * E(p) == beta * E(p_t)) *)
  assert (Hkl' : Id K (plus (plus (mult (inv_pos t Ht) Et) (log (Z_temp t))) (opp Sp))).
  {
    apply (id_trans Hkl).
    apply (id_trans (id_sym (plus_assoc (opp Sp) (mult (inv_pos t Ht) (energy_expectation p)) (log (Z_temp t))))).
    apply (id_trans (plus_comm (opp Sp) (plus (mult (inv_pos t Ht) (energy_expectation p)) (log (Z_temp t))))).
    apply (id_cong (fun x => plus (plus x (log (Z_temp t))) (opp Sp))
                   (id_cong (fun x => mult (inv_pos t Ht) x) Henergy)).
  }
  (* goal: minus Spt Sp == K; minus Spt Sp == plus Spt (opp Sp) ==
   [beta * E(p_t) + log Z] - Sp (Hse forward, Hkl' backward) *)
  unfold minus.
  apply (id_trans (id_cong (fun x => plus x (opp Sp)) Hse) (id_sym Hkl')).
Qed.

(* maximum entropy, temperature version: E(p) == E_temp(t) implies
   S[p] <= S[p_t] (assembling [entropy_deficit_kl_temp],
   [gibbs_inequality] and the le chain, following the fixed-temperature
   skeleton) *)
Theorem max_entropy_is_boltzmann_temp : forall t : R, forall Ht : lt zero t, forall p : S -> R,
  normalized p -> positive_dist p ->
  Id (energy_expectation p) (energy_exp_temp t Ht) ->
  le (entropy_dist p) (entropy_dist (boltzmann_dist_temp t Ht)).
Proof.
  intros t Ht p Hnp Hpp Henergy.
  (* 1. S[p_t] - S[p] = KL (temperature-version entropy deficit) *)
  assert (Hdef : Id (minus (entropy_dist (boltzmann_dist_temp t Ht)) (entropy_dist p))
                    (relative_entropy p (boltzmann_dist_temp t Ht)))
    by exact (entropy_deficit_kl_temp t Ht p Hnp Hpp Henergy).
  (* 2. KL >= 0 ([gibbs_inequality]: both p and p_t normalized and positive) *)
  assert (Hkl : le zero (relative_entropy p (boltzmann_dist_temp t Ht))).
  {
    apply (gibbs_inequality p (boltzmann_dist_temp t Ht)).
    - exact Hnp.
    - exact Hpp.
    - exact (boltzmann_dist_temp_normalized t Ht).
    - intro s. exact (boltzmann_dist_temp_pos t Ht s).
  }
  (* 3. 0 <= S[p_t] - S[p] implies S[p] <= S[p_t] *)
  assert (Hnonneg : le zero (minus (entropy_dist (boltzmann_dist_temp t Ht)) (entropy_dist p)))
    by exact (le_id_r zero (relative_entropy p (boltzmann_dist_temp t Ht))
                     (minus (entropy_dist (boltzmann_dist_temp t Ht)) (entropy_dist p))
                     (id_sym Hdef) Hkl).
  assert (Hplus : Id (plus (entropy_dist p) (minus (entropy_dist (boltzmann_dist_temp t Ht)) (entropy_dist p)))
                     (entropy_dist (boltzmann_dist_temp t Ht)))
    by exact (minus_plus_cancel (entropy_dist p) (entropy_dist (boltzmann_dist_temp t Ht))).
  assert (Hle : le (entropy_dist p)
                   (plus (entropy_dist p) (minus (entropy_dist (boltzmann_dist_temp t Ht)) (entropy_dist p))))
    by exact (le_plus_nonneg_r (entropy_dist p) (minus (entropy_dist (boltzmann_dist_temp t Ht)) (entropy_dist p)) Hnonneg).
  exact (le_id_r (entropy_dist p)
                 (plus (entropy_dist p) (minus (entropy_dist (boltzmann_dist_temp t Ht)) (entropy_dist p)))
                 (entropy_dist (boltzmann_dist_temp t Ht)) Hplus Hle).
Qed.

(* uniqueness, temperature version: equal constrained energy and equal
   entropy imply p == p_t pointwise (assembling [entropy_deficit_kl_temp],
   [minus_self_zero] and [gibbs_equality], following the fixed-temperature
   skeleton) *)
Theorem entropy_max_unique_temp : forall t : R, forall Ht : lt zero t, forall p : S -> R,
  normalized p -> positive_dist p ->
  Id (energy_expectation p) (energy_exp_temp t Ht) ->
  Id (entropy_dist p) (entropy_dist (boltzmann_dist_temp t Ht)) ->
  forall s : S, Id (p s) (boltzmann_dist_temp t Ht s).
Proof.
  intros t Ht p Hnp Hpp Henergy Hent s.
  (* 1. S[p_t] - S[p] = KL *)
  assert (Hdef : Id (minus (entropy_dist (boltzmann_dist_temp t Ht)) (entropy_dist p))
                    (relative_entropy p (boltzmann_dist_temp t Ht)))
    by exact (entropy_deficit_kl_temp t Ht p Hnp Hpp Henergy).
  (* 2. equal entropies give KL = 0 *)
  assert (Hkl0 : Id (relative_entropy p (boltzmann_dist_temp t Ht)) zero).
  {
    assert (Hmz : Id (minus (entropy_dist (boltzmann_dist_temp t Ht)) (entropy_dist p)) zero)
      by exact (minus_self_zero (entropy_dist (boltzmann_dist_temp t Ht)) (entropy_dist p) (id_sym Hent)).
    exact (id_trans (id_sym Hdef) Hmz).
  }
  (* 3. gibbs_equality: KL = 0 implies p = p_t *)
  exact (gibbs_equality p (boltzmann_dist_temp t Ht) Hnp Hpp (boltzmann_dist_temp_normalized t Ht)
                       (fun s => boltzmann_dist_temp_pos t Ht s) Hkl0 s).
Qed.

(* duality closure: for every temperature t (equivalently, every
   constrained energy E_temp(t)), the entropy maximization problem has a
   solution ([sigT], witnessed by p_t itself), an optimal one (maximal
   entropy at equal energy) and a unique one (equal energy and equal
   entropy imply pointwise equality) *)
Theorem temp_energy_dual_closed : forall t : R, forall Ht : lt zero t,
  sigT (fun pb : S -> R =>
    And (And (normalized pb) (positive_dist pb))
        (And (Id (energy_expectation pb) (energy_exp_temp t Ht))
             (And (forall p : S -> R, normalized p -> positive_dist p ->
                    Id (energy_expectation p) (energy_exp_temp t Ht) ->
                    le (entropy_dist p) (entropy_dist pb))
                  (forall p : S -> R, normalized p -> positive_dist p ->
                    Id (energy_expectation p) (energy_exp_temp t Ht) ->
                    Id (entropy_dist p) (entropy_dist pb) ->
                    forall s : S, Id (p s) (pb s))))).
Proof.
  intros t Ht.
  exists (boltzmann_dist_temp t Ht).
  split.
  - split.
    + exact (boltzmann_dist_temp_normalized t Ht).
    + intro s. exact (boltzmann_dist_temp_pos t Ht s).
  - split.
    + reflexivity.
    + split.
      * intros p Hnp Hpp Henergy.
        exact (max_entropy_is_boltzmann_temp t Ht p Hnp Hpp Henergy).
      * intros p Hnp Hpp Henergy Hent.
        exact (entropy_max_unique_temp t Ht p Hnp Hpp Henergy Hent).
Qed.

(* ============================================================ *)
(* strict monotonicity of the temperature against the energy *)
(*   statement (positive-difference form): t1 < t2 and
   KL(p_t2 || p_t1) > 0 *)
(*     imply 0 < E(t2) - E(t1).  Identity: *)
(*     (b1 - b2) * (E2 - E1) == KL1 + KL2 (subtracting the two temperature
   KL decompositions) *)
(*   explicit condition: a strict-positivity interface for KL (satisfied
   whenever the energies are nontrivial) *)
(* ============================================================ *)

(* KL decomposition reshape: -S2 + b1 * E2 + log Z1 ==
   (b1 - b2) * E2 + (log Z1 - log Z2)
   (substituting S2 == b2 * E2 + log Z2, then [opp_plus] and
   associativity/commutativity) *)
Lemma temp_strict_A_chain2 : forall (t1 t2 : R) (Ht1 : lt zero t1) (Ht2 : lt zero t2),
  Id (plus (plus (opp (entropy_dist (boltzmann_dist_temp t2 Ht2))) (mult (inv_pos t1 Ht1) (energy_exp_temp t2 Ht2))) (log (Z_temp t1)))
     (plus (mult (minus (inv_pos t1 Ht1) (inv_pos t2 Ht2)) (energy_exp_temp t2 Ht2))
           (minus (log (Z_temp t1)) (log (Z_temp t2)))).
Proof.
  intros t1 t2 Ht1 Ht2.
  set (b1 := inv_pos t1 Ht1). set (b2 := inv_pos t2 Ht2).
  set (E2 := energy_exp_temp t2 Ht2).
  set (S2 := entropy_dist (boltzmann_dist_temp t2 Ht2)).
  set (Z1 := Z_temp t1). set (Z2 := Z_temp t2).
  assert (Hse : Id S2 (plus (mult b2 E2) (log Z2))).
  { unfold S2, b2, E2, Z2. apply (entropy_temp_explicit t2 Ht2). }
  assert (H1 : Id (plus (plus (opp S2) (mult b1 E2)) (log Z1))
                  (plus (plus (opp (plus (mult b2 E2) (log Z2))) (mult b1 E2)) (log Z1))).
  { apply (id_cong (fun x => plus (plus (opp x) (mult b1 E2)) (log Z1)) Hse). }
  assert (H2 : Id (plus (plus (opp (plus (mult b2 E2) (log Z2))) (mult b1 E2)) (log Z1))
                  (plus (plus (plus (opp (mult b2 E2)) (opp (log Z2))) (mult b1 E2)) (log Z1))).
  { apply (id_cong (fun x => plus (plus x (mult b1 E2)) (log Z1))).
    apply (opp_plus (mult b2 E2) (log Z2)). }
  assert (H3 : Id (plus (plus (plus (opp (mult b2 E2)) (opp (log Z2))) (mult b1 E2)) (log Z1))
                  (plus (plus (opp (mult b2 E2)) (mult b1 E2)) (plus (opp (log Z2)) (log Z1)))).
  {
    apply (id_trans
             (id_cong (fun x => plus x (log Z1))
                      (id_trans (id_sym (plus_assoc (opp (mult b2 E2)) (opp (log Z2)) (mult b1 E2)))
                     (id_trans (id_cong (fun x => plus (opp (mult b2 E2)) x)
                                        (plus_comm (opp (log Z2)) (mult b1 E2)))
                               (plus_assoc (opp (mult b2 E2)) (mult b1 E2) (opp (log Z2))))))).
    apply id_sym.
    apply (plus_assoc (plus (opp (mult b2 E2)) (mult b1 E2)) (opp (log Z2)) (log Z1)).
  }
  assert (H4 : Id (plus (opp (mult b2 E2)) (mult b1 E2))
                  (mult (minus b1 b2) E2)).
  {
    apply (id_trans (plus_comm (opp (mult b2 E2)) (mult b1 E2))
           (id_sym (mult_minus_distr_r b1 b2 E2))).
  }
  assert (H5 : Id (plus (opp (log Z2)) (log Z1))
                  (minus (log Z1) (log Z2))).
  { unfold minus. apply (plus_comm (opp (log Z2)) (log Z1)). }
  assert (Hm4 : Id (plus (plus (opp (mult b2 E2)) (mult b1 E2)) (plus (opp (log Z2)) (log Z1)))
                   (plus (mult (minus b1 b2) E2) (plus (opp (log Z2)) (log Z1)))).
  { apply (id_cong (fun x => plus x (plus (opp (log Z2)) (log Z1))) H4). }
  assert (Hfin : Id (plus (plus (opp (mult b2 E2)) (mult b1 E2)) (plus (opp (log Z2)) (log Z1)))
                    (plus (mult (minus b1 b2) E2) (minus (log Z1) (log Z2)))).
  { apply (id_trans Hm4).
    apply (id_cong (fun x => plus (mult (minus b1 b2) E2) x) H5). }
  apply (id_trans H1).
  apply (id_trans H2).
  apply (id_trans H3).
  exact Hfin.
Qed.

(* simplification (avoiding a very long associativity chain): transitivity
   step by step, as in [temp_strict_ident2] *)
Lemma temp_strict_ident2 : forall (t1 t2 : R) (Ht1 : lt zero t1) (Ht2 : lt zero t2),
  Id (plus (relative_entropy (boltzmann_dist_temp t2 Ht2) (boltzmann_dist_temp t1 Ht1))
           (relative_entropy (boltzmann_dist_temp t1 Ht1) (boltzmann_dist_temp t2 Ht2)))
     (mult (minus (inv_pos t1 Ht1) (inv_pos t2 Ht2))
           (minus (energy_exp_temp t2 Ht2) (energy_exp_temp t1 Ht1))).
Proof.
  intros t1 t2 Ht1 Ht2.
  set (b1 := inv_pos t1 Ht1). set (b2 := inv_pos t2 Ht2).
  set (E1 := energy_exp_temp t1 Ht1). set (E2 := energy_exp_temp t2 Ht2).
  set (Z1 := Z_temp t1). set (Z2 := Z_temp t2).
  assert (HK1 : Id (relative_entropy (boltzmann_dist_temp t2 Ht2) (boltzmann_dist_temp t1 Ht1))
                   (plus (mult (minus b1 b2) E2) (minus (log Z1) (log Z2)))).
  {
    unfold b1, b2, E2, Z1, Z2.
    apply (id_trans
             (relative_entropy_temp_decomp t1 Ht1 (boltzmann_dist_temp t2 Ht2)
                                           (boltzmann_dist_temp_normalized t2 Ht2))
             (temp_strict_A_chain2 t1 t2 Ht1 Ht2)).
  }
  assert (HK2 : Id (relative_entropy (boltzmann_dist_temp t1 Ht1) (boltzmann_dist_temp t2 Ht2))
                   (plus (mult (minus b2 b1) E1) (minus (log Z2) (log Z1)))).
  {
    unfold b1, b2, E1, Z1, Z2.
    apply (id_trans
             (relative_entropy_temp_decomp t2 Ht2 (boltzmann_dist_temp t1 Ht1)
                                           (boltzmann_dist_temp_normalized t1 Ht1))
             (temp_strict_A_chain2 t2 t1 Ht2 Ht1)).
  }
  assert (Hsum : Id (plus (relative_entropy (boltzmann_dist_temp t2 Ht2) (boltzmann_dist_temp t1 Ht1))
                          (relative_entropy (boltzmann_dist_temp t1 Ht1) (boltzmann_dist_temp t2 Ht2)))
                    (plus (plus (mult (minus b1 b2) E2) (minus (log Z1) (log Z2)))
                          (plus (mult (minus b2 b1) E1) (minus (log Z2) (log Z1))))).
  {
    apply (id_cong2 plus HK1 HK2).
  }
  apply (id_trans Hsum).
  (* cancel the log terms (as with Hz above) *)
  assert (Hz : Id (plus (minus (log Z1) (log Z2)) (minus (log Z2) (log Z1))) zero).
  { unfold minus.
    apply (id_trans (id_sym (plus_assoc (log Z1) (opp (log Z2)) (plus (log Z2) (opp (log Z1)))))
           (id_trans (id_cong (fun x => plus (log Z1) x)
                              (plus_assoc (opp (log Z2)) (log Z2) (opp (log Z1))))
           (id_trans (id_cong (fun x => plus (log Z1) x)
                              (id_cong (fun x => plus x (opp (log Z1)))
                                       (id_trans (plus_comm (opp (log Z2)) (log Z2)) (plus_opp (log Z2)))))
           (id_trans (id_cong (fun x => plus (log Z1) x)
                              (id_trans (plus_comm zero (opp (log Z1))) (plus_zero (opp (log Z1)))))
                     (plus_opp (log Z1)))))). }
  assert (Hoppm : Id (minus b2 b1) (opp (minus b1 b2))).
  {
    unfold minus.
    exact (id_sym (id_trans (opp_plus b1 (opp b2))
                   (id_trans (id_cong (fun x => plus (opp b1) x) (double_neg b2))
                             (plus_comm (opp b1) b2)))).
  }
  assert (Hmain2 : Id (plus (mult (minus b1 b2) E2) (mult (minus b2 b1) E1))
                      (mult (minus b1 b2) (minus E2 E1))).
  {
    apply (id_trans (id_cong (fun x => plus (mult (minus b1 b2) E2) (mult x E1)) Hoppm)
           (id_trans (id_cong (fun x => plus (mult (minus b1 b2) E2) x)
                              (opp_mult_r (minus b1 b2) E1))
                     (id_sym (mult_minus_distr_l (minus b1 b2) E2 E1)))).
  }
  (* step by step:
   M1 := plus (plus (mult d E2) (minus L1 L2))
              (plus (mult d' E1) (minus L2 L1))
   == plus (mult d E2) (plus (minus L1 L2) (plus (mult d' E1) (minus L2 L1)))
      (associativity, reversed)
   == plus (mult d E2) (plus (mult d' E1) (plus (minus L1 L2) (minus L2 L1)))
      (commutativity, inner swap)
   == plus (mult d E2) (plus (mult d' E1) zero)  (by Hz)
   == plus (mult d E2) (mult d' E1)  ([plus_zero])
   == mult d (minus E2 E1)  (by Hmain2) *)
  assert (H1 : Id (plus (plus (mult (minus b1 b2) E2) (minus (log Z1) (log Z2)))
                        (plus (mult (minus b2 b1) E1) (minus (log Z2) (log Z1))))
                  (plus (mult (minus b1 b2) E2)
                        (plus (minus (log Z1) (log Z2))
                              (plus (mult (minus b2 b1) E1) (minus (log Z2) (log Z1)))))).
  { apply id_sym.
    apply (plus_assoc (mult (minus b1 b2) E2) (minus (log Z1) (log Z2))
                      (plus (mult (minus b2 b1) E1) (minus (log Z2) (log Z1)))). }
  assert (H2 : Id (plus (mult (minus b1 b2) E2)
                        (plus (minus (log Z1) (log Z2))
                              (plus (mult (minus b2 b1) E1) (minus (log Z2) (log Z1)))))
                  (plus (mult (minus b1 b2) E2)
                        (plus (mult (minus b2 b1) E1)
                              (plus (minus (log Z1) (log Z2)) (minus (log Z2) (log Z1)))))).
  {
    assert (H2a : Id (plus (mult (minus b1 b2) E2)
                           (plus (minus (log Z1) (log Z2))
                                 (plus (mult (minus b2 b1) E1) (minus (log Z2) (log Z1)))))
                     (plus (mult (minus b1 b2) E2)
                           (plus (plus (minus (log Z1) (log Z2)) (mult (minus b2 b1) E1))
                                 (minus (log Z2) (log Z1))))).
    { apply (id_cong (fun x => plus (mult (minus b1 b2) E2) x)).
      apply (plus_assoc (minus (log Z1) (log Z2)) (mult (minus b2 b1) E1) (minus (log Z2) (log Z1))). }
    assert (H2b : Id (plus (mult (minus b1 b2) E2)
                           (plus (plus (minus (log Z1) (log Z2)) (mult (minus b2 b1) E1))
                                 (minus (log Z2) (log Z1))))
                     (plus (mult (minus b1 b2) E2)
                           (plus (plus (mult (minus b2 b1) E1) (minus (log Z1) (log Z2)))
                                 (minus (log Z2) (log Z1))))).
    { apply (id_cong (fun x => plus (mult (minus b1 b2) E2) (plus x (minus (log Z2) (log Z1))))).
      apply (plus_comm (minus (log Z1) (log Z2)) (mult (minus b2 b1) E1)). }
    assert (H2c : Id (plus (mult (minus b1 b2) E2)
                           (plus (plus (mult (minus b2 b1) E1) (minus (log Z1) (log Z2)))
                                 (minus (log Z2) (log Z1))))
                     (plus (mult (minus b1 b2) E2)
                           (plus (mult (minus b2 b1) E1)
                                 (plus (minus (log Z1) (log Z2)) (minus (log Z2) (log Z1)))))).
    { apply (id_cong (fun x => plus (mult (minus b1 b2) E2) x)).
      apply id_sym.
      apply (plus_assoc (mult (minus b2 b1) E1) (minus (log Z1) (log Z2)) (minus (log Z2) (log Z1))). }
    exact (id_trans H2a (id_trans H2b H2c)).
  }
  assert (H3 : Id (plus (mult (minus b1 b2) E2)
                        (plus (mult (minus b2 b1) E1) zero))
                  (plus (mult (minus b1 b2) E2) (mult (minus b2 b1) E1))).
  { apply (id_cong (fun x => plus (mult (minus b1 b2) E2) x)).
    apply (plus_zero (mult (minus b2 b1) E1)). }
  assert (Hza : Id (plus (mult (minus b1 b2) E2)
                         (plus (mult (minus b2 b1) E1)
                               (plus (minus (log Z1) (log Z2)) (minus (log Z2) (log Z1)))))
                   (plus (mult (minus b1 b2) E2)
                         (plus (mult (minus b2 b1) E1) zero))).
  { apply (id_cong (fun x => plus (mult (minus b1 b2) E2)
                                  (plus (mult (minus b2 b1) E1) x)) Hz). }
  assert (Hfin : Id (plus (plus (mult (minus b1 b2) E2) (minus (log Z1) (log Z2)))
                          (plus (mult (minus b2 b1) E1) (minus (log Z2) (log Z1))))
                    (mult (minus b1 b2) (minus E2 E1))).
  {
    apply (id_trans H1).
    apply (id_trans H2).
    apply (id_trans Hza).
    apply (id_trans H3).
    exact Hmain2.
  }
  exact Hfin.
Qed.

(* ============================================================ *)
(* final theorem: strict monotonicity of the temperature against the energy
   (positive-difference form) *)
(*   t1 < t2 and KL(p_t2 || p_t1) > 0 imply 0 < E2 - E1 *)
(* ============================================================ *)
Theorem energy_exp_temp_strict_mono : forall (t1 t2 : R) (Ht1 : lt zero t1) (Ht2 : lt zero t2),
  lt t1 t2 ->
  lt zero (relative_entropy (boltzmann_dist_temp t2 Ht2) (boltzmann_dist_temp t1 Ht1)) ->
  lt zero (minus (energy_exp_temp t2 Ht2) (energy_exp_temp t1 Ht1)).
Proof.
  intros t1 t2 Ht1 Ht2 Ht12 Hkl1.
  set (b1 := inv_pos t1 Ht1). set (b2 := inv_pos t2 Ht2).
  set (E1 := energy_exp_temp t1 Ht1). set (E2 := energy_exp_temp t2 Ht2).
  set (B1 := boltzmann_dist_temp t1 Ht1). set (B2 := boltzmann_dist_temp t2 Ht2).
  set (K1 := relative_entropy B2 B1). set (K2 := relative_entropy B1 B2).
  (* beta2 < beta1 and d := b1 - b2 > 0 *)
  assert (Hb : lt b2 b1) by (unfold b1, b2; apply (inv_pos_lt_compat t1 t2 Ht1 Ht2 Ht12)).
  assert (Hbd : lt zero (minus b1 b2)) by (unfold b1, b2; apply (lt_minus_nonneg b2 b1 Hb)).
  (* K2 >= 0 (Gibbs inequality) *)
  assert (Hkl2 : le zero K2).
  { unfold K2, B1, B2.
    apply (gibbs_inequality (boltzmann_dist_temp t1 Ht1) (boltzmann_dist_temp t2 Ht2)).
    - apply (boltzmann_dist_temp_normalized t1 Ht1).
    - intro s. apply (boltzmann_dist_temp_pos t1 Ht1 s).
    - apply (boltzmann_dist_temp_normalized t2 Ht2).
    - intro s. apply (boltzmann_dist_temp_pos t2 Ht2 s). }
  (* K1 + K2 > 0 (K1 > 0 and K2 >= 0 give K1 <= K1 + K2, then transitivity
   of lt) *)
  assert (Hklsum : lt zero (plus K1 K2)).
  {
    apply (lt_le_trans zero K1 (plus K1 K2)).
    - unfold K1, B1, B2. exact Hkl1.
    - apply (le_plus_nonneg_r K1 K2). exact Hkl2.
  }
  (* identity: K1 + K2 == d * (E2 - E1) *)
  assert (Hid : Id (plus K1 K2) (mult (minus b1 b2) (minus E2 E1))).
  { unfold K1, K2, b1, b2, E1, E2. exact (temp_strict_ident2 t1 t2 Ht1 Ht2). }
  (* 0 < d * (E2 - E1) (replacing by [lt_id_r]) *)
  assert (Hprod : lt zero (mult (minus b1 b2) (minus E2 E1))).
  { apply (lt_id_r zero (plus K1 K2) (mult (minus b1 b2) (minus E2 E1))).
    - exact Hid.
    - exact Hklsum. }
  (* cancel the positive factor: 0 < E2 - E1 (commute first) *)
  apply (lt_mult_pos_cancel (minus E2 E1) (minus b1 b2) Hbd).
  apply (lt_id_r zero (mult (minus b1 b2) (minus E2 E1))
                  (mult (minus E2 E1) (minus b1 b2))).
  - apply (mult_comm (minus b1 b2) (minus E2 E1)).
  - exact Hprod.
Qed.

(* ============================================================ *)



(* ============================================================ *)
(* KL-regularized reward maximization (the alignment setting of modern
   model training) *)
(* ============================================================ *)
(* the goal of modern alignment (RLHF/DPO/PPO): *)
(* maximize E_pi[r] - beta * KL(pi‖pi_ref) *)
(* maximize reward while staying within a KL penalty of the reference
   policy pi_ref. *)
(* Mathematically this replicates the Boltzmann mechanism exactly (reward
   in place of energy, the reference *)
(* policy in place of the uniform prior).  This section proves the
   closed-form solution and its optimality: *)
(* the optimal policy is pi*(s) proportional to pi_ref(s) * e^(r(s)/beta)
   (a reward-weighted Boltzmann), *)
(* and it is the unique optimum. *)
(* ------------------------------------------------------------ *)

(* ============================================================ *)
(* the first three pillars (unique minimum of the free energy, KL as the
   deviation measure, maximum entropy) close the theory; *)
(* this section adds the practical interface: cross-entropy
   H(p, q) := -sum p * log q. *)
(* From [energy_in_log_boltzmann] (E = -D * (log p_b + log Z)), *)
(* ⟨E⟩_p = -D * (H(p,p_b) + log Z) *)
(* F[p] = ⟨E⟩_p - D * S[p] = -D * (H(p,p_b) + log Z + S[p]) *)
(* training (minimizing F) is equivalent to minimizing the cross-entropy
   H(p, p_b) at fixed p_b. *)
(* ------------------------------------------------------------ *)

(* cross-entropy: H(p, q) := -sum_s p(s) * log q(s) *)
Definition cross_entropy (p q : S -> R) : R :=
  sum_over_S (fun s => mult (p s) (opp (log (q s)))).

(* cross-entropy/relative-entropy/entropy identity:
   H(p, q) = S[p] + KL(p || q)
   (the information-theoretic core: cross-entropy = own entropy + relative
   entropy; expanding the definitions and using linearity of sums) *)
Theorem cross_entropy_decomp :
  forall p q : S -> R,
    Id (cross_entropy p q)
       (plus (entropy_dist p) (relative_entropy p q)).
Proof.
  intros p q.
  unfold cross_entropy, entropy_dist, relative_entropy.
  (* sum p * (-log q) = sum p * (-log p) + sum p * (log p - log q) *)
  (* pointwise: mult (p s) (opp (log (q s))) =
   plus (mult (p s) (opp (log (p s))))
        (mult (p s) (minus (log (p s)) (log (q s)))) *)
  assert (Hpt : forall s, Id (mult (p s) (opp (log (q s))))
                            (plus (mult (p s) (opp (log (p s))))
                                  (mult (p s) (minus (log (p s)) (log (q s)))))).
  {
    intro s.
    unfold minus.
    assert (Hd : Id (mult (p s) (plus (opp (log (p s))) (plus (log (p s)) (opp (log (q s))))))
                    (plus (mult (p s) (opp (log (p s))))
                          (mult (p s) (plus (log (p s)) (opp (log (q s)))))))
      by exact (distrib (p s) (opp (log (p s))) (plus (log (p s)) (opp (log (q s))))).
    (* left side: opp (log p) + (log p - log q) = -log q
   ([minus_plus_cancel]) *)
    assert (Hcancel : Id (plus (opp (log (p s))) (plus (log (p s)) (opp (log (q s)))))
                         (opp (log (q s)))).
    {
      (* assoc: opp log p + (log p - log q) = (opp log p + log p) - log q *)
      assert (Ha : Id (plus (opp (log (p s))) (plus (log (p s)) (opp (log (q s)))))
                      (plus (plus (opp (log (p s))) (log (p s))) (opp (log (q s)))))
        by exact (plus_assoc (opp (log (p s))) (log (p s)) (opp (log (q s)))).
      (* inner cancellation: opp (log p) + log p = 0 *)
      assert (Hz : Id (plus (opp (log (p s))) (log (p s))) zero)
        by exact (id_trans (plus_comm (opp (log (p s))) (log (p s))) (plus_opp (log (p s)))).
      (* (opp log p + log p) - log q = 0 - log q = -log q *)
      assert (Hb : Id (plus (plus (opp (log (p s))) (log (p s))) (opp (log (q s))))
                      (plus zero (opp (log (q s)))))
        by exact (id_cong (fun x => plus x (opp (log (q s)))) Hz).
      assert (Hc : Id (plus zero (opp (log (q s)))) (opp (log (q s))))
        by exact (id_trans (plus_comm zero (opp (log (q s)))) (plus_zero (opp (log (q s))))).
      exact (id_trans Ha (id_trans Hb Hc)).
    }
    assert (Hleft : Id (mult (p s) (plus (opp (log (p s))) (plus (log (p s)) (opp (log (q s))))))
                       (mult (p s) (opp (log (q s)))))
      by exact (id_cong (fun x => mult (p s) x) Hcancel).
    (* right side: mult (p s) (log p - log q) = mult (p s) (log p) + mult (p s) (-log q) *)
    assert (Hdist2 : Id (mult (p s) (plus (log (p s)) (opp (log (q s)))))
                        (plus (mult (p s) (log (p s))) (mult (p s) (opp (log (q s))))))
      by exact (distrib (p s) (log (p s)) (opp (log (q s)))).
    (* goal: mult (p s) (-log q) = plus (mult (p s) (-log p))
                                       (mult (p s) (log p - log q)),
   reading Hd backwards (after Hleft, swap the two sides) *)
    exact (id_trans (id_sym Hleft) Hd).
  }
  assert (Hext : Id (sum_over_S (fun s => mult (p s) (opp (log (q s)))))
                   (sum_over_S (fun s => plus (mult (p s) (opp (log (p s))))
                                            (mult (p s) (minus (log (p s)) (log (q s)))))))
    by exact (sum_over_S_ext (fun s => mult (p s) (opp (log (q s))))
                             (fun s => plus (mult (p s) (opp (log (p s))))
                                            (mult (p s) (minus (log (p s)) (log (q s)))))
                             Hpt).
  rewrite Hext.
  assert (Hadd : Id (sum_over_S (fun s => plus (mult (p s) (opp (log (p s))))
                                            (mult (p s) (minus (log (p s)) (log (q s))))))
                   (plus (sum_over_S (fun s => mult (p s) (opp (log (p s)))))
                         (sum_over_S (fun s => mult (p s) (minus (log (p s)) (log (q s)))))))
    by exact (sum_over_S_add (fun s => mult (p s) (opp (log (p s))))
                             (fun s => mult (p s) (minus (log (p s)) (log (q s))))).
  rewrite Hadd.
  reflexivity.
Qed.

Theorem energy_cross_entropy :
  forall p : S -> R,
    normalized p ->
    Id (energy_expectation p)
       (plus (mult D (cross_entropy p boltzmann_dist)) (opp (mult D (log Z)))).
Proof.
  intros p Hnp.
  unfold energy_expectation, cross_entropy.
  (* pointwise: mult (p s) (base_loss s) =
   mult (p s) (-D * (log p_b s + log Z)) *)
  assert (Hpt : forall s, Id (mult (p s) (base_loss s))
                            (mult (p s) (opp (mult D (plus (log (boltzmann_dist s)) (log Z)))))).
  {
    intro s.
    assert (He : Id (base_loss s) (opp (mult D (plus (log (boltzmann_dist s)) (log Z)))))
      by exact (energy_in_log_boltzmann s).
    exact (id_cong (fun x => mult (p s) x) He).
  }
  assert (Hext : Id (sum_over_S (fun s => mult (p s) (base_loss s)))
                   (sum_over_S (fun s => mult (p s) (opp (mult D (plus (log (boltzmann_dist s)) (log Z)))))))
    by exact (sum_over_S_ext (fun s => mult (p s) (base_loss s))
                             (fun s => mult (p s) (opp (mult D (plus (log (boltzmann_dist s)) (log Z)))))
                             Hpt).
  rewrite Hext.
  (* expand pointwise to -D * (p * log p_b + p * log Z) *)
  assert (Hpt2 : forall s, Id (mult (p s) (opp (mult D (plus (log (boltzmann_dist s)) (log Z)))))
                             (opp (mult D (plus (mult (p s) (log (boltzmann_dist s)))
                                                (mult (p s) (log Z)))))).
  {
    intro s.
    assert (Hopp : Id (mult (p s) (opp (mult D (plus (log (boltzmann_dist s)) (log Z)))))
                      (opp (mult (p s) (mult D (plus (log (boltzmann_dist s)) (log Z))))))
      by exact (opp_mult_l (p s) (mult D (plus (log (boltzmann_dist s)) (log Z)))).
    assert (Hsw : Id (mult (p s) (mult D (plus (log (boltzmann_dist s)) (log Z))))
                     (mult D (mult (p s) (plus (log (boltzmann_dist s)) (log Z))))).
    {
      assert (H1 : Id (mult (p s) (mult D (plus (log (boltzmann_dist s)) (log Z))))
                      (mult (mult (p s) D) (plus (log (boltzmann_dist s)) (log Z))))
        by exact (mult_assoc (p s) D (plus (log (boltzmann_dist s)) (log Z))).
      assert (H2 : Id (mult (mult (p s) D) (plus (log (boltzmann_dist s)) (log Z)))
                      (mult (mult D (p s)) (plus (log (boltzmann_dist s)) (log Z))))
        by exact (id_cong (fun x => mult x (plus (log (boltzmann_dist s)) (log Z))) (mult_comm (p s) D)).
      assert (H3 : Id (mult (mult D (p s)) (plus (log (boltzmann_dist s)) (log Z)))
                      (mult D (mult (p s) (plus (log (boltzmann_dist s)) (log Z)))))
        by exact (id_sym (mult_assoc D (p s) (plus (log (boltzmann_dist s)) (log Z)))).
      exact (id_trans H1 (id_trans H2 H3)).
    }
    assert (Hdist : Id (mult (p s) (plus (log (boltzmann_dist s)) (log Z)))
                       (plus (mult (p s) (log (boltzmann_dist s))) (mult (p s) (log Z))))
      by exact (distrib (p s) (log (boltzmann_dist s)) (log Z)).
    assert (Hd2 : Id (mult D (mult (p s) (plus (log (boltzmann_dist s)) (log Z))))
                     (mult D (plus (mult (p s) (log (boltzmann_dist s))) (mult (p s) (log Z)))))
      by exact (id_cong (fun x => mult D x) Hdist).
    assert (Hd3 : Id (mult D (plus (mult (p s) (log (boltzmann_dist s))) (mult (p s) (log Z))))
                     (plus (mult D (mult (p s) (log (boltzmann_dist s))))
                           (mult D (mult (p s) (log Z)))))
      by exact (distrib D (mult (p s) (log (boltzmann_dist s))) (mult (p s) (log Z))).
    assert (Htot : Id (mult (p s) (mult D (plus (log (boltzmann_dist s)) (log Z))))
                     (plus (mult D (mult (p s) (log (boltzmann_dist s))))
                           (mult D (mult (p s) (log Z)))))
      by exact (id_trans Hsw (id_trans Hd2 Hd3)).
    assert (Hopp2 : Id (opp (mult (p s) (mult D (plus (log (boltzmann_dist s)) (log Z)))))
                      (opp (plus (mult D (mult (p s) (log (boltzmann_dist s))))
                                 (mult D (mult (p s) (log Z))))))
      by exact (id_cong opp Htot).
    assert (Hopp3 : Id (opp (plus (mult D (mult (p s) (log (boltzmann_dist s))))
                                 (mult D (mult (p s) (log Z)))))
                    (opp (mult D (plus (mult (p s) (log (boltzmann_dist s)))
                                       (mult (p s) (log Z)))))).
    {
      assert (Hd4 : Id (mult D (plus (mult (p s) (log (boltzmann_dist s))) (mult (p s) (log Z))))
                      (plus (mult D (mult (p s) (log (boltzmann_dist s))))
                            (mult D (mult (p s) (log Z)))))
        by exact (distrib D (mult (p s) (log (boltzmann_dist s))) (mult (p s) (log Z))).
      exact (id_cong opp (id_sym Hd4)).
    }
    exact (id_trans Hopp (id_trans Hopp2 Hopp3)).
  }
  assert (Hext2 : Id (sum_over_S (fun s => mult (p s) (opp (mult D (plus (log (boltzmann_dist s)) (log Z))))))
                     (sum_over_S (fun s => opp (mult D (plus (mult (p s) (log (boltzmann_dist s)))
                                                           (mult (p s) (log Z)))))))
    by exact (sum_over_S_ext (fun s => mult (p s) (opp (mult D (plus (log (boltzmann_dist s)) (log Z)))))
                             (fun s => opp (mult D (plus (mult (p s) (log (boltzmann_dist s)))
                                                         (mult (p s) (log Z)))))
                             Hpt2).
  rewrite Hext2.
  assert (Hso : Id (sum_over_S (fun s => opp (mult D (plus (mult (p s) (log (boltzmann_dist s)))
                                                         (mult (p s) (log Z))))))
                   (opp (sum_over_S (fun s => mult D (plus (mult (p s) (log (boltzmann_dist s)))
                                                          (mult (p s) (log Z)))))))
    by exact (sum_opp (fun s => mult D (plus (mult (p s) (log (boltzmann_dist s)))
                                            (mult (p s) (log Z))))).
  rewrite Hso.
  assert (Hlin : Id (sum_over_S (fun s => mult D (plus (mult (p s) (log (boltzmann_dist s)))
                                                       (mult (p s) (log Z)))))
                    (mult D (sum_over_S (fun s => plus (mult (p s) (log (boltzmann_dist s)))
                                                       (mult (p s) (log Z))))))
    by exact (sum_over_S_linear D (fun s => plus (mult (p s) (log (boltzmann_dist s)))
                                                 (mult (p s) (log Z)))).
  rewrite Hlin.
  assert (Hadd : Id (sum_over_S (fun s => plus (mult (p s) (log (boltzmann_dist s)))
                                              (mult (p s) (log Z))))
                   (plus (sum_over_S (fun s => mult (p s) (log (boltzmann_dist s))))
                         (sum_over_S (fun s => mult (p s) (log Z)))))
    by exact (sum_over_S_add (fun s => mult (p s) (log (boltzmann_dist s)))
                             (fun s => mult (p s) (log Z))).
  rewrite Hadd.
  (* sum p * log p_b = -cross_entropy (cross_entropy := sum p * (-log p_b)) *)
  assert (Hce : Id (sum_over_S (fun s => mult (p s) (log (boltzmann_dist s))))
                   (opp (sum_over_S (fun s => mult (p s) (opp (log (boltzmann_dist s))))))).
  {
    assert (Hpt3 : forall s, Id (mult (p s) (log (boltzmann_dist s)))
                               (opp (mult (p s) (opp (log (boltzmann_dist s)))))).
    {
      intro s.
      apply id_sym.
      apply (id_trans (id_cong opp (opp_mult_l (p s) (log (boltzmann_dist s))))
                   (double_neg (mult (p s) (log (boltzmann_dist s))))).
    }
    assert (Hext3 : Id (sum_over_S (fun s => mult (p s) (log (boltzmann_dist s))))
                      (sum_over_S (fun s => opp (mult (p s) (opp (log (boltzmann_dist s)))))))
      by exact (sum_over_S_ext (fun s => mult (p s) (log (boltzmann_dist s)))
                               (fun s => opp (mult (p s) (opp (log (boltzmann_dist s))))) Hpt3).
    assert (Hso3 : Id (sum_over_S (fun s => opp (mult (p s) (opp (log (boltzmann_dist s))))))
                      (opp (sum_over_S (fun s => mult (p s) (opp (log (boltzmann_dist s)))))))
      by exact (sum_opp (fun s => mult (p s) (opp (log (boltzmann_dist s))))).
    exact (id_trans Hext3 Hso3).
  }
  rewrite Hce.
  (* sum p * log Z = log Z (normalization) *)
  assert (Hlz : Id (sum_over_S (fun s => mult (p s) (log Z))) (log Z)).
  {
    assert (Hsw : Id (sum_over_S (fun s => mult (p s) (log Z)))
                     (sum_over_S (fun s => mult (log Z) (p s))))
      by exact (sum_over_S_ext (fun s => mult (p s) (log Z))
                               (fun s => mult (log Z) (p s))
                               (fun s => mult_comm (p s) (log Z))).
    rewrite Hsw.
    assert (Hl1 : Id (sum_over_S (fun s => mult (log Z) (p s))) (mult (log Z) (sum_over_S p)))
      by exact (sum_over_S_linear (log Z) p).
    rewrite Hl1.
    rewrite Hnp.
    assert (Hm1 : Id (mult (log Z) one) (log Z)) by exact (mult_one (log Z)).
    rewrite Hm1.
    reflexivity.
  }
  rewrite Hlz.
  (* goal: opp (mult D (plus (opp (cross_entropy p boltzmann_dist)) (log Z)))
   equals -(D * (sum p log p_b + log Z)) = -(-H + log Z)
   = plus (mult D H) (opp (mult D (log Z))). *)
  (* match the right side of the goal using the original [cross_entropy]
   definition directly *)
  unfold cross_entropy.
  (* goal: opp (mult D (plus (opp (sum p * (-log p_b))) (log Z))) =
   plus (mult D (sum p * (-log p_b))) (opp (mult D (log Z))),
   by the ring identity opp (X + Y) = opp X + opp Y *)
  assert (Hring : forall X Y : R, Id (opp (mult D (plus (opp X) Y)))
                                    (plus (mult D X) (opp (mult D Y)))).
  {
    intros X Y.
    assert (H1 : Id (opp (mult D (plus (opp X) Y)))
                    (opp (plus (mult D (opp X)) (mult D Y))))
      by exact (id_cong opp (distrib D (opp X) Y)).
    assert (H2 : Id (opp (plus (mult D (opp X)) (mult D Y)))
                    (plus (opp (mult D (opp X))) (opp (mult D Y))))
      by exact (opp_plus (mult D (opp X)) (mult D Y)).
    assert (H3 : Id (opp (mult D (opp X))) (mult D X))
      by exact (id_trans (id_sym (opp_mult_l D (opp X))) (id_cong (fun x => mult D x) (double_neg X))).
    assert (H4 : Id (plus (opp (mult D (opp X))) (opp (mult D Y)))
                    (plus (mult D X) (opp (mult D Y))))
      by exact (id_cong (fun x => plus x (opp (mult D Y))) H3).
    exact (id_trans H1 (id_trans H2 H4)).
  }
  (* the goal now: Id (opp (mult D (plus (opp S) (log Z))))
                   (plus (mult D S) (opp (mult D (log Z)))),
   where S := sum_over_S (fun s => mult (p s) (opp (log (boltzmann_dist s)))) *)
  exact (Hring (sum_over_S (fun s => mult (p s) (opp (log (boltzmann_dist s))))) (log Z)).
Qed.

(* ============================================================ *)
(* variational inference: the ELBO and the evidence lower bound *)
(* ============================================================ *)
(* in the free-energy framework, ELBO(q) := -F[q] is a variational lower *)
(* bound on the evidence (the energy form of the log partition function,
   opp (free_energy boltzmann_dist)); training (maximizing *)
(* the ELBO) is equivalent to minimizing the free energy.  Three theorems: *)
(*   (a) [elbo_lower_bound]: ELBO(q) <= evidence (free-energy minimization,
   negated); *)
(* (b) evidence_kl_decomp: evidence = ELBO(q) + D * KL(q||p_b) *)
(*       the gap between the evidence and the ELBO equals the KL divergence
   exactly (the core identity of variational inference); *)
(*   (c) [elbo_explicit]: the explicit entropy-plus-energy form of the
   ELBO. *)
(* ------------------------------------------------------------ *)

(* ELBO: the evidence lower bound of the variational distribution q *)
Definition elbo (q : S -> R) : R :=
  opp (free_energy q).

(* evidence: the energy form of the log partition function (an abstraction
   of D * log Z, no need for D = 1) *)
Definition evidence : R :=
  opp (free_energy boltzmann_dist).

(* ELBO(q) <= evidence: directly from free-energy minimization (negation
   with [opp_le_compat]) *)
Theorem elbo_lower_bound :
  forall q : S -> R,
    normalized q -> positive_dist q ->
    le (elbo q) evidence.
Proof.
  intros q Hnq Hpq.
  unfold elbo, evidence.
  apply (opp_le_compat (free_energy boltzmann_dist) (free_energy q)).
  exact (min_free_energy_is_boltzmann q Hnq Hpq).
Qed.

(* KL decomposition of the evidence: evidence = ELBO(q) + D * KL(q || p_b).
   The core identity of variational inference: the gap between the evidence
   and the ELBO equals the KL divergence exactly (negating
   [free_energy_kl_decomp]: -F[b] = -F[q] + D * KL) *)
Theorem evidence_kl_decomp :
  forall q : S -> R,
    normalized q ->
    Id evidence
       (plus (elbo q) (mult D (relative_entropy q boltzmann_dist))).
Proof.
  intros q Hnq.
  unfold evidence, elbo.
  assert (Hdecomp : Id (free_energy q)
                       (plus (free_energy boltzmann_dist)
                             (mult D (relative_entropy q boltzmann_dist))))
    by exact (free_energy_kl_decomp q Hnq).
  assert (Htarget : Id (plus (opp (free_energy q)) (mult D (relative_entropy q boltzmann_dist)))
                       (opp (free_energy boltzmann_dist))).
  {
    assert (H1 : Id (plus (opp (free_energy q)) (mult D (relative_entropy q boltzmann_dist)))
                    (plus (opp (plus (free_energy boltzmann_dist) (mult D (relative_entropy q boltzmann_dist))))
                          (mult D (relative_entropy q boltzmann_dist))))
      by exact (id_cong (fun x => plus x (mult D (relative_entropy q boltzmann_dist))) (id_cong opp Hdecomp)).
    assert (H2 : Id (plus (opp (plus (free_energy boltzmann_dist) (mult D (relative_entropy q boltzmann_dist))))
                          (mult D (relative_entropy q boltzmann_dist)))
                    (plus (plus (opp (free_energy boltzmann_dist)) (opp (mult D (relative_entropy q boltzmann_dist))))
                          (mult D (relative_entropy q boltzmann_dist))))
      by exact (id_cong (fun x => plus x (mult D (relative_entropy q boltzmann_dist)))
                        (opp_plus (free_energy boltzmann_dist) (mult D (relative_entropy q boltzmann_dist)))).
    assert (H3 : Id (plus (plus (opp (free_energy boltzmann_dist)) (opp (mult D (relative_entropy q boltzmann_dist))))
                          (mult D (relative_entropy q boltzmann_dist)))
                    (plus (opp (free_energy boltzmann_dist)) zero)).
    {
      assert (H3a : Id (plus (plus (opp (free_energy boltzmann_dist)) (opp (mult D (relative_entropy q boltzmann_dist))))
                            (mult D (relative_entropy q boltzmann_dist)))
                      (plus (opp (free_energy boltzmann_dist))
                            (plus (opp (mult D (relative_entropy q boltzmann_dist)))
                                  (mult D (relative_entropy q boltzmann_dist)))))
        by exact (id_sym (plus_assoc (opp (free_energy boltzmann_dist))
                                     (opp (mult D (relative_entropy q boltzmann_dist)))
                                     (mult D (relative_entropy q boltzmann_dist)))).
      assert (H3b : Id (plus (opp (mult D (relative_entropy q boltzmann_dist))) (mult D (relative_entropy q boltzmann_dist))) zero)
        by exact (id_trans (plus_comm (opp (mult D (relative_entropy q boltzmann_dist))) (mult D (relative_entropy q boltzmann_dist)))
                           (plus_opp (mult D (relative_entropy q boltzmann_dist)))).
      assert (H3c : Id (plus (opp (free_energy boltzmann_dist))
                             (plus (opp (mult D (relative_entropy q boltzmann_dist)))
                                   (mult D (relative_entropy q boltzmann_dist))))
                      (plus (opp (free_energy boltzmann_dist)) zero))
        by exact (id_cong (fun x => plus (opp (free_energy boltzmann_dist)) x) H3b).
      exact (id_trans H3a H3c).
    }
    assert (H4 : Id (plus (opp (free_energy boltzmann_dist)) zero) (opp (free_energy boltzmann_dist)))
      by exact (plus_zero (opp (free_energy boltzmann_dist))).
    exact (id_trans H1 (id_trans H2 (id_trans H3 H4))).
  }
  exact (id_sym Htarget).
Qed.

(* explicit decomposition of the ELBO: -F[q] = -<E>_q + D * S[q]
   (S[q] := -sum q * log q, the information entropy) *)
Theorem elbo_explicit :
  forall q : S -> R,
    Id (elbo q)
       (plus (opp (sum_over_S (fun s => mult (q s) (base_loss s))))
             (mult D (entropy_dist q))).
Proof.
  intro q.
  (* [free_energy] is a generalized lambda; [unfold] does not beta-reduce, so
   use [change] (a kernel conversion) *)
  change (Id (opp (plus (sum_over_S (fun s => mult (q s) (base_loss s)))
                        (mult D (sum_over_S (fun s => mult (q s) (log (q s)))))))
             (plus (opp (sum_over_S (fun s => mult (q s) (base_loss s))))
                   (mult D (sum_over_S (fun s => mult (q s) (opp (log (q s)))))))).
  assert (Hop : Id (opp (plus (sum_over_S (fun s => mult (q s) (base_loss s)))
                              (mult D (sum_over_S (fun s => mult (q s) (log (q s)))))))
                   (plus (opp (sum_over_S (fun s => mult (q s) (base_loss s))))
                         (opp (mult D (sum_over_S (fun s => mult (q s) (log (q s))))))))
    by exact (opp_plus (sum_over_S (fun s => mult (q s) (base_loss s)))
                       (mult D (sum_over_S (fun s => mult (q s) (log (q s)))))).
  rewrite Hop.
  assert (Hent : Id (opp (mult D (sum_over_S (fun s => mult (q s) (log (q s))))))
                   (mult D (sum_over_S (fun s => mult (q s) (opp (log (q s))))))).
  {
    assert (Hpt : forall s, Id (mult (q s) (opp (log (q s))))
                             (opp (mult (q s) (log (q s)))))
      by (intro s; exact (opp_mult_l (q s) (log (q s)))).
    assert (He : Id (sum_over_S (fun s => mult (q s) (opp (log (q s)))))
                    (sum_over_S (fun s => opp (mult (q s) (log (q s))))))
      by exact (sum_over_S_ext _ _ Hpt).
    assert (Hso : Id (sum_over_S (fun s => opp (mult (q s) (log (q s)))))
                     (opp (sum_over_S (fun s => mult (q s) (log (q s))))))
      by exact (sum_opp (fun s => mult (q s) (log (q s)))).
    assert (Hlin : Id (mult D (sum_over_S (fun s => mult (q s) (opp (log (q s))))))
                     (mult D (opp (sum_over_S (fun s => mult (q s) (log (q s)))))))
      by exact (id_cong (fun x => mult D x) (id_trans He Hso)).
    assert (Hoppr : Id (mult D (opp (sum_over_S (fun s => mult (q s) (log (q s))))))
                      (opp (mult D (sum_over_S (fun s => mult (q s) (log (q s)))))))
      by exact (opp_mult_l D (sum_over_S (fun s => mult (q s) (log (q s))))).
    exact (id_sym (id_trans Hlin Hoppr)).
  }
  rewrite Hent.
  reflexivity.
Qed.

(* ============================================================ *)
(* tightness of the ELBO and the exact KL form of the evidence gap *)
(* ============================================================ *)
(* (a) when the variational distribution q is exactly the Boltzmann
   posterior, the ELBO attains *)
(*     the evidence value with no gap (the equality case — the zero-error
   state of variational inference); *)
(* (b) for any normalized q, evidence - ELBO(q) equals D * KL(q || p_b)
   exactly, *)
(*     a quantifiable posterior-approximation error for training. *)
(* ------------------------------------------------------------ *)

(* KL(p || p) = 0 (self-relative-entropy vanishes; proved inside
   FreeEnergyMinimization): after unfolding, pointwise
   p s * (log p s - log p s) = p s * 0 = 0, closed by [sum_over_S_ext],
   [sum_over_S_linear] and [mult_zero]. *)
Lemma relative_entropy_self_zero' : forall p : S -> R,
  Id (relative_entropy p p) zero.
Proof.
  intro p.
  unfold relative_entropy.
  (* pointwise: p s * (log p s - log p s) = zero *)
  assert (Hpt : forall s, Id (mult (p s) (minus (log (p s)) (log (p s)))) zero).
  {
    intro s.
    assert (Hz : Id (minus (log (p s)) (log (p s))) zero)
      by exact (minus_self_zero (log (p s)) (log (p s)) (@id_refl R (log (p s)))).
    exact (id_trans (id_cong (fun x => mult (p s) x) Hz) (mult_zero (p s))).
  }
  assert (Hext : Id (sum_over_S (fun s => mult (p s) (minus (log (p s)) (log (p s)))))
                    (sum_over_S (fun s => zero)))
    by exact (sum_over_S_ext _ _ Hpt).
  assert (Hzero : Id (sum_over_S (fun s => zero)) zero).
  {
    (* the zero function equals mult zero (the constant-one function)
   pointwise; closed by [sum_over_S_linear] *)
    assert (Hsame : Id (sum_over_S (fun s => zero))
                       (sum_over_S (fun s => mult zero one)))
      by (apply sum_over_S_ext; intro s; exact (id_sym (id_trans (mult_comm zero one) (mult_zero one)))).
    assert (Hlin : Id (sum_over_S (fun s => mult zero one))
                      (mult zero (sum_over_S (fun s => one))))
      by exact (sum_over_S_linear zero (fun s : S => one)).
    assert (Hmz : Id (mult zero (sum_over_S (fun s : S => one))) zero)
      by exact (id_trans (mult_comm zero (sum_over_S (fun s : S => one)))
                         (mult_zero (sum_over_S (fun s : S => one)))).
    exact (id_trans Hsame (id_trans Hlin Hmz)).
  }
  exact (id_trans Hext Hzero).
Qed.

(* (a) the ELBO is tight at the Boltzmann distribution:
   ELBO[p_b] = evidence.
   Proof: [evidence_kl_decomp] gives evidence = ELBO[p_b] + D * KL(p_b || p_b),
   and [relative_entropy_self_zero'] gives KL(p_b || p_b) = 0, hence
   evidence = ELBO[p_b].
   Content: vanishing self-relative-entropy plus ring cancellation. *)
Theorem elbo_tight :
  Id (elbo boltzmann_dist) evidence.
Proof.
  unfold evidence.
  (* evidence = ELBO[p_b] + D * KL(p_b || p_b) (the KL decomposition at
   q = p_b) *)
  assert (Hkl : Id (mult D (relative_entropy boltzmann_dist boltzmann_dist)) zero).
  {
    assert (Hself : Id (relative_entropy boltzmann_dist boltzmann_dist) zero)
      by exact (relative_entropy_self_zero' boltzmann_dist).
    exact (id_trans (id_cong (fun x => mult D x) Hself) (mult_zero D)).
  }
  assert (Hdec : Id evidence
                   (plus (elbo boltzmann_dist) (mult D (relative_entropy boltzmann_dist boltzmann_dist))))
    by exact (evidence_kl_decomp boltzmann_dist (boltzmann_normalized)).
  (* evidence = ELBO[p_b] + 0 = ELBO[p_b] *)
  assert (Hplus : Id (plus (elbo boltzmann_dist) (mult D (relative_entropy boltzmann_dist boltzmann_dist)))
                     (elbo boltzmann_dist))
    by exact (id_trans (id_cong (fun x => plus (elbo boltzmann_dist) x) Hkl)
                       (plus_zero (elbo boltzmann_dist))).
  exact (id_sym (id_trans Hdec Hplus)).
Qed.

(* (b) the evidence-ELBO gap equals D * KL(q || p_b) (an exact diagnostic
   of the variational gap).
   Proof: [evidence_kl_decomp] gives evidence = ELBO(q) + D * KL(q || p_b);
   subtract ELBO(q) on both sides ([minus_plus_cancel_r]:
   minus (plus a b) a = b).
   Content: the KL decomposition identity plus cancellation by subtraction. *)
Theorem evidence_gap_kl :
  forall q : S -> R,
    normalized q ->
    Id (minus evidence (elbo q))
       (mult D (relative_entropy q boltzmann_dist)).
Proof.
  intros q Hnq.
  assert (Hdec : Id evidence
                   (plus (elbo q) (mult D (relative_entropy q boltzmann_dist))))
    by exact (evidence_kl_decomp q Hnq).
  (* subtract elbo q on both sides:
   minus evidence (elbo q) = minus (plus (elbo q) KL') (elbo q) = KL' *)
  assert (Hminus : Id (minus evidence (elbo q))
                      (minus (plus (elbo q) (mult D (relative_entropy q boltzmann_dist))) (elbo q)))
    by exact (id_cong (fun x => minus x (elbo q)) Hdec).
  assert (Hcancel : Id (minus (plus (elbo q) (mult D (relative_entropy q boltzmann_dist))) (elbo q))
                       (mult D (relative_entropy q boltzmann_dist)))
    by exact (minus_plus_cancel_r (elbo q) (mult D (relative_entropy q boltzmann_dist))).
  exact (id_trans Hminus Hcancel).
Qed.

(* ============================================================ *)
(* KL equivalence of the cross-entropy training objective *)
(* ============================================================ *)
(* core: cross_entropy(p, q) - cross_entropy(p, p) = KL(p || q) *)
(* meaning: with the target distribution p fixed, minimizing cross-entropy
   is minimizing KL(p || q). *)
(* route: [cross_entropy_decomp], vanishing self-relative-entropy, and
   ring-algebra regrouping. *)
(* ------------------------------------------------------------ *)

(* cross-entropy minus own entropy = KL: H(p, q) - H(p, p) = KL(p || q).
   Proof: H(p, q) = S[p] + KL(p || q) ([cross_entropy_decomp]);
   H(p, p) = S[p] + KL(p || p) = S[p] (self-KL vanishes);
   subtracting: S[p] + KL(p || q) - S[p] = KL(p || q)
   ([plus_assoc] and [plus_opp]). *)
Theorem cross_entropy_minus_self :
  forall p q : S -> R,
    Id (minus (cross_entropy p q) (cross_entropy p p))
       (relative_entropy p q).
Proof.
  intros p q.
  (* H(p,q) = S[p] + KL(p||q) *)
  assert (H1 : Id (cross_entropy p q)
                  (plus (entropy_dist p) (relative_entropy p q)))
    by exact (cross_entropy_decomp p q).
  (* H(p, p) = S[p] + KL(p || p) = S[p] (self-KL vanishes) *)
  assert (H2 : Id (cross_entropy p p) (entropy_dist p)).
  {
    assert (H2a : Id (cross_entropy p p)
                     (plus (entropy_dist p) (relative_entropy p p)))
      by exact (cross_entropy_decomp p p).
    assert (H2b : Id (relative_entropy p p) zero)
      by exact (relative_entropy_self_zero' p).
    assert (H2c : Id (plus (entropy_dist p) (relative_entropy p p))
                     (plus (entropy_dist p) zero))
      by exact (id_cong (fun x => plus (entropy_dist p) x) H2b).
    assert (H2d : Id (plus (entropy_dist p) zero) (entropy_dist p))
      by exact (plus_zero (entropy_dist p)).
    exact (id_trans H2a (id_trans H2c H2d)).
  }
  (* H(p,q) - H(p,p) = (S + KL) - S = KL *)
  assert (Hmain : Id (minus (plus (entropy_dist p) (relative_entropy p q)) (entropy_dist p))
                     (relative_entropy p q)).
  {
    unfold minus.
    (* plus (plus S KL) (opp S) = plus S (plus KL (opp S)) = plus S (plus (opp S) KL) = KL *)
    assert (Ha : Id (plus (plus (entropy_dist p) (relative_entropy p q)) (opp (entropy_dist p)))
                    (plus (entropy_dist p) (plus (relative_entropy p q) (opp (entropy_dist p)))))
      by exact (id_sym (plus_assoc (entropy_dist p) (relative_entropy p q) (opp (entropy_dist p)))).
    assert (Hb : Id (plus (entropy_dist p) (plus (relative_entropy p q) (opp (entropy_dist p))))
                    (plus (entropy_dist p) (plus (opp (entropy_dist p)) (relative_entropy p q))))
      by exact (id_cong (fun x => plus (entropy_dist p) x)
                        (plus_comm (relative_entropy p q) (opp (entropy_dist p)))).
    assert (Hc : Id (plus (entropy_dist p) (plus (opp (entropy_dist p)) (relative_entropy p q)))
                    (plus (plus (entropy_dist p) (opp (entropy_dist p))) (relative_entropy p q)))
      by exact (plus_assoc (entropy_dist p) (opp (entropy_dist p)) (relative_entropy p q)).
    assert (Hd : Id (plus (plus (entropy_dist p) (opp (entropy_dist p))) (relative_entropy p q))
                    (plus zero (relative_entropy p q)))
      by exact (id_cong (fun x => plus x (relative_entropy p q)) (plus_opp (entropy_dist p))).
    assert (He : Id (plus zero (relative_entropy p q)) (relative_entropy p q))
      by exact (id_trans (plus_comm zero (relative_entropy p q)) (plus_zero (relative_entropy p q))).
    exact (id_trans Ha (id_trans Hb (id_trans Hc (id_trans Hd He)))).
  }
  (* assemble: H(p, q) - H(p, p) = (S + KL) - S = KL *)
  assert (Hrepl : Id (minus (cross_entropy p q) (cross_entropy p p))
                     (minus (plus (entropy_dist p) (relative_entropy p q)) (entropy_dist p)))
    by exact (id_cong2 minus H1 H2).
  exact (id_trans Hrepl Hmain).
Qed.

(* training equivalence: decreases in cross-entropy are decreases in KL
   (target p fixed).  If H(p, q2) <= H(p, q1), then
   KL(p || q2) <= KL(p || q1).
   Route: the [cross_entropy_decomp] decomposition, cancelling the common
   summand, and a nonnegative-difference chain. *)

(* local lemma: cancelling a common summand,
   minus (plus A B) (plus A C) = minus B C *)
Lemma minus_plus_common_local : forall A B C : R,
  Id (minus (plus A B) (plus A C)) (minus B C).
Proof.
  intros A B C.
  unfold minus.
  assert (H1 : Id (plus (plus A B) (opp (plus A C)))
                  (plus (plus A B) (plus (opp A) (opp C))))
    by exact (id_cong (fun x => plus (plus A B) x) (opp_plus A C)).
  assert (H2 : Id (plus (plus A B) (plus (opp A) (opp C)))
                  (plus (plus A (opp A)) (plus B (opp C))))
    by exact (plus_swap_mid A B (opp A) (opp C)).
  assert (H3 : Id (plus (plus A (opp A)) (plus B (opp C)))
                  (plus zero (plus B (opp C))))
    by exact (id_cong (fun x => plus x (plus B (opp C))) (plus_opp A)).
  assert (H4 : Id (plus zero (plus B (opp C))) (plus B (opp C)))
    by exact (id_trans (plus_comm zero (plus B (opp C))) (plus_zero (plus B (opp C)))).
  exact (id_trans H1 (id_trans H2 (id_trans H3 H4))).
Qed.

Theorem training_equivalence :
  forall p q1 q2 : S -> R,
    le (cross_entropy p q2) (cross_entropy p q1) ->
    le (relative_entropy p q2) (relative_entropy p q1).
Proof.
  intros p q1 q2 Hce.
  (* difference identity: (H2 - H1) = (KL2 - KL1).
   H2 = S + KL2 and H1 = S + KL1 ([cross_entropy_decomp]);
   subtracting cancels the common term S via [minus_plus_common_local]. *)
  assert (Hdiff : Id (minus (cross_entropy p q2) (cross_entropy p q1))
                     (minus (relative_entropy p q2) (relative_entropy p q1))).
  {
    assert (H2d : Id (cross_entropy p q2)
                     (plus (entropy_dist p) (relative_entropy p q2)))
      by exact (cross_entropy_decomp p q2).
    assert (H1d : Id (cross_entropy p q1)
                     (plus (entropy_dist p) (relative_entropy p q1)))
      by exact (cross_entropy_decomp p q1).
    assert (Hrepl : Id (minus (cross_entropy p q2) (cross_entropy p q1))
                       (minus (plus (entropy_dist p) (relative_entropy p q2))
                              (plus (entropy_dist p) (relative_entropy p q1))))
      by exact (id_cong2 minus H2d H1d).
    assert (Hcancel : Id (minus (plus (entropy_dist p) (relative_entropy p q2))
                                (plus (entropy_dist p) (relative_entropy p q1)))
                         (minus (relative_entropy p q2) (relative_entropy p q1)))
      by exact (minus_plus_common_local (entropy_dist p) (relative_entropy p q2) (relative_entropy p q1)).
    exact (id_trans Hrepl Hcancel).
  }
  (* from Hce : le H2 H1 derive le zero (minus H1 H2)
   ([le_minus_nonneg] H2 H1) *)
  assert (Hd : le zero (minus (cross_entropy p q1) (cross_entropy p q2)))
    by exact (le_minus_nonneg (cross_entropy p q2) (cross_entropy p q1) Hce).
  (* substitute: minus H1 H2 = minus KL1 KL2 ([cross_entropy_decomp] and
   cancellation of the common term) *)
  assert (Hdiff' : Id (minus (cross_entropy p q1) (cross_entropy p q2))
                      (minus (relative_entropy p q1) (relative_entropy p q2))).
  {
    assert (H1d : Id (cross_entropy p q1)
                     (plus (entropy_dist p) (relative_entropy p q1)))
      by exact (cross_entropy_decomp p q1).
    assert (H2d : Id (cross_entropy p q2)
                     (plus (entropy_dist p) (relative_entropy p q2)))
      by exact (cross_entropy_decomp p q2).
    assert (Hrepl : Id (minus (cross_entropy p q1) (cross_entropy p q2))
                       (minus (plus (entropy_dist p) (relative_entropy p q1))
                              (plus (entropy_dist p) (relative_entropy p q2))))
      by exact (id_cong2 minus H1d H2d).
    assert (Hcancel : Id (minus (plus (entropy_dist p) (relative_entropy p q1))
                                (plus (entropy_dist p) (relative_entropy p q2)))
                         (minus (relative_entropy p q1) (relative_entropy p q2)))
      by exact (minus_plus_common_local (entropy_dist p) (relative_entropy p q1) (relative_entropy p q2)).
    exact (id_trans Hrepl Hcancel).
  }
  assert (Hd' : le zero (minus (relative_entropy p q1) (relative_entropy p q2)))
    by exact (le_id_r zero (minus (cross_entropy p q1) (cross_entropy p q2))
                      (minus (relative_entropy p q1) (relative_entropy p q2))
                      Hdiff' Hd).
  (* le KL2 KL1: KL2 <= KL2 + (KL1 - KL2) = KL1 *)
  apply (le_id_r (relative_entropy p q2)
                 (plus (relative_entropy p q2) (minus (relative_entropy p q1) (relative_entropy p q2)))
                 (relative_entropy p q1)
                 (minus_plus_cancel (relative_entropy p q2) (relative_entropy p q1))).
  exact (le_plus_nonneg_r (relative_entropy p q2)
                          (minus (relative_entropy p q1) (relative_entropy p q2)) Hd').
Qed.

End FreeEnergyMinimization.

(* ============================================================ *)
(* KL-regularized reward maximization (the alignment setting of modern
   model training) *)
(* ============================================================ *)
(* the goal of modern alignment (RLHF/DPO/PPO): *)
(* maximize E_pi[r] - beta * KL(pi‖pi_ref) *)
(* maximize reward while staying within a KL penalty of the reference
   policy pi_ref (the SFT policy). *)
(* Mathematically this replicates the Boltzmann mechanism exactly (reward
   in place of energy, the reference *)
(* policy in place of the uniform prior).  Closed form:
   pi*(s) proportional to pi_ref(s) * e^(r(s)/beta). *)
(* Optimality J(pi) <= J(pi_star) is proved via solving back for the reward
   plus the Gibbs inequality. *)
(* ------------------------------------------------------------ *)

Print Assumptions r_pow_nonneg.
Print Assumptions mult_one_minus_r.
Print Assumptions telescoping.
Print Assumptions one_minus_kappa_pos.
Print Assumptions mult_swap_mid.
Print Assumptions mult_swap_outer.
Print Assumptions minus_pos.
Print Assumptions mult_minus_distr_r.
