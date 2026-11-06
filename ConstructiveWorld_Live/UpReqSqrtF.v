(* ConstructiveWorld-Set -- constructive numeric constructions over the req setoid interface. *)

(** * UpReqSqrtF: functional Newton square root with explicit slack certificates.

    Mission.  A functional Newton square root on the [req]-setoid ring
      interface: [sqrtf_newton_dep] iterates values with positivity
      witnesses in [sigT], [sqrtf_sqrt] returns value, witness and slack
      term [t] with [req (mult r r) (plus (mult t t) a)],
      [sqrtf_fixed_point_correct] turns fixed points of the Newton step into
      square roots, and [sqrtf_sq_ge_a], [sqrtf_iterate_lower],
      [nsq_slack_contraction] carry the convergence estimates.

    Dependencies.  Requires [S01_BaseRing], [S02_CauchyComplete], [S03_QExp],
      [S04_RealExpLogConv], [S05_AlignmentGRPO], [S06_DiffSamplingGibbs],
      [S07_RealSetoidExpLog], [S08_RealMainlineDPO], [S09_EntropyReal],
      [S10_KVQuantTrig], [S11_TP3B5], [S12_B5RecycleSF],
      [S13_NLiveAudit], [S14_B5BatchBlock], [S15_TailFEPUp],
      [UpReqAlgebra] of this development.

    References.  This development, UpReqSqrtF.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" UpReqSqrtF.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 00015ff4]. *)
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
Import RealInterfaceEnhancedMod.

Section SqrtF.

(* Tree-face adaptation (registered precedent: UpDebtSqrtAbsReq / UpReqAlgebra;
   class declaration at S07_RealSetoidExpLog.v L8075 "Class
   RealInterfaceEnhancedSetoid").  In this tree the interface class is
   unparameterized: its carrier is the global Real and its sole registered
   instance is RealEnhancedReal.  The source piece was written against the
   older parameterized-interface world, so the two Context lines
   (Context {R : Set} and Context {RIS : RealInterfaceEnhancedSetoid R}) are
   replaced by the notation below, and the Let bindings re-anchor to that
   instance.  Statement-face re-anchor (registered precedent: the
   UpDebtSqrtAbsReq real_eq face): every bare projection token req/lt/le on
   the statement faces and the assert type faces is rewritten to the
   concrete faces real_eq/real_lt/real_le (S02_CauchyComplete 409/411/480/484),
   with statement names unchanged; the two order-field anchor Lets
   (Let lt / Let le) are removed as no longer needed.  Proof bodies keep
   zero character changes. *)
Notation R := Real.

Let zero := @zero RealEnhancedReal.
Let one := @one RealEnhancedReal.
Let plus := @plus RealEnhancedReal.
Let mult := @mult RealEnhancedReal.
Let opp := @opp RealEnhancedReal.
Let inv_pos := @inv_pos RealEnhancedReal.

(* ============================================================ *)
(* Section 1. Newton constants: two := 1+1 and half := inv(two).  *)
(*   (the same local rebuild as UpDebtSqrtAbsReq; the nsq_ prefix *)
(*   keeps the names clash-free)                                  *)
(* ============================================================ *)

Definition nsq_two : R := plus one one.

Lemma nsq_two_pos : real_lt zero nsq_two.
Proof.
  exact (plus_positive one one one_pos one_pos).
Qed.

Definition nsq_half : R := inv_pos nsq_two nsq_two_pos.

Lemma nsq_half_pos : real_lt zero nsq_half.
Proof. exact (inv_pos_pos nsq_two nsq_two_pos). Qed.

(* two * half == one: a direct use of [inv_pos_correct], the defining
   kernel of half *)
Lemma nsq_half_two_correct : real_eq (mult nsq_two nsq_half) one.
Proof. exact (inv_pos_correct nsq_two nsq_two_pos). Qed.

(* ============================================================ *)
(* Section 2. one Newton step: g(y) := half * (y + a * (1/y)).    *)
(*   positivity: half > 0, y > 0 and a * (1/y) > 0 give a positive *)
(*   sum, hence a positive product.                              *)
(* ============================================================ *)

Definition sqrtf_step (a y : R) (Ha : real_lt zero a) (Hy : real_lt zero y) : R :=
  mult nsq_half (plus y (mult a (inv_pos y Hy))).

Lemma sqrtf_step_pos : forall (a y : R) (Ha : real_lt zero a) (Hy : real_lt zero y),
  real_lt zero (sqrtf_step a y Ha Hy).
Proof.
  intros a y Ha Hy. unfold sqrtf_step.
  apply mult_positive.
  - exact nsq_half_pos.
  - apply plus_positive.
    + exact Hy.
    + apply mult_positive.
      * exact Ha.
      * apply inv_pos_pos.
Qed.

(* ============================================================ *)
(* Section 3. the functional Newton iteration (a dependent        *)
(*   Fixpoint that carries its proofs).  Each recursive rank      *)
(*   produces a [sigT] pair (value, positivity witness), so the   *)
(*   positivity invariant is generated in lockstep with the       *)
(*   function body, entirely at the [Set] level.                  *)
(* ============================================================ *)

Fixpoint sqrtf_newton_dep (a : R) (Ha : real_lt zero a) (x : R) (Hx : real_lt zero x)
         (n : nat) {struct n} : sigT (fun y : R => real_lt zero y) :=
  match n with
  | Datatypes.O => existT _ x Hx
  | Datatypes.S m =>
      match sqrtf_newton_dep a Ha x Hx m with
      | existT _ y Hy =>
          existT _ (sqrtf_step a y Ha Hy) (sqrtf_step_pos a y Ha Hy)
      end
  end.

(* function body: the n-step Newton iteration (the rank n controls the
   iteration precision) *)
Definition sqrtf_newton (a : R) (Ha : real_lt zero a) (x : R) (Hx : real_lt zero x)
           (n : nat) : R :=
  projT1 (sqrtf_newton_dep a Ha x Hx n).

(* positivity invariant: every iterate is strictly positive (the second
   component of the dependent Fixpoint, used directly).
   A transparent Definition rather than a lemma: the positivity witness
   feeds a value position of the iteration (the witness position of
   [inv_pos] is itself a value position, proof-relevant, with
   precedent), and the canonical witness must reduce by delta to stay
   convertible with the witnesses produced inside the Fixpoint body. *)
Definition sqrtf_newton_pos (a : R) (Ha : real_lt zero a) (x : R) (Hx : real_lt zero x)
           (n : nat) : real_lt zero (sqrtf_newton a Ha x Hx n) :=
  projT2 (sqrtf_newton_dep a Ha x Hx n).

(* unfolding of the iteration (two sanity statements): the rank-0 value
   returns the initial point; the rank (S n) value is one step applied
   to the rank-n value *)
Lemma sqrtf_newton_zero : forall (a : R) (Ha : real_lt zero a) (x : R) (Hx : real_lt zero x),
  real_eq (sqrtf_newton a Ha x Hx 0) x.
Proof.
  intros a Ha x Hx. unfold sqrtf_newton.
  exact (req_refl x).
Qed.

Lemma sqrtf_newton_succ : forall (a : R) (Ha : real_lt zero a) (x : R) (Hx : real_lt zero x)
                                 (n : nat),
  real_eq (sqrtf_newton a Ha x Hx (Datatypes.S n))
      (sqrtf_step a (sqrtf_newton a Ha x Hx n) Ha
                   (sqrtf_newton_pos a Ha x Hx n)).
Proof.
  intros a Ha x Hx n.
  unfold sqrtf_newton, sqrtf_newton_pos.
  cbn [sqrtf_newton_dep projT1].
  destruct (sqrtf_newton_dep a Ha x Hx n) as [y Hy] eqn:E.
  exact (req_refl (sqrtf_step a y Ha Hy)).
Qed.

(* ============================================================ *)
(* Section 4. the Newton algebra engine (pure polynomial ring     *)
(*   algebra on the [req] carrier).  Core identity:               *)
(*   g(y) * g(y) == s(y) * s(y) + a with s(y) := half * (y - a/y)  *)
(*   (the residual square: the square of a Newton output equals a  *)
(*   plus an exact square -- the algebraic shape of finite-step    *)
(*   approximate correctness).                                    *)
(* ============================================================ *)

(* tail lemma: half * (X+X) == X, a direct consequence of
   two * half == one *)
Lemma nsq_tail : forall X : R, real_eq (mult nsq_half (plus X X)) X.
Proof.
  intro X.
  apply (req_trans (mult nsq_half (plus X X))
                   (mult (mult nsq_half nsq_two) X)
                   X).
  - apply (req_trans (mult nsq_half (plus X X))
                     (mult nsq_half (mult nsq_two X))
                     (mult (mult nsq_half nsq_two) X)).
    + exact (req_mult_compat nsq_half nsq_half (plus X X) (mult nsq_two X)
               (req_refl nsq_half)
               (req_sym (mult nsq_two X) (plus X X) (req_two_mult X))).
    + exact (mult_assoc nsq_half nsq_two X).
  - apply (req_trans (mult (mult nsq_half nsq_two) X)
                     (mult one X)
                     X).
    + exact (req_mult_compat (mult nsq_half nsq_two) one X X
               (req_trans (mult nsq_half nsq_two) (mult nsq_two nsq_half) one
                          (mult_comm nsq_half nsq_two)
                          nsq_half_two_correct)
               (req_refl X)).
    + exact (req_trans (mult one X) (mult X one) X
                       (mult_comm one X) (mult_one X)).
Qed.

(* generalized step difference: h*(p+q) - h*(p-q) == h*(q+q), on the
   [req_minus] carrier *)
Lemma nsq_h_minus : forall h p q : R,
  real_eq (req_minus (mult h (plus p q)) (mult h (plus p (opp q))))
      (mult h (plus q q)).
Proof.
  intros h p q. unfold req_minus.
  apply (req_trans (plus (mult h (plus p q)) (opp (mult h (plus p (opp q)))))
                   (mult h (plus (plus p q) (opp (plus p (opp q)))))
                   (mult h (plus q q))).
  - apply (req_trans (plus (mult h (plus p q)) (opp (mult h (plus p (opp q)))))
                     (plus (mult h (plus p q))
                           (mult h (opp (plus p (opp q)))))
                     (mult h (plus (plus p q) (opp (plus p (opp q)))))).
    + exact (req_plus_compat (mult h (plus p q)) (mult h (plus p q))
                             (opp (mult h (plus p (opp q))))
                             (mult h (opp (plus p (opp q))))
                             (req_refl (mult h (plus p q)))
                             (req_sym (mult h (opp (plus p (opp q))))
                                      (opp (mult h (plus p (opp q))))
                                      (req_opp_mult_l h (plus p (opp q))))).
    + exact (req_sym (mult h (plus (plus p q) (opp (plus p (opp q)))))
                     (plus (mult h (plus p q))
                           (mult h (opp (plus p (opp q)))))
                     (distrib h (plus p q) (opp (plus p (opp q))))).
  - exact (req_mult_compat h h
             (plus (plus p q) (opp (plus p (opp q)))) (plus q q)
             (req_refl h)
             (req_trans (plus (plus p q) (opp (plus p (opp q))))
                        (plus q (opp (opp q)))
                        (plus q q)
                        (req_minus_plus_congr p q (opp q))
                        (req_plus_compat q q (opp (opp q)) q
                           (req_refl q) (req_double_neg q)))).
Qed.

(* generalized step sum: h*(p+q) + h*(p-q) == h*(p+p) *)
Lemma nsq_h_plus : forall h p q : R,
  real_eq (plus (mult h (plus p q)) (mult h (plus p (opp q))))
      (mult h (plus p p)).
Proof.
  intros h p q. unfold req_minus.
  apply (req_trans (plus (mult h (plus p q)) (mult h (plus p (opp q))))
                   (mult h (plus (plus p q) (plus p (opp q))))
                   (mult h (plus p p))).
  - exact (req_sym (mult h (plus (plus p q) (plus p (opp q))))
                   (plus (mult h (plus p q)) (mult h (plus p (opp q))))
                   (distrib h (plus p q) (plus p (opp q)))).
  - exact (req_mult_compat h h
             (plus (plus p q) (plus p (opp q))) (plus p p)
             (req_refl h)
             (req_trans (plus (plus p q) (plus p (opp q)))
                        (plus (plus p p) (plus q (opp q)))
                        (plus p p)
                        (req_plus_swap_mid p q p (opp q))
                        (req_trans (plus (plus p p) (plus q (opp q)))
                                   (plus (plus p p) zero)
                                   (plus p p)
                                   (req_plus_compat (plus p p) (plus p p)
                                      (plus q (opp q)) zero
                                      (req_refl (plus p p)) (plus_opp q))
                                   (plus_zero (plus p p))))).
Qed.

(* generalized polarization identity: p*p == (p-q)*(p+q) + q*q (a
   difference-of-squares decomposition) *)
Lemma nsq_polarization : forall p q : R,
  real_eq (mult p p)
      (plus (mult (req_minus p q) (plus p q)) (mult q q)).
Proof.
  intros p q. unfold req_minus.
  assert (Hd : real_eq (mult (plus p (opp q)) (plus p q))
                   (plus (mult p p) (opp (mult q q)))).
  { apply (req_trans
             (mult (plus p (opp q)) (plus p q))
             (plus (mult (plus p (opp q)) p) (mult (plus p (opp q)) q))
             (plus (mult p p) (opp (mult q q)))).
    - exact (distrib (plus p (opp q)) p q).
    - apply (req_trans
               (plus (mult (plus p (opp q)) p) (mult (plus p (opp q)) q))
               (plus (plus (mult p p) (opp (mult p q)))
                     (plus (mult q p) (opp (mult q q))))
               (plus (mult p p) (opp (mult q q)))).
      + apply (req_plus_compat
                 (mult (plus p (opp q)) p)
                 (plus (mult p p) (opp (mult p q)))
                 (mult (plus p (opp q)) q)
                 (plus (mult q p) (opp (mult q q)))
                 (req_trans (mult (plus p (opp q)) p)
                            (mult p (plus p (opp q)))
                            (plus (mult p p) (opp (mult p q)))
                            (mult_comm (plus p (opp q)) p)
                            (req_trans (mult p (plus p (opp q)))
                                       (plus (mult p p) (mult p (opp q)))
                                       (plus (mult p p) (opp (mult p q)))
                                       (distrib p p (opp q))
                                       (req_plus_compat (mult p p) (mult p p)
                                          (mult p (opp q)) (opp (mult p q))
                                          (req_refl (mult p p))
                                          (req_opp_mult_l p q))))
                 (req_trans (mult (plus p (opp q)) q)
                            (mult q (plus p (opp q)))
                            (plus (mult q p) (opp (mult q q)))
                            (mult_comm (plus p (opp q)) q)
                            (req_trans (mult q (plus p (opp q)))
                                       (plus (mult q p) (mult q (opp q)))
                                       (plus (mult q p) (opp (mult q q)))
                                       (distrib q p (opp q))
                                       (req_plus_compat (mult q p) (mult q p)
                                          (mult q (opp q)) (opp (mult q q))
                                          (req_refl (mult q p))
                                          (req_opp_mult_l q q))))).
      + apply (req_trans
                 (plus (plus (mult p p) (opp (mult p q)))
                       (plus (mult q p) (opp (mult q q))))
                 (plus (mult p p)
                       (plus (plus (opp (mult p q)) (mult q p))
                             (opp (mult q q))))
                 (plus (mult p p) (opp (mult q q)))).
        * exact (req_trans
                   (plus (plus (mult p p) (opp (mult p q)))
                         (plus (mult q p) (opp (mult q q))))
                   (plus (mult p p)
                         (plus (opp (mult p q)) (plus (mult q p) (opp (mult q q)))))
                   (plus (mult p p)
                         (plus (plus (opp (mult p q)) (mult q p)) (opp (mult q q))))
                   (req_sym (plus (mult p p)
                                  (plus (opp (mult p q)) (plus (mult q p) (opp (mult q q)))))
                            (plus (plus (mult p p) (opp (mult p q)))
                                  (plus (mult q p) (opp (mult q q))))
                            (plus_assoc (mult p p) (opp (mult p q))
                                        (plus (mult q p) (opp (mult q q)))))
                   (req_plus_compat (mult p p) (mult p p)
                      (plus (opp (mult p q)) (plus (mult q p) (opp (mult q q))))
                      (plus (plus (opp (mult p q)) (mult q p)) (opp (mult q q)))
                      (req_refl (mult p p))
                      (plus_assoc (opp (mult p q)) (mult q p) (opp (mult q q))))).
        * apply (req_trans
                   (plus (mult p p)
                         (plus (plus (opp (mult p q)) (mult q p))
                               (opp (mult q q))))
                   (plus (mult p p) (plus zero (opp (mult q q))))
                   (plus (mult p p) (opp (mult q q)))).
          -- exact (req_plus_compat (mult p p) (mult p p)
                      (plus (plus (opp (mult p q)) (mult q p)) (opp (mult q q)))
                      (plus zero (opp (mult q q)))
                      (req_refl (mult p p))
                      (req_plus_compat (plus (opp (mult p q)) (mult q p)) zero
                         (opp (mult q q)) (opp (mult q q))
                         (req_trans (plus (opp (mult p q)) (mult q p))
                                    (plus (opp (mult p q)) (mult p q))
                                    zero
                                    (req_plus_compat (opp (mult p q)) (opp (mult p q))
                                       (mult q p) (mult p q)
                                       (req_refl (opp (mult p q)))
                                       (mult_comm q p))
                                    (req_trans (plus (opp (mult p q)) (mult p q))
                                               (plus (mult p q) (opp (mult p q)))
                                               zero
                                               (plus_comm (opp (mult p q)) (mult p q))
                                               (plus_opp (mult p q))))
                         (req_refl (opp (mult q q))))).
          -- exact (req_plus_compat (mult p p) (mult p p)
                       (plus zero (opp (mult q q))) (opp (mult q q))
                       (req_refl (mult p p))
                       (req_trans (plus zero (opp (mult q q)))
                                  (plus (opp (mult q q)) zero)
                                  (opp (mult q q))
                                  (plus_comm zero (opp (mult q q)))
                                  (plus_zero (opp (mult q q))))). }
  exact (req_sym
           (plus (mult (plus p (opp q)) (plus p q)) (mult q q))
           (mult p p)
           (req_trans (plus (mult (plus p (opp q)) (plus p q)) (mult q q))
                      (plus (plus (mult p p) (opp (mult q q))) (mult q q))
                      (mult p p)
                      (req_plus_compat (mult (plus p (opp q)) (plus p q))
                                       (plus (mult p p) (opp (mult q q)))
                                       (mult q q) (mult q q)
                                       Hd (req_refl (mult q q)))
                      (req_trans (plus (plus (mult p p) (opp (mult q q))) (mult q q))
                                 (plus (mult p p) (plus (opp (mult q q)) (mult q q)))
                                 (mult p p)
                                 (req_sym (plus (mult p p)
                                                (plus (opp (mult q q)) (mult q q)))
                                          (plus (plus (mult p p) (opp (mult q q)))
                                                (mult q q))
                                          (plus_assoc (mult p p) (opp (mult q q))
                                                      (mult q q)))
                                 (req_trans (plus (mult p p)
                                                  (plus (opp (mult q q)) (mult q q)))
                                            (plus (mult p p) zero)
                                            (mult p p)
                                            (req_plus_compat (mult p p) (mult p p)
                                               (plus (opp (mult q q)) (mult q q)) zero
                                               (req_refl (mult p p))
                                               (req_trans (plus (opp (mult q q)) (mult q q))
                                                          (plus (mult q q) (opp (mult q q)))
                                                          zero
                                                          (plus_comm (opp (mult q q)) (mult q q))
                                                          (plus_opp (mult q q))))
                                            (plus_zero (mult p p)))))).
Qed.

(* cross term: (a*(1/y))*y == a, a reordered use of [inv_pos_correct] *)
Lemma nsq_u_mult_y : forall (a y : R) (Ha : real_lt zero a) (Hy : real_lt zero y),
  real_eq (mult (mult a (inv_pos y Hy)) y) a.
Proof.
  intros a y Ha Hy.
  apply (req_trans (mult (mult a (inv_pos y Hy)) y)
                   (mult a (mult (inv_pos y Hy) y))
                   a).
  - exact (req_sym (mult a (mult (inv_pos y Hy) y))
                   (mult (mult a (inv_pos y Hy)) y)
                   (mult_assoc a (inv_pos y Hy) y)).
  - apply (req_trans (mult a (mult (inv_pos y Hy) y))
                     (mult a (mult y (inv_pos y Hy)))
                     a).
    + exact (req_mult_compat a a (mult (inv_pos y Hy) y) (mult y (inv_pos y Hy))
               (req_refl a) (mult_comm (inv_pos y Hy) y)).
    + apply (req_trans (mult a (mult y (inv_pos y Hy)))
                       (mult a one)
                       a).
      * exact (req_mult_compat a a (mult y (inv_pos y Hy)) one
                 (req_refl a) (inv_pos_correct y Hy)).
      * exact (req_trans (mult a one) (mult one a) a
                         (mult_comm a one)
                         (req_trans (mult one a) (mult a one) a
                                    (mult_comm one a) (mult_one a))).
Qed.

(* ============================================================ *)
(* Section 5. finite-step approximate correctness pieces.        *)
(* ============================================================ *)

(* slack term: s(y) := half * (y - a/y), the carrier paired with g(y) *)
Definition sqrtf_slack (a y : R) (Ha : real_lt zero a) (Hy : real_lt zero y) : R :=
  mult nsq_half (plus y (opp (mult a (inv_pos y Hy)))).

(* step difference: g(y) - s(y) == a/y *)
Lemma nsq_step_minus_slack : forall (a y : R) (Ha : real_lt zero a) (Hy : real_lt zero y),
  real_eq (req_minus (sqrtf_step a y Ha Hy) (sqrtf_slack a y Ha Hy))
      (mult a (inv_pos y Hy)).
Proof.
  intros a y Ha Hy.
  exact (req_trans (req_minus (sqrtf_step a y Ha Hy) (sqrtf_slack a y Ha Hy))
                   (mult nsq_half (plus (mult a (inv_pos y Hy)) (mult a (inv_pos y Hy))))
                   (mult a (inv_pos y Hy))
                   (nsq_h_minus nsq_half y (mult a (inv_pos y Hy)))
                   (nsq_tail (mult a (inv_pos y Hy)))).
Qed.

(* step sum: g(y) + s(y) == y *)
Lemma nsq_step_plus_slack : forall (a y : R) (Ha : real_lt zero a) (Hy : real_lt zero y),
  real_eq (plus (sqrtf_step a y Ha Hy) (sqrtf_slack a y Ha Hy)) y.
Proof.
  intros a y Ha Hy.
  exact (req_trans (plus (sqrtf_step a y Ha Hy) (sqrtf_slack a y Ha Hy))
                   (mult nsq_half (plus y y))
                   y
                   (nsq_h_plus nsq_half y (mult a (inv_pos y Hy)))
                   (nsq_tail y)).
Qed.

(* ============================================================ *)
(* Section 5, continued: the residual square identity behind the  *)
(*   finite-step correctness pieces.  g(y) * g(y) == s(y) * s(y) + a: *)
(*   the square of the output equals a plus an exact square.      *)
(*   Decomposition: p*p == (p-q)*(p+q) + q*q (polarization); with *)
(*   p := g(y) and q := s(y) the cross term satisfies             *)
(*   (g-s)*(g+s) == (a/y)*y == a.                                 *)
(* ============================================================ *)

Lemma sqrtf_step_residual : forall (a y : R) (Ha : real_lt zero a) (Hy : real_lt zero y),
  sigT (fun s : R =>
        real_eq (mult (sqrtf_step a y Ha Hy) (sqrtf_step a y Ha Hy))
            (plus (mult s s) a)).
Proof.
  intros a y Ha Hy.
  exists (sqrtf_slack a y Ha Hy).
  apply (req_trans (mult (sqrtf_step a y Ha Hy) (sqrtf_step a y Ha Hy))
                   (plus (mult (req_minus (sqrtf_step a y Ha Hy) (sqrtf_slack a y Ha Hy))
                               (plus (sqrtf_step a y Ha Hy) (sqrtf_slack a y Ha Hy)))
                         (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy)))
                   (plus (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy)) a)).
  - exact (nsq_polarization (sqrtf_step a y Ha Hy) (sqrtf_slack a y Ha Hy)).
  - apply (req_trans
             (plus (mult (req_minus (sqrtf_step a y Ha Hy) (sqrtf_slack a y Ha Hy))
                         (plus (sqrtf_step a y Ha Hy) (sqrtf_slack a y Ha Hy)))
                   (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy)))
             (plus (mult (mult a (inv_pos y Hy)) y)
                   (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy)))
             (plus (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy)) a)).
    + exact (req_plus_compat
               (mult (req_minus (sqrtf_step a y Ha Hy) (sqrtf_slack a y Ha Hy))
                     (plus (sqrtf_step a y Ha Hy) (sqrtf_slack a y Ha Hy)))
               (mult (mult a (inv_pos y Hy)) y)
               (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy))
               (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy))
               (req_mult_compat
                  (req_minus (sqrtf_step a y Ha Hy) (sqrtf_slack a y Ha Hy))
                  (mult a (inv_pos y Hy))
                  (plus (sqrtf_step a y Ha Hy) (sqrtf_slack a y Ha Hy))
                  y
                  (nsq_step_minus_slack a y Ha Hy)
                  (nsq_step_plus_slack a y Ha Hy))
               (req_refl (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy)))).
    + apply (req_trans
               (plus (mult (mult a (inv_pos y Hy)) y)
                     (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy)))
               (plus a (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy)))
               (plus (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy)) a)).
      * exact (req_plus_compat (mult (mult a (inv_pos y Hy)) y) a
                 (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy))
                 (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy))
                 (nsq_u_mult_y a y Ha Hy)
                 (req_refl (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy)))).
      * exact (req_sym (plus (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy)) a)
                       (plus a (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy)))
                       (plus_comm (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy)) a)).
Qed.

(* ============================================================ *)
(* Section 6. the uniform per-step certificate and the functional *)
(*   square root (main theorem).                                  *)
(* ============================================================ *)

(* uniform per-step certificate: the iterate at rank (S n) satisfies
   z*z == t*t + a with t the slack term.  Finite-step approximate
   correctness: at every precision rank the output carries an explicit
   square-shaped remainder estimate (a larger n gives a smaller slack;
   see the part-2 skeleton note). *)
Lemma sqrtf_newton_cert : forall (a : R) (Ha : real_lt zero a) (x : R) (Hx : real_lt zero x)
                                (n : nat),
  sigT (fun t : R =>
        real_eq (mult (sqrtf_newton a Ha x Hx (Datatypes.S n))
                  (sqrtf_newton a Ha x Hx (Datatypes.S n)))
            (plus (mult t t) a)).
Proof.
  intros a Ha x Hx n.
  destruct (sqrtf_step_residual a (sqrtf_newton a Ha x Hx n) Ha
              (sqrtf_newton_pos a Ha x Hx n)) as [t Ht].
  exists t.
  apply (req_trans (mult (sqrtf_newton a Ha x Hx (Datatypes.S n))
                         (sqrtf_newton a Ha x Hx (Datatypes.S n)))
                   (mult (sqrtf_step a (sqrtf_newton a Ha x Hx n) Ha
                          (sqrtf_newton_pos a Ha x Hx n))
                         (sqrtf_step a (sqrtf_newton a Ha x Hx n) Ha
                          (sqrtf_newton_pos a Ha x Hx n)))
                   (plus (mult t t) a)).
  - exact (req_mult_compat (sqrtf_newton a Ha x Hx (Datatypes.S n))
                           (sqrtf_step a (sqrtf_newton a Ha x Hx n) Ha
                            (sqrtf_newton_pos a Ha x Hx n))
                           (sqrtf_newton a Ha x Hx (Datatypes.S n))
                           (sqrtf_step a (sqrtf_newton a Ha x Hx n) Ha
                            (sqrtf_newton_pos a Ha x Hx n))
                           (sqrtf_newton_succ a Ha x Hx n)
                           (sqrtf_newton_succ a Ha x Hx n)).
  - exact Ht.
Qed.

(* main theorem (the functional square root, the statement aligned with
   the U3 axis): given a > 0, an initial point x > 0 and a precision
   rank n, [sqrtf_sqrt] produces a triple (value r, positivity witness,
   slack term t) with r*r == t*t + a.  It is the constructive
   counterpart of a witness-style square root (given r, verify
   r*r == d): here r is computed by the Fixpoint and the remainder is
   carried explicitly.  The nesting is carried by [sigT], with the
   positivity witness raised to the first witness position. *)
Definition sqrtf_sqrt (a : R) (Ha : real_lt zero a) (x : R) (Hx : real_lt zero x) (n : nat)
  : sigT (fun r : R =>
          sigT (fun _ : real_lt zero r =>
                sigT (fun t : R =>
                      real_eq (mult r r) (plus (mult t t) a)))) :=
  existT _ (sqrtf_newton a Ha x Hx (Datatypes.S n))
    (existT _ (sqrtf_newton_pos a Ha x Hx (Datatypes.S n))
              (sqrtf_newton_cert a Ha x Hx n)).

(* specialization of the main theorem to the initial point x := a: a
   positive a supplies its own positive initial point, and the
   signature narrows to (a, Ha, n) *)
Lemma sqrtf_sqrt_self_init : forall (a : R) (Ha : real_lt zero a) (n : nat),
  sigT (fun r : R =>
        sigT (fun _ : real_lt zero r =>
              sigT (fun t : R =>
                    real_eq (mult r r) (plus (mult t t) a)))).
Proof.
  intros a Ha n.
  exact (existT _ (sqrtf_newton a Ha a Ha (Datatypes.S n))
           (existT _ (sqrtf_newton_pos a Ha a Ha (Datatypes.S n))
                     (sqrtf_newton_cert a Ha a Ha n))).
Qed.

(* ============================================================ *)
(* Section 7. the limit correctness piece and the skeleton of the *)
(*   convergence certificate.                                    *)
(* ============================================================ *)

(* limit correctness piece: the fixed points of the Newton step are
   exactly the square roots.  z == g(z) gives z*z == a.  Once the
   convergence certificate is completed (the Cauchy property of the
   z_n plus passage to the limit), this lemma promotes the limit value
   to a true square root -- the missing functional half of the
   1/sqrt(d) binding.  The proof is pure polynomial ring algebra:
   multiply both sides of the fixed point equation by two, then
   cancel. *)
Lemma sqrtf_fixed_point_correct : forall (a z : R) (Ha : real_lt zero a) (Hz : real_lt zero z),
  real_eq z (sqrtf_step a z Ha Hz) -> real_eq (mult z z) a.
Proof.
  intros a z Ha Hz H.
  (* first step: the fixed point equation gives two * z == z + a * (1/z) *)
  assert (H2 : real_eq (mult nsq_two z) (plus z (mult a (inv_pos z Hz)))).
  { apply (req_trans (mult nsq_two z)
                     (mult (mult nsq_two nsq_half)
                           (plus z (mult a (inv_pos z Hz))))
                     (plus z (mult a (inv_pos z Hz)))).
    - apply (req_trans (mult nsq_two z)
                       (mult nsq_two (sqrtf_step a z Ha Hz))
                       (mult (mult nsq_two nsq_half)
                             (plus z (mult a (inv_pos z Hz))))).
      + exact (req_mult_compat nsq_two nsq_two z (sqrtf_step a z Ha Hz)
                 (req_refl nsq_two) H).
      + exact (mult_assoc nsq_two nsq_half (plus z (mult a (inv_pos z Hz)))).
    - apply (req_trans (mult (mult nsq_two nsq_half) (plus z (mult a (inv_pos z Hz))))
                       (mult one (plus z (mult a (inv_pos z Hz))))
                       (plus z (mult a (inv_pos z Hz)))).
      + exact (req_mult_compat (mult nsq_two nsq_half) one
                 (plus z (mult a (inv_pos z Hz))) (plus z (mult a (inv_pos z Hz)))
                 (req_trans (mult nsq_two nsq_half) (mult nsq_half nsq_two) one
                            (mult_comm nsq_two nsq_half)
                            (req_trans (mult nsq_half nsq_two)
                                       (mult nsq_two nsq_half) one
                                       (mult_comm nsq_half nsq_two)
                                       nsq_half_two_correct))
                 (req_refl (plus z (mult a (inv_pos z Hz))))).
      + exact (req_trans (mult one (plus z (mult a (inv_pos z Hz))))
                         (mult (plus z (mult a (inv_pos z Hz))) one)
                         (plus z (mult a (inv_pos z Hz)))
                         (mult_comm one (plus z (mult a (inv_pos z Hz))))
                         (mult_one (plus z (mult a (inv_pos z Hz))))). }
  (* second step: z + z == z + a/z gives z == a/z by left cancellation
     ([req_plus_cancel_l]) *)
  assert (Hzu : real_eq z (mult a (inv_pos z Hz))).
  { apply (req_plus_cancel_l z z (mult a (inv_pos z Hz))).
    apply (req_trans (plus z z) (mult nsq_two z)
                     (plus z (mult a (inv_pos z Hz)))).
    - exact (req_sym (mult nsq_two z) (plus z z) (req_two_mult z)).
    - exact H2. }
  (* third step: z*z == z*(a/z) == a*(z*(1/z)) == a*one == a *)
  apply (req_trans (mult z z) (mult z (mult a (inv_pos z Hz))) a).
  - exact (req_mult_compat z z z (mult a (inv_pos z Hz))
             (req_refl z) Hzu).
  - apply (req_trans (mult z (mult a (inv_pos z Hz)))
                     (mult a (mult z (inv_pos z Hz)))
                     a).
    + apply (req_trans (mult z (mult a (inv_pos z Hz)))
                       (mult (mult z a) (inv_pos z Hz))
                       (mult a (mult z (inv_pos z Hz)))).
      * exact (mult_assoc z a (inv_pos z Hz)).
      * apply (req_trans (mult (mult z a) (inv_pos z Hz))
                         (mult (mult a z) (inv_pos z Hz))
                         (mult a (mult z (inv_pos z Hz)))).
        -- exact (req_mult_compat (mult z a) (mult a z) (inv_pos z Hz) (inv_pos z Hz)
                    (mult_comm z a) (req_refl (inv_pos z Hz))).
        -- exact (req_sym (mult a (mult z (inv_pos z Hz)))
                          (mult (mult a z) (inv_pos z Hz))
                          (mult_assoc a z (inv_pos z Hz))).
    + apply (req_trans (mult a (mult z (inv_pos z Hz)))
                       (mult a one)
                       a).
      * exact (req_mult_compat a a (mult z (inv_pos z Hz)) one
                 (req_refl a) (inv_pos_correct z Hz)).
      * exact (req_trans (mult a one) (mult one a) a
                         (mult_comm a one)
                         (req_trans (mult one a) (mult a one) a
                                    (mult_comm one a) (mult_one a))).
Qed.

(* ============================================================ *)
(* Part 2 skeleton and open point -- the convergence certificate  *)
(*   (incomplete; the missing ingredient is stated explicitly     *)
(*   below).                                                     *)
(*                                                              *)
(* Target statement (interface-native Bishop per-eps form,        *)
(*   congruent with the premise of [cauchy_complete] so that a    *)
(*   later completion feeds the completeness field directly):     *)
(*   Lemma sqrtf_newton_cauchy : forall (a : R) (Ha : lt zero a)   *)
(*     (x : R) (Hx : lt zero x) (eps : R), lt zero eps ->          *)
(*     sigT (fun N : nat => forall m n : nat, NatLe N m ->         *)
(*       NatLe N n -> lt (metric (sqrtf_newton a Ha x Hx m)        *)
(*                                (sqrtf_newton a Ha x Hx n)) eps).*)
(*                                                              *)
(* Proof plan (three steps):                                     *)
(*  (1) residual square chain: the Section 5 identity gives       *)
(*      z_{n+1} * z_{n+1} == a + t_n * t_n with                   *)
(*      t_n := s(z_n) := half * (z_n - a/z_n); moreover           *)
(*      t_{n+1} == t_n * t_n / (2 * z_{n+1}) (the ratio form of    *)
(*      the same polarization decomposition).                    *)
(*  (2) contraction bound: z_n >= m > 0 (the positivity invariant *)
(*      plus a lower bound) gives |t_{n+1}| <= |t_n|^2/(2m), hence *)
(*      geometric convergence and per-eps Cauchy convergence.    *)
(*  (3) limit promotion: the Cauchy property plus                 *)
(*      [cauchy_complete] yields a limit l, and                   *)
(*      [sqrtf_fixed_point_correct] (Section 7) transports along  *)
(*      [req] compatibility to l*l == a -- the functional square  *)
(*      root closes.                                             *)
(*                                                              *)
(* Open point: the ingredient of step (2), the nonnegativity of   *)
(*   the residual and the order preservation of the square, is    *)
(*   not constructible at this interface layer:                   *)
(*   le zero (mult t t) (nonnegativity of a square) is not an     *)
(*   interface theorem: the same-position precedent [square_nonneg] *)
(*   of the GRPO library keeps an explicit premise position       *)
(*   (entry 6 of the UpReqDist header notes), the interface has   *)
(*   no le/Or decomposition field and no trichotomy for [lt]      *)
(*   (the classical axioms were removed, as that module records   *)
(*   at lines 173-176).  Two resolution routes remain for later   *)
(*   work:                                                       *)
(*   (a) the premise route: state the section premise             *)
(*       [nsq_square_nonneg] (le zero (mult t t)); the Real       *)
(*       instance can discharge it;                              *)
(*   (b) the concrete-layer route: the [real_abs] family          *)
(*       (pointwise Qabs plus Cauchy) proves |x|*|x| == x*x       *)
(*       and abs >= 0 at the concrete layer, discharged by        *)
(*       specialization at instantiation.                        *)
(* Part 2 assets already in place in this module:                 *)
(*   [sqrtf_fixed_point_correct] (the limit correctness piece,    *)
(*   complete) + the Section 5 residual square identity (the      *)
(*   algebraic core of the contraction chain, complete)           *)
(*   + the Section 8 convergence chain pieces (uses of residual   *)
(*   nonnegativity, square lower bound, monotonicity, uniform     *)
(*   lower bound, contraction ratio identity -- in explicit       *)
(*   premise form; see the Section 8 note).                       *)
(* ============================================================ *)

(* ============================================================ *)
(* Section 8. the part-2 convergence chain (assembled in stages): *)
(*   the explicit premise of route (a) plus the contraction ratio *)
(*   identity.                                                   *)
(*                                                              *)
(* Pieces:                                                        *)
(*  - [nsq_square_nonneg]: the explicit section premise (route    *)
(*    (a); same-position precedent [square_nonneg] of the GRPO    *)
(*    library, entry 6 of the UpReqDist header notes); stated at  *)
(*    section level and generalized into an explicit premise of   *)
(*    the lemma; [Print Assumptions] stays Closed with zero axiom *)
(*    face;                                                      *)
(*  - [sqrtf_sq_ge_a]: uses of residual nonnegativity (premise +  *)
(*    the Section 5 identity give g(y)^2 >= a);                  *)

(*  - [sqrtf_iterate_sq_ge]: the square lower bound z_{S n}^2 >= a *)
(*    for every iterate;                                          *)
(*  - [sqrtf_inv_le_self]: the square lower bound becomes the     *)
(*    reciprocal upper bound a*(1/z) <= z;                        *)
(*  - [sqrtf_step_contract]: one-step contraction in [le],        *)
(*    g(y) <= y;                                                  *)
(*  - [sqrtf_iterate_mono_step] / _from1: the iterates decrease   *)
(*    monotonically from z_1 on;                                  *)
(*  - [sqrtf_iterate_lower]: the uniform lower bound              *)
(*    m0 := a*(1/z_1) <= z_n for all n >= 1;                      *)
(*  - [nsq_two_slack] + [nsq_slack_contraction]: the contraction  *)
(*    ratio identity 2*g(y)*s(g(y)) == s(y)*s(y) (the ratio form  *)
(*    of plan step (1)).                                          *)
(*                                                              *)
(* Refinement of the premise analysis: the plain form             *)
(*   le zero (mult t t) cannot be discharged at the Real layer    *)
(*   either -- the le of RealEnhancedReal is the encoding         *)
(*   Or (real_lt) (real_eq) (instance section), and both branches *)
(*   fail for t_n^2 without a uniform positive tail (a t := 1/n   *)
(*   style sequence is a counterexample); the abs family of the   *)
(*   interface does not suffice either (there is no [req] bridge  *)
(*   between |t|*|t| and t*t: the sign is undecidable and the     *)
(*   interface has no decomposition field).  This premise is      *)
(*   therefore an irreducible explicit premise of the convergence *)
(*   chain; the viable remainder of route (b) is a pointwise      *)
(*   rebuild at the concrete layer (same position as              *)
(*   [Qsquare_nonneg] at the Q layer; [real_square_nonneg_eps]    *)
(*   is a per-eps Bishop statement of the same family), left for  *)
(*   later work.                                                  *)
(*                                                              *)
(* Explicit premises of the tail stage (for the exact remainder): *)
(*   the full Cauchy certificate assembles from three parts --    *)
(*   the contraction ratio identity (complete in this section)    *)
(*   + the statement "there is K with |s(z_K)| <= m0" (the        *)
(*   rank-taking step, which needs an Archimedean same-position   *)
(*   premise) + a per-eps upper bound for the geometric tail sum  *)
(*   (triangle iteration on the metric tail sum, via a            *)
(*   [metric_abs] bridge premise); the remaining stages are left  *)
(*   for later work.                                              *)
(* ============================================================ *)

Hypothesis nsq_square_nonneg : forall t : R, real_le zero (mult t t).

(* uses of residual nonnegativity: s(y)^2 >= 0 (the section premise)
   combined with the Section 5 identity gives g(y)^2 >= a.
   Assembled from three transports: [le_plus_compat] injects the
   premise on the a side, [req] compatibility carries
   plus zero a ~ a and g*g ~ s^2 + a. *)
Lemma sqrtf_sq_ge_a : forall (a y : R) (Ha : real_lt zero a) (Hy : real_lt zero y),
  real_le a (mult (sqrtf_step a y Ha Hy) (sqrtf_step a y Ha Hy)).
Proof.
  intros a y Ha Hy.
  destruct (sqrtf_step_residual a y Ha Hy) as [s Hs].
  exact (req_le_compat (plus zero a) a
                       (plus (mult s s) a)
                       (mult (sqrtf_step a y Ha Hy) (sqrtf_step a y Ha Hy))
                       (req_plus_zero_l a)
                       (req_sym (mult (sqrtf_step a y Ha Hy) (sqrtf_step a y Ha Hy))
                                (plus (mult s s) a)
                                Hs)
                       (le_plus_compat zero (mult s s) a a
                          (nsq_square_nonneg s) (le_refl a))).
Qed.

(* square lower bound for every iterate: z_{S n}^2 >= a (transport
   along the succ unfolding by [req] + the previous lemma) *)
Lemma sqrtf_iterate_sq_ge : forall (a : R) (Ha : real_lt zero a) (x : R) (Hx : real_lt zero x)
                                  (n : nat),
  real_le a (mult (sqrtf_newton a Ha x Hx (Datatypes.S n))
             (sqrtf_newton a Ha x Hx (Datatypes.S n))).
Proof.
  intros a Ha x Hx n.
  apply (req_le_compat a a
           (mult (sqrtf_step a (sqrtf_newton a Ha x Hx n) Ha
                            (sqrtf_newton_pos a Ha x Hx n))
                 (sqrtf_step a (sqrtf_newton a Ha x Hx n) Ha
                             (sqrtf_newton_pos a Ha x Hx n)))
           (mult (sqrtf_newton a Ha x Hx (Datatypes.S n))
                 (sqrtf_newton a Ha x Hx (Datatypes.S n)))
           (req_refl a)
           (req_mult_compat (sqrtf_step a (sqrtf_newton a Ha x Hx n) Ha
                                          (sqrtf_newton_pos a Ha x Hx n))
                            (sqrtf_newton a Ha x Hx (Datatypes.S n))
                            (sqrtf_step a (sqrtf_newton a Ha x Hx n) Ha
                                         (sqrtf_newton_pos a Ha x Hx n))
                            (sqrtf_newton a Ha x Hx (Datatypes.S n))
                            (req_sym (sqrtf_newton a Ha x Hx (Datatypes.S n)) (sqrtf_step a (sqrtf_newton a Ha x Hx n) Ha (sqrtf_newton_pos a Ha x Hx n)) (sqrtf_newton_succ a Ha x Hx n))
                            (req_sym (sqrtf_newton a Ha x Hx (Datatypes.S n)) (sqrtf_step a (sqrtf_newton a Ha x Hx n) Ha (sqrtf_newton_pos a Ha x Hx n)) (sqrtf_newton_succ a Ha x Hx n)))).
  exact (sqrtf_sq_ge_a a (sqrtf_newton a Ha x Hx n) Ha
           (sqrtf_newton_pos a Ha x Hx n)).
Qed.

(* the square lower bound becomes a reciprocal upper bound:
   a <= z*z gives a*(1/z) <= z.  Multiply by 1/z > 0 on the left and
   finish with [inv_pos_correct]: 1/z*(z*z) ~ (1/z*z)*z ~ 1*z ~ z. *)
Lemma sqrtf_inv_le_self : forall (a z : R) (Ha : real_lt zero a) (Hz : real_lt zero z),
  real_le a (mult z z) -> real_le (mult a (inv_pos z Hz)) z.
Proof.
  intros a z Ha Hz H.
  apply (le_trans (mult a (inv_pos z Hz))
                  (mult (mult z z) (inv_pos z Hz))
                  z).
  - exact (le_mult_compat a (mult z z) (inv_pos z Hz) (inv_pos_pos z Hz) H).
  - exact (req_le_compat (mult (mult z z) (inv_pos z Hz))
                         (mult (mult z z) (inv_pos z Hz))
                         (mult (mult z z) (inv_pos z Hz))
                         z
           (req_refl (mult (mult z z) (inv_pos z Hz)))
           (req_trans (mult (mult z z) (inv_pos z Hz))
                      (mult z (mult z (inv_pos z Hz)))
                      z
                      (req_sym (mult z (mult z (inv_pos z Hz)))
                               (mult (mult z z) (inv_pos z Hz))
                               (mult_assoc z z (inv_pos z Hz)))
                      (req_trans (mult z (mult z (inv_pos z Hz)))
                                 (mult z one)
                                 z
                                 (req_mult_compat z z (mult z (inv_pos z Hz)) one
                                    (req_refl z)
                                    (inv_pos_correct z Hz))
                                 (mult_one z)))
           (le_refl (mult (mult z z) (inv_pos z Hz)))).
Qed.

(* one-step contraction in [le]: a <= y*y gives g(y) <= y.
   Since g(y) = half*(y + a/y) <= half*(y + y) == y, the last step is
   [nsq_tail]. *)
Lemma sqrtf_step_contract : forall (a y : R) (Ha : real_lt zero a) (Hy : real_lt zero y),
  real_le a (mult y y) -> real_le (sqrtf_step a y Ha Hy) y.
Proof.
  intros a y Ha Hy H.
  apply (le_trans (sqrtf_step a y Ha Hy)
                  (mult nsq_half (plus y (mult a (inv_pos y Hy))))
                  y).
  - exact (le_refl (sqrtf_step a y Ha Hy)).
  - apply (le_trans (mult nsq_half (plus y (mult a (inv_pos y Hy))))
                    (mult nsq_half (plus y y))
                    y).
    + exact (req_le_compat (mult (plus y (mult a (inv_pos y Hy))) nsq_half)
                           (mult nsq_half (plus y (mult a (inv_pos y Hy))))
                           (mult (plus y y) nsq_half)
                           (mult nsq_half (plus y y))
             (mult_comm (plus y (mult a (inv_pos y Hy))) nsq_half)
             (mult_comm (plus y y) nsq_half)
             (le_mult_compat (plus y (mult a (inv_pos y Hy))) (plus y y) nsq_half
                nsq_half_pos
                (le_plus_compat y y (mult a (inv_pos y Hy)) y
                   (le_refl y) (sqrtf_inv_le_self a y Ha Hy H)))).
    + exact (req_le_compat (mult nsq_half (plus y y))
                           (mult nsq_half (plus y y))
                           (mult nsq_half (plus y y))
                           y
               (req_refl (mult nsq_half (plus y y)))
               (nsq_tail y)
               (le_refl (mult nsq_half (plus y y)))).
Qed.

(* monotonicity of the iterates, single step: z_{S (S n)} <= z_{S n}
   (uses z_{S n}^2 >= a) *)
Lemma sqrtf_iterate_mono_step : forall (a : R) (Ha : real_lt zero a) (x : R) (Hx : real_lt zero x)
                                       (n : nat),
  real_le (sqrtf_newton a Ha x Hx (Datatypes.S (Datatypes.S n)))
     (sqrtf_newton a Ha x Hx (Datatypes.S n)).
Proof.
  intros a Ha x Hx n.
  apply (req_le_compat (sqrtf_step a (sqrtf_newton a Ha x Hx (Datatypes.S n)) Ha
                                    (sqrtf_newton_pos a Ha x Hx (Datatypes.S n)))
                       (sqrtf_newton a Ha x Hx (Datatypes.S (Datatypes.S n)))
                       (sqrtf_newton a Ha x Hx (Datatypes.S n))
                       (sqrtf_newton a Ha x Hx (Datatypes.S n))
           (req_sym (sqrtf_newton a Ha x Hx (Datatypes.S (Datatypes.S n)))
                    (sqrtf_step a (sqrtf_newton a Ha x Hx (Datatypes.S n)) Ha
                                 (sqrtf_newton_pos a Ha x Hx (Datatypes.S n)))
                    (sqrtf_newton_succ a Ha x Hx (Datatypes.S n)))
           (req_refl (sqrtf_newton a Ha x Hx (Datatypes.S n)))).
  exact (sqrtf_step_contract a (sqrtf_newton a Ha x Hx (Datatypes.S n)) Ha
           (sqrtf_newton_pos a Ha x Hx (Datatypes.S n))
           (sqrtf_iterate_sq_ge a Ha x Hx n)).
Qed.

(* monotonicity of the iterates, uniform from z_1 on: z_{S n} <= z_1
   (induction plus the single-step lemma) *)
Lemma sqrtf_iterate_mono_from1 : forall (a : R) (Ha : real_lt zero a) (x : R) (Hx : real_lt zero x)
                                        (n : nat),
  real_le (sqrtf_newton a Ha x Hx (Datatypes.S n)) (sqrtf_newton a Ha x Hx 1).
Proof.
  intros a Ha x Hx n. induction n as [| n IH].
  - exact (le_refl (sqrtf_newton a Ha x Hx 1)).
  - apply (le_trans (sqrtf_newton a Ha x Hx (Datatypes.S (Datatypes.S n)))
                    (sqrtf_newton a Ha x Hx (Datatypes.S n))
                    (sqrtf_newton a Ha x Hx 1)).
    + exact (sqrtf_iterate_mono_step a Ha x Hx n).
    + exact IH.
Qed.

(* uniform lower bound: m0 := a*(1/z_1) <= z_n for every n >= 1.
   From z_n <= z_1 the reciprocal reverses the order, 1/z_1 <= 1/z_n,
   so a/z_1 <= a/z_n <= z_n; the last step is the reciprocal form of
   the square lower bound. *)
Lemma sqrtf_iterate_lower : forall (a : R) (Ha : real_lt zero a) (x : R) (Hx : real_lt zero x)
                                   (n : nat),
  real_le (mult a (inv_pos (sqrtf_newton a Ha x Hx 1)
                      (sqrtf_newton_pos a Ha x Hx 1)))
     (sqrtf_newton a Ha x Hx (Datatypes.S n)).
Proof.
  intros a Ha x Hx n.
  apply (le_trans (mult a (inv_pos (sqrtf_newton a Ha x Hx 1)
                                   (sqrtf_newton_pos a Ha x Hx 1)))
                  (mult a (inv_pos (sqrtf_newton a Ha x Hx (Datatypes.S n))
                                   (sqrtf_newton_pos a Ha x Hx (Datatypes.S n))))
                  (sqrtf_newton a Ha x Hx (Datatypes.S n))).
  - apply (req_le_compat
             (mult (inv_pos (sqrtf_newton a Ha x Hx 1) (sqrtf_newton_pos a Ha x Hx 1)) a)
             (mult a (inv_pos (sqrtf_newton a Ha x Hx 1) (sqrtf_newton_pos a Ha x Hx 1)))
             (mult (inv_pos (sqrtf_newton a Ha x Hx (Datatypes.S n))
                            (sqrtf_newton_pos a Ha x Hx (Datatypes.S n))) a)
             (mult a (inv_pos (sqrtf_newton a Ha x Hx (Datatypes.S n))
                              (sqrtf_newton_pos a Ha x Hx (Datatypes.S n))))
             (mult_comm (inv_pos (sqrtf_newton a Ha x Hx 1)
                                 (sqrtf_newton_pos a Ha x Hx 1)) a)
             (mult_comm (inv_pos (sqrtf_newton a Ha x Hx (Datatypes.S n))
                                 (sqrtf_newton_pos a Ha x Hx (Datatypes.S n))) a)).
    exact (le_mult_compat
             (inv_pos (sqrtf_newton a Ha x Hx 1) (sqrtf_newton_pos a Ha x Hx 1))
             (inv_pos (sqrtf_newton a Ha x Hx (Datatypes.S n))
                      (sqrtf_newton_pos a Ha x Hx (Datatypes.S n)))
             a Ha
             (inv_pos_le_compat (sqrtf_newton a Ha x Hx (Datatypes.S n))
                                (sqrtf_newton a Ha x Hx 1)
                                (sqrtf_newton_pos a Ha x Hx (Datatypes.S n))
                                (sqrtf_newton_pos a Ha x Hx 1)
                                (sqrtf_iterate_mono_from1 a Ha x Hx n))).
  - exact (sqrtf_inv_le_self a (sqrtf_newton a Ha x Hx (Datatypes.S n)) Ha
             (sqrtf_newton_pos a Ha x Hx (Datatypes.S n))
             (sqrtf_iterate_sq_ge a Ha x Hx n)).
Qed.

(* tail lemma: nsq_two * s(u) == u - a/u, a direct consequence of
   two * half == one in slack form: 2*(half*w) ~ (2*half)*w ~ 1*w ~ w;
   delta on [sqrtf_slack] exposes the definitional shape. *)
Lemma nsq_two_slack : forall (a u : R) (Ha : real_lt zero a) (Hu : real_lt zero u),
  real_eq (mult nsq_two (sqrtf_slack a u Ha Hu))
      (plus u (opp (mult a (inv_pos u Hu)))).
Proof.
  intros a u Ha Hu.
  apply (req_trans (mult nsq_two (sqrtf_slack a u Ha Hu))
                   (mult (mult nsq_two nsq_half)
                         (plus u (opp (mult a (inv_pos u Hu)))))
                   (plus u (opp (mult a (inv_pos u Hu))))).
  - exact (mult_assoc nsq_two nsq_half (plus u (opp (mult a (inv_pos u Hu))))).
  - apply (req_trans (mult (mult nsq_two nsq_half)
                           (plus u (opp (mult a (inv_pos u Hu)))))
                     (mult one (plus u (opp (mult a (inv_pos u Hu)))))
                     (plus u (opp (mult a (inv_pos u Hu))))).
    + exact (req_mult_compat (mult nsq_two nsq_half) one
               (plus u (opp (mult a (inv_pos u Hu))))
               (plus u (opp (mult a (inv_pos u Hu))))
               (req_trans (mult nsq_two nsq_half) (mult nsq_half nsq_two) one
                          (mult_comm nsq_two nsq_half)
                          (req_trans (mult nsq_half nsq_two)
                                     (mult nsq_two nsq_half)
                                     one
                                     (mult_comm nsq_half nsq_two)
                                     nsq_half_two_correct))
               (req_refl (plus u (opp (mult a (inv_pos u Hu)))))).
    + exact (req_mult_one_l (plus u (opp (mult a (inv_pos u Hu))))).
Qed.

(* the Section 5 identity stated directly without the [sigT] wrapper
   (the witness, the [sqrtf_slack] term, is inlined; the lemma serves
   the convergence chain, and its [req] chain mirrors that of the
   Section 5 statement) *)
Lemma nsq_step_residual_req : forall (a y : R) (Ha : real_lt zero a) (Hy : real_lt zero y),
  real_eq (mult (sqrtf_step a y Ha Hy) (sqrtf_step a y Ha Hy))
      (plus (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy)) a).
Proof.
  intros a y Ha Hy.
  apply (req_trans (mult (sqrtf_step a y Ha Hy) (sqrtf_step a y Ha Hy))
                   (plus (mult (req_minus (sqrtf_step a y Ha Hy) (sqrtf_slack a y Ha Hy))
                               (plus (sqrtf_step a y Ha Hy) (sqrtf_slack a y Ha Hy)))
                         (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy)))
                   (plus (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy)) a)).
  - exact (nsq_polarization (sqrtf_step a y Ha Hy) (sqrtf_slack a y Ha Hy)).
  - apply (req_trans
             (plus (mult (req_minus (sqrtf_step a y Ha Hy) (sqrtf_slack a y Ha Hy))
                         (plus (sqrtf_step a y Ha Hy) (sqrtf_slack a y Ha Hy)))
                   (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy)))
             (plus (mult (mult a (inv_pos y Hy)) y)
                   (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy)))
             (plus (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy)) a)).
    + exact (req_plus_compat
               (mult (req_minus (sqrtf_step a y Ha Hy) (sqrtf_slack a y Ha Hy))
                     (plus (sqrtf_step a y Ha Hy) (sqrtf_slack a y Ha Hy)))
               (mult (mult a (inv_pos y Hy)) y)
               (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy))
               (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy))
               (req_mult_compat
                  (req_minus (sqrtf_step a y Ha Hy) (sqrtf_slack a y Ha Hy))
                  (mult a (inv_pos y Hy))
                  (plus (sqrtf_step a y Ha Hy) (sqrtf_slack a y Ha Hy))
                  y
                  (nsq_step_minus_slack a y Ha Hy)
                  (nsq_step_plus_slack a y Ha Hy))
               (req_refl (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy)))).
    + apply (req_trans
               (plus (mult (mult a (inv_pos y Hy)) y)
                     (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy)))
               (plus a (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy)))
               (plus (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy)) a)).
      * exact (req_plus_compat (mult (mult a (inv_pos y Hy)) y) a
                 (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy))
                 (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy))
                 (nsq_u_mult_y a y Ha Hy)
                 (req_refl (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy)))).
      * exact (req_sym (plus (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy)) a)
                       (plus a (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy)))
                       (plus_comm (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy)) a)).
Qed.

(* the contraction ratio identity (core piece of the convergence chain,
   the ratio form of plan step (1)):
   2*g(y)*s(g(y)) == s(y)*s(y).
   Algebra: 2*u*s(u) == u*(u - a/u) == u*u + opp a (the cross term
   u*(a/u) == a by a reordered [nsq_u_mult_y]), hence
   2*u*s(u) + a == u*u == s(y)^2 + a by the Section 5 identity, and the
   added a cancels on the left by [req_plus_cancel_l]. *)
Lemma nsq_slack_contraction : forall (a y : R) (Ha : real_lt zero a) (Hy : real_lt zero y),
  real_eq (mult (mult nsq_two (sqrtf_step a y Ha Hy))
            (sqrtf_slack a (sqrtf_step a y Ha Hy) Ha (sqrtf_step_pos a y Ha Hy)))
      (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy)).
Proof.
  intros a y Ha Hy.
  pose proof (nsq_step_residual_req a y Ha Hy) as Hres.
  set (Hu := sqrtf_step_pos a y Ha Hy) in *.
  (* branch A: 2*u*s_u == u*u + opp a *)
  assert (HA : real_eq (mult (mult nsq_two (sqrtf_step a y Ha Hy))
                         (sqrtf_slack a (sqrtf_step a y Ha Hy) Ha Hu))
                   (plus (mult (sqrtf_step a y Ha Hy) (sqrtf_step a y Ha Hy))
                         (opp a))).
  { apply (req_trans
             (mult (mult nsq_two (sqrtf_step a y Ha Hy))
                   (sqrtf_slack a (sqrtf_step a y Ha Hy) Ha Hu))
             (mult (sqrtf_step a y Ha Hy)
                   (plus (sqrtf_step a y Ha Hy)
                         (opp (mult a (inv_pos (sqrtf_step a y Ha Hy) Hu)))))
             (plus (mult (sqrtf_step a y Ha Hy) (sqrtf_step a y Ha Hy))
                   (opp a))).
    - apply (req_trans
               (mult (mult nsq_two (sqrtf_step a y Ha Hy))
                     (sqrtf_slack a (sqrtf_step a y Ha Hy) Ha Hu))
               (mult (sqrtf_step a y Ha Hy)
                     (mult nsq_two (sqrtf_slack a (sqrtf_step a y Ha Hy) Ha Hu)))
               (mult (sqrtf_step a y Ha Hy)
                     (plus (sqrtf_step a y Ha Hy)
                           (opp (mult a (inv_pos (sqrtf_step a y Ha Hy) Hu)))))).
      + apply (req_trans
                 (mult (mult nsq_two (sqrtf_step a y Ha Hy))
                       (sqrtf_slack a (sqrtf_step a y Ha Hy) Ha Hu))
                 (mult (mult (sqrtf_step a y Ha Hy) nsq_two)
                       (sqrtf_slack a (sqrtf_step a y Ha Hy) Ha Hu))
                 (mult (sqrtf_step a y Ha Hy)
                       (mult nsq_two (sqrtf_slack a (sqrtf_step a y Ha Hy) Ha Hu)))).
        * exact (req_mult_compat (mult nsq_two (sqrtf_step a y Ha Hy))
                    (mult (sqrtf_step a y Ha Hy) nsq_two)
                    (sqrtf_slack a (sqrtf_step a y Ha Hy) Ha Hu)
                    (sqrtf_slack a (sqrtf_step a y Ha Hy) Ha Hu)
                    (mult_comm nsq_two (sqrtf_step a y Ha Hy))
                    (req_refl (sqrtf_slack a (sqrtf_step a y Ha Hy) Ha Hu))).
        * exact (req_sym (mult (sqrtf_step a y Ha Hy)
                               (mult nsq_two (sqrtf_slack a (sqrtf_step a y Ha Hy) Ha Hu)))
                         (mult (mult (sqrtf_step a y Ha Hy) nsq_two)
                               (sqrtf_slack a (sqrtf_step a y Ha Hy) Ha Hu))
                         (mult_assoc (sqrtf_step a y Ha Hy) nsq_two
                                     (sqrtf_slack a (sqrtf_step a y Ha Hy) Ha Hu))).
      + exact (req_mult_compat (sqrtf_step a y Ha Hy) (sqrtf_step a y Ha Hy)
                 (mult nsq_two (sqrtf_slack a (sqrtf_step a y Ha Hy) Ha Hu))
                 (plus (sqrtf_step a y Ha Hy)
                       (opp (mult a (inv_pos (sqrtf_step a y Ha Hy) Hu))))
                 (req_refl (sqrtf_step a y Ha Hy))
                 (nsq_two_slack a (sqrtf_step a y Ha Hy) Ha Hu)).
    - apply (req_trans
               (mult (sqrtf_step a y Ha Hy)
                     (plus (sqrtf_step a y Ha Hy)
                           (opp (mult a (inv_pos (sqrtf_step a y Ha Hy) Hu)))))
               (plus (mult (sqrtf_step a y Ha Hy) (sqrtf_step a y Ha Hy))
                     (mult (sqrtf_step a y Ha Hy)
                           (opp (mult a (inv_pos (sqrtf_step a y Ha Hy) Hu)))))
               (plus (mult (sqrtf_step a y Ha Hy) (sqrtf_step a y Ha Hy))
                     (opp a))).
      + exact (distrib (sqrtf_step a y Ha Hy) (sqrtf_step a y Ha Hy)
                       (opp (mult a (inv_pos (sqrtf_step a y Ha Hy) Hu)))).
      + exact (req_plus_compat (mult (sqrtf_step a y Ha Hy) (sqrtf_step a y Ha Hy))
                 (mult (sqrtf_step a y Ha Hy) (sqrtf_step a y Ha Hy))
                 (mult (sqrtf_step a y Ha Hy)
                       (opp (mult a (inv_pos (sqrtf_step a y Ha Hy) Hu))))
                 (opp a)
                 (req_refl (mult (sqrtf_step a y Ha Hy) (sqrtf_step a y Ha Hy)))
                 (req_trans (mult (sqrtf_step a y Ha Hy)
                                  (opp (mult a (inv_pos (sqrtf_step a y Ha Hy) Hu))))
                            (opp (mult (sqrtf_step a y Ha Hy)
                                       (mult a (inv_pos (sqrtf_step a y Ha Hy) Hu))))
                            (opp a)
                            (req_opp_mult_l (sqrtf_step a y Ha Hy)
                                            (mult a (inv_pos (sqrtf_step a y Ha Hy) Hu)))
                            (req_opp_compat (mult (sqrtf_step a y Ha Hy)
                                                  (mult a (inv_pos (sqrtf_step a y Ha Hy) Hu)))
                                            a
                                            (req_trans (mult (sqrtf_step a y Ha Hy)
                                                             (mult a (inv_pos (sqrtf_step a y Ha Hy) Hu)))
                                                       (mult (mult a (inv_pos (sqrtf_step a y Ha Hy) Hu))
                                                             (sqrtf_step a y Ha Hy))
                                                       a
                                                       (mult_comm (sqrtf_step a y Ha Hy)
                                                                  (mult a (inv_pos (sqrtf_step a y Ha Hy) Hu)))
                                                       (nsq_u_mult_y a (sqrtf_step a y Ha Hy) Ha Hu))))) . }
  (* confluence: a + 2us == a + u*u == a + s(y)^2; the left a cancels
     by [req_plus_cancel_l] *)
  apply (req_plus_cancel_l a
           (mult (mult nsq_two (sqrtf_step a y Ha Hy))
                 (sqrtf_slack a (sqrtf_step a y Ha Hy) Ha Hu))
           (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy))).
  apply (req_trans (plus a (mult (mult nsq_two (sqrtf_step a y Ha Hy))
                                 (sqrtf_slack a (sqrtf_step a y Ha Hy) Ha Hu)))
                   (plus (mult (mult nsq_two (sqrtf_step a y Ha Hy))
                               (sqrtf_slack a (sqrtf_step a y Ha Hy) Ha Hu)) a)
                   (plus a (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy)))).
  - exact (plus_comm a (mult (mult nsq_two (sqrtf_step a y Ha Hy))
                             (sqrtf_slack a (sqrtf_step a y Ha Hy) Ha Hu))).
  - apply (req_trans (plus (mult (mult nsq_two (sqrtf_step a y Ha Hy))
                                 (sqrtf_slack a (sqrtf_step a y Ha Hy) Ha Hu)) a)
                     (plus (plus (mult (sqrtf_step a y Ha Hy) (sqrtf_step a y Ha Hy)) (opp a)) a)
                     (plus a (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy)))).
    + exact (req_plus_compat (mult (mult nsq_two (sqrtf_step a y Ha Hy))
                                   (sqrtf_slack a (sqrtf_step a y Ha Hy) Ha Hu))
                             (plus (mult (sqrtf_step a y Ha Hy) (sqrtf_step a y Ha Hy)) (opp a))
                             a a HA (req_refl a)).
    + apply (req_trans (plus (plus (mult (sqrtf_step a y Ha Hy) (sqrtf_step a y Ha Hy)) (opp a)) a)
                       (mult (sqrtf_step a y Ha Hy) (sqrtf_step a y Ha Hy))
                       (plus a (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy)))).
      * apply (req_trans (plus (plus (mult (sqrtf_step a y Ha Hy) (sqrtf_step a y Ha Hy)) (opp a)) a)
                         (plus (mult (sqrtf_step a y Ha Hy) (sqrtf_step a y Ha Hy)) (plus (opp a) a))
                         (mult (sqrtf_step a y Ha Hy) (sqrtf_step a y Ha Hy))).
        -- exact (req_sym (plus (mult (sqrtf_step a y Ha Hy) (sqrtf_step a y Ha Hy))
                                (plus (opp a) a))
                          (plus (plus (mult (sqrtf_step a y Ha Hy) (sqrtf_step a y Ha Hy)) (opp a)) a)
                          (plus_assoc (mult (sqrtf_step a y Ha Hy) (sqrtf_step a y Ha Hy))
                                      (opp a) a)).
        -- apply (req_trans (plus (mult (sqrtf_step a y Ha Hy) (sqrtf_step a y Ha Hy))
                                  (plus (opp a) a))
                            (plus (mult (sqrtf_step a y Ha Hy) (sqrtf_step a y Ha Hy)) zero)
                            (mult (sqrtf_step a y Ha Hy) (sqrtf_step a y Ha Hy))).
           ++ exact (req_plus_compat (mult (sqrtf_step a y Ha Hy) (sqrtf_step a y Ha Hy))
                                        (mult (sqrtf_step a y Ha Hy) (sqrtf_step a y Ha Hy))
                                        (plus (opp a) a) zero
                                        (req_refl (mult (sqrtf_step a y Ha Hy) (sqrtf_step a y Ha Hy)))
                                        (req_plus_opp_l a)).
           ++ exact (plus_zero (mult (sqrtf_step a y Ha Hy) (sqrtf_step a y Ha Hy))).
      * apply (req_trans (mult (sqrtf_step a y Ha Hy) (sqrtf_step a y Ha Hy))
                         (plus (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy)) a)
                         (plus a (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy)))).
        -- exact Hres.
        -- exact (plus_comm (mult (sqrtf_slack a y Ha Hy) (sqrtf_slack a y Ha Hy)) a).
Qed.

End SqrtF.

(* closedness audit section (appended after the section body): each
    audited statement is declared individually, and [Closed under the
    global context] on every line is the expected verdict. *)
Print Assumptions nsq_two_pos.
Print Assumptions nsq_half_pos.
Print Assumptions nsq_half_two_correct.
Print Assumptions sqrtf_newton_zero.
Print Assumptions nsq_step_minus_slack.
Print Assumptions nsq_step_plus_slack.
Print Assumptions sqrtf_sqrt_self_init.
Print Assumptions sqrtf_iterate_sq_ge.
Print Assumptions sqrtf_inv_le_self.
Print Assumptions sqrtf_step_contract.
Print Assumptions sqrtf_iterate_mono_step.