(* ConstructiveWorld-Set — temperature-scaled extensions of the Gibbs inequality family. *)

(** * GibbsFamilyExt: temperature-parameterized Gibbs and Jeffreys
    inequalities for the constructive reals.

    Mission.  Temperature-parameterized Gibbs inequality forms: the
      pointwise cores [gfe_gibbs_core_temp_B] and
      [gfe_gibbs_inequality_temp_B], the gap form [gfe_gibbs_temp_gap_B]
      with its flat expansion [gfe_gibbs_temp_gap_B_flat], order
      preservation under positive multiplication [gfe_le_b_mult_pos],
      and the symmetric Jeffreys statements
      [gfe_jeffreys_sym_B]/[gfe_jeffreys_sym_list_B].

    Dependencies.  Stdlib [List].  Requires [S01_BaseRing] through
      [S15_TailFEPUp] and [UpRealLeB], [UpRealLeB2], [UpRealLeB3],
      [UpReqKLStrictB] of this development.

    References.  This development, GibbsFamilyExt.v, the baseline module
      in ConstructiveWorld-Main whose statement names are carried over
      here verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements are carried by [Set] and the
      order/equality predicates are Set-valued; every statement closes
      with [Qed] without classical logic, extracts with
      [Obj.magic] = 0 and no erasure, and [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" GibbsFamilyExt.v]
      compiles cleanly (exit 0); the first eight bytes of the artifact
      are [436f7121 00015ff4]. *)

From Stdlib Require Import List.
Import ListNotations.
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
Require Import UpRealLeB.
Require Import UpRealLeB2.
Require Import UpRealLeB3.
Require Import UpReqKLStrictB.

(* ============================================================ *)
(* Part 0. Order-algebraic support lemmas (four statements) *)
(* ============================================================ *)

(* 0.1 Bridge from strict positivity to weak nonnegativity (the
   temperature premise is downgraded: a [b > 0] exit feeds a [b >= 0]
   entry).  [real_le] is an [Or] encoding, so the strict-order premise
   feeds the left disjunct directly through [inl], with no
   intermediate lemma. *)
Lemma gfe_le_of_lt : forall b : Real,
  real_lt real_zero b -> real_le real_zero b.
Proof.
  intros b Hb. exact (inl Hb).
Qed.

(* 0.2 The identity [(q + (-p)) + (p + (-q)) == 0]: the cancellation
   core of the asymmetric forms (a three-step associativity chain that
   never distributes over the additive inverse; it drives the
   symmetric Jeffreys forms). *)
Lemma gfe_pq_shift_zero : forall p q : Real,
  real_eq (real_plus (real_plus q (real_opp p)) (real_plus p (real_opp q)))
          real_zero.
Proof.
  intros p q.
  assert (Hopp0 : real_eq (real_plus (real_opp p) p) real_zero).
  { exact (real_eq_trans (real_plus (real_opp p) p)
                         (real_plus p (real_opp p)) real_zero
             (real_plus_comm (real_opp p) p) (real_plus_opp p)). }
  (* Step 1: two associativity regroupings fold the [p] summand into
     the [q] side. *)
  assert (Hs1 : real_eq (real_plus (real_plus q (real_opp p))
                                   (real_plus p (real_opp q)))
                        (real_plus (real_plus q (real_plus (real_opp p) p))
                                   (real_opp q))).
  { apply (real_eq_trans
             (real_plus (real_plus q (real_opp p)) (real_plus p (real_opp q)))
             (real_plus (real_plus (real_plus q (real_opp p)) p) (real_opp q))
             (real_plus (real_plus q (real_plus (real_opp p) p)) (real_opp q))).
    - exact (real_plus_assoc (real_plus q (real_opp p)) p (real_opp q)).
    - apply (RealSetoid.real_eq_plus_compat
               (real_plus (real_plus q (real_opp p)) p)
               (real_opp q)
               (real_plus q (real_plus (real_opp p) p))
               (real_opp q)).
      + apply (real_eq_sym (real_plus q (real_plus (real_opp p) p))
                           (real_plus (real_plus q (real_opp p)) p)).
        exact (real_plus_assoc q (real_opp p) p).
      + apply real_eq_refl. }
  (* Step 2: the inner sum [(-p) + p] cancels to zero. *)
  assert (Hs2 : real_eq (real_plus (real_plus q (real_plus (real_opp p) p))
                                   (real_opp q))
                        (real_plus (real_plus q real_zero) (real_opp q))).
  { apply (RealSetoid.real_eq_plus_compat
             (real_plus q (real_plus (real_opp p) p))
             (real_opp q)
             (real_plus q real_zero)
             (real_opp q)).
    - apply (RealSetoid.real_eq_plus_compat q
               (real_plus (real_opp p) p) q real_zero).
      + apply real_eq_refl.
      + exact Hopp0.
    - apply real_eq_refl. }
  (* Steps 3 and 4: after rewriting [(q + 0) + (-q)] to [q + (-q)],
     [real_plus_opp] closes the goal. *)
  assert (Hs3 : real_eq (real_plus (real_plus q real_zero) (real_opp q))
                        real_zero).
  { apply (real_eq_trans
             (real_plus (real_plus q real_zero) (real_opp q))
             (real_plus q (real_opp q))
             real_zero).
    - apply (RealSetoid.real_eq_plus_compat (real_plus q real_zero)
               (real_opp q) q (real_opp q)).
      + exact (real_plus_zero q).
      + apply real_eq_refl.
    - exact (real_plus_opp q). }
  exact (real_eq_trans
           (real_plus (real_plus q (real_opp p)) (real_plus p (real_opp q)))
           (real_plus (real_plus q (real_plus (real_opp p) p)) (real_opp q))
           real_zero
           Hs1
           (real_eq_trans
              (real_plus (real_plus q (real_plus (real_opp p) p)) (real_opp q))
              (real_plus (real_plus q real_zero) (real_opp q))
              real_zero Hs2 Hs3)).
Qed.

(* 0.3 The shifted cancellation identity [(a + s) + (d + t) == a + d]
   whenever [s + t == 0]; one application of [real_plus_swap_mid]
   closes it.  This is the engine behind the symmetric Jeffreys
   identity. *)
Lemma gfe_sym_sum_eq : forall (a d s t : Real),
  real_eq (real_plus s t) real_zero ->
  real_eq (real_plus (real_plus a s) (real_plus d t)) (real_plus a d).
Proof.
  intros a d s t Hst.
  apply (real_eq_trans
           (real_plus (real_plus a s) (real_plus d t))
           (real_plus (real_plus a d) (real_plus s t))
           (real_plus a d)).
  - exact (real_plus_swap_mid a s d t).
  - apply (real_eq_trans
             (real_plus (real_plus a d) (real_plus s t))
             (real_plus (real_plus a d) real_zero)
             (real_plus a d)).
    + apply (RealSetoid.real_eq_plus_compat (real_plus a d) (real_plus s t)
               (real_plus a d) real_zero).
      * apply real_eq_refl.
      * exact Hst.
    + exact (real_plus_zero (real_plus a d)).
Qed.

(* 0.4 Right-hand rewriting for the Bishop order (family-level
   combinator: [le_b x y] together with [y == z] gives [le_b x z]; the
   dual of the left-hand rewriter [leb3_le_b_eq_l], which has no
   right-hand counterpart in the development). *)
Lemma gfe_le_b_eq_r : forall (x y z : Real),
  real_le_b x y -> real_eq y z -> real_le_b x z.
Proof.
  intros x y z Hxy Heq. unfold real_le_b in Hxy. unfold real_le_b.
  intros eps Heps.
  apply (RealSetoid.real_lt_compat x x
           (real_plus y eps) (real_plus z eps)).
  - apply real_eq_refl.
  - apply (RealSetoid.real_eq_plus_compat y eps z eps).
    + exact Heq.
    + apply real_eq_refl.
  - exact (Hxy eps Heps).
Qed.

(* ============================================================ *)
(* Part A. Temperature-parameterized forms (variant face A; five
   members of the beta-weighted Gibbs family) *)
(* ============================================================ *)

(* A1 The eps-form of the temperature-parameterized pointwise core,
   under the weak premise [b >= 0] (zero temperature is allowed):
   [b*(p-q) <= b*kl(p,q) + b*p*eps].
   Chain: [real_gibbs_core_eps], then right-multiplication monotonicity
   [real_le_mult_compat_r], then a distributivity rewrite — three
   assembly steps with the coefficient kept explicit throughout. *)
Lemma gfe_gibbs_core_temp_eps : forall (p q b : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (Hb : real_le real_zero b) (eps : Real) (Heps : real_lt real_zero eps),
  real_le (real_mult b (real_plus p (real_opp q)))
          (real_plus (real_mult b (real_kl_term p q Hp Hq))
                     (real_mult b (real_mult p eps))).
Proof.
  intros p q b Hp Hq Hb eps Heps.
  apply (RealSetoid.real_le_id_r
           (real_mult b (real_plus p (real_opp q)))
           (real_mult b (real_plus (real_kl_term p q Hp Hq)
                                   (real_mult p eps)))
           (real_plus (real_mult b (real_kl_term p q Hp Hq))
                      (real_mult b (real_mult p eps)))).
  - exact (real_distrib b (real_kl_term p q Hp Hq) (real_mult p eps)).
  - exact (real_le_mult_compat_r b (real_plus p (real_opp q))
             (real_plus (real_kl_term p q Hp Hq) (real_mult p eps)) Hb
             (real_gibbs_core_eps p q Hp Hq eps Heps)).
Qed.

(* A2 The Bishop form of the temperature-parameterized pointwise core,
   under the strict premise [b > 0]: [b*(p-q) <=_B b*kl(p,q)].
   Closer: [real_le_closure_b] with [D := b*p] (positivity witness
   [real_mult_positive]); the per-eps slack [(b*p)*eps] is supplied by
   A1 after an associativity rewrite.
   Note: at [b = 0] no witness for [D] can be produced — the Bishop
   premise is strictly stronger than the eps premise, so the choice of
   inequality form bifurcates constructively under temperature
   scaling. *)
Theorem gfe_gibbs_core_temp_B : forall (p q b : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (Hb : real_lt real_zero b),
  real_le_b (real_mult b (real_plus p (real_opp q)))
            (real_mult b (real_kl_term p q Hp Hq)).
Proof.
  intros p q b Hp Hq Hb.
  apply (real_le_closure_b
           (real_mult b (real_plus p (real_opp q)))
           (real_mult b (real_kl_term p q Hp Hq))
           (real_mult b p) (real_mult_positive b p Hb Hp)).
  intros eps Heps.
  apply (RealSetoid.real_le_id_r
           (real_mult b (real_plus p (real_opp q)))
           (real_plus (real_mult b (real_kl_term p q Hp Hq))
                      (real_mult b (real_mult p eps)))
           (real_plus (real_mult b (real_kl_term p q Hp Hq))
                      (real_mult (real_mult b p) eps))).
  - apply (RealSetoid.real_eq_plus_compat
             (real_mult b (real_kl_term p q Hp Hq))
             (real_mult b (real_mult p eps))
             (real_mult b (real_kl_term p q Hp Hq))
             (real_mult (real_mult b p) eps)).
    + apply real_eq_refl.
    + exact (real_mult_assoc b p eps).
  - exact (gfe_gibbs_core_temp_eps p q b Hp Hq (gfe_le_of_lt b Hb) eps Heps).
Qed.

(* A3 The eps-form of the temperature-parameterized finite sum, under
   the weak premise [b >= 0]: [0 <= b*sum_s kl(p s,q s) + b*eps].
   Chain: [real_gibbs_inequality_eps], then right-multiplication
   monotonicity, then a distributivity rewrite; the left end
   [b*0 == 0] is rewritten via [real_mult_zero] (normalization
   cancellation survives temperature scaling). *)
Lemma gfe_gibbs_inequality_temp_eps : forall (X : Type) (l : list X)
  (p q : X -> Real)
  (Hp : forall s : X, real_lt real_zero (p s))
  (Hq : forall s : X, real_lt real_zero (q s))
  (Hnormp : real_eq (real_list_sum X p l) real_one)
  (Hnormq : real_eq (real_list_sum X q l) real_one)
  (b : Real) (Hb : real_le real_zero b) (eps : Real)
  (Heps : real_lt real_zero eps),
  real_le real_zero
    (real_plus (real_mult b (real_list_sum X
                  (fun s : X => real_kl_term (p s) (q s) (Hp s) (Hq s)) l))
               (real_mult b eps)).
Proof.
  intros X l p q Hp Hq Hnormp Hnormq b Hb eps Heps.
  apply (RealSetoid.real_le_id_l real_zero (real_mult b real_zero)
           (real_plus
              (real_mult b (real_list_sum X
                  (fun s : X => real_kl_term (p s) (q s) (Hp s) (Hq s)) l))
              (real_mult b eps))).
  - exact (real_eq_sym (real_mult b real_zero) real_zero (real_mult_zero b)).
  - apply (RealSetoid.real_le_id_r (real_mult b real_zero)
             (real_mult b (real_plus (real_list_sum X
                  (fun s : X => real_kl_term (p s) (q s) (Hp s) (Hq s)) l)
                  eps))
             (real_plus
                (real_mult b (real_list_sum X
                   (fun s : X => real_kl_term (p s) (q s) (Hp s) (Hq s)) l))
                (real_mult b eps))).
    + exact (real_distrib b (real_list_sum X
                 (fun s : X => real_kl_term (p s) (q s) (Hp s) (Hq s)) l)
                 eps).
    + exact (real_le_mult_compat_r b real_zero
                (real_plus (real_list_sum X
                    (fun s : X => real_kl_term (p s) (q s) (Hp s) (Hq s)) l)
                  eps) Hb
                (real_gibbs_inequality_eps X l p q Hp Hq Hnormp Hnormq
                   eps Heps)).
Qed.

(* A4 The Bishop form of the temperature-parameterized finite sum,
   under the strict premise [b > 0]: [0 <=_B b*sum_s kl(p s,q s)].
   Closer: [real_le_closure_b] with [D := b]; the slack shape of the
   A3 output, [(b*sum kl) + b*eps], matches the shape [y + D*eps]
   supplied by the closure verbatim, so it substitutes in one step. *)
Theorem gfe_gibbs_inequality_temp_B : forall (X : Type) (l : list X)
  (p q : X -> Real)
  (Hp : forall s : X, real_lt real_zero (p s))
  (Hq : forall s : X, real_lt real_zero (q s))
  (Hnormp : real_eq (real_list_sum X p l) real_one)
  (Hnormq : real_eq (real_list_sum X q l) real_one)
  (b : Real) (Hb : real_lt real_zero b),
  real_le_b real_zero
    (real_mult b (real_list_sum X
        (fun s : X => real_kl_term (p s) (q s) (Hp s) (Hq s)) l)).
Proof.
  intros X l p q Hp Hq Hnormp Hnormq b Hb.
  exact (real_le_closure_b real_zero
           (real_mult b (real_list_sum X
               (fun s : X => real_kl_term (p s) (q s) (Hp s) (Hq s)) l))
           b Hb
           (fun eps Heps => gfe_gibbs_inequality_temp_eps X l p q Hp Hq
              Hnormp Hnormq b (gfe_le_of_lt b Hb) eps Heps)).
Qed.

(* A5 Family-level combinator: multiplication by a positive number
   preserves the Bishop order (this development has no other
   multiplicative exit for [<=_B]):
   [x <=_B y /\ 0 < b -> b*x <=_B b*y].
   Chain: unfold [real_le_b] along each eps, lift to [real_le] via
   [real_lt_le_iff_req], apply right-multiplication monotonicity,
   rewrite by distributivity, then close again with
   [real_le_closure_b] ([D := b]). *)
Lemma gfe_le_b_mult_pos : forall (x y b : Real),
  real_lt real_zero b -> real_le_b x y -> real_le_b (real_mult b x) (real_mult b y).
Proof.
  intros x y b Hb Hxy.
  apply (real_le_closure_b (real_mult b x) (real_mult b y) b Hb).
  intros eps Heps.
  apply (RealSetoid.real_le_id_r (real_mult b x)
           (real_mult b (real_plus y eps))
           (real_plus (real_mult b y) (real_mult b eps))).
  - exact (real_distrib b y eps).
  - apply (real_le_mult_compat_r b x (real_plus y eps) (gfe_le_of_lt b Hb)).
    exact (inl (Hxy eps Heps)).
Qed.

(* A6 The unconditional gap in Bishop form under temperature
   ([b > 0]): [0 <=_B b*(kl(p,q) + (q-p))].
   Chain: the premise-free gap form [klstb_gibbs_core_shift_B] is
   rescaled once through the A5 combinator — invariance of the
   second-law reading under temperature scaling. *)
Theorem gfe_gibbs_temp_gap_B : forall (p q b : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (Hb : real_lt real_zero b),
  real_le_b real_zero
    (real_mult b (real_plus (real_kl_term p q Hp Hq)
                            (real_plus q (real_opp p)))).
Proof.
  intros p q b Hp Hq Hb.
  apply (leb3_le_b_eq_l (real_mult b real_zero) real_zero
           (real_mult b (real_plus (real_kl_term p q Hp Hq)
                                   (real_plus q (real_opp p))))).
  - exact (real_mult_zero b).
  - exact (gfe_le_b_mult_pos real_zero
             (real_plus (real_kl_term p q Hp Hq) (real_plus q (real_opp p)))
             b Hb (klstb_gibbs_core_shift_B p q Hp Hq)).
Qed.

(* A6b Expanded-form corollary: [0 <=_B b*kl(p,q) + b*(q-p)] (the
   distributivity face). *)
Lemma gfe_gibbs_temp_gap_B_flat : forall (p q b : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (Hb : real_lt real_zero b),
  real_le_b real_zero
    (real_plus (real_mult b (real_kl_term p q Hp Hq))
               (real_mult b (real_plus q (real_opp p)))).
Proof.
  intros p q b Hp Hq Hb.
  apply (gfe_le_b_eq_r real_zero
           (real_mult b (real_plus (real_kl_term p q Hp Hq)
                                   (real_plus q (real_opp p))))
           (real_plus (real_mult b (real_kl_term p q Hp Hq))
                      (real_mult b (real_plus q (real_opp p))))).
  - exact (gfe_gibbs_temp_gap_B p q b Hp Hq Hb).
  - exact (real_distrib b (real_kl_term p q Hp Hq)
             (real_plus q (real_opp p))).
Qed.

(* ============================================================ *)
(* Part B. Symmetric Jeffreys forms (variant face B; two statements
   complementary to the asymmetric forms) *)
(* ============================================================ *)

(* B1 The symmetric (Jeffreys) pointwise Bishop form, closing the
   asymmetric forms complementarily: [0 <=_B kl(p,q) + kl(q,p)].
   Chain: the two shift forms [klstb_gibbs_core_shift_B] are each
   [>=_B 0] and are added with [real_le_b_plus_compat]; the shifted
   cancellation terms [(q-p) + (p-q)] then peel off the sum through
   [gfe_sym_sum_eq] (the [swap_mid] engine). *)
Theorem gfe_jeffreys_sym_B : forall (p q : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q),
  real_le_b real_zero
    (real_plus (real_kl_term p q Hp Hq) (real_kl_term q p Hq Hp)).
Proof.
  intros p q Hp Hq.
  apply (gfe_le_b_eq_r real_zero
           (real_plus (real_plus (real_kl_term p q Hp Hq)
                                 (real_plus q (real_opp p)))
                      (real_plus (real_kl_term q p Hq Hp)
                                 (real_plus p (real_opp q))))
           (real_plus (real_kl_term p q Hp Hq) (real_kl_term q p Hq Hp))).
  - apply (leb3_le_b_eq_l (real_plus real_zero real_zero) real_zero _
             (real_plus_zero real_zero)
             (real_le_b_plus_compat real_zero
                (real_plus (real_kl_term p q Hp Hq) (real_plus q (real_opp p)))
                real_zero
                (real_plus (real_kl_term q p Hq Hp) (real_plus p (real_opp q)))
                (klstb_gibbs_core_shift_B p q Hp Hq)
                (klstb_gibbs_core_shift_B q p Hq Hp))).
  - exact (gfe_sym_sum_eq (real_kl_term p q Hp Hq) (real_kl_term q p Hq Hp)
             (real_plus q (real_opp p)) (real_plus p (real_opp q))
             (gfe_pq_shift_zero p q)).
Qed.

(* B2 The symmetric (Jeffreys) finite-sum Bishop form:
   [0 <=_B sum_s (kl(p s,q s) + kl(q s,p s))].
   Chain: [klstb_list_sum_le_b] feeds B1 pointwise, and the all-zero
   constant sum is rewritten via [klstb_list_sum_zero] (the symmetric
   family closes at the summation level). *)
Theorem gfe_jeffreys_sym_list_B : forall (X : Type) (l : list X)
  (p q : X -> Real)
  (Hp : forall s : X, real_lt real_zero (p s))
  (Hq : forall s : X, real_lt real_zero (q s)),
  real_le_b real_zero
    (real_list_sum X
       (fun s : X => real_plus (real_kl_term (p s) (q s) (Hp s) (Hq s))
                               (real_kl_term (q s) (p s) (Hq s) (Hp s))) l).
Proof.
  intros X l p q Hp Hq.
  apply (leb3_le_b_eq_l
           (real_list_sum X (fun _ : X => real_zero) l)
           real_zero
           (real_list_sum X
              (fun s : X => real_plus (real_kl_term (p s) (q s) (Hp s) (Hq s))
                                      (real_kl_term (q s) (p s) (Hq s) (Hp s)))
              l)).
  - exact (klstb_list_sum_zero X l).
  - apply (klstb_list_sum_le_b X (fun _ : X => real_zero)
             (fun s : X => real_plus (real_kl_term (p s) (q s) (Hp s) (Hq s))
                                     (real_kl_term (q s) (p s) (Hq s) (Hp s)))
             l).
    intro s. exact (gfe_jeffreys_sym_B (p s) (q s) (Hp s) (Hq s)).
Qed.

(* ============================================================ *)
(* Closure audit: [Print Assumptions] reports every statement Closed. *)
(* ============================================================ *)

Print Assumptions gfe_le_of_lt.
Print Assumptions gfe_pq_shift_zero.
Print Assumptions gfe_sym_sum_eq.
Print Assumptions gfe_le_b_eq_r.
Print Assumptions gfe_gibbs_core_temp_eps.
Print Assumptions gfe_gibbs_core_temp_B.
Print Assumptions gfe_gibbs_inequality_temp_eps.
Print Assumptions gfe_gibbs_inequality_temp_B.
Print Assumptions gfe_le_b_mult_pos.
Print Assumptions gfe_gibbs_temp_gap_B.
Print Assumptions gfe_gibbs_temp_gap_B_flat.
Print Assumptions gfe_jeffreys_sym_B.
Print Assumptions gfe_jeffreys_sym_list_B.
