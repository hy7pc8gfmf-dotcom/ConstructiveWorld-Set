(* ConstructiveWorld-Set -- the B-form upper-bound family for sums of absolute values over lists. *)
(** * UpAblAbsSumLeB: B-form upper bounds for absolute-value sums.

    Mission.  [uabS4_abs_diff_triangle_le_B]/[uabS4_abs_sum_le_B_pair],
      [uabS4_abs_list_sum_le_B]/[uabS4_abs_list_sum_le_eps] (weighted
      upper bounds for the absolute-value sum over a list), and
      [uabS4_lt_double_margin_le_half_contr]/[uabS4_diff_double_kill]
      (contraction under the doubled margin).

    Dependencies.  This development: [S01_BaseRing] .. [S15_TailFEPUp]
      (full chain), [UpRealLeB]; Stdlib [List], [QArith.Qring].

    References.  The finite-sum triangle inequality |Σf| ≤ Σ|f| of real
      analysis, in B-predicate form; UpRealLeB.v ([real_le_b], the
      Bishop-form reachable-strongest predicate, with its closure lemmas);
      S08_RealMainlineDPO.v ([real_list_sum]); the same-name
      ConstructiveWorld-Main baseline.

    Constructivity.  Every proof closed by [Qed]; axiom-free; no classical
      logic; statements Set-carried (the order predicate and the equality
      are Set-valued, zero Prop leakage).

    Build.  [coqc -native-compiler no -q -Q ConstructiveWorld_Live "" UpAblAbsSumLeB.v] (direct call, cpu_guard wrapped). *)

From Stdlib Require Import List.
From Stdlib Require Import QArith.Qring.
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

(* ============================================================ *)
(* §0 in-repository interface check (each Check compared against the real signature) *)
(* ============================================================ *)

Check real_le_b.              (* the Bishop-form ≤ (the reachable-strongest-form predicate, see UpRealLeB) *)
Check real_le_closure_b_one.  (* per-eps completion into B-form (one-step closure) *)
Check real_le_closure_b.      (* B-form closure with the weighted positivity certificate D *)
Check real_abs_triangle_le_B. (* |a+b| ≤_B |a|+|b| (the B-form triangle inequality) *)
Check real_abs_triangle_le_eps. (* |a+b| ≤ (|a|+|b|)+eps per eps (the two-point kernel triangle inequality) *)
Check real_lt_zero_one.       (* 0 < 1 (the W(nil) positivity certificate) *)
Check real_lt_plus_r_zero.    (* y < y+eps (see UpRealLeB) *)
Check real_list_sum.          (* the list fold (universally quantified in X, see S08_RealMainlineDPO) *)
Check RealSetoid.real_eq_abs_compat. (* abs respects real_eq *)
Check real_abs_zero_req.      (* |0| ≡ 0 *)
Check real_lt_irrefl.         (* irreflexivity of < on the reals (the common landing point of contradiction arguments) *)

(* ============================================================ *)
(* §1 basic lemma: right absorption by a positive margin + the difference-form two-point triangle inequality *)
(* ============================================================ *)

(* Basic lemma: le a b and 0 < c imply le a (b+c) (right absorption by a
   positive margin).
   Construction: in each Or component the same chain -- the lt component by
   transitivity (b < b+c by translating the reshaped (b+0)), the eq
   component after transport; both are closed by the left injection through
   real_lt_le_iff_req. *)
Lemma uabS4_le_add_r : forall a b c : Real,
  real_le a b -> real_lt real_zero c -> real_le a (real_plus b c).
Proof.
  intros a b c Hab Hc.
  apply (RealSetoid.real_lt_le_iff_req a (real_plus b c)). apply inl.
  destruct Hab as [Hab | Hab].
  - apply (real_lt_trans a b (real_plus b c)).
    + exact Hab.
    + apply (RealSetoid.real_lt_id_l b (real_plus b real_zero) (real_plus b c)).
      * apply real_eq_sym. apply real_plus_zero.
      * apply (real_lt_plus_translate b real_zero c). exact Hc.
  - apply (RealSetoid.real_lt_id_l a b (real_plus b c)).
    + exact Hab.
    + apply (RealSetoid.real_lt_id_l b (real_plus b real_zero) (real_plus b c)).
      * apply real_eq_sym. apply real_plus_zero.
      * apply (real_lt_plus_translate b real_zero c). exact Hc.
Qed.

(* A.1 the two-point kernel difference form (per eps, Or-inl):
   |a−c| ≤ (|a−b|+|b−c|)+eps.
   Construction: an eq chain for the difference identity
   (a−b)+(b−c) ≡ a−c (assoc ×2 plus opp and zero, five steps, each term
   transported through real_eq_plus_compat); after abs respects eq, the
   two-point kernel triangle applies directly. *)
Lemma uabS4_abs_diff_triangle_le_eps : forall a b c e : Real,
  real_lt real_zero e ->
  real_le (real_abs (real_plus a (real_opp c)))
          (real_plus (real_plus (real_abs (real_plus a (real_opp b)))
                                (real_abs (real_plus b (real_opp c)))) e).
Proof.
  intros a b c e He.
  assert (Hdiff : real_eq (real_plus (real_plus a (real_opp b))
                                     (real_plus b (real_opp c)))
                          (real_plus a (real_opp c))).
  { eapply real_eq_trans.
    - apply real_eq_sym. apply real_plus_assoc.
    - apply (RealSetoid.real_eq_plus_compat a
               (real_plus (real_opp b) (real_plus b (real_opp c))) a
               (real_opp c)).
      + apply real_eq_refl.
      + eapply real_eq_trans.
        * apply real_plus_assoc.
        * eapply real_eq_trans.
          -- apply (RealSetoid.real_eq_plus_compat (real_plus (real_opp b) b)
                          (real_opp c) real_zero (real_opp c)).
             ++ apply (real_eq_trans _ _ _ (real_plus_comm (real_opp b) b)).
                apply real_plus_opp.
             ++ apply real_eq_refl.
          -- apply (real_eq_trans _ _ _ (real_plus_comm real_zero (real_opp c))).
             apply real_plus_zero. }
  apply (RealSetoid.real_le_id_l _ _ _
           (RealSetoid.real_eq_abs_compat _ _
              (real_eq_sym (real_plus (real_plus a (real_opp b))
                                      (real_plus b (real_opp c)))
                           (real_plus a (real_opp c)) Hdiff))).
  exact (real_abs_triangle_le_eps (real_plus a (real_opp b))
                                  (real_plus b (real_opp c)) e He).
Qed.

(* A.2 the two-point kernel difference form (B-form, the reachable strongest
   form): |a−c| ≤_B |a−b|+|b−c|. *)
Theorem uabS4_abs_diff_triangle_le_B : forall a b c : Real,
  real_le_b (real_abs (real_plus a (real_opp c)))
            (real_plus (real_abs (real_plus a (real_opp b)))
                       (real_abs (real_plus b (real_opp c)))).
Proof.
  intros a b c.
  exact (real_le_closure_b_one
    (real_abs (real_plus a (real_opp c)))
    (real_plus (real_abs (real_plus a (real_opp b)))
               (real_abs (real_plus b (real_opp c))))
    (fun e He => uabS4_abs_diff_triangle_le_eps a b c e He)).
Qed.


(* A.3 the B-form instance in the two-point world (S := bool): two points
   are the smallest nontrivial world for the abs_sum_le problem;
   real_abs_triangle_le_B applies directly here. *)
Theorem uabS4_abs_sum_le_B_pair : forall f : bool -> Real,
  real_le_b (real_abs (real_plus (f true) (f false)))
            (real_plus (real_abs (f true)) (real_abs (f false))).
Proof.
  intros f.
  exact (real_abs_triangle_le_B (f true) (f false)).
Qed.

(* ============================================================ *)
(* §2 the list fold form: weighted induction by a weight function + B-form closure *)
(* ============================================================ *)

(* The weight function: W(nil)=1, W(w::rest)=W(rest)+1 (definitional tail
   weight +1).
   Error allocation: each single-point introduction contributes exactly one
   whole unit e per step, the tail margin is carried by W(rest)·e, and the
   total (W(rest)+1)·e ≡ W(cons)·e -- this allocation holds exactly at
   every level. *)
Fixpoint uabS4_wlen (X : Type) (l : list X) : Real :=
  match l with
  | nil => real_one
  | w :: rest => real_plus (uabS4_wlen X rest) real_one
  end.

(* The weight positivity certificate: 0 < W(l) (by induction: 1 > 0; and
   W(rest) > 0 translates to W(rest)+1). *)
Lemma uabS4_wlen_pos : forall (X : Type) (l : list X),
  real_lt real_zero (uabS4_wlen X l).
Proof.
  intros X l. induction l as [| w rest IH].
  - exact real_lt_zero_one.
  - apply (real_lt_trans real_zero (uabS4_wlen X rest)
             (real_plus (uabS4_wlen X rest) real_one)).
    + exact IH.
    + apply real_lt_plus_r_zero. exact real_lt_zero_one.
Qed.

(* The induction-step lemma (the cons step of the fold induction):
   the two-point kernel triangle (single-point introduction, margin exactly
   one whole unit e) plus the tail margin (carried weighted by w·e)
   imply the fold-target margin (w+1)·e.
   Construction: composed through real_le_plus_compat, then finally
   transported along an eq chain of assoc ×3 and distrib/mult_one
   ((w+1)·e ≡ w·e + e, rearranged stepwise via comm/distrib). *)
Lemma uabS4_cons_glue : forall a s t w e : Real,
  real_lt real_zero e ->
  real_le (real_abs (real_plus a s))
          (real_plus (real_plus (real_abs a) (real_abs s)) e) ->
  real_le (real_abs s) (real_plus t (real_mult w e)) ->
  real_le (real_abs (real_plus a s))
          (real_plus (real_plus (real_abs a) t)
                     (real_mult (real_plus w real_one) e)).
Proof.
  intros a s t w e He Hpair Hih.
  assert (Hmid : real_le (real_plus (real_abs a) (real_abs s))
                         (real_plus (real_abs a) (real_plus t (real_mult w e)))).
  { apply (real_le_plus_compat (real_abs a) (real_abs a)
             (real_abs s) (real_plus t (real_mult w e))).
    - exact (RealSetoid.real_eq_le _ _ (real_eq_refl (real_abs a))).
    - exact Hih. }
  assert (Hstep : real_le (real_plus (real_plus (real_abs a) (real_abs s)) e)
                          (real_plus (real_plus (real_abs a)
                                     (real_plus t (real_mult w e))) e)).
  { apply (real_le_plus_compat _ _ e e).
    - exact Hmid.
    - exact (RealSetoid.real_eq_le _ _ (real_eq_refl e)). }
  assert (Hchain : real_le (real_abs (real_plus a s))
                           (real_plus (real_plus (real_abs a)
                                      (real_plus t (real_mult w e))) e)).
  { apply (real_le_trans _ _ _ Hpair Hstep). }
  apply (RealSetoid.real_le_id_r (real_abs (real_plus a s))
           (real_plus (real_plus (real_abs a) (real_plus t (real_mult w e))) e)
           (real_plus (real_plus (real_abs a) t)
                      (real_mult (real_plus w real_one) e))).
  - eapply real_eq_trans.
    + apply real_eq_sym. apply real_plus_assoc.
    + eapply real_eq_trans.
      * apply (RealSetoid.real_eq_plus_compat (real_abs a)
                   (real_plus (real_plus t (real_mult w e)) e) (real_abs a)
                   (real_plus t (real_plus (real_mult w e) e))).
        -- apply real_eq_refl.
        -- apply real_eq_sym. apply real_plus_assoc.
      * eapply real_eq_trans.
        -- apply real_plus_assoc.
        -- apply (RealSetoid.real_eq_plus_compat (real_plus (real_abs a) t)
                        (real_plus (real_mult w e) e)
                        (real_plus (real_abs a) t)
                        (real_mult (real_plus w real_one) e)).
           ++ apply real_eq_refl.
           ++ apply real_eq_sym.
              apply (real_eq_trans _ _ _
                       (real_mult_comm (real_plus w real_one) e)).
              apply (real_eq_trans _ _ _ (real_distrib e w real_one)).
              apply (RealSetoid.real_eq_plus_compat (real_mult e w)
                          (real_mult e real_one) (real_mult w e) e).
              ** apply real_mult_comm.
              ** apply real_mult_one.
  - exact Hchain.
Qed.

(* B.1 the weighted induction body (per-eps form, weight function W):
   |Σ_l f| ≤ Σ_l|f| + W(l)·e.
   Case l=[]: |0| ≡ 0 ≤ 0 + 1·e (right absorption by a positive margin).
   Induction step from l to w::rest: the two-point kernel triangle
   introduces one whole unit e, the tail is carried at the same weight by
   the inductive premise (IH), composed through uabS4_cons_glue. *)
Lemma uabS4_abs_list_sum_le_wt : forall (X : Type) (f : X -> Real) (l : list X)
                                        (e : Real),
  real_lt real_zero e ->
  real_le (real_abs (real_list_sum X f l))
          (real_plus (real_list_sum X (fun x => real_abs (f x)) l)
                     (real_mult (uabS4_wlen X l) e)).
Proof.
  intros X f l. induction l as [| w rest IH]; intro e; intro He.
  - apply (uabS4_le_add_r (real_abs (real_list_sum X f nil)) real_zero
             (real_mult (uabS4_wlen X nil) e)).
    + apply (RealSetoid.real_le_id_l (real_abs real_zero) real_zero real_zero).
      * exact real_abs_zero_req.
      * exact (RealSetoid.real_eq_le real_zero real_zero (real_eq_refl real_zero)).
    + apply (RealSetoid.real_lt_id_r real_zero e (real_mult real_one e)).
      * apply real_eq_sym.
        apply (real_eq_trans _ _ _ (real_mult_comm real_one e)).
        apply real_mult_one.
      * exact He.
  - apply (uabS4_cons_glue (f w) (real_list_sum X f rest)
             (real_list_sum X (fun x => real_abs (f x)) rest)
             (uabS4_wlen X rest) e He).
    + exact (real_abs_triangle_le_eps (f w) (real_list_sum X f rest) e He).
    + exact (IH e He).
Qed.

(* B.2 the B-form closure (the reachable strongest form):
   |Σ_l f| ≤_B Σ_l|f|.
   real_le_closure_b closes the weighted family with the explicit
   positivity certificate D := W(l). *)
Theorem uabS4_abs_list_sum_le_B : forall (X : Type) (f : X -> Real) (l : list X),
  real_le_b (real_abs (real_list_sum X f l))
            (real_list_sum X (fun x => real_abs (f x)) l).
Proof.
  intros X f l.
  exact (real_le_closure_b
    (real_abs (real_list_sum X f l))
    (real_list_sum X (fun x => real_abs (f x)) l)
    (uabS4_wlen X l) (uabS4_wlen_pos X l)
    (fun e He => uabS4_abs_list_sum_le_wt X f l e He)).
Qed.


(* B.3 the per-eps corollary: B-form implies |Σ_l f| ≤ Σ_l|f| + eps
   (Or-inl injection).
   Comparison: the B-form is strictly stronger than the per-eps form --
   real_le_closure_b_one is the one-step inversion. *)
Theorem uabS4_abs_list_sum_le_eps : forall (X : Type) (f : X -> Real) (l : list X)
                                           (e : Real),
  real_lt real_zero e ->
  real_le (real_abs (real_list_sum X f l))
          (real_plus (real_list_sum X (fun x => real_abs (f x)) l) e).
Proof.
  intros X f l e He.
  apply (RealSetoid.real_lt_le_iff_req _ _).
  apply inl.
  exact (uabS4_abs_list_sum_le_B X f l e He).
Qed.

(* ============================================================ *)
(* §3 the non-coexistence lemma for margin factor 2 *)
(* ============================================================ *)

(* C.1 non-coexistence at margin factor 2: 0 < e together with
   real_lt (Y+2e) X and real_le X (Y+e) cannot coexist.
   Construction: both Or components derive real_lt (Y+2e) (Y+e) --
   the lt component by transitivity (Y+2e < X < Y+e); the eq component by
   transport on the RHS (X ≡ Y+e);
   on the other side, e < 2e by translation gives Y+e < Y+2e, and the
   conjunction with the above contradicts real_lt_irrefl.
   Boundary note: when the margin is exactly e (factor 1), the eq component
   and the reverse strict inequality can coexist (an approximation example
   of the form xₙ−yₙ = e+1/n); at factor 2 they cannot. *)
Theorem uabS4_lt_double_margin_le_half_contr : forall X Y e : Real,
  real_lt real_zero e ->
  real_lt (real_plus Y (real_plus e e)) X ->
  real_le X (real_plus Y e) ->
  Empty_set.
Proof.
  intros X Y e He Hfar Hle.
  assert (Hboom : real_lt (real_plus Y (real_plus e e))
                          (real_plus Y e) -> Empty_set).
  { intro Hbad.
    assert (Hfwd : real_lt (real_plus Y e) (real_plus Y (real_plus e e))).
    { apply (real_lt_plus_translate Y e (real_plus e e)).
      apply (RealSetoid.real_lt_id_l e (real_plus e real_zero) (real_plus e e)).
      - apply real_eq_sym. apply real_plus_zero.
      - apply (real_lt_plus_translate e real_zero e). exact He. }
    exact (real_lt_irrefl _ (real_lt_trans _ _ _ Hbad Hfwd)). }
  unfold real_le in Hle. destruct Hle as [Hlt | Heq].
  - exact (Hboom (real_lt_trans _ _ _ Hfar Hlt)).
  - apply Hboom.
    exact (RealSetoid.real_lt_id_r (real_plus Y (real_plus e e)) X
             (real_plus Y e) Heq Hfar).
Qed.

(* C.2 the difference-form instance of the factor-2 contradiction (the
   diagonal combination of the two-point kernel difference form with C.1):
   with the per-eps difference-form two-point kernel
   (uabS4_abs_diff_triangle_le_eps) as the le source, a contradiction
   instance under the margin constraint of the shape
   real_lt (b + 2e) a together with |a−c| ≤_B |a−b|+|b−c| --
   the B-form at eps := e gives le a (|a−b|+|b−c|+e), and substituting
   into C.1 yields the result. *)
Theorem uabS4_diff_double_kill : forall a b c e : Real,
  real_lt real_zero e ->
  real_lt (real_plus (real_plus (real_abs (real_plus a (real_opp b)))
                                  (real_abs (real_plus b (real_opp c))))
                     (real_plus e e))
          (real_abs (real_plus a (real_opp c))) ->
  Empty_set.
Proof.
  intros a b c e He Hfar.
  apply (uabS4_lt_double_margin_le_half_contr           (real_abs (real_plus a (real_opp c)))           (real_plus (real_abs (real_plus a (real_opp b)))                      (real_abs (real_plus b (real_opp c)))) e He Hfar).
  exact (uabS4_abs_diff_triangle_le_eps a b c e He).
Qed.

(* ============================================================ *)
(* Audit note: Print Assumptions expected all Closed (zero external unproved assumptions) *)
(* ============================================================ *)

Print Assumptions uabS4_le_add_r.
Print Assumptions uabS4_abs_diff_triangle_le_eps.
Print Assumptions uabS4_abs_diff_triangle_le_B.
Print Assumptions uabS4_abs_sum_le_B_pair.
Print Assumptions uabS4_wlen_pos.
Print Assumptions uabS4_cons_glue.
Print Assumptions uabS4_abs_list_sum_le_wt.
Print Assumptions uabS4_abs_list_sum_le_B.
Print Assumptions uabS4_abs_list_sum_le_eps.
Print Assumptions uabS4_lt_double_margin_le_half_contr.
Print Assumptions uabS4_diff_double_kill.
