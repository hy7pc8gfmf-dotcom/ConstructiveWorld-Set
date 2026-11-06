(* ConstructiveWorld-Set -- upstream TV-chain premise-site per-eps absolute-value supply. *)

(** * UpReqTVAbsEps: per-eps absolute-value chain supply for the TV premise site.

    Mission.  Formalizes the eps-slack companion to the triangle inequality
      for finite sums of reals: [tvd_abs_sum_le_list_eps] bounds the absolute
      value of a finite [real_list_sum] by the pointwise-absolute sum plus a
      positive [eps]; the helpers [tv9_lt_plus_r_zero], [tv9_two_pos],
      [tv9_half], [tv9_half_pos], [tv9_double_inv] and [tv9_abs_triangle_ih]
      supply the strict translation, the half quantity, its positivity, the
      half-plus-half normalization and the induction combiner.

    Dependencies.  Stdlib [List], [QArith.Qring].  Requires [S01_BaseRing],
      [S02_CauchyComplete], [S03_QExp], [S04_RealExpLogConv],
      [S05_AlignmentGRPO], [S06_DiffSamplingGibbs], [S07_RealSetoidExpLog],
      [S08_RealMainlineDPO], [S09_EntropyReal], [S10_KVQuantTrig],
      [S11_TP3B5], [S12_B5RecycleSF], [S13_NLiveAudit], [S14_B5BatchBlock],
      [S15_TailFEPUp] of this development.

    References.  This development, UpReqTVAbsEps.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" UpReqTVAbsEps.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 00015ff4]. *)
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

(* ---- 0. Pointwise ring-identity extraction (standalone copy of the
        UpTVDoeblin tvd_rring move): a [real_eq] goal reduces to pointwise
        Q identities resolved by [ring].
        [real_plus], [real_mult], [real_opp], [real_minus_r], [real_one],
        [real_zero] are transparent and simplify pointwise to Q expressions
        after [cbn [projT1 ...]]; [real_abs] and [real_inv_pos] stay opaque
        and enter [ring] as atoms. ---- *)
Ltac tv9_rring :=
  apply real_eq_of_zero_diff; intro n0; apply qeq_imp_qeqT;
  repeat match goal with
         | [ x : Real |- _ ] => destruct x
         end;
  cbn [projT1 real_plus real_mult real_opp real_minus_r real_one real_zero
       real_list_sum real_of_nat] in *;
  ring.

(* ---- 1. Strict right translation (six-line inline form of UpRealLeB
        real_lt_plus_r_zero): 0 < eps gives y < y + eps, by lt translation
        plus the reshaping y+0==y. ---- *)
Lemma tv9_lt_plus_r_zero : forall (y eps : Real),
  real_lt real_zero eps -> real_lt y (real_plus y eps).
Proof.
  intros y eps Heps.
  apply (RealSetoid.real_lt_id_l y (real_plus y real_zero) (real_plus y eps)).
  - apply real_eq_sym. apply real_plus_zero.
  - apply (real_lt_plus_translate y real_zero eps). exact Heps.
Qed.

(* ---- 2. Positivity of two (standalone copy of the UpTVDoeblin tv_two_pos
        move): 0 < 1+1; built in this file to avoid a section binding to the
        same-named library lemma. ---- *)
Lemma tv9_two_pos : real_lt real_zero (real_plus real_one real_one).
Proof.
  apply (RealSetoid.real_lt_id_l real_zero
           (real_plus real_zero real_zero)
           (real_plus real_one real_one)).
  - exact (real_eq_sym (real_plus real_zero real_zero) real_zero
             (real_plus_zero real_zero)).
  - exact (real_lt_plus_compat real_zero real_one real_zero real_one
             real_lt_zero_one real_lt_zero_one).
Qed.

(* ---- 3. Half quantity: [tv9_half := 1/(1+1)] (standalone copy of the
        UpTVDoeblin tv_half construction). ---- *)
Definition tv9_half : Real :=
  real_inv_pos (real_plus real_one real_one) tv9_two_pos.

Lemma tv9_half_pos : real_lt real_zero tv9_half.
Proof. exact (real_inv_pos_pos (real_plus real_one real_one) tv9_two_pos). Qed.

(* ---- 4. Half-doubling normalization: (t·e)+(t·e) == e with
   t := 1/(1+1), i.e. h+h == eps. ----
   Equation chain: (t·e)+(t·e) == ((1+1)·t)·e (by ring)
           == real_one·e (inverse law real_inv_pos_correct, x on the left)
           == e (by ring). ---- *)
Lemma tv9_double_inv : forall (t e : Real),
  real_eq (real_mult (real_plus real_one real_one) t) real_one ->
  real_eq (real_plus (real_mult t e) (real_mult t e)) e.
Proof.
  intros t e Hinv.
  apply (real_eq_trans
           (real_plus (real_mult t e) (real_mult t e))
           (real_mult (real_mult (real_plus real_one real_one) t) e)
           e).
  - tv9_rring.
  - apply (real_eq_trans
             (real_mult (real_mult (real_plus real_one real_one) t) e)
             (real_mult real_one e)
             e).
    + exact (RealSetoid.real_eq_mult_compat _ _ _ _ Hinv (real_eq_refl e)).
    + tv9_rring.
Qed.

(* ---- 5. Triangle-plus-inductive-premise combiner (the step-case core
   piece; every equation chain is digested here). ----
   Given h positive, h+h == e, the triangle instance
   |a+b| ≤ (|a|+|b|)+h and the inductive premise |b| ≤ c+h, it yields
   |a+b| ≤ (|a|+c)+e.
   Chain: |a|+|b| ≤ |a|+(c+h) (plus_compat)
         (|a|+|b|)+h ≤ (|a|+(c+h))+h (plus_compat on the second summand)
         reshape (|a|+(c+h))+h == ((|a|+c)+h)+h == (|a|+c)+(h+h)
             == (|a|+c)+e (assoc in two steps plus the half-doubling
             normalization, closed by real_le_id_r). ---- *)
Lemma tv9_abs_triangle_ih : forall (a b c h e : Real),
  real_lt real_zero h ->
  real_eq (real_plus h h) e ->
  real_le (real_abs (real_plus a b))
          (real_plus (real_plus (real_abs a) (real_abs b)) h) ->
  real_le (real_abs b) (real_plus c h) ->
  real_le (real_abs (real_plus a b)) (real_plus (real_plus (real_abs a) c) e).
Proof.
  intros a b c h e Hh Ehh HTri HIH.
  assert (P2 : real_le (real_plus (real_abs a) (real_abs b))
                       (real_plus (real_abs a) (real_plus c h))).
  { exact (real_le_plus_compat (real_abs a) (real_abs a) (real_abs b)
             (real_plus c h) (real_le_refl (real_abs a)) HIH). }
  assert (P3 : real_le (real_plus (real_plus (real_abs a) (real_abs b)) h)
                       (real_plus (real_plus (real_abs a) (real_plus c h)) h)).
  { exact (real_le_plus_compat _ _ h h P2 (real_le_refl h)). }
  assert (HT : real_le (real_abs (real_plus a b))
                       (real_plus (real_plus (real_abs a) (real_plus c h)) h)).
  { exact (real_le_trans _ _ _ HTri P3). }
  apply (RealSetoid.real_le_id_r
           (real_abs (real_plus a b))
           (real_plus (real_plus (real_abs a) (real_plus c h)) h)
           (real_plus (real_plus (real_abs a) c) e)).
  - apply (real_eq_trans
             (real_plus (real_plus (real_abs a) (real_plus c h)) h)
             (real_plus (real_plus (real_plus (real_abs a) c) h) h)
             (real_plus (real_plus (real_abs a) c) e)).
    + exact (RealSetoid.real_eq_plus_compat _ h _ h
               (real_plus_assoc (real_abs a) c h) (real_eq_refl h)).
    + apply (real_eq_trans
               (real_plus (real_plus (real_plus (real_abs a) c) h) h)
               (real_plus (real_plus (real_abs a) c) (real_plus h h))
               (real_plus (real_plus (real_abs a) c) e)).
      * exact (real_eq_sym _ _
                 (real_plus_assoc (real_plus (real_abs a) c) h h)).
      * exact (RealSetoid.real_eq_plus_compat _ (real_plus h h) _ e
                 (real_eq_refl _) Ehh).
  - exact HT.
Qed.

(* ============================================================ *)
(* Main statement: the eps-slack companion to Theorem 5.10        *)
(* (zero-interface; the Or-encoded eps slack enters verbatim).    *)
(* ============================================================ *)
Lemma tvd_abs_sum_le_list_eps :
  forall (l : list (list Real)) (f : list Real -> Real) (eps : Real),
    real_lt real_zero eps ->
    real_le (real_abs (real_list_sum (list Real) f l))
            (real_plus (real_list_sum (list Real)
                          (fun w => real_abs (f w)) l) eps).
Proof.
  intros l f. induction l as [| w rest IH]; intros eps Heps.
  - (* Base case []: after [cbn] the goal is |real_zero| ≤ real_zero + eps;
       take the strict left branch (the inlined real_lt_plus_r_zero piece);
       the reshaping |0| == 0 (real_abs_zero_req) goes through
       real_lt_id_l. *)
    cbn [real_list_sum].
    apply (RealSetoid.real_lt_le_iff_req (real_abs real_zero)
             (real_plus real_zero eps)). left.
    apply (RealSetoid.real_lt_id_l (real_abs real_zero) real_zero
             (real_plus real_zero eps)).
    + exact real_abs_zero_req.
    + exact (tv9_lt_plus_r_zero real_zero eps Heps).
  - (* Step case w::rest: after [cbn] connects with real_plus, the triangle
       piece and the inductive premise each consume the half quantity
       h := tv9_half·eps (positivity by real_mult_pos_compat); the
       half-doubling normalization h+h==eps (tv9_double_inv +
       real_inv_pos_correct) hands everything to tv9_abs_triangle_ih in
       one step. *)
    cbn [real_list_sum].
    apply (tv9_abs_triangle_ih (f w)
             (real_list_sum (list Real) f rest)
             (real_list_sum (list Real)
                (fun w0 : list Real => real_abs (f w0)) rest)
             (real_mult tv9_half eps) eps).
    + exact (real_mult_pos_compat tv9_half eps tv9_half_pos Heps).
    + exact (tv9_double_inv tv9_half eps
               (real_inv_pos_correct (real_plus real_one real_one)
                  tv9_two_pos)).
    + exact (real_abs_triangle_le_eps (f w)
               (real_list_sum (list Real) f rest)
               (real_mult tv9_half eps)
               (real_mult_pos_compat tv9_half eps tv9_half_pos Heps)).
    + exact (IH (real_mult tv9_half eps)
               (real_mult_pos_compat tv9_half eps tv9_half_pos Heps)).
Qed.

Print Assumptions tv9_half_pos.
