(* ConstructiveWorld-Set -- B-form Bishop-order statements for the ppo, summation, minp-projection and lattice families. *)

(** * G06_BForm: B-form statements for ppo conservatism, Bishop sums, minp projection and lattice laws.

    Mission.  B-form (Bishop order [real_le_b]) statements in four merged
      member families: ppo conservatism [real_ppo_conservative_B_full], the
      pointwise-to-sum lift [sumb_list_sum_le_b] on [sumb_lenR], the minp
      projection cluster [real_minp_projection_eps_B] and
      [real_minp_projection_B_split], the lattice laws [latb_lt_b],
      [latb_max_le_b], [latb_min_le_b], [latb_real_lt_interconnect].

    Dependencies.  Stdlib [QArith.Qring], [QArith.QArith], [QArith.Qminmax],
      [Arith.PeanoNat].  Requires of this development [S01_BaseRing],
      [S02_CauchyComplete], [S03_QExp], [S04_RealExpLogConv], [S05_AlignmentGRPO],
      [S06_DiffSamplingGibbs], [S07_RealSetoidExpLog], [S08_RealMainlineDPO],
      [S09_EntropyReal], [S10_KVQuantTrig], [S11_TP3B5], [S12_B5RecycleSF],
      [S13_NLiveAudit], [S14_B5BatchBlock], [S15_TailFEPUp], [UpAuditBridge],
      [UpRealLeB], [UpRealLeB2], [UpRealLeB3].

    References.  This development, G06_BForm.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" G06_BForm.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 000160bc]. *)
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
(* ============================================================
   member module UpReqPPOB: the B-form upgrade of the ppo conservatism
   theorem, its complete Bishop form (merged as-is with its own Requires).
   Main statement real_ppo_conservative_B_full:
   sum pi_old * min(r, clip r) * adv <=_B sum pi_old * r * adv.  The only
   missing premise of the conditional statement real_ppo_conservative_B in
   UpRealLeB.v, the explicit certificate of E > 0 for E := sum pi_old * adv,
   is supplied directly by the aggregated-positivity premise
   lebR_res_weight_pos : real_lt real_zero E, so the closure-combiner use
   keeps the apply line unchanged.
   The pointwise advantage_pos premise cannot be dropped: the eps-form source
   real_ppo_conservative_eps (S08 L2342) uses it pointwise at its
   real_le_mult_compat step (S08 L2367); under aggregated positivity alone
   the main conclusion is false (model counterexample: S = {1,2}, pi = 1,
   adv = (0.2, -0.1), r = (1.2, 5), eps_c = 0.1 gives E = 0.1 > 0 while
   sum (r - min(r, clip r)) * adv = 0.02 - 0.39 < 0, LHS > RHS); the
   weakening therefore only reaches the certificate axis (the argument
   position becomes aggregated positivity) and the pointwise axis stays a
   verbatim copy of the source statement.
   Constructivity: real_le_b is a Set-valued forall type and real_lt a sigT
   Set type, so no Prop leaks into any conclusion; the premises pi_old_pos
   and advantage_pos are copied verbatim from the source statement; all
   printed statements are Closed under the global context.
   ============================================================ *)
Section RealPPOLeBFull.

Variable S : Type.
Variable real_sum_over_S : (S -> Real) -> Real.
Variable real_sum_over_S_ext : forall (f g : S -> Real),
  (forall s : S, real_eq (f s) (g s)) -> real_eq (real_sum_over_S f) (real_sum_over_S g).
Variable real_sum_over_S_le : forall (f g : S -> Real),
  (forall s : S, real_le (f s) (g s)) -> real_le (real_sum_over_S f) (real_sum_over_S g).
Variable real_sum_over_S_add : forall (f g : S -> Real),
  real_eq (real_sum_over_S (fun s : S => real_plus (f s) (g s)))
          (real_plus (real_sum_over_S f) (real_sum_over_S g)).
(* the scalar-extraction interface, placed as in Part C *)
Variable real_sum_over_S_linear : forall (a : Real) (f : S -> Real),
  real_eq (real_sum_over_S (fun s : S => real_mult a (f s)))
           (real_mult a (real_sum_over_S f)).
(* the sum-positivity slot of T2(1) (explicit argument position) was removed
   with the premise weakening: aggregated positivity E > 0 rises directly to
   the premise position (after the lebR_res_weight definition) and no longer
   goes through a pointwise-positive-implies-sum-positive slot. *)
Variable real_pi_star_ : S -> Real.
Variable real_pi_old : S -> Real.
Variable real_pi_old_pos : forall s : S, real_lt real_zero (real_pi_old s).
Variable real_advantage_fn : S -> Real.
Variable real_advantage_pos : forall s : S, real_lt real_zero (real_advantage_fn s).
Variable epsilon : Real.
(* residual weight coefficient E := sum pi_old * adv (defined as in Part C, inter-convertible with the discharged lemma) *)
Definition lebR_res_weight : Real :=
  real_sum_over_S (fun s : S => real_mult (real_pi_old s) (real_advantage_fn s)).

(* aggregated-positivity premise: E > 0 moves from internal derivation to a
   direct premise; the closure-combiner use of the main statement keeps the
   same apply line and surface name, and the supply side moves from a slot
   plus a derivation chain to this premise position (explicit, entering the
   main statement signature through the section, not a free-floating global
   constant). *)
Hypothesis lebR_res_weight_pos : real_lt real_zero lebR_res_weight.
(* main statement: the complete <=_B form; the E > 0 certificate is supplied by the aggregated-positivity premise *)
Theorem real_ppo_conservative_B_full :
  real_le_b
    (real_sum_over_S (fun s : S =>
      real_mult (real_pi_old s)
        (real_mult (real_min (real_importance_ratio_ S real_pi_star_ real_pi_old real_pi_old_pos s)
                             (real_ppo_clip_ epsilon (real_importance_ratio_ S real_pi_star_ real_pi_old real_pi_old_pos s)))
                   (real_advantage_fn s))))
    (real_sum_over_S (fun s : S =>
      real_mult (real_pi_old s)
        (real_mult (real_importance_ratio_ S real_pi_star_ real_pi_old real_pi_old_pos s)
                   (real_advantage_fn s)))).
Proof.
  apply (real_le_closure_b _ _ lebR_res_weight lebR_res_weight_pos).
  intros eps Heps.
  apply (real_le_trans _
           (real_plus
              (real_sum_over_S (fun s : S =>
                 real_mult (real_pi_old s)
                   (real_mult (real_importance_ratio_ S real_pi_star_ real_pi_old real_pi_old_pos s)
                              (real_advantage_fn s))))
              (real_sum_over_S (fun s : S =>
                 real_mult (real_pi_old s) (real_mult eps (real_advantage_fn s))))) _).
  - exact (real_ppo_conservative_eps S real_sum_over_S real_sum_over_S_ext
             real_sum_over_S_le real_sum_over_S_add real_pi_star_ real_pi_old
             real_pi_old_pos real_advantage_fn real_advantage_pos epsilon eps Heps).
  - apply (real_le_plus_compat _ _ _ _ (real_le_refl _)).
    apply (RealSetoid.real_eq_le _ _).
    exact (real_ppo_res_fold S real_sum_over_S real_sum_over_S_ext
             real_sum_over_S_linear real_pi_old real_advantage_fn eps).
Qed.
End RealPPOLeBFull.

(* end note: the residual fold real_ppo_res_fold takes 7 arguments and the
   eps-form source statement 13, all supplied explicitly. *)
(* end note: lebR_res_weight_pos is a section premise since the premise
   weakening, entering the main statement signature through the section, no
   longer exported as a standalone constant. *)
Print Assumptions real_ppo_conservative_B_full.
Print Assumptions lebR_res_weight.
(* the prints of the companions rplb_res_weight_pos_uncond and
   rplb_sum_pos_discharged sit at the end of the file, after the section that
   defines them. *)

(* ============================================================ *)
(* proof section: the constructive carrier lemma for sum positivity.  After
   the former rplb_sum_pos section argument was removed with the premise
   weakening, this section keeps the implication pointwise positive implies
   sum positive alive as an independent construction on the list carrier;
   the companion lemmas rebuild the E > 0 carrier face directly, without
   argument instantiation.
   Carrier determination: the real_list_sum of the base RealListSumMain
   section is a list Fixpoint, generic in X, with the nil branch at
   real_zero.  The empty branch decides the statement shape: for the empty
   list the sum is real_zero, so strict positivity fails, and the statement
   must carry the nonemptiness premise Not (Id l nil) (the same shape as the
   base sum_temp_positive; the same empty-branch criterion as the
   closure-combiner case).
   Lead lemma: the list-carrier instance of sum positivity (induction, two
   branches: contradiction on nil, two feeds of real_plus_positive on cons);
   the companion rebuilds the E > 0 carrier face over a fixed nonempty vocab
   with pi_old and adv both constant real_one and the certificate
   real_lt_zero_one (base L39486) -- nothing residual at the exits. *)
(* ============================================================ *)
Section RplbSumPosDischarged.
Variable X : Set.

(* proof lemma: a finite sum with pointwise positive terms is positive (nonempty-list premise; the list-carrier instance of the former rplb_sum_pos argument) *)
Lemma rplb_sum_pos_discharged :
  forall (f : X -> Real) (l : list X),
    Not (Id l nil) ->
    (forall s : X, real_lt real_zero (f s)) ->
    real_lt real_zero (real_list_sum X f l).
Proof.
  intros f l.
  induction l as [| x rest IH]; intros Hnil Hpos.
  - (* empty branch: the nonemptiness premise contradicts directly; the sum is real_zero, so the premise holds *)
    contradiction Hnil. apply id_refl.
  - destruct rest as [| y rest'].
    + (* single-element branch: f x + 0 reshapes back to f x (real_plus_zero through real_lt_eq_lt) *)
      exact (real_lt_eq_lt real_zero (f x)
               (real_plus (f x) (real_list_sum X f nil))
               (Hpos x)
               (real_eq_sym (real_plus (f x) (real_list_sum X f nil)) (f x)
                  (real_plus_zero (f x)))).
    + (* general cons branch: two feeds of real_plus_positive -- pointwise positivity plus the induction positivity of the tail *)
      apply (real_plus_positive (f x) (real_list_sum X f (y :: rest'))).
      * apply Hpos.
      * apply IH. intro Hc. inversion Hc. apply Hpos.
Qed.
End RplbSumPosDischarged.

(* companion (rebuilt): the unconditional reconstruction of the E > 0 carrier
   face: pi_old and adv both the constant real_one, delivered through the lead
   lemma (two feeds of real_mult_positive plus the sum-positivity carrier
   lemma), with no dependence on the weakened premise position. *)
Section RplbResWeightPosUncond.
Variable X : Set.
Variable vocab : list X.
Hypothesis vocab_nonempty : Not (Id vocab nil).

Definition rplb_sum_vocab (f : X -> Real) : Real := real_list_sum X f vocab.

Lemma rplb_res_weight_pos_uncond :
  real_lt real_zero
    (lebR_res_weight X rplb_sum_vocab (fun _ : X => real_one) (fun _ : X => real_one)).
Proof.
  unfold lebR_res_weight, rplb_sum_vocab.
  apply (rplb_sum_pos_discharged X
           (fun s : X => real_mult real_one real_one) vocab vocab_nonempty).
  intro s.
  exact (real_mult_positive real_one real_one real_lt_zero_one real_lt_zero_one).
Qed.
End RplbResWeightPosUncond.

Print Assumptions rplb_sum_pos_discharged.
Print Assumptions rplb_res_weight_pos_uncond.

(* ======== member module UpReqSumB (merged as-is, with its own Requires) ======== *)
(* ============================================================ *)
(* member module UpReqSumB: the pointwise <=_B sum-lifting module
   (real_list_sum_le_b_compat).
   Main results (all Set-level, no Prop leakage, pure term-mode assembly):
   part 1, sumb_lenR: a self-contained Real-layer list-length machine
        (Fixpoint, nil -> 0, cons -> 1 + lenR rest).  No nat bridge: the
        nat-embedding lemmas of the base tree live behind a frozen interface
        and are not reusable here, so this file runs its own Real induction
        with zero interface dependencies.
   part 1, sumb_lenR_nonneg: 0 <= lenR l (induction plus pointwise nonneg
        addition compatibility).
   part 1, sumb_sum_const: sum(constant c) == lenR l * c (induction; the
        cons step is the distributive law plus a one-factor reshaping,
        isomorphic to the lenR definition step -- the core reshaping module
        of the summation face).
   part 2, sumb_list_sum_le_b: the main statement -- pointwise <=_B implies
        sum <=_B (the n-ary Bishop sum face, a Fubini-style pointwise lift).
        Given delta > 0, expand every pointwise <=_B at the same delta (no
        1/n split: under the Bishop universal face, n copies of the same
        delta suffice -- the essential difference from a plain-eps split
        chain); each pointwise lt branch rises to real_le through the one-way
        Or-coding bridge; real_list_sum_le lifts the order to sum f <=
        sum (g + delta); sum (g + delta) reshapes to sum g + lenR * delta
        (two steps: add and sum_const); the nonnegative-coefficient closure
        combiner (C := lenR l, the nonnegativity certificate being the
        part-1 lemma) closes in one step.
   Uses (all through certified upstream .vo files, no upstream rewriting):
   the base real_list_sum lemmas (section proof signatures with X as the
   first argument, Check-checked); UpRealLeB2 real_le_closure_b_nonneg (the
   nonnegative-coefficient closure combiner); the RealSetoid combiner face
   (lt_le_iff_req, le_id_l, le_id_r, eq_plus_compat).
   Constructivity: zero axioms and zero unclosed proofs; Set-level statements
   (real_le_b is a Set-valued forall type, no Prop leaks into any
   conclusion); pure term-mode explicit assembly (real_eq is not Id, no
   rewriting, the whole chain goes through real_eq_trans and compat);
   everything closed by Qed; the new statements are Closed under Print
   Assumptions (at the end of the file). *)
(* ============================================================ *)

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
Require Import UpRealLeB2.

(* ============================================================ *)
(* part 1, S.1: the self-contained length machine lenR (Real layer, no nat-bridge interface) *)
(* ============================================================ *)

Fixpoint sumb_lenR (X : Type) (l : list X) : Real :=
  match l with
  | nil => real_zero
  | cons _ rest => real_plus real_one (sumb_lenR X rest)
  end.

(* ============================================================ *)
(* part 1, S.2: length nonnegativity, 0 <= lenR l.
   Induction: the cons step 0 <= 1 + lenR rest goes through the 0 + 0 and 0
   reshapes plus pointwise nonneg addition compatibility. *)
(* ============================================================ *)

Lemma sumb_lenR_nonneg : forall (X : Type) (l : list X),
  real_le real_zero (sumb_lenR X l).
Proof.
  intros X l. induction l as [| w rest IH]; simpl.
  - apply real_le_refl.
  - apply (RealSetoid.real_le_id_l (real_plus real_zero real_zero) real_zero
                                   (real_plus real_one (sumb_lenR X rest))).
    + apply real_plus_zero.
    + apply (real_le_plus_compat real_zero real_one real_zero (sumb_lenR X rest)).
      * exact (RealSetoid.real_lt_le_iff_req real_zero real_one (inl real_lt_zero_one)).
      * exact IH.
Qed.

(* ============================================================ *)
(* part 1, S.3: constant-sum collapse, sum(constant c) == lenR l * c.
   Induction: the cons step gives c + sum_const rest == c + lenR rest * c (IH)
   == 1 * c + lenR rest * c (one-factor reshaping) == (1 + lenR rest) * c
   (distributive law). *)
(* ============================================================ *)

Lemma sumb_sum_const : forall (X : Type) (c : Real) (l : list X),
  real_eq (real_list_sum X (fun _ : X => c) l) (real_mult (sumb_lenR X l) c).
Proof.
  intros X c l. induction l as [| w rest IH]; simpl.
  - (* 0 == 0 * c: through the c * 0 intermediate (mult_zero sits on the right factor, bridged by comm) *)
    apply (real_eq_trans _ (real_mult c real_zero) _).
    + apply real_eq_sym. apply real_mult_zero.
    + apply real_mult_comm.
  - apply (real_eq_trans _
             (real_plus c (real_mult (sumb_lenR X rest) c)) _).
    + apply (RealSetoid.real_eq_plus_compat c
               (real_list_sum X (fun _ : X => c) rest)
               c
               (real_mult (sumb_lenR X rest) c)).
      * apply real_eq_refl.
      * exact IH.
    + apply (real_eq_trans _
               (real_plus (real_mult real_one c)
                          (real_mult (sumb_lenR X rest) c)) _).
      * apply (RealSetoid.real_eq_plus_compat c
                 (real_mult (sumb_lenR X rest) c)
                 (real_mult real_one c)
                 (real_mult (sumb_lenR X rest) c)).
        -- (* c == 1 * c: c * 1 == c (mult_one on the right factor) plus the comm bridge *)
           apply (real_eq_trans _ (real_mult c real_one) _).
           ++ apply real_eq_sym. apply real_mult_one.
           ++ apply real_mult_comm.
        -- apply real_eq_refl.
      * (* (1 * c) + (lenR * c) == (1 + lenR) * c: real_distrib_r connects directly, same orientation, nothing flipped *)
        apply real_distrib_r.
Qed.

(* ============================================================ *)
(* part 2, S.4: the main statement, the pointwise <=_B sum lift (the n-ary
   Bishop sum face).  sumb_list_sum_le_b: pointwise <=_B implies sum <=_B.
   Proof chain: given delta > 0, expand every pointwise <=_B at the same
   delta (no 1/n split: under the real_le_b universal face, n copies of the
   same delta suffice); each pointwise lt branch rises to real_le through the
   one-way Or-coding bridge (within the stated Or-coding boundary: the Or
   coding serves only as a one-way bridge); real_list_sum_le lifts the order
   to sum f <= sum (g + delta); sum (g + delta) == sum g + sum(constant
   delta) == sum g + lenR * delta (the add step and the part-1 sum_const
   step); the nonnegative-coefficient closure combiner closes in one step
   (C := lenR l, the nonnegativity certificate being part-1 lenR_nonneg). *)
(* ============================================================ *)

Lemma sumb_list_sum_le_b : forall (X : Type) (f g : X -> Real) (l : list X),
  (forall w : X, real_le_b (f w) (g w)) ->
  real_le_b (real_list_sum X f l) (real_list_sum X g l).
Proof.
  intros X f g l H.
  (* no unfold needed: the closure-combiner conclusion is already a real_le_b
     form and matches directly (the outer universal delta is consumed by the
     combiner; the pointwise unification of eps happens inside its universal
     premise position) *)
  apply (real_le_closure_b_nonneg
           (real_list_sum X f l)
           (real_list_sum X g l)
           (sumb_lenR X l)).
  - (* premise 1: 0 <= C := lenR l (the part-1 lemma) *)
    apply sumb_lenR_nonneg.
  - (* premise 2: forall eps > 0, sum f <= sum g + lenR * eps *)
    intros eps Heps.
    (* pointwise unification of eps: f w < g w + eps (the lt branch) rises to real_le (the inl one-way Or-coding bridge) *)
    assert (Hpt : forall w : X, real_le (f w) (real_plus (g w) eps)).
    { intro w.
      exact (RealSetoid.real_lt_le_iff_req (f w) (real_plus (g w) eps)
               (inl (H w eps Heps))). }
    pose proof (real_list_sum_le X f (fun w : X => real_plus (g w) eps) l Hpt) as Hsum.
    (* reshape the right end: sum (g + eps) == sum g + sum(constant eps) == sum g + lenR * eps *)
    apply (RealSetoid.real_le_id_r
             (real_list_sum X f l)
             (real_list_sum X (fun w : X => real_plus (g w) eps) l)
             (real_plus (real_list_sum X g l)
                        (real_mult (sumb_lenR X l) eps))).
    + apply (real_eq_trans _
               (real_plus (real_list_sum X g l)
                          (real_list_sum X (fun _ : X => eps) l)) _).
      * apply (real_list_sum_add X g (fun _ : X => eps) l).
      * apply (RealSetoid.real_eq_plus_compat (real_list_sum X g l)
                 (real_list_sum X (fun _ : X => eps) l)
                 (real_list_sum X g l)
                 (real_mult (sumb_lenR X l) eps)).
        -- apply real_eq_refl.
        -- apply sumb_sum_const.
    + exact Hsum.
Qed.

(* ============================================================ *)
(* end notes.
   Pointwise unification of eps: sumb_list_sum_le_b is provable and needs no
   1/n split.  Root cause: real_le_b is a Set-valued universal face (for all
   eps > 0), so an n-ary sum closure can take the same delta at every
   pointwise lemma; the n copies of delta merge into the right end and
   collapse to sum(constant delta), reshaped to lenR * delta in one step.
   This differs essentially from the eps/2 split chains of the plain-eps
   family (the leb2_half_add base module): universal slack is freely copyable
   on the Bishop face, no constructive halving is needed.
   Self-contained length machine: sumb_lenR is a three-line Real-layer
   Fixpoint with no nat-bridge interface; the nat-embedding lemmas of the
   base tree are frozen across the interface and are bypassed here.  The
   numerical alignment of lenR with length has no use face: this design uses
   no nat numerics and runs entirely on Real induction.
   Closure-combiner choice: the main statement takes the nonnegative-
   coefficient combiner (C := lenR l, certificate sumb_lenR_nonneg).  Strict
   positivity of lenR fails on the empty list (lenR nil == 0), so a C > 0
   certificate route is unusable -- exactly the specification situation of
   real_le_closure_b_nonneg (UpRealLeB2 L102); the empty branch closes
   naturally through the C + 1 > 0 certificate face of the combiner, with no
   case split.
   Or-coding boundary: the pointwise lift uses only the one-way bridge (the
   lt branch through inl), consistent with the fact that the Or-form
   pointwise premise lift is not provable (the min counterexample); this
   file makes no Or-form pointwise-lift claim.
   The four specification statements of the original task (lenR,
   lenR_nonneg, sum_const, the main statement) all land in this file; the
   prefix sumb_ is collision-free in the tree, avoiding the leb3_ territory;
   the n-ary face complements the earlier binary-only combiner boundary. *)
(* ============================================================ *)

Print Assumptions sumb_lenR_nonneg.
Print Assumptions sumb_sum_const.
Print Assumptions sumb_list_sum_le_b.

(* ======== member module UpReqMinPProjB (merged as-is, with its own Requires) ======== *)
(* ============================================================ *)
(* member module UpReqMinPProjB: the B-form upgrade cluster of the minp
   projection theorem (item W2' of the second paper).  Base: the
   real_minp_projection_eps statement of UpAuditBridge.v (the merged version
   that passed the checkpoints on the base face); this file only uses it and
   rewrites nothing upstream.
   Main results (Set-level conclusions, no new logical premises, all truly
   proved):
   1. real_minp_projection_eps_B (main statement):
      KL_list(q||minp) <=_B KL_list(q||full), the universal eps slack
      discharged.  Route: one-step closure by real_le_closure_b_one plus the
      direct connection to the base eps-form statement (the plain-eps slack
      family closes uniformly in Bishop form; the exact classical disjunction
      form is not provable -- there is a min counterexample -- and this
      statement is the Bishop-form resolution of that verdict).
   2. real_minp_tail_nonneg_B (companion A): the B form of tail
      nonnegativity, 0 <=_B sum kl_tail; chain = the uab_kl_tail_eval
      equation reshaping (real_eq_sym) + real_opp_log_Z_aud_nonneg + the
      one-way bridge real_le_to_le_b.
   3. real_minp_projection_B_split (companion B): a reproof of the main
      conclusion by a decomposition route, not using the base eps-form
      statement: companion A + the <=_B addition-compatibility combiner
      (UpRealLeB2 real_le_b_plus_compat) + the right-end equation reshaping
      by uab_kl_sum_split -- a cross-validation of the same conclusion by
      two routes.
   4. Four helper lemmas (prefix umpb_, pure Real layer, no section
      dependencies): <=_B reflexivity, left-end equation transport,
      right-end equation transport, monotone addition of a nonnegative right
      summand.
   Constructivity notes: every statement closed by a real Qed proof (term-mode
      explicit assembly, real_eq is not Id so no rewriting, the chain runs
      through the real_eq_trans/sym/compat family), no degraded placeholders;
      all conclusions Set-level (real_le_b is a Set-valued forall type, no
      Prop leakage); the premise positions are verbatim copies of the base
      proof face (copying the premise face is the upgrade discipline); the
      disjunction/negation premise face kept by the verdict belongs to the
      root MinP machine interface inherited from the base (same shape there),
      so this file adds no logical premise of its own; the section variables
      replicate the eight arguments of the base proof face verbatim
      (declaration order included, Check-checked); extraction reports
      Obj.magic = 0; Print Assumptions closed for every statement (the prints
      at the end of the file). *)
(* ============================================================ *)

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
Require Import UpAuditBridge.
Require Import UpRealLeB.
Require Import UpRealLeB2.

(* ============================================================ *)
(* helper-lemma area (pure Real layer, no section dependencies, all term-mode real proofs) *)
(* ============================================================ *)

(* helper 1: <=_B reflexivity (the one-way bridge plus real_le_refl, one step) *)
Lemma umpb_le_b_refl : forall x : Real, real_le_b x x.
Proof.
  intros x. apply real_le_to_le_b. apply real_le_refl.
Qed.

(* helper 2: right-end equation transport for <=_B: x <=_B y1 and y1 == y2
   give x <=_B y2 (real_eq is an eps-wise approximation equivalence and must
   not be rewritten, so the route is RealSetoid lt_id_r plus plus_compat) *)
Lemma umpb_le_b_eq_r : forall x y1 y2 : Real,
  real_le_b x y1 -> real_eq y1 y2 -> real_le_b x y2.
Proof.
  intros x y1 y2 H Heq. unfold real_le_b in H. unfold real_le_b.
  intros eps Heps.
  apply (RealSetoid.real_lt_id_r x (real_plus y1 eps) (real_plus y2 eps)).
  - apply (RealSetoid.real_eq_plus_compat y1 eps y2 eps).
    + exact Heq.
    + apply real_eq_refl.
  - exact (H eps Heps).
Qed.

(* helper 3: left-end equation transport for <=_B: x1 == x2 and x1 <=_B y give x2 <=_B y *)
Lemma umpb_le_b_eq_l : forall x1 x2 y : Real,
  real_eq x1 x2 -> real_le_b x1 y -> real_le_b x2 y.
Proof.
  intros x1 x2 y Heq H. unfold real_le_b in H. unfold real_le_b.
  intros eps Heps.
  apply (RealSetoid.real_lt_id_l x2 x1 (real_plus y eps)).
  - apply real_eq_sym. exact Heq.
  - exact (H eps Heps).
Qed.

(* helper 4: nonnegative right addition for <=_B: 0 <=_B c gives a <=_B a + c
   (the B-form analogue of the nonneg-right-add lemma: the
   addition-compatibility combiner plus the a + 0 == a left transport) *)
Lemma umpb_le_b_plus_nonneg_r : forall a c : Real,
  real_le_b real_zero c -> real_le_b a (real_plus a c).
Proof.
  intros a c Hc.
  apply (umpb_le_b_eq_l (real_plus a real_zero) a (real_plus a c)).
  - apply real_plus_zero.
  - apply (real_le_b_plus_compat a a real_zero c).
    + apply umpb_le_b_refl.
    + exact Hc.
Qed.

(* ============================================================ *)
(* main section: the section variables replicate the eight arguments of the
   base UpAuditBridge proof face verbatim (declaration order included) *)
(* ============================================================ *)

Section UpReqMinPProjB.

Variable Token : Type.
Variable vocab : list Token.
Variable real_temp_factor : Token -> Real.
Variable real_minp_keep : list Token -> Token -> Set.
Variable real_minp_keep_dec : forall (prefix : list Token) (w : Token),
  Or (real_minp_keep prefix w) (Not (real_minp_keep prefix w)).
Variable uab_temp_sum_pos : forall prefix : list Token,
  real_lt real_zero
    (uab_temp_sum Token vocab real_temp_factor real_minp_keep
                  real_minp_keep_dec prefix).
Variable uab_temp_factor_pos : forall w : Token,
  real_lt real_zero (real_temp_factor w).
Variable uab_Z_full_pos : real_lt real_zero
  (Z_full Token vocab real_temp_factor).

(* ============================================================ *)
(* main statement: KL_list(q||minp) <=_B KL_list(q||full).
   Universal discharge of the eps slack: the plain-eps form bounds eps-wise
   (direct connection to the base statement) and closes as the non-strict
   Bishop order through the closure combiner with D := one, whose positivity
   certificate real_lt_zero_one is an existing base lemma, so no new
   premise. *)
(* ============================================================ *)

Theorem real_minp_projection_eps_B :
  forall (prefix : list Token) (q : Token -> Real)
    (Hq_norm : real_eq (real_list_sum Token q vocab) real_one)
    (Hq_pos : forall w : Token,
                real_minp_keep prefix w -> real_lt real_zero (q w))
    (Hq_fail : forall w : Token,
                 Not (real_minp_keep prefix w) -> real_eq (q w) real_zero),
  real_le_b
    (real_list_sum Token
       (uab_kl_q_minp Token vocab real_temp_factor real_minp_keep
                      real_minp_keep_dec uab_temp_sum_pos uab_temp_factor_pos
                      prefix q Hq_pos) vocab)
    (real_list_sum Token
       (uab_kl_q_full Token vocab real_temp_factor real_minp_keep
                      real_minp_keep_dec uab_temp_factor_pos uab_Z_full_pos
                      prefix q Hq_pos) vocab).
Proof.
  intros prefix q Hq_norm Hq_pos Hq_fail.
  apply real_le_closure_b_one. intros eps Heps.
  exact (real_minp_projection_eps Token vocab real_temp_factor real_minp_keep
           real_minp_keep_dec uab_temp_sum_pos uab_temp_factor_pos
           uab_Z_full_pos prefix q Hq_norm Hq_pos Hq_fail eps Heps).
Qed.

(* ============================================================ *)
(* companion A: the B form of tail nonnegativity, 0 <=_B sum kl_tail.
   Chain: uab_kl_tail_eval (the sum of the tail equals - log uab_Z_aud)
   reshapes the right end into the base nonnegativity lemma, and the one-way
   bridge lifts the result to the B form -- the independent lemma form of the
   main step of the base proof. *)
(* ============================================================ *)

Theorem real_minp_tail_nonneg_B :
  forall (prefix : list Token) (q : Token -> Real)
    (Hq_norm : real_eq (real_list_sum Token q vocab) real_one)
    (Hq_pos : forall w : Token,
                real_minp_keep prefix w -> real_lt real_zero (q w))
    (Hq_fail : forall w : Token,
                 Not (real_minp_keep prefix w) -> real_eq (q w) real_zero),
  real_le_b real_zero
    (real_list_sum Token
       (uab_kl_tail Token vocab real_temp_factor real_minp_keep
                    real_minp_keep_dec uab_temp_sum_pos uab_temp_factor_pos
                    uab_Z_full_pos prefix q Hq_pos) vocab).
Proof.
  intros prefix q Hq_norm Hq_pos Hq_fail.
  apply real_le_to_le_b.
  apply (RealSetoid.real_le_id_r real_zero
           (real_opp (real_log
              (uab_Z_aud Token vocab real_temp_factor real_minp_keep
                     real_minp_keep_dec uab_Z_full_pos prefix)
              (uab_Z_aud_pos_cert Token vocab real_temp_factor real_minp_keep
                                  real_minp_keep_dec uab_temp_sum_pos
                                  uab_Z_full_pos prefix)))
           (real_list_sum Token
              (uab_kl_tail Token vocab real_temp_factor real_minp_keep
                           real_minp_keep_dec uab_temp_sum_pos
                           uab_temp_factor_pos uab_Z_full_pos
                           prefix q Hq_pos) vocab)).
  - exact (real_eq_sym _ _
             (uab_kl_tail_eval Token vocab real_temp_factor real_minp_keep
                real_minp_keep_dec uab_temp_sum_pos uab_temp_factor_pos
                uab_Z_full_pos prefix q Hq_norm Hq_pos Hq_fail)).
  - exact (real_opp_log_Z_aud_nonneg Token vocab real_temp_factor
             real_minp_keep real_minp_keep_dec uab_temp_sum_pos
             uab_temp_factor_pos uab_Z_full_pos prefix).
Qed.

(* ============================================================ *)
(* companion B: a reproof of the main conclusion by decomposition, with the
   base eps-form statement unused.
   Chain: companion A (tail nonnegativity in B form) + helper 4 (nonnegative
   right addition) + the <=_B addition-compatibility combiner + the
   uab_kl_sum_split identity reshaped at the right end (helper 2).  No eps is
   evaluated. *)
(* ============================================================ *)

Theorem real_minp_projection_B_split :
  forall (prefix : list Token) (q : Token -> Real)
    (Hq_norm : real_eq (real_list_sum Token q vocab) real_one)
    (Hq_pos : forall w : Token,
                real_minp_keep prefix w -> real_lt real_zero (q w))
    (Hq_fail : forall w : Token,
                 Not (real_minp_keep prefix w) -> real_eq (q w) real_zero),
  real_le_b
    (real_list_sum Token
       (uab_kl_q_minp Token vocab real_temp_factor real_minp_keep
                      real_minp_keep_dec uab_temp_sum_pos uab_temp_factor_pos
                      prefix q Hq_pos) vocab)
    (real_list_sum Token
       (uab_kl_q_full Token vocab real_temp_factor real_minp_keep
                      real_minp_keep_dec uab_temp_factor_pos uab_Z_full_pos
                      prefix q Hq_pos) vocab).
Proof.
  intros prefix q Hq_norm Hq_pos Hq_fail.
  pose proof (real_minp_tail_nonneg_B prefix q Hq_norm Hq_pos Hq_fail)
    as HtailB.
  pose proof (uab_kl_sum_split Token vocab real_temp_factor real_minp_keep
                 real_minp_keep_dec uab_temp_sum_pos uab_temp_factor_pos
                 uab_Z_full_pos prefix q Hq_norm Hq_pos Hq_fail) as Hsplit.
  apply (umpb_le_b_eq_r
           (real_list_sum Token
              (uab_kl_q_minp Token vocab real_temp_factor real_minp_keep
                             real_minp_keep_dec uab_temp_sum_pos
                             uab_temp_factor_pos prefix q Hq_pos) vocab)
           (real_plus
              (real_list_sum Token
                 (uab_kl_q_minp Token vocab real_temp_factor real_minp_keep
                                real_minp_keep_dec uab_temp_sum_pos
                                uab_temp_factor_pos prefix q Hq_pos) vocab)
              (real_list_sum Token
                 (uab_kl_tail Token vocab real_temp_factor real_minp_keep
                              real_minp_keep_dec uab_temp_sum_pos
                              uab_temp_factor_pos uab_Z_full_pos
                              prefix q Hq_pos) vocab))
           (real_list_sum Token
              (uab_kl_q_full Token vocab real_temp_factor real_minp_keep
                             real_minp_keep_dec uab_temp_factor_pos
                             uab_Z_full_pos prefix q Hq_pos) vocab)).
  - apply umpb_le_b_plus_nonneg_r. exact HtailB.
  - exact (real_eq_sym _ _ Hsplit).
Qed.

End UpReqMinPProjB.

(* ============================================================ *)
(* the Print Assumptions audit for all statements (prints below) *)
(* ============================================================ *)

Print Assumptions umpb_le_b_refl.
Print Assumptions umpb_le_b_eq_r.
Print Assumptions umpb_le_b_eq_l.
Print Assumptions umpb_le_b_plus_nonneg_r.
Print Assumptions real_minp_projection_eps_B.
Print Assumptions real_minp_tail_nonneg_B.
Print Assumptions real_minp_projection_B_split.

(* ======== member module UpReqLatticeB (merged as-is, with its own Requires) ======== *)
(* ============================================================ *)
(* member module UpReqLatticeB: the front part of the B-form lattice
   combinator face, the strict-lt primitive plus the max side.
   Scope: the front part of lattice goal 4.  The min side and the lattice
   absorption laws belong to the later part; this file contributes the
   strict-lt primitive, the two connection lemmas and the three max-side
   statements.  Upstream use: UpRealLeB3 (the three transport lemmas
   eq_r/plus_nonneg_r/refl) + UpRealLeB (the closure combiner with D
   specialized to one, plus the one-way bridge) + base anchors (real_max_proj,
   the pointwise Q-layer projection channel; real_max as the pointwise Qmax
   coding; real_lt as a sigT witness type; the stdlib generic lattice strict
   forms Q.max_lub_lt and Q.min_dec, Qopp_le_compat, Qlt_minus_iff).
   A note on the pointwise Qmax upper-bound strict form: no full witness
   rearrangement is needed -- the stdlib generic lattice lemma Q.max_lub_lt
   (n < p implies m < p implies max n m < p) connects directly after
   pointwise reduction, closing in one step, which halves the work for the
   new primitive; the min dual (Q.min_glb_lt, same library) transfers by the
   same method.
   Six statements: 1 latb_lt_b, the strict-order primitive (there is
   delta > 0 with x <=_B y - delta; the sigT + And form follows the real_lt
   isomorphism, Set-level with no Prop on the surface) / 2 latb_lt_b_to_le_b,
   the strict-to-<=_B connection (the boundary plus delta cancels pairwise at
   the right end) / 3 latb_real_lt_to_le_b, base strict order implies <=_B
   (the Or left branch in one step) / 4 latb_lt_max_intro, the strict
   upper-bound introduction primitive (the Q-layer channel: the min witness
   plus max_lub_lt pointwise direct) / 5 latb_max_le_b, the max upper-bound
   lattice main statement (a <=_B c and b <=_B c imply max <=_B c; both
   premises take the same d := c + eps, the left branches enter the Or, and
   the one-closure combiner closes in one step) / 6 latb_max_le_r, the
   absorption instance (a <=_B b implies max a b <=_B b).
   Constructivity notes: all statements Set-level (latb_lt_b is a sigT
   witness type whose And components follow the existing real_lt usage;
   conclusions are all real_le_b or real_lt); no Or-form unprovable face is
   claimed: the exact form real_le (real_max a b) c is out of scope (same
   branch-choice source as the min counterexample), the strict face only goes
   through real_lt witnesses; no new premises (all positivity certificates
   are existing lemmas); everything truly proved and closed, no degraded
   placeholders; extraction reports Obj.magic = 0; Print Assumptions closed
   for every statement (the prints at the end of the file). *)
(* ============================================================ *)

From Stdlib Require Import QArith.QArith QArith.Qring QArith.Qminmax.
From Stdlib Require Import Arith.PeanoNat.
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

Local Open Scope Q_scope.

(* ============================================================ *)
(* 1. the strict-lt primitive and the <=_B connection lemmas *)
(* ============================================================ *)

(* statement 1: the Bishop strict-order primitive: x <_B y := there is
   delta > 0 with x <=_B y + (- delta).
   The sigT + And form follows the real_lt isomorphism (the same Set-level
   wrapper as the base real_lt); the margin clause is expressed through
   real_le_b (no Prop on the surface). *)
Definition latb_lt_b (x y : Real) : Set :=
  sigT (fun d : Real => And (real_lt real_zero d)
                            (real_le_b x (real_plus y (real_opp d)))).

(* statement 2: the connection lemma (strict form implies <=_B): x <=_B y - delta
   with delta > 0 gives x <=_B (y - delta) + delta == y.  Add the positive
   amount delta at the right end (the nonneg-right-add transport lemma), then
   an associativity + cancellation + zero-identity chain of reshapes. *)
Lemma latb_lt_b_to_le_b : forall x y : Real, latb_lt_b x y -> real_le_b x y.
Proof.
  intros x y Hd. destruct Hd as [d [Hdpos Hle]].
  apply (leb3_le_b_eq_r x (real_plus (real_plus y (real_opp d)) d) y).
  - apply (leb3_le_b_plus_nonneg_r x (real_plus y (real_opp d)) d Hle).
    unfold real_le. left. exact Hdpos.
  - assert (Hz : real_eq (real_plus (real_opp d) d) real_zero).
    { apply (real_eq_trans (real_plus (real_opp d) d)
               (real_plus d (real_opp d)) real_zero).
      - apply real_plus_comm.
      - apply real_plus_opp. }
    apply (real_eq_trans (real_plus (real_plus y (real_opp d)) d)
             (real_plus y (real_plus (real_opp d) d)) y).
    + apply real_eq_sym. apply real_plus_assoc.
    + apply (real_eq_trans (real_plus y (real_plus (real_opp d) d))
               (real_plus y real_zero) y).
      * apply (RealSetoid.real_eq_plus_compat y
                 (real_plus (real_opp d) d) y real_zero).
        -- apply real_eq_refl.
        -- exact Hz.
      * apply real_plus_zero.
Qed.

(* statement 3: the connection lemma from the base strict order: real_lt is
   the Or-form left branch, so the one-way bridge closes in one step. *)
Lemma latb_real_lt_to_le_b : forall x y : Real,
  real_lt x y -> real_le_b x y.
Proof.
  intros x y H. apply real_le_to_le_b. unfold real_le. left. exact H.
Qed.

(* ============================================================ *)
(* 2. max-side combinator lemmas (through the real_max_proj Q-layer channel) *)
(* ============================================================ *)

(* statement 4: the strict upper-bound introduction primitive: a < d and b < d
   give max a b < d.
   The witness eps is set to Qmin ea eb (positivity by the Q.min_dec branch)
   and N to max Na Nb; after pointwise reduction (the real_max_proj channel)
   the a_n < d_n - Qmin <= d_n - ea side and the b_n side reshape through
   Qopp_le_compat and Qplus_le_compat respectively, Q.max_lub_lt closes the
   Qmax in one step, and the final segment is the Qlt_minus_iff + ring
   identity reshaping. *)
Lemma latb_lt_max_intro : forall a b d : Real,
  real_lt a d -> real_lt b d -> real_lt (real_max a b) d.
Proof.
  intros a b d Ha Hb.
  destruct Ha as [ea [Hea [Na HNa]]].
  destruct Hb as [eb [Heb [Nb HNb]]].
  exists (Qmin ea eb). split.
  - apply Qlt_to_QltT.
    destruct (Q.min_dec ea eb) as [E | E].
    + rewrite E. apply QltT_to_Qlt. exact Hea.
    + rewrite E. apply QltT_to_Qlt. exact Heb.
  - exists (Nat.max Na Nb). intros n Hn.
    apply Qlt_to_QltT.
    (* real_max_proj is a QeqT-face equation (Id carrier); rewrite needs the
       Qeq setoid face -- bridge one layer per the S07 real_abs_proj idiom *)
    rewrite (qeqT_imp_qeq _ _ (real_max_proj a b n)).
    assert (Han : NatLe Na n).
    { apply NatLe_lift. apply Nat.le_trans with (Nat.max Na Nb).
      - apply Nat.le_max_l.
      - exact (NatLe_drop _ _ Hn). }
    assert (Hbn : NatLe Nb n).
    { apply NatLe_lift. apply Nat.le_trans with (Nat.max Na Nb).
      - apply Nat.le_max_r.
      - exact (NatLe_drop _ _ Hn). }
    pose proof (QltT_to_Qlt _ _ (HNa n Han)) as Q1.
    pose proof (QltT_to_Qlt _ _ (HNb n Hbn)) as Q2.
    assert (Ml : Qle (Qmin ea eb) ea) by apply Q.le_min_l.
    assert (Mr : Qle (Qmin ea eb) eb) by apply Q.le_min_r.
    (* strict-bound flip: ea < d_n - a_n gives a_n < d_n - ea (Qlt_minus_iff plus a ring identity) *)
    assert (Q1r : projT1 a n < projT1 d n - ea).
    { apply (proj2 (Qlt_minus_iff (projT1 a n) (projT1 d n - ea))).
      assert (Hj1 : (projT1 d n - ea - projT1 a n ==
                     projT1 d n - projT1 a n - ea)%Q)
        by (unfold Qminus; ring).
      rewrite Hj1.
      apply (proj1 (Qlt_minus_iff ea (projT1 d n - projT1 a n))).
      exact Q1. }
    assert (Q2r : projT1 b n < projT1 d n - eb).
    { apply (proj2 (Qlt_minus_iff (projT1 b n) (projT1 d n - eb))).
      assert (Hj2 : (projT1 d n - eb - projT1 b n ==
                     projT1 d n - projT1 b n - eb)%Q)
        by (unfold Qminus; ring).
      rewrite Hj2.
      apply (proj1 (Qlt_minus_iff eb (projT1 d n - projT1 b n))).
      exact Q2. }
    assert (Qa : projT1 a n < projT1 d n - Qmin ea eb).
    { apply (Qlt_le_trans _ (projT1 d n - ea) _ Q1r).
      unfold Qminus. apply Qplus_le_compat.
      - apply Qle_refl.
      - apply Qopp_le_compat. exact Ml. }
    assert (Qb : projT1 b n < projT1 d n - Qmin ea eb).
    { apply (Qlt_le_trans _ (projT1 d n - eb) _ Q2r).
      unfold Qminus. apply Qplus_le_compat.
      - apply Qle_refl.
      - apply Qopp_le_compat. exact Mr. }
    assert (Hmax : Qmax (projT1 a n) (projT1 b n)
                     < projT1 d n - Qmin ea eb)
      by (apply Q.max_lub_lt; assumption).
    apply (proj2 (Qlt_minus_iff (Qmin ea eb)
              (projT1 d n - Qmax (projT1 a n) (projT1 b n)))).
    assert (Hj : (projT1 d n - Qmax (projT1 a n) (projT1 b n)
                    + - Qmin ea eb ==
                  projT1 d n - Qmin ea eb
                    + - Qmax (projT1 a n) (projT1 b n))%Q)
      by (unfold Qminus; ring).
    rewrite Hj.
    apply (proj1 (Qlt_minus_iff (Qmax (projT1 a n) (projT1 b n))
                   (projT1 d n - Qmin ea eb))).
    exact Hmax.
Qed.

(* statement 5 (main statement): the max upper-bound lattice law: a <=_B c and
   b <=_B c give max a b <=_B c.
   Given eps > 0, both premises take d := c + eps; statement 4 yields
   max a b < c + eps (strict) in one step, the Or left branch enters the
   exact face, and the one-closure combiner closes in one step -- the
   constructive branch-choice difficulty (the same source as the min
   counterexample) does not exist on the strict-witness face, so no eps/2
   split is needed. *)
Lemma latb_max_le_b : forall a b c : Real,
  real_le_b a c -> real_le_b b c -> real_le_b (real_max a b) c.
Proof.
  intros a b c Ha Hb.
  apply real_le_closure_b_one.
  intros eps Heps. unfold real_le. left.
  apply latb_lt_max_intro.
  - exact (Ha eps Heps).
  - exact (Hb eps Heps).
Qed.

(* statement 6: the absorption instance: a <=_B b gives max a b <=_B b (statement 5 plus <=_B reflexivity). *)
Lemma latb_max_le_r : forall a b : Real,
  real_le_b a b -> real_le_b (real_max a b) b.
Proof.
  intros a b H. apply (latb_max_le_b a b b H).
  apply leb3_le_b_refl.
Qed.

(* ============================================================ *)
(* 3. the assumption audit (every statement Closed, printed below) *)
(* ============================================================ *)

Print Assumptions latb_lt_b.
Print Assumptions latb_lt_b_to_le_b.
Print Assumptions latb_real_lt_to_le_b.
Print Assumptions latb_lt_max_intro.
Print Assumptions latb_max_le_b.
Print Assumptions latb_max_le_r.

(* ============================================================ *)
(* 4. the min-side combinator lemmas (the appended later-part section): the
   dual primitive, the lower-bound lattice laws and the glb main statement.
   Five statements: 7 latb_min_glb, the strict lower-bound introduction
   primitive (the Q-layer channel: the Qmin witness plus Q.min_glb_lt
   pointwise direct; the strict-bound shift e + p_n < a_n goes through
   Qle_lt_trans and Qplus_le_compat; the return-slack flip follows the
   Qlt_minus_iff pattern) / 8 latb_min_le_b, the min lower-bound lattice main
   statement (c <=_B a and c <=_B b give c <=_B min a b; asymmetric to the
   max side -- the eps slack hangs outside the min, so the one-step
   one-closure combiner is unreachable (on the max side the eps sits inside
   the conclusion position of latb_lt_max_intro), and the full pointwise
   proof runs: the real_plus_proj reshape + the Qmin lower-bound shift + the
   Q.min_dec branch closure) / 9 latb_min_le_l, the lower-bound lattice law
   left (a free lemma: real_min_le_l_B at UpRealLeB L396, connected verbatim)
   / 10 latb_min_le_r, the lower-bound lattice law right (real_min_le_r_B at
   UpRealLeB L403, connected directly) / 11 latb_min_le_le, the trans
   assembly lemma (real_le_b_trans at UpRealLeB2 plus statement 9 in two
   steps: min a b <=_B a <=_B c gives min a b <=_B c).
   Constructivity along the same line: all statements Set-level (real_lt
   sigT witness forms and real_le_b forall forms, no Prop on the surface);
   no new premises; everything truly proved and closed, no degraded
   placeholders. *)
(* ============================================================ *)

(* statement 7: the strict lower-bound introduction primitive: p < a and p < b
   give p < min a b.
   The witness e is set to Qmin ea eb (positivity by the Q.min_dec branch)
   and N to max Na Nb; after pointwise reduction (the real_min_proj channel),
   the ea < a_n - p_n bounds flip to ea + p_n < a_n, the shift
   e + p_n <= ea + p_n (two Qle_lt_trans steps) gives e + p_n < a_n and
   e + p_n < b_n, Q.min_glb_lt closes the Qmin in one step, and the final
   segment flips back through Qlt_minus_iff + ring identities to the real_lt
   witness form e < Qmin - p_n. *)
Lemma latb_min_glb : forall p a b : Real,
  real_lt p a -> real_lt p b -> real_lt p (real_min a b).
Proof.
  intros p a b Hp Ha.
  destruct Hp as [ea [Hea [Na HNa]]].
  destruct Ha as [eb [Heb [Nb HNb]]].
  exists (Qmin ea eb). split.
  - apply Qlt_to_QltT.
    destruct (Q.min_dec ea eb) as [E | E].
    + rewrite E. apply QltT_to_Qlt. exact Hea.
    + rewrite E. apply QltT_to_Qlt. exact Heb.
  - exists (Nat.max Na Nb). intros n Hn.
    apply Qlt_to_QltT.
    (* real_min_proj is a QeqT-face equation (Id carrier); rewrite needs the
       Qeq setoid face -- bridge one layer per the S07 real_abs_proj idiom *)
    rewrite (qeqT_imp_qeq _ _ (real_min_proj a b n)).
    assert (Han : NatLe Na n).
    { apply NatLe_lift. apply Nat.le_trans with (Nat.max Na Nb).
      - apply Nat.le_max_l.
      - exact (NatLe_drop _ _ Hn). }
    assert (Hbn : NatLe Nb n).
    { apply NatLe_lift. apply Nat.le_trans with (Nat.max Na Nb).
      - apply Nat.le_max_r.
      - exact (NatLe_drop _ _ Hn). }
    pose proof (QltT_to_Qlt _ _ (HNa n Han)) as Q1.
    pose proof (QltT_to_Qlt _ _ (HNb n Hbn)) as Q2.
    assert (Ml : Qle (Qmin ea eb) ea) by apply Q.le_min_l.
    assert (Mr : Qle (Qmin ea eb) eb) by apply Q.le_min_r.
    (* strict-bound flip: ea < a_n - p_n gives ea + p_n < a_n (Qlt_minus_iff plus a ring identity) *)
    assert (Q1r : ea + projT1 p n < projT1 a n).
    { apply (proj2 (Qlt_minus_iff (ea + projT1 p n) (projT1 a n))).
      assert (Hj1 : (projT1 a n - (ea + projT1 p n) ==
                     projT1 a n - projT1 p n - ea)%Q)
        by (unfold Qminus; ring).
      rewrite Hj1.
      apply (proj1 (Qlt_minus_iff ea (projT1 a n - projT1 p n))).
      exact Q1. }
    assert (Q2r : eb + projT1 p n < projT1 b n).
    { apply (proj2 (Qlt_minus_iff (eb + projT1 p n) (projT1 b n))).
      assert (Hj2 : (projT1 b n - (eb + projT1 p n) ==
                     projT1 b n - projT1 p n - eb)%Q)
        by (unfold Qminus; ring).
      rewrite Hj2.
      apply (proj1 (Qlt_minus_iff eb (projT1 b n - projT1 p n))).
      exact Q2. }
    (* lower-bound shift: e + p_n <= ea + p_n < a_n and e + p_n <= eb + p_n < b_n
       (Qle_lt_trans with all middle arguments explicit + the two-premise form
       of Qplus_le_compat) *)
    assert (Qa : Qmin ea eb + projT1 p n < projT1 a n).
    { apply (Qle_lt_trans (Qmin ea eb + projT1 p n)
               (ea + projT1 p n) (projT1 a n)).
      - apply Qplus_le_compat.
        + exact Ml.
        + apply Qle_refl.
      - exact Q1r. }
    assert (Qb : Qmin ea eb + projT1 p n < projT1 b n).
    { apply (Qle_lt_trans (Qmin ea eb + projT1 p n)
               (eb + projT1 p n) (projT1 b n)).
      - apply Qplus_le_compat.
        + exact Mr.
        + apply Qle_refl.
      - exact Q2r. }
    assert (Hmin : Qmin ea eb + projT1 p n
                     < Qmin (projT1 a n) (projT1 b n))
      by (apply Q.min_glb_lt; assumption).
    (* flip back to the witness form: e < Qmin - p_n iff 0 < Qmin - p_n - e iff 0 < Qmin - (e + p_n) *)
    apply (proj2 (Qlt_minus_iff (Qmin ea eb)
              (Qmin (projT1 a n) (projT1 b n) - projT1 p n))).
    assert (Hj : (Qmin (projT1 a n) (projT1 b n) - projT1 p n
                    - Qmin ea eb ==
                  Qmin (projT1 a n) (projT1 b n)
                    - (Qmin ea eb + projT1 p n))%Q)
      by (unfold Qminus; ring).
    rewrite Hj.
    apply (proj1 (Qlt_minus_iff (Qmin ea eb + projT1 p n)
                   (Qmin (projT1 a n) (projT1 b n)))).
    exact Hmin.
Qed.

(* statement 8 (main statement): the min lower-bound lattice law: c <=_B a and
   c <=_B b give c <=_B min a b.
   Asymmetry with statement 5: the eps slack hangs outside the min (the goal
   is c < min a b + eps) and the conclusion position of statement 7 has no
   eps position, so the one-step one-closure combiner is unreachable -- the
   full pointwise proof runs: both premises take the same eps, the
   real_plus_proj reshape moves to the a_n + eps_n side, the Qmin lower-bound
   shift (Qopp_le_compat) precedes the Q.min_dec branch closure (after the
   branch the goal is exactly a ready-made strict bound of the left or right
   branch). *)
Lemma latb_min_le_b : forall c a b : Real,
  real_le_b c a -> real_le_b c b -> real_le_b c (real_min a b).
Proof.
  intros c a b Hca Hcb.
  unfold real_le_b. intros eps Heps.
  pose proof (Hca eps Heps) as L1.
  pose proof (Hcb eps Heps) as L2.
  destruct L1 as [ea [Hea [Na HNa]]].
  destruct L2 as [eb [Heb [Nb HNb]]].
  exists (Qmin ea eb). split.
  - apply Qlt_to_QltT.
    destruct (Q.min_dec ea eb) as [E | E].
    + rewrite E. apply QltT_to_Qlt. exact Hea.
    + rewrite E. apply QltT_to_Qlt. exact Heb.
  - exists (Nat.max Na Nb). intros n Hn.
    apply Qlt_to_QltT.
    rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_min a b) eps n)).
    (* real_min_proj is a QeqT-face equation (Id carrier); rewrite needs the
       Qeq setoid face -- bridge one layer per the S07 real_abs_proj idiom *)
    rewrite (qeqT_imp_qeq _ _ (real_min_proj a b n)).
    assert (Han : NatLe Na n).
    { apply NatLe_lift. apply Nat.le_trans with (Nat.max Na Nb).
      - apply Nat.le_max_l.
      - exact (NatLe_drop _ _ Hn). }
    assert (Hbn : NatLe Nb n).
    { apply NatLe_lift. apply Nat.le_trans with (Nat.max Na Nb).
      - apply Nat.le_max_r.
      - exact (NatLe_drop _ _ Hn). }
    (* strict-bound flip: ea < (a + eps)_n - c_n gives c_n < (a + eps)_n - ea (Qlt_minus_iff plus a ring identity) *)
    assert (Q1 : projT1 c n < projT1 a n + projT1 eps n - ea).
    { rewrite <- (qeqT_imp_qeq _ _ (real_plus_proj a eps n)).
      apply (proj2 (Qlt_minus_iff (projT1 c n)
                (projT1 (real_plus a eps) n - ea))).
      assert (Hj1 : (projT1 (real_plus a eps) n - ea - projT1 c n ==
                     projT1 (real_plus a eps) n - projT1 c n - ea)%Q)
        by (unfold Qminus; ring).
      rewrite Hj1.
      apply (proj1 (Qlt_minus_iff ea
                (projT1 (real_plus a eps) n - projT1 c n))).
      apply QltT_to_Qlt. exact (HNa n Han). }
    assert (Q2 : projT1 c n < projT1 b n + projT1 eps n - eb).
    { rewrite <- (qeqT_imp_qeq _ _ (real_plus_proj b eps n)).
      apply (proj2 (Qlt_minus_iff (projT1 c n)
                (projT1 (real_plus b eps) n - eb))).
      assert (Hj2 : (projT1 (real_plus b eps) n - eb - projT1 c n ==
                     projT1 (real_plus b eps) n - projT1 c n - eb)%Q)
        by (unfold Qminus; ring).
      rewrite Hj2.
      apply (proj1 (Qlt_minus_iff eb
                (projT1 (real_plus b eps) n - projT1 c n))).
      apply QltT_to_Qlt. exact (HNb n Hbn). }
    assert (Ml : Qle (Qmin ea eb) ea) by apply Q.le_min_l.
    assert (Mr : Qle (Qmin ea eb) eb) by apply Q.le_min_r.
    (* flip back to the c_n-left configuration: e < X - c_n iff 0 < X - c_n - e iff 0 < X - e - c_n iff c_n < X - e *)
    apply (proj2 (Qlt_minus_iff (Qmin ea eb)
              (Qmin (projT1 a n) (projT1 b n) + projT1 eps n
                - projT1 c n))).
    assert (Hj : (Qmin (projT1 a n) (projT1 b n) + projT1 eps n
                    - projT1 c n - Qmin ea eb ==
                  Qmin (projT1 a n) (projT1 b n) + projT1 eps n
                    - Qmin ea eb - projT1 c n)%Q)
      by (unfold Qminus; ring).
    rewrite Hj.
    apply (proj1 (Qlt_minus_iff (projT1 c n)
              (Qmin (projT1 a n) (projT1 b n) + projT1 eps n
                - Qmin ea eb))).
    destruct (Q.min_dec (projT1 a n) (projT1 b n)) as [EM | EM].
    + rewrite EM.
      apply (Qlt_le_trans _ (projT1 a n + projT1 eps n - ea) _ Q1).
      unfold Qminus. apply Qplus_le_compat.
      * apply Qle_refl.
      * apply Qopp_le_compat. exact Ml.
    + rewrite EM.
      apply (Qlt_le_trans _ (projT1 b n + projT1 eps n - eb) _ Q2).
      unfold Qminus. apply Qplus_le_compat.
      * apply Qle_refl.
      * apply Qopp_le_compat. exact Mr.
Qed.

(* statement 9: the lower-bound lattice law left: min a b <=_B a (a free lemma:
   real_min_le_l_B at UpRealLeB L396 has exactly the signature
   forall a b, real_le_b (real_min a b) a, connected verbatim). *)
Lemma latb_min_le_l : forall a b : Real, real_le_b (real_min a b) a.
Proof. intros a b. exact (real_min_le_l_B a b). Qed.

(* statement 10: the lower-bound lattice law right: min a b <=_B b (a free
   lemma: real_min_le_r_B at UpRealLeB L403, connected directly). *)
Lemma latb_min_le_r : forall a b : Real, real_le_b (real_min a b) b.
Proof. intros a b. exact (real_min_le_r_B a b). Qed.

(* statement 11: the trans assembly lemma: a <=_B c gives min a b <=_B c.
   real_le_b_trans at UpRealLeB2 (signature forall x y z, real_le_b x y ->
   real_le_b y z -> real_le_b x z) plus statement 9, assembled in two
   steps. *)
Lemma latb_min_le_le : forall a b c : Real,
  real_le_b a c -> real_le_b (real_min a b) c.
Proof.
  intros a b c H. apply (real_le_b_trans (real_min a b) a c).
  - apply real_min_le_l_B.
  - exact H.
Qed.

(* ============================================================ *)
(* 5. the assumption audit (every statement Closed, printed below) *)
(* ============================================================ *)

Print Assumptions latb_min_glb.
Print Assumptions latb_min_le_b.
Print Assumptions latb_min_le_l.
Print Assumptions latb_min_le_r.
Print Assumptions latb_min_le_le.

(* ============================================================ *)
(* 6. interconnection with the base strict order: real_lt x y implies
   latb_lt_b x y (one direction only; the reverse direction, latb_lt_b
   implies real_lt, is out of scope).
   The base strict order real_lt is the Cauchy-chase form: there are eps > 0
   and N with eps < y_n - x_n for all n >= N; latb_lt_b asks for delta > 0
   with x <=_B y + (- delta).
   Proof route: the real_lt witness (eps, N) is the eventual-separation
   window.  The positive Real delta is set to real_const eps with positivity
   witness eps * (1/2) over the constant-sequence window N := 0; the
   positivity half-quantity identity eps - eps * (1/2) == eps * (1 - 1/2) is
   a ring polynomial identity plus the closed computation 1 - 1/2 == 1/2 --
   the / of Q is a separate Qdiv operator that ring treats as an
   unabstractable function symbol, so division-containing expressions in
   variables must first be put in multiplicative form.  For the main part,
   given any positive e, take its sigT first component e0 as the slack
   (positivity comes free); the windows intersect at N := max N N0: the
   separation window flips through Qlt_minus_iff to 0 < y_n - x_n + (-eps),
   the chase window gives e0 < e_n (real_zero simplifies pointwise), and
   Qplus_lt_compat merges to 0 + e0 < (y_n - x_n + (-eps)) + e_n, reshaped by
   ring identities back into the real_lt witness position (pointwise
   expansions by real_plus_proj, real_opp_proj, real_const_proj). *)
(* ============================================================ *)

Lemma latb_real_lt_interconnect : forall x y : Real,
  real_lt x y -> latb_lt_b x y.
Proof.
  intros x y H.
  destruct H as [eps [Heps0 [N HN]]].
  pose proof (QltT_to_Qlt _ _ Heps0) as HepsQ.
  assert (Hhalf : Qlt 0 (1 / 2)).
  { vm_compute. reflexivity. }
  assert (Hhalf_eps : Qlt 0 (eps * (1 / 2))).
  { assert (Hz2 : (0 * (1 / 2) == 0)%Q) by (unfold Qminus; ring).
    rewrite <- Hz2.
    exact (proj2 (Qmult_lt_r 0 eps (1 / 2) Hhalf) HepsQ). }
  exists (real_const eps). split.
  - (* delta positivity: witness eps * (1/2) over the constant-sequence window N := 0 *)
    exists (eps * (1 / 2)). split.
    + apply Qlt_to_QltT. exact Hhalf_eps.
    + exists O. intros n Hn.
      apply Qlt_to_QltT.
      rewrite (qeqT_imp_qeq _ _ (real_const_proj eps n)).
      assert (Hzp : projT1 real_zero n == 0) by reflexivity.
      rewrite Hzp.
      assert (Hj : (eps - 0 == eps)%Q) by (unfold Qminus; ring).
      rewrite Hj.
      apply (proj2 (Qlt_minus_iff (eps * (1 / 2)) eps)).
      assert (Hj2 : (eps + - (eps * (1 / 2)) == eps * (1 - (1 / 2)))%Q)
        by (unfold Qminus; ring).
      rewrite Hj2.
      assert (Hc : (1 - (1 / 2) == 1 / 2)%Q) by (vm_compute; reflexivity).
      rewrite Hc.
      exact Hhalf_eps.
  - (* main part: x <=_B y + (- delta) closed eps-wise *)
    unfold real_le_b. intros e He.
    destruct He as [e0 [He0pos [N0 HN0]]].
    exists e0. split.
    + exact He0pos.
    + exists (Nat.max N N0). intros n Hn.
      apply Qlt_to_QltT.
      (* real_plus_proj/real_opp_proj are QeqT-face equations; rewrite
         needs the Qeq setoid face -- bridge one layer, S07 idiom *)
      rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_plus y (real_opp (real_const eps))) e n)).
      rewrite (qeqT_imp_qeq _ _ (real_plus_proj y (real_opp (real_const eps)) n)).
      rewrite (qeqT_imp_qeq _ _ (real_opp_proj (real_const eps) n)).
      rewrite (qeqT_imp_qeq _ _ (real_const_proj eps n)).
      assert (HnN : NatLe N n).
      { apply NatLe_lift. apply Nat.le_trans with (Nat.max N N0).
        - apply Nat.le_max_l.
        - exact (NatLe_drop _ _ Hn). }
      assert (HnN0 : NatLe N0 n).
      { apply NatLe_lift. apply Nat.le_trans with (Nat.max N N0).
        - apply Nat.le_max_r.
        - exact (NatLe_drop _ _ Hn). }
      assert (Hzn : projT1 real_zero n == 0) by reflexivity.
      pose proof (QltT_to_Qlt _ _ (HN0 n HnN0)) as HB.
      rewrite Hzn in HB.
      assert (Hj3 : (projT1 e n - 0 == projT1 e n)%Q) by (unfold Qminus; ring).
      rewrite Hj3 in HB.
      pose proof (QltT_to_Qlt _ _ (HN n HnN)) as Q1.
      assert (HP : 0 < projT1 y n - projT1 x n + - eps).
      { apply (proj1 (Qlt_minus_iff eps (projT1 y n - projT1 x n))).
        exact Q1. }
      assert (Hfin : 0 + e0 < projT1 y n - projT1 x n + - eps + projT1 e n).
      { apply Qplus_lt_compat.
        - exact HP.
        - exact HB. }
      assert (Hj1 : (0 + e0 == e0)%Q) by (apply Qplus_0_l).
      rewrite Hj1 in Hfin.
      assert (Hj4 : (projT1 y n - projT1 x n + - eps + projT1 e n ==
                     projT1 y n + - eps + projT1 e n - projT1 x n)%Q)
        by (unfold Qminus; ring).
      rewrite Hj4 in Hfin.
      exact Hfin.
Qed.

Print Assumptions latb_real_lt_interconnect.
