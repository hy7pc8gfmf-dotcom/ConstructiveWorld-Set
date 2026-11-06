(* ConstructiveWorld-Set -- strict-lt primitive and max/min lattice laws for the B-face order. *)

(** * UpReqLatticeB: strict-lt primitive and max/min-side lattice laws.

    Mission.  Formalizes the B-face lattice section of the up-completed real
      line: the strict-order primitive [latb_lt_b], the connectors
      [latb_lt_b_to_le_b] / [latb_real_lt_to_le_b], the max-side laws
      [latb_lt_max_intro] / [latb_max_le_b] / [latb_max_le_r], the min-side
      duals [latb_min_glb] / [latb_min_le_b] / [latb_min_le_l] /
      [latb_min_le_r] / [latb_min_le_le], and [latb_real_lt_interconnect].

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qring], [QArith.Qminmax],
      [Arith.PeanoNat].  Requires [S01_BaseRing], [S02_CauchyComplete],
      [S03_QExp], [S04_RealExpLogConv], [S05_AlignmentGRPO],
      [S06_DiffSamplingGibbs], [S07_RealSetoidExpLog], [S08_RealMainlineDPO],
      [S09_EntropyReal], [S10_KVQuantTrig], [S11_TP3B5], [S12_B5RecycleSF],
      [S13_NLiveAudit], [S14_B5BatchBlock], [S15_TailFEPUp], [UpRealLeB],
      [UpRealLeB2], [UpRealLeB3] of this development.

    References.  This development, UpReqLatticeB.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" UpReqLatticeB.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 00015ff4]. *)
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
(* Section 1. The strict-lt primitive and the ≤_B connectors.   *)
(* ============================================================ *)

(* Item 1: the Bishop-style strict-order primitive x <ᴮ y, read as
   exists d > 0 with x ≤_B y + (-d).  The sigT + And shape mirrors the
   real_lt witness form as a Set-level package; the margin clause is
   carried by [real_le_b], so no Prop appears on the statement face. *)
Definition latb_lt_b (x y : Real) : Set :=
  sigT (fun d : Real => And (real_lt real_zero d)
                            (real_le_b x (real_plus y (real_opp d)))).

(* Item 2: connector from the strict form to ≤_B: x ≤_B y - d with d > 0
   gives x ≤_B (y - d) + d == y.  The proof adds the positive d on the
   right by the right-addition transport for nonneg amounts, then
   reshapes along the associativity, cancellation and additive-unit
   identity chain. *)
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

(* Item 3: connector from the strict order to ≤_B: real_lt is exactly
   the left branch of the Or form, so the one-way bridge closes in one
   step. *)
Lemma latb_real_lt_to_le_b : forall x y : Real,
  real_lt x y -> real_le_b x y.
Proof.
  intros x y H. apply real_le_to_le_b. unfold real_le. left. exact H.
Qed.

(* ============================================================ *)
(* Section 2. Max-side combinators, via the real_max_proj channel to    *)
(*   the Q layer.                                                       *)
(* ============================================================ *)

(* Item 4: strict upper-bound introduction: a < d and b < d give
   max a b < d.  The witness eps is set to Qmin ea eb (positivity by the
   Q.min_dec branch) and N to max Na Nb; after the pointwise reduction
   through the real_max_proj channel, the a_n < d_n - Qmin ≤ d_n - ea
   side and the b_n side reshape by Qopp_le_compat and Qplus_le_compat,
   Q.max_lub_lt closes Qmax in one step, and the final segment reshapes
   along the Qlt_minus_iff and ring identities. *)
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
    (* strict-bound flip: ea < d_n - a_n gives a_n < d_n - ea
       (Qlt_minus_iff plus ring identities). *)
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

(* Item 5 (main): the max upper-bound lattice law: a ≤_B c and b ≤_B c
   give max a b ≤_B c.  For eps > 0 both premises take d := c + eps, and
   Item 4 gives the strict max a b < c + eps in one step; the Or left
   branch enters the exact face and the one completer closes in a single
   step.  The constructive branch-choice difficulty of the weak face has
   no counterpart on the strict witness face, so no eps/2 split is
   needed. *)
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

(* Item 6: absorption instance: a ≤_B b gives max a b ≤_B b
   (Item 5 plus reflexivity of ≤_B). *)
Lemma latb_max_le_r : forall a b : Real,
  real_le_b a b -> real_le_b (real_max a b) b.
Proof.
  intros a b H. apply (latb_max_le_b a b b H).
  apply leb3_le_b_refl.
Qed.

(* ============================================================ *)
(* Section 3. Assumption audit (every statement Closed under the        *)
(*   global context).                                                   *)
(* ============================================================ *)

Print Assumptions latb_lt_b.
Print Assumptions latb_lt_b_to_le_b.
Print Assumptions latb_real_lt_to_le_b.
Print Assumptions latb_lt_max_intro.
Print Assumptions latb_max_le_b.
Print Assumptions latb_max_le_r.

(* ============================================================ *)
(* Section 4. Min-side combinators: the dual primitive, the lower-bound *)
(*   lattice laws and the glb main law.                                 *)
(*                                                                      *)
(* Five items.  7 [latb_min_glb], strict lower-bound introduction       *)
(*   (Q-layer channel: the Qmin witness with the pointwise              *)
(*   Q.min_glb_lt connection; the strict-bound shift e + p_n < a_n      *)
(*   goes through Qle_lt_trans and Qplus_le_compat; the return margin   *)
(*   flip follows the Qlt_minus_iff pattern).  8 [latb_min_le_b], the   *)
(*   min lower-bound lattice law (c ≤_B a and c ≤_B b give c ≤_B        *)
(*   min a b); unlike the max-side law, the eps margin sits outside     *)
(*   the min, so the one completer cannot close in one step (on the     *)
(*   max side the eps sits inside the latb_lt_max_intro conclusion);    *)
(*   the proof runs the full pointwise argument: real_plus_proj         *)
(*   reshaping, the Qmin lower-bound shift and the Q.min_dec branch.    *)
(*   9 [latb_min_le_l], left lower-bound law (free item:                *)
(*   real_min_le_l_B connects verbatim).  10 [latb_min_le_r], right     *)
(*   lower-bound law (real_min_le_r_B connects verbatim).               *)
(*   11 [latb_min_le_le], the transitivity assembly (real_le_b_trans    *)
(*   plus Item 9 in two steps: min a b ≤_B a ≤_B c gives                *)
(*   min a b ≤_B c).                                                    *)
(*                                                                      *)
(* Discipline as in the earlier section: the statement face stays       *)
(*   entirely at the Set level (the real_lt sigT witness form and the   *)
(*   real_le_b forall form, no Prop on the face); the premise face      *)
(*   adds nothing new; every statement closes by a real proof, no       *)
(*   downgrade.                                                         *)

(* Item 7: strict lower-bound introduction: p < a and p < b give
   p < min a b.  The witness e is set to Qmin ea eb (positivity by the
   Q.min_dec branch) and N to max Na Nb; after the pointwise reduction
   through the real_min_proj channel, ea < a_n - p_n flips to
   ea + p_n < a_n, the shift e + p_n ≤ ea + p_n (two Qle_lt_trans steps)
   gives e + p_n < a_n and e + p_n < b_n, Q.min_glb_lt closes Qmin in
   one step, and the final segment flips back along the Qlt_minus_iff
   and ring identities to the real_lt witness form e < Qmin - p_n. *)
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
    (* strict-bound flip: ea < a_n - p_n gives ea + p_n < a_n
       (Qlt_minus_iff plus ring identities). *)
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
    (* lower-bound shift: e + p_n ≤ ea + p_n < a_n and
       e + p_n ≤ eb + p_n < b_n (Qle_lt_trans with the middle term given
       explicitly and Qplus_le_compat in its two-premise form). *)
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
    (* flip back to the witness form: e < Qmin - p_n iff
       0 < Qmin - p_n - e iff 0 < Qmin - (e + p_n). *)
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

(* Item 8 (main): the min lower-bound lattice law: c ≤_B a and c ≤_B b
   give c ≤_B min a b.  The asymmetry with Item 5: the eps margin sits
   outside the min (goal c < min a b + eps), and the Item 7 conclusion
   has no eps slot, so the one completer cannot close in one step; the
   proof runs the full pointwise argument: both premises take the same
   eps, real_plus_proj reshapes to the a_n + eps_n side, and after the
   Qmin lower-bound shift (Qopp_le_compat) the Q.min_dec branch closes
   (after the branch the goal is exactly the ready strict bound of the
   left or right branch). *)
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
    rewrite (qeqT_imp_qeq _ _ (real_min_proj a b n)).
    assert (Han : NatLe Na n).
    { apply NatLe_lift. apply Nat.le_trans with (Nat.max Na Nb).
      - apply Nat.le_max_l.
      - exact (NatLe_drop _ _ Hn). }
    assert (Hbn : NatLe Nb n).
    { apply NatLe_lift. apply Nat.le_trans with (Nat.max Na Nb).
      - apply Nat.le_max_r.
      - exact (NatLe_drop _ _ Hn). }
    (* strict-bound flip: ea < (a + eps)_n - c_n gives
       c_n < (a + eps)_n - ea (Qlt_minus_iff plus ring). *)
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
    (* flip back with c_n on the left: e < X - c_n iff 0 < X - c_n - e
       iff 0 < X - e - c_n iff c_n < X - e. *)
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

(* Item 9: left lower-bound law: min a b ≤_B a (free item: the library
   real_min_le_l_B of UpRealLeB, with signature
   forall a b, real_le_b (real_min a b) a, connects verbatim). *)
Lemma latb_min_le_l : forall a b : Real, real_le_b (real_min a b) a.
Proof. intros a b. exact (real_min_le_l_B a b). Qed.

(* Item 10: right lower-bound law: min a b ≤_B b (free item: the
   library real_min_le_r_B of UpRealLeB has the same shape and connects
   verbatim). *)
Lemma latb_min_le_r : forall a b : Real, real_le_b (real_min a b) b.
Proof. intros a b. exact (real_min_le_r_B a b). Qed.

(* Item 11: transitivity assembly: a ≤_B c gives min a b ≤_B c.
   real_le_b_trans of UpRealLeB2, with signature
   forall x y z, real_le_b x y -> real_le_b y z -> real_le_b x z,
   assembles with Item 9 in two steps. *)
Lemma latb_min_le_le : forall a b c : Real,
  real_le_b a c -> real_le_b (real_min a b) c.
Proof.
  intros a b c H. apply (real_le_b_trans (real_min a b) a c).
  - apply real_min_le_l_B.
  - exact H.
Qed.

(* ============================================================ *)
(* Section 5. Assumption audit for the min side (every statement        *)
(*   Closed under the global context).                                  *)
(* ============================================================ *)

Print Assumptions latb_min_glb.
Print Assumptions latb_min_le_b.
Print Assumptions latb_min_le_l.
Print Assumptions latb_min_le_r.
Print Assumptions latb_min_le_le.

(* ============================================================ *)
(* Section 6. Interconnect with the base strict order (latb_lt_b from   *)
(*   real_lt).                                                          *)
(*                                                                      *)
(* Goal statement: real_lt x y gives latb_lt_b x y, connecting the      *)
(*   base strict order (real_lt, the Cauchy-sequence form: exists       *)
(*   eps > 0, exists N, forall n >= N, eps < y_n - x_n) into latb_lt_b  *)
(*   (exists d > 0, x ≤_B y + (-d)).  One direction only: the reverse   *)
(*   (latb_lt_b giving real_lt) is out of scope.                        *)
(*                                                                      *)
(* Method: the real_lt witness (eps, N) states eventual separation, so  *)
(*   take N := 0; the positivity half uses the identity                 *)
(*   eps - eps * (1/2) == eps * (1 - 1/2) in ring polynomial form plus  *)
(*   the closed computation 1 - 1/2 == 1/2 (division in Q is a separate *)
(*   Qdiv operator, opaque to ring, so a division involving a variable  *)
(*   must first be rewritten in multiplicative form); the main part     *)
(*   shows, for every n >= max N N0,                                    *)
(*   0 + e0 < (y_n - x_n + (-eps)) + e_n, reshaped by ring identities   *)
(*   back to the real_lt witness slots (pointwise unfolding by          *)
(*   real_plus_proj, real_opp_proj and real_const_proj).                *)
(*                                                                      *)
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
  - 
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
  - (* main part: x ≤_B y + (-d) established for every margin e. *)
    unfold real_le_b. intros e He.
    destruct He as [e0 [He0pos [N0 HN0]]].
    exists e0. split.
    + exact He0pos.
    + exists (Nat.max N N0). intros n Hn.
      apply Qlt_to_QltT.
      rewrite (qeqT_imp_qeq _ _
                (real_plus_proj (real_plus y (real_opp (real_const eps))) e n)).
      rewrite (qeqT_imp_qeq _ _
                (real_plus_proj y (real_opp (real_const eps)) n)).
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
