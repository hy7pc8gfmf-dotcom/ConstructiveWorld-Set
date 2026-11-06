(* ConstructiveWorld-Set -- pointwise B-absorption of the absolute value and triangle inequalities over abstract summation slots. *)

(** * UpAblS06AbsFeed: pointwise absolute-value absorption and the summation triangle over an abstract slot interface.

    Mission.  Pointwise B-absorption for the absolute value and the triangle
      inequality over an abstract summation slot: [|x| >=_B x] and
      [|x| >=_B -x], the two-sided sandwich [uabS4c_abs_le_b_two_sided], the
      B-form transports [uabS4c_leb_req_left] and [uabS4c_leb_opp_anti], and
      the SumOver interface theorem [uabS4c_abs_sum_le_B_slot] with instance
      [uabS4c_slot_pair_B] and supply [s6f_abs_kernel_bound_slot].

    Dependencies.  Stdlib [List], [Lia], [Lqa], [QArith.Qring], [QArith.Qabs],
      [QArith.Qminmax].  Requires [S01_BaseRing], [S02_CauchyComplete],
      [S03_QExp], [S04_RealExpLogConv], [S05_AlignmentGRPO],
      [S06_DiffSamplingGibbs], [S07_RealSetoidExpLog], [S08_RealMainlineDPO],
      [S09_EntropyReal], [S10_KVQuantTrig], [S11_TP3B5], [S12_B5RecycleSF],
      [S13_NLiveAudit], [S14_B5BatchBlock], [S15_TailFEPUp], [UpRealLeB],
      [UpAblAbsSumLeB] of this development.

    References.  This development, UpAblS06AbsFeed.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" UpAblS06AbsFeed.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 00015ff4]. *)
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Lqa.
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
Require Import UpAblAbsSumLeB.

(* ================= Section 1. the uabS4c_q_abs_ge_l family ================= *)
From Stdlib Require Import QArith.Qring QArith.Qabs QArith.Qminmax.

(* Section 0. interface inventory of the development (each Check against its real signature) *)

Check real_le_b.              (* the Bishop form of <=, the strongest reachable order predicate *)
Check real_le_to_le_b.        (* one-way bridge from the Or form to the B form *)
Check real_abs.               (* pointwise Qabs *)
Check real_abs_proj.          (* pointwise projection *)
Check real_eps_witness.       (* positive rational witness with the built-in half margin *)
Check q_abs_lt_two_sided.     (* two-sided sandwich at the Q layer, same core mechanism *)
Check Qlt_le_dec.             (* decidable sign and order on Q (no classical logic) *)
Check real_plus_proj.
Check real_opp_proj.
Check real_mult_proj.
Check real_const_proj.
Check real_eq_of_zero_diff.   (* pointwise zero difference implies real_eq *)
Check RealSetoid.real_eq_plus_compat.
Check real_plus_assoc.
Check real_plus_comm.
Check real_plus_zero.
Check real_plus_opp.
Check real_mult_comm.
Check real_mult_one.
Check RealSetoid.real_lt_le_iff_req.
Check real_le_plus_compat.
Check uabS4_le_add_r.               (* positive-margin right absorption supplied by [UpAblAbsSumLeB] *)
Check uabS4_abs_diff_triangle_le_eps. (* [UpAblAbsSumLeB] A.1: two-point kernel-difference form, pointwise-eps shape *)
Check uabS4_abs_diff_triangle_le_B.   (* [UpAblAbsSumLeB] A.2: two-point kernel-difference form, B shape *)
Check uabS4_abs_sum_le_B_pair.        (* [UpAblAbsSumLeB] A.3: two-point instance, B shape *)
Check uabS4_cons_glue.                (* the induction-step lemma of [UpAblAbsSumLeB] ([uabS4_cons_glue]) *)
Check uabS4_lt_double_margin_le_half_contr. (* [UpAblAbsSumLeB] C.1: the doubled margin cannot coexist with the bound *)
Check real_list_sum.                  (* list folding, universally quantified over the element type *)

(* Section 1. Real-layer basic lemmas (pointwise B absorption, two-sided sandwich, *)
(*   half construction, compatibility pairs)                                *)

(* A.0 at the Q layer: u <= |u| ([Qlt_le_dec] sign decision, decidable on Q  *)
(*   without classical logic)                                                *)
Lemma uabS4c_q_abs_ge_l : forall u : Q, Qle u (Qabs u).
Proof.
  intros u. destruct (Qlt_le_dec u 0) as [Hlt | Hge].
  - assert (Habs : Qabs u == - u) by (apply Qabs_neg; apply Qlt_le_weak; exact Hlt).
    rewrite Habs.
    (* negative branch: for u < 0 the goal is u <= -u.  After the explicit  *)
    (*   num/den decomposition, multiplication monotonicity                 *)
    (*   [Z.mul_le_mono_nonneg_r] with a nonnegative right factor reduces   *)
    (*   the goal to nu <= -nu, and [Z.le_trans] composes nu <= 0 <= -nu,   *)
    (*   the right segment coming from the antitone [Z.opp_le_mono]         *)
    (*   applied to nu <= 0.                                                *)
    destruct u as [nu du]. unfold Qle, Qopp. cbn [Qnum Qden].
    unfold Qlt in Hlt. cbn [Qnum Qden] in Hlt.
    rewrite Z.mul_1_r, Z.mul_0_l in Hlt.
    apply Z.mul_le_mono_nonneg_r.
    + apply Z.lt_le_incl. apply Pos2Z.is_pos.
    + apply (Z.le_trans nu 0 (- nu)).
      * apply Z.lt_le_incl. exact Hlt.
      * exact (proj1 (Z.opp_le_mono nu 0) (Z.lt_le_incl nu 0 Hlt)).
  - assert (Habs : Qabs u == u) by (apply Qabs_pos; exact Hge).
    rewrite Habs. apply Qle_refl.
Qed.

(* A.1 at the Q layer: -u <= |u| *)
Lemma uabS4c_q_abs_ge_opp : forall u : Q, Qle (- u) (Qabs u).
Proof.
  intros u. destruct (Qlt_le_dec u 0) as [Hlt | Hge].
  - assert (Habs : Qabs u == - u) by (apply Qabs_neg; apply Qlt_le_weak; exact Hlt).
    rewrite Habs. apply Qle_refl.
  - assert (Habs : Qabs u == u) by (apply Qabs_pos; exact Hge).
    rewrite Habs.
    (* nonnegative branch: for 0 <= u the goal is -u <= u.  After the       *)
    (*   explicit num/den decomposition, multiplication monotonicity        *)
    (*   [Z.mul_le_mono_nonneg_r] with a nonnegative right factor reduces   *)
    (*   the goal to -nu <= nu, and [Z.le_trans] composes -nu <= 0 <= nu,   *)
    (*   the left segment coming from the antitone [Z.opp_le_mono]          *)
    (*   applied to 0 <= nu.                                                *)
    destruct u as [nu du]. unfold Qle, Qopp. cbn [Qnum Qden].
    unfold Qle in Hge. cbn [Qnum Qden] in Hge.
    rewrite Z.mul_0_l, Z.mul_1_r in Hge.
    apply Z.mul_le_mono_nonneg_r.
    + apply Z.lt_le_incl. apply Pos2Z.is_pos.
    + apply (Z.le_trans (- nu) 0 nu).
      * exact (proj1 (Z.opp_le_mono 0 nu) Hge).
      * exact Hge.
Qed.

(* A.2 pointwise B absorption, positive side: x <=_B |x|; pointwise          *)
(*   Qabs(u_n) >= u_n with the positive witness of the built-in half margin. *)
Lemma uabS4c_abs_ge_l_b : forall x : Real, real_le_b x (real_abs x).
Proof.
  intros x eps Heps.
  destruct (real_eps_witness eps Heps) as [eps0 [Heps0 [N0 HN0]]].
  unfold real_lt. exists (eps0 / 2)%Q. split.
  - apply Qlt_to_QltT. apply Qlt_shift_div_l.
    + reflexivity.
    + simpl. apply QltT_to_Qlt. exact Heps0.
  - exists N0. intros n Hn.
    apply Qlt_to_QltT.
    setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_abs x) eps n)).
    setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj x n)).
    assert (Hq0 : Qlt (eps0 / 2) (projT1 eps n))
      by (apply QltT_to_Qlt; exact (HN0 n Hn)).
    assert (Hge : Qle (projT1 x n) (Qabs (projT1 x n))) by apply uabS4c_q_abs_ge_l.
    lra.
Qed.

(* A.3 pointwise B absorption, negative side: -x <=_B |x|; pointwise         *)
(*   Qabs(u_n) >= -u_n.                                                      *)
Lemma uabS4c_abs_ge_opp_b : forall x : Real, real_le_b (real_opp x) (real_abs x).
Proof.
  intros x eps Heps.
  destruct (real_eps_witness eps Heps) as [eps0 [Heps0 [N0 HN0]]].
  unfold real_lt. exists (eps0 / 2)%Q. split.
  - apply Qlt_to_QltT. apply Qlt_shift_div_l.
    + reflexivity.
    + simpl. apply QltT_to_Qlt. exact Heps0.
  - exists N0. intros n Hn.
    apply Qlt_to_QltT.
    setoid_rewrite (qeqT_imp_qeq _ _ (real_opp_proj x n)).
    setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_abs x) eps n)).
    setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj x n)).
    assert (Hq0 : Qlt (eps0 / 2) (projT1 eps n))
      by (apply QltT_to_Qlt; exact (HN0 n Hn)).
    assert (Hge : Qle (- projT1 x n) (Qabs (projT1 x n))) by apply uabS4c_q_abs_ge_opp.
    lra.
Qed.

(* A.4 core lemma: the two-sided sandwich implies the abs B form:            *)
(*   x <=_B Y and -x <=_B Y imply |x| <=_B Y.                                *)
(*   Construction: for each eps take delta = min(d1, d2) (the [Qlt_le_dec]   *)
(*   dichotomy) and decide the sign of each point by [Qabs]: on the          *)
(*   u_n >= 0 branch the positive witness d1 applies, on the u_n < 0 branch  *)
(*   the negative witness d2 applies, so each side of the sandwich carries   *)
(*   one arm; the pointwise sign dichotomy lives where Q is decidable        *)
(*   (constructivity preserved, no global sign decision).                    *)
Lemma uabS4c_abs_le_b_two_sided : forall x Y : Real,
  real_le_b x Y -> real_le_b (real_opp x) Y -> real_le_b (real_abs x) Y.
Proof.
  intros x Y H1 H2 eps Heps.
  specialize (H1 eps Heps). specialize (H2 eps Heps).
  unfold real_lt in H1, H2.
  destruct H1 as [d1 [Hd1 [N1 HN1]]]. destruct H2 as [d2 [Hd2 [N2 HN2]]].
  destruct (Qlt_le_dec d1 d2) as [Hd12 | Hd21].
  - exists d1. split. exact Hd1.
    exists (Nat.max N1 N2). intros n Hn.
    assert (Ha : NatLe N1 n).
    { apply NatLe_lift.
      assert (Hdrop : (Nat.max N1 N2 <= n)%nat) by exact (NatLe_drop _ _ Hn).
      lia. }
    assert (Hb : NatLe N2 n).
    { apply NatLe_lift.
      assert (Hdrop : (Nat.max N1 N2 <= n)%nat) by exact (NatLe_drop _ _ Hn).
      lia. }
    apply Qlt_to_QltT.
    pose proof (HN1 n Ha) as Hp1. apply QltT_to_Qlt in Hp1.
    setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj Y eps n)) in Hp1.
    pose proof (HN2 n Hb) as Hp2. apply QltT_to_Qlt in Hp2.
    setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj Y eps n)) in Hp2.
    setoid_rewrite (qeqT_imp_qeq _ _ (real_opp_proj x n)) in Hp2.
    setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj Y eps n)).
    setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj x n)).
    destruct (Qlt_le_dec (projT1 x n) 0) as [Hx | Hx].
    + assert (Habs : Qabs (projT1 x n) == - projT1 x n)
        by (apply Qabs_neg; apply Qlt_le_weak; exact Hx).
      rewrite Habs. lra.
    + assert (Habs : Qabs (projT1 x n) == projT1 x n) by (apply Qabs_pos; exact Hx).
      rewrite Habs. lra.
  - exists d2. split. exact Hd2.
    exists (Nat.max N1 N2). intros n Hn.
    assert (Ha : NatLe N1 n).
    { apply NatLe_lift.
      assert (Hdrop : (Nat.max N1 N2 <= n)%nat) by exact (NatLe_drop _ _ Hn).
      lia. }
    assert (Hb : NatLe N2 n).
    { apply NatLe_lift.
      assert (Hdrop : (Nat.max N1 N2 <= n)%nat) by exact (NatLe_drop _ _ Hn).
      lia. }
    apply Qlt_to_QltT.
    pose proof (HN1 n Ha) as Hp1. apply QltT_to_Qlt in Hp1.
    setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj Y eps n)) in Hp1.
    pose proof (HN2 n Hb) as Hp2. apply QltT_to_Qlt in Hp2.
    setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj Y eps n)) in Hp2.
    setoid_rewrite (qeqT_imp_qeq _ _ (real_opp_proj x n)) in Hp2.
    setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj Y eps n)).
    setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj x n)).
    destruct (Qlt_le_dec (projT1 x n) 0) as [Hx | Hx].
    + assert (Habs : Qabs (projT1 x n) == - projT1 x n)
        by (apply Qabs_neg; apply Qlt_le_weak; exact Hx).
      rewrite Habs. lra.
    + assert (Habs : Qabs (projT1 x n) == projT1 x n) by (apply Qabs_pos; exact Hx).
      rewrite Habs. lra.
Qed.

(* A.5 right equality transport for the B form: a = b and a <=_B Y imply     *)
(*   b <=_B Y.                                                               *)
Lemma uabS4c_leb_req_left : forall a b Y : Real,
  real_eq a b -> real_le_b a Y -> real_le_b b Y.
Proof.
  intros a b Y Hab H eps Heps.
  specialize (H eps Heps). unfold real_lt in H.
  destruct H as [d1 [Hd1 [N1 HN1]]].
  assert (Hd1q : Qlt 0 d1) by (apply QltT_to_Qlt; exact Hd1).
  assert (Hhalf : QltT 0 (d1 * (1#2))) by (apply Qlt_to_QltT; lra).
  destruct (Hab (d1 * (1#2))%Q Hhalf) as [N2 HN2].
  exists (d1 * (1#2))%Q. split.
  - exact Hhalf.
  - exists (Nat.max N1 N2). intros n Hn.
    assert (Ha : NatLe N1 n).
    { apply NatLe_lift.
      assert (Hdrop : (Nat.max N1 N2 <= n)%nat) by exact (NatLe_drop _ _ Hn).
      lia. }
    assert (Hb : NatLe N2 n).
    { apply NatLe_lift.
      assert (Hdrop : (Nat.max N1 N2 <= n)%nat) by exact (NatLe_drop _ _ Hn).
      lia. }
    apply Qlt_to_QltT.
    rewrite !(qeqT_imp_qeq _ _ (real_plus_proj _ _ _)).
    pose proof (HN1 n Ha) as Hp1. apply QltT_to_Qlt in Hp1.
    rewrite (qeqT_imp_qeq _ _ (real_plus_proj _ _ _)) in Hp1.
    assert (Hq2 : Qlt (Qabs (projT1 a n - projT1 b n)) (d1 * (1#2)))
      by (apply QltT_to_Qlt; exact (HN2 n Hb)).
    destruct (Qlt_le_dec (projT1 a n - projT1 b n) 0) as [Hwb | Hwb].
    + assert (Habs : Qabs (projT1 a n - projT1 b n) == - (projT1 a n - projT1 b n))
        by (apply Qabs_neg; apply Qlt_le_weak; exact Hwb).
      rewrite Habs in Hq2.
      assert (Hw2 : projT1 b n - projT1 a n == - (projT1 a n - projT1 b n)) by ring.
      rewrite <- Hw2 in Hq2.
      lra.
    + assert (Habs : Qabs (projT1 a n - projT1 b n) == projT1 a n - projT1 b n)
        by (apply Qabs_pos; exact Hwb).
      rewrite Habs in Hq2.
      lra.
Qed.

(* A.6 half construction: half e + half e = e (a pointwise ring identity via *)
(*   real_const (1#2), no [inv2] side condition needed), plus positivity of  *)
(*   half.                                                                   *)
Definition uabS4c_half (e : Real) : Real := real_mult e (real_const (1#2)).

Lemma uabS4c_half_eq : forall e : Real,
  real_eq (real_plus (uabS4c_half e) (uabS4c_half e)) e.
Proof.
  intros e. apply real_eq_of_zero_diff. intro n.
  unfold uabS4c_half.
  apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (real_plus_proj _ _ _)). rewrite (qeqT_imp_qeq _ _ (real_mult_proj _ _ _)). rewrite (qeqT_imp_qeq _ _ (real_const_proj _ _)).
  unfold Qminus. ring.
Qed.

Lemma uabS4c_half_pos : forall e : Real,
  real_lt real_zero e -> real_lt real_zero (uabS4c_half e).
Proof.
  intros e He.
  destruct (real_eps_witness e He) as [eps0 [Heps0 [N0 HN0]]].
  assert (Hq0 : Qlt 0 eps0) by (apply QltT_to_Qlt; exact Heps0).
  unfold real_lt. exists (eps0 * (1#4))%Q. split.
  - apply Qlt_to_QltT. lra.
  - exists N0. intros n Hn.
    apply Qlt_to_QltT.
    unfold uabS4c_half.
    rewrite (qeqT_imp_qeq _ _ (real_mult_proj _ _ _)). rewrite (qeqT_imp_qeq _ _ (real_const_proj _ _)).
    assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
    rewrite Hz.
    pose proof (HN0 n Hn) as Hp.
    apply QltT_to_Qlt in Hp.
    assert (Heq2 : eps0 * (1#2) == eps0 / 2) by reflexivity.
    rewrite <- Heq2 in Hp.
    lra.
Qed.

(* A.7 B-form compatibility of addition: a <=_B c and b <=_B d imply         *)
(*   a + b <=_B c + d.  This is where the half construction applies: each    *)
(*   side takes a half-margin budget and h_n + h_n coincides with eps_n      *)
(*   pointwise on Q.                                                         *)
Lemma uabS4c_leb_plus_compat : forall a b c d : Real,
  real_le_b a c -> real_le_b b d -> real_le_b (real_plus a b) (real_plus c d).
Proof.
  intros a b c d H1 H2 eps Heps.
  assert (Hh : real_lt real_zero (uabS4c_half eps)) by (apply uabS4c_half_pos; exact Heps).
  specialize (H1 (uabS4c_half eps) Hh). specialize (H2 (uabS4c_half eps) Hh).
  unfold real_lt in H1, H2.
  destruct H1 as [d1 [Hd1 [N1 HN1]]]. destruct H2 as [d2 [Hd2 [N2 HN2]]].
  assert (Hd1q : Qlt 0 d1) by (apply QltT_to_Qlt; exact Hd1).
  assert (Hd2q : Qlt 0 d2) by (apply QltT_to_Qlt; exact Hd2).
  destruct (Qlt_le_dec d1 d2) as [Hd12 | Hd21].
  - exists d1. split. exact Hd1.
    exists (Nat.max N1 N2). intros n Hn.
    assert (Ha : NatLe N1 n).
    { apply NatLe_lift.
      assert (Hdrop : (Nat.max N1 N2 <= n)%nat) by exact (NatLe_drop _ _ Hn).
      lia. }
    assert (Hb : NatLe N2 n).
    { apply NatLe_lift.
      assert (Hdrop : (Nat.max N1 N2 <= n)%nat) by exact (NatLe_drop _ _ Hn).
      lia. }
    apply Qlt_to_QltT.
    rewrite !(qeqT_imp_qeq _ _ (real_plus_proj _ _ _)).
    pose proof (HN1 n Ha) as Hp1. apply QltT_to_Qlt in Hp1.
    rewrite (qeqT_imp_qeq _ _ (real_plus_proj _ _ _)) in Hp1.
    pose proof (HN2 n Hb) as Hp2. apply QltT_to_Qlt in Hp2.
    rewrite (qeqT_imp_qeq _ _ (real_plus_proj _ _ _)) in Hp2.
    assert (Hhp : projT1 (uabS4c_half eps) n + projT1 (uabS4c_half eps) n == projT1 eps n).
    { unfold uabS4c_half. rewrite (qeqT_imp_qeq _ _ (real_mult_proj _ _ _)). rewrite (qeqT_imp_qeq _ _ (real_const_proj _ _)). ring. }
    rewrite <- Hhp.
    lra.
  - exists d2. split. exact Hd2.
    exists (Nat.max N1 N2). intros n Hn.
    assert (Ha : NatLe N1 n).
    { apply NatLe_lift.
      assert (Hdrop : (Nat.max N1 N2 <= n)%nat) by exact (NatLe_drop _ _ Hn).
      lia. }
    assert (Hb : NatLe N2 n).
    { apply NatLe_lift.
      assert (Hdrop : (Nat.max N1 N2 <= n)%nat) by exact (NatLe_drop _ _ Hn).
      lia. }
    apply Qlt_to_QltT.
    rewrite !(qeqT_imp_qeq _ _ (real_plus_proj _ _ _)).
    pose proof (HN1 n Ha) as Hp1. apply QltT_to_Qlt in Hp1.
    rewrite (qeqT_imp_qeq _ _ (real_plus_proj _ _ _)) in Hp1.
    pose proof (HN2 n Hb) as Hp2. apply QltT_to_Qlt in Hp2.
    rewrite (qeqT_imp_qeq _ _ (real_plus_proj _ _ _)) in Hp2.
    assert (Hhp : projT1 (uabS4c_half eps) n + projT1 (uabS4c_half eps) n == projT1 eps n).
    { unfold uabS4c_half. rewrite (qeqT_imp_qeq _ _ (real_mult_proj _ _ _)). rewrite (qeqT_imp_qeq _ _ (real_const_proj _ _)). ring. }
    rewrite <- Hhp.
    lra.
Qed.

(* A.8 antitone compatibility of opp for the B form: a <=_B b implies        *)
(*   -b <=_B -a.                                                             *)
Lemma uabS4c_leb_opp_anti : forall a b : Real,
  real_le_b a b -> real_le_b (real_opp b) (real_opp a).
Proof.
  intros a b H eps Heps.
  specialize (H eps Heps). unfold real_lt in H.
  destruct H as [d1 [Hd1 [N1 HN1]]].
  exists d1. split. exact Hd1.
  exists N1. intros n Hn.
  apply Qlt_to_QltT.
  rewrite (qeqT_imp_qeq _ _ (real_plus_proj _ _ _)). rewrite !(qeqT_imp_qeq _ _ (real_opp_proj _ _)).
  pose proof (HN1 n Hn) as Hp1. apply QltT_to_Qlt in Hp1.
  rewrite (qeqT_imp_qeq _ _ (real_plus_proj _ _ _)) in Hp1.
  lra.
Qed.

(* Section 2. the abstract SumOver interface section: the honest interface shape of *)
(*   UpReqSampling specialized to R := Real; the three fields are explicit   *)
(*   Set-layer premises, and the abs_sum_le field is omitted because this    *)
(*   module proves it.                                                       *)

Section uabS4c_SumOverSlot.

Variable S : Set.
Variable sumf : (S -> Real) -> Real.

(* premise field 1, extensionality: pointwise real_eq implies real_eq of the *)
(*   sums (the library shape sum_ext).                                       *)
Variable uabS4c_sum_ext : forall f g : S -> Real,
  (forall s : S, real_eq (f s) (g s)) -> real_eq (sumf f) (sumf g).
(* premise field 2, addition: the pointwise sum equals the sum of the sums   *)
(*   (the library shape sum_add).                                            *)
Variable uabS4c_sum_add : forall f g : S -> Real,
  real_eq (sumf (fun s : S => real_plus (f s) (g s))) (real_plus (sumf f) (sumf g)).
(* premise field 3, monotonicity in the Bishop upgrade form: pointwise       *)
(*   real_le_b implies real_le_b of the sums; the library Or field follows   *)
(*   in one step via real_le_to_le_b, so this premise is strictly weaker and *)
(*   the conclusion stronger.                                                *)
Variable uabS4c_sum_le_B : forall f g : S -> Real,
  (forall s : S, real_le_b (f s) (g s)) -> real_le_b (sumf f) (sumf g).

(* B.0 algebra of the zero function: the sum of 0 equals 0 (self-proved from *)
(*   the ext and add fields by a cancellation chain, no new premises).       *)
Lemma uabS4c_sum_zero_eq : real_eq (sumf (fun _ : S => real_zero)) real_zero.
Proof.
  assert (Hid : real_eq (sumf (fun _ : S => real_zero))
                        (real_plus (sumf (fun _ : S => real_zero))
                                   (sumf (fun _ : S => real_zero)))).
  { eapply real_eq_trans.
    - apply (uabS4c_sum_ext (fun _ : S => real_zero)
               (fun _ : S => real_plus real_zero real_zero)).
      intro s. apply real_eq_sym. apply real_plus_zero.
    - apply (uabS4c_sum_add (fun _ : S => real_zero) (fun _ : S => real_zero)). }
  assert (Hkey : real_eq (real_plus (sumf (fun _ : S => real_zero))
                                    (real_opp (sumf (fun _ : S => real_zero))))
                         (sumf (fun _ : S => real_zero))).
  { eapply real_eq_trans.
    - apply RealSetoid.real_eq_plus_compat.
      + exact Hid.
      + apply real_eq_refl.
    - eapply real_eq_trans.
      + apply real_eq_sym. apply real_plus_assoc.
      + eapply real_eq_trans.
        * apply RealSetoid.real_eq_plus_compat.
          -- apply real_eq_refl.
          -- apply real_plus_opp.
        * apply real_plus_zero. }
  eapply real_eq_trans.
  - apply real_eq_sym. exact Hkey.
  - apply real_plus_opp.
Qed.

(* B.1 algebra of the negative function: the sum of -f equals -(the sum of   *)
(*   f) (self-proved from the ext and add fields with B.0, no new premises). *)
Lemma uabS4c_sum_opp_eq : forall f : S -> Real,
  real_eq (sumf (fun s : S => real_opp (f s))) (real_opp (sumf f)).
Proof.
  intros f.
  assert (Hadd : real_eq (sumf (fun s : S => real_plus (f s) (real_opp (f s))))
                         (real_plus (sumf f) (sumf (fun s : S => real_opp (f s)))))
    by apply (uabS4c_sum_add f (fun s : S => real_opp (f s))).
  assert (Hext : real_eq (sumf (fun s : S => real_plus (f s) (real_opp (f s))))
                         (sumf (fun _ : S => real_zero)))
    by (apply (uabS4c_sum_ext (fun s : S => real_plus (f s) (real_opp (f s)))
                (fun _ : S => real_zero)); intro s; apply real_plus_opp).
  assert (Hplus : real_eq (real_plus (sumf f) (sumf (fun s : S => real_opp (f s))))
                          real_zero).
  { eapply real_eq_trans.
    - apply real_eq_sym. exact Hadd.
    - eapply real_eq_trans.
      + exact Hext.
      + apply uabS4c_sum_zero_eq. }
  (* chain: so = 0 + so = (sf + (-sf)) + so = sf + ((-sf) + so)              *)
  (*   = sf + (so + (-sf)) = (sf + so) + (-sf) = 0 + (-sf) = (-sf) + 0 = -sf *)
  assert (Hs1 : real_eq (sumf (fun s : S => real_opp (f s)))
                        (real_plus real_zero (sumf (fun s : S => real_opp (f s))))).
  { eapply real_eq_trans.
    - apply real_eq_sym. apply real_plus_zero.
    - apply real_eq_sym. apply real_plus_comm. }
  assert (Hs2 : real_eq (real_plus real_zero (sumf (fun s : S => real_opp (f s))))
                        (real_plus (real_plus (sumf f) (real_opp (sumf f)))
                                   (sumf (fun s : S => real_opp (f s))))).
  { apply RealSetoid.real_eq_plus_compat.
    - apply real_eq_sym. apply real_plus_opp.
    - apply real_eq_refl. }
  assert (Hs3 : real_eq (real_plus (real_plus (sumf f) (real_opp (sumf f)))
                                   (sumf (fun s : S => real_opp (f s))))
                        (real_plus (sumf f)
                                   (real_plus (real_opp (sumf f))
                                              (sumf (fun s : S => real_opp (f s))))))
    by (apply real_eq_sym; apply real_plus_assoc).
  assert (Hs4 : real_eq (real_plus (sumf f)
                                   (real_plus (real_opp (sumf f))
                                              (sumf (fun s : S => real_opp (f s)))))
                        (real_plus (sumf f)
                                   (real_plus (sumf (fun s : S => real_opp (f s)))
                                              (real_opp (sumf f)))))
    by (apply RealSetoid.real_eq_plus_compat;
        [apply real_eq_refl | apply real_plus_comm]).
  assert (Hs5 : real_eq (real_plus (sumf f)
                                   (real_plus (sumf (fun s : S => real_opp (f s)))
                                              (real_opp (sumf f))))
                        (real_plus (real_plus (sumf f)
                                   (sumf (fun s : S => real_opp (f s))))
                                   (real_opp (sumf f))))
    by apply real_plus_assoc.
  assert (Hs6 : real_eq (real_plus (real_plus (sumf f)
                                   (sumf (fun s : S => real_opp (f s))))
                                   (real_opp (sumf f)))
                        (real_plus real_zero (real_opp (sumf f))))
    by (apply RealSetoid.real_eq_plus_compat; [exact Hplus | apply real_eq_refl]).
  assert (Hs7 : real_eq (real_plus real_zero (real_opp (sumf f)))
                        (real_opp (sumf f))).
  { eapply real_eq_trans.
    - apply real_plus_comm.
    - apply real_plus_zero. }
  exact (real_eq_trans _ _ _ Hs1
           (real_eq_trans _ _ _ Hs2
              (real_eq_trans _ _ _ Hs3
                 (real_eq_trans _ _ _ Hs4
                    (real_eq_trans _ _ _ Hs5 (real_eq_trans _ _ _ Hs6 Hs7)))))).
Qed.

(* B.2 main theorem in the interface-native B form:                          *)
(*   |sum sumf f| <=_B sum sumf (fun s => |f s|).                            *)
(*   Construction: the two pointwise B absorptions (A.2/A.3) feed the        *)
(*   monotonicity field for both sum bounds, the negative bound is           *)
(*   transported by B.1 via A.5, and the two-sided sandwich core A.4         *)
(*   concludes - the three premise fields each carry one role, with no       *)
(*   induction.                                                              *)
Theorem uabS4c_abs_sum_le_B_slot : forall f : S -> Real,
  real_le_b (real_abs (sumf f)) (sumf (fun s : S => real_abs (f s))).
Proof.
  intros f.
  assert (H1 : real_le_b (sumf f) (sumf (fun s : S => real_abs (f s)))).
  { apply uabS4c_sum_le_B. intro s. apply uabS4c_abs_ge_l_b. }
  assert (H2 : real_le_b (sumf (fun s : S => real_opp (f s)))
                         (sumf (fun s : S => real_abs (f s)))).
  { apply uabS4c_sum_le_B. intro s. apply uabS4c_abs_ge_opp_b. }
  assert (H3 : real_le_b (real_opp (sumf f))
                         (sumf (fun s : S => real_abs (f s)))).
  { apply (uabS4c_leb_req_left (sumf (fun s : S => real_opp (f s)))
             (real_opp (sumf f))).
    - apply uabS4c_sum_opp_eq.
    - exact H2. }
  exact (uabS4c_abs_le_b_two_sided (sumf f)
           (sumf (fun s : S => real_abs (f s))) H1 H3).
Qed.

(* B.3 pointwise-eps corollary: from the B form to the pointwise-eps form by *)
(*   inl injection, the counterpart of [UpAblAbsSumLeB] B.3.                 *)
Theorem uabS4c_abs_sum_le_eps_slot : forall (f : S -> Real) (e : Real),
  real_lt real_zero e ->
  real_le (real_abs (sumf f))
          (real_plus (sumf (fun s : S => real_abs (f s))) e).
Proof.
  intros f e He.
  apply (RealSetoid.real_lt_le_iff_req). apply inl.
  exact (uabS4c_abs_sum_le_B_slot f e He).
Qed.

(* B.4 doubled-margin contradiction lemma: the B-form bound cannot be        *)
(*   exceeded by a doubled margin (constructively, no witness of that        *)
(*   exists).  It applies donor C.1 ([uabS4_lt_double_margin_le_half_contr]) *)
(*   together with B.3 of this module - an interface-level consistency       *)
(*   certificate.                                                            *)
Theorem uabS4c_slot_double_kill : forall (f : S -> Real) (e : Real),
  real_lt real_zero e ->
  real_lt (real_plus (sumf (fun s : S => real_abs (f s))) (real_plus e e))
          (real_abs (sumf f)) ->
  Empty_set.
Proof.
  intros f e He Hfar.
  apply (uabS4_lt_double_margin_le_half_contr (real_abs (sumf f))
           (sumf (fun s : S => real_abs (f s))) e He Hfar).
  exact (uabS4c_abs_sum_le_eps_slot f e He).
Qed.

End uabS4c_SumOverSlot.

(* Section 3. satisfiability instance of the interface (the bool two-point sum), *)
(*   with the donor counterpart.                                             *)

(* C.0 the three interface fields for the bool two-point sum (extensionality, *)
(*   addition, monotonicity in Bishop form).                                 *)
Lemma uabS4c_pair_ext : forall (f g : bool -> Real),
  (forall s : bool, real_eq (f s) (g s)) ->
  real_eq (real_plus (f true) (f false)) (real_plus (g true) (g false)).
Proof.
  intros f g H. apply RealSetoid.real_eq_plus_compat.
  - exact (H true).
  - exact (H false).
Qed.

Lemma uabS4c_pair_add : forall f g : bool -> Real,
  real_eq (real_plus (real_plus (f true) (g true)) (real_plus (f false) (g false)))
          (real_plus (real_plus (f true) (f false)) (real_plus (g true) (g false))).
Proof.
  intros f g.
  assert (Ht1 : real_eq (real_plus (real_plus (f true) (g true)) (real_plus (f false) (g false)))
                        (real_plus (f true) (real_plus (g true) (real_plus (f false) (g false)))))
    by (apply real_eq_sym; apply real_plus_assoc).
  assert (Ht2 : real_eq (real_plus (f true) (real_plus (g true) (real_plus (f false) (g false))))
                        (real_plus (f true) (real_plus (real_plus (g true) (f false)) (g false))))
    by (apply RealSetoid.real_eq_plus_compat;
        [apply real_eq_refl | apply real_plus_assoc]).
  assert (Ht3 : real_eq (real_plus (f true) (real_plus (real_plus (g true) (f false)) (g false)))
                        (real_plus (f true) (real_plus (real_plus (f false) (g true)) (g false))))
    by (apply RealSetoid.real_eq_plus_compat;
        [apply real_eq_refl | apply RealSetoid.real_eq_plus_compat;
          [apply real_plus_comm | apply real_eq_refl]]).
  assert (Ht4 : real_eq (real_plus (f true) (real_plus (real_plus (f false) (g true)) (g false)))
                        (real_plus (f true) (real_plus (f false) (real_plus (g true) (g false)))))
    by (apply RealSetoid.real_eq_plus_compat;
        [apply real_eq_refl | apply real_eq_sym; apply real_plus_assoc]).
  assert (Ht5 : real_eq (real_plus (f true) (real_plus (f false) (real_plus (g true) (g false))))
                        (real_plus (real_plus (f true) (f false)) (real_plus (g true) (g false))))
    by apply real_plus_assoc.
  exact (real_eq_trans _ _ _ Ht1 (real_eq_trans _ _ _ Ht2 (real_eq_trans _ _ _ Ht3 (real_eq_trans _ _ _ Ht4 Ht5)))).
Qed.

Lemma uabS4c_pair_le_B : forall f g : bool -> Real,
  (forall s : bool, real_le_b (f s) (g s)) ->
  real_le_b (real_plus (f true) (f false)) (real_plus (g true) (g false)).
Proof.
  intros f g H. apply uabS4c_leb_plus_compat.
  - exact (H true).
  - exact (H false).
Qed.

Check uabS4c_abs_sum_le_B_slot.

(* C.1 the two-point sum form re-derived through the abstract interface,     *)
(*   statement identical to donor A.3 ([uabS4_abs_sum_le_B_pair]): the       *)
(*   interface route and the donor route carry the same statement side by    *)
(*   side.  A semantic side note: the half construction of A.7 is genuinely  *)
(*   used at the monotonicity field of this instance.                        *)
Theorem uabS4c_slot_pair_B : forall f : bool -> Real,
  real_le_b (real_abs (real_plus (f true) (f false)))
            (real_plus (real_abs (f true)) (real_abs (f false))).
Proof.
  intros f.
  exact (uabS4c_abs_sum_le_B_slot bool
           (fun (h : bool -> Real) => real_plus (h true) (h false))
           uabS4c_pair_ext uabS4c_pair_add uabS4c_pair_le_B f).
Qed.

(* audit note: Print Assumptions is expected to report Closed throughout     *)
(*   (no external unproved assumptions; the section variables are            *)
(*   generalized away at End).                                               *)

Print Assumptions uabS4c_abs_ge_l_b.
Print Assumptions uabS4c_abs_ge_opp_b.
Print Assumptions uabS4c_abs_le_b_two_sided.
Print Assumptions uabS4c_leb_req_left.
Print Assumptions uabS4c_half_eq.
Print Assumptions uabS4c_half_pos.
Print Assumptions uabS4c_leb_plus_compat.
Print Assumptions uabS4c_leb_opp_anti.
Print Assumptions uabS4c_abs_sum_le_B_slot.
Print Assumptions uabS4c_abs_sum_le_eps_slot.
Print Assumptions uabS4c_slot_double_kill.
Print Assumptions uabS4c_slot_pair_B.
(* ================= Section 2. the s6f_q_const_pos family ================= *)
From Stdlib Require Import QArith.Qring QArith.Qabs QArith.Qminmax.

(* Section 0. signature verification of the dependencies (identifier drift surfaces *)
(*   at compile time).                                                       *)

Check real_le_b.              (* the Bishop form of <= of [UpRealLeB], a statement-face predicate *)
Check real_eq.                (* per-eps equality (at the set level) *)
Check real_abs.               (* pointwise Qabs (the ConstructiveWorld real) *)
Check real_abs_proj.          (* pointwise projection *)
Check real_mult.              (* pointwise multiplication *)
Check real_mult_proj.         (* pointwise projection (multiplication) *)
Check real_const.             (* constant real *)
Check real_const_proj.        (* pointwise projection (constant) *)
Check real_eq_trans.          (* transitivity of equality *)
Check real_eq_refl.           (* reflexivity of equality *)
Check real_eq_of_zero_diff.   (* pointwise zero difference implies real_eq *)
Check RealSetoid.real_eq_mult_compat. (* compatibility of multiplication with equality *)
Check uabS4c_abs_sum_le_B_slot. (* the main supply theorem (generalized by End) *)
Check uabS4c_abs_sum_le_eps_slot. (* pointwise-eps supply (covers the statement required by part two) *)
Check Qabs_Qmult.             (* on Q: Qabs (u * v) == Qabs u * Qabs v *)
Check Qabs_pos.               (* on Q: 0 <= u implies Qabs u == u *)
Check Qabs_neg.               (* on Q: 0 <= -u implies Qabs u == -u *)
Check Qlt_shift_div_l.        (* half positivity on Q *)
Check Qlt_to_QltT.
Check QltT_to_Qlt.
Check Qlt_le_dec.             (* decidable sign on Q (no classical logic) *)
Check Qle_Qabs.               (* on Q: u <= Qabs u *)
Check Qlt_le_trans.
Check NatLe_lift.
Check NatLe_drop.

(* Section A. the conversion layer (pointwise abs rewriting plus right-end equality *)
(*   transport for the B form).                                              *)

(* A.0 bridge from rational positivity to the Real layer: 0 < e (rational)   *)
(*   implies real_lt real_zero (real_const e).                               *)
(*   Witness: the half margin d := e * (1#2) with N := 0; pointwise the      *)
(*   projection via real_const_proj yields e itself.                         *)
(*   Practical note: lra fails on Q division, so half margins are always     *)
(*   written in the multiplication form e * (1#2).                           *)
Lemma s6f_q_const_pos : forall e : Q,
  QltT 0 e -> real_lt real_zero (real_const e).
Proof.
  intros e He.
  assert (Hhalfq : Qlt 0 (e * (1#2))).
  { apply QltT_to_Qlt in He. lra. }
  assert (Hhalf : QltT 0 (e * (1#2))) by (apply Qlt_to_QltT; exact Hhalfq).
  exists (e * (1#2))%Q. split.
  - exact Hhalf.
  - exists O. intros n Hn.
    apply Qlt_to_QltT.
    rewrite (qeqT_imp_qeq _ _ (real_const_proj _ _)).
    assert (Hz : projT1 real_zero n == 0) by reflexivity.
    rewrite Hz.
    lra.
Qed.

(* A.1 abs identity for nonnegative reals: 0 <=_B q implies |q| = q.         *)
(*   Idea: halve the budget of real_le_b (multiplication form (1#2)), take   *)
(*   the eventual tail (ultimately q_n > -eps/2) and dichotomize on it: for  *)
(*   q_n < 0 one gets -2 * q_n < eps; for q_n >= 0 the identity              *)
(*   Qabs q_n == q_n gives a zero difference.                                *)
Lemma s6f_abs_nonneg_eq : forall q : Real,
  real_le_b real_zero q -> real_eq (real_abs q) q.
Proof.
  intros q Hq.
  unfold real_eq. intros eps0 Heps0.
  (* budget halved (multiplication form (1#2)): the tail has                 *)
  (*   q_n > d0 - eps0/2 > -eps0/2; after the dichotomy the case q_n < 0     *)
  (*   gives -2 * q_n < eps0 and the case q_n >= 0 gives a zero difference   *)
  assert (Hhalfq : Qlt 0 (eps0 * (1#2))).
  { apply QltT_to_Qlt in Heps0. lra. }
  assert (Hhalf : QltT 0 (eps0 * (1#2))) by (apply Qlt_to_QltT; exact Hhalfq).
  destruct (Hq (real_const (eps0 * (1#2))) (s6f_q_const_pos (eps0 * (1#2)) Hhalf))
    as [d0 [Hd0 [N0 HN0]]].
  exists N0. intros n Hn.
  apply Qlt_to_QltT.
  rewrite (qeqT_imp_qeq _ _ (real_abs_proj _ _)).
  pose proof (HN0 n Hn) as Hp. apply QltT_to_Qlt in Hp.
  rewrite (qeqT_imp_qeq _ _ (real_plus_proj _ _ _)) in Hp.
  rewrite (qeqT_imp_qeq _ _ (real_const_proj _ _)) in Hp.
  assert (Hz : projT1 real_zero n == 0) by reflexivity.
  rewrite Hz in Hp.
  assert (Hd0q : Qlt 0 d0) by (apply QltT_to_Qlt; exact Hd0).
  destruct (Qlt_le_dec (projT1 q n) 0) as [Hqn | Hqn].
  - assert (Habs : Qabs (projT1 q n) == - projT1 q n)
      by (apply Qabs_neg; apply Qlt_le_weak; exact Hqn).
    rewrite Habs.
    assert (Hp2 : Qlt 0 (- projT1 q n - projT1 q n)) by lra.
    assert (Habs2 : Qabs (- projT1 q n - projT1 q n)
                    == - projT1 q n - projT1 q n)
      by (apply Qabs_pos; apply Qlt_le_weak; exact Hp2).
    rewrite Habs2.
    lra.
  - assert (Habs : Qabs (projT1 q n) == projT1 q n)
      by (apply Qabs_pos; exact Hqn).
    rewrite Habs.
    assert (Hz2 : projT1 q n - projT1 q n == 0) by lra.
    rewrite Hz2.
    assert (Hz3 : Qabs 0 == 0) by reflexivity.
    rewrite Hz3.
    apply QltT_to_Qlt. exact Heps0.
Qed.

(* A.2 double-abs product identity, unconditional: |x * q| = |x| * |q|.      *)
(*   real_eq_of_zero_diff reduces it to a pointwise zero difference and the  *)
(*   Qabs_Qmult identity concludes (at the Q layer, no classical logic).     *)
Lemma s6f_abs_abs_mult_eq : forall x q : Real,
  real_eq (real_abs (real_mult x q)) (real_mult (real_abs x) (real_abs q)).
Proof.
  intros x q. apply real_eq_of_zero_diff. intro n.
  apply qeq_imp_qeqT.
  rewrite !(qeqT_imp_qeq _ _ (real_abs_proj _ _)).
  rewrite !(qeqT_imp_qeq _ _ (real_mult_proj _ _ _)).
  rewrite !(qeqT_imp_qeq _ _ (real_abs_proj _ _)).
  rewrite Qabs_Qmult.
  lra.
Qed.

(* A.3 main pointwise abs rewriting lemma (the conversion-layer core for     *)
(*   part one): 0 <=_B q implies |x * q| = |x| * q.                          *)
(*   Chain: |x * q| = |x| * |q| (A.2) = |x| * q (A.1 with                    *)
(*   RealSetoid.real_eq_mult_compat).                                        *)
Lemma s6f_abs_mult_eq : forall x q : Real,
  real_le_b real_zero q ->
  real_eq (real_abs (real_mult x q)) (real_mult (real_abs x) q).
Proof.
  intros x q Hq.
  eapply real_eq_trans.
  - apply s6f_abs_abs_mult_eq.
  - apply RealSetoid.real_eq_mult_compat.
    + apply real_eq_refl.
    + apply s6f_abs_nonneg_eq. exact Hq.
Qed.

(* A.4 right-end equality transport for the B form (the dual of              *)
(*   uabS4c_leb_req_left): a = b and Y <=_B a imply Y <=_B b.                *)
(*   Idea: halve the budget d (h := d * (1#2)) - real_eq gives the tail with *)
(*   |a_n - b_n| < h at budget h; align tails with the budget d of the       *)
(*   Y + a side by max, and lra concludes on Q.                              *)
Lemma s6f_leb_req_right : forall a b Y : Real,
  real_eq a b -> real_le_b Y a -> real_le_b Y b.
Proof.
  intros a b Y Hab HYa eps Heps.
  pose proof (HYa eps Heps) as HYa'.
  unfold real_le_b in HYa'. unfold real_lt in HYa'.
  destruct HYa' as [d [Hd [N1 HN1]]].
  (* half witness: h := d * (1#2) - the equality budget takes exactly half,  *)
  (*   so d - h = h and the max-aligned tails close exactly                  *)
  assert (Hh : Qlt 0 (d * (1#2))).
  { apply QltT_to_Qlt in Hd. lra. }
  assert (HhT : QltT 0 (d * (1#2))) by (apply Qlt_to_QltT; exact Hh).
  destruct (Hab (d * (1#2)) HhT) as [N2 HN2].
  exists (d * (1#2)). split.
  - exact HhT.
  - exists (Nat.max N1 N2). intros n Hn.
    assert (Ha1 : NatLe N1 n).
    { apply NatLe_lift.
      assert (Hdrop : (Nat.max N1 N2 <= n)%nat) by exact (NatLe_drop _ _ Hn).
      lia. }
    assert (Ha2 : NatLe N2 n).
    { apply NatLe_lift.
      assert (Hdrop : (Nat.max N1 N2 <= n)%nat) by exact (NatLe_drop _ _ Hn).
      lia. }
    apply Qlt_to_QltT.
    pose proof (HN1 n Ha1) as Hp1. apply QltT_to_Qlt in Hp1.
    rewrite (qeqT_imp_qeq _ _ (real_plus_proj _ _ _)) in Hp1.
    pose proof (HN2 n Ha2) as Hp2. apply QltT_to_Qlt in Hp2.
    assert (Hge : Qle (projT1 a n - projT1 b n)
                      (Qabs (projT1 a n - projT1 b n)))
      by apply Qle_Qabs.
    assert (Hp2' : Qlt (projT1 a n - projT1 b n) (d * (1#2)))
      by (apply (Qle_lt_trans _ (Qabs (projT1 a n - projT1 b n)) _);
          [exact Hge | exact Hp2]).
    rewrite (qeqT_imp_qeq _ _ (real_plus_proj _ _ _)).
    lra.
Qed.

(* Section B. supply for part one (the abs_kernel_bound form): the B-layer supply of *)
(*   the same statement shape, preserved pointwise: |sum f * q| <=_B         *)
(*   sum |f| * q; the carrier is the concrete Real, the sumf abstraction is  *)
(*   any summation operator over S : Set, and the three premises quantify    *)
(*   the donor theorem's premises explicitly.                                *)

Theorem s6f_abs_kernel_bound_slot :
  forall (S : Set) (sumf : (S -> Real) -> Real),
    (forall f g : S -> Real,
      (forall s : S, real_eq (f s) (g s)) -> real_eq (sumf f) (sumf g)) ->
    (forall f g : S -> Real,
      real_eq (sumf (fun s : S => real_plus (f s) (g s)))
              (real_plus (sumf f) (sumf g))) ->
    (forall f g : S -> Real,
      (forall s : S, real_le_b (f s) (g s)) -> real_le_b (sumf f) (sumf g)) ->
    forall (f q : S -> Real),
      (forall s : S, real_le_b real_zero (q s)) ->
      real_le_b (real_abs (sumf (fun s : S => real_mult (f s) (q s))))
                (sumf (fun s : S => real_mult (real_abs (f s)) (q s))).
Proof.
  intros S sumf Hext Hadd Hleb f q Hq.
  (* the donor uabS4c_abs_sum_le_B_slot applied directly at g := f * q:      *)
  (*   |sum f * q| <=_B sum |f * q|                                          *)
  assert (Hdon : real_le_b (real_abs (sumf (fun s : S => real_mult (f s) (q s))))
                           (sumf (fun s : S => real_abs (real_mult (f s) (q s)))))
    by (apply (uabS4c_abs_sum_le_B_slot S sumf Hext Hadd Hleb)).
  (* pointwise conversion: |f s * q s| = |f s| * q s (q s >=_B 0)            *)
  assert (Hpt : forall s : S, real_eq (real_abs (real_mult (f s) (q s)))
                                      (real_mult (real_abs (f s)) (q s)))
    by (intro s; apply s6f_abs_mult_eq; exact (Hq s)).
  (* extensionality transport of the summation operator (premise one, Hext)  *)
  assert (Hsum : real_eq (sumf (fun s : S => real_abs (real_mult (f s) (q s))))
                         (sumf (fun s : S => real_mult (real_abs (f s)) (q s))))
    by (apply Hext; exact Hpt).
  (* right-end equality transport for the B form (A.4 of this module)        *)
  exact (s6f_leb_req_right _ _ _ Hsum Hdon).
Qed.

(* Section C. part two (the eviction_steady_deviation form): a proved conclusion  *)
(*   with zero new constructions.  S06 uses abs_sum_le as a bare field       *)
(*   application (no specialization: abs_sum_le (fun s' => ...) applied as   *)
(*   is); its statement-form supply is uabS4c_abs_sum_le_B_slot itself (same *)
(*   statement, verified in the Section 0 inventory); the difference-rewrite and *)
(*   linear-extraction faces are interface Id algebra restatements (no new   *)
(*   supply used).  No forced specialization.                                *)

(* assumption audit: all six Print Assumptions report Closed *)
Print Assumptions s6f_q_const_pos.
Print Assumptions s6f_abs_nonneg_eq.
Print Assumptions s6f_abs_abs_mult_eq.
Print Assumptions s6f_abs_mult_eq.
Print Assumptions s6f_leb_req_right.
Print Assumptions s6f_abs_kernel_bound_slot.
