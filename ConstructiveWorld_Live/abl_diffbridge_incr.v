(* ConstructiveWorld-Set — differentiability predicate bridges. *)

(** * abl_diffbridge_incr: translations between the increment form and the
    record form of differentiability.

    Mission.  Two-way translations between the increment form [HasIncr]
      (an eps-linear shape for total functions, from
      [abl_arctan_diff_16]) and the record form [RealDifferentiable]
      (an eps shape with positivity premises): [HasIncrPos] aligns with
      the record's correctness field; [dbi_realdiff_hasincrpos] and
      [dbi_hasincrpos_realdiff] convert between record and increment
      supply; [dbi_hasincr_incrpos] / [dbi_incrpos_hasincr] connect the
      two faces; the last two lemmas composite end to end.

    Dependencies.  Requires [S01_BaseRing] through [S11_TP3B5],
      [abl_arctan_diff_16] ([HasIncr] plus three skeleton lemmas),
      the [RealDifferentiable] record of [S08_RealMainlineDPO], and
      Stdlib [QArith]/[List]/[Setoid]/[Lia].

    References.  The baseline module abl_diffbridge_incr.v in
      ConstructiveWorld-Main (statement names carried over verbatim,
      statement-face Set-carrier completion).

    Constructivity.  All statements close by [Qed]; [HasIncrPos] is
      assembled from [real_lt]/[real_le]/[sigT]/[And]; the slope choice
      projects pointwise through [projT1] rather than classical choice;
      extraction has [Obj.magic] = 0; [coqchk] reports [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" abl_diffbridge_incr.v]
      compiles cleanly (exit 0); the artifact begins [436f7121 00015ff4]. *)


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
Require Import abl_arctan_diff_16.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               Lists.List Bool.Bool Arith.Arith.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax Structures.GenericMinMax.

(* ================= 0. The premise-carrying increment predicate ================= *)
(*    [HasIncrPos] aligns verbatim with the record's correctness field: the
      predicate index Hx (partial-function face) plus the domain premise Hxh
      (0 < x + h); the error-term slope order follows [HasIncr] (h*a) rather
      than the record (a*h); the rewrite is carried by [dbi_err_eq_comm].
      Entirely Set-layer. *)
Definition HasIncrPos (f : forall x : Real, real_lt real_zero x -> Real)
           (x a : Real) (Hx : real_lt real_zero x) : Set :=
  forall (eps : Real), real_lt real_zero eps ->
  sigT (fun d : Real =>
    And (real_lt real_zero d)
        (forall (h : Real), real_lt (real_abs h) d ->
          forall (Hxh : real_lt real_zero (real_plus x h)),
          forall (eps' : Real), real_lt real_zero eps' ->
          real_le (real_abs (real_plus (f (real_plus x h) Hxh)
                     (real_opp (real_plus (f x Hx) (real_mult h a)))))
                  (real_plus (real_mult eps (real_abs h)) eps'))).

(* ================= 1. Three Q-layer helpers (pointwise bookkeeping base) ================= *)
Lemma dbi_qplus_le_r : forall a b c : Q, Qle a b -> QleT' (a + c) (b + c).
Proof.
  intros a b c H.
  apply Qle_to_QleT'.
  apply (Qplus_le_compat a b c c).
  - exact H.
  - apply Qle_refl.
Qed.

Lemma dbi_qplus_le_l : forall a b c : Q, Qle a b -> QleT' (c + a) (c + b).
Proof.
  intros a b c H.
  apply Qle_to_QleT'.
  apply (Qplus_le_compat c c a b).
  - apply Qle_refl.
  - exact H.
Qed.

(* -|a| <= a (two branches of [Qabs_case], with the positivity premise of
      [Qabs] stripped: the 0 <= a branch goes by antitonicity of [Qopp] plus
      the zero bridge; the a <= 0 branch reduces to an equality by
      [Qopp_involutive]; no rewriting throughout). *)
Lemma dbi_q_opp_abs_le : forall a : Q, QleT' (Qopp (Qabs a)) a.
Proof.
  intros a.
  assert (Hcore : Qle (Qopp (Qabs a)) a).
  { apply (Qabs_case a (fun t => Qle (Qopp t) a)).
  - intros H0a.
    apply (Qle_trans (Qopp a) 0%Q a).
    + apply (Qopp_le_compat 0%Q a). exact H0a.
    + exact H0a.
  - intros Hb0.
    apply QleT'_to_Qle. apply S02_CauchyComplete.qeq_leT'.
    apply qeq_imp_qeqT. apply Qopp_involutive.
  }
  apply Qle_to_QleT'. exact Hcore.
Qed.

(* ================= 2. The error-term slope swap h*a <-> a*h ================= *)
(*    The only non-definitional rewrite of the increment error shape,
      shared by both directions and the end-to-end composites. *)
Lemma dbi_err_eq_comm :
  forall (f : forall x : Real, real_lt real_zero x -> Real)
         (x a : Real) (Hx : real_lt real_zero x) (h : Real)
         (Hxh : real_lt real_zero (real_plus x h)),
  real_eq (real_abs (real_plus (f (real_plus x h) Hxh)
             (real_opp (real_plus (f x Hx) (real_mult h a)))))
          (real_abs (real_plus (f (real_plus x h) Hxh)
             (real_opp (real_plus (f x Hx) (real_mult a h))))).
Proof.
  intros f x a Hx h Hxh.
  apply real_abs_eq_compat.
  apply (RealSetoid.real_eq_plus_compat (f (real_plus x h) Hxh)
           (real_opp (real_plus (f x Hx) (real_mult h a)))
           (f (real_plus x h) Hxh)
           (real_opp (real_plus (f x Hx) (real_mult a h)))).
  - apply real_eq_refl.
  - apply (RealSetoid.real_eq_opp_compat
             (real_plus (f x Hx) (real_mult h a))
             (real_plus (f x Hx) (real_mult a h))).
    apply (RealSetoid.real_eq_plus_compat (f x Hx) (real_mult h a)
             (f x Hx) (real_mult a h)).
    + apply real_eq_refl.
    + apply (real_mult_comm h a).
Qed.

(* ================= 3. Direction one (record to increment supply) ================= *)
(*    The record's correctness field instantiated at x is exactly
      [HasIncrPos]: the slope is the record's slope at x with the delta
      taken directly; the only bookkeeping is the slope order swap
      ([dbi_err_eq_comm] with [real_le_eq_l]). *)
Theorem dbi_realdiff_hasincrpos :
  forall (f : forall x : Real, real_lt real_zero x -> Real)
         (Hf : RealDifferentiable f) (x : Real) (Hx : real_lt real_zero x),
  HasIncrPos f x (rdf f Hf x Hx) Hx.
Proof.
  intros f Hf x Hx eps Heps.
  destruct (rdf_correct f Hf x Hx eps Heps) as [delta [Hd Hstep]].
  exists delta. split.
  - exact Hd.
  - intros h Hh Hxh eps' Heps'.
    apply (real_le_eq_l
             (real_abs (real_plus (f (real_plus x h) Hxh)
                (real_opp (real_plus (f x Hx)
                   (real_mult h (rdf f Hf x Hx))))))
             (real_abs (real_plus (f (real_plus x h) Hxh)
                (real_opp (real_plus (f x Hx)
                   (real_mult (rdf f Hf x Hx) h)))))).
    + exact (dbi_err_eq_comm f x (rdf f Hf x Hx) Hx h Hxh).
    + exact (Hstep h Hh Hxh eps' Heps').
Qed.

(* ================= 4. Direction two (increment supply to record) ================= *)
(*    The pointwise sigT supply projects through [projT1] into a slope
      function (a legal Set-layer selection, not classical); the record's
      correctness slot is filled directly by the supplied [HasIncrPos]
      instance. *)
Theorem dbi_hasincrpos_realdiff :
  forall (f : forall x : Real, real_lt real_zero x -> Real),
  (forall (x : Real) (Hx : real_lt real_zero x),
     sigT (fun a : Real => HasIncrPos f x a Hx)) ->
  RealDifferentiable f.
Proof.
  intros f Hsup.
  exists (fun x Hx => projT1 (Hsup x Hx)).
  cbv beta.
  intros x Hx eps Heps.
  destruct (Hsup x Hx) as [a Ha].
  destruct (Ha eps Heps) as [delta [Hd Hstep]].
  exists delta. split.
  - exact Hd.
  - intros h Hh Hxh eps' Heps'.
    apply (real_le_eq_l
             (real_abs (real_plus (f (real_plus x h) Hxh)
                (real_opp (real_plus (f x Hx) (real_mult a h)))))
             (real_abs (real_plus (f (real_plus x h) Hxh)
                (real_opp (real_plus (f x Hx) (real_mult h a)))))).
    + apply real_eq_sym. exact (dbi_err_eq_comm f x a Hx h Hxh).
    + exact (Hstep h Hh Hxh eps' Heps').
Qed.

(* ================= 5. The domain-condition helper: the half-point bound ================= *)
Lemma dbi_halfx_pos : forall x : Real,
  real_lt real_zero x ->
  real_lt real_zero (real_mult (real_const (1#2)) x).
Proof.
  intros x Hx. apply (abl9_qscale_pos (1#2) x).
  - unfold Qlt. simpl. lia.
  - exact Hx.
Qed.

(* |h| < x/2 and 0 < x give 0 < x + h (pointwise Q bookkeeping: the strict
      part e0 < half*x_n - |h_n| goes through directly
      ([QltT] to [Qlt] by [Qlt_le_trans]); the literal weak chains are
      assembled through equality bridges:
      M_n - A_n <= half*x_n - |h_n| <= x_n - |h_n| <= x_n + h_n, which
      equals the projected right-hand side). *)
Lemma dbi_abs_lt_half_add_pos : forall (x h : Real),
  real_lt real_zero x ->
  real_lt (real_abs h) (real_mult (real_const (1#2)) x) ->
  real_lt real_zero (real_plus x h).
Proof.
  intros x h Hx Hhl.
  destruct Hhl as [e0 [He0 [N0 HN0]]].
  destruct Hx as [ex [Hex [Nx HNx]]].
  exists e0. split.
  - exact He0.
  - exists (Nat.max N0 Nx). intros n Hn.
    assert (Hn0 : NatLe N0 n).
    { apply NatLe_lift. apply Nat.le_trans with (Nat.max N0 Nx).
      - apply Nat.le_max_l.
      - apply (NatLe_drop _ _ Hn). }
    assert (Hnx : NatLe Nx n).
    { apply NatLe_lift. apply Nat.le_trans with (Nat.max N0 Nx).
      - apply Nat.le_max_r.
      - apply (NatLe_drop _ _ Hn). }
(* The four projection identities *)
    assert (Hz : projT1 real_zero n == 0%Q) by (cbn [projT1]; reflexivity).
    assert (Hplus : projT1 (real_plus x h) n == (projT1 x n + projT1 h n)%Q)
      by (apply qeqT_imp_qeq; apply real_plus_proj).
    assert (Habs : projT1 (real_abs h) n == Qabs (projT1 h n))
      by (apply qeqT_imp_qeq; apply real_abs_proj).
    assert (Hmul : projT1 (real_mult (real_const (1#2)) x) n
                   == ((1#2) * projT1 x n)%Q).
    { rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_const (1#2)) x n)).
      rewrite (qeqT_imp_qeq _ _ (real_const_proj (1#2) n)). reflexivity. }
(* Q bookkeeping: 0 < ex <= x_n - 0 == x_n, 0 < half*x_n <= x_n, and
       -|h_n| <= h_n *)
    assert (Hexlt : Qlt 0 ex) by (apply QltT_to_Qlt; exact Hex).
    assert (Hsub : (projT1 x n - projT1 real_zero n == projT1 x n)%Q)
      by (rewrite Hz; ring).
    assert (Hxnlt0 : Qlt 0 (projT1 x n)).
    { apply (Qlt_le_trans 0%Q ex).
      - exact Hexlt.
      - apply (Qle_trans ex (projT1 x n - projT1 real_zero n)%Q (projT1 x n)).
        + exact (Qlt_le_weak ex (projT1 x n - projT1 real_zero n)%Q
                   (QltT_to_Qlt ex (projT1 x n - projT1 real_zero n)%Q
                      (HNx n Hnx))).
        + apply QleT'_to_Qle. apply S02_CauchyComplete.qeq_leT'. apply qeq_imp_qeqT. exact Hsub. }
    assert (Hhalf0 : Qlt 0 ((1#2) * projT1 x n)%Q).
    { apply (Qmult_lt_0_compat (1#2) (projT1 x n)).
      - unfold Qlt. simpl. lia.
      - exact Hxnlt0. }
    assert (Hhalfle : Qle ((1#2) * projT1 x n) (projT1 x n)).
    { assert (Hsplit : ((1#2) * projT1 x n + (1#2) * projT1 x n
                        == projT1 x n)%Q) by ring.
      assert (H1 : Qle (0 + (1#2) * projT1 x n)%Q
                       ((1#2) * projT1 x n + (1#2) * projT1 x n)%Q).
      { apply (Qplus_le_compat 0%Q ((1#2) * projT1 x n)%Q
                               ((1#2) * projT1 x n)%Q ((1#2) * projT1 x n)%Q).
        - apply (Qlt_le_weak 0%Q). exact Hhalf0.
        - apply Qle_refl. }
      apply (Qle_trans ((1#2) * projT1 x n)
              ((1#2) * projT1 x n + (1#2) * projT1 x n)%Q (projT1 x n)).
      - apply (Qle_trans ((1#2) * projT1 x n) (0 + (1#2) * projT1 x n)%Q
                 ((1#2) * projT1 x n + (1#2) * projT1 x n)%Q).
        + apply QleT'_to_Qle. apply S02_CauchyComplete.qeq_leT'. apply qeq_imp_qeqT. ring.
        + exact H1.
      - apply QleT'_to_Qle. apply S02_CauchyComplete.qeq_leT'. apply qeq_imp_qeqT. exact Hsplit. }
    assert (Hneg : Qle (Qopp (Qabs (projT1 h n))) (projT1 h n))
      by (apply QleT'_to_Qle; apply dbi_q_opp_abs_le).
(* Assembling the literal weak chains (four limbs, three bridges) *)
    assert (Heq1 : (projT1 (real_mult (real_const (1#2)) x) n
                    - projT1 (real_abs h) n
                    == ((1#2) * projT1 x n - Qabs (projT1 h n)))%Q).
    { rewrite Hmul. rewrite Habs. reflexivity. }
    assert (Hb1 : Qle (projT1 (real_mult (real_const (1#2)) x) n
                       - projT1 (real_abs h) n)%Q
                      ((1#2) * projT1 x n - Qabs (projT1 h n))%Q)
      by (apply QleT'_to_Qle; apply S02_CauchyComplete.qeq_leT'; apply qeq_imp_qeqT; exact Heq1).
    assert (Hleg1 : Qle ((1#2) * projT1 x n - Qabs (projT1 h n))%Q
                         (projT1 x n - Qabs (projT1 h n))%Q).
    { apply QleT'_to_Qle.
      apply (dbi_qplus_le_r ((1#2) * projT1 x n) (projT1 x n)
                            (Qopp (Qabs (projT1 h n)))).
      exact Hhalfle. }
    assert (Hleg2 : Qle (projT1 x n - Qabs (projT1 h n))%Q
                         (projT1 x n + projT1 h n)).
    { apply QleT'_to_Qle.
      apply (dbi_qplus_le_l (Qopp (Qabs (projT1 h n))) (projT1 h n)
                            (projT1 x n)).
      exact Hneg. }
    assert (Hrhs : (projT1 (real_plus x h) n - projT1 real_zero n
                    == projT1 x n + projT1 h n)%Q)
      by (rewrite Hplus; rewrite Hz; ring).
    assert (Hb2 : Qle (projT1 x n + projT1 h n)
                      (projT1 (real_plus x h) n - projT1 real_zero n)%Q)
      by (apply QleT'_to_Qle; apply S02_CauchyComplete.qeq_leT'; apply qeq_imp_qeqT; apply Qeq_sym; exact Hrhs).
(* The strict part passes through directly; the weak chains merge *)
    apply Qlt_to_QltT.
    apply (Qlt_le_trans e0 (projT1 (real_mult (real_const (1#2)) x) n
                              - projT1 (real_abs h) n)%Q).
    + exact (QltT_to_Qlt e0
               (projT1 (real_mult (real_const (1#2)) x) n
                - projT1 (real_abs h) n)%Q (HN0 n Hn0)).
    + exact (Qle_trans
               (projT1 (real_mult (real_const (1#2)) x) n
                - projT1 (real_abs h) n)%Q
               ((1#2) * projT1 x n - Qabs (projT1 h n))%Q
               (projT1 (real_plus x h) n - projT1 real_zero n)%Q
               Hb1
               (Qle_trans
                  ((1#2) * projT1 x n - Qabs (projT1 h n))%Q
                  (projT1 x n - Qabs (projT1 h n))%Q
                  (projT1 (real_plus x h) n - projT1 real_zero n)%Q
                  Hleg1
                  (Qle_trans
                     (projT1 x n - Qabs (projT1 h n))%Q
                     (projT1 x n + projT1 h n)
                     (projT1 (real_plus x h) n - projT1 real_zero n)%Q
                     Hleg2 Hb2))).
Qed.

(* ================= 6. Total face <-> premise-carrying face ================= *)
(*    6a. [HasIncr] to [HasIncrPos] for a total function: the Hxh slot is
      discharged trivially. *)
Lemma dbi_hasincr_incrpos :
  forall (f : Real -> Real) (x a : Real) (Hx : real_lt real_zero x),
  HasIncr f x a ->
  HasIncrPos (fun (y : Real) (_ : real_lt real_zero y) => f y) x a Hx.
Proof.
  intros f x a Hx H eps Heps.
  destruct (H eps Heps) as [d [Hd Hstep]].
  exists d. split.
  - exact Hd.
  - intros h Hh Hxh eps' Heps'.
    exact (Hstep h Hh eps' Heps').
Qed.

(* 6b. [HasIncrPos] for a total function to [HasIncr]: take delta as the
      minimum of the given delta0 and x/2; |h| < x/2 keeps x + h positive
      (the domain condition record), with x/2 positive by
      [dbi_halfx_pos] and the bound by [dbi_abs_lt_half_add_pos]. *)
Lemma dbi_incrpos_hasincr :
  forall (f : Real -> Real) (x a : Real) (Hx : real_lt real_zero x),
  HasIncrPos (fun (y : Real) (_ : real_lt real_zero y) => f y) x a Hx ->
  HasIncr f x a.
Proof.
  intros f x a Hx H eps Heps.
  destruct (H eps Heps) as [d0 [Hd0 Hstep0]].
  assert (Hhx : real_lt real_zero (real_mult (real_const (1#2)) x))
    by (apply dbi_halfx_pos; exact Hx).
  exists (real_min d0 (real_mult (real_const (1#2)) x)). split.
  - apply real_min_pos.
    + exact Hd0.
    + exact Hhx.
  - intros h Hh eps' Heps'.
    assert (Hhd0 : real_lt (real_abs h) d0).
    { apply (abl9_min_lt_l d0 (real_mult (real_const (1#2)) x) (real_abs h)).
      exact Hh. }
    assert (Hhhalf : real_lt (real_abs h) (real_mult (real_const (1#2)) x)).
    { apply (abl9_min_lt_r d0 (real_mult (real_const (1#2)) x) (real_abs h)).
      exact Hh. }
    assert (Hxh : real_lt real_zero (real_plus x h))
      by (apply (dbi_abs_lt_half_add_pos x h Hx); exact Hhhalf).
    exact (Hstep0 h Hhd0 Hxh eps' Heps').
Qed.

(* ================= 7. The end-to-end composites ================= *)
Theorem dbi_realdiff_hasincr :
  forall (f : Real -> Real)
         (Hf : RealDifferentiable (fun (y : Real) (_ : real_lt real_zero y) => f y))
         (x : Real),
  real_lt real_zero x ->
  sigT (fun a : Real => HasIncr f x a).
Proof.
  intros f Hf x Hx.
  exists (rdf (fun (y : Real) (_ : real_lt real_zero y) => f y) Hf x Hx).
  apply (dbi_incrpos_hasincr f x _ Hx).
  apply (dbi_realdiff_hasincrpos
           (fun (y : Real) (_ : real_lt real_zero y) => f y) Hf x Hx).
Qed.

Theorem dbi_hasincr_realdiff :
  forall (f : Real -> Real),
  (forall (x : Real), real_lt real_zero x ->
     sigT (fun a : Real => HasIncr f x a)) ->
  RealDifferentiable (fun (y : Real) (_ : real_lt real_zero y) => f y).
Proof.
  intros f Hsup.
  apply (dbi_hasincrpos_realdiff
           (fun (y : Real) (_ : real_lt real_zero y) => f y)).
  intros x Hx.
  destruct (Hsup x Hx) as [a Ha].
  exists a. exact (dbi_hasincr_incrpos f x a Hx Ha).
Qed.

(* ================= Final verification: assumption closure ================= *)
Print Assumptions dbi_qplus_le_r.
Print Assumptions dbi_qplus_le_l.
Print Assumptions dbi_q_opp_abs_le.
Print Assumptions dbi_err_eq_comm.
Print Assumptions dbi_realdiff_hasincrpos.
Print Assumptions dbi_hasincrpos_realdiff.
Print Assumptions dbi_halfx_pos.
Print Assumptions dbi_abs_lt_half_add_pos.
Print Assumptions dbi_hasincr_incrpos.
Print Assumptions dbi_incrpos_hasincr.
Print Assumptions dbi_realdiff_hasincr.
Print Assumptions dbi_hasincr_realdiff.
