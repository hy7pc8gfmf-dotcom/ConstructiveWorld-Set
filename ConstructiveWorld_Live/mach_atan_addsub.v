(* ConstructiveWorld-Set -- arctan sum and difference identities for constant rational arguments. *)

(** * mach_atan_addsub: arctan addition and subtraction formulas on the rational unit domain.

    Mission.  For constant rational arguments of the arctan series this file
      proves [mach_atan_sub] (arctan u - arctan v == arctan ((u-v)/(1+u*v)),
      0 < v < u < 1) and [mach_atan_add] (arctan u + arctan v == arctan
      ((u+v)/(1-u*v)), 0 < u < 1, 0 < v < 1, u + v + u*v <= 1); both statements
      are [real_eq] between series values, obtained from the sine and cosine
      addition formulas and the turn relation [mach_sin_atan_eq_gen].

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs], [QArith.Qround],
      [QArith.Qminmax], [Lists.List], [Bool.Bool], [Arith.Arith], [Setoid],
      [Morphisms], [Lia], [extraction.Extraction], [Lqa].  Requires
      [S01_BaseRing], [S02_CauchyComplete], [S03_QExp], [S04_RealExpLogConv],
      [S05_AlignmentGRPO], [S06_DiffSamplingGibbs], [S07_RealSetoidExpLog],
      [S08_RealMainlineDPO], [S09_EntropyReal], [S10_KVQuantTrig], [S11_TP3B5],
      [S12_B5RecycleSF], [S13_NLiveAudit], [S14_B5BatchBlock] of this development.

    References.  This development, mach_atan_addsub.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" mach_atan_addsub.v] compiles cleanly
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
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               Lists.List Bool.Bool Arith.Arith.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax.
From Stdlib Require Import extraction.Extraction.
Import PropositionConvergenceCore.
From Stdlib Require Import Lqa.

(* ============================================================ *)
(* Part 0: pointwise bridge and real-ring helpers.               *)
(* ============================================================ *)

(* Qminus is a derived constant outside the ring signature; unfold it
   before reifying ring/field equations. *)
Ltac mach_qring := try unfold Qminus; ring.
Ltac mach_qfield := try unfold Qminus; field.

Lemma mach_real_zero_proj : forall n : nat, QeqT (projT1 real_zero n) 0.
Proof. intro n. unfold real_zero. reflexivity. Qed.

Lemma mach_real_eq_pt : forall a b : Real,
  (forall n : nat, QeqT (projT1 a n) (projT1 b n)) -> real_eq a b.
Proof.
  intros a b HptT eps Heps.
  pose proof (fun n : nat => qeqT_imp_qeq (projT1 a n) (projT1 b n) (HptT n)) as Hpt.
  exists 0%nat. intros n Hn.
  apply (qltT_eq_compat_l 0 (Qabs (projT1 a n - projT1 b n)) eps).
  - assert (Hz0 : Qabs 0 == 0) by (unfold Qabs; reflexivity).
    apply qeq_imp_qeqT.
    apply (Qeq_trans 0 (Qabs 0) (Qabs (projT1 a n - projT1 b n)) (Qeq_sym (Qabs 0) 0 Hz0)).
    apply Qabs_wd. rewrite Hpt. ring.
  - exact Heps.
Qed.

Lemma mach_real_const_eq : forall a b : Q, QeqT a b -> real_eq (real_const a) (real_const b).
Proof.
  intros a b HabT. pose proof (qeqT_imp_qeq a b HabT) as Hab.
  apply mach_real_eq_pt. intro n. apply qeq_imp_qeqT.
  setoid_rewrite (qeqT_imp_qeq _ _ (real_const_proj a n)). setoid_rewrite (qeqT_imp_qeq _ _ (real_const_proj b n)). exact Hab.
Qed.

Lemma mach_real_const_mult : forall a b : Q,
  real_eq (real_mult (real_const a) (real_const b)) (real_const (a * b)).
Proof.
  intros a b. apply mach_real_eq_pt. intro n. apply qeq_imp_qeqT.
  setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_const a) (real_const b) n)).
  repeat setoid_rewrite (qeqT_imp_qeq _ _ real_const_proj). reflexivity.
Qed.

Lemma mach_real_plus_assoc : forall a b c : Real,
  real_eq (real_plus a (real_plus b c)) (real_plus (real_plus a b) c).
Proof.
  intros a b c. apply mach_real_eq_pt. intro n. apply qeq_imp_qeqT.
  setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj a (real_plus b c) n)).
  setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj b c n)).
  setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_plus a b) c n)).
  setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj a b n)). ring.
Qed.

Lemma mach_real_mult_assoc : forall a b c : Real,
  real_eq (real_mult a (real_mult b c)) (real_mult (real_mult a b) c).
Proof.
  intros a b c. apply mach_real_eq_pt. intro n. apply qeq_imp_qeqT.
  setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj a (real_mult b c) n)).
  setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_mult a b) c n)).
  setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj b c n)). setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj a b n)). mach_qring.
Qed.

Lemma mach_real_mult_comm : forall a b : Real,
  real_eq (real_mult a b) (real_mult b a).
Proof.
  intros a b. apply mach_real_eq_pt. intro n. apply qeq_imp_qeqT.
  setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj a b n)). setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj b a n)). mach_qring.
Qed.

Lemma mach_real_mult_opp_r : forall a b : Real,
  real_eq (real_mult a (real_opp b)) (real_opp (real_mult a b)).
Proof.
  intros a b. apply mach_real_eq_pt. intro n. apply qeq_imp_qeqT.
  setoid_rewrite (qeqT_imp_qeq _ _ (real_opp_proj (real_mult a b) n)).
  setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj a b n)).
  setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj a (real_opp b) n)).
  setoid_rewrite (qeqT_imp_qeq _ _ (real_opp_proj b n)). mach_qring.
Qed.

Lemma mach_real_opp_opp : forall a : Real, real_eq (real_opp (real_opp a)) a.
Proof.
  intros a. apply mach_real_eq_pt. intro n. apply qeq_imp_qeqT.
  setoid_rewrite (qeqT_imp_qeq _ _ (real_opp_proj (real_opp a) n)). setoid_rewrite (qeqT_imp_qeq _ _ (real_opp_proj a n)). mach_qring.
Qed.

Lemma mach_real_mult_zero_l : forall a : Real,
  real_eq (real_mult real_zero a) real_zero.
Proof.
  intros a. apply mach_real_eq_pt. intro n. apply qeq_imp_qeqT.
  setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj real_zero a n)). rewrite (qeqT_imp_qeq _ _ (mach_real_zero_proj n)). ring.
Qed.

Lemma mach_real_const_one_mult : forall K : Real,
  real_eq (real_mult (real_const 1) K) K.
Proof.
  intro K. apply mach_real_eq_pt. intro n. apply qeq_imp_qeqT.
  setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_const 1) K n)). setoid_rewrite (qeqT_imp_qeq _ _ (real_const_proj 1 n)). ring.
Qed.

(* constant-linear combination: a*K - b*K == (a-b)*K *)
Lemma mach_real_const_lin : forall (K : Real) (aa bb : Q),
  real_eq (real_plus (real_mult (real_const aa) K) (real_opp (real_mult (real_const bb) K)))
          (real_mult (real_const (aa - bb)) K).
Proof.
  intros K aa bb. apply mach_real_eq_pt. intro n. apply qeq_imp_qeqT.
  setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult (real_const aa) K)
             (real_opp (real_mult (real_const bb) K)) n)).
  setoid_rewrite (qeqT_imp_qeq _ _ (real_opp_proj (real_mult (real_const bb) K) n)).
  setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_const aa) K n)).
  setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_const bb) K n)).
  setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_const (aa - bb)) K n)).
  setoid_rewrite (qeqT_imp_qeq _ _ (real_const_proj aa n)). setoid_rewrite (qeqT_imp_qeq _ _ (real_const_proj bb n)).
  setoid_rewrite (qeqT_imp_qeq _ _ (real_const_proj (aa - bb) n)). mach_qring.
Qed.

(* constant-linear combination, plus form: a*K + b*K == (a+b)*K *)
Lemma mach_real_const_lin2 : forall (K : Real) (aa bb : Q),
  real_eq (real_plus (real_mult (real_const aa) K) (real_mult (real_const bb) K))
          (real_mult (real_const (aa + bb)) K).
Proof.
  intros K aa bb. apply mach_real_eq_pt. intro n. apply qeq_imp_qeqT.
  setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult (real_const aa) K) (real_mult (real_const bb) K) n)).
  setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_const aa) K n)).
  setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_const bb) K n)).
  setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_const (aa + bb)) K n)).
  setoid_rewrite (qeqT_imp_qeq _ _ (real_const_proj aa n)). setoid_rewrite (qeqT_imp_qeq _ _ (real_const_proj bb n)).
  setoid_rewrite (qeqT_imp_qeq _ _ (real_const_proj (aa + bb) n)). mach_qring.
Qed.

(* product of two turned factors: (aa*cX) * (vv*cY) == (aa*vv)*(cX*cY) *)
Lemma mach_real_prod_const : forall (sX cX cY sY : Real) (uu vv : Q),
  real_eq sX (real_mult (real_const uu) cX) ->
  real_eq sY (real_mult (real_const vv) cY) ->
  real_eq (real_mult sX sY) (real_mult (real_const (uu * vv)) (real_mult cX cY)).
Proof.
  intros sX cX cY sY uu vv Hsu Hsv.
  apply (real_eq_trans _ (real_mult (real_mult (real_const uu) cX)
                                    (real_mult (real_const vv) cY))).
  - apply (RealSetoid.real_eq_mult_compat _ _ _ _); [exact Hsu | exact Hsv].
  - apply (real_eq_trans
             _ (real_mult (real_const uu) (real_mult cX (real_mult (real_const vv) cY)))).
    + apply real_eq_sym. apply mach_real_mult_assoc.
    + apply (real_eq_trans
               _ (real_mult (real_const uu) (real_mult (real_mult cX (real_const vv)) cY))).
      * apply (RealSetoid.real_eq_mult_compat _ _ _ _).
        -- apply real_eq_refl.
        -- apply mach_real_mult_assoc.
      * apply (real_eq_trans
                 _ (real_mult (real_const uu)
                              (real_mult (real_mult (real_const vv) cX) cY))).
        -- apply (RealSetoid.real_eq_mult_compat _ _ _ _).
           ++ apply real_eq_refl.
           ++ apply (RealSetoid.real_eq_mult_compat _ _ _ _).
              ** apply mach_real_mult_comm.
              ** apply real_eq_refl.
        -- apply (real_eq_trans
                    _ (real_mult (real_const uu)
                                 (real_mult (real_const vv) (real_mult cX cY)))).
           ++ apply (RealSetoid.real_eq_mult_compat _ _ _ _).
              ** apply real_eq_refl.
              ** apply real_eq_sym. apply mach_real_mult_assoc.
           ++ apply (real_eq_trans
                       _ (real_mult (real_mult (real_const uu) (real_const vv))
                                    (real_mult cX cY))).
              ** apply mach_real_mult_assoc.
              ** apply (RealSetoid.real_eq_mult_compat _ _ _ _).
                 --- exact (mach_real_const_mult uu vv).
                 --- apply real_eq_refl.
Qed.

(* linear-combination shape 1 (sine difference core):
   sX*cY + cX*(-sY) == (uu - vv)*(cX*cY)  given the turns. *)
Lemma mach_real_lin_comb1 : forall (sX cX cY sY : Real) (uu vv : Q),
  real_eq sX (real_mult (real_const uu) cX) ->
  real_eq sY (real_mult (real_const vv) cY) ->
  real_eq (real_plus (real_mult sX cY) (real_mult cX (real_opp sY)))
          (real_mult (real_const (uu - vv)) (real_mult cX cY)).
Proof.
  intros sX cX cY sY uu vv Hsu Hsv.
  apply (real_eq_trans _ (real_plus (real_mult (real_mult (real_const uu) cX) cY)
                                    (real_mult cX (real_opp (real_mult (real_const vv) cY))))).
  - apply (RealSetoid.real_eq_plus_compat _ _ _ _).
    + apply (RealSetoid.real_eq_mult_compat _ _ _ _); [exact Hsu | apply real_eq_refl].
    + apply (RealSetoid.real_eq_mult_compat _ _ _ _);
        [apply real_eq_refl | apply (RealSetoid.real_eq_opp_compat _ _); exact Hsv].
  - apply (real_eq_trans _ (real_plus (real_mult (real_const uu) (real_mult cX cY))
                                      (real_opp (real_mult (real_const vv) (real_mult cX cY))))).
    + apply (RealSetoid.real_eq_plus_compat _ _ _ _).
      * apply real_eq_sym. apply mach_real_mult_assoc.
      * apply (real_eq_trans _ (real_opp (real_mult cX (real_mult (real_const vv) cY)))).
        -- apply mach_real_mult_opp_r.
        -- apply (RealSetoid.real_eq_opp_compat _ _).
           apply (real_eq_trans _ (real_mult (real_const vv) (real_mult cX cY))).
           ++ apply (real_eq_trans
                       _ (real_mult (real_mult cX (real_const vv)) cY)).
              ** apply mach_real_mult_assoc.
              ** apply (real_eq_trans
                          _ (real_mult (real_mult (real_const vv) cX) cY)).
                 --- apply (RealSetoid.real_eq_mult_compat _ _ _ _).
                     +++ apply mach_real_mult_comm.
                     +++ apply real_eq_refl.
                 --- exact (real_eq_sym _ _
                              (mach_real_mult_assoc (real_const vv) cX cY)).
           ++ apply real_eq_refl.
    + apply mach_real_const_lin.
Qed.


(* linear-combination shape 2 (sine sum core):
   sX*cY + cX*sY == (uu + vv)*(cX*cY)  given the turns. *)
Lemma mach_real_lin_comb3 : forall (sX cX cY sY : Real) (uu vv : Q),
  real_eq sX (real_mult (real_const uu) cX) ->
  real_eq sY (real_mult (real_const vv) cY) ->
  real_eq (real_plus (real_mult sX cY) (real_mult cX sY))
          (real_mult (real_const (uu + vv)) (real_mult cX cY)).
Proof.
  intros sX cX cY sY uu vv Hsu Hsv.
  apply (real_eq_trans _ (real_plus (real_mult (real_mult (real_const uu) cX) cY)
                                    (real_mult cX (real_mult (real_const vv) cY)))).
  - apply (RealSetoid.real_eq_plus_compat _ _ _ _).
    + apply (RealSetoid.real_eq_mult_compat _ _ _ _); [exact Hsu | apply real_eq_refl].
    + apply (RealSetoid.real_eq_mult_compat _ _ _ _); [apply real_eq_refl | exact Hsv].
  - apply (real_eq_trans _ (real_plus (real_mult (real_const uu) (real_mult cX cY))
                                      (real_mult (real_const vv) (real_mult cX cY)))).
    + apply (RealSetoid.real_eq_plus_compat _ _ _ _).
      * apply real_eq_sym. apply mach_real_mult_assoc.
      * apply (real_eq_trans _ (real_mult (real_const vv) (real_mult cX cY))).
        -- apply (real_eq_trans
                    _ (real_mult (real_mult cX (real_const vv)) cY)).
           ++ apply mach_real_mult_assoc.
           ++ apply (real_eq_trans
                       _ (real_mult (real_mult (real_const vv) cX) cY)).
              ** apply (RealSetoid.real_eq_mult_compat _ _ _ _).
                 --- apply mach_real_mult_comm.
                 --- apply real_eq_refl.
              ** exact (real_eq_sym _ _
                           (mach_real_mult_assoc (real_const vv) cX cY)).
        -- apply real_eq_refl.
    + apply mach_real_const_lin2.
Qed.


(* cosine difference shape: cX*cY + sX*sY == (1 + uu*vv)*(cX*cY). *)
Lemma mach_shape_cos_diff : forall (sX cX sY cY : Real) (uu vv : Q),
  real_eq sX (real_mult (real_const uu) cX) ->
  real_eq sY (real_mult (real_const vv) cY) ->
  real_eq (real_plus (real_mult cX cY) (real_mult sX sY))
          (real_mult (real_const (1 + uu * vv)) (real_mult cX cY)).
Proof.
  intros sX cX sY cY uu vv Hsu Hsv.
  apply (real_eq_trans _ (real_plus (real_mult (real_const 1) (real_mult cX cY))
                                    (real_mult (real_const (uu * vv)) (real_mult cX cY)))).
  - apply (RealSetoid.real_eq_plus_compat _ _ _ _).
    + apply real_eq_sym. apply mach_real_const_one_mult.
    + exact (mach_real_prod_const sX cX cY sY uu vv Hsu Hsv).
  - exact (mach_real_const_lin2 (real_mult cX cY) 1 (uu * vv)).
Qed.

(* cosine sum shape: cX*cY - sX*sY == (1 - uu*vv)*(cX*cY). *)
Lemma mach_shape_cos_sum : forall (sX cX sY cY : Real) (uu vv : Q),
  real_eq sX (real_mult (real_const uu) cX) ->
  real_eq sY (real_mult (real_const vv) cY) ->
  real_eq (real_plus (real_mult cX cY) (real_opp (real_mult sX sY)))
          (real_mult (real_const (1 - uu * vv)) (real_mult cX cY)).
Proof.
  intros sX cX sY cY uu vv Hsu Hsv.
  apply (real_eq_trans _ (real_plus (real_mult (real_const 1) (real_mult cX cY))
                                    (real_opp (real_mult (real_const (uu * vv)) (real_mult cX cY))))).
  - apply (RealSetoid.real_eq_plus_compat _ _ _ _).
    + apply real_eq_sym. apply mach_real_const_one_mult.
    + apply (RealSetoid.real_eq_opp_compat _ _).
      exact (mach_real_prod_const sX cX cY sY uu vv Hsu Hsv).
  - exact (mach_real_const_lin (real_mult cX cY) 1 (uu * vv)).
Qed.

(* second-order linear combination (difference of a turned pair):
   sD*cZ - (bb*M)*(ww*cZ) == (aa - bb*ww)*(M*cZ). *)
Lemma mach_real_lin_comb2 : forall (sD cD M cZ : Real) (aa bb ww : Q),
  real_eq sD (real_mult (real_const aa) M) ->
  real_eq cD (real_mult (real_const bb) M) ->
  real_eq (real_plus (real_mult sD cZ) (real_opp (real_mult cD (real_mult (real_const ww) cZ))))
          (real_mult (real_const (aa - bb * ww)) (real_mult M cZ)).
Proof.
  intros sD cD M cZ aa bb ww HsD HcD.
  apply (real_eq_trans _ (real_plus (real_mult (real_mult (real_const aa) M) cZ)
                                    (real_opp (real_mult (real_mult (real_const bb) M)
                                                         (real_mult (real_const ww) cZ))))).
  - apply (RealSetoid.real_eq_plus_compat _ _ _ _).
    + apply (RealSetoid.real_eq_mult_compat _ _ _ _); [exact HsD | apply real_eq_refl].
    + apply (RealSetoid.real_eq_opp_compat _ _).
      apply (RealSetoid.real_eq_mult_compat _ _ _ _); [exact HcD | apply real_eq_refl].
  - apply (real_eq_trans _ (real_plus (real_mult (real_const aa) (real_mult M cZ))
                                      (real_opp (real_mult (real_const (bb * ww)) (real_mult M cZ))))).
    + apply (RealSetoid.real_eq_plus_compat _ _ _ _).
      * apply real_eq_sym. apply mach_real_mult_assoc.
      * apply (RealSetoid.real_eq_opp_compat _ _).
        apply (real_eq_trans _ (real_mult (real_const bb)
                                  (real_mult M (real_mult (real_const ww) cZ)))).
        -- exact (real_eq_sym _ _
                    (mach_real_mult_assoc (real_const bb) M
                       (real_mult (real_const ww) cZ))).
        -- apply (real_eq_trans _ (real_mult (real_const bb)
                                        (real_mult (real_const ww) (real_mult M cZ)))).
           ++ apply (RealSetoid.real_eq_mult_compat _ _ _ _).
              ** apply real_eq_refl.
              ** apply (real_eq_trans
                          _ (real_mult (real_mult M (real_const ww)) cZ)).
                 --- apply mach_real_mult_assoc.
                 --- apply (real_eq_trans
                             _ (real_mult (real_mult (real_const ww) M) cZ)).
                    +++ apply (RealSetoid.real_eq_mult_compat _ _ _ _).
                        ---- apply mach_real_mult_comm.
                        ---- apply real_eq_refl.
                    +++ exact (real_eq_sym _ _
                                 (mach_real_mult_assoc (real_const ww) M cZ)).
           ++ apply (real_eq_trans
                       _ (real_mult (real_mult (real_const bb) (real_const ww))
                                    (real_mult M cZ))).
              ** apply mach_real_mult_assoc.
              ** apply (RealSetoid.real_eq_mult_compat _ _ _ _).
                 --- exact (mach_real_const_mult bb ww).
                 --- apply real_eq_refl.
    + exact (mach_real_const_lin (real_mult M cZ) aa (bb * ww)).
Qed.


(* ============================================================ *)
(* Part 1: pointwise domain certificates.                        *)
(* ============================================================ *)

Lemma mach_pt_bound_of_lt : forall u : Q, QltT 0 u -> QltT u 1 ->
  forall n : nat, QleT' (Qabs (projT1 (real_const u) n)) 1.
Proof.
  intros u Hu0T Hu1T n.
  pose proof (QltT_to_Qlt 0 u Hu0T) as Hu0.
  pose proof (QltT_to_Qlt u 1 Hu1T) as Hu1.
  apply Qle_to_QleT'.
  apply (Qle_trans _ (Qabs u) _).
  - apply QleT'_to_Qle.
    apply qeq_imp_qle.
    apply qeq_imp_qeqT.
    apply (Qabs_wd (projT1 (real_const u) n) u).
    apply qeqT_imp_qeq. apply real_const_proj.
  - assert (Habs : Qabs u == u) by (apply Qabs_pos; apply Qlt_le_weak; exact Hu0).
    rewrite Habs. apply Qlt_le_weak. exact Hu1.
Qed.

Lemma mach_pt_bound_of_le : forall u : Q, QltT 0 u -> QleT' u 1 ->
  forall n : nat, QleT' (Qabs (projT1 (real_const u) n)) 1.
Proof.
  intros u Hu0T Hu1T n.
  pose proof (QltT_to_Qlt 0 u Hu0T) as Hu0.
  pose proof (QleT'_to_Qle u 1 Hu1T) as Hu1.
  apply Qle_to_QleT'.
  apply (Qle_trans _ (Qabs u) _).
  - apply QleT'_to_Qle.
    apply qeq_imp_qle.
    apply qeq_imp_qeqT.
    apply (Qabs_wd (projT1 (real_const u) n) u).
    apply qeqT_imp_qeq. apply real_const_proj.
  - assert (Habs : Qabs u == u) by (apply Qabs_pos; apply Qlt_le_weak; exact Hu0).
    rewrite Habs. exact Hu1.
Qed.

Lemma mach_q_abs_le_one : forall q : Q, QltT 0 q -> QleT' q 1 -> QleT' (Qabs q) 1.
Proof.
  intros q Hq0T Hq1T.
  pose proof (QltT_to_Qlt 0 q Hq0T) as Hq0.
  pose proof (QleT'_to_Qle q 1 Hq1T) as Hq1.
  apply Qle_to_QleT'.
  assert (Habs : Qabs q == q) by (apply Qabs_pos; apply Qlt_le_weak; exact Hq0).
  rewrite Habs. exact Hq1.
Qed.

(* ============================================================ *)
(* Part 2: Q-side bounds for the Möbius transform arguments.     *)
(* ============================================================ *)

Lemma mach_w_sub_pos : forall u v : Q, QltT 0 v -> QltT v u -> QltT u 1 ->
  QltT 0 ((u - v) / (1 + u * v)).
Proof.
  intros u v Hv0T HvuT Hu1T.
  pose proof (QltT_to_Qlt 0 v Hv0T) as Hv0.
  pose proof (QltT_to_Qlt v u HvuT) as Hvu.
  pose proof (QltT_to_Qlt u 1 Hu1T) as Hu1.
  apply Qlt_to_QltT.
  assert (Hn : (0 < u - v)%Q) by lra.
  assert (Hu0 : (0 < u)%Q) by exact (Qlt_trans 0 v u Hv0 Hvu).
  assert (Hub : (0 < u * v)%Q) by (apply Qmult_lt_0_compat; [exact Hu0 | exact Hv0]).
  assert (Hd : (0 < 1 + u * v)%Q) by lra.
  unfold Qdiv.
  apply Qmult_lt_0_compat.
  - exact Hn.
  - apply Qinv_lt_0_compat. exact Hd.
Qed.

Lemma mach_w_sub_lt : forall u v : Q, QltT 0 v -> QltT v u -> QltT u 1 ->
  QltT ((u - v) / (1 + u * v)) 1.
Proof.
  intros u v Hv0T HvuT Hu1T.
  pose proof (QltT_to_Qlt 0 v Hv0T) as Hv0.
  pose proof (QltT_to_Qlt v u HvuT) as Hvu.
  pose proof (QltT_to_Qlt u 1 Hu1T) as Hu1.
  apply Qlt_to_QltT.
  assert (Hu0 : (0 < u)%Q) by exact (Qlt_trans 0 v u Hv0 Hvu).
  assert (Hub : (0 < u * v)%Q) by (apply Qmult_lt_0_compat; [exact Hu0 | exact Hv0]).
  assert (Hd : (0 < 1 + u * v)%Q) by lra.
  destruct (Qlt_le_dec ((u - v) / (1 + u * v)) 1) as [H | H].
  - exact H.
  - exfalso.
    assert (Hm : (1 * (1 + u * v) <= ((u - v) / (1 + u * v)) * (1 + u * v))%Q)
      by (apply Qmult_le_compat_r; [exact H | apply Qlt_le_weak; exact Hd]).
    assert (Hden : (((u - v) / (1 + u * v)) * (1 + u * v) == (u - v))%Q).
    { unfold Qdiv. field.
      intro Hzz. apply (Qlt_irrefl 0).
      rewrite Hzz in Hd. exact Hd. }
    assert (Hc : ((1 + u * v) <= (u - v))%Q).
    { exact (proj1 (Qle_comp (1 * (1 + u * v)) (1 + u * v) (Qmult_1_l (1 + u * v))
                             ((u - v) / (1 + u * v) * (1 + u * v)) (u - v) Hden) Hm). }
    assert (Hk : (u * (1 - v) < 1 * (1 - v))%Q)
      by (apply Qmult_lt_compat_r; [lra | exact Hu1]).
    assert (Hkr : (u * (1 - v) == u - u * v)%Q) by mach_qring.
    assert (Hkr2 : (1 * (1 - v) == 1 - v)%Q) by mach_qring.
    lra.
Qed.

Lemma mach_w_add_pos : forall u v : Q, QltT 0 u -> QltT 0 v -> QleT' (u + v + u * v) 1 ->
  QltT 0 ((u + v) / (1 - u * v)).
Proof.
  intros u v Hu0T Hv0T HleT.
  pose proof (QltT_to_Qlt 0 u Hu0T) as Hu0.
  pose proof (QltT_to_Qlt 0 v Hv0T) as Hv0.
  pose proof (QleT'_to_Qle (u + v + u * v) 1 HleT) as Hle.
  apply Qlt_to_QltT.
  assert (Hn : (0 < u + v)%Q) by lra.
  assert (Hd : (0 < 1 - u * v)%Q) by lra.
  unfold Qdiv.
  apply Qmult_lt_0_compat.
  - exact Hn.
  - apply Qinv_lt_0_compat. exact Hd.
Qed.

Lemma mach_w_add_le : forall u v : Q, QltT 0 v -> QleT' (u + v + u * v) 1 ->
  QleT' ((u + v) / (1 - u * v)) 1.
Proof.
  intros u v Hv0T HleT.
  pose proof (QltT_to_Qlt 0 v Hv0T) as Hv0.
  pose proof (QleT'_to_Qle (u + v + u * v) 1 HleT) as Hle.
  apply Qle_to_QleT'.
  assert (Hd : (0 < 1 - u * v)%Q).
  - destruct (Qlt_le_dec 0 u) as [Hup | Hun].
    + assert (Hub : (0 < u * v)%Q)
        by (apply Qmult_lt_0_compat; [exact Hup | exact Hv0]).
      lra.
    + assert (Hub : (u * v <= 0 * v)%Q)
        by (apply Qmult_le_compat_r; [exact Hun | apply Qlt_le_weak; exact Hv0]).
      lra.
  - destruct (Qlt_le_dec 1 ((u + v) / (1 - u * v))) as [Hgt | Hle1].
    + exfalso.
      assert (Hm : (1 * (1 - u * v) < ((u + v) / (1 - u * v)) * (1 - u * v))%Q)
        by (apply Qmult_lt_compat_r; [exact Hd | exact Hgt]).
      assert (Hden : (((u + v) / (1 - u * v)) * (1 - u * v) == (u + v))%Q).
      { unfold Qdiv. field.
        intro Hzz. apply (Qlt_irrefl 0).
        rewrite Hzz in Hd. exact Hd. }
      assert (Hc : ((1 - u * v) < (u + v))%Q).
      { exact (proj1 (Qlt_compat (1 * (1 - u * v)) (1 - u * v) (Qmult_1_l (1 - u * v))
                              ((u + v) / (1 - u * v) * (1 - u * v)) (u + v) Hden) Hm). }
      lra.
    + exact Hle1.
Qed.

(* ============================================================ *)
(* Part 3: turn relations  sin(arctan q) == q * cos(arctan q).   *)
(* ============================================================ *)

(* Extensionality of the arctan partial sums: equal rational arguments
   give equal partial sums at every index (Qeq congruence, by induction
   on the index). *)
Lemma mach_q_pow_ext : forall (m : nat) (a b : Q),
  QeqT a b -> QeqT (q_pow a m) (q_pow b m).
Proof.
  intro m. induction m as [| m IHm]; intros a b Hab.
  - reflexivity.
  - cbn [q_pow]. apply qeq_imp_qeqT. apply Qmult_comp.
    + exact (qeqT_imp_qeq _ _ Hab).
    + exact (qeqT_imp_qeq _ _ (IHm a b Hab)).
Qed.

Lemma mach_arctan_partial_ext : forall (n : nat) (a b : Q),
  QeqT a b -> QeqT (arctan_partial n a) (arctan_partial n b).
Proof.
  intro n. induction n as [| m IHm]; intros a b Hab.
  - cbn [arctan_partial]. unfold arctan_term. apply qeq_imp_qeqT. apply Qmult_comp.
    + reflexivity.
    + unfold Qdiv. apply Qmult_comp.
      * exact (qeqT_imp_qeq _ _ (mach_q_pow_ext (2 * 0 + 1)%nat a b Hab)).
      * reflexivity.
  - cbn [arctan_partial]. apply qeq_imp_qeqT. apply Qplus_comp.
    + exact (qeqT_imp_qeq _ _ (IHm a b Hab)).
    + unfold arctan_term. apply Qmult_comp.
      * reflexivity.
      * unfold Qdiv. apply Qmult_comp;
          [ exact (qeqT_imp_qeq _ _ (mach_q_pow_ext (2 * Datatypes.S m + 1)%nat a b Hab))
          | reflexivity ].
Qed.

Lemma mach_sin_atan_eq_gen : forall (q : Q) (Hq0T : QltT 0 q)
  (Hq : forall n : nat, QleT' (Qabs (projT1 (real_const q) n)) 1),
  real_eq (cauchy_real_sin (cauchy_real_arctan (real_const q) Hq))
          (real_mult (real_const q)
                     (cauchy_real_cos (cauchy_real_arctan (real_const q) Hq))).
Proof.
  intros q Hq0T Hq.
  pose proof (QltT_to_Qlt 0 q Hq0T) as Hq0.
  destruct (Qeq_dec q 1) as [Heq | Hneq].
  - (* q == 1 : transfer from b5b_endpoint *)
    set (A1 := cauchy_real_arctan (real_const 1) atan1_pt_bound).
    assert (HA : real_eq (cauchy_real_arctan (real_const q) Hq) A1).
    { apply mach_real_eq_pt. intro n. apply qeq_imp_qeqT. unfold A1.
      setoid_rewrite (qeqT_imp_qeq _ _ (arctan_real_proj (real_const q) Hq n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (arctan_real_proj (real_const 1) atan1_pt_bound n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_const_proj q n)). setoid_rewrite (qeqT_imp_qeq _ _ (real_const_proj 1 n)).
      exact (qeqT_imp_qeq _ _ (mach_arctan_partial_ext n q 1 (qeq_imp_qeqT q 1 Heq))). }
    apply (real_eq_trans _ (real_mult (real_const 1)
                     (cauchy_real_cos (cauchy_real_arctan (real_const q) Hq)))).
    + apply (real_eq_trans _ (cauchy_real_sin A1)).
      * apply real_sin_eq_compat. exact HA.
      * apply (real_eq_trans _ (real_mult (real_const 1) (cauchy_real_cos A1))).
        -- apply (real_eq_minus_zero _ _).
           exact (b5b_endpoint b5dS_E_zero_on_unit).
        -- apply (RealSetoid.real_eq_mult_compat _ _ _ _).
           ++ apply real_eq_refl.
           ++ apply real_cos_eq_compat. exact (real_eq_sym _ _ HA).
    + apply (RealSetoid.real_eq_mult_compat _ _ _ _).
      * apply mach_real_const_eq. apply qeq_imp_qeqT. exact (Qeq_sym _ _ Heq).
      * apply real_eq_refl.
  - (* q < 1 : direct discharge from the rational turn relation *)
    assert (Hlt : Qlt q 1).
    { destruct (Qlt_le_dec q 1) as [H | H].
      - exact H.
      - exfalso.
        assert (Habsq : Qabs q == q) by (apply Qabs_pos; apply Qlt_le_weak; exact Hq0).
        assert (Hdom : Qle q 1).
        { exact (proj1 (Qle_comp (Qabs q) q Habsq 1 1 (Qeq_refl 1))
                       (QleT'_to_Qle _ _ (Hq 0%nat))). }
        apply Hneq. exact (Qle_antisym q 1 Hdom H). }
    apply (real_eq_minus_zero _ _).
    exact (b5dQ_E_rational_zero q (Qlt_to_QltT 0 q Hq0) (Qlt_to_QltT q 1 Hlt) Hq).
Qed.

(* ============================================================ *)
(* Part 4: pointwise angle bounds for constant arguments.        *)
(* ============================================================ *)

Lemma mach_q3_le : forall q : Q, QleT' 0 q -> QleT' q 1 -> QleT' (q * q * q) q.
Proof.
  intros q H0T H1T.
  pose proof (QleT'_to_Qle 0 q H0T) as H0.
  pose proof (QleT'_to_Qle q 1 H1T) as H1.
  apply Qle_to_QleT'.
  assert (Hqq : (q * q <= q)%Q).
  { apply (Qle_trans (q * q) (q * 1) q).
    - rewrite (Qmult_comm q 1). apply (Qmult_le_compat_r q 1 q H1 H0).
    - rewrite Qmult_1_r. apply Qle_refl. }
  apply (Qle_trans (q * q * q) (q * q) q).
  - apply (Qmult_le_compat_r (q * q) q q Hqq H0).
  - exact Hqq.
Qed.

Lemma mach_q5_le3 : forall q : Q, QleT' 0 q -> QleT' q 1 -> QleT' (q*q*q*q*q) (q*q*q).
Proof.
  intros q H0T H1T.
  pose proof (QleT'_to_Qle 0 q H0T) as H0.
  pose proof (QleT'_to_Qle q 1 H1T) as H1.
  apply Qle_to_QleT'.
  assert (Hqq : (q * q <= q)%Q).
  { apply (Qle_trans (q * q) (q * 1) q).
    - rewrite (Qmult_comm q 1). apply (Qmult_le_compat_r q 1 q H1 H0).
    - rewrite Qmult_1_r. apply Qle_refl. }
  assert (Hq3 : (q*q*q <= q*q)%Q).
  { apply (Qmult_le_compat_r (q * q) q q Hqq H0). }
  assert (Hq4 : (q*q*q*q <= q*q*q)%Q).
  { apply (Qmult_le_compat_r (q*q*q) (q*q) q Hq3 H0). }
  apply (Qle_trans (q*q*q*q*q) (q*q*q*q) (q*q*q)).
  - apply (Qmult_le_compat_r (q*q*q*q) (q*q*q) q Hq4 H0).
  - exact Hq4.
Qed.

Lemma mach_qinv_one : QeqT (Qinv (1#1)) 1.
Proof. vm_compute. reflexivity. Qed.

Lemma mach_qinv_three : QeqT (Qinv (3#1)) (1#3).
Proof. vm_compute. reflexivity. Qed.

Lemma mach_qdiv_one : forall x : Q, QeqT (x / (1#1)) x.
Proof. intro x. apply qeq_imp_qeqT. unfold Qdiv. rewrite (qeqT_imp_qeq _ _ mach_qinv_one). apply Qmult_1_r. Qed.

Lemma mach_qdiv_three : forall x : Q, QeqT (x / (3#1)) (x * (1#3)).
Proof. intro x. apply qeq_imp_qeqT. unfold Qdiv. rewrite (qeqT_imp_qeq _ _ mach_qinv_three). apply Qeq_refl. Qed.

Lemma mach_qfact_one : QeqT (q_fact (Datatypes.S (2*0))) (1#1).
Proof. vm_compute. reflexivity. Qed.

Lemma mach_qinv_five : QeqT (Qinv (5#1)) (1#5).
Proof. vm_compute. reflexivity. Qed.

Lemma mach_qdiv_five : forall x : Q, QeqT (x / (5#1)) (x * (1#5)).
Proof. intro x. apply qeq_imp_qeqT. unfold Qdiv. rewrite (qeqT_imp_qeq _ _ mach_qinv_five). apply Qeq_refl. Qed.

Lemma mach_qinv_nine : QeqT (Qinv (9#1)) (1#9).
Proof. vm_compute. reflexivity. Qed.

Lemma mach_qdiv_nine : forall x : Q, QeqT (x / (9#1)) (x * (1#9)).
Proof. intro x. apply qeq_imp_qeqT. unfold Qdiv. rewrite (qeqT_imp_qeq _ _ mach_qinv_nine). apply Qeq_refl. Qed.

Lemma mach_qminus_0 : forall x : Q, QeqT (x - 0) x.
Proof.
  intro x. apply qeq_imp_qeqT. unfold Qminus.
  assert (Ez0 : Qopp 0 == 0) by (vm_compute; reflexivity).
  rewrite Ez0. apply Qplus_0_r.
Qed.

Lemma mach_atan_p1 : forall q : Q, QeqT (arctan_partial 1 q) (q - q*q*q*(1#3)).
Proof.
  intro q.
  apply qeq_imp_qeqT.
  change (arctan_partial 1 q) with (arctan_partial 0 q + arctan_term 1 q).
  change (arctan_partial 0 q) with (arctan_term 0 q).
  unfold arctan_term.
  change (q_pow (-1) 0) with (1#1).
  change (q_pow (-1) 1) with ((-1)#1).
  change (q_pow q (2*0+1)) with (q * (1#1)).
  change (q_pow q (2*1+1)) with (q * (q * (q * (1#1)))).
  change (Z.of_nat (2*0+1)) with 1%Z.
  change (Z.of_nat (2*1+1)) with 3%Z.
  rewrite (fun w : Q => qeqT_imp_qeq _ _ (mach_qdiv_one w)).
  rewrite (fun w : Q => qeqT_imp_qeq _ _ (mach_qdiv_three w)).
  rewrite Qmult_1_l.
  ring.
Qed.

Lemma mach_atan_p0 : forall q : Q, QeqT (arctan_partial 0 q) q.
Proof.
  intro q.
  apply qeq_imp_qeqT.
  change (arctan_partial 0 q) with (arctan_term 0 q).
  unfold arctan_term.
  change (q_pow (-1) 0) with (1#1).
  change (q_pow q (2*0+1)) with (q * (1#1)).
  change (Z.of_nat (2*0+1)) with 1%Z.
  rewrite (fun w : Q => qeqT_imp_qeq _ _ (mach_qdiv_one w)). ring.
Qed.

Lemma mach_q_pow_minus_one_even : forall i : nat, QeqT (q_pow (-1) (2*i)) 1.
Proof.
  induction i as [| i IH].
  - reflexivity.
  - apply qeq_imp_qeqT.
    replace (2*(Datatypes.S i))%nat with (Datatypes.S (Datatypes.S (2*i))) by lia.
    setoid_rewrite (qeqT_imp_qeq _ _ (q_pow_succ (-1) (Datatypes.S (2*i)))).
    setoid_rewrite (qeqT_imp_qeq _ _ (q_pow_succ (-1) (2*i))).
    rewrite (qeqT_imp_qeq _ _ IH). reflexivity.
Qed.

Lemma mach_qnegneg_mul : forall u v : Q, QeqT ((-u) * (-v)) (u * v).
Proof. intros. apply qeq_imp_qeqT. ring. Qed.

Lemma mach_q_pow_opp_even : forall (j : nat) (y : Q), QeqT (q_pow (-y) (2*j)) (q_pow y (2*j)).
Proof.
  intro j. induction j as [| j IH]; intro y.
  - reflexivity.
  - apply qeq_imp_qeqT.
    replace (2*(Datatypes.S j))%nat with (Datatypes.S (Datatypes.S (2*j))) by lia.
    change (q_pow (-y) (Datatypes.S (Datatypes.S (2*j)))) with ((-y) * q_pow (-y) (Datatypes.S (2*j))).
    change (q_pow (-y) (Datatypes.S (2*j))) with ((-y) * q_pow (-y) (2*j)).
    change (q_pow y (Datatypes.S (Datatypes.S (2*j)))) with (y * q_pow y (Datatypes.S (2*j))).
    change (q_pow y (Datatypes.S (2*j))) with (y * q_pow y (2*j)).
    rewrite (qeqT_imp_qeq _ _ (IH y)).
    rewrite !Qmult_assoc.
    apply (Qmult_comp ((-y) * (-y)) (y * y) (qeqT_imp_qeq _ _ (mach_qnegneg_mul y y))).
    apply Qeq_refl.
Qed.

Lemma mach_qneg1_mul : forall u : Q, QeqT (- u) ((-1#1) * u).
Proof. intro u. apply qeq_imp_qeqT. ring. Qed.

Lemma mach_qopp_add : forall a b : Q, QeqT (- (a + b)) (- a + - b).
Proof. intros a b. apply qeq_imp_qeqT. ring. Qed.

Lemma mach_qmul_div_neg1_l : forall c a b : Q,
  QeqT (c * (((-1#1) * a) / b)) (- (c * (a / b))).
Proof.
  intros c a b. apply qeq_imp_qeqT. unfold Qdiv.
  rewrite (qeqT_imp_qeq _ _ (mach_qneg1_mul (c * (a * Qinv b)))).
  exact (Qeq_trans _ _ _
    (Qmult_comp c c (Qeq_refl c) (((-1#1) * a) * Qinv b) ((-1#1) * (a * Qinv b))
       (Qeq_sym _ _ (Qmult_assoc (-1#1) a (Qinv b))))
    (Qeq_trans _ _ _
       (Qmult_assoc c (-1#1) (a * Qinv b))
       (Qeq_trans _ _ _
          (Qmult_comp (c * (-1#1)) ((-1#1) * c) (Qmult_comm c (-1#1))
             (a * Qinv b) (a * Qinv b) (Qeq_refl (a * Qinv b)))
          (Qeq_sym _ _ (Qmult_assoc (-1#1) c (a * Qinv b)))))).
Qed.

Lemma mach_qmul_neg1_l_assoc : forall u v : Q,
  QeqT (((-1#1) * u) * v) ((-1#1) * (u * v)).
Proof. intros u v. apply qeq_imp_qeqT. exact (Qeq_sym _ _ (Qmult_assoc (-1#1) u v)). Qed.

Lemma mach_sin_term_odd : forall (j : nat) (y : Q), QeqT (sin_term j (-y)) (- (sin_term j y)).
Proof.
  intros j y. unfold sin_term.
  apply qeq_imp_qeqT.
  change (q_pow (-y) (Datatypes.S (2*j))) with ((-y) * q_pow (-y) (2*j)).
  change (q_pow y (Datatypes.S (2*j))) with (y * q_pow y (2*j)).
  rewrite (qeqT_imp_qeq _ _ (mach_q_pow_opp_even j y)).
  rewrite (qeqT_imp_qeq _ _ (mach_qneg1_mul y)).
  rewrite (qeqT_imp_qeq _ _ (mach_qmul_neg1_l_assoc y (q_pow y (2*j)))).
  rewrite (qeqT_imp_qeq _ _
             (mach_qmul_div_neg1_l (q_pow (-1) j) (y * q_pow y (2*j))
                                (q_fact (Datatypes.S (2*j))))).
  reflexivity.
Qed.

Lemma mach_sin_partial_odd : forall (n : nat) (y : Q),
  QeqT (sin_partial n (-y)) (- (sin_partial n y)).
Proof.
  intro n. induction n as [| n IH]; intro y.
  - apply qeq_imp_qeqT. unfold sin_partial, sin_term.
    change (q_pow (-1) 0) with ((1#1)).
    change (q_pow (-y) (Datatypes.S (2*0))) with ((-y) * q_pow (-y) (2*0)).
    change (q_pow y (Datatypes.S (2*0))) with (y * q_pow y (2*0)).
    change (q_pow (-y) (2*0)) with ((1#1)).
    change (q_pow y (2*0)) with ((1#1)).
    rewrite (qeqT_imp_qeq _ _ mach_qfact_one).
    rewrite !(fun w : Q => qeqT_imp_qeq _ _ (mach_qdiv_one w)).
    ring.
  - cbn [sin_partial]. apply qeq_imp_qeqT. rewrite (qeqT_imp_qeq _ _ (IH y)).
    rewrite (qeqT_imp_qeq _ _ (mach_sin_term_odd (Datatypes.S n) y)).
    apply Qeq_sym. exact (qeqT_imp_qeq _ _ (mach_qopp_add (sin_partial n y) (sin_term (Datatypes.S n) y))).
Qed.

(* Pointwise lower bound: every partial sum stays above q/3. *)
Lemma mach_atan_pt_lower : forall (q : Q) (Hq0T : QltT 0 q) (Hq1 : QleT' (Qabs q) 1),
  forall n : nat, QltT ((1#3)*q) (arctan_partial n q).
Proof.
  intros q Hq0T Hq1 n.
  pose proof (QltT_to_Qlt 0 q Hq0T) as Hq0.
  apply Qlt_to_QltT.
  assert (Hq1q : (q <= 1)%Q).
  { assert (Habsq : Qabs q == q) by (apply Qabs_pos; apply Qlt_le_weak; exact Hq0).
    exact (proj1 (Qle_comp (Qabs q) q Habsq 1 1 (Qeq_refl 1)) (QleT'_to_Qle _ _ Hq1)). }
  assert (Hq3 : (q*q*q <= q)%Q)
    by (apply QleT'_to_Qle; apply mach_q3_le; [apply Qle_to_QleT'; apply Qlt_le_weak; exact Hq0 |
                           apply Qle_to_QleT'; exact Hq1q]).
  assert (Hq53 : (q*q*q*q*q <= q*q*q)%Q)
    by (apply QleT'_to_Qle; apply mach_q5_le3; [apply Qle_to_QleT'; apply Qlt_le_weak; exact Hq0 |
                            apply Qle_to_QleT'; exact Hq1q]).
  assert (H43 : (4*(q*q*q) < 5*q)%Q) by lra.
  destruct n as [| n].
  - rewrite (qeqT_imp_qeq _ _ (mach_atan_p0 q)).
    assert (Hb13 : ((1#3) * q < 1 * q)%Q)
      by (apply (Qmult_lt_compat_r (1#3) 1 q Hq0); unfold Qlt; simpl; lia).
    lra.
  - assert (Hle : (1 <= Datatypes.S n)%nat) by lia.
    pose proof (atan_tail_bound q 1 (Datatypes.S n) Hq1 Hle) as Hb.
    assert (Hbl : Qle (- (arctan_partial (Datatypes.S n) q - arctan_partial 1 q)) (atan_mag 2 q)).
    { apply (Qle_trans _ (Qabs (- (arctan_partial (Datatypes.S n) q - arctan_partial 1 q)))).
      - apply Qle_Qabs.
      - rewrite Qabs_opp. exact (QleT'_to_Qle _ _ Hb). }
    assert (Habsq : Qabs q == q) by (apply Qabs_pos; apply Qlt_le_weak; exact Hq0).
    assert (Hmag : atan_mag 2 q == q*q*q*q*q*(1#5)).
    { unfold atan_mag. rewrite Habsq.
      change (q_pow q (2*2+1)) with (q * (q * (q * (q * (q * (1#1)))))).
      change (Z.of_nat (2*2+1)) with 5%Z.
      rewrite (fun w : Q => qeqT_imp_qeq _ _ (mach_qdiv_five w)). ring. }
    rewrite Hmag in Hbl.
    rewrite (qeqT_imp_qeq _ _ (mach_atan_p1 q)) in Hbl.
    lra.
Qed.

(* Pointwise upper bound: from index 3 on, every partial sum stays
   strictly below 13/15 (uniform in 0 < q <= 1, with the boundary case
   q = 1 anchored at the partial sum of order 3). *)
Lemma mach_atan_pt_upper : forall (q : Q) (Hq0T : QltT 0 q) (Hq1 : QleT' (Qabs q) 1),
  forall n : nat, (3 <= n)%nat -> QltT (arctan_partial n q) (13#15).
Proof.
  intros q Hq0T Hq1 n Hn.
  pose proof (QltT_to_Qlt 0 q Hq0T) as Hq0.
  apply Qlt_to_QltT.
  assert (Hq1q : (q <= 1)%Q).
  { assert (Habsq : Qabs q == q) by (apply Qabs_pos; apply Qlt_le_weak; exact Hq0).
    exact (proj1 (Qle_comp (Qabs q) q Habsq 1 1 (Qeq_refl 1)) (QleT'_to_Qle _ _ Hq1)). }
  assert (Hq2 : (q*q <= 1)%Q).
  { apply (Qle_trans (q*q) (q*1) 1).
    - rewrite (Qmult_comm q 1). apply (Qmult_le_compat_r q 1 q Hq1q (Qlt_le_weak 0 q Hq0)).
    - rewrite Qmult_1_r. exact Hq1q. }
  destruct (Qeq_dec q 1) as [Heq | Hneq].
  - (* q == 1 : anchor at the order-3 partial sum, tail 1/9 *)
    rewrite Heq.
    pose proof (atan_tail_bound q 3 n Hq1 Hn) as Ht.
    assert (HA : Qabs q == Qabs 1) by (apply Qabs_wd; exact Heq).
    assert (Hmag1 : atan_mag 4 q == atan_mag 4 1).
    { unfold atan_mag, Qdiv. apply Qmult_comp.
      - exact (qeqT_imp_qeq _ _ (mach_q_pow_ext (2*4+1) (Qabs q) (Qabs 1) (qeq_imp_qeqT (Qabs q) (Qabs 1) HA))).
      - reflexivity. }
    assert (Ht2 : Qle (arctan_partial n 1 - arctan_partial 3 1) (atan_mag 4 1)).
    { apply (proj1 (Qle_comp
        (arctan_partial n q - arctan_partial 3 q)
        (arctan_partial n 1 - arctan_partial 3 1)
        (Qminus_comp (arctan_partial n q) (arctan_partial n 1)
          (qeqT_imp_qeq _ _ (mach_arctan_partial_ext n q 1 (qeq_imp_qeqT q 1 Heq)))
          (arctan_partial 3 q) (arctan_partial 3 1)
          (qeqT_imp_qeq _ _ (mach_arctan_partial_ext 3 q 1 (qeq_imp_qeqT q 1 Heq))))
        (atan_mag 4 q) (atan_mag 4 1) Hmag1)).
      apply (Qle_trans _ (Qabs (arctan_partial n q - arctan_partial 3 q))).
      - apply Qle_Qabs.
      - exact (QleT'_to_Qle _ _ Ht). }
    assert (Hmag : atan_mag 4 1 == (1#9)).
    { unfold atan_mag. change (Qabs 1) with (1#1). setoid_rewrite (qeqT_imp_qeq _ _ (sc_q_pow_one (2*4+1))).
      change (Z.of_nat (2*4+1)) with 9%Z. rewrite (qeqT_imp_qeq _ _ (mach_qdiv_nine (1#1))). ring. }
    rewrite Hmag in Ht2.
    assert (Hp3 : arctan_partial 3 1 == (76#105)).
    { vm_compute. reflexivity. }
    rewrite Hp3 in Ht2.
    lra.
  - (* q < 1 : anchor at the order-1 partial sum, tail q^5/5 *)
    assert (Hlt : Qlt q 1).
    { destruct (Qle_lt_or_eq q 1 Hq1q) as [Hl | Heq'].
      - exact Hl.
      - exfalso. apply Hneq. exact Heq'. }
    assert (Hn1 : (1 <= n)%nat) by lia.
    pose proof (atan_tail_bound q 1 n Hq1 Hn1) as Ht.
    assert (Ht2 : Qle (arctan_partial n q - arctan_partial 1 q) (atan_mag 2 q)).
    { apply (Qle_trans _ (Qabs (arctan_partial n q - arctan_partial 1 q))).
      - apply Qle_Qabs.
      - exact (QleT'_to_Qle _ _ Ht). }
    assert (Habsq : Qabs q == q) by (apply Qabs_pos; apply Qlt_le_weak; exact Hq0).
    assert (Hmag : atan_mag 2 q == q*q*q*q*q*(1#5)).
    { unfold atan_mag. rewrite Habsq.
      change (q_pow q (2*2+1)) with (q * (q * (q * (q * (q * (1#1)))))).
      change (Z.of_nat (2*2+1)) with 5%Z.
      rewrite (fun w : Q => qeqT_imp_qeq _ _ (mach_qdiv_five w)). ring. }
    rewrite Hmag in Ht2.
    assert (Hq3 : (q*q*q <= q)%Q)
      by (apply QleT'_to_Qle; apply mach_q3_le; [apply Qle_to_QleT'; apply Qlt_le_weak; exact Hq0 |
                           apply Qle_to_QleT'; exact Hq1q]).
    assert (Hq53 : (q*q*q*q*q <= q*q*q)%Q)
      by (apply QleT'_to_Qle; apply mach_q5_le3; [apply Qle_to_QleT'; apply Qlt_le_weak; exact Hq0 |
                            apply Qle_to_QleT'; exact Hq1q]).
    assert (Hfac : (0 < (1 - q) * (13 - 2*q - 2*(q*q)))%Q).
    { apply Qmult_lt_0_compat.
      - lra.
      - lra. }
    assert (Heqf : ((1 - q) * (13 - 2*q - 2*(q*q)) == 13 - 15*q + 2*(q*q*q))%Q) by ring.
    assert (Hge : (0 < 13 - 15*q + 2*(q*q*q))%Q) by (rewrite <- Heqf; exact Hfac).
    rewrite (qeqT_imp_qeq _ _ (mach_atan_p1 q)) in Ht2.
    lra.
Qed.

(* Real-level order bounds for constant-argument arctan values. *)
Lemma mach_atan_lower_real : forall (q : Q) (Hq0T : QltT 0 q) (Hq1 : QleT' (Qabs q) 1)
  (cert : forall n : nat, QleT' (Qabs (projT1 (real_const q) n)) 1),
  real_lt real_zero (cauchy_real_arctan (real_const q) cert).
Proof.
  intros q Hq0T Hq1 cert. unfold real_lt.
  pose proof (QltT_to_Qlt 0 q Hq0T) as Hq0.
  exists ((1#3)*q). split.
  - apply Qlt_to_QltT. apply Qmult_lt_0_compat.
    + change (Qlt 0 (1#3)). unfold Qlt. simpl. lia.
    + exact Hq0.
  - exists 0%nat. intros n Hn.
    apply Qlt_to_QltT.
    setoid_rewrite (qeqT_imp_qeq _ _ (arctan_real_proj (real_const q) cert n)).
    setoid_rewrite (qeqT_imp_qeq _ _ (real_const_proj q n)).
    rewrite (qeqT_imp_qeq _ _ (mach_real_zero_proj n)).
    pose proof (QltT_to_Qlt _ _ (mach_atan_pt_lower q Hq0T Hq1 n)) as Hlow.
    lra.
Qed.

Lemma mach_atan_upper_real : forall (q : Q) (Hq0T : QltT 0 q) (Hq1 : QleT' (Qabs q) 1)
  (cert : forall n : nat, QleT' (Qabs (projT1 (real_const q) n)) 1),
  real_lt (cauchy_real_arctan (real_const q) cert) (real_const 1).
Proof.
  intros q Hq0T Hq1 cert. unfold real_lt.
  pose proof (QltT_to_Qlt 0 q Hq0T) as Hq0.
  exists (2#15). split.
  - apply Qlt_to_QltT. change (Qlt 0 (2#15)). unfold Qlt. simpl. lia.
  - exists 3%nat. intros n Hn.
    apply Qlt_to_QltT.
    setoid_rewrite (qeqT_imp_qeq _ _ (arctan_real_proj (real_const q) cert n)).
    setoid_rewrite (qeqT_imp_qeq _ _ (real_const_proj q n)).
    setoid_rewrite (qeqT_imp_qeq _ _ (real_const_proj 1 n)).
    pose proof (QltT_to_Qlt _ _ (mach_atan_pt_upper q Hq0T Hq1 n (NatLe_drop 3 n Hn))) as Hub.
    lra.
Qed.

(* ============================================================ *)
(* Part 5: explicit linear gap for the sine partial sums:        *)
(* sin_partial n y >= y/3 for all n and 0 <= y <= 2.             *)
(* ============================================================ *)

Lemma mach_sin_pair_even_pos : forall (i : nat) (y : Q), QleT' 0 y -> QleT' y 2 ->
  QleT' 0 (sin_term (2*i) y + sin_term (Datatypes.S (2*i)) y).
Proof.
  intros i y Hy0T Hy2T.
  pose proof (QleT'_to_Qle 0 y Hy0T) as Hy0.
  pose proof (QleT'_to_Qle y 2 Hy2T) as Hy2.
  apply Qle_to_QleT'.
  assert (Hy2' : (y*y <= 4)%Q).
  { apply (Qle_trans (y*y) (2*y) 4).
    - apply (Qmult_le_compat_r y 2 y Hy2 Hy0).
    - lra. }
  set (d2 := (Z.of_nat (4*i+2) # 1)).
  set (d3 := (Z.of_nat (4*i+3) # 1)).
  assert (Hd2 : (2 <= d2)%Q) by (unfold d2; unfold Qle; simpl; lia).
  assert (Hd3 : (3 <= d3)%Q) by (unfold d3; unfold Qle; simpl; lia).
  assert (Hpos : (0 < d2 * d3)%Q) by (apply Qmult_lt_0_compat; lra).
  assert (Hf1 : (0 < q_fact (4*i+1))%Q) by exact (QltT_to_Qlt _ _ (q_fact_pos (4*i+1))).
  assert (Hne1 : ~ (q_fact (4*i+1) == 0)).
  { intro Hzz. apply (Qlt_irrefl 0). rewrite Hzz in Hf1. exact Hf1. }
  assert (Hnep : ~ ((d2 * d3) == 0)).
  { intro Hzz. apply (Qlt_irrefl 0). rewrite Hzz in Hpos. exact Hpos. }
  assert (Hd2' : (0 < d2)%Q) by lra.
  assert (Hd3' : (0 < d3)%Q) by lra.
  assert (HposD : (0 < d3 * d2)%Q) by (apply Qmult_lt_0_compat; assumption).
  assert (HneD : ~ ((d3 * d2) * q_fact (4*i+1) == 0)).
  { intro Hzz. apply (Qlt_irrefl 0).
    pose proof (Qmult_lt_0_compat (d3 * d2) (q_fact (4*i+1)) HposD Hf1) as Hpp.
    rewrite Hzz in Hpp. exact Hpp. }
  unfold sin_term.
  replace (2*(2*i)+1)%nat with (4*i+1)%nat by lia.
  replace (Datatypes.S (2*(Datatypes.S (2*i)))) with (4*i+3)%nat by lia.
  replace (Datatypes.S (2*(2*i)))%nat with (4*i+1)%nat by lia.
  rewrite (qeqT_imp_qeq _ _ (mach_q_pow_minus_one_even i)).
  rewrite Qmult_1_l.
  assert (Hm1 : q_pow (-1) (Datatypes.S (2*i)) == (-1)%Q).
  { setoid_rewrite (qeqT_imp_qeq _ _ (q_pow_succ (-1) (2*i))). rewrite (qeqT_imp_qeq _ _ (mach_q_pow_minus_one_even i)). ring. }
  rewrite Hm1.
  assert (Hf3 : q_fact (4*i+3) == (d3 * d2) * q_fact (4*i+1)).
  { unfold d2, d3.
    replace (4*i+3)%nat with (Datatypes.S (4*i+2))%nat by lia.
    setoid_rewrite (qeqT_imp_qeq _ _ (q_fact_succ (4*i+2))).
    replace (4*i+2)%nat with (Datatypes.S (4*i+1))%nat by lia.
    setoid_rewrite (qeqT_imp_qeq _ _ (q_fact_succ (4*i+1))).
    replace (Z.of_nat (4*i+3)) with (Z.of_nat (Datatypes.S (Datatypes.S (4*i+1)))) by lia.
    rewrite Qmult_assoc. reflexivity. }
  rewrite Hf3.
  assert (Hp3 : q_pow y (4*i+3) == q_pow y (4*i+1) * (y*y)).
  { replace (4*i+3)%nat with ((4*i+1)+2)%nat by lia.
    setoid_rewrite (qeqT_imp_qeq _ _ (atan_q_pow_add y (4*i+1) 2)).
    change (q_pow y 2%nat) with (y * (y * (1#1))).
    ring. }
  rewrite Hp3.
  assert (Heq : q_pow y (4*i+1) / q_fact (4*i+1) +
                -1 * (q_pow y (4*i+1) * (y*y) / (d3 * d2 * q_fact (4*i+1))) ==
                q_pow y (4*i+1) / q_fact (4*i+1) * (1 - (y*y) / (d2 * d3))).
  { unfold Qdiv. repeat rewrite Qinv_mult_distr. ring. }
  apply (proj1 (Qle_comp 0 0 (Qeq_refl 0)
    (q_pow y (4*i+1) / q_fact (4*i+1) * (1 - (y*y) / (d2 * d3)))
    (q_pow y (4*i+1) / q_fact (4*i+1) +
     -1 * (q_pow y (4*i+1) * (y*y) / (d3 * d2 * q_fact (4*i+1))))
    (Qeq_sym _ _ Heq))).
  apply Qmult_le_0_compat.
  - unfold Qdiv. apply Qmult_le_0_compat.
    + apply QleT'_to_Qle. apply q_pow_nonneg. apply Qle_to_QleT'. exact Hy0.
    + apply Qinv_le_0_compat. apply Qlt_le_weak. exact Hf1.
  - apply (Qlt_le_weak 0 (1 - (y*y) / (d2 * d3))).
    assert (Heq2 : 1 - (y*y)/(d2*d3) == ((d2*d3) - (y*y))/((d2*d3))).
    { unfold Qdiv, Qminus.
      assert (Hr : (d2*d3)*Qinv (d2*d3) == 1)
        by (apply Qmult_inv_r; exact Hnep).
      assert (Hd : (Qplus (d2*d3) (Qopp (y*y)))*Qinv (d2*d3) ==
                   (d2*d3)*Qinv (d2*d3) + Qopp ((y*y)*Qinv (d2*d3))) by ring.
      rewrite Hd. rewrite Hr. apply Qeq_refl. }
    rewrite Heq2. unfold Qdiv. apply Qmult_lt_0_compat.
    + assert (H03 : (0 < 3)%Q) by (unfold Qlt; simpl; lia).
      assert (Hdd : (2 * 3 <= d2 * d3)%Q).
      { assert (Hs1 : (2 * 3 <= 3 * d2)%Q).
        { pose proof (Qmult_le_compat_r 2 d2 3 Hd2 (Qlt_le_weak 0 3 H03)) as Hx.
          rewrite (Qmult_comm d2 3) in Hx. exact Hx. }
        assert (Hs2 : (3 * d2 <= d2 * d3)%Q).
        { pose proof (Qmult_le_compat_r 3 d3 d2 Hd3 (Qlt_le_weak 0 d2 Hd2')) as Hx.
          rewrite (Qmult_comm d3 d2) in Hx. exact Hx. }
        exact (Qle_trans (2*3) (3*d2) (d2*d3) Hs1 Hs2). }
      lra.
    + apply Qinv_lt_0_compat. exact Hpos.
Qed.

Lemma mach_sin_term_even_pos : forall (j : nat) (y : Q), QleT' 0 y ->
  QleT' 0 (sin_term (2*j) y).
Proof.
  intros j y Hy0T.
  pose proof (QleT'_to_Qle 0 y Hy0T) as Hy0.
  apply Qle_to_QleT'.
  unfold sin_term.
  rewrite (qeqT_imp_qeq _ _ (mach_q_pow_minus_one_even j)).
  replace (2*(2*j)+1)%nat with (4*j+1)%nat by lia.
  replace (Datatypes.S (2*(2*j)))%nat with (4*j+1)%nat by lia.
  apply Qmult_le_0_compat.
  - apply (Qlt_le_weak 0 1). unfold Qlt. simpl. lia.
  - unfold Qdiv. apply Qmult_le_0_compat.
    + apply QleT'_to_Qle. apply q_pow_nonneg. apply Qle_to_QleT'. exact Hy0.
    + apply Qinv_le_0_compat. apply Qlt_le_weak. exact (QltT_to_Qlt _ _ (q_fact_pos (4*j+1))).
Qed.

Lemma mach_sin_odd_chain : forall (y : Q), QleT' 0 y -> QleT' y 2 -> forall i : nat,
  QleT' (y - y*y*y*(1#6)) (sin_partial (2*i+1) y).
Proof.
  intros y Hy0T Hy2T i.
  pose proof (QleT'_to_Qle 0 y Hy0T) as Hy0.
  pose proof (QleT'_to_Qle y 2 Hy2T) as Hy2.
  apply Qle_to_QleT'.
  induction i as [| i IH].
  - replace (2*0+1)%nat with 1%nat by lia.
    assert (Hdef : sin_partial 1 y == y - y*y*y*(1#6)).
    { cbn [sin_partial]. unfold sin_term, q_pow, Qdiv. cbn. ring. }
    rewrite Hdef. apply Qle_refl.
  - replace (2*(Datatypes.S i)+1)%nat with (Datatypes.S (Datatypes.S (2*i+1)))%nat by lia.
    assert (Hstep : sin_partial (Datatypes.S (Datatypes.S (2*i+1))) y ==
                    sin_partial (2*i+1) y + (sin_term (Datatypes.S (2*i+1)) y +
                                             sin_term (Datatypes.S (Datatypes.S (2*i+1))) y)).
    { cbn [sin_partial]. symmetry. apply Qplus_assoc. }
    rewrite Hstep.
    apply (Qle_trans _ (sin_partial (2*i+1) y)).
    + exact IH.
    + assert (Hpair : Qle 0 (sin_term (Datatypes.S (2*i+1)) y +
                              sin_term (Datatypes.S (Datatypes.S (2*i+1))) y)).
      { replace (Datatypes.S (2*i+1))%nat with (2*(Datatypes.S i))%nat by lia.
        exact (QleT'_to_Qle _ _
                (mach_sin_pair_even_pos (Datatypes.S i) y Hy0T Hy2T)). }
      lra.
Qed.

Lemma mach_sin_gap : forall (y : Q), QleT' 0 y -> QleT' y 2 -> forall n : nat,
  QleT' ((1#3)*y) (sin_partial n y).
Proof.
  intros y Hy0T Hy2T n.
  pose proof (QleT'_to_Qle 0 y Hy0T) as Hy0.
  pose proof (QleT'_to_Qle y 2 Hy2T) as Hy2.
  apply Qle_to_QleT'.
  destruct n as [| n].
  - assert (Hdef : sin_partial 0 y == y)
      by (cbn [sin_partial]; unfold sin_term, q_pow, Qdiv; cbn; ring).
    rewrite Hdef. lra.
  - destruct n as [| n].
    + replace (Datatypes.S 0)%nat with 1%nat by lia.
      assert (Hdef : sin_partial 1 y == y - y*y*y*(1#6))
        by (cbn [sin_partial]; unfold sin_term, q_pow, Qdiv; cbn; ring).
      rewrite Hdef.
      assert (Hy3 : (y*y*y <= 2*(2*y))%Q).
      { assert (Hyy : (y*y <= 2*y)%Q) by (apply (Qmult_le_compat_r y 2 y Hy2 Hy0)).
        assert (H02 : (0 <= 2)%Q) by (unfold Qle; simpl; lia).
        assert (Hzy : (0 <= 2*y)%Q) by (apply (Qmult_le_0_compat 2 y H02 Hy0)).
        apply (Qle_trans ((y*y)*y) ((2*y)*y) (2*(2*y))).
        - apply (Qmult_le_compat_r (y*y) (2*y) y Hyy Hy0).
        - rewrite (Qmult_comm (2*y) y).
          apply (Qmult_le_compat_r y 2 (2*y) Hy2 Hzy). }
      lra.
    + destruct (Nat.Even_or_Odd n) as [[m Hm] | [m Hm]].
      * replace n with (2*m)%nat by lia.
        replace (Datatypes.S (Datatypes.S (2*m)))%nat with (Datatypes.S (2*m+1))%nat by lia.
        assert (Hy3 : (y*y*y <= 2*(2*y))%Q).
        { assert (Hyy : (y*y <= 2*y)%Q) by (apply (Qmult_le_compat_r y 2 y Hy2 Hy0)).
          assert (H02 : (0 <= 2)%Q) by (unfold Qle; simpl; lia).
          assert (Hzy : (0 <= 2*y)%Q) by (apply (Qmult_le_0_compat 2 y H02 Hy0)).
          apply (Qle_trans ((y*y)*y) ((2*y)*y) (2*(2*y))).
          - apply (Qmult_le_compat_r (y*y) (2*y) y Hyy Hy0).
          - rewrite (Qmult_comm (2*y) y).
            apply (Qmult_le_compat_r y 2 (2*y) Hy2 Hzy). }
        apply (Qle_trans _ (y - y*y*y*(1#6))).
        -- lra.
        -- assert (Hstep : sin_partial (Datatypes.S (2*m+1)) y ==
                            sin_partial (2*m+1) y + sin_term (Datatypes.S (2*m+1)) y)
             by (cbn [sin_partial]; reflexivity).
           rewrite Hstep.
           assert (Hpair : Qle 0 (sin_term (Datatypes.S (2*m+1)) y))
             by (replace (Datatypes.S (2*m+1))%nat with (2*(Datatypes.S m))%nat by lia;
                 exact (QleT'_to_Qle _ _
                         (mach_sin_term_even_pos (Datatypes.S m) y Hy0T))).
           apply (Qle_trans _ (sin_partial (2*m+1) y)).
           ++ exact (QleT'_to_Qle _ _ (mach_sin_odd_chain y Hy0T Hy2T m)).
           ++ lra.
      * replace n with (2*m+1)%nat by lia.
        replace (Datatypes.S (Datatypes.S (2*m+1)))%nat with (2*(Datatypes.S m)+1)%nat by lia.
        apply (Qle_trans _ (y - y*y*y*(1#6))).
        -- assert (Hy3 : (y*y*y <= 2*(2*y))%Q).
           { assert (Hyy : (y*y <= 2*y)%Q) by (apply (Qmult_le_compat_r y 2 y Hy2 Hy0)).
             assert (H02 : (0 <= 2)%Q) by (unfold Qle; simpl; lia).
             assert (Hzy : (0 <= 2*y)%Q) by (apply (Qmult_le_0_compat 2 y H02 Hy0)).
             apply (Qle_trans ((y*y)*y) ((2*y)*y) (2*(2*y))).
             + apply (Qmult_le_compat_r (y*y) (2*y) y Hyy Hy0).
             + rewrite (Qmult_comm (2*y) y).
               apply (Qmult_le_compat_r y 2 (2*y) Hy2 Hzy). }
           lra.
        -- exact (QleT'_to_Qle _ _
                    (mach_sin_odd_chain y Hy0T Hy2T (Datatypes.S m))).
Qed.

(* ============================================================ *)
(* Part 6: constructive squeeze — a terminal sine-zero on        *)
(* (-2, 2) forces the argument to be zero.                       *)
(* ============================================================ *)

Lemma mach_sin_zero_uniq : forall (E : Real),
  real_lt (real_const (-2#1)) E -> real_lt E (real_const (2#1)) ->
  real_eq (cauchy_real_sin E) real_zero -> real_eq E real_zero.
Proof.
  intros E Hlo Hup Hs eps Heps.
  destruct (real_lt_lower_pt (-2#1) E Hlo) as [Nlo HNlo].
  destruct (real_lt_upper_pt (2#1) E Hup) as [Nup HNup].
  assert (Heps3 : QltT 0 (eps / 3)) by (apply (qltT_div_pos eps 3 Heps qltT_0_3)).
  destruct (Hs (eps/3) Heps3) as [Nsin HNsin].
  exists (Nat.max Nsin (Nat.max Nlo Nup)). intros n Hn.
  assert (Hnmax : (Nat.max Nsin (Nat.max Nlo Nup) <= n)%nat) by (apply NatLe_drop; exact Hn).
  assert (Hn1 : (Nsin <= n)%nat) by lia.
  assert (Hn2 : (Nlo <= n)%nat) by lia.
  assert (Hn3 : (Nup <= n)%nat) by lia.
  pose proof (HNlo n Hn2) as HEl.
  pose proof (HNup n Hn3) as HEu.
  pose proof (HNsin n (NatLe_lift Nsin n Hn1)) as HS.
  assert (HSq : Qlt (Qabs (sin_partial n (projT1 E n))) (eps / 3)).
  { apply QltT_to_Qlt.
    apply (qltT_eq_compat_l
             (Qabs (projT1 (cauchy_real_sin E) n - projT1 real_zero n))
             (Qabs (sin_partial n (projT1 E n))) (eps / 3)).
    - apply qeq_imp_qeqT.
      apply Qeq_trans with (Qabs (sin_partial n (projT1 E n) - 0)%Q).
      + apply Qabs_wd. apply Qminus_comp.
        * apply qeqT_imp_qeq. exact (real_sin_proj E n).
        * exact (qeqT_imp_qeq _ _ (mach_real_zero_proj n)).
      + apply Qabs_wd. exact (qeqT_imp_qeq _ _ (mach_qminus_0 _)).
    - exact HS. }
  set (y := projT1 E n) in *.
  destruct (Qeq_dec y 0) as [Hy0 | Hy0ne].
  - apply (qltT_eq_compat_l (Qabs (0 - 0)%Q) (Qabs (y - projT1 real_zero n)) eps).
    + apply qeq_imp_qeqT. apply Qeq_sym. apply Qabs_wd. apply Qminus_comp.
      * exact Hy0.
      * exact (qeqT_imp_qeq _ _ (mach_real_zero_proj n)).
    + change (Qabs (0 - 0)%Q) with 0%Q. exact Heps.
  - destruct (Qlt_le_dec 0 y) as [Hypos | Hyneg].
    + pose proof (QleT'_to_Qle _ _
                    (mach_sin_gap y (Qle_to_QleT' 0 y (Qlt_le_weak 0 y Hypos))
                       (Qle_to_QleT' y 2 (Qlt_le_weak y 2 HEu)) n)) as Hgap.
      assert (Hsp : Qabs (sin_partial n y) == sin_partial n y).
      { apply Qabs_pos. apply (Qle_trans _ ((1#3)*y)); [lra | exact Hgap]. }
      assert (H1 : Qlt ((1#3)*y) (eps / 3)).
      { rewrite <- Hsp in Hgap.
        apply (Qle_lt_trans _ (Qabs (sin_partial n y))).
        - exact Hgap.
        - exact HSq. }
      assert (H03 : (0 < 3)%Q) by (unfold Qlt; simpl; lia).
      pose proof (Qmult_lt_compat_r ((1#3)*y) (eps / 3) 3 H03 H1) as H2.
      assert (E3y : ((1#3)*y) * 3 == y) by ring.
      assert (E3e : (eps / 3) * 3 == eps).
      { unfold Qdiv. rewrite (qeqT_imp_qeq _ _ mach_qinv_three). ring. }
      rewrite E3y in H2. rewrite E3e in H2.
      apply (qltT_eq_compat_l (Qabs y) (Qabs (y - projT1 real_zero n)) eps).
      * apply qeq_imp_qeqT. apply Qeq_sym. apply Qabs_wd.
        apply (Qeq_trans _ (y - 0)%Q).
        -- apply (Qminus_comp y y (Qeq_refl y) (projT1 real_zero n) 0
                    (qeqT_imp_qeq _ _ (mach_real_zero_proj n))).
        -- exact (qeqT_imp_qeq _ _ (mach_qminus_0 _)).
      * apply (qltT_eq_compat_l y (Qabs y) eps).
        -- apply qeq_imp_qeqT. apply Qeq_sym. apply Qabs_pos. apply Qlt_le_weak. exact Hypos.
        -- apply Qlt_to_QltT. exact H2.
    + assert (Hyn : Qlt y 0).
      { destruct (Qlt_le_dec y 0) as [H | H]; [exact H |].
        exfalso. apply Hy0ne. apply (Qle_antisym y 0); [exact Hyneg | exact H]. }
      assert (Hyp : Qle 0 (-y)) by lra.
      assert (Hy2n : Qle (-y) 2) by lra.
      pose proof (QleT'_to_Qle _ _
                    (mach_sin_gap (-y) (Qle_to_QleT' 0 (-y) Hyp)
                       (Qle_to_QleT' (-y) 2 Hy2n) n)) as Hgap.
      assert (Hodd : sin_partial n y == - sin_partial n (-y)).
      { rewrite (qeqT_imp_qeq _ _ (mach_sin_partial_odd n y)). symmetry. apply Qopp_involutive. }
      assert (Hsp : Qabs (sin_partial n y) == sin_partial n (-y)).
      { rewrite Hodd. rewrite Qabs_opp.
        apply Qabs_pos. apply (Qle_trans _ ((1#3)*(-y))); [lra | exact Hgap]. }
      rewrite <- Hsp in Hgap.
      assert (H1 : Qlt ((1#3)*(-y)) (eps / 3)).
      { apply (Qle_lt_trans _ (Qabs (sin_partial n y))); [exact Hgap | exact HSq]. }
      assert (H03 : (0 < 3)%Q) by (unfold Qlt; simpl; lia).
      pose proof (Qmult_lt_compat_r ((1#3)*(-y)) (eps / 3) 3 H03 H1) as H2.
      assert (E3y : ((1#3)*(-y)) * 3 == (-y)) by ring.
      assert (E3e : (eps / 3) * 3 == eps).
      { unfold Qdiv. rewrite (qeqT_imp_qeq _ _ mach_qinv_three). ring. }
      rewrite E3y in H2. rewrite E3e in H2.
      apply (qltT_eq_compat_l (Qabs (-y)) (Qabs (y - projT1 real_zero n)) eps).
      * apply qeq_imp_qeqT.
        apply (Qeq_trans _ (Qabs y)).
        -- apply Qabs_opp.
        -- apply (Qeq_trans _ (Qabs (y - 0)%Q)).
           ++ apply Qeq_sym. apply Qabs_wd. exact (qeqT_imp_qeq _ _ (mach_qminus_0 _)).
           ++ apply Qabs_wd.
              apply (Qminus_comp y y (Qeq_refl y) (projT1 real_zero n) 0
                       (qeqT_imp_qeq _ _ (mach_real_zero_proj n))).
      * apply (qltT_eq_compat_l (-y) (Qabs (-y)) eps).
        -- apply qeq_imp_qeqT. apply Qeq_sym. apply Qabs_pos. exact Hyp.
        -- apply Qlt_to_QltT. exact H2.
Qed.

(* ============================================================ *)
(* Part 7: the subtraction formula.                              *)
(* ============================================================ *)

Lemma mach_atan_sub : forall (u v : Q) (Hv0T : QltT 0 v) (HvuT : QltT v u)
  (Hu1T : QltT u 1),
  real_eq (real_plus (cauchy_real_arctan (real_const u)
                                  (mach_pt_bound_of_lt u
                                     (qleT'_ltT_ltT 0 v u (qltT_leT' 0 v Hv0T) HvuT)
                                     Hu1T))
                     (real_opp (cauchy_real_arctan (real_const v)
                                  (mach_pt_bound_of_lt v Hv0T
                                     (qleT'_ltT_ltT v u 1 (qltT_leT' v u HvuT) Hu1T)))))
          (cauchy_real_arctan (real_const ((u - v) / (1 + u * v)))
                              (mach_pt_bound_of_lt ((u - v) / (1 + u * v))
                                                   (mach_w_sub_pos u v Hv0T HvuT Hu1T)
                                                   (mach_w_sub_lt u v Hv0T HvuT Hu1T))).
Proof.
  intros u v Hv0T HvuT Hu1T.
  pose proof (QltT_to_Qlt 0 v Hv0T) as Hv0.
  pose proof (QltT_to_Qlt v u HvuT) as Hvu.
  pose proof (QltT_to_Qlt u 1 Hu1T) as Hu1.
  pose proof (Qlt_trans 0 v u Hv0 Hvu) as Hu0.
  pose proof (Qlt_trans v u 1 Hvu Hu1) as Hv1.
  pose proof (mach_w_sub_pos u v Hv0T HvuT Hu1T) as Hw0T.
  pose proof (QltT_to_Qlt _ _ Hw0T) as Hw0.
  pose proof (mach_w_sub_lt u v Hv0T HvuT Hu1T) as Hw1T.
  pose proof (QltT_to_Qlt _ _ Hw1T) as Hw1.
  pose proof (qleT'_ltT_ltT 0 v u (qltT_leT' 0 v Hv0T) HvuT) as Hu0T.
  pose proof (qleT'_ltT_ltT v u 1 (qltT_leT' v u HvuT) Hu1T) as Hv1T.
  pose proof (mach_sin_atan_eq_gen u Hu0T (mach_pt_bound_of_lt u Hu0T Hu1T)) as HTu.
  pose proof (mach_sin_atan_eq_gen v Hv0T (mach_pt_bound_of_lt v Hv0T Hv1T)) as HTv.
  pose proof (mach_sin_atan_eq_gen ((u - v) / (1 + u * v)) Hw0T
              (mach_pt_bound_of_lt ((u - v) / (1 + u * v)) Hw0T Hw1T)) as HTw.
  set (X := cauchy_real_arctan (real_const u) (mach_pt_bound_of_lt u Hu0T Hu1T)) in *.
  set (Y := cauchy_real_arctan (real_const v) (mach_pt_bound_of_lt v Hv0T Hv1T)) in *.
  set (Z := cauchy_real_arctan (real_const ((u - v) / (1 + u * v)))
                               (mach_pt_bound_of_lt ((u - v) / (1 + u * v)) Hw0T Hw1T)) in *.
  set (cXY := real_mult (cauchy_real_cos X) (cauchy_real_cos Y)) in *.
  (* difference-angle trig values *)
  assert (HsD : real_eq (cauchy_real_sin (real_plus X (real_opp Y)))
                        (real_mult (real_const (u - v)) cXY)).
  { apply (real_eq_trans _ (real_plus (real_mult (cauchy_real_sin X) (cauchy_real_cos (real_opp Y)))
                                      (real_mult (cauchy_real_cos X) (cauchy_real_sin (real_opp Y))))).
    - exact (rs_add_sin X (real_opp Y)).
    - apply (real_eq_trans _ (real_plus (real_mult (cauchy_real_sin X) (cauchy_real_cos Y))
                                        (real_mult (cauchy_real_cos X) (real_opp (cauchy_real_sin Y))))).
      + apply (RealSetoid.real_eq_plus_compat _ _ _ _).
        * apply (RealSetoid.real_eq_mult_compat _ _ _ _); [apply real_eq_refl | apply real_cos_opp].
        * apply (RealSetoid.real_eq_mult_compat _ _ _ _); [apply real_eq_refl | apply real_sin_opp].
      + exact (mach_real_lin_comb1 (cauchy_real_sin X) (cauchy_real_cos X)
                                   (cauchy_real_cos Y) (cauchy_real_sin Y) u v HTu HTv). }
  assert (HcD : real_eq (cauchy_real_cos (real_plus X (real_opp Y)))
                        (real_mult (real_const (1 + u * v)) cXY)).
  { apply (real_eq_trans _ (real_plus (real_mult (cauchy_real_cos X) (cauchy_real_cos (real_opp Y)))
                                      (real_opp (real_mult (cauchy_real_sin X) (cauchy_real_sin (real_opp Y)))))).
    - exact (rs_add_cos X (real_opp Y)).
    - apply (real_eq_trans _ (real_plus (real_mult (cauchy_real_cos X) (cauchy_real_cos Y))
                                        (real_opp (real_mult (cauchy_real_sin X) (real_opp (cauchy_real_sin Y)))))).
      + apply (RealSetoid.real_eq_plus_compat _ _ _ _).
        * apply (RealSetoid.real_eq_mult_compat _ _ _ _); [apply real_eq_refl | apply real_cos_opp].
        * apply (RealSetoid.real_eq_opp_compat _ _).
          apply (RealSetoid.real_eq_mult_compat _ _ _ _); [apply real_eq_refl | apply real_sin_opp].
      + apply (real_eq_trans _ (real_plus (real_mult (cauchy_real_cos X) (cauchy_real_cos Y))
                                          (real_mult (cauchy_real_sin X) (cauchy_real_sin Y)))).
        * apply (RealSetoid.real_eq_plus_compat _ _ _ _).
          -- apply real_eq_refl.
          -- apply (real_eq_trans _ (real_opp (real_opp (real_mult (cauchy_real_sin X) (cauchy_real_sin Y))))).
             ++ exact (RealSetoid.real_eq_opp_compat
                         (real_mult (cauchy_real_sin X) (real_opp (cauchy_real_sin Y)))
                         (real_opp (real_mult (cauchy_real_sin X) (cauchy_real_sin Y)))
                         (mach_real_mult_opp_r (cauchy_real_sin X) (cauchy_real_sin Y))).
             ++ apply mach_real_opp_opp.
        * exact (mach_shape_cos_diff (cauchy_real_sin X) (cauchy_real_cos X)
                                     (cauchy_real_sin Y) (cauchy_real_cos Y) u v HTu HTv). }
  (* sin((X - Y) - Z) == 0 *)
  assert (HsE : real_eq (cauchy_real_sin (real_plus (real_plus X (real_opp Y)) (real_opp Z)))
                        (real_mult (real_const ((u - v) - (1 + u * v) * ((u - v) / (1 + u * v))))
                                   (real_mult cXY (cauchy_real_cos Z)))).
  { apply (real_eq_trans _ (real_plus
              (real_mult (cauchy_real_sin (real_plus X (real_opp Y))) (cauchy_real_cos (real_opp Z)))
              (real_mult (cauchy_real_cos (real_plus X (real_opp Y))) (cauchy_real_sin (real_opp Z))))).
    - exact (rs_add_sin (real_plus X (real_opp Y)) (real_opp Z)).
    - apply (real_eq_trans _ (real_plus
                (real_mult (cauchy_real_sin (real_plus X (real_opp Y))) (cauchy_real_cos Z))
                (real_opp (real_mult (cauchy_real_cos (real_plus X (real_opp Y)))
                                     (real_mult (real_const ((u - v) / (1 + u * v)))
                                                (cauchy_real_cos Z)))))).
      + apply (RealSetoid.real_eq_plus_compat _ _ _ _).
        * apply (RealSetoid.real_eq_mult_compat _ _ _ _); [apply real_eq_refl | apply real_cos_opp].
        * exact (real_eq_trans
                   (real_mult (cauchy_real_cos (real_plus X (real_opp Y)))
                              (cauchy_real_sin (real_opp Z)))
                   (real_mult (cauchy_real_cos (real_plus X (real_opp Y)))
                              (real_opp (cauchy_real_sin Z)))
                   (real_opp (real_mult (cauchy_real_cos (real_plus X (real_opp Y)))
                                        (real_mult (real_const ((u - v) / (1 + u * v)))
                                                   (cauchy_real_cos Z))))
                   (RealSetoid.real_eq_mult_compat
                      (cauchy_real_cos (real_plus X (real_opp Y)))
                      (cauchy_real_sin (real_opp Z))
                      (cauchy_real_cos (real_plus X (real_opp Y)))
                      (real_opp (cauchy_real_sin Z))
                      (real_eq_refl (cauchy_real_cos (real_plus X (real_opp Y))))
                      (real_sin_opp Z))
                   (real_eq_trans
                      (real_mult (cauchy_real_cos (real_plus X (real_opp Y)))
                                 (real_opp (cauchy_real_sin Z)))
                      (real_mult (cauchy_real_cos (real_plus X (real_opp Y)))
                                 (real_opp (real_mult (real_const ((u - v) / (1 + u * v)))
                                                      (cauchy_real_cos Z))))
                      (real_opp (real_mult (cauchy_real_cos (real_plus X (real_opp Y)))
                                           (real_mult (real_const ((u - v) / (1 + u * v)))
                                                      (cauchy_real_cos Z))))
                      (RealSetoid.real_eq_mult_compat
                         (cauchy_real_cos (real_plus X (real_opp Y)))
                         (real_opp (cauchy_real_sin Z))
                         (cauchy_real_cos (real_plus X (real_opp Y)))
                         (real_opp (real_mult (real_const ((u - v) / (1 + u * v)))
                                              (cauchy_real_cos Z)))
                         (real_eq_refl (cauchy_real_cos (real_plus X (real_opp Y))))
                         (RealSetoid.real_eq_opp_compat (cauchy_real_sin Z)
                            (real_mult (real_const ((u - v) / (1 + u * v))) (cauchy_real_cos Z))
                            HTw))
                      (mach_real_mult_opp_r (cauchy_real_cos (real_plus X (real_opp Y)))
                                            (real_mult (real_const ((u - v) / (1 + u * v)))
                                                       (cauchy_real_cos Z))))).
      + exact (mach_real_lin_comb2 (cauchy_real_sin (real_plus X (real_opp Y)))
                                   (cauchy_real_cos (real_plus X (real_opp Y)))
                                   cXY (cauchy_real_cos Z)
                                   (u - v) (1 + u * v) ((u - v) / (1 + u * v)) HsD HcD). }
  assert (Hz : ((u - v) - (1 + u * v) * ((u - v) / (1 + u * v)) == 0)%Q).
  { assert (Hden : (0 < 1 + u * v)%Q)
      by (pose proof (Qmult_lt_0_compat u v Hu0 Hv0) as Huv; lra).
    assert (Hne : ~ ((1 + u * v) == 0)).
    { intro Hzz. apply (Qlt_irrefl 0). rewrite Hzz in Hden. exact Hden. }
    unfold Qdiv. field. exact Hne. }
  assert (HsEz : real_eq (cauchy_real_sin (real_plus (real_plus X (real_opp Y)) (real_opp Z)))
                         real_zero).
    apply (real_eq_trans _ (real_mult (real_const 0) (real_mult cXY (cauchy_real_cos Z)))).
    apply (real_eq_trans _ (real_mult (real_const ((u - v) - (1 + u * v) * ((u - v) / (1 + u * v)))) (real_mult cXY (cauchy_real_cos Z)))).
      exact HsE.
      apply (RealSetoid.real_eq_mult_compat
        (real_const ((u - v) - (1 + u * v) * ((u - v) / (1 + u * v)))) (real_mult cXY (cauchy_real_cos Z)) (real_const 0)
        (real_mult cXY (cauchy_real_cos Z)));
        [apply mach_real_const_eq; apply qeq_imp_qeqT; exact Hz | apply real_eq_refl].
      apply mach_real_eq_pt. intro n. apply qeq_imp_qeqT.
      setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_const 0) (real_mult cXY (cauchy_real_cos Z)) n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_const_proj 0 n)).
      ring.
  (* squeeze: the difference lies in (-2, 2) and has zero sine *)
  assert (Hu1le : (u <= 1)%Q) by (apply Qlt_le_weak; exact Hu1).
  assert (Hv1le : (v <= 1)%Q) by (apply Qlt_le_weak; exact Hv1).
  assert (Hw1le : ((u - v) / (1 + u * v) <= 1)%Q) by (apply Qlt_le_weak; exact Hw1).
  pose proof (mach_q_abs_le_one u (Qlt_to_QltT 0 u Hu0) (Qle_to_QleT' u 1 Hu1le)) as Hcu.
  pose proof (mach_q_abs_le_one v (Qlt_to_QltT 0 v Hv0) (Qle_to_QleT' v 1 Hv1le)) as Hcv.
  pose proof (mach_q_abs_le_one ((u - v) / (1 + u * v)) Hw0T (Qle_to_QleT' _ _ Hw1le)) as Hcw.
  assert (Hlo : real_lt (real_const (-2#1)) (real_plus (real_plus X (real_opp Y)) (real_opp Z))).
  { unfold real_lt. exists (1#5). split.
    - apply Qlt_to_QltT. change (Qlt 0 (1#5)). unfold Qlt. simpl. lia.
    - exists 3%nat. intros n Hn.
      apply Qlt_to_QltT.
      pose proof (QltT_to_Qlt _ _ (mach_atan_pt_upper u Hu0T Hcu n (NatLe_drop 3 n Hn))) as Hpu.
      pose proof (QltT_to_Qlt _ _ (mach_atan_pt_upper v Hv0T Hcv n (NatLe_drop 3 n Hn))) as Hpv.
      pose proof (QltT_to_Qlt _ _ (mach_atan_pt_upper ((u - v) / (1 + u * v)) Hw0T Hcw n (NatLe_drop 3 n Hn))) as Hpw.
      pose proof (QltT_to_Qlt _ _ (mach_atan_pt_lower u Hu0T Hcu n)) as Hlu.
      setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_plus X (real_opp Y)) (real_opp Z) n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj X (real_opp Y) n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_opp_proj Y n)). setoid_rewrite (qeqT_imp_qeq _ _ (real_opp_proj Z n)).
      unfold X, Y, Z.
      setoid_rewrite (qeqT_imp_qeq _ _ (arctan_real_proj (real_const u) (mach_pt_bound_of_lt u Hu0T Hu1T) n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_const_proj u n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (arctan_real_proj (real_const v) (mach_pt_bound_of_lt v Hv0T Hv1T) n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_const_proj v n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (arctan_real_proj (real_const ((u - v) / (1 + u * v)))
                                (mach_pt_bound_of_lt ((u - v) / (1 + u * v)) Hw0T Hw1T) n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_const_proj ((u - v) / (1 + u * v)) n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_const_proj (-2#1) n)).
      lra. }
  assert (Hup : real_lt (real_plus (real_plus X (real_opp Y)) (real_opp Z)) (real_const 2)).
  { unfold real_lt. exists (1#2). split.
    - apply Qlt_to_QltT. change (Qlt 0 (1#2)). unfold Qlt. simpl. lia.
    - exists 3%nat. intros n Hn.
      apply Qlt_to_QltT.
      pose proof (QltT_to_Qlt _ _ (mach_atan_pt_upper u Hu0T Hcu n (NatLe_drop 3 n Hn))) as Hpu.
      pose proof (QltT_to_Qlt _ _ (mach_atan_pt_upper v Hv0T Hcv n (NatLe_drop 3 n Hn))) as Hpv.
      pose proof (QltT_to_Qlt _ _ (mach_atan_pt_upper ((u - v) / (1 + u * v)) Hw0T Hcw n (NatLe_drop 3 n Hn))) as Hpw.
      pose proof (QltT_to_Qlt _ _ (mach_atan_pt_lower v Hv0T Hcv n)) as Hlv.
      pose proof (QltT_to_Qlt _ _ (mach_atan_pt_lower ((u - v) / (1 + u * v)) Hw0T Hcw n)) as Hlw.
      setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_plus X (real_opp Y)) (real_opp Z) n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj X (real_opp Y) n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_opp_proj Y n)). setoid_rewrite (qeqT_imp_qeq _ _ (real_opp_proj Z n)).
      unfold X, Y, Z.
      setoid_rewrite (qeqT_imp_qeq _ _ (arctan_real_proj (real_const u) (mach_pt_bound_of_lt u Hu0T Hu1T) n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_const_proj u n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (arctan_real_proj (real_const v) (mach_pt_bound_of_lt v Hv0T Hv1T) n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_const_proj v n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (arctan_real_proj (real_const ((u - v) / (1 + u * v)))
                                (mach_pt_bound_of_lt ((u - v) / (1 + u * v)) Hw0T Hw1T) n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_const_proj ((u - v) / (1 + u * v)) n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_const_proj 2 n)).
      lra. }
  apply (real_eq_minus_zero _ _).
  exact (mach_sin_zero_uniq (real_plus (real_plus X (real_opp Y)) (real_opp Z))
                            Hlo Hup HsEz).
Qed.

(* ============================================================ *)
(* Part 8: the addition formula.                                 *)
(* ============================================================ *)

Lemma mach_atan_add : forall (u v : Q) (Hu0T : QltT 0 u) (Hv0T : QltT 0 v)
  (Hu1T : QltT u 1) (Hv1T : QltT v 1) (HleT : QleT' (u + v + u * v) 1),
  real_eq (real_plus (cauchy_real_arctan (real_const u) (mach_pt_bound_of_lt u Hu0T Hu1T))
                     (cauchy_real_arctan (real_const v) (mach_pt_bound_of_lt v Hv0T Hv1T)))
          (cauchy_real_arctan (real_const ((u + v) / (1 - u * v)))
                              (mach_pt_bound_of_le ((u + v) / (1 - u * v))
                                                   (mach_w_add_pos u v Hu0T Hv0T HleT)
                                                   (mach_w_add_le u v Hv0T HleT))).
Proof.
  intros u v Hu0T Hv0T Hu1T Hv1T HleT.
  pose proof (QltT_to_Qlt 0 u Hu0T) as Hu0.
  pose proof (QltT_to_Qlt 0 v Hv0T) as Hv0.
  pose proof (QltT_to_Qlt u 1 Hu1T) as Hu1.
  pose proof (QltT_to_Qlt v 1 Hv1T) as Hv1.
  pose proof (QleT'_to_Qle (u + v + u * v) 1 HleT) as Hle.
  pose proof (mach_w_add_pos u v Hu0T Hv0T HleT) as Hw0T.
  pose proof (QltT_to_Qlt _ _ Hw0T) as Hw0.
  pose proof (mach_w_add_le u v Hv0T HleT) as Hw1T.
  pose proof (QleT'_to_Qle _ _ Hw1T) as Hw1.
  pose proof (mach_sin_atan_eq_gen u Hu0T (mach_pt_bound_of_lt u Hu0T Hu1T)) as HTu.
  pose proof (mach_sin_atan_eq_gen v Hv0T (mach_pt_bound_of_lt v Hv0T Hv1T)) as HTv.
  pose proof (mach_sin_atan_eq_gen ((u + v) / (1 - u * v)) Hw0T
              (mach_pt_bound_of_le ((u + v) / (1 - u * v)) Hw0T Hw1T)) as HTw.
  set (X := cauchy_real_arctan (real_const u) (mach_pt_bound_of_lt u Hu0T Hu1T)) in *.
  set (Y := cauchy_real_arctan (real_const v) (mach_pt_bound_of_lt v Hv0T Hv1T)) in *.
  set (Z := cauchy_real_arctan (real_const ((u + v) / (1 - u * v)))
                               (mach_pt_bound_of_le ((u + v) / (1 - u * v)) Hw0T Hw1T)) in *.
  set (cXY := real_mult (cauchy_real_cos X) (cauchy_real_cos Y)) in *.
  assert (HsD : real_eq (cauchy_real_sin (real_plus X Y)) (real_mult (real_const (u + v)) cXY)).
  { apply (real_eq_trans _ (real_plus (real_mult (cauchy_real_sin X) (cauchy_real_cos Y))
                                      (real_mult (cauchy_real_cos X) (cauchy_real_sin Y)))).
    - exact (rs_add_sin X Y).
    - exact (mach_real_lin_comb3 (cauchy_real_sin X) (cauchy_real_cos X)
                                 (cauchy_real_cos Y) (cauchy_real_sin Y) u v HTu HTv). }
  assert (HcD : real_eq (cauchy_real_cos (real_plus X Y)) (real_mult (real_const (1 - u * v)) cXY)).
  { apply (real_eq_trans _ (real_plus (real_mult (cauchy_real_cos X) (cauchy_real_cos Y))
                                      (real_opp (real_mult (cauchy_real_sin X) (cauchy_real_sin Y))))).
    - exact (rs_add_cos X Y).
    - exact (mach_shape_cos_sum (cauchy_real_sin X) (cauchy_real_cos X)
                                (cauchy_real_sin Y) (cauchy_real_cos Y) u v HTu HTv). }
  assert (HsE : real_eq (cauchy_real_sin (real_plus (real_plus X Y) (real_opp Z)))
                        (real_mult (real_const ((u + v) - (1 - u * v) * ((u + v) / (1 - u * v))))
                                   (real_mult cXY (cauchy_real_cos Z)))).
  { apply (real_eq_trans _ (real_plus
              (real_mult (cauchy_real_sin (real_plus X Y)) (cauchy_real_cos (real_opp Z)))
              (real_mult (cauchy_real_cos (real_plus X Y)) (cauchy_real_sin (real_opp Z))))).
    - exact (rs_add_sin (real_plus X Y) (real_opp Z)).
    - apply (real_eq_trans _ (real_plus
                (real_mult (cauchy_real_sin (real_plus X Y)) (cauchy_real_cos Z))
                (real_opp (real_mult (cauchy_real_cos (real_plus X Y))
                                     (real_mult (real_const ((u + v) / (1 - u * v)))
                                                (cauchy_real_cos Z)))))).
      + apply (RealSetoid.real_eq_plus_compat _ _ _ _).
        * apply (RealSetoid.real_eq_mult_compat _ _ _ _); [apply real_eq_refl | apply real_cos_opp].
        * exact (real_eq_trans
                   (real_mult (cauchy_real_cos (real_plus X Y))
                              (cauchy_real_sin (real_opp Z)))
                   (real_mult (cauchy_real_cos (real_plus X Y))
                              (real_opp (cauchy_real_sin Z)))
                   (real_opp (real_mult (cauchy_real_cos (real_plus X Y))
                                        (real_mult (real_const ((u + v) / (1 - u * v)))
                                                   (cauchy_real_cos Z))))
                   (RealSetoid.real_eq_mult_compat
                      (cauchy_real_cos (real_plus X Y))
                      (cauchy_real_sin (real_opp Z))
                      (cauchy_real_cos (real_plus X Y))
                      (real_opp (cauchy_real_sin Z))
                      (real_eq_refl (cauchy_real_cos (real_plus X Y)))
                      (real_sin_opp Z))
                   (real_eq_trans
                      (real_mult (cauchy_real_cos (real_plus X Y))
                                 (real_opp (cauchy_real_sin Z)))
                      (real_mult (cauchy_real_cos (real_plus X Y))
                                 (real_opp (real_mult (real_const ((u + v) / (1 - u * v)))
                                                      (cauchy_real_cos Z))))
                      (real_opp (real_mult (cauchy_real_cos (real_plus X Y))
                                           (real_mult (real_const ((u + v) / (1 - u * v)))
                                                      (cauchy_real_cos Z))))
                      (RealSetoid.real_eq_mult_compat
                         (cauchy_real_cos (real_plus X Y))
                         (real_opp (cauchy_real_sin Z))
                         (cauchy_real_cos (real_plus X Y))
                         (real_opp (real_mult (real_const ((u + v) / (1 - u * v)))
                                              (cauchy_real_cos Z)))
                         (real_eq_refl (cauchy_real_cos (real_plus X Y)))
                         (RealSetoid.real_eq_opp_compat (cauchy_real_sin Z)
                            (real_mult (real_const ((u + v) / (1 - u * v))) (cauchy_real_cos Z))
                            HTw))
                      (mach_real_mult_opp_r (cauchy_real_cos (real_plus X Y))
                                            (real_mult (real_const ((u + v) / (1 - u * v)))
                                                       (cauchy_real_cos Z))))).
      + exact (mach_real_lin_comb2 (cauchy_real_sin (real_plus X Y))
                                   (cauchy_real_cos (real_plus X Y))
                                   cXY (cauchy_real_cos Z)
                                   (u + v) (1 - u * v) ((u + v) / (1 - u * v)) HsD HcD). }
  assert (Hz : ((u + v) - (1 - u * v) * ((u + v) / (1 - u * v)) == 0)%Q).
  { assert (Hden : (0 < 1 - u * v)%Q) by lra.
    assert (Hne : ~ ((1 - u * v) == 0)).
    { intro Hzz. apply (Qlt_irrefl 0). rewrite Hzz in Hden. exact Hden. }
    unfold Qdiv. field. exact Hne. }
  assert (HsEz : real_eq (cauchy_real_sin (real_plus (real_plus X Y) (real_opp Z))) real_zero).
    apply (real_eq_trans _ (real_mult (real_const 0) (real_mult cXY (cauchy_real_cos Z)))).
    apply (real_eq_trans _ (real_mult (real_const ((u + v) - (1 - u * v) * ((u + v) / (1 - u * v)))) (real_mult cXY (cauchy_real_cos Z)))).
      exact HsE.
      apply (RealSetoid.real_eq_mult_compat
        (real_const ((u + v) - (1 - u * v) * ((u + v) / (1 - u * v)))) (real_mult cXY (cauchy_real_cos Z)) (real_const 0)
        (real_mult cXY (cauchy_real_cos Z)));
        [apply mach_real_const_eq; apply qeq_imp_qeqT; exact Hz | apply real_eq_refl].
      apply mach_real_eq_pt. intro n. apply qeq_imp_qeqT.
      setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_const 0) (real_mult cXY (cauchy_real_cos Z)) n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_const_proj 0 n)).
      ring.
  assert (Hu1le : (u <= 1)%Q) by (apply Qlt_le_weak; exact Hu1).
  assert (Hv1le : (v <= 1)%Q) by (apply Qlt_le_weak; exact Hv1).
  pose proof (mach_q_abs_le_one u (Qlt_to_QltT 0 u Hu0) (Qle_to_QleT' u 1 Hu1le)) as Hcu.
  pose proof (mach_q_abs_le_one v (Qlt_to_QltT 0 v Hv0) (Qle_to_QleT' v 1 Hv1le)) as Hcv.
  pose proof (mach_q_abs_le_one ((u + v) / (1 - u * v)) Hw0T (Qle_to_QleT' _ _ Hw1)) as Hcw.
  assert (Hlo : real_lt (real_const (-2#1)) (real_plus (real_plus X Y) (real_opp Z))).
  { unfold real_lt. exists (1#2). split.
    - apply Qlt_to_QltT. change (Qlt 0 (1#2)). unfold Qlt. simpl. lia.
    - exists 3%nat. intros n Hn.
      apply Qlt_to_QltT.
      pose proof (QltT_to_Qlt _ _ (mach_atan_pt_upper u Hu0T Hcu n (NatLe_drop 3 n Hn))) as Hpu.
      pose proof (QltT_to_Qlt _ _ (mach_atan_pt_upper v Hv0T Hcv n (NatLe_drop 3 n Hn))) as Hpv.
      pose proof (QltT_to_Qlt _ _ (mach_atan_pt_upper ((u + v) / (1 - u * v)) Hw0T Hcw n (NatLe_drop 3 n Hn))) as Hpw.
      pose proof (QltT_to_Qlt _ _ (mach_atan_pt_lower u Hu0T Hcu n)) as Hlu.
      pose proof (QltT_to_Qlt _ _ (mach_atan_pt_lower v Hv0T Hcv n)) as Hlv.
      setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_plus X Y) (real_opp Z) n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj X Y n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_opp_proj Z n)).
      unfold X, Y, Z.
      setoid_rewrite (qeqT_imp_qeq _ _ (arctan_real_proj (real_const u) (mach_pt_bound_of_lt u Hu0T Hu1T) n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_const_proj u n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (arctan_real_proj (real_const v) (mach_pt_bound_of_lt v Hv0T Hv1T) n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_const_proj v n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (arctan_real_proj (real_const ((u + v) / (1 - u * v)))
                                (mach_pt_bound_of_le ((u + v) / (1 - u * v)) Hw0T Hw1T) n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_const_proj ((u + v) / (1 - u * v)) n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_const_proj (-2#1) n)).
      lra. }
  assert (Hup : real_lt (real_plus (real_plus X Y) (real_opp Z)) (real_const 2)).
  { unfold real_lt. exists (1#5). split.
    - apply Qlt_to_QltT. change (Qlt 0 (1#5)). unfold Qlt. simpl. lia.
    - exists 3%nat. intros n Hn.
      apply Qlt_to_QltT.
      pose proof (QltT_to_Qlt _ _ (mach_atan_pt_upper u Hu0T Hcu n (NatLe_drop 3 n Hn))) as Hpu.
      pose proof (QltT_to_Qlt _ _ (mach_atan_pt_upper v Hv0T Hcv n (NatLe_drop 3 n Hn))) as Hpv.
      pose proof (QltT_to_Qlt _ _ (mach_atan_pt_upper ((u + v) / (1 - u * v)) Hw0T Hcw n (NatLe_drop 3 n Hn))) as Hpw.
      pose proof (QltT_to_Qlt _ _ (mach_atan_pt_lower ((u + v) / (1 - u * v)) Hw0T Hcw n)) as Hlw.
      setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_plus X Y) (real_opp Z) n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj X Y n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_opp_proj Z n)).
      unfold X, Y, Z.
      setoid_rewrite (qeqT_imp_qeq _ _ (arctan_real_proj (real_const u) (mach_pt_bound_of_lt u Hu0T Hu1T) n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_const_proj u n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (arctan_real_proj (real_const v) (mach_pt_bound_of_lt v Hv0T Hv1T) n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_const_proj v n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (arctan_real_proj (real_const ((u + v) / (1 - u * v)))
                                (mach_pt_bound_of_le ((u + v) / (1 - u * v)) Hw0T Hw1T) n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_const_proj ((u + v) / (1 - u * v)) n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_const_proj 2 n)).
      lra. }
  apply (real_eq_minus_zero _ _).
  exact (mach_sin_zero_uniq (real_plus (real_plus X Y) (real_opp Z)) Hlo Hup HsEz).
Qed.

(* ============================================================ *)
(* Part 9: certification probes.                                 *)
(* ============================================================ *)

Print Assumptions mach_atan_sub.
Print Assumptions mach_atan_add.
Recursive Extraction mach_atan_sub.
Recursive Extraction mach_atan_add.
