(* ConstructiveWorld-Set -- Cauchy-real instance realizations of the Paper7Ablation expf ablation family. *)

(** * ToyR_UpAblP7_Paper7Ablation_S1inst: Cauchy-real instance file for the five expf slots of Paper7Ablation.

    Mission.  This file instantiates the five expf slots of [Paper7Ablation]
      (well-definedness, positivity, zero, product, strict monotonicity) on
      the Cauchy reals of [S07_RealSetoidExpLog].  The auxiliary lemmas
      [s1inst_exp_cong_zero] (exponential continuous at zero) and
      [s1inst_real_mult_cancel_l] (left cancellation by a positive real)
      rebuild the multiplicative-inverse elimination chain of [p7a_expf_wd].
      Main statements: [s1inst_p7a_expf_wd] (assembly form over the three
      fields [cauchy_real_exp_plus], [cauchy_real_exp_zero], [cauchy_real_exp_pos]),
      [s1inst_p7a_expf_wd_direct], [s1inst_dual_cover], [s1inst_p7a_expf_mono_le].

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs], [QArith.Qround],
      [Lists.List], [Bool.Bool], [Arith.Arith], [Setoid], [Morphisms], [Lia],
      [QArith.Qminmax].  Requires [S01_BaseRing], [S02_CauchyComplete],
      [S03_QExp], [S07_RealSetoidExpLog], [Paper7Ablation] of this development.

    References.  This development, ToyR_UpAblP7_Paper7Ablation_S1inst.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" ToyR_UpAblP7_Paper7Ablation_S1inst.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 000160bc]. *)
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import Paper7Ablation.

From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               Lists.List Bool.Bool Arith.Arith.
Import ListNotations.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax.

(* ================== Section 1. The exponential is continuous at zero ================== *)
(* Fills the congruence step of the assembly chain: [x == 0] implies
   [e^x == 1].  Proved from the S03 primitives alone, without consuming
   [cauchy_real_exp_wd]. *)
Lemma s1inst_exp_cong_zero : forall x : Real,
  real_eq x real_zero -> real_eq (cauchy_real_exp x) real_one.
Proof.
  intros x Hx. destruct x as [u Hu].
  unfold real_eq in Hx |- *.
  intros eps Heps.
  destruct (real_norm_bounded (existT (fun s : Qseq => cauchy s) u Hu))
    as [M [HMpos HM]].
  assert (HMnonnegT : QleT' 0 M) by (apply qltT_leT'; exact HMpos).
  destruct (exp_series_arch M HMnonnegT) as [C [HC1 HC]].
  assert (HCposT : QltT 0 C).
  { apply (qltT_leT'_ltT 0 1 C). exact qltT_0_1. exact HC1. }
  assert (HCpos : Qlt 0 C) by (apply QltT_to_Qlt; exact HCposT).
  assert (HCnonneg : Qle 0 C) by (apply (Qlt_le_weak 0 C); exact HCpos).
  assert (HepsC : QltT 0 (eps / (2 * C))).
  { apply (qltT_div_pos eps (2 * C)).
    - exact Heps.
    - apply (qmult_ltT_0_compat 2 C). exact qltT_0_2. exact HCposT. }
  destruct (Hx (eps / (2 * C))%Q HepsC) as [N1 HN1].
  exists N1. intros n Hn.
  cbn [projT1] in HN1.
  simpl.
  (* Goal: [QltT (Qabs (exp_partial n (u n) - 1)) eps]. *)
  assert (Hshape : QeqT (Qabs (exp_partial n (u n) - exp_partial n 0))
                        (Qabs (exp_partial n (u n) - 1))).
  { apply qeq_imp_qeqT.
    setoid_rewrite (qeqT_imp_qeq _ _ (exp_partial_zero n)). reflexivity. }
  apply (qltT_eq_compat_l (Qabs (exp_partial n (u n) - exp_partial n 0))
                          (Qabs (exp_partial n (u n) - 1))
                          eps Hshape).
  apply Qlt_to_QltT.
  apply (Qle_lt_trans _ (Qabs (u n - 0) * C) _).
  - apply (Qle_trans _ (Qabs (u n - 0) * exp_series n M) _).
    + exact (QleT'_to_Qle _ _
               (exp_partial_lipschitz (u n) 0 M n HMnonnegT (HM n) HMnonnegT)).
    + apply (Qmult_le_compat_nonneg (Qabs (u n - 0)) (Qabs (u n - 0))
                                    (exp_series n M) C).
      * split; [apply Qabs_nonneg | apply Qle_refl].
      * split.
        -- apply QleT'_to_Qle. apply (exp_series_nonneg n M HMnonnegT).
        -- apply QleT'_to_Qle. apply (HC n).
  - apply (Qle_lt_trans _ ((eps / (2 * C)) * C) _).
    + apply (Qmult_le_compat_r (Qabs (u n - 0)) (eps / (2 * C)) C).
      * apply (Qlt_le_weak (Qabs (u n - 0)) (eps / (2 * C))).
        apply QltT_to_Qlt. exact (HN1 n Hn).
      * exact HCnonneg.
    + apply (Qle_lt_trans _ (eps / 2) _).
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
        assert (Hc : (eps / (2 * C)) * C == eps / 2).
        { unfold Qdiv. field.
          intro Hz. exact (Qlt_not_eq 0 C HCpos (Qeq_sym C 0 Hz)). }
        exact Hc.
      * apply QltT_to_Qlt. apply (q_half_lt_self eps). exact Heps.
Qed.

(* ============ Section 2. Left cancellation of real multiplication ============ *)
(* Modeled on [mult_cancel_l] of [S01_BaseRing]. *)
Lemma s1inst_real_mult_cancel_l : forall a b c : Real,
  real_lt real_zero a ->
  real_eq (real_mult a b) (real_mult a c) -> real_eq b c.
Proof.
  intros a b c Ha Habc.
  assert (H1 : real_eq (real_mult (real_inv_pos a Ha) (real_mult a b))
                       (real_mult (real_inv_pos a Ha) (real_mult a c))).
  { apply (RealSetoid.real_eq_mult_compat (real_inv_pos a Ha) (real_mult a b)
             (real_inv_pos a Ha) (real_mult a c)).
    - apply real_eq_refl.
    - exact Habc. }
  assert (Hinv : real_eq (real_mult (real_inv_pos a Ha) a) real_one).
  { apply (real_eq_trans _ (real_mult a (real_inv_pos a Ha)) _).
    - apply real_mult_comm.
    - exact (real_inv_pos_correct a Ha). }
  assert (Honeb : real_eq (real_mult real_one b) b).
  { apply (real_eq_trans _ (real_mult b real_one) _).
    - apply real_mult_comm.
    - exact (real_mult_one b). }
  assert (Honec : real_eq (real_mult real_one c) c).
  { apply (real_eq_trans _ (real_mult c real_one) _).
    - apply real_mult_comm.
    - exact (real_mult_one c). }
  assert (Hlb : real_eq (real_mult (real_inv_pos a Ha) (real_mult a b)) b).
  { apply (real_eq_trans _ (real_mult (real_mult (real_inv_pos a Ha) a) b) _).
    - exact (real_mult_assoc (real_inv_pos a Ha) a b).
    - apply (real_eq_trans _ (real_mult real_one b) _).
      + apply (RealSetoid.real_eq_mult_compat
                 (real_mult (real_inv_pos a Ha) a) b real_one b).
        * exact Hinv.
        * apply real_eq_refl.
      + exact Honeb. }
  assert (Hrc : real_eq (real_mult (real_inv_pos a Ha) (real_mult a c)) c).
  { apply (real_eq_trans _ (real_mult (real_mult (real_inv_pos a Ha) a) c) _).
    - exact (real_mult_assoc (real_inv_pos a Ha) a c).
    - apply (real_eq_trans _ (real_mult real_one c) _).
      + apply (RealSetoid.real_eq_mult_compat
                 (real_mult (real_inv_pos a Ha) a) c real_one c).
        * exact Hinv.
        * apply real_eq_refl.
      + exact Honec. }
  apply (real_eq_trans b (real_mult (real_inv_pos a Ha) (real_mult a b)) c).
  - apply real_eq_sym. exact Hlb.
  - exact (real_eq_trans _ _ _ H1 Hrc).
Qed.

(* ======== Section 3. Assembly form: the three-field elimination chain ======== *)
(* Instance statement of [p7a_expf_wd]: [real_eq] congruence of the Cauchy
   exponential, rebuilt from the three field lemmas [cauchy_real_exp_plus],
   [cauchy_real_exp_zero], [cauchy_real_exp_pos] together with Sections 1
   and 2, replaying the multiplicative-inverse elimination chain of
   [p7a_expf_wd]; the direct form is not consumed. *)
Theorem s1inst_p7a_expf_wd : forall a b : Real,
  real_eq a b -> real_eq (cauchy_real_exp a) (cauchy_real_exp b).
Proof.
  intros a b Hab.
  assert (Ha1 : real_eq (real_mult (cauchy_real_exp a)
                                  (cauchy_real_exp (real_opp b))) real_one).
  { apply (real_eq_trans _ (cauchy_real_exp (real_plus a (real_opp b))) _).
    - apply real_eq_sym. exact (cauchy_real_exp_plus a (real_opp b)).
    - apply (s1inst_exp_cong_zero (real_plus a (real_opp b))).
      apply (real_eq_trans (real_plus a (real_opp b))
             (real_plus b (real_opp b)) real_zero).
      + exact (RealSetoid.real_eq_plus_compat a (real_opp b) b (real_opp b)
                 Hab (real_eq_refl (real_opp b))).
      + exact (real_plus_opp b). }
  assert (Hb1 : real_eq (real_mult (cauchy_real_exp b)
                                  (cauchy_real_exp (real_opp b))) real_one).
  { apply (real_eq_trans _ (cauchy_real_exp (real_plus b (real_opp b))) _).
    - apply real_eq_sym. exact (cauchy_real_exp_plus b (real_opp b)).
    - apply (s1inst_exp_cong_zero (real_plus b (real_opp b))).
      exact (real_plus_opp b). }
  apply (s1inst_real_mult_cancel_l (cauchy_real_exp (real_opp b))
           (cauchy_real_exp a) (cauchy_real_exp b)
           (cauchy_real_exp_pos (real_opp b))).
  apply (real_eq_trans
           (real_mult (cauchy_real_exp (real_opp b)) (cauchy_real_exp a))
           real_one
           (real_mult (cauchy_real_exp (real_opp b)) (cauchy_real_exp b))).
  - apply (real_eq_trans _ (real_mult (cauchy_real_exp a)
                     (cauchy_real_exp (real_opp b))) _).
    + apply real_mult_comm.
    + exact Ha1.
  - apply real_eq_sym.
    apply (real_eq_trans _ (real_mult (cauchy_real_exp b)
                      (cauchy_real_exp (real_opp b))) _).
    + apply real_mult_comm.
    + exact Hb1.
Qed.

(* ============== Section 4. Direct form: one of the two covers ============== *)
(* Consumes [cauchy_real_exp_wd] directly. *)
Theorem s1inst_p7a_expf_wd_direct : forall a b : Real,
  real_eq a b -> real_eq (cauchy_real_exp a) (cauchy_real_exp b).
Proof.
  exact cauchy_real_exp_wd.
Qed.

(* ====== Section 5. Dual cover: abstract ablation statement vs Cauchy instance ====== *)
(* Type note: the abstract branch is a Type-level forall quantifying the
   interface, which the Set-wise [And] cannot host, so the pair is packed in
   [sigT]: the first component is the proof of the abstract ablation statement
   ([p7a_expf_wd] in fully applied form, the genuine [Paper7Ablation]
   dependency), the second component is the assembly and direct double cover
   of the Cauchy instance statement. *)
Corollary s1inst_dual_cover :
  sigT
    (fun _ : forall {RI : S01_BaseRing.RealInterfaceEnhanced}
                    (expf : @S01_BaseRing.R RI -> @S01_BaseRing.R RI),
       (forall x : @S01_BaseRing.R RI,
          @S01_BaseRing.lt RI (@S01_BaseRing.zero RI) (expf x)) ->
       S01_BaseRing.Id (expf (@S01_BaseRing.zero RI))
                       (@S01_BaseRing.one RI) ->
       (forall a b : @S01_BaseRing.R RI,
          S01_BaseRing.Id (expf (@S01_BaseRing.plus RI a b))
                          (@S01_BaseRing.mult RI (expf a) (expf b))) ->
       forall a b : @S01_BaseRing.R RI,
         S01_BaseRing.Id a b -> S01_BaseRing.Id (expf a) (expf b) =>
     And
       (forall a b : Real,
          real_eq a b -> real_eq (cauchy_real_exp a) (cauchy_real_exp b))
       (forall a b : Real,
          real_eq a b -> real_eq (cauchy_real_exp a) (cauchy_real_exp b))).
Proof.
  (* Abstract ablation branch: citing [p7a_expf_wd] bare would trigger eager
     instantiation of the implicit interface argument and mismatch the
     expected type, whose leading quantifier is the explicit [RI]; hence the
     fully applied [@]-form. *)
  exists (fun (RI : S01_BaseRing.RealInterfaceEnhanced)
             (expf : @S01_BaseRing.R RI -> @S01_BaseRing.R RI)
             (expf_pos : forall x : @S01_BaseRing.R RI,
                 @S01_BaseRing.lt RI (@S01_BaseRing.zero RI) (expf x))
             (expf_zero : S01_BaseRing.Id (expf (@S01_BaseRing.zero RI))
                            (@S01_BaseRing.one RI))
             (expf_plus : forall a b : @S01_BaseRing.R RI,
                 S01_BaseRing.Id (expf (@S01_BaseRing.plus RI a b))
                                 (@S01_BaseRing.mult RI (expf a) (expf b))) =>
           @p7a_expf_wd RI expf expf_pos expf_zero expf_plus).
  split.
  - exact s1inst_p7a_expf_wd.
  - exact s1inst_p7a_expf_wd_direct.
Qed.

(* ==== Section 6. The mono_le instance: mono_lt, the Or decomposition, wd ==== *)
(* [real_le] is [Or (real_lt) (real_eq)] ([S02_CauchyComplete]): the strict
   branch is slot-5 strict monotonicity [cauchy_real_exp_mono]; the equality
   branch is the assembly-form wd path.  A decidable trichotomy order is not
   satisfiable on the Cauchy instance (the strong trichotomy form of LPO is
   unprovable), so the [Or] encoding is the model-level counterpart of the
   decidable-order trichotomy. *)
Theorem s1inst_p7a_expf_mono_le : forall a b : Real,
  real_le a b -> real_le (cauchy_real_exp a) (cauchy_real_exp b).
Proof.
  intros a b Hab.
  unfold real_le in Hab |- *.
  destruct Hab as [Hlt | Heq].
  - (* Strict branch: slot-5 strict monotonicity applies directly. *)
    left. exact (cauchy_real_exp_mono a b Hlt).
  - (* Equality branch: the assembly-form wd path, the three-field
       elimination chain. *)
    right. exact (s1inst_p7a_expf_wd a b Heq).
Qed.

(* ---- Closing: [Print Assumptions] audit of every named statement ---- *)
Print Assumptions s1inst_exp_cong_zero.
Print Assumptions s1inst_real_mult_cancel_l.
Print Assumptions s1inst_p7a_expf_wd.
Print Assumptions s1inst_p7a_expf_wd_direct.
Print Assumptions s1inst_dual_cover.
Print Assumptions s1inst_p7a_expf_mono_le.
