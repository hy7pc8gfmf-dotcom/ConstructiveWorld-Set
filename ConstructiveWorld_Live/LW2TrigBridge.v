(* ============================================================
   LW2TrigBridge.v -- the two constructive representations of pi
   (the geometric zero representation real_pi_geom, and the Leibniz
   series sum cauchy_real_pi_leibniz) made interoperable at the
   trigonometric endpoint-value face.
   Mission. cos(pi) == -1 and sin(pi) == 0 are transported from the
   real_pi_geom representation to the Leibniz representation through
   channel_f1; the double-angle pointwise statements sin(2 th) ==
   2*sin(th)*cos(th) and cos(2 th) == cos(th)^2 - sin(th)^2 are
   supplied; the direct edge cos_pi_half == 2*arctan_one_real is
   recast as 2*arctan_one_real == pi_L/2, connecting cos_pi_half,
   arctan_one_real, and pi_L in one zero-premise statement.
   Dependencies. S01_BaseRing, S02_CauchyComplete (the real_eq
   faces), S03_QExp through S09_EntropyReal, S10_KVQuantTrig
   (cauchy_real_sin/cos, rs_add_sin/cos, real_sin_eq_compat,
   real_cos_eq_compat, real_pi_geom, cos_pi_half), S11_TP3B5
   (cauchy_real_pi_leibniz, channel_f1, arctan_one_real),
   S12_B5RecycleSF, S14_B5BatchBlock (pi_triangle_direct_edge),
   LW0PiTrigValues, LW0_SinPos, UpReqPadeTailPos.
   References. mathlib Real.sin_two_mul and Real.cos_two_mul (the
   double-angle pointwise forms), Real.arctan_one_eq_pi_div_four,
   Real.cos_pi_half.
   Constructivity. Every statement is Set-layer (real_eq :
   Real -> Real -> Set; And the Set-layer product); zero Prop
   propositions, zero axioms, zero admissions, zero classical logic;
   proofs assemble from in-library statements and Q-layer pointwise
   identities; Separate Extraction supported.
   Build. coqc -q -Q <tree root> "" LW2TrigBridge.v
   (compile LW0PiTrigValues.v and LW0_SinPos.v first).
   ============================================================ *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               Lists.List Bool.Bool Arith.Arith.
Import ListNotations.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax.
Opaque Qred.

(* ---- The Q-layer pointwise identity pair (independent statement face, ring-closed) ---- *)
Lemma lw2_q_point_double : forall w : Q, (w + w - 2 * w == 0)%Q.
Proof. intro w. ring. Qed.

Lemma lw2_q_point_double_half : forall w : Q,
  (w - (1 # 2) * (2 * w) == 0)%Q.
Proof. intro w. ring. Qed.

(* ---- Generic doubling: z + z == 2*z (the Q-layer pointwise identity) ---- *)
Lemma lw2_real_double : forall z : Real,
  real_eq (real_plus z z) (real_mult (real_const 2) z).
Proof.
  intro z. destruct z as [w Hw].
  apply real_eq_of_zero_diff.
  intro n.
  apply qeq_imp_qeqT. simpl.
  apply lw2_q_point_double.
Qed.

(* ---- Pointwise halving identity: z == (1/2)*(2*z) (the Q-layer pointwise identity) ----
   it reads 2*z-form statements back into z-form (paired with
   lw2_half_mult_eq_compat). *)
Lemma lw2_real_double_half : forall z : Real,
  real_eq z (real_mult (real_const (1 / 2)) (real_mult (real_const 2) z)).
Proof.
  intro z. destruct z as [w Hw].
  apply real_eq_of_zero_diff.
  intro n.
  apply qeq_imp_qeqT. simpl.
  apply lw2_q_point_double_half.
Qed.

(* ---- Congruence of the halving scalar product over real_eq ----
   eps-slack: |x_n - y_n| < 2*eps gives |x_n/2 - y_n/2| < eps. *)
Lemma lw2_half_mult_eq_compat : forall x y : Real,
  real_eq x y ->
  real_eq (real_mult (real_const (1 / 2)) x)
          (real_mult (real_const (1 / 2)) y).
Proof.
  intros x y Hxy eps Heps.
  assert (Hlt : (0 < eps)%Q) by (apply QltT_to_Qlt; exact Heps).
  assert (Hc : (0 < 2)%Q) by (unfold Qlt; reflexivity).
  assert (Hm : (0 * 2 < eps * 2)%Q)
    by (apply (proj2 (Qmult_lt_r 0 eps 2 Hc)); exact Hlt).
  assert (Hmz : ((0 * 2) == 0)%Q) by ring.
  setoid_rewrite Hmz in Hm.
  assert (HmT : QltT 0 (eps * 2)%Q) by (apply Qlt_to_QltT; exact Hm).
  destruct x as [u Hu]. destruct y as [v Hv].
  unfold real_eq in Hxy.
  destruct (Hxy (eps * 2)%Q HmT) as [N HN].
  exists N. intros n Hn.
  specialize (HN n Hn).
  change (QltT (Qabs ((1 # 2) * u n - (1 # 2) * v n)) eps).
  apply Qlt_to_QltT.
  assert (Hrw : (((1 # 2) * u n - (1 # 2) * v n)
               == ((u n - v n) * (1 # 2)))%Q) by ring.
  setoid_rewrite Hrw.
  rewrite Qabs_Qmult.
  assert (Hh : (Qabs (1 # 2) == (1 # 2))%Q) by (vm_compute; reflexivity).
  rewrite Hh.
  apply (Qle_lt_trans _ (Qabs (u n - v n) * (1 # 2))%Q _).
  - apply Qle_refl.
  - assert (Hq : (Qabs (u n - v n) * (1 # 2) < (eps * 2) * (1 # 2))%Q).
    { apply (proj2 (Qmult_lt_r (Qabs (u n - v n)) (eps * 2) (1 # 2) Hc)).
      apply QltT_to_Qlt. exact HN. }
    assert (Hre : (((eps * 2) * (1 # 2)) == eps)%Q) by ring.
    setoid_rewrite Hre in Hq.
    exact Hq.
Qed.

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
Require Import S14_B5BatchBlock.
Require Import LW0PiTrigValues.
Require Import LW0_SinPos.
Import PropositionConvergenceCore.

(* ---- The zero-premise closed instance of channel_f1 ----
   the two premises of the section-exported form are supplied by the
   in-library equalities 4*theta1 == pi_L and
   sin theta1 == cos theta1. *)
Lemma lw2_channel_f1_closed :
  real_eq real_pi_geom cauchy_real_pi_leibniz.
Proof.
  exact (channel_f1 a3_h4_value_bridge
           (b5b_hsc_theorem b5dS_E_zero_on_unit)).
Qed.

(* ---- Endpoint value one: sin(pi_L) == 0 ----
   pi_geom_sin_pi_zero transported through the sin congruence over
   real_eq and channel_f1 (real_pi_geom == pi_L). *)
Lemma lw2_pi_L_sin_zero :
  real_eq (cauchy_real_sin cauchy_real_pi_leibniz) real_zero.
Proof.
  apply (real_eq_trans
          (cauchy_real_sin cauchy_real_pi_leibniz)
          (cauchy_real_sin real_pi_geom)
          real_zero).
  - exact (real_eq_sym _ _
             (real_sin_eq_compat real_pi_geom cauchy_real_pi_leibniz
                lw2_channel_f1_closed)).
  - exact pi_geom_sin_pi_zero.
Qed.

(* ---- Endpoint value two: cos(pi_L) == -1 ----
   pi_geom_cos_pi_neg_one transported through the cos congruence over
   real_eq and channel_f1. *)
Lemma lw2_pi_L_cos_neg_one :
  real_eq (cauchy_real_cos cauchy_real_pi_leibniz) (real_const (-1)%Q).
Proof.
  apply (real_eq_trans
          (cauchy_real_cos cauchy_real_pi_leibniz)
          (cauchy_real_cos real_pi_geom)
          (real_const (-1)%Q)).
  - exact (real_eq_sym _ _
             (real_cos_eq_compat real_pi_geom cauchy_real_pi_leibniz
                lw2_channel_f1_closed)).
  - exact pi_geom_cos_pi_neg_one.
Qed.

(* ---- The pi_L reading of the direct edge: 2*arctan_one_real == pi_L/2 ----
   chain: 2*arctan_one_real == cos_pi_half (symmetry of
   pi_triangle_direct_edge) == (2*cos_pi_half)*(1/2) (the pointwise
   identity) == pi_L*(1/2) (the halving congruence paired with
   channel_f1, where 2*cos_pi_half is the body of real_pi_geom). *)
Lemma lw2_theta_double_eq_pi_L :
  real_eq (real_mult (real_const 2) arctan_one_real)
          (real_mult (real_const (1 / 2)) cauchy_real_pi_leibniz).
Proof.
  apply (real_eq_trans
          (real_mult (real_const 2) arctan_one_real)
          cos_pi_half
          (real_mult (real_const (1 / 2)) cauchy_real_pi_leibniz)).
  - exact (real_eq_sym cos_pi_half
             (real_mult (real_const 2) arctan_one_real)
             pi_triangle_direct_edge).
  - exact (real_eq_trans
             cos_pi_half
             (real_mult (real_const (1 / 2))
                (real_mult (real_const 2) cos_pi_half))
             (real_mult (real_const (1 / 2)) cauchy_real_pi_leibniz)
             (lw2_real_double_half cos_pi_half)
             (lw2_half_mult_eq_compat
                (real_mult (real_const 2) cos_pi_half)
                cauchy_real_pi_leibniz
                lw2_channel_f1_closed)).
Qed.

(* ---- Double angle (sin side): sin(2*theta) == 2*sin(theta)*cos(theta) ----
   rs_add_sin at X = Y gives sin(theta+theta) ==
   sin(theta)*cos(theta) + cos(theta)*sin(theta); the second term is
   reordered via real_mult_comm and gathered by the generic doubling
   identity. *)
Lemma lw2_sin_double_eq_two_sin_cos : forall X : Real,
  real_eq (cauchy_real_sin (real_plus X X))
          (real_mult (real_const 2)
                     (real_mult (cauchy_real_sin X) (cauchy_real_cos X))).
Proof.
  intro X.
  apply (real_eq_trans
          (cauchy_real_sin (real_plus X X))
          (real_plus (real_mult (cauchy_real_sin X) (cauchy_real_cos X))
                     (real_mult (cauchy_real_cos X) (cauchy_real_sin X)))
          (real_mult (real_const 2)
                     (real_mult (cauchy_real_sin X) (cauchy_real_cos X)))).
  - exact (rs_add_sin X X).
  - apply (real_eq_trans
            (real_plus (real_mult (cauchy_real_sin X) (cauchy_real_cos X))
                       (real_mult (cauchy_real_cos X) (cauchy_real_sin X)))
            (real_plus (real_mult (cauchy_real_sin X) (cauchy_real_cos X))
                       (real_mult (cauchy_real_sin X) (cauchy_real_cos X)))
            (real_mult (real_const 2)
                       (real_mult (cauchy_real_sin X)
                                  (cauchy_real_cos X)))).
    + apply (lw0_sin_plus_eq_compat
               (real_mult (cauchy_real_sin X) (cauchy_real_cos X))
               (real_mult (cauchy_real_sin X) (cauchy_real_cos X))
               (real_mult (cauchy_real_cos X) (cauchy_real_sin X))
               (real_mult (cauchy_real_sin X) (cauchy_real_cos X))).
      * apply real_eq_refl.
      * apply real_mult_comm.
    + exact (lw2_real_double
               (real_mult (cauchy_real_sin X) (cauchy_real_cos X))).
Qed.

(* ---- Double angle (cos side): cos(2*theta) == cos(theta)^2 - sin(theta)^2 ----
   the direct instance of rs_add_cos at X = Y. *)
Lemma lw2_cos_double_eq_cos_sq_minus_sin_sq : forall X : Real,
  real_eq (cauchy_real_cos (real_plus X X))
          (real_plus (real_mult (cauchy_real_cos X) (cauchy_real_cos X))
                     (real_opp (real_mult (cauchy_real_sin X)
                                          (cauchy_real_sin X)))).
Proof.
  intro X.
  exact (rs_add_cos X X).
Qed.

(* ---- The pi_L endpoint-value certificate: the Set-layer product packaging of sin(pi_L) == 0 and cos(pi_L) == -1 ---- *)
Lemma lw2_pi_L_trig_values :
  And (real_eq (cauchy_real_sin cauchy_real_pi_leibniz) real_zero)
      (real_eq (cauchy_real_cos cauchy_real_pi_leibniz)
               (real_const (-1)%Q)).
Proof.
  exact (lw2_pi_L_sin_zero, lw2_pi_L_cos_neg_one).
Qed.
