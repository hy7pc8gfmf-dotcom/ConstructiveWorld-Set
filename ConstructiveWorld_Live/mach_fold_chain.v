(* ConstructiveWorld-Set -- the Machin fold chain: pi/4 vertex certificate
   and the Leibniz pi bridge.
    Mission.  Formally certify the Machin pi/4 vertex chain on the Set
      statement faces: the fold-chain theorem mach_fold_chain and the one-edge
      lemma mach_edge_one, feeding the Leibniz pi bridge.
    Dependencies.  S01_BaseRing, S02_CauchyComplete, S03_QExp,
      S04_RealExpLogConv, S05_AlignmentGRPO, S06_DiffSamplingGibbs,
      S07_RealSetoidExpLog, S08_RealMainlineDPO, S09_EntropyReal,
      S10_KVQuantTrig, S11_TP3B5, mach_fold_q, mach_atan_addsub; Stdlib
      QArith (QArith/Qabs/Qround/Qminmax), ZArith, Lia, Setoid, Morphisms.
    Constructivity.  Zero admitting statements; every named statement is
      carried by Set through the QltT / QleT' / QeqT / real_eq faces; proof
      bodies consume constructive Prop bookkeeping (Qle / Qlt tail chains)
      inside proofs only.

    Order no.  Route 2, work order R2-WA (Mach premise layer), step P2:
      cross-tree aligned recast of the fold chain.

    Statement faces.  mach_q_pos_1_5, mach_q_lt1_1_5, mach_q_le_1_5_double,
      mach_q_pos_1183_2873, mach_q_le_add_premise, mach_q_add_transform_1_5,
      mach_arctan_bound_irrelevance, mach_arctan_const_ext, mach_fold_chain,
      mach_edge_one -- every named statement is carried by Set through the
      QltT / QleT' / QeqT / real_eq faces; zero Prop statement faces.

    Source routing.  Recast of the main93-tree module onto the Set
      statement faces (Set snapshot of S02_CauchyComplete /
      S10_KVQuantTrig / S11_TP3B5).  The alignment delta against the
      baseline module sits in the pointwise-transport proofs:
      arctan_real_proj and real_const_proj are consumed in their QeqT
      faces through the bridge qeqT_imp_qeq (cross-tree signature map,
      groups 3 and 7); all other faces and proofs carry over verbatim.

    Build.  coqc -native-compiler no -q -Q <sandbox> "" mach_fold_chain.v
      -- Rocq 9.3.0; the sandbox world carries the Set-form S01..S14 chain
      plus the mach_fold_q / mach_atan_addsub transplants.

    Related registrations.  Consumes the S02 bridges Qlt_to_QltT,
      Qle_to_QleT', qeq_imp_qeqT, qeqT_imp_qeq; the ten statement names
      above are exclusive in the Set tree (cross-tree declaration census:
      no collisions).  Proof bodies consume constructive Prop facts
      (Qle / Qlt chains from the tail-bound bookkeeping) inside the
      proofs only. *)

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
Require Import mach_fold_q.
Require Import mach_atan_addsub.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               Lists.List Bool.Bool Arith.Arith.
Import ListNotations.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax.
From Stdlib Require Import ZArith.
Import PropositionConvergenceCore.
Opaque Qred.

(* ============================================================ *)
(* Section 1  Closed-fraction premises and transform certificates   *)
(*                                                                *)
(*   The range checks are the pointwise premises of the addition    *)
(*   formula (0 < u, 0 < v, u < 1, v < 1 and the fifth premise      *)
(*   u + v + u*v <= 1) at u = 1/5 (the doubling step) and at        *)
(*   u = 5/12, v = 1183/2873 (the final step); the transform        *)
(*   lemmas connect the (u+v)/(1-u*v) shape of the addition-formula *)
(*   conclusion with the literal shapes certified at the Q level.   *)
(* ============================================================ *)

Lemma mach_q_pos_1_5 : QltT 0 (1 # 5).
Proof.
  apply Qlt_to_QltT.
  change (0 * 5 < 1 * 1)%Z.
  lia.
Defined.

Lemma mach_q_lt1_1_5 : QltT (1 # 5) 1.
Proof.
  apply Qlt_to_QltT.
  change (1 * 1 < 1 * 5)%Z.
  lia.
Defined.

(* Fifth premise of the doubling step: 1/5 + 1/5 + 1/25 = 11/25 <= 1. *)
Lemma mach_q_le_1_5_double : QleT' ((1 # 5) + (1 # 5) + (1 # 5) * (1 # 5)) 1.
Proof.
  apply Qle_to_QleT'.
  change ((10 * 25 + 1 * 25) * 1 <= 1 * (25 * 25))%Z.
  lia.
Defined.

Lemma mach_q_pos_1183_2873 : QltT 0 (1183 # 2873).
Proof.
  apply Qlt_to_QltT.
  change (0 * 2873 < 1183 * 1)%Z.
  lia.
Defined.

(* Fifth premise of the final step: the numerator 28561 + 5915 = 34476
   over 34476*34476 is exactly 1 (28561 = 13^4, see mach_q_decompose_28561). *)
Lemma mach_q_le_add_premise :
  QleT' ((5 # 12) + (1183 # 2873) + (5 # 12) * (1183 # 2873)) 1.
Proof.
  apply Qle_to_QleT'.
  change ((28561 * 34476 + 5915 * 34476) * 1 <= 1 * (34476 * 34476))%Z.
  lia.
Defined.

(* Doubling-step tan-value transform: (1/5 + 1/5)/(1 - 1/25) == 5/12,
   the companion shape of mach_q_tan2a's 2*(1/5) form. *)
Lemma mach_q_add_transform_1_5 :
  QeqT (((1 # 5) + (1 # 5)) / (1 - (1 # 5) * (1 # 5))) (5 # 12).
Proof.
  apply qeq_imp_qeqT.
  vm_compute.
  reflexivity.
Defined.

(* ============================================================ *)
(* Section 2  Witness irrelevance and constant extensionality for   *)
(*            the real arctan values                                *)
(* ============================================================ *)

(* The real arctan value depends only on the argument, not on the
   choice of the pointwise-bound witness. *)
Lemma mach_arctan_bound_irrelevance :
  forall (x : Real)
         (Hx Hy : forall n : nat, QleT' (Qabs (projT1 x n)) 1),
    real_eq (cauchy_real_arctan x Hx) (cauchy_real_arctan x Hy).
Proof.
  intros x Hx Hy.
  apply mach_real_eq_pt.
  intro n.
  apply qeq_imp_qeqT.
  (* One transport per projection: both witnesses share the argument x,
     so the pointwise face lands on the reflexive Qeq shape. *)
  repeat setoid_rewrite (qeqT_imp_qeq _ _ (arctan_real_proj x Hx n)).
  repeat setoid_rewrite (qeqT_imp_qeq _ _ (arctan_real_proj x Hy n)).
  reflexivity.
Defined.

(* Equal rational constants give equal real arctan values under the two
   pointwise-bound witnesses (partial sums extend along Qeq; see
   mach_arctan_partial_ext). *)
Lemma mach_arctan_const_ext :
  forall (a b : Q)
         (Ha : forall n : nat, QleT' (Qabs (projT1 (real_const a) n)) 1)
         (Hb : forall n : nat, QleT' (Qabs (projT1 (real_const b) n)) 1),
    QeqT a b ->
    real_eq (cauchy_real_arctan (real_const a) Ha)
            (cauchy_real_arctan (real_const b) Hb).
Proof.
  intros a b Ha Hb HabT.
  pose proof (qeqT_imp_qeq a b HabT) as Hab.
  apply mach_real_eq_pt.
  intro n.
  apply qeq_imp_qeqT.
  setoid_rewrite (qeqT_imp_qeq _ _ (arctan_real_proj (real_const a) Ha n)).
  setoid_rewrite (qeqT_imp_qeq _ _ (arctan_real_proj (real_const b) Hb n)).
  setoid_rewrite (qeqT_imp_qeq _ _ (real_const_proj a n)).
  setoid_rewrite (qeqT_imp_qeq _ _ (real_const_proj b n)).
  exact (qeqT_imp_qeq _ _ (mach_arctan_partial_ext n a b HabT)).
Defined.

(* ============================================================ *)
(* Section 3  The fold theorem                                      *)
(*                                                                *)
(*   Controlled pivots: D = arctan(5/12), Bsub = arctan(1/239)       *)
(*   (difference-form witness), W = arctan(1183/2873).  The assembly *)
(*   has five legs:                                                  *)
(*   (1) 4*A - B == 4*A - Bsub (witness transport);                  *)
(*   (2) 4*A == D + D (doubling instance + multiplicative constant   *)
(*       distribution);                                              *)
(*   (3) (D+D) - Bsub == D + (D - Bsub) (associativity);             *)
(*   (4) D - Bsub == W (difference instance + the 1183/2873          *)
(*       transform);                                                 *)
(*   (5) D + W == arctan(1) (addition instance + the value-1         *)
(*       transform).                                                 *)
(* ============================================================ *)

Theorem mach_fold_chain : real_eq mach_pi_quarter arctan_one_real.
Proof.
  unfold mach_pi_quarter.
  set (Dcert := mach_pt_bound_of_lt (5 # 12)
                  (qleT'_ltT_ltT 0 (1 # 239) (5 # 12)
                     (qltT_leT' 0 (1 # 239) mach_q_range_0_lt_1_239T)
                     mach_q_range_1_239_lt_5_12T)
                  mach_q_range_5_12_lt1T).
  set (D := cauchy_real_arctan (real_const (5 # 12)) Dcert).
  set (Bsubcert := mach_pt_bound_of_lt (1 # 239) mach_q_range_0_lt_1_239T
                     (qleT'_ltT_ltT (1 # 239) (5 # 12) 1
                        (qltT_leT' (1 # 239) (5 # 12) mach_q_range_1_239_lt_5_12T)
                        mach_q_range_5_12_lt1T)).
  set (Bsub := cauchy_real_arctan (real_const (1 # 239)) Bsubcert).
  set (Wcert := mach_pt_bound_of_lt (1183 # 2873)
                  mach_q_pos_1183_2873 mach_q_range_1183_2873_lt1T).
  set (W := cauchy_real_arctan (real_const (1183 # 2873)) Wcert).
  (* The three formula instances: difference (5/12, 1/239), final
     addition (5/12, 1183/2873), doubling addition (1/5, 1/5). *)
  pose proof (mach_atan_sub (5 # 12) (1 # 239)
              mach_q_range_0_lt_1_239T mach_q_range_1_239_lt_5_12T
              mach_q_range_5_12_lt1T) as Hsub.
  pose proof (mach_atan_add (5 # 12) (1183 # 2873)
              (qleT'_ltT_ltT 0 (1 # 239) (5 # 12)
                 (qltT_leT' 0 (1 # 239) mach_q_range_0_lt_1_239T)
                 mach_q_range_1_239_lt_5_12T)
              mach_q_pos_1183_2873 mach_q_range_5_12_lt1T
              mach_q_range_1183_2873_lt1T mach_q_le_add_premise) as Hadd.
  pose proof (mach_atan_add (1 # 5) (1 # 5) mach_q_pos_1_5 mach_q_pos_1_5
              mach_q_lt1_1_5 mach_q_lt1_1_5 mach_q_le_1_5_double) as Hdbl.
  (* Doubling: 2*A == A + A. *)
  pose proof (mach_real_const_one_mult mach_atan_one_fifth) as Hone.
  assert (H2A : real_eq (real_mult (real_const 2) mach_atan_one_fifth)
                        (real_plus mach_atan_one_fifth mach_atan_one_fifth)).
  { eapply real_eq_trans.
    - exact (real_eq_sym _ _ (mach_real_const_lin2 mach_atan_one_fifth 1 1)).
    - apply (RealSetoid.real_eq_plus_compat _ _ _ _); exact Hone. }
  (* Witness transport of the doubling conclusion:
     arctan((1/5+1/5)/(1-1/25)) == D. *)
  pose proof (mach_arctan_bound_irrelevance (real_const (1 # 5)) mach_pt_bound_1_5
                 (mach_pt_bound_of_lt (1 # 5) mach_q_pos_1_5 mach_q_lt1_1_5)) as HA_c.
  assert (HAA : real_eq (real_plus mach_atan_one_fifth mach_atan_one_fifth) D).
  { eapply real_eq_trans.
    - apply (RealSetoid.real_eq_plus_compat mach_atan_one_fifth mach_atan_one_fifth
              (cauchy_real_arctan (real_const (1 # 5))
                 (mach_pt_bound_of_lt (1 # 5) mach_q_pos_1_5 mach_q_lt1_1_5))
              (cauchy_real_arctan (real_const (1 # 5))
                 (mach_pt_bound_of_lt (1 # 5) mach_q_pos_1_5 mach_q_lt1_1_5)));
      [exact HA_c | exact HA_c].
    - eapply real_eq_trans.
      + exact Hdbl.
      + apply (mach_arctan_const_ext _ (5 # 12) _ Dcert mach_q_add_transform_1_5). }
  (* 4*A == (A+A)+(A+A) == D + D. *)
  assert (H4ADD : real_eq (real_mult (real_const 4) mach_atan_one_fifth)
                          (real_plus D D)).
  { eapply real_eq_trans.
    - exact (real_eq_sym _ _ (mach_real_const_lin2 mach_atan_one_fifth 2 2)).
    - eapply real_eq_trans.
      + apply (RealSetoid.real_eq_plus_compat
                 (real_mult (real_const 2) mach_atan_one_fifth)
                 (real_mult (real_const 2) mach_atan_one_fifth)
                 (real_plus mach_atan_one_fifth mach_atan_one_fifth)
                 (real_plus mach_atan_one_fifth mach_atan_one_fifth));
         [exact H2A | exact H2A].
      + apply (RealSetoid.real_eq_plus_compat
                 (real_plus mach_atan_one_fifth mach_atan_one_fifth)
                 (real_plus mach_atan_one_fifth mach_atan_one_fifth)
                 D D); [exact HAA | exact HAA]. }
  (* Difference leg: D - Bsub == W (through the 1183/2873 transform). *)
  assert (Hsubleg : real_eq (real_plus D (real_opp Bsub)) W).
  { eapply real_eq_trans.
    - exact Hsub.
    - apply (mach_arctan_const_ext _ (1183 # 2873) _ Wcert mach_q_diff_transformT). }
  (* Addition leg: D + W == arctan(1) (through the value-1 transform). *)
  assert (Hfin : real_eq (real_plus D W)
                   (cauchy_real_arctan (real_const 1) atan1_pt_bound)).
  { eapply real_eq_trans.
    - exact Hadd.
    - apply (mach_arctan_const_ext _ 1 _ atan1_pt_bound mach_q_add_transformT). }
  (* The five legs chained. *)
  assert (HL0 : real_eq (real_plus (real_mult (real_const 4) mach_atan_one_fifth)
                                   (real_opp mach_atan_1_239))
                        (real_plus (real_mult (real_const 4) mach_atan_one_fifth)
                                   (real_opp Bsub))).
  { apply (RealSetoid.real_eq_plus_compat _ _ _ _).
    - apply real_eq_refl.
    - apply (RealSetoid.real_eq_opp_compat _ _).
      apply (mach_arctan_bound_irrelevance (real_const (1 # 239))
              mach_pt_bound_1_239 Bsubcert). }
  assert (HL1 : real_eq (real_plus (real_mult (real_const 4) mach_atan_one_fifth)
                                   (real_opp Bsub))
                        (real_plus (real_plus D D) (real_opp Bsub))).
  { apply (RealSetoid.real_eq_plus_compat _ _ _ _).
    - exact H4ADD.
    - apply real_eq_refl. }
  assert (HL2 : real_eq (real_plus (real_plus D D) (real_opp Bsub))
                        (real_plus D (real_plus D (real_opp Bsub)))).
  { exact (real_eq_sym _ _ (mach_real_plus_assoc D D (real_opp Bsub))). }
  assert (HL3 : real_eq (real_plus D (real_plus D (real_opp Bsub)))
                        (real_plus D W)).
  { apply (RealSetoid.real_eq_plus_compat _ _ _ _).
    - apply real_eq_refl.
    - exact Hsubleg. }
  exact (real_eq_trans _ _ _ HL0
           (real_eq_trans _ _ _ HL1
              (real_eq_trans _ _ _ HL2 (real_eq_trans _ _ _ HL3 Hfin)))).
Defined.

(* ============================================================ *)
(* Section 4  The pi bridge                                         *)
(*                                                                *)
(*   Two transport steps: 4*mach_pi_quarter == 4*arctan_one_real      *)
(*   (multiplicative compatibility of the fold theorem) and           *)
(*   4*arctan_one_real == pi_L (the S11 a3_h4_value_bridge reused     *)
(*   as is).                                                          *)
(* ============================================================ *)

Theorem mach_edge_one :
  real_eq (real_mult (real_const 4) mach_pi_quarter) cauchy_real_pi_leibniz.
Proof.
  apply (real_eq_trans _ (real_mult (real_const 4) arctan_one_real)).
  - apply (RealSetoid.real_eq_mult_compat _ _ _ _).
    + apply real_eq_refl.
    + exact mach_fold_chain.
  - exact a3_h4_value_bridge.
Defined.
