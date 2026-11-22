(* ==========================================================================
   abl_W9_slice57_10.v - zero-use slot retirement anchors + A-family
   slice 5-7 numeric instance ablation.
   Mission. (1) S10/S12 zero-use slot retirement anchors: five retired
   slot shapes replicated verbatim as typed Definitions with numeric
   inhabitability witnesses; the four re-judged load-bearing slots
   carried by Check attention_is_gibbs_setoid (S10) and Check
   sf_ewc_pos_eps (S12). (2) The fisher square-sum instance (abstract
   layer forall t, real_le real_zero (real_mult t t) is an rLPO
   obstruction; recorded, not discharged): fisher := one square plus
   one square. (3) Slice 5-7 numeric instances: ir2_no_sqrtZ b:=1,
   ir2_delta_step n:=1, is3_no_sqrtZ b:=1, is3_delta_step n:=1,
   lic_core n:=1 (K universal), lic_rsum_lt n:=1, ln2b_pow_ge1 A:=1,
   ln2b_pow_bern A:=n:=1, ln2b_pow_core V:=A:=1, ln2b_pow_lift
   V:=A:=1 B:=2, ln2i_t_pos j:=1, ln2i_t_le j:=1; lic_window_shift
   composite premise recorded, not discharged.
   Dependencies. Stdlib QArith.QArith QArith.Qabs ZArith Lia Extraction;
   in-tree S01_BaseRing S02_CauchyComplete S03_QExp (q_fact) S07_RealSetoidExpLog
   S10_KVQuantTrig S12_B5RecycleSF UpReqBanachNormOpp (ZLtT carrier)
   UpReqIrrationalCriterion UpReqSqrt3Irrational UpReqLn2Irrational Ln2Bridge.
   References. abl_W9_Afamily_08 / abl_W9_slice34_09; slot anchors in the per-part body comments.
   Constructivity. Purely constructive, zero classical/acknowledgement faces;
   statement faces Set-carried (NatLe / Id / ZLtT / QleT' / QltT / real_lt /
   real_le; zero new Prop statements); upstream premise slots bridged in-proof
   (NatLe_drop / ZLtT_drop / QleT'_to_Qle / QltT_to_Qlt / id_eq_SI); strict
   nat-lt as NatLe (S n) m; pieces [Defined]; Print Assumptions all Closed (20);
   Obj.magic 0 (.ml/.mli).
   Build. coqc -Q <world> "" <file> via cpu_guard v3; Separate Extraction
   driver (single command, 20 slots), ocamlc, sample run.
   ========================================================================== *)

From Stdlib Require Import QArith.QArith QArith.Qabs ZArith Lia.
From Stdlib Require Import Extraction.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import S10_KVQuantTrig.
Require Import S12_B5RecycleSF.
Require Import UpReqBanachNormOpp.
Require Import UpReqIrrationalCriterion.
Require Import UpReqSqrt3Irrational.
Require Import UpReqLn2Irrational.
Require Import Ln2Bridge.

(* ============================================================ *)
(* Part 0 - numeric instance witnesses. Set-carrier faces of the *)
(*   index/positivity premises consumed by the slice instances:  *)
(*   NatLe (leb judgment identity), ZLtT (Z.ltb judgment), and   *)
(*   the successor form NatLe (S n) m, the definitional identity *)
(*   face of strict nat-lt (Nat.lt n m := Nat.le (S n) m).       *)
(* ============================================================ *)

Lemma abl10_idx1 : NatLe 1 1.
Proof. exact (NatLe_lift 1 1 (le_n 1)). Defined.

Lemma abl10_zpos1 : ZLtT 0 1.
Proof. unfold ZLtT. cbn. exact id_refl. Defined.

Lemma abl10_lt12 : NatLe (Datatypes.S (1 * 1 ^ (1 * 1))) (2 ^ (1 * 1)).
Proof. apply NatLe_lift. cbn. exact (le_n 2). Defined.

(* ============================================================ *)
(* Part 1 - zero-consumption slot retirement machine anchors.    *)
(*   Five typed Definitions replicate the retired slot shapes    *)
(*   verbatim; type-checking certifies the replication, and the  *)
(*   two inhabitability witnesses show the shapes inhabited at   *)
(*   numeric instances.                                          *)
(* ============================================================ *)

(* Slot real_L_pos @ S10:65 : real_lt real_zero L (single hit at the *)
(* declaration site, zero consumers tree-wide). *)
Definition abl10_shape_real_L_pos (L : Real) : Set := real_lt real_zero L.

Lemma abl10_real_L_pos_inhab : real_lt real_zero real_one.
Proof. exact real_lt_zero_one. Defined.

(* Slot real_metric_nonneg @ S10:68 : forall s s', real_le real_zero *)
(* (real_metric s s') (single hit at the declaration site). *)
Definition abl10_shape_real_metric_nonneg (S : Type)
  (real_metric : S -> S -> Real) : Type :=
  forall s s' : S, real_le real_zero (real_metric s s').

(* Zero-metric instance: the shape is inhabited (retirement is not a *)
(* phantom). *)
Definition abl10_metric_zero_inst (S : Type) : S -> S -> Real :=
  fun _ _ => real_zero.

Lemma abl10_metric_zero_nonneg : forall (S : Type) (s s' : S),
  real_le real_zero (abl10_metric_zero_inst S s s').
Proof. intros S s s'. exact (inr (real_eq_refl real_zero)). Defined.

(* SFRicciBlock section slots @ S12:13824/13827/13828 (zero theorems in *)
(* the section; the single internal use edge sf_drift_center <-         *)
(* sf_drift_lipschitz has zero tree-wide consumers). *)
Definition abl10_shape_sf_ricci_flow_step : Set := Real -> SFVec -> SFVec.

Definition abl10_shape_sf_drift_center : Set := Real -> SFSense -> SFSense.

Definition abl10_shape_sf_drift_lipschitz
  (sf_drift_center : Real -> SFSense -> SFSense) : Set :=
  forall (t1 t2 : Real) (c : SFSense),
    real_le (sf_dist_sq (sf_sense_coord (sf_drift_center t1 c))
                        (sf_sense_coord (sf_drift_center t2 c)))
            (sf_n2r 1).

(* Re-judged load-bearing slots: the four re-judged slots are carried by *)
(* the generalized signatures closed over in attention_is_gibbs_setoid   *)
(* (sum_req_over_S_ext / sum_req_over_S_linear / sum_pos_preserved_req)  *)
(* and sf_ewc_pos_eps (the fisher face); the two S10 Context binders are *)
(* non-zero-use. Machine anchors: *)
Check attention_is_gibbs_setoid.
Check sf_ewc_pos_eps.

(* ============================================================ *)
(* Part 2 - fisher square-sum constructive instance. The abstract *)
(*   layer forall t, real_le real_zero (real_mult t t) is an     *)
(*   rLPO-equivalent obstruction (recorded, not discharged); the *)
(*   lawful ablation axis is the numeric instance fisher := one  *)
(*   square + one square, composed from in-tree real-face pieces *)
(*   into a real_lt witness.                                     *)
(* ============================================================ *)

Definition abl10_sq1 : Real := real_mult real_one real_one.

Lemma abl10_sq1_pos : real_lt real_zero abl10_sq1.
Proof.
  exact (real_mult_pos_compat real_one real_one real_lt_zero_one
           real_lt_zero_one).
Defined.

Definition abl10_fisher_sqsum : Real := real_plus abl10_sq1 abl10_sq1.

Lemma abl10_fisher_sqsum_pos : real_lt real_zero abl10_fisher_sqsum.
Proof.
  exact (real_eq_lt_lt real_zero (real_plus real_zero real_zero)
           abl10_fisher_sqsum
           (real_eq_sym (real_plus real_zero real_zero) real_zero
              (real_plus_zero real_zero))
           (real_lt_plus_compat real_zero abl10_sq1 real_zero abl10_sq1
              abl10_sq1_pos abl10_sq1_pos)).
Defined.

(* Instantiation of the SFEWC assumption-slot shape real_le real_zero *)
(* sf_fisher at the fisher square-sum instance. *)
Lemma abl10_fisher_sqsum_nonneg : real_le real_zero abl10_fisher_sqsum.
Proof. exact (inl abl10_fisher_sqsum_pos). Defined.

(* ============================================================ *)
(* Part 3 - slice 5: Sqrt3 four slots.                          *)
(* ============================================================ *)

(* Coverage: ir2_no_sqrtZ @ UpReqSqrt3Irrational L180, slot 1 (0 < b)%Z *)
(* at b := 1; the equation premise is carried by the Id face (the Set   *)
(* equality judgment on Z) and bridged in-proof via id_eq_SI. *)
Theorem abl10_ir2_no_sqrtZ_b1 : forall a : Z,
  Id (a * a)%Z (2 * (1 * 1))%Z -> Empty_set.
Proof.
  intros a Ha.
  exact (False_rect Empty_set
           (ir2_no_sqrtZ a 1 (ZLtT_drop 0 1 abl10_zpos1)
              (id_eq_SI Z (a * a)%Z (2 * (1 * 1))%Z Ha))).
Defined.

(* Coverage: ir2_delta_step @ UpReqSqrt3Irrational L506, slot 1 *)
(* (1 <= n)%nat at n := 1; the Qle premise carrier is recast to *)
(* the decidable face QleT' and bridged in-proof. *)
Theorem abl10_ir2_delta_step_n1 :
  QleT' (ir2_delta 1) (1#4) ->
  QleT' (ir2_delta (Datatypes.S 1)) ((1#28) * ir2_delta 1).
Proof.
  intro H.
  exact (Qle_to_QleT' _ _
           (ir2_delta_step 1 (NatLe_drop _ _ abl10_idx1)
              (QleT'_to_Qle _ _ H))).
Defined.

(* Coverage: is3_no_sqrtZ @ UpReqSqrt3Irrational L1351, slot 1 *)
(* (0 < b)%Z at b := 1. *)
Theorem abl10_is3_no_sqrtZ_b1 : forall a : Z,
  Id (a * a)%Z (3 * (1 * 1))%Z -> Empty_set.
Proof.
  intros a Ha.
  exact (False_rect Empty_set
           (is3_no_sqrtZ a 1 (ZLtT_drop 0 1 abl10_zpos1)
              (id_eq_SI Z (a * a)%Z (3 * (1 * 1))%Z Ha))).
Defined.

(* Coverage: is3_delta_step @ UpReqSqrt3Irrational L1614, slot 1 *)
(* (1 <= n)%nat at n := 1. *)
Theorem abl10_is3_delta_step_n1 :
  QleT' (is3_delta 1) (1#16) ->
  QleT' (is3_delta (Datatypes.S 1)) ((1#176) * is3_delta 1).
Proof.
  intro H.
  exact (Qle_to_QleT' _ _
           (is3_delta_step 1 (NatLe_drop _ _ abl10_idx1)
              (QleT'_to_Qle _ _ H))).
Defined.

(* ============================================================ *)
(* Part 4 - slice 6: LIC two slots.                             *)
(* ============================================================ *)

(* Coverage: lic_core @ UpReqIrrationalCriterion L410, slot 1 *)
(* (1 <= n)%nat at n := 1, K universal. *)
Theorem abl10_lic_core_n1 : forall K : nat,
  QleT' (q_fact (1 + K) * (q_fact 1 * lic_rsum 1 K) + q_fact 1)
        (q_fact (1 + K)).
Proof.
  intro K.
  exact (Qle_to_QleT' _ _ (lic_core 1 K (NatLe_drop _ _ abl10_idx1))).
Defined.

(* Coverage: lic_rsum_lt @ UpReqIrrationalCriterion L495, slot 1 *)
(* (1 <= n)%nat at n := 1, K universal. *)
Theorem abl10_lic_rsum_lt_n1 : forall K : nat,
  QltT (lic_rsum 1 K) (1%Q / q_fact 1).
Proof.
  intro K.
  exact (Qlt_to_QltT _ _ (lic_rsum_lt 1 K (NatLe_drop _ _ abl10_idx1))).
Defined.

(* lic_window_shift @ UpReqIrrationalCriterion L621: composite premise
   forall k, 1<=k -> k<=2b+2 -> ... — recorded, not discharged; no numeric
   instance is derived here. *)

(* ============================================================ *)
(* Part 5 - slice 7: Ln2Bridge + UpReqLn2Irrational slots.      *)
(* ============================================================ *)

(* Coverage: ln2b_pow_ge1 @ Ln2Bridge L249, slot 1 (1 <= A)%nat at *)
(* A := 1, k universal. *)
Theorem abl10_ln2b_pow_ge1_A1 : forall k : nat, NatLe 1 (1 ^ k).
Proof.
  intro k.
  exact (ln2b_pow_ge1 1 k (NatLe_drop _ _ abl10_idx1)).
Defined.

(* Coverage: ln2b_pow_bern @ Ln2Bridge L258, slots 1/2 (1 <= A)(1 <= n) *)
(* at A := n := 1 (both slots consumed by the same instance). *)
Theorem abl10_ln2b_pow_bern_A1n1 :
  NatLe (1 ^ 1 + 1 * 1 ^ (1 - 1)) ((1 + 1) ^ 1).
Proof.
  exact (ln2b_pow_bern 1 1 (NatLe_drop _ _ abl10_idx1)
           (NatLe_drop _ _ abl10_idx1)).
Defined.

(* Coverage: ln2b_pow_core @ Ln2Bridge L288, slots 1/2 (1 <= V)(1 <= A) *)
(* at V := A := 1. The strict conclusion (1*1^(1*1) < (1+1)^(1*1))%nat *)
(* is rendered in the successor carrier NatLe (S n) m, the definitional *)
(* identity face of strict nat-lt. *)
Theorem abl10_ln2b_pow_core_V1A1 :
  NatLe (Datatypes.S (1 * 1 ^ (1 * 1))) ((1 + 1) ^ (1 * 1)).
Proof.
  exact (ln2b_pow_core 1 1 (NatLe_drop _ _ abl10_idx1)
           (NatLe_drop _ _ abl10_idx1)).
Defined.

(* Coverage: ln2b_pow_lift @ Ln2Bridge L306, slots 1/2 (1 <= V')(1 <= A') *)
(* at V' := A' := 1, with the associated B'-face strict premise instanced *)
(* at B' := 2 (abl10_lt12). Conclusion face: Id (Z.ltb ...) true. *)
Theorem abl10_ln2b_pow_lift_V1A1B2 :
  Id (Z.ltb (Z.of_nat 1 * (Z.of_nat 1) ^ (Z.of_nat 1 * Z.of_nat 1))
            ((Z.of_nat 2) ^ (Z.of_nat 1 * Z.of_nat 1))) true.
Proof.
  exact (ln2b_pow_lift 1 1 2 (NatLe_drop _ _ abl10_idx1)
           (NatLe_drop _ _ abl10_idx1) (NatLe_drop _ _ abl10_lt12)).
Defined.

(* Coverage: ln2i_t_pos @ UpReqLn2Irrational L136, slot 1 (1 <= j)%nat *)
(* at j := 1. *)
Theorem abl10_ln2i_t_pos_j1 : QltT 0 (ln2i_t 1).
Proof.
  exact (Qlt_to_QltT _ _ (ln2i_t_pos 1 (NatLe_drop _ _ abl10_idx1))).
Defined.

(* Coverage: ln2i_t_le @ UpReqLn2Irrational L147, slot 1 (1 <= j)%nat *)
(* at j := 1. *)
Theorem abl10_ln2i_t_le_j1 : QleT' (ln2i_t 1) (Qinv (ln2i_p2 1)).
Proof.
  exact (Qle_to_QleT' _ _ (ln2i_t_le 1 (NatLe_drop _ _ abl10_idx1))).
Defined.

(* ============================================================ *)
(* Part 6 - tail check: Print Assumptions on all statements,    *)
(*   then the in-file extraction check on two informative faces *)
(*   (the extraction gate proper is the Separate Extraction     *)
(*   driver over all 20 slots: Obj.magic 0 in .ml and .mli).    *)
(* ============================================================ *)

Print Assumptions abl10_idx1.
Print Assumptions abl10_zpos1.
Print Assumptions abl10_lt12.
Print Assumptions abl10_real_L_pos_inhab.
Print Assumptions abl10_metric_zero_nonneg.
Print Assumptions abl10_sq1_pos.
Print Assumptions abl10_fisher_sqsum_pos.
Print Assumptions abl10_fisher_sqsum_nonneg.
Print Assumptions abl10_ir2_no_sqrtZ_b1.
Print Assumptions abl10_ir2_delta_step_n1.
Print Assumptions abl10_is3_no_sqrtZ_b1.
Print Assumptions abl10_is3_delta_step_n1.
Print Assumptions abl10_lic_core_n1.
Print Assumptions abl10_lic_rsum_lt_n1.
Print Assumptions abl10_ln2b_pow_ge1_A1.
Print Assumptions abl10_ln2b_pow_bern_A1n1.
Print Assumptions abl10_ln2b_pow_core_V1A1.
Print Assumptions abl10_ln2b_pow_lift_V1A1B2.
Print Assumptions abl10_ln2i_t_pos_j1.
Print Assumptions abl10_ln2i_t_le_j1.

(* Extraction check: the real_le data face (fisher square-sum instance) *)
(* and one judgment face. *)
Recursive Extraction abl10_fisher_sqsum_nonneg.
Recursive Extraction abl10_ln2b_pow_bern_A1n1.
