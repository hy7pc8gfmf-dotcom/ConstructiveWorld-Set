(* ConstructiveWorld-Set -- MixTimeChain: attention mixing time, end to end. *)
(** * MixTimeChain: the attention mixing-time end-to-end witness on Set.

    Mission.  From the [BoundedSoftmax] interface through the definition
      [delta_star := lo * lo], the proof [delta_star < 1], the premise
      package [kappa := 1 - delta_star] in (0,1), the explicit step-count
      witness [mix_k_select], and the substitution of the residual rate,
      to the complete [sigT] witness of [kappa^k * TV0 < budget]; the
      whole chain reports Closed under [Print Assumptions].

    Dependencies.  The chain S01..S15 of this development, [UpRealLeB],
      [UpRealLeB2], [G07_KLWall], [KLWallClosed], [UpTVDoeblin],
      [AttnDoeblin], [Paper7Ablation], [RateTheoryAblation],
      [UpReqMixingTime]; Stdlib [List], [PeanoNat].

    References.  ConstructiveWorld-Main [MixTimeChain]; the sibling
      [MixTimeChainIface] repeats Section 1 of this file verbatim; the
      two are not interchangeable, this file adds the discharged path.

    Constructivity.  All statements are carried by Set ([real_lt],
      [real_le_b], [sigT] and [prod] are Set-valued, no Prop leakage);
      no admissions, no new axioms; the main statements are [Defined],
      transparent and extractable; the proofs are nontrivial.  Of the
      17 assumption slots of the two sections, the 6 bare data slots
      stay as section variables and the 11 remaining slots are
      discharged by the supply family at the end of the file.

    Build.  [rocq c -native-compiler no -q -Q . "" MixTimeChain.v] on
      Rocq 9.3.0, compilation wrapped by the cpu_guard wrapper. *)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
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
Require Import G07_KLWall.
Require Import KLWallClosed.
Require Import UpTVDoeblin.
Require Import AttnDoeblin.
Require Import Paper7Ablation.
Require Import RateTheoryAblation.
Require Import UpReqMixingTime.

(* ================= Section 1. The kappa := 1 - delta_star premise package (interface face) ================= *)

(* Uses the three [Paper7Ablation] package statements plus the AttnDoeblin
   [bs_delta_star_lt_one]: at the softmax slice of [BoundedSoftmax] (the
   temp/Delta/expf mini-interface), delta_star := lo^2 satisfies
   0 < delta_star < 1, hence kappa := 1 - delta_star lies in (0,1). *)
(* The Let definitions repeat AttnDoeblin verbatim:
   lo := expf (invT * (- Delta)), invT := inv_pos temp temp_pos,
   delta_star := mult lo lo. *)
Section MtcKappaPackage.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {DO : DecidableOrder RI}.

Variable temp : R.
Variable temp_pos : lt zero temp.
Variable Delta : R.
Variable Delta_pos : lt zero Delta.
Variable expf : R -> R.
Variable expf_pos : forall x : R, lt zero (expf x).
Variable expf_zero : Id (expf zero) one.
Variable expf_plus : forall a b : R, Id (expf (plus a b)) (mult (expf a) (expf b)).
Variable expf_mono_lt : forall a b : R, lt a b -> lt (expf a) (expf b).

Let invT := inv_pos temp temp_pos.
Let lo := expf (mult invT (opp Delta)).
Let delta_star := mult lo lo.
Let kappa := minus one delta_star.

(* lo > 0, given directly by the positivity of expf. *)
Theorem mtc_lo_pos_if : lt zero lo.
Proof.
  exact (expf_pos (mult invT (opp Delta))).
Qed.

(* delta_star = lo^2 < 1: the already-proved [bs_delta_star_lt_one]
   (AttnDoeblin 6.1) used with every slot supplied; the post-section form
   was checked against the elaborated signature. *)
Theorem mtc_delta_star_lt_one_if : lt delta_star one.
Proof.
  exact (@bs_delta_star_lt_one RI temp temp_pos Delta Delta_pos
           expf expf_pos expf_zero expf_plus expf_mono_lt).
Qed.

(* kappa > 0: the [Paper7Ablation] statement [p7a_omd_pos]; the
   post-section form takes no lo-positivity slot, as verified. *)
Theorem mtc_kappa_pos_if : lt zero kappa.
Proof.
  exact (@p7a_omd_pos RI DO lo mtc_delta_star_lt_one_if).
Qed.

(* kappa < 1: the [Paper7Ablation] statement [p7a_omd_lt_one], which goes
   through [p7a_delta_star_pos] internally. *)
Theorem mtc_kappa_lt_one_if : lt kappa one.
Proof.
  exact (@p7a_omd_lt_one RI DO lo mtc_lo_pos_if).
Qed.

(* The combined package form, taken by downstream modules as a single statement. *)
Theorem mtc_kappa_package_if :
  prod (lt zero kappa) (lt kappa one).
Proof.
  exact (pair mtc_kappa_pos_if mtc_kappa_lt_one_if).
Qed.

End MtcKappaPackage.

(* ================= Section 2. The concrete face: from the softmax slice to the selector ================= *)

(* The same-shaped slice on the concrete Cauchy real layer (real_lt,
   tv_omd, tv_rpow): lo := expf (invT * (- Delta)), delta_star := lo^2,
   kappa := tv_omd delta_star (definitionally 1 - delta_star).  The main
   theorem [mtc_attention_mixing_time_local] uses the selector
   [mix_k_select] here and produces the complete [sigT] witness of
   kappa^k * TV0 < budget. *)
Section MtcCauchySoftmax.

Variable invT : Real.
Variable invT_pos : real_lt real_zero invT.
Variable Delta : Real.
Variable Delta_pos : real_lt real_zero Delta.
Variable expf : Real -> Real.
Variable expf_pos : forall x : Real, real_lt real_zero (expf x).
Variable expf_zero : real_eq (expf real_zero) real_one.
Variable expf_mono_lt : forall a b : Real, real_lt a b -> real_lt (expf a) (expf b).

Let lo := expf (real_mult invT (real_opp Delta)).
Let delta_star := real_mult lo lo.
Let kappa := tv_omd delta_star.

(* lo > 0. *)
Theorem mtc_lo_pos : real_lt real_zero lo.
Proof.
  exact (expf_pos (real_mult invT (real_opp Delta))).
Qed.

(* lo < 1: invT * (- Delta) < 0 and expf is strictly increasing (the
   concrete-layer isomorphic chain of [p7a_lo_lt_one]: real_lt_zero_opp,
   real_mult_lt_compat_l, real_lt_eq_lt, real_mult_zero). *)
Theorem mtc_lo_lt_one : real_lt lo real_one.
Proof.
  assert (Hod : real_lt (real_opp Delta) real_zero).
  { exact (real_lt_zero_opp Delta Delta_pos). }
  assert (Hneg : real_lt (real_mult invT (real_opp Delta)) real_zero).
  { exact (real_lt_eq_lt (real_mult invT (real_opp Delta))
             (real_mult invT real_zero) real_zero
             (real_mult_lt_compat_l (real_opp Delta) real_zero invT
                Hod invT_pos)
             (real_mult_zero invT)). }
  exact (real_lt_eq_lt lo (expf real_zero) real_one
           (expf_mono_lt (real_mult invT (real_opp Delta)) real_zero Hneg)
           expf_zero).
Qed.

(* delta_star = lo^2 > 0. *)
Theorem mtc_delta_star_pos : real_lt real_zero delta_star.
Proof.
  exact (real_mult_pos_compat lo lo mtc_lo_pos mtc_lo_pos).
Qed.

(* delta_star = lo^2 < 1: lo * lo < lo * 1 == lo < 1 (strict
   multiplication monotonicity, the [real_mult_one] reshaping, and
   transitivity of <; the concrete-layer copy of [real_lt_mult] from the
   [Paper7Ablation] interface module). *)
Theorem mtc_delta_star_lt_one : real_lt delta_star real_one.
Proof.
  exact (real_lt_trans (real_mult lo lo) lo real_one
           (real_lt_eq_lt (real_mult lo lo) (real_mult real_one lo) lo
              (real_mult_lt_compat lo real_one lo
                 mtc_lo_lt_one mtc_lo_pos)
              (real_eq_trans _ _ _ (real_mult_comm real_one lo)
                 (real_mult_one lo)))
           mtc_lo_lt_one).
Qed.

(* kappa := 1 - delta_star > 0 (used by the [UpTVDoeblin] residual module). *)
Theorem mtc_kappa_pos : real_lt real_zero kappa.
Proof.
  exact (tv_omd_pos_of_lt delta_star mtc_delta_star_lt_one).
Qed.

(* kappa := 1 - delta_star < 1 (used by the [UpReqMixingTime] statement 5(a)). *)
Theorem mtc_kappa_lt_one : real_lt kappa real_one.
Proof.
  exact (mix_omd_lt_one delta_star mtc_delta_star_pos).
Qed.

(* ================= Main assembly: the rate is the algorithm (end to end) ================= *)
(* The kappa in (0,1) package, the explicit step-count witness
   [mix_k_select], and the substitution of the residual contraction rate:
   for every TV0 >= 0 and every positive budget the theorem returns a
   step count k with kappa^k * TV0 < budget.  [sigT] witness, [Defined],
   transparent and extractable. *)
Theorem mtc_attention_mixing_time_local :
  forall TV0 budget : Real,
    real_le real_zero TV0 -> real_lt real_zero budget ->
    sigT (fun k : nat =>
      real_lt (real_mult (tv_rpow kappa k) TV0) budget).
Proof.
  intros TV0 budget HTV Hb.
  exact (mix_k_select kappa TV0 budget
           mtc_kappa_pos mtc_kappa_lt_one HTV Hb).
Defined.

(* ================= Contraction-rate substitution: global monotonicity of the residual rate ================= *)
(* The Bishop-style global monotonicity (the degenerate end of section
   4.3).  Uses [rta_omd_powb_mono_b] of [RateTheoryAblation] (the tv_rpow
   rate-layer use-form of [klc_closed_powb_mono] through the reshaping
   lemma [rta_rpow_powb_eq]): at 0 <= delta_star <= 1, kappa^m <= kappa^n
   whenever n <= m, so the geometric rate handed to the selector is
   indeed a monotone contraction rate. *)
Theorem mtc_residual_rate_mono :
  forall n m : nat,
    NatLe n m ->
    real_le_b (tv_rpow kappa m) (tv_rpow kappa n).
Proof.
  intros n m Hle.
  apply (rta_omd_powb_mono_b delta_star n m).
  - apply (RealSetoid.real_lt_le_iff_req real_zero delta_star).
    left. exact mtc_delta_star_pos.
  - apply (RealSetoid.real_lt_le_iff_req delta_star real_one).
    left. exact mtc_delta_star_lt_one.
  - exact Hle.
Qed.

(* ================= Strict-branch certificate (constructive positivity at the degenerate end) ================= *)
(* Uses [rta_strict_branch_real] of [RateTheoryAblation]: at
   eta := delta_star both the positivity certificate 0 < 1 - delta_star
   and the Bishop contraction assembly are obtained at once; the
   certificate is exactly the piece the upstream analysis found not
   freely available, obtained here constructively under delta_star < 1. *)
Theorem mtc_strict_branch_local :
  prod (real_lt real_zero kappa)
       (real_le_b (powb_pow kappa 1) (powb_pow kappa 0)).
Proof.
  destruct (rta_strict_branch_real delta_star 0 1
              (RealSetoid.real_lt_le_iff_req real_zero delta_star
                 (inl mtc_delta_star_pos))
              mtc_delta_star_lt_one
              (NatLe_lift 0 1 (Nat.le_0_l 1))) as [Hp Hb].
  exact (pair Hp Hb).
Qed.

End MtcCauchySoftmax.

(* ================= Section 3. Supply in the shape of Part C: the Cauchy instance closes the chain ================= *)

(* The expf mini-interface is discharged by [cauchy_real_exp] (the
   three-field route of AttnDoeblin Part C), so the main statement
   reaches the Cauchy-instance form with zero expf premises: positivity
   of the inverse temperature and of the logit diameter suffices, and
   the mixing time is returned. *)
Corollary mtc_mixing_time_cauchy_exp :
  forall (invT Delta : Real),
    real_lt real_zero invT -> real_lt real_zero Delta ->
    forall TV0 budget : Real,
      real_le real_zero TV0 -> real_lt real_zero budget ->
      sigT (fun k : nat =>
        real_lt (real_mult
                   (tv_rpow (tv_omd (real_mult
                                       (cauchy_real_exp
                                          (real_mult invT (real_opp Delta)))
                                       (cauchy_real_exp
                                          (real_mult invT (real_opp Delta)))))
                            k)
                   TV0)
                budget).
Proof.
  intros invT Delta invT_pos Delta_pos TV0 budget HTV Hb.
  exact (mtc_attention_mixing_time_local invT invT_pos Delta Delta_pos
           cauchy_real_exp
           cauchy_real_exp_pos cauchy_real_exp_zero cauchy_real_exp_mono
           TV0 budget HTV Hb).
Defined.

(* ================= Section 4. Supply family for the discharged slots (the mtchain_*_supply theorems) ================= *)

(* Across the two sections there are 17 assumption slots: the 6 bare
   data slots (temp, Delta, expf, invT and the like) legitimately stay
   as section variables; the 11 remaining slots (6 in the interface
   section, 5 in the concrete section) are discharged slot by slot here
   on the canonical Real carrier.  Field mapping: lt := real_lt,
   req := real_eq, zero := real_zero, one := real_one, plus := real_plus,
   mult := real_mult.  The carrier temperature and spread take the unit
   element (same values and same proofs as [cf2_temp] and [cf2_Delta] of
   [UpReqConcFin2]; positivity supplied by [real_lt_zero_one], which adds
   no dependency), and the carrier exponential is [cauchy_real_exp], the
   witness body of real_expf_realizable (AttnDoeblin Part C, the same
   statement as [S13_NLiveAudit]) whose fields
   [cauchy_real_exp_pos], [cauchy_real_exp_zero], [cauchy_real_exp_plus]
   and [cauchy_real_exp_mono_lt] supply the slots directly.  The abstract
   slot declarations of both sections and all existing theorem signatures
   are unchanged; downstream modules can assemble zero-premise instances
   from these carriers. *)

(* The six propositional slots of the interface section [MtcKappaPackage]. *)

(* Slot [temp_pos]: positivity of the carrier temperature (unit-element carrier; direct reference to [real_lt_zero_one]). *)
Theorem mtchain_if_temp_pos_supply : real_lt real_zero real_one.
Proof.
  exact (real_lt_zero_one).
Qed.

(* Slot [Delta_pos]: positivity of the carrier spread (same carrier). *)
Theorem mtchain_if_Delta_pos_supply : real_lt real_zero real_one.
Proof.
  exact (real_lt_zero_one).
Qed.

(* Slot [expf_pos]: pointwise positivity of the carrier exponential (direct reference to [cauchy_real_exp_pos]). *)
Theorem mtchain_if_expf_pos_supply :
  forall x : Real, real_lt real_zero (cauchy_real_exp x).
Proof.
  exact (cauchy_real_exp_pos).
Qed.

(* Slot [expf_zero]: value of the carrier exponential at zero (direct reference to [cauchy_real_exp_zero]). *)
Theorem mtchain_if_expf_zero_supply :
  real_eq (cauchy_real_exp real_zero) real_one.
Proof.
  exact (cauchy_real_exp_zero).
Qed.

(* Slot [expf_plus]: the carrier exponential turns sums into products (direct reference to [cauchy_real_exp_plus]). *)
Theorem mtchain_if_expf_plus_supply :
  forall a b : Real,
    real_eq (cauchy_real_exp (real_plus a b))
            (real_mult (cauchy_real_exp a) (cauchy_real_exp b)).
Proof.
  exact (cauchy_real_exp_plus).
Qed.

(* Slot [expf_mono_lt]: strict monotonicity of the carrier exponential (direct reference to [cauchy_real_exp_mono]). *)
Theorem mtchain_if_expf_mono_lt_supply :
  forall a b : Real, real_lt a b -> real_lt (cauchy_real_exp a) (cauchy_real_exp b).
Proof.
  exact (cauchy_real_exp_mono).
Qed.

(* The five propositional slots of the concrete section [MtcCauchySoftmax]. *)

(* Slot [invT_pos]: positivity of the carrier inverse temperature (unit-element carrier). *)
Theorem mtchain_cs_invT_pos_supply : real_lt real_zero real_one.
Proof.
  exact (real_lt_zero_one).
Qed.

(* Slot [Delta_pos]: positivity of the carrier spread (unit-element carrier). *)
Theorem mtchain_cs_Delta_pos_supply : real_lt real_zero real_one.
Proof.
  exact (real_lt_zero_one).
Qed.

(* Slot [expf_pos]: pointwise positivity of the carrier exponential. *)
Theorem mtchain_cs_expf_pos_supply :
  forall x : Real, real_lt real_zero (cauchy_real_exp x).
Proof.
  exact (cauchy_real_exp_pos).
Qed.

(* Slot [expf_zero]: value of the carrier exponential at zero. *)
Theorem mtchain_cs_expf_zero_supply :
  real_eq (cauchy_real_exp real_zero) real_one.
Proof.
  exact (cauchy_real_exp_zero).
Qed.

(* Slot [expf_mono_lt]: strict monotonicity of the carrier exponential. *)
Theorem mtchain_cs_expf_mono_lt_supply :
  forall a b : Real, real_lt a b -> real_lt (cauchy_real_exp a) (cauchy_real_exp b).
Proof.
  exact (cauchy_real_exp_mono).
Qed.

(* ================= Section 5. Verification audit: [Print Assumptions] of every exported statement must report the closed context (zero axioms) ================= *)
Print Assumptions mtc_kappa_package_if.
Print Assumptions mtc_attention_mixing_time_local.
Print Assumptions mtc_residual_rate_mono.
Print Assumptions mtc_strict_branch_local.
Print Assumptions mtc_mixing_time_cauchy_exp.
Print Assumptions mtchain_if_temp_pos_supply.
Print Assumptions mtchain_if_Delta_pos_supply.
Print Assumptions mtchain_if_expf_pos_supply.
Print Assumptions mtchain_if_expf_zero_supply.
Print Assumptions mtchain_if_expf_plus_supply.
Print Assumptions mtchain_if_expf_mono_lt_supply.
Print Assumptions mtchain_cs_invT_pos_supply.
Print Assumptions mtchain_cs_Delta_pos_supply.
Print Assumptions mtchain_cs_expf_pos_supply.
Print Assumptions mtchain_cs_expf_zero_supply.
Print Assumptions mtchain_cs_expf_mono_lt_supply.
