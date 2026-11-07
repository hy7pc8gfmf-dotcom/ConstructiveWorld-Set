(* ConstructiveWorld-Set — the firewall requirement section's two
   temperature-monotonicity assumption slots at the interface-union context. *)
(** * PA_TempMonoW2Mark: the [tmw_] temperature-monotonicity family.

    Mission.  The [tmw_] family — two conditional forms (carrying the
      explicit extra premise beta1 > beta2) and two full-strength forms, plus
      the minimal demonstration item [tmw_le_minus_nonneg_fw_et]; the
      strength difference is disclosed as-is (each discharge theorem carries
      one premise the requirement slot does not have).
    Dependencies.  Requires [S01_BaseRing] through [S15_TailFEPUp],
      [UpReqAlgebra], [UpReqDist], [UpReqTempEntropy]
      ([req_energy_exp_temp_mono], [req_energy_exp_temp_strict_mono],
      [req_inv_pos_lt_contra]), [UpFirewallReq] ([fw_et], [fw_bt],
      [fw_bt_pos]) of this development; the argument-less [Class]
      [RealInterfaceEnhancedSetoid] (module [RealInterfaceEnhancedMod]).
    References.  This development and the ConstructiveWorld-Main baseline
      module of the same name: energy monotonicity of the temperature-scaled
      Gibbs family (statistical-mechanics formalization); statement names
      carried over verbatim from the source piece; adaptation = pure binder
      removal + notation rebinding on this development's own precedent:
      [R := Real] by notation, predicate faces [real_lt]/[real_eq]/[real_le],
      [fw_et]/[fw_bt]/[fw_bt_pos] at the argument-less face, proof bodies
      discharged by direct consumption of the in-register supply theorems.
    Constructivity.  All statements live on the [Set] layer; every station
      closes with [Qed], zero admitted items; pure term assembly (zero
      rewrite tactics); the tail [Print Assumptions] lines report the
      closure face; no new axioms.
    Build.  [rocq c -native-compiler no -q -Q ConstructiveWorld_Live ""
      PA_TempMonoW2Mark.v] compiles cleanly (exit 0) under the [cpu_guard]
      thermal wrapper with [ulimit -s 65532]. *)

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
Require Import UpReqAlgebra.
Require Import UpReqDist.
Require Import UpReqTempEntropy.
Require Import UpFirewallReq.
Import RealInterfaceEnhancedMod.
Notation R := Real.

(* The witness context: the union of the firewall requirement section's
   assumption face with the discharge face of Section ReqTempEntropy;
   one witness per assumption slot. *)
Section TmwMonoW2.
Variable S : Set.
Variable sumf : (S -> R) -> R.

(* ---- summation face (the requirement ssum_* slots and the discharge
   fsum_* slots, same-shape union) ---- *)
Hypothesis tmw_sum_ext :
  forall f g : S -> R, (forall s : S, real_eq (f s) (g s)) -> real_eq (sumf f) (sumf g).
Hypothesis tmw_sum_add :
  forall f g : S -> R,
    real_eq (sumf (fun s => plus (f s) (g s))) (plus (sumf f) (sumf g)).
Hypothesis tmw_sum_linear :
  forall (a : R) (f : S -> R),
    real_eq (sumf (fun s => mult a (f s))) (mult a (sumf f)).
Hypothesis tmw_sum_pos :
  forall f : S -> R, (forall s : S, real_lt zero (f s)) -> real_lt zero (sumf f).
Hypothesis tmw_sum_le :
  forall f g : S -> R, (forall s : S, real_le (f s) (g s)) -> real_le (sumf f) (sumf g).
Hypothesis tmw_sum_zero_nonneg :
  forall f : S -> R,
    (forall s : S, real_le zero (f s)) -> real_eq (sumf f) zero ->
    forall s : S, real_eq (f s) zero.

Variable base_loss : S -> R.

(* ---- log bridge face (required by the discharge side; the same-shape
   slots exist on the requirement side) ---- *)
Hypothesis tmw_dist_log_inv_one_inv :
  forall (x : R) (Hx : real_lt zero x) (Hi : real_lt zero (inv_pos x Hx)),
    real_eq (log (inv_pos x Hx) Hi) (opp (log x Hx)).
Hypothesis tmw_dist_log_exp_neg :
  forall u : R, real_eq (log (exp_neg u) (exp_neg_pos u)) (opp u).
Hypothesis tmw_dist_log_le_linear :
  forall (x : R) (Hx : real_lt zero x), real_le (log x Hx) (req_minus x one).
Hypothesis tmw_dist_log_eq_linear :
  forall (x : R) (Hx : real_lt zero x),
    real_eq (log x Hx) (req_minus x one) -> real_eq x one.

(* ---- Z_temp interface (same position as the requirement's
   req_Z_temp_spec slot) ---- *)
Variable Z_temp : R -> R.
Hypothesis tmw_Z_temp_spec : forall (t : R) (Ht : real_lt zero t),
  real_eq (Z_temp t) (sumf (fun s => exp_neg (mult (inv_pos t Ht) (base_loss s)))).

(* Conditional form W2a: the requirement-slot statement with the extra
   premise kept explicitly (no strengthening). The proof consumes the
   supply theorem req_energy_exp_temp_mono at the witness instance by
   one exact step. *)
Theorem tmw_req_energy_exp_temp_mono_cond :
  forall (t1 t2 : R) (Ht1 : real_lt zero t1) (Ht2 : real_lt zero t2),
  real_lt t1 t2 ->
  real_lt zero (req_minus (inv_pos t1 Ht1) (inv_pos t2 Ht2)) ->
  real_le (@UpFirewallReq.fw_et S sumf tmw_sum_pos base_loss
                            Z_temp tmw_Z_temp_spec t1 Ht1)
     (@UpFirewallReq.fw_et S sumf tmw_sum_pos base_loss
                            Z_temp tmw_Z_temp_spec t2 Ht2).
Proof.
  intros t1 t2 Ht1 Ht2 Hlt Hbd.
  exact (UpReqTempEntropy.req_energy_exp_temp_mono           S sumf tmw_sum_ext tmw_sum_add tmw_sum_linear tmw_sum_pos           tmw_sum_le           base_loss           tmw_dist_log_inv_one_inv tmw_dist_log_exp_neg           tmw_dist_log_le_linear           Z_temp tmw_Z_temp_spec t1 t2 Ht1 Ht2 Hlt Hbd).
Qed.

(* Conditional form W2b: the requirement-slot statement with the extra
   premise kept explicitly (no strengthening); discharged by the supply
   theorem req_energy_exp_temp_strict_mono at the witness instance. *)
Theorem tmw_req_energy_exp_temp_strict_mono_cond :
  forall (t1 t2 : R) (Ht1 : real_lt zero t1) (Ht2 : real_lt zero t2),
  real_lt t1 t2 ->
  real_lt zero (req_relative_entropy S sumf
             (@UpFirewallReq.fw_bt S sumf tmw_sum_pos base_loss
                                   Z_temp tmw_Z_temp_spec t2 Ht2)
             (@UpFirewallReq.fw_bt S sumf tmw_sum_pos base_loss
                                   Z_temp tmw_Z_temp_spec t1 Ht1)
             (@UpFirewallReq.fw_bt_pos S sumf tmw_sum_pos base_loss
                                       Z_temp tmw_Z_temp_spec t2 Ht2)
             (@UpFirewallReq.fw_bt_pos S sumf tmw_sum_pos base_loss
                                       Z_temp tmw_Z_temp_spec t1 Ht1)) ->
  real_lt zero (req_minus (inv_pos t1 Ht1) (inv_pos t2 Ht2)) ->
  real_lt zero (req_minus (@UpFirewallReq.fw_et S sumf tmw_sum_pos
                                              base_loss Z_temp
                                              tmw_Z_temp_spec t2 Ht2)
                     (@UpFirewallReq.fw_et S sumf tmw_sum_pos
                                              base_loss Z_temp
                                              tmw_Z_temp_spec t1 Ht1)).
Proof.
  intros t1 t2 Ht1 Ht2 Hlt Hkl Hbd.
  exact (UpReqTempEntropy.req_energy_exp_temp_strict_mono           S sumf tmw_sum_ext tmw_sum_add tmw_sum_linear tmw_sum_pos           tmw_sum_le           base_loss           tmw_dist_log_inv_one_inv tmw_dist_log_exp_neg           tmw_dist_log_le_linear           Z_temp tmw_Z_temp_spec t1 t2 Ht1 Ht2 Hlt Hkl Hbd).
Qed.

(* Full-strength form W2a: from the single premise of the requirement's
   lt_minus_nonneg slot shape to the conditional-slot statement verbatim.
   The inversion of the inverse is supplied by req_inv_pos_lt_contra
   (proved inside the interface closure, axiom-free); the only remaining
   assumption is the pre-existing slot shape itself (no new claim). *)
Theorem tmw_req_energy_exp_temp_mono_full :
  (forall a b : R, real_lt a b -> real_lt zero (req_minus b a)) ->
  forall (t1 t2 : R) (Ht1 : real_lt zero t1) (Ht2 : real_lt zero t2),
  real_lt t1 t2 ->
  real_le (@UpFirewallReq.fw_et S sumf tmw_sum_pos base_loss
                            Z_temp tmw_Z_temp_spec t1 Ht1)
     (@UpFirewallReq.fw_et S sumf tmw_sum_pos base_loss
                            Z_temp tmw_Z_temp_spec t2 Ht2).
Proof.
  intros Hlmn t1 t2 Ht1 Ht2 Hlt.
  exact (UpReqTempEntropy.req_energy_exp_temp_mono           S sumf tmw_sum_ext tmw_sum_add tmw_sum_linear tmw_sum_pos           tmw_sum_le           base_loss           tmw_dist_log_inv_one_inv tmw_dist_log_exp_neg           tmw_dist_log_le_linear           Z_temp tmw_Z_temp_spec t1 t2 Ht1 Ht2 Hlt           (Hlmn (inv_pos t2 Ht2) (inv_pos t1 Ht1)                 (UpReqTempEntropy.req_inv_pos_lt_contra t1 t2 Ht1 Ht2 Hlt))).
Qed.

(* Full-strength form W2b: the same remaining slot shape implies the
   strict slot verbatim (its conclusion is the requirement's own
   assertion target at this position). *)
Theorem tmw_req_energy_exp_temp_strict_mono_full :
  (forall a b : R, real_lt a b -> real_lt zero (req_minus b a)) ->
  forall (t1 t2 : R) (Ht1 : real_lt zero t1) (Ht2 : real_lt zero t2),
  real_lt t1 t2 ->
  real_lt zero (req_relative_entropy S sumf
             (@UpFirewallReq.fw_bt S sumf tmw_sum_pos base_loss
                                   Z_temp tmw_Z_temp_spec t2 Ht2)
             (@UpFirewallReq.fw_bt S sumf tmw_sum_pos base_loss
                                   Z_temp tmw_Z_temp_spec t1 Ht1)
             (@UpFirewallReq.fw_bt_pos S sumf tmw_sum_pos base_loss
                                       Z_temp tmw_Z_temp_spec t2 Ht2)
             (@UpFirewallReq.fw_bt_pos S sumf tmw_sum_pos base_loss
                                       Z_temp tmw_Z_temp_spec t1 Ht1)) ->
  real_lt zero (req_minus (@UpFirewallReq.fw_et S sumf tmw_sum_pos
                                              base_loss Z_temp
                                              tmw_Z_temp_spec t2 Ht2)
                     (@UpFirewallReq.fw_et S sumf tmw_sum_pos
                                              base_loss Z_temp
                                              tmw_Z_temp_spec t1 Ht1)).
Proof.
  intros Hlmn t1 t2 Ht1 Ht2 Hlt Hkl.
  exact (UpReqTempEntropy.req_energy_exp_temp_strict_mono           S sumf tmw_sum_ext tmw_sum_add tmw_sum_linear tmw_sum_pos           tmw_sum_le           base_loss           tmw_dist_log_inv_one_inv tmw_dist_log_exp_neg           tmw_dist_log_le_linear           Z_temp tmw_Z_temp_spec t1 t2 Ht1 Ht2 Hlt Hkl           (Hlmn (inv_pos t2 Ht2) (inv_pos t1 Ht1)                 (UpReqTempEntropy.req_inv_pos_lt_contra t1 t2 Ht1 Ht2 Hlt))).
Qed.

(* Minimal demonstration item: the requirement's assertion line at this
   position, replicated verbatim - req_le_minus_nonneg applied to the two
   energy expectations through the full-strength form W2a. *)
Theorem tmw_le_minus_nonneg_fw_et :
  (forall a b : R, real_lt a b -> real_lt zero (req_minus b a)) ->
  forall (t1 t2 : R) (Ht1 : real_lt zero t1) (Ht2 : real_lt zero t2),
  real_lt t1 t2 ->
  real_le zero (req_minus (@UpFirewallReq.fw_et S sumf tmw_sum_pos
                                              base_loss Z_temp
                                              tmw_Z_temp_spec t2 Ht2)
                     (@UpFirewallReq.fw_et S sumf tmw_sum_pos
                                              base_loss Z_temp
                                              tmw_Z_temp_spec t1 Ht1)).
Proof.
  intros Hlmn t1 t2 Ht1 Ht2 Hlt.
  exact (req_le_minus_nonneg           (@UpFirewallReq.fw_et S sumf tmw_sum_pos base_loss                                 Z_temp tmw_Z_temp_spec t1 Ht1)           (@UpFirewallReq.fw_et S sumf tmw_sum_pos base_loss                                 Z_temp tmw_Z_temp_spec t2 Ht2)           (tmw_req_energy_exp_temp_mono_full Hlmn t1 t2 Ht1 Ht2 Hlt)).
Qed.

End TmwMonoW2.

(* ============ assumption audit (all five items) ============ *)
Print Assumptions tmw_req_energy_exp_temp_mono_cond.
Print Assumptions tmw_req_energy_exp_temp_strict_mono_cond.
Print Assumptions tmw_req_energy_exp_temp_mono_full.
Print Assumptions tmw_req_energy_exp_temp_strict_mono_full.
Print Assumptions tmw_le_minus_nonneg_fw_et.

Print Assumptions tmw_le_minus_nonneg_fw_et.
Print Assumptions tmw_req_energy_exp_temp_strict_mono_full.
Print Assumptions tmw_req_energy_exp_temp_mono_full.
Print Assumptions tmw_req_energy_exp_temp_strict_mono_cond.
Print Assumptions tmw_req_energy_exp_temp_mono_cond.
