(* ========================================================================== *)
(* Module   : G12_ZPosFam                                                     *)
(* Mission.  Partition-function positivity family on the Set carrier: over an *)
(*            enumerated state list the Boltzmann partition function          *)
(*            Z = sum_s exp(-beta * base_loss s) is strictly positive, the    *)
(*            only datum being that the enumeration is nonempty; the abstract *)
(*            form lifts to any Z equal (req) to such a finite sum, and the   *)
(*            same key discharges the alignment partition slots (Z_align_req  *)
(*            / req2_Z_align), the attention Z_thermo slots, the temperature  *)
(*            partition spec, the Gibbs premise-elimination family (the       *)
(*            partition-equality premise from pointwise mirror + sum ext),    *)
(*            and two downstream re-docks (log-pi-star, DPO loss at pi-star). *)
(* Dependencies. S01_BaseRing .. S15_TailFEPUp, UpReqSumD (sumd_sumf,         *)
(*            sumd_sum_pos, sumd_sum_ext, sumd_sum_linear), UpReqAlign,       *)
(*            UpReqAlign2, UpReqAttnIter, UpReqAttnGibbs, UpReqDpoLoss,       *)
(*            UpReqAlignRestA, CW220_Extensions (SetoidThermoCore); Stdlib List. *)
(* References. UpReqSumD (Not (l = nil) slot form); UpReqAlign (partition     *)
(*            condition); S10_KVQuantTrig (exp_neg_req_compat_setoid);        *)
(*            CW220_Extensions (SetoidThermoCore, req_attention_is_gibbs_temp). *)
(* Constructivity. All statements Set-carried: order/equality faces are the   *)
(*            interface fields lt/req (real_lt/real_eq of the constructive    *)
(*            Cauchy reals), witnesses in the decidable rational layer        *)
(*            (QltT/QeqT of S02_CauchyComplete); zero Prop statements, zero   *)
(*            axioms, zero admits; datum Not (enum = nil) per UpReqSumD. All  *)
(*            definitions transparent, every lemma closed with Defined (no    *)
(*            Qed: no pure-Prop bridge face); exact-only term assembly.       *)
(* Build. coqc -native-compiler no -q -Q <Set Live root> "" G12_ZPosFam.v     *)
(* ========================================================================== *)

From Stdlib Require Import List.
Import ListNotations.
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
Require Import UpReqSumD.
Require Import UpReqAlign.
Require Import UpReqAlign2.
Require Import UpReqAttnIter.
Require Import UpReqAttnGibbs.
Require Import UpReqDpoLoss.
Require Import UpReqAlignRestA.
Require Import CW220_Extensions.
Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* Section ZPosDischarge: positivity of the enumerated Boltzmann  *)
(* partition function and its temperature family.                *)
(* ============================================================ *)
Section ZPosDischarge.

Variable S : Set.
Variable enum : list S.
Variable base_loss : S -> Real.
Variable beta : Real.
Variable beta_pos : lt zero beta.

(* Per-term Boltzmann factor is strictly positive: the exponential is
   pointwise positive regardless of the exponent. *)
Lemma zposd_boltz_factor_pos : forall s : S,
  lt zero (exp_neg (mult (inv_pos beta beta_pos) (base_loss s))).
Proof.
  intro s. exact (exp_neg_pos (mult (inv_pos beta beta_pos) (base_loss s))).
Defined.

(* The concrete partition function: the enumerated finite sum of the
   Boltzmann factors. *)
Definition zposd_Z : Real :=
  sumd_sumf S enum
    (fun s : S => exp_neg (mult (inv_pos beta beta_pos) (base_loss s))).

(* Strict positivity of Z, with nonemptiness of the enumeration as the
   only datum. *)
Lemma zposd_Z_pos : Not (enum = nil) -> lt zero zposd_Z.
Proof.
  intro Hne.
  exact (sumd_sum_pos S enum
           (fun s : S => exp_neg (mult (inv_pos beta beta_pos) (base_loss s)))
           Hne
           (fun s : S => exp_neg_pos (mult (inv_pos beta beta_pos) (base_loss s)))).
Defined.

(* The partition condition holds definitionally for the concrete Z. *)
Definition zposd_partition :
  req zposd_Z
      (sumd_sumf S enum
         (fun s : S => exp_neg (mult (inv_pos beta beta_pos) (base_loss s)))) :=
  req_refl (sumd_sumf S enum
              (fun s : S => exp_neg (mult (inv_pos beta beta_pos) (base_loss s)))).

(* Abstract form: any Z equal to such a finite sum is strictly positive,
   transported along the equality by req_lt_compat. *)
Lemma zposd_Z_pos_of_partition : forall Z : Real,
  req Z (sumd_sumf S enum
           (fun s : S => exp_neg (mult (inv_pos beta beta_pos) (base_loss s)))) ->
  Not (enum = nil) -> lt zero Z.
Proof.
  intros Z Hcond Hne.
  exact (req_lt_compat zero zero
           (sumd_sumf S enum
              (fun s : S => exp_neg (mult (inv_pos beta beta_pos) (base_loss s))))
           Z
           (req_refl zero)
           (req_sym Z
              (sumd_sumf S enum
                 (fun s : S => exp_neg (mult (inv_pos beta beta_pos) (base_loss s))))
              Hcond)
           (sumd_sum_pos S enum
              (fun s : S => exp_neg (mult (inv_pos beta beta_pos) (base_loss s)))
              Hne
              (fun s : S => exp_neg_pos (mult (inv_pos beta beta_pos) (base_loss s))))).
Defined.

(* The Boltzmann distribution at inverse temperature beta. *)
Definition zposd_boltzmann_dist (Hne : Not (enum = nil)) (s : S) : Real :=
  mult (inv_pos zposd_Z (zposd_Z_pos Hne))
       (exp_neg (mult (inv_pos beta beta_pos) (base_loss s))).

Lemma zposd_boltzmann_dist_pos : forall (Hne : Not (enum = nil)) (s : S),
  lt zero (zposd_boltzmann_dist Hne s).
Proof.
  intros Hne s.
  exact (mult_positive (inv_pos zposd_Z (zposd_Z_pos Hne))
           (exp_neg (mult (inv_pos beta beta_pos) (base_loss s)))
           (inv_pos_pos zposd_Z (zposd_Z_pos Hne))
           (zposd_boltz_factor_pos s)).
Defined.

(* Temperature family: the partition function at temperature t. *)
Definition zposd_Z_temp (t : Real) (Ht : lt zero t) : Real :=
  sumd_sumf S enum
    (fun s : S => exp_neg (mult (inv_pos t Ht) (base_loss s))).

Lemma zposd_Z_temp_pos : forall (t : Real) (Ht : lt zero t),
  Not (enum = nil) -> lt zero (zposd_Z_temp t Ht).
Proof.
  intros t Ht Hne.
  exact (sumd_sum_pos S enum
           (fun s : S => exp_neg (mult (inv_pos t Ht) (base_loss s)))
           Hne
           (fun s : S => exp_neg_pos (mult (inv_pos t Ht) (base_loss s)))).
Defined.

(* The temperature partition condition holds definitionally. *)
Definition zposd_Z_temp_spec : forall (t : Real) (Ht : lt zero t),
  req (zposd_Z_temp t Ht)
      (sumd_sumf S enum
         (fun s : S => exp_neg (mult (inv_pos t Ht) (base_loss s)))) :=
  fun (t : Real) (Ht : lt zero t) =>
    req_refl (sumd_sumf S enum
                (fun s : S => exp_neg (mult (inv_pos t Ht) (base_loss s)))).

(* The Boltzmann distribution at temperature t. *)
Definition zposd_boltzmann_dist_temp (t : Real) (Ht : lt zero t)
           (Hne : Not (enum = nil)) (s : S) : Real :=
  mult (inv_pos (zposd_Z_temp t Ht) (zposd_Z_temp_pos t Ht Hne))
       (exp_neg (mult (inv_pos t Ht) (base_loss s))).

Lemma zposd_boltzmann_dist_temp_pos :
  forall (t : Real) (Ht : lt zero t) (Hne : Not (enum = nil)) (s : S),
  lt zero (zposd_boltzmann_dist_temp t Ht Hne s).
Proof.
  intros t Ht Hne s.
  exact (mult_positive (inv_pos (zposd_Z_temp t Ht) (zposd_Z_temp_pos t Ht Hne))
           (exp_neg (mult (inv_pos t Ht) (base_loss s)))
           (inv_pos_pos (zposd_Z_temp t Ht) (zposd_Z_temp_pos t Ht Hne))
           (exp_neg_pos (mult (inv_pos t Ht) (base_loss s)))).
Defined.

End ZPosDischarge.

(* ============================================================ *)
(* The alignment partition key: the Z_align_req / req2_Z_align    *)
(* slots discharged at the enumerated carrier.                   *)
(* ============================================================ *)

Lemma zpfinal_partition_cond :
  forall (S : Set) (enum : list S)
         (reward : S -> Real) (beta : Real) (beta_pos : lt zero beta)
         (pi_ref : S -> Real) (pi_ref_pos : forall s : S, lt zero (pi_ref s)),
  req (UpReqAlign.Z_align_req S (sumd_sumf S enum) reward beta beta_pos pi_ref)
      (sumd_sumf S enum
         (fun s : S => exp_neg (mult (inv_pos beta beta_pos)
                              (UpReqAlign.align_energy_req S reward beta pi_ref pi_ref_pos s)))).
Proof.
  intros S enum reward beta beta_pos pi_ref pi_ref_pos.
  exact (UpReqAlign.req_align_partition_condition S (sumd_sumf S enum)
           (sumd_sum_ext S enum)
           reward beta beta_pos pi_ref pi_ref_pos).
Defined.

Lemma zpfinal_Z_align_req_pos :
  forall (S : Set) (enum : list S)
         (reward : S -> Real) (beta : Real) (beta_pos : lt zero beta)
         (pi_ref : S -> Real) (pi_ref_pos : forall s : S, lt zero (pi_ref s))
         (Hne : Not (enum = nil)),
  lt zero (UpReqAlign.Z_align_req S (sumd_sumf S enum) reward beta beta_pos pi_ref).
Proof.
  intros S enum reward beta beta_pos pi_ref pi_ref_pos Hne.
  exact (zposd_Z_pos_of_partition S enum
           (UpReqAlign.align_energy_req S reward beta pi_ref pi_ref_pos)
           beta beta_pos
           (UpReqAlign.Z_align_req S (sumd_sumf S enum) reward beta beta_pos pi_ref)
           (zpfinal_partition_cond S enum reward beta beta_pos pi_ref pi_ref_pos)
           Hne).
Defined.

(* The req2 twin: its body is the same sum, so the key transports by
   conversion. *)
Lemma zpfinal_req2_Z_align_pos :
  forall (S : Set) (enum : list S)
         (reward : S -> Real) (beta : Real) (beta_pos : lt zero beta)
         (pi_ref : S -> Real) (pi_ref_pos : forall s : S, lt zero (pi_ref s))
         (Hne : Not (enum = nil)),
  lt zero (UpReqAlign2.req2_Z_align S (sumd_sumf S enum) reward beta beta_pos pi_ref).
Proof.
  intros S enum reward beta beta_pos pi_ref pi_ref_pos Hne.
  exact (zpfinal_Z_align_req_pos S enum reward beta beta_pos pi_ref pi_ref_pos Hne).
Defined.

(* Normalization of the closed-form optimal policy, at the enumerated
   carrier. *)
Lemma zpfinal_pi_star_normalized_enum :
  forall (S : Set) (enum : list S)
         (reward : S -> Real) (beta : Real) (beta_pos : lt zero beta)
         (pi_ref : S -> Real) (pi_ref_pos : forall s : S, lt zero (pi_ref s))
         (Hne : Not (enum = nil)),
  req (sumd_sumf S enum
         (UpReqAlign.pi_star_req S (sumd_sumf S enum)
            (fun f : S -> Real => sumd_sum_pos S enum f Hne)
            reward beta beta_pos pi_ref pi_ref_pos))
      one.
Proof.
  intros S enum reward beta beta_pos pi_ref pi_ref_pos Hne.
  exact (UpReqAlign.req_pi_star_normalized S (sumd_sumf S enum)
           (sumd_sum_linear S enum)
           (fun f : S -> Real => sumd_sum_pos S enum f Hne)
           reward beta beta_pos pi_ref pi_ref_pos).
Defined.

(* ============================================================ *)
(* Attention Z_thermo slots discharged at the enumerated carrier. *)
(* ============================================================ *)

Lemma slot_Z_thermo_setoid_enum :
  forall (S : Set) (enum : list S)
         (D : Real) (D_pos : lt zero D) (energy : S -> Real)
         (Hne : Not (enum = nil)),
  lt zero (CW220_Extensions.SetoidThermoCore.Z_thermo S (sumd_sumf S enum) D D_pos energy).
Proof.
  intros S enum D D_pos energy Hne.
  exact (zposd_Z_pos S enum energy D D_pos Hne).
Defined.

Lemma slot_Z_thermo_i_enum :
  forall (S : Set) (enum : list S)
         (D : Real) (D_pos : lt zero D) (energy : S -> Real)
         (Hne : Not (enum = nil)),
  lt zero (UpReqAttnIter.Z_thermo_i S (sumd_sumf S enum) D D_pos energy).
Proof.
  intros S enum D D_pos energy Hne.
  exact (sumd_sum_pos S enum
           (UpReqAttnIter.boltzmann_factor_i S D D_pos energy)
           Hne
           (fun s : S => exp_neg_pos (mult (inv_pos D D_pos) (energy s)))).
Defined.

Lemma slot_Z_thermo_r_enum :
  forall (S : Set) (enum : list S)
         (D : Real) (D_pos : lt zero D) (energy : S -> Real)
         (Hne : Not (enum = nil)),
  lt zero (UpReqAttnGibbs.Z_thermo_r S (sumd_sumf S enum) D D_pos energy).
Proof.
  intros S enum D D_pos energy Hne.
  exact (sumd_sum_pos S enum
           (UpReqAttnGibbs.boltzmann_factor_r S D D_pos energy)
           Hne
           (fun s : S => exp_neg_pos (mult (inv_pos D D_pos) (energy s)))).
Defined.

(* ============================================================ *)
(* Gibbs premise elimination: the partition-equality premise      *)
(* supplied by the pointwise mirror premise plus sum              *)
(* extensionality (an interface face any concrete sum satisfies). *)
(* ============================================================ *)

(* Congruence of exp_neg along req: a theorem of the S10 layer
   (exp_neg_req_compat_setoid), replacing the section premise of the
   Gibbs carrier. *)
Lemma zauto_exp_neg_req_compat :
  forall x y : Real, real_eq x y -> real_eq (exp_neg x) (exp_neg y).
Proof.
  intros x y H. exact (exp_neg_req_compat_setoid x y H).
Defined.

(* Pointwise mirror: inv T == inv D and energy == -z pointwise force
   the Boltzmann factor to equal the mirrored softmax term. *)
Lemma zauto_mirror_point_temp :
  forall (S : Set) (T : Real) (T_pos : lt zero T)
         (D : Real) (D_pos : lt zero D) (energy z : S -> Real),
  req (inv_pos T T_pos) (inv_pos D D_pos) ->
  (forall s : S, req (energy s) (opp (z s))) ->
  forall s : S,
  req (CW220_Extensions.SetoidThermoCore.boltzmann_factor S D D_pos energy s)
      (exp_neg (opp (mult (inv_pos T T_pos) (z s)))).
Proof.
  intros S T T_pos D D_pos energy z HD Henergy s.
  exact (zauto_exp_neg_req_compat (mult (inv_pos D D_pos) (energy s))
                                  (opp (mult (inv_pos T T_pos) (z s)))
          (req_trans (mult (inv_pos D D_pos) (energy s))
                     (opp (mult (inv_pos D D_pos) (z s)))
                     (opp (mult (inv_pos T T_pos) (z s)))
          (req_trans (mult (inv_pos D D_pos) (energy s))
                     (mult (inv_pos D D_pos) (opp (z s)))
                     (opp (mult (inv_pos D D_pos) (z s)))
              (req_mult_compat (inv_pos D D_pos) (inv_pos D D_pos)
                                (energy s) (opp (z s))
                                (req_refl (inv_pos D D_pos))
                                (Henergy s))
              (CW220_Extensions.SetoidThermoCore.req_mult_opp_l
                 (inv_pos D D_pos) (z s)))
          (req_opp_compat (mult (inv_pos D D_pos) (z s))
                          (mult (inv_pos T T_pos) (z s))
              (req_mult_compat (inv_pos D D_pos) (inv_pos T T_pos)
                                (z s) (z s)
                                (req_sym (inv_pos T T_pos) (inv_pos D D_pos) HD)
                                (req_refl (z s)))))).
Defined.

(* The Z_auto lemma: the two partitions are equal; the partition-equality
   premise of the Gibbs theorem no longer appears. *)
Lemma zauto_Z_eq_temp :
  forall (S : Set) (sumf : (S -> Real) -> Real)
         (sum_ext : forall f g : S -> Real,
            (forall s : S, real_eq (f s) (g s)) -> real_eq (sumf f) (sumf g))
         (T : Real) (T_pos : lt zero T)
         (D : Real) (D_pos : lt zero D) (energy z : S -> Real),
  req (inv_pos T T_pos) (inv_pos D D_pos) ->
  (forall s : S, req (energy s) (opp (z s))) ->
  req (CW220_Extensions.SetoidThermoCore.cwe_partition_function_temp S sumf T T_pos z)
      (CW220_Extensions.SetoidThermoCore.Z_thermo S sumf D D_pos energy).
Proof.
  intros S sumf sum_ext T T_pos D D_pos energy z HD Henergy.
  exact (sum_ext (fun s : S => exp_neg (opp (mult (inv_pos T T_pos) (z s))))
                 (fun s : S => exp_neg (mult (inv_pos D D_pos) (energy s)))
                 (fun s : S =>
                    req_sym (exp_neg (mult (inv_pos D D_pos) (energy s)))
                            (exp_neg (opp (mult (inv_pos T T_pos) (z s))))
                            (zauto_mirror_point_temp S T T_pos D D_pos energy z
                                                     HD Henergy s))).
Defined.

(* Premise-eliminated Gibbs theorem: same conclusion as the carrier
   theorem with its third premise supplied by zauto_Z_eq_temp. *)
Lemma zauto_attention_is_gibbs_temp_noZ :
  forall (S : Set) (sumf : (S -> Real) -> Real)
         (sum_ext : forall f g : S -> Real,
            (forall s : S, real_eq (f s) (g s)) -> real_eq (sumf f) (sumf g))
         (T : Real) (T_pos : lt zero T)
         (D : Real) (D_pos : lt zero D) (energy z : S -> Real)
         (partition_function_temp_pos :
            lt zero (CW220_Extensions.SetoidThermoCore.cwe_partition_function_temp
                       S sumf T T_pos z))
         (Z_thermo_pos :
            lt zero (CW220_Extensions.SetoidThermoCore.Z_thermo S sumf D D_pos energy)),
  req (inv_pos T T_pos) (inv_pos D D_pos) ->
  (forall s : S, req (energy s) (opp (z s))) ->
  forall s : S,
  req (CW220_Extensions.SetoidThermoCore.cwe_softmax_temp S sumf T T_pos z
         partition_function_temp_pos s)
      (CW220_Extensions.SetoidThermoCore.boltzmann_dist_attn S sumf D D_pos energy
         Z_thermo_pos s).
Proof.
  intros S sumf sum_ext T T_pos D D_pos energy z HpZ HzZ HD Henergy s.
  exact (CW220_Extensions.SetoidThermoCore.req_attention_is_gibbs_temp
           S sumf zauto_exp_neg_req_compat
           T T_pos D D_pos energy z HpZ HzZ HD Henergy
           (req_sym (CW220_Extensions.SetoidThermoCore.cwe_partition_function_temp
                       S sumf T T_pos z)
                    (CW220_Extensions.SetoidThermoCore.Z_thermo S sumf D D_pos energy)
                    (zauto_Z_eq_temp S sumf sum_ext T T_pos D D_pos energy z
                                     HD Henergy))
           s).
Defined.

(* The Gibbs theorem closed at the enumerated carrier: both positivity
   slots are discharged from the nonemptiness datum alone. *)
Lemma zauto_attention_gibbs_enum :
  forall (S : Set) (enum : list S) (Hne : Not (enum = nil))
         (T : Real) (T_pos : lt zero T)
         (D : Real) (D_pos : lt zero D) (energy z : S -> Real),
  req (inv_pos T T_pos) (inv_pos D D_pos) ->
  (forall s : S, req (energy s) (opp (z s))) ->
  forall s : S,
  req (CW220_Extensions.SetoidThermoCore.cwe_softmax_temp S (sumd_sumf S enum)
         T T_pos z
         (sumd_sum_pos S enum
            (fun s : S => exp_neg (opp (mult (inv_pos T T_pos) (z s))))
            Hne
            (fun s : S => exp_neg_pos (opp (mult (inv_pos T T_pos) (z s)))))
         s)
      (CW220_Extensions.SetoidThermoCore.boltzmann_dist_attn S (sumd_sumf S enum)
         D D_pos energy
         (zposd_Z_pos S enum energy D D_pos Hne)
         s).
Proof.
  intros S enum Hne T T_pos D D_pos energy z HD Henergy s.
  exact (CW220_Extensions.SetoidThermoCore.req_attention_is_gibbs_temp
           S (sumd_sumf S enum) zauto_exp_neg_req_compat
           T T_pos D D_pos energy z
           (sumd_sum_pos S enum
              (fun s : S => exp_neg (opp (mult (inv_pos T T_pos) (z s))))
              Hne
              (fun s : S => exp_neg_pos (opp (mult (inv_pos T T_pos) (z s)))))
           (zposd_Z_pos S enum energy D D_pos Hne)
           HD Henergy
           (req_sym (CW220_Extensions.SetoidThermoCore.cwe_partition_function_temp
                       S (sumd_sumf S enum) T T_pos z)
                    (CW220_Extensions.SetoidThermoCore.Z_thermo S (sumd_sumf S enum)
                       D D_pos energy)
                    (zauto_Z_eq_temp S (sumd_sumf S enum) (sumd_sum_ext S enum)
                                     T T_pos D D_pos energy z HD Henergy))
           s).
Defined.

(* ============================================================ *)
(* Id-layer twin: the mirror and Z_auto faces at the structural   *)
(* identity type, over the SumOver interface.                    *)
(* ============================================================ *)
Section ZAutoId.

Context {RI : RealInterface}.
Context {SS : StateSpace RI}.
Context {SO : SumOver RI SS}.

Let RId := @S01_BaseRing.R RI.
Let SI := @S01_BaseRing.S RI SS.
Let zeroI := @S01_BaseRing.zero RI.
Let oneI := @S01_BaseRing.one RI.
Let multI := @S01_BaseRing.mult RI.
Let oppI := @S01_BaseRing.opp RI.
Let ltI := @S01_BaseRing.lt RI.
Let inv_posI := @S01_BaseRing.inv_pos RI.
Let exp_negI := @S01_BaseRing.exp_neg RI.
Let sumI := @S01_BaseRing.sum_over_S RI SS SO.

Variable D : RId.
Variable D_pos : ltI zeroI D.
Variable energy : SI -> RId.
Variable z : SI -> RId.

Definition zauto_id_boltzmann_factor (s : SI) : RId :=
  exp_negI (multI (inv_posI D D_pos) (energy s)).

Definition zauto_id_Z_thermo : RId :=
  sumI zauto_id_boltzmann_factor.

Definition zauto_id_exp_pos (x : RId) : RId := exp_negI (oppI x).

Definition zauto_id_partition : RId :=
  sumI (fun s : SI => zauto_id_exp_pos (z s)).

Lemma zauto_id_mirror :
  Id (inv_posI D D_pos) oneI ->
  (forall s : SI, Id (energy s) (oppI (z s))) ->
  forall s : SI,
  Id (zauto_id_boltzmann_factor s) (zauto_id_exp_pos (z s)).
Proof.
  intros HD Henergy s.
  exact (id_cong (fun x : RId => exp_negI x)
           (id_trans
              (id_trans (id_cong (fun x : RId => multI x (energy s)) HD)
                        (id_trans (@S01_BaseRing.mult_comm RI oneI (energy s))
                                  (@S01_BaseRing.mult_one RI (energy s))))
              (Henergy s))).
Defined.

Lemma zauto_id_Z_eq :
  Id (inv_posI D D_pos) oneI ->
  (forall s : SI, Id (energy s) (oppI (z s))) ->
  Id zauto_id_partition zauto_id_Z_thermo.
Proof.
  intros HD Henergy.
  exact (@S01_BaseRing.sum_over_S_ext RI SS SO
           (fun s : SI => zauto_id_exp_pos (z s))
           zauto_id_boltzmann_factor
           (fun s : SI => id_sym (zauto_id_mirror HD Henergy s))).
Defined.

End ZAutoId.

(* ============================================================ *)
(* Downstream re-docks: the log-pi-star closed form and the DPO   *)
(* total-loss-at-star theorem, with Z_align_pos supplied by the   *)
(* enumerated key; the log compatibility bridges stay explicit    *)
(* (interface-gap faces, not discharged here).                    *)
(* ============================================================ *)

Lemma zpfinal_ralt_log_pi_star_enum :
  forall (S : Set) (enum : list S)
         (reward : S -> Real) (beta : Real) (beta_pos : lt zero beta)
         (pi_ref : S -> Real) (pi_ref_pos : forall s : S, lt zero (pi_ref s))
         (Hne : Not (enum = nil))
         (Hlog : forall (x y : Real) (Hx : lt zero x) (Hy : lt zero y),
                   req x y -> req (log x Hx) (log y Hy))
         (Hlie : forall x : Real, req (log_inv (exp_neg x) (exp_neg_pos x)) x),
  forall s : S,
  req (log (UpReqAlign.pi_star_req S (sumd_sumf S enum)
              (fun f : S -> Real => sumd_sum_pos S enum f Hne)
              reward beta beta_pos pi_ref pi_ref_pos s)
           (UpReqAlignRestA.ralt_pistar_pos S (sumd_sumf S enum)
              (fun f : S -> Real => sumd_sum_pos S enum f Hne)
              reward beta beta_pos pi_ref pi_ref_pos s))
      (plus (opp (log (UpReqAlign.Z_align_req S (sumd_sumf S enum)
                           reward beta beta_pos pi_ref)
                      (zpfinal_Z_align_req_pos S enum reward beta beta_pos
                         pi_ref pi_ref_pos Hne)))
            (plus (log (pi_ref s) (pi_ref_pos s))
                  (mult (inv_pos beta beta_pos) (reward s)))).
Proof.
  intros S enum reward beta beta_pos pi_ref pi_ref_pos Hne Hlog Hlie s.
  exact (UpReqAlignRestA.ralt_log_pi_star S (sumd_sumf S enum)
           (fun f : S -> Real => sumd_sum_pos S enum f Hne)
           reward beta beta_pos pi_ref pi_ref_pos
           (zpfinal_Z_align_req_pos S enum reward beta beta_pos pi_ref pi_ref_pos Hne)
           Hlog Hlie s).
Defined.

Lemma zpfinal_rdl_total_loss_at_star_enum :
  forall (S : Set) (enum : list S)
         (reward : S -> Real) (beta : Real) (beta_pos : lt zero beta)
         (pi_ref : S -> Real) (pi_ref_pos : forall s : S, lt zero (pi_ref s))
         (Hne : Not (enum = nil))
         (Hlog : forall (x y : Real) (Hx : lt zero x) (Hy : lt zero y),
                   req x y -> req (log x Hx) (log y Hy))
         (Hlie : forall x : Real, req (log_inv (exp_neg x) (exp_neg_pos x)) x)
         (Preference : Set) (pref_win pref_lose : Preference -> S)
         (pref_dataset : list Preference),
  req (UpReqDpoLoss.rdl_dpo_total_loss S beta pi_ref pi_ref_pos
         Preference pref_win pref_lose pref_dataset
         (UpReqDpoLoss.rdl_pistar S (sumd_sumf S enum)
            (fun f : S -> Real => sumd_sum_pos S enum f Hne)
            reward beta beta_pos pi_ref pi_ref_pos)
         (UpReqDpoLoss.rdl_pistar_pos S (sumd_sumf S enum)
            (fun f : S -> Real => sumd_sum_pos S enum f Hne)
            reward beta beta_pos pi_ref pi_ref_pos))
      (UpReqDpoLoss.rdl_dpo_total_loss_star S reward Preference
         pref_win pref_lose pref_dataset).
Proof.
  intros S enum reward beta beta_pos pi_ref pi_ref_pos Hne Hlog Hlie
         Preference pref_win pref_lose pref_dataset.
  exact (UpReqDpoLoss.rdl_dpo_total_loss_at_star S (sumd_sumf S enum)
           (fun f : S -> Real => sumd_sum_pos S enum f Hne)
           reward beta beta_pos pi_ref pi_ref_pos
           (zpfinal_Z_align_req_pos S enum reward beta beta_pos pi_ref pi_ref_pos Hne)
           Hlog Hlie Preference pref_win pref_lose pref_dataset).
Defined.

(* ============================================================ *)
(* Assumption audit: one line per item, all Closed.               *)
(* ============================================================ *)
Print Assumptions zposd_boltz_factor_pos.
Print Assumptions zposd_Z.
Print Assumptions zposd_Z_pos.
Print Assumptions zposd_partition.
Print Assumptions zposd_Z_pos_of_partition.
Print Assumptions zposd_boltzmann_dist.
Print Assumptions zposd_boltzmann_dist_pos.
Print Assumptions zposd_Z_temp.
Print Assumptions zposd_Z_temp_pos.
Print Assumptions zposd_Z_temp_spec.
Print Assumptions zposd_boltzmann_dist_temp.
Print Assumptions zposd_boltzmann_dist_temp_pos.
Print Assumptions zpfinal_partition_cond.
Print Assumptions zpfinal_Z_align_req_pos.
Print Assumptions zpfinal_req2_Z_align_pos.
Print Assumptions zpfinal_pi_star_normalized_enum.
Print Assumptions slot_Z_thermo_setoid_enum.
Print Assumptions slot_Z_thermo_i_enum.
Print Assumptions slot_Z_thermo_r_enum.
Print Assumptions zauto_exp_neg_req_compat.
Print Assumptions zauto_mirror_point_temp.
Print Assumptions zauto_Z_eq_temp.
Print Assumptions zauto_attention_is_gibbs_temp_noZ.
Print Assumptions zauto_attention_gibbs_enum.
Print Assumptions zauto_id_mirror.
Print Assumptions zauto_id_Z_eq.
Print Assumptions zpfinal_ralt_log_pi_star_enum.
Print Assumptions zpfinal_rdl_total_loss_at_star_enum.
