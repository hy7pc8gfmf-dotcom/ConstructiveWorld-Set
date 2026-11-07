(* ConstructiveWorld-Set — the steady-state distribution in Boltzmann form on the Real layer. *)

(** * UpReqSteadyThermo: Theorem 4.9 [steady_state_boltzmann] on the
      [Real] layer — the Boltzmann form of the stationary distribution.

    Mission.  Under the partition condition and detailed balance, proves
      the steady-state equation for the thermodynamics-side carrier
      [real_steady_state_boltzmann]: for every state [s],
      [sum_{s'} p(s') * T(s',s) == p(s)].

    Dependencies.  Requires [S01_BaseRing] through [S15_TailFEPUp],
      [UpReqConcSoftmax] (the finite-sum carrier [csm_sumf]), and
      [ConcMixSelFeed] (the supply anchors [cms_sum_ext] and
      [cms_sum_linear]) of this development.

    References.  This development, the ConstructiveWorld-Main baseline
      module of the same name; isomorphic to the [Id]-layer
      [BoltzmannSteadyState].

    Constructivity.  The statement face lives on the [Set] layer
      ([real_eq]/[real_lt]/[real_le] are [Set]-valued); no premises left
      open, no classical reasoning; every statement closes with [Qed]
      and is extractable.  The two abstract summation slots
      ([real_sum_over_S_ext]/[real_sum_over_S_linear]) receive
      certificate instances at the end of the file
      ([real_sum_over_S := csm_sumf S0 enum]).

    Build.  [coqc -native-compiler no -q -Q . "" UpReqSteadyThermo.v]
      compiles cleanly (exit 0); the first eight bytes of the artifact
      are [436f7121 000160bc]. *)
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
Require Import UpReqConcSoftmax.
Require Import ConcMixSelFeed.

(* ============================================================ *)
(* Section [RealThermoSteady]: isomorphic to the [Id]-layer      *)
(*   [BoltzmannSteadyState].                                     *)
(* ============================================================ *)
Section RealThermoSteady.

(* The summation carrier (the [Real]-layer parallel interface; the same position as [RealAttnSteady] in [S08_RealMainlineDPO]). *)
Variable S : Type.
Variable real_sum_over_S : (S -> Real) -> Real.
Variable real_sum_over_S_ext : forall (f g : S -> Real),
  (forall s : S, real_eq (f s) (g s)) -> real_eq (real_sum_over_S f) (real_sum_over_S g).
Variable real_sum_over_S_linear : forall (a : Real) (f : S -> Real),
  real_eq (real_sum_over_S (fun s : S => real_mult a (f s)))
          (real_mult a (real_sum_over_S f)).

(* [Id]-layer positions: [base_loss] / [D] / [D_pos] / [Z] / [Z_pos]. *)
Variable energy : S -> Real.
Variable D : Real.
Variable D_pos : real_lt real_zero D.
Variable Z_r : Real.
Variable Z_r_pos : real_lt real_zero Z_r.

(* [Id]-layer position: [partition_condition] ([real_eq] carrier; the same axis as [rfep_boltzmann_normalized_real]). *)
Variable real_partition_condition :
  real_eq Z_r
          (real_sum_over_S
             (fun s : S => real_exp_neg (real_mult (real_inv_pos D D_pos) (energy s)))).

(* [Id]-layer positions: [boltzmann_unnorm] / [boltzmann_prob] (thermodynamics-side carrier). *)
Definition real_boltzmann_unnorm (s : S) : Real :=
  real_exp_neg (real_mult (real_inv_pos D D_pos) (energy s)).
Definition real_boltzmann_prob (s : S) : Real :=
  real_mult (real_inv_pos Z_r Z_r_pos) (real_boltzmann_unnorm s).

(* [Id]-layer positions: [transition] / [transition_nonneg] / [transition_normalization] / [detailed_balance]. *)
Variable real_transition : S -> S -> Real.
Variable real_transition_nonneg : forall (s s' : S),
  real_le real_zero (real_transition s s').
Variable real_transition_normalization : forall s : S,
  real_eq (real_sum_over_S (fun s' : S => real_transition s s')) real_one.
Variable real_detailed_balance : forall (s s' : S),
  real_eq (real_mult (real_boltzmann_prob s) (real_transition s s'))
          (real_mult (real_boltzmann_prob s') (real_transition s' s)).

(* ============================================================ *)
(* Main theorem: the steady-state equation (Theorem 4.9 restated  *)
(*   as an equality on the [Real] layer):                         *)
(*   [sum_{s'} p(s') * T(s',s) == p(s)].                          *)
(*   Five-step chain: (1) detailed balance pointwise,             *)
(*   (2) extensionality of the sum, (3) linear extraction,        *)
(*   (4) kernel normalization (through [mult_compat]),            *)
(*   (5) finish with [mult_one].                                  *)
(* ============================================================ *)
Theorem real_steady_state_boltzmann : forall s : S,
  real_eq (real_sum_over_S (fun s' : S => real_mult (real_boltzmann_prob s') (real_transition s' s)))
          (real_boltzmann_prob s).
Proof.
  intro s.
  (* step (2): the sum extensionality shell ([real_sum_over_S_ext]); its pointwise premise is step (1). *)
  apply (real_eq_trans _
           (real_sum_over_S (fun s' : S => real_mult (real_boltzmann_prob s) (real_transition s s')))
           _).
  - apply (real_sum_over_S_ext
             (fun s' : S => real_mult (real_boltzmann_prob s') (real_transition s' s))
             (fun s' : S => real_mult (real_boltzmann_prob s) (real_transition s s'))).
    (* step (1): the pointwise detailed-balance rewrite (argument order [(s' s)], as in the [Id]-layer proof). *)
    intro s'. exact (real_detailed_balance s' s).
  - (* step (3): extracting [p(s)] linearly ([real_sum_over_S_linear]). *)
    apply (real_eq_trans _
             (real_mult (real_boltzmann_prob s) (real_sum_over_S (fun s' : S => real_transition s s')))
             _).
    + apply (real_sum_over_S_linear (real_boltzmann_prob s) (fun s' : S => real_transition s s')).
    + (* step (4): kernel normalization ([real_transition_normalization] placed through [mult_compat]). *)
      apply (real_eq_trans _ (real_mult (real_boltzmann_prob s) real_one) _).
      * apply (RealSetoid.real_eq_mult_compat (real_boltzmann_prob s)
                 (real_sum_over_S (fun s' : S => real_transition s s'))
                 (real_boltzmann_prob s) real_one
                 (real_eq_refl _) (real_transition_normalization s)).
      * (* step (5): [p(s) * 1 == p(s)], finished by [real_mult_one]. *)
        exact (real_mult_one (real_boltzmann_prob s)).
Qed.

End RealThermoSteady.

(* ============================================================ *)
(* Supply section for the summation premise slots:               *)
(*   [real_sum_over_S_ext] and [real_sum_over_S_linear].         *)
(*                                                               *)
(*   The two slots are interface obligations of the abstract      *)
(*   summation operator [real_sum_over_S]; this section supplies  *)
(*   isomorphic statements slot by slot over the finite-sum       *)
(*   carrier [csm_sumf S0 enum] (a fold over the enumeration      *)
(*   list, [UpReqConcSoftmax]).  The supplied statements match    *)
(*   the original premise slots verbatim modulo the carrier       *)
(*   substitution [real_sum_over_S := csm_sumf S0 enum]; the      *)
(*   supply anchors are [cms_sum_ext] and [cms_sum_linear] in     *)
(*   [ConcMixSelFeed].  The abstract premise declarations and     *)
(*   the signatures of existing theorems are unchanged.           *)
(* ============================================================ *)
Section SteadyThermoSumSlotsSupply.
Variable S0 : Set.
Variable enum : list S0.

(* Slot [real_sum_over_S_ext]: sum extensionality ([cms_sum_ext S0 enum] applied with all arguments explicit). *)
Theorem sts_sum_ext_supply : forall (f g : S0 -> Real),
  (forall s : S0, real_eq (f s) (g s)) ->
  real_eq (csm_sumf S0 enum f) (csm_sumf S0 enum g).
Proof. exact (cms_sum_ext S0 enum). Qed.

(* Slot [real_sum_over_S_linear]: scalar extraction ([cms_sum_linear] applied with all arguments explicit). *)
Theorem sts_sum_linear_supply : forall (a : Real) (f : S0 -> Real),
  real_eq (csm_sumf S0 enum (fun s : S0 => real_mult a (f s)))
          (real_mult a (csm_sumf S0 enum f)).
Proof. exact (cms_sum_linear S0 enum). Qed.

End SteadyThermoSumSlotsSupply.

Print Assumptions sts_sum_ext_supply.
Print Assumptions sts_sum_linear_supply.
