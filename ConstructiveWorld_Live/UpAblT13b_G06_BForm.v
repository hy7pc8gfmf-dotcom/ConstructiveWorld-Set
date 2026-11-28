(* ========================================================================= *)
(* Module   : G06 B-form discharge slots, seat-series carrier face          *)
(* Mission. Same-domain statement face over the Cauchy-setoid real carrier: *)
(*   the finite-list-sum algebra (extensionality, monotonicity, additivity, *)
(*   linearity), positivity of the weighted aggregate, truncated-mass and   *)
(*   full-partition positivity, then interface-level positive-partition     *)
(*   items for the eviction family, the two alignment cores, the two-state  *)
(*   partition pin, and the sigmoid migrate pair, each discharged through   *)
(*   its host module with the summation slot carried explicitly.            *)
(* Dependencies. S01_BaseRing .. S15_TailFEPUp; UpAuditBridge (uab_temp_sum, *)
(*   Z_full); G06_BForm (lebR_res_weight, rplb_sum_pos_discharged);         *)
(*   G13_EvictFam (evq family); UpReqAlign (Z_align_req); UpReqAlign2       *)
(*   (req2_Z_align); UpSigMigrate (sigm family); UpSigMigrate2 (bsum,       *)
(*   two_state_*, c_partition, Z_align_a_sum); Stdlib List.                 *)
(* References. S02_CauchyComplete (Real, real_lt as the per-eps sigT face); *)
(*   S08_RealMainlineDPO (real_list_sum family); the argument-less          *)
(*   interface adaptation of UpReqAlign.v / G13_EvictFam.v (R := Real,      *)
(*   req/lt/le := carrier relations, value fields via global instance).     *)
(* Constructivity. Every statement face is Set-carried: relations are       *)
(*   real_lt/real_le/real_eq (Set-valued; real_lt is the S02 per-eps sigT   *)
(*   face, witness eps and bounds as Set data, zero Prop components inside  *)
(*   the carrier), so every conclusion extracts; all items close with       *)
(*   Defined (transparent Set certificates; no item is sealed opaque, as    *)
(*   this piece carries no pure-Prop bridge face); proof-side constructive  *)
(*   Prop derivations (nonemptiness contradiction, eq-to-Id bridge) erase   *)
(*   under extraction; zero axiom, zero admission literals, no classical    *)
(*   logic.                                                                 *)
(* Build. rocq c -native-compiler no -q -Q <live tree> ""                   *)
(*   this piece file (green-verdict driver: exit 0, PA all closed).         *)
(* ========================================================================= *)
From Stdlib Require Import List.
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
Require Import UpAuditBridge.
Require Import G06_BForm.
Require Import G13_EvictFam.
Require Import UpReqAlign.
Require Import UpReqAlign2.
Require Import UpSigMigrate.
Require Import UpSigMigrate2.
Import RealInterfaceEnhancedMod.

(* Concrete-carrier binding (UpReqAlign.v / G13_EvictFam.v precedent): the  *)
(* carrier is the global Cauchy real [Real]; the relation faces [req]/[lt]  *)
(* are bound to the global Set-carrier relations; the value fields ([zero], *)
(* [plus], [mult], [exp_neg], [inv_pos], ...) resolve through the global    *)
(* interface instance.                                                      *)
Notation R := Real.
Notation req := real_eq.
Notation lt := real_lt.

(* ================ Section 1: the raw Real-carrier list-sum face ================ *)

(* Item 1: list-sum extensionality. *)
Theorem uabT13b_g06_ros_ext :
  forall (S : Type) (l : list S) (f g : S -> Real),
    (forall s : S, real_eq (f s) (g s)) ->
    real_eq (real_list_sum S f l) (real_list_sum S g l).
Proof.
  intros S l f g H.
  induction l as [| w rest IH]; simpl.
  - apply real_eq_refl.
  - apply (RealSetoid.real_eq_plus_compat (f w) (real_list_sum S f rest)
             (g w) (real_list_sum S g rest)).
    + exact (H w).
    + exact IH.
Defined.

(* Item 2: list-sum monotonicity. *)
Theorem uabT13b_g06_ros_le :
  forall (S : Type) (l : list S) (f g : S -> Real),
    (forall s : S, real_le (f s) (g s)) ->
    real_le (real_list_sum S f l) (real_list_sum S g l).
Proof.
  intros S l f g H.
  induction l as [| w rest IH]; simpl.
  - apply real_le_refl.
  - apply (real_le_plus_compat (f w) (g w) (real_list_sum S f rest)
             (real_list_sum S g rest)).
    + exact (H w).
    + exact IH.
Defined.

(* Item 3: additivity of the list sum. *)
Theorem uabT13b_g06_ros_add :
  forall (S : Type) (l : list S) (f g : S -> Real),
    real_eq (real_list_sum S (fun s : S => real_plus (f s) (g s)) l)
            (real_plus (real_list_sum S f l) (real_list_sum S g l)).
Proof.
  intros S l f g.
  induction l as [| w rest IH]; simpl.
  - apply (real_eq_sym (real_plus real_zero real_zero) real_zero).
    apply (real_plus_zero real_zero).
  - apply (real_eq_trans _
             (real_plus (real_plus (f w) (g w))
                        (real_plus (real_list_sum S f rest)
                                   (real_list_sum S g rest))) _).
    + apply (RealSetoid.real_eq_plus_compat (real_plus (f w) (g w))
               (real_list_sum S (fun w0 : S => real_plus (f w0) (g w0)) rest)
               (real_plus (f w) (g w))
               (real_plus (real_list_sum S f rest) (real_list_sum S g rest))).
      * apply real_eq_refl.
      * exact IH.
    + apply (real_plus_swap_mid (f w) (g w) (real_list_sum S f rest)
               (real_list_sum S g rest)).
Defined.

(* Item 4: linearity of the list sum. *)
Theorem uabT13b_g06_ros_linear :
  forall (S : Type) (l : list S) (a : Real) (f : S -> Real),
    real_eq (real_list_sum S (fun s : S => real_mult a (f s)) l)
            (real_mult a (real_list_sum S f l)).
Proof.
  intros S l a f.
  induction l as [| w rest IH]; simpl.
  - apply (real_eq_sym (real_mult a real_zero) real_zero).
    apply (real_mult_zero a).
  - apply (real_eq_trans _
             (real_plus (real_mult a (f w))
                        (real_mult a (real_list_sum S f rest))) _).
    + apply (RealSetoid.real_eq_plus_compat (real_mult a (f w))
               (real_list_sum S (fun w0 : S => real_mult a (f w0)) rest)
               (real_mult a (f w))
               (real_mult a (real_list_sum S f rest))).
      * apply real_eq_refl.
      * exact IH.
    + apply (real_eq_sym (real_mult a (real_plus (f w) (real_list_sum S f rest)))
               (real_plus (real_mult a (f w)) (real_mult a (real_list_sum S f rest)))).
      apply (real_distrib a (f w) (real_list_sum S f rest)).
Defined.

(* Item 5: positivity of the weighted aggregate; the vocabulary nonemptiness *)
(* premise is carried at the Set level (Not over the Set-level Id).          *)
Theorem uabT13b_g06_lebR_weight_pos :
  forall (X : Set) (vocab : list X), Not (Id vocab nil) ->
    real_lt real_zero
      (lebR_res_weight X (fun f : X -> Real => real_list_sum X f vocab)
                        (fun _ : X => real_one) (fun _ : X => real_one)).
Proof.
  intros X vocab Hne.
  unfold lebR_res_weight.
  apply (rplb_sum_pos_discharged X
           (fun s : X => real_mult real_one real_one) vocab Hne).
  intro s.
  exact (real_mult_positive real_one real_one real_lt_zero_one real_lt_zero_one).
Defined.

(* Item 6: truncated-mass positivity; every token is kept by the constant    *)
(* decidable keep face, so the kept sum is the plain list sum.               *)
Theorem uabT13b_g06_uabtemp_sum_pos :
  forall (Token : Set) (vocab : list Token) (rtf : Token -> Real),
    (forall w : Token, real_lt real_zero (rtf w)) -> Not (Id vocab nil) ->
    forall prefix : list Token,
      real_lt real_zero
        (@uab_temp_sum Token vocab rtf
             (fun (_ : list Token) (_ : Token) => unit)
             (fun (_ : list Token) (_ : Token) => inl tt : Or unit (Not unit))
             prefix).
Proof.
  intros Token vocab rtf Hf Hne prefix.
  assert (Hnp : vocab <> nil).
  { intro Hc. destruct (Hne (RealSetoid.eq_Id vocab nil Hc)). }
  exact (real_list_sum_pos Token rtf vocab Hf Hnp).
Defined.

(* Item 7: full-partition positivity; the nonemptiness premise is consumed   *)
(* on the empty branch only.                                                 *)
Theorem uabT13b_g06_Zfull_pos :
  forall (Token : Set) (vocab : list Token) (rtf : Token -> Real),
    (forall w : Token, real_lt real_zero (rtf w)) -> Not (Id vocab nil) ->
    real_lt real_zero (Z_full Token vocab rtf).
Proof.
  intros Token vocab rtf Hf Hne.
  unfold Z_full.
  revert Hne.
  induction vocab as [| w rest IH]; simpl; intros Hne.
  - destruct (Hne id_refl).
  - destruct rest as [| w' rest'].
    + apply (RealSetoid.real_lt_id_r real_zero (rtf w) (real_plus (rtf w) real_zero)).
      * apply (real_eq_sym (real_plus (rtf w) real_zero) (rtf w)).
        apply (real_plus_zero (rtf w)).
      * exact (Hf w).
    + apply (RealSetoid.real_lt_id_l real_zero (real_plus real_zero real_zero)
               (real_plus (rtf w) (real_list_sum Token rtf (w' :: rest')))).
      * apply (real_eq_sym (real_plus real_zero real_zero) real_zero).
        apply (real_plus_zero real_zero).
      * apply (real_lt_plus_compat real_zero (rtf w) real_zero
                 (real_list_sum Token rtf (w' :: rest'))).
        -- exact (Hf w).
        -- apply IH. intro Hc. inversion Hc.
Defined.

(* ================ Section 2: the eviction family face (G13_EvictFam) ================ *)

(* Item 1: the thermodynamic partition sum is positive; pointwise positivity *)
(* is fed through the summation slot.                                        *)
Theorem uabT13b_evq_Zthermo_pos :
  forall (S : Set) (sumf : (S -> R) -> R)
         (Hpos : forall f : S -> R, (forall s : S, lt zero (f s)) -> lt zero (sumf f))
         (D : R) (D_pos : lt zero D) (energy : S -> R),
    lt zero (@evq_Z_thermo S sumf D D_pos energy).
Proof.
  intros S sumf Hpos D D_pos energy.
  unfold evq_Z_thermo, evq_boltzmann_factor.
  apply Hpos.
  intros s.
  exact (exp_neg_pos (mult (inv_pos D D_pos) (energy s))).
Defined.

(* Item 2: the evicted partition is positive; every item is kept by the      *)
(* constant decidable keep face, so the pointwise term is the plain          *)
(* Boltzmann factor.                                                         *)
Theorem uabT13b_evq_evicted_partition_pos :
  forall (S : Set) (sumf : (S -> R) -> R)
         (Hpos : forall f : S -> R, (forall s : S, lt zero (f s)) -> lt zero (sumf f))
         (D : R) (D_pos : lt zero D) (energy : S -> R),
    lt zero (@evq_evicted_partition S sumf D D_pos energy
               (fun (_ : S) => unit)
               (fun (_ : S) => inl tt : Or unit (Not unit))).
Proof.
  intros S sumf Hpos D D_pos energy.
  unfold evq_evicted_partition, evq_boltzmann_factor.
  apply Hpos.
  intros s.
  exact (exp_neg_pos (mult (inv_pos D D_pos) (energy s))).
Defined.

(* ================ Section 3: the alignment core face (UpReqAlign) ================ *)

(* Item 1: the alignment partition function is positive; the pointwise chain *)
(* is pi_ref positivity times exp positivity.                                *)
Theorem uabT13b_align_Zalign_pos :
  forall (S : Set) (sumf : (S -> R) -> R)
         (Hpos : forall f : S -> R, (forall s : S, lt zero (f s)) -> lt zero (sumf f))
         (reward : S -> R) (beta : R) (beta_pos : lt zero beta)
         (pi_ref : S -> R) (Hpi : forall s : S, lt zero (pi_ref s)),
    lt zero (@Z_align_req S sumf reward beta beta_pos pi_ref).
Proof.
  intros S sumf Hpos reward beta beta_pos pi_ref Hpi.
  unfold Z_align_req.
  apply Hpos. intros s.
  exact (mult_positive (pi_ref s)
           (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))
           (Hpi s) (exp_neg_pos _)).
Defined.

(* ================ Section 4: the alignment-2 core face (UpReqAlign2) ================ *)

(* Item 1: the same chain for the second alignment core. *)
Theorem uabT13b_align2_Zalign_pos :
  forall (S : Set) (sumf : (S -> R) -> R)
         (Hpos : forall f : S -> R, (forall s : S, lt zero (f s)) -> lt zero (sumf f))
         (reward : S -> R) (beta : R) (beta_pos : lt zero beta)
         (pi_ref : S -> R) (Hpi : forall s : S, lt zero (pi_ref s)),
    lt zero (@req2_Z_align S sumf reward beta beta_pos pi_ref).
Proof.
  intros S sumf Hpos reward beta beta_pos pi_ref Hpi.
  unfold req2_Z_align.
  apply Hpos. intros s.
  exact (mult_positive (pi_ref s)
           (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))
           (Hpi s) (exp_neg_pos _)).
Defined.

(* ================ Section 5: the alignment-rest face (UpReqAlign support) ================ *)

(* Item 1: the same chain for the rest-alignment statement family. *)
Theorem uabT13b_ralt_Zalign_pos :
  forall (S : Set) (sumf : (S -> R) -> R)
         (Hpos : forall f : S -> R, (forall s : S, lt zero (f s)) -> lt zero (sumf f))
         (reward : S -> R) (beta : R) (beta_pos : lt zero beta)
         (pi_ref : S -> R) (Hpi : forall s : S, lt zero (pi_ref s)),
    lt zero (@Z_align_req S sumf reward beta beta_pos pi_ref).
Proof.
  intros S sumf Hpos reward beta beta_pos pi_ref Hpi.
  unfold Z_align_req.
  apply Hpos. intros s.
  exact (mult_positive (pi_ref s)
           (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))
           (Hpi s) (exp_neg_pos _)).
Defined.

(* ================ Section 6: the two-state partition pin (UpSigMigrate2) ================ *)

(* Item 1: concrete instance assembly; the partition condition resolves to   *)
(* the two-state instance lemma (transparent instance algebra).              *)
Theorem uabT13b_dist_partition_cond :
  req two_state_Z
      (bsum (fun s : bool =>
               exp_neg (mult (inv_pos real_one real_lt_zero_one)
                             (two_state_loss s)))).
Proof.
  exact c_partition.
Defined.

(* ================ Section 7: the sigmoid migrate face (UpSigMigrate) ================ *)

(* Item 1: partition-condition migration to positivity of the partition      *)
(* value, through the lt_id_r read face of the interface.                    *)
Theorem uabT13b_sigm_Zpos :
  forall (S : Set) (sumf : (S -> R) -> R)
         (Hpos : forall f : S -> R, (forall s : S, lt zero (f s)) -> lt zero (sumf f))
         (base_loss : S -> R) (D : R) (D_pos : lt zero D) (Z : R),
    req Z (sumf (fun s : S => exp_neg (mult (inv_pos D D_pos) (base_loss s)))) ->
    lt zero Z.
Proof.
  intros S sumf Hpos base_loss D D_pos Z Hpc.
  apply (lt_id_r zero
           (sumf (fun s : S => exp_neg (mult (inv_pos D D_pos) (base_loss s)))) Z).
  - apply req_sym. exact Hpc.
  - apply Hpos. intros s.
    exact (exp_neg_pos (mult (inv_pos D D_pos) (base_loss s))).
Defined.

(* Item 2: the thermodynamic partition sum is positive. *)
Theorem uabT13b_sigm_Zthermo_pos :
  forall (S : Set) (sumf : (S -> R) -> R)
         (Hpos : forall f : S -> R, (forall s : S, lt zero (f s)) -> lt zero (sumf f))
         (D : R) (D_pos : lt zero D) (energy : S -> R),
    lt zero (@sigm_Z_thermo S sumf D D_pos energy).
Proof.
  intros S sumf Hpos D D_pos energy.
  unfold sigm_Z_thermo, sigm_boltzmann_factor.
  apply Hpos.
  intros s.
  exact (exp_neg_pos (mult (inv_pos D D_pos) (energy s))).
Defined.

(* Item 3: concrete two-state instance supply (the Real carrier face,        *)
(* resolved through the global instance).                                    *)
Theorem uabT13b_sigm_partition_cond :
  req two_state_Z
      (bsum (fun s : bool =>
               exp_neg (mult (inv_pos real_one real_lt_zero_one)
                             (two_state_loss s)))).
Proof.
  exact c_partition.
Defined.

(* ================ Section 8: the sigmoid migrate-2 face (UpSigMigrate2) ================ *)

(* Item 1: partition-condition migration to positivity (second migrate core). *)
Theorem uabT13b_sigm2_Zpos :
  forall (S : Set) (sumf : (S -> R) -> R)
         (Hpos : forall f : S -> R, (forall s : S, lt zero (f s)) -> lt zero (sumf f))
         (base_loss : S -> R) (D : R) (D_pos : lt zero D) (Z : R),
    req Z (sumf (fun s : S => exp_neg (mult (inv_pos D D_pos) (base_loss s)))) ->
    lt zero Z.
Proof.
  intros S sumf Hpos base_loss D D_pos Z Hpc.
  apply (lt_id_r zero
           (sumf (fun s : S => exp_neg (mult (inv_pos D D_pos) (base_loss s)))) Z).
  - apply req_sym. exact Hpc.
  - apply Hpos. intros s.
    exact (exp_neg_pos (mult (inv_pos D D_pos) (base_loss s))).
Defined.

(* Item 2: the align-a partition sum is positive. *)
Theorem uabT13b_sigm2_Zalign_a_pos :
  forall (S : Set) (sumf : (S -> R) -> R)
         (Hpos : forall f : S -> R, (forall s : S, lt zero (f s)) -> lt zero (sumf f))
         (reward : S -> R) (beta : R) (beta_pos : lt zero beta)
         (pi_ref : S -> R) (Hpi : forall s : S, lt zero (pi_ref s)),
    lt zero (@Z_align_a_sum S sumf reward beta beta_pos pi_ref).
Proof.
  intros S sumf Hpos reward beta beta_pos pi_ref Hpi.
  unfold Z_align_a_sum.
  apply Hpos. intros s.
  exact (mult_positive (pi_ref s)
           (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))
           (Hpi s) (exp_neg_pos _)).
Defined.

(* ================ Tail: per-item assumption audit ================ *)

Print Assumptions uabT13b_g06_ros_ext.
Print Assumptions uabT13b_g06_ros_le.
Print Assumptions uabT13b_g06_ros_add.
Print Assumptions uabT13b_g06_ros_linear.
Print Assumptions uabT13b_g06_lebR_weight_pos.
Print Assumptions uabT13b_g06_uabtemp_sum_pos.
Print Assumptions uabT13b_g06_Zfull_pos.
Print Assumptions uabT13b_evq_Zthermo_pos.
Print Assumptions uabT13b_evq_evicted_partition_pos.
Print Assumptions uabT13b_align_Zalign_pos.
Print Assumptions uabT13b_align2_Zalign_pos.
Print Assumptions uabT13b_ralt_Zalign_pos.
Print Assumptions uabT13b_dist_partition_cond.
Print Assumptions uabT13b_sigm_Zpos.
Print Assumptions uabT13b_sigm_Zthermo_pos.
Print Assumptions uabT13b_sigm_partition_cond.
Print Assumptions uabT13b_sigm2_Zpos.
Print Assumptions uabT13b_sigm2_Zalign_a_pos.
