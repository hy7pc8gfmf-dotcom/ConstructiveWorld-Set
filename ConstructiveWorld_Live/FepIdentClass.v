(* ========================================================================= *)
(* Module   : FepIdentClass                                                  *)
(* Mission. The three identification conditions of the constructive          *)
(*   free-energy variational principle -- temperature matching, energy as   *)
(*   negative logits, partition-function matching -- as named fields of     *)
(*   Class FepIdentification on the concrete Cauchy Real carrier; the       *)
(*   field-level softmax/Boltzmann constructions; the consumer theorem      *)
(*   fic_attention_is_gibbs_temp (fields imply softmax = Boltzmann, given   *)
(*   exp compatibility); the instance FepIdentificationReal; and the        *)
(*   identity-face pieces fic_attention_is_gibbs_temp_id (the landed S06    *)
(*   statement) and fic_attention_is_gibbs_temp_via_id (data yields the     *)
(*   object, projections the conclusion).                                  *)
(* Dependencies. S01_BaseRing (Id, RealInterfaceEnhanced, StateSpace,       *)
(*   SumOver); S02_CauchyComplete (Real, real_eq/real_lt); S03_QExp        *)
(*   (real_inv_pos); S06_DiffSamplingGibbs (attention_is_gibbs_temp,       *)
(*   softmax_temp, boltzmann_dist_attn, Z_thermo,                         *)
(*   partition_function_temp); S07_RealSetoidExpLog (real_exp_neg,         *)
(*   cauchy_real_exp_wd, real_inv_pos_ext, real_plus_positive,             *)
(*   real_lt_zero_one, and the RealSetoid-module twins real_lt_id_l,       *)
(*   real_eq_plus_compat, real_eq_mult_compat, real_eq_opp_compat).       *)
(* References. The constructive free-energy variational principle note,     *)
(*   Sections 6.5 and 10.2; the AttentionGibbsBridge section of S06.        *)
(* Constructivity. All statement faces are Set-valued: real_eq/real_lt      *)
(*   (each Real -> Real -> Set, the landed eps-step mirror form with QltT   *)
(*   embedded in sigT, consumed as given) and the Set-level inductive Id;   *)
(*   zero Prop statements, zero axioms, zero admits; nothing is closed      *)
(*   opaquely: every definition and theorem ends in Defined; the transport  *)
(*   fic_id_to_req is the constructive match on id_refl, no converse.      *)
(* Build. coqc -native-compiler no -q -Q <deps root> "" FepIdentClass.v    *)
(* ========================================================================= *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.

(* ===================================================================== *)
(* A. The named identification interface (three fields + named premises)  *)
(* ===================================================================== *)

Class FepIdentification : Type := {
  fic_S : Set;
  fic_sumf : (fic_S -> Real) -> Real;
  fic_sum_pos :
    forall f : fic_S -> Real,
      (forall s : fic_S, real_lt real_zero (f s)) -> real_lt real_zero (fic_sumf f);
  fic_T : Real;
  fic_T_pos : real_lt real_zero fic_T;
  fic_D : Real;
  fic_D_pos : real_lt real_zero fic_D;
  fic_z : fic_S -> Real;
  fic_energy : fic_S -> Real;
  fic_Z_thermo : Real;
  fic_Z_thermo_pos : real_lt real_zero fic_Z_thermo;
  (* identification 1: temperature matching, inv T == inv D *)
  fic_temp_match : real_eq (real_inv_pos fic_T fic_T_pos) (real_inv_pos fic_D fic_D_pos);
  (* identification 2: the energy is the negative logits *)
  fic_energy_neg : forall s : fic_S, real_eq (fic_energy s) (real_opp (fic_z s));
  (* identification 3: the thermodynamic partition matches the temperature
     softmax partition (the right side = exp of minus invT times logits) *)
  fic_partition_match :
    real_eq fic_Z_thermo
      (fic_sumf (fun s : fic_S =>
        real_exp_neg (real_opp (real_mult (real_inv_pos fic_T fic_T_pos) (fic_z s)))))
}.

(* ===================================================================== *)
(* B. Both constructions at the interface, and the consumer theorem       *)
(* ===================================================================== *)

(* helper: a * (-x) == -(a * x), a seven-step ring-law term (the Setoid
   Enhanced interface has no opp-mult field; built from distrib,
   mult_zero, plus_opp, assoc, comm and plus_zero) *)
Definition fic_opp_mult_r : forall a x : Real,
  real_eq (real_mult a (real_opp x)) (real_opp (real_mult a x)).
Proof.
  intros a x.
  assert (Huv : real_eq (real_plus (real_mult a x) (real_mult a (real_opp x))) real_zero).
  { exact (real_eq_trans (real_plus (real_mult a x) (real_mult a (real_opp x)))
             (real_mult a (real_plus x (real_opp x))) real_zero
             (real_eq_sym _ _ (real_distrib a x (real_opp x)))
             (real_eq_trans (real_mult a (real_plus x (real_opp x)))
                (real_mult a real_zero) real_zero
                (RealSetoid.real_eq_mult_compat a (real_plus x (real_opp x)) a real_zero
                   (real_eq_refl a) (real_plus_opp x))
                (real_mult_zero a))). }
  assert (Hstep1 : real_eq (real_mult a (real_opp x))
                     (real_plus (real_mult a (real_opp x)) real_zero)).
  { exact (real_eq_sym _ _ (real_plus_zero (real_mult a (real_opp x)))). }
  assert (Hstep2 : real_eq (real_plus (real_mult a (real_opp x)) real_zero)
                     (real_plus (real_mult a (real_opp x))
                                (real_plus (real_mult a x) (real_opp (real_mult a x))))).
  { exact (RealSetoid.real_eq_plus_compat (real_mult a (real_opp x)) real_zero
             (real_mult a (real_opp x)) (real_plus (real_mult a x) (real_opp (real_mult a x)))
             (real_eq_refl (real_mult a (real_opp x)))
             (real_eq_sym (real_plus (real_mult a x) (real_opp (real_mult a x))) real_zero
                (real_plus_opp (real_mult a x)))). }
  assert (Hstep3 : real_eq (real_plus (real_mult a (real_opp x))
                                      (real_plus (real_mult a x) (real_opp (real_mult a x))))
                     (real_plus real_zero (real_opp (real_mult a x)))).
  { exact (real_eq_trans
             (real_plus (real_mult a (real_opp x))
                        (real_plus (real_mult a x) (real_opp (real_mult a x))))
             (real_plus (real_plus (real_mult a (real_opp x)) (real_mult a x))
                        (real_opp (real_mult a x)))
             (real_plus real_zero (real_opp (real_mult a x)))
             (real_plus_assoc (real_mult a (real_opp x)) (real_mult a x)
                (real_opp (real_mult a x)))
             (real_eq_trans (real_plus (real_plus (real_mult a (real_opp x)) (real_mult a x))
                                       (real_opp (real_mult a x)))
                (real_plus (real_plus (real_mult a x) (real_mult a (real_opp x)))
                           (real_opp (real_mult a x)))
                (real_plus real_zero (real_opp (real_mult a x)))
                (RealSetoid.real_eq_plus_compat (real_plus (real_mult a (real_opp x)) (real_mult a x))
                   (real_opp (real_mult a x))
                   (real_plus (real_mult a x) (real_mult a (real_opp x))) (real_opp (real_mult a x))
                   (real_plus_comm (real_mult a (real_opp x)) (real_mult a x))
                   (real_eq_refl (real_opp (real_mult a x))))
                (RealSetoid.real_eq_plus_compat (real_plus (real_mult a x) (real_mult a (real_opp x)))
                   (real_opp (real_mult a x)) real_zero (real_opp (real_mult a x))
                   Huv (real_eq_refl (real_opp (real_mult a x)))))). }
  assert (Hstep4 : real_eq (real_plus real_zero (real_opp (real_mult a x)))
                     (real_opp (real_mult a x))).
  { exact (real_eq_trans (real_plus real_zero (real_opp (real_mult a x)))
             (real_plus (real_opp (real_mult a x)) real_zero) (real_opp (real_mult a x))
             (real_plus_comm real_zero (real_opp (real_mult a x)))
             (real_plus_zero (real_opp (real_mult a x)))). }
  exact (real_eq_trans (real_mult a (real_opp x))
           (real_plus (real_mult a (real_opp x)) real_zero) (real_opp (real_mult a x))
           Hstep1
           (real_eq_trans (real_plus (real_mult a (real_opp x)) real_zero)
              (real_plus (real_mult a (real_opp x))
                         (real_plus (real_mult a x) (real_opp (real_mult a x))))
              (real_opp (real_mult a x)) Hstep2
              (real_eq_trans (real_plus (real_mult a (real_opp x))
                                        (real_plus (real_mult a x) (real_opp (real_mult a x))))
                 (real_plus real_zero (real_opp (real_mult a x)))
                 (real_opp (real_mult a x)) Hstep3 Hstep4))).
Defined.

(* explicit type-annotated intermediates for the record-field consumption
   positions (positive inverses of the named fields); every class-field
   projection is applied with an explicit @ against the named instance *)
Definition fic_inv_T (I : FepIdentification) : Real :=
  real_inv_pos (@fic_T I) (@fic_T_pos I).

Definition fic_inv_D (I : FepIdentification) : Real :=
  real_inv_pos (@fic_D I) (@fic_D_pos I).

Definition fic_inv_Z (I : FepIdentification) : Real :=
  real_inv_pos (@fic_Z_thermo I) (@fic_Z_thermo_pos I).

(* side A (paper Section 6.3): the temperature softmax partition *)
Definition fic_partition_function_temp (I : FepIdentification) : Real :=
  @fic_sumf I (fun s : @fic_S I =>
    real_exp_neg (real_opp (real_mult (fic_inv_T I) (@fic_z I s)))).

Definition fic_partition_function_temp_pos (I : FepIdentification) :
  real_lt real_zero (fic_partition_function_temp I) :=
  @fic_sum_pos I (fun s : @fic_S I =>
    real_exp_neg (real_opp (real_mult (fic_inv_T I) (@fic_z I s))))
    (fun s : @fic_S I => real_exp_neg_pos (real_opp (real_mult (fic_inv_T I) (@fic_z I s)))).

Definition fic_softmax_temp (I : FepIdentification) (s : @fic_S I) : Real :=
  real_mult (real_exp_neg (real_opp (real_mult (fic_inv_T I) (@fic_z I s))))
            (real_inv_pos (fic_partition_function_temp I)
                          (fic_partition_function_temp_pos I)).

(* side B (paper Sections 6.1/6.3): the Boltzmann distribution *)
Definition fic_boltzmann_factor (I : FepIdentification) (s : @fic_S I) : Real :=
  real_exp_neg (real_mult (fic_inv_D I) (@fic_energy I s)).

Definition fic_boltzmann_dist (I : FepIdentification) (s : @fic_S I) : Real :=
  real_mult (fic_inv_Z I) (fic_boltzmann_factor I s).

(* consumer theorem: with exp compatibility (an explicit premise; a true
   supplier on the concrete carrier is fic_real_exp_neg_compat below), the
   three identification fields imply softmax = Boltzmann pointwise *)
Definition fic_attention_is_gibbs_temp :
  forall (I : FepIdentification),
    (forall x y : Real, real_eq x y -> real_eq (real_exp_neg x) (real_exp_neg y)) ->
    forall s : @fic_S I, real_eq (fic_softmax_temp I s) (fic_boltzmann_dist I s).
Proof.
  intros I Hexp s.
  (* normalization inverse unification: inv(Z_thermo) == inv(temperature
     softmax partition) (identification 3 + inv_pos_ext) *)
  assert (Hie : real_eq (fic_inv_Z I)
                        (real_inv_pos (fic_partition_function_temp I)
                                      (fic_partition_function_temp_pos I)))
    by exact (real_inv_pos_ext (@fic_Z_thermo I) (fic_partition_function_temp I)
                (@fic_Z_thermo_pos I) (fic_partition_function_temp_pos I)
                (@fic_partition_match I)).
  unfold fic_softmax_temp, fic_boltzmann_dist, fic_boltzmann_factor.
  (* pointwise factor: exp(-invT * z) == exp(invD * energy)
     (identification 2 + identification 1 + the opp-mult bridge, lifted
     through exp compatibility) *)
  assert (Hf : real_eq (real_exp_neg (real_opp (real_mult (fic_inv_T I) (@fic_z I s))))
                       (real_exp_neg (real_mult (fic_inv_D I) (@fic_energy I s)))).
  { apply Hexp.
    exact (real_eq_trans (real_opp (real_mult (fic_inv_T I) (@fic_z I s)))
             (real_mult (fic_inv_T I) (real_opp (@fic_z I s)))
             (real_mult (fic_inv_D I) (@fic_energy I s))
             (real_eq_sym _ _ (fic_opp_mult_r (fic_inv_T I) (@fic_z I s)))
             (RealSetoid.real_eq_mult_compat (fic_inv_T I) (real_opp (@fic_z I s))
                (fic_inv_D I) (@fic_energy I s)
                (@fic_temp_match I)
                (real_eq_sym (@fic_energy I s) (real_opp (@fic_z I s))
                   (@fic_energy_neg I s)))). }
  (* commutation + inverse unification close: A * inv(P) == inv(Z) * B *)
  exact (real_eq_trans
           (real_mult (real_exp_neg (real_opp (real_mult (fic_inv_T I) (@fic_z I s))))
                      (real_inv_pos (fic_partition_function_temp I)
                                    (fic_partition_function_temp_pos I)))
           (real_mult (real_inv_pos (fic_partition_function_temp I)
                                    (fic_partition_function_temp_pos I))
                      (real_exp_neg (real_opp (real_mult (fic_inv_T I) (@fic_z I s)))))
           (real_mult (fic_inv_Z I) (real_exp_neg (real_mult (fic_inv_D I) (@fic_energy I s))))
           (real_mult_comm (real_exp_neg (real_opp (real_mult (fic_inv_T I) (@fic_z I s))))
                           (real_inv_pos (fic_partition_function_temp I)
                                         (fic_partition_function_temp_pos I)))
           (RealSetoid.real_eq_mult_compat
              (real_inv_pos (fic_partition_function_temp I)
                            (fic_partition_function_temp_pos I))
              (real_exp_neg (real_opp (real_mult (fic_inv_T I) (@fic_z I s))))
              (fic_inv_Z I)
              (real_exp_neg (real_mult (fic_inv_D I) (@fic_energy I s)))
              (real_eq_sym _ _ Hie) Hf)).
Defined.

(* ===================================================================== *)
(* C. The concrete instance FepIdentificationReal: satisfiability of the  *)
(*    three identification conditions on the two-state carrier            *)
(* ===================================================================== *)

(* exp compatibility on the concrete carrier (cauchy_real_exp_wd plus the
   opp-compatibility lemma): a true supplier for the explicit premise of
   fic_attention_is_gibbs_temp *)
Definition fic_real_exp_neg_compat :
  forall x y : Real, real_eq x y -> real_eq (real_exp_neg x) (real_exp_neg y).
Proof.
  intros x y H.
  exact (cauchy_real_exp_wd (real_opp x) (real_opp y) (RealSetoid.real_eq_opp_compat x y H)).
Defined.

(* instance body: fic_S := bool (two states), the sum := binary plus;
   fic_T := fic_D := one (identification 1 at reflection level);
   fic_energy := -one, fic_z := one (identification 2 at reflection level);
   fic_Z_thermo := e^{-1*(-1)} + e^{-1*(-1)}, identification 3 via the
   fic_opp_mult_r bridge lifted through exp compatibility (1*(-1) ==
   -(1*1)); the field values are substituted into the expected types of the
   later fields (beta-reducible) *)
Definition FepIdentificationReal : FepIdentification :=
  @Build_FepIdentification
    (* fic_S *)            bool
    (* fic_sumf *)         (fun f : bool -> Real => real_plus (f true) (f false))
    (* fic_sum_pos *)      (fun (f : bool -> Real)
                               (Hf : forall s : bool, real_lt real_zero (f s)) =>
                             RealSetoid.real_lt_id_l real_zero (real_plus real_zero real_zero)
                               (real_plus (f true) (f false))
                               (real_eq_sym (real_plus real_zero real_zero) real_zero
                                  (real_plus_zero real_zero))
                               (real_lt_plus_compat real_zero (f true) real_zero (f false)
                                  (Hf true) (Hf false)))
    (* fic_T *)            real_one
    (* fic_T_pos *)        real_lt_zero_one
    (* fic_D *)            real_one
    (* fic_D_pos *)        real_lt_zero_one
    (* fic_z *)            (fun _ : bool => real_one)
    (* fic_energy *)       (fun _ : bool => real_opp real_one)
    (* fic_Z_thermo *)     (real_plus
                              (real_exp_neg
                                 (real_mult (real_inv_pos real_one real_lt_zero_one)
                                            (real_opp real_one)))
                              (real_exp_neg
                                 (real_mult (real_inv_pos real_one real_lt_zero_one)
                                            (real_opp real_one))))
    (* fic_Z_thermo_pos *) (real_plus_positive
                              (real_exp_neg
                                 (real_mult (real_inv_pos real_one real_lt_zero_one)
                                            (real_opp real_one)))
                              (real_exp_neg
                                 (real_mult (real_inv_pos real_one real_lt_zero_one)
                                            (real_opp real_one)))
                              (real_exp_neg_pos
                                 (real_mult (real_inv_pos real_one real_lt_zero_one)
                                            (real_opp real_one)))
                              (real_exp_neg_pos
                                 (real_mult (real_inv_pos real_one real_lt_zero_one)
                                            (real_opp real_one))))
    (* fic_temp_match: both sides are inv(one), reflection level *)
    (real_eq_refl (real_inv_pos real_one real_lt_zero_one))
    (* fic_energy_neg: energy = -logits, reflection level *)
    (fun _ : bool => real_eq_refl (real_opp real_one))
    (* fic_partition_match: the opp-mult bridge per point, lifted through
       exp compatibility, both summands of the same shape *)
    (RealSetoid.real_eq_plus_compat
       (real_exp_neg (real_mult (real_inv_pos real_one real_lt_zero_one) (real_opp real_one)))
       (real_exp_neg (real_mult (real_inv_pos real_one real_lt_zero_one) (real_opp real_one)))
       (real_exp_neg (real_opp (real_mult (real_inv_pos real_one real_lt_zero_one) real_one)))
       (real_exp_neg (real_opp (real_mult (real_inv_pos real_one real_lt_zero_one) real_one)))
       (fic_real_exp_neg_compat
          (real_mult (real_inv_pos real_one real_lt_zero_one) (real_opp real_one))
          (real_opp (real_mult (real_inv_pos real_one real_lt_zero_one) real_one))
          (fic_opp_mult_r (real_inv_pos real_one real_lt_zero_one) real_one))
       (fic_real_exp_neg_compat
          (real_mult (real_inv_pos real_one real_lt_zero_one) (real_opp real_one))
          (real_opp (real_mult (real_inv_pos real_one real_lt_zero_one) real_one))
          (fic_opp_mult_r (real_inv_pos real_one real_lt_zero_one) real_one))).

(* ===================================================================== *)
(* D. Identity-face pieces: the original statement face of the paper, the *)
(*    loading of identification data into the interface object, and the   *)
(*    closing of the loop                                                 *)
(* ===================================================================== *)

(* Set-level transport: identity gives equality (constructive match on
   id_refl; the converse direction is not claimed) *)
Definition fic_id_to_req : forall x y : Real, Id x y -> real_eq x y.
Proof.
  intros x y p. destruct p.
  exact (real_eq_refl x).
Defined.

(* loading: identity-face identification data yields the interface object
   (the three fields are the data transported along fic_id_to_req) *)
Definition fic_id_data :
  forall (SS : Set) (sumf : (SS -> Real) -> Real),
  forall (spp : forall f : SS -> Real,
            (forall s : SS, real_lt real_zero (f s)) -> real_lt real_zero (sumf f)),
  forall (T : Real) (T_pos : real_lt real_zero T),
  forall (D : Real) (D_pos : real_lt real_zero D),
  forall (z0 energy0 : SS -> Real),
  forall (Zc : Real) (Zp : real_lt real_zero Zc),
  Id (real_inv_pos T T_pos) (real_inv_pos D D_pos) ->
  (forall s : SS, Id (energy0 s) (real_opp (z0 s))) ->
  Id Zc (sumf (fun s : SS =>
           real_exp_neg (real_opp (real_mult (real_inv_pos T T_pos) (z0 s))))) ->
  FepIdentification.
Proof.
  intros SS sumf spp T T_pos D D_pos z0 energy0 Zc Zp H1 H2 H3.
  exact (@Build_FepIdentification SS sumf spp T T_pos D D_pos z0 energy0 Zc Zp
           (fic_id_to_req _ _ H1)
           (fun s : SS => fic_id_to_req _ _ (H2 s))
           (fic_id_to_req _ _ H3)).
Defined.

(* the identity-face consumer: all three identifications imply
   attention = Boltzmann (full-argument use of the landed statement
   attention_is_gibbs_temp of S06_DiffSamplingGibbs) *)
Theorem fic_attention_is_gibbs_temp_id :
  forall (RI : RealInterfaceEnhanced) (SS : StateSpace RI) (SO : SumOver RI SS),
  forall (spp : forall f : @S01_BaseRing.S RI SS -> @S01_BaseRing.R RI,
            (forall s : @S01_BaseRing.S RI SS,
               @S01_BaseRing.lt RI (@S01_BaseRing.zero RI) (f s)) ->
            @S01_BaseRing.lt RI (@S01_BaseRing.zero RI) (@sum_over_S RI SS SO f)),
  forall (T : @S01_BaseRing.R RI) (T_pos : @S01_BaseRing.lt RI (@S01_BaseRing.zero RI) T),
  forall (D : @S01_BaseRing.R RI) (D_pos : @S01_BaseRing.lt RI (@S01_BaseRing.zero RI) D),
  forall (energy0 z0 : @S01_BaseRing.S RI SS -> @S01_BaseRing.R RI),
  Id (@S01_BaseRing.inv_pos RI T T_pos) (@S01_BaseRing.inv_pos RI D D_pos) ->
  (forall s : @S01_BaseRing.S RI SS,
     Id (energy0 s) (@S01_BaseRing.opp RI (z0 s))) ->
  Id (@Z_thermo RI SS SO D D_pos energy0)
     (@partition_function_temp RI SS SO T T_pos z0) ->
  forall s : @S01_BaseRing.S RI SS,
    Id (@softmax_temp RI SS SO spp T T_pos z0 s)
       (@boltzmann_dist_attn RI SS SO spp D D_pos energy0 s).
Proof.
  intros RI SS SO spp T T_pos D D_pos energy0 z0 H1 H2 H3 s.
  exact (@attention_is_gibbs_temp RI SS SO spp T T_pos D D_pos energy0 z0 H1 H2 H3 s).
Defined.

(* loop closure: identification data -> interface object -> back to the
   pointwise equality, through the consumer theorem at the object's fields *)
Definition fic_attention_is_gibbs_temp_via_id :
  forall (SS : Set) (sumf : (SS -> Real) -> Real),
  forall (spp : forall f : SS -> Real,
            (forall s : SS, real_lt real_zero (f s)) -> real_lt real_zero (sumf f)),
  forall (T : Real) (T_pos : real_lt real_zero T),
  forall (D : Real) (D_pos : real_lt real_zero D),
  forall (z0 energy0 : SS -> Real),
  forall (Zc : Real) (Zp : real_lt real_zero Zc),
  forall (H1 : Id (real_inv_pos T T_pos) (real_inv_pos D D_pos)),
  forall (H2 : forall s : SS, Id (energy0 s) (real_opp (z0 s))),
  forall (H3 : Id Zc (sumf (fun s : SS =>
             real_exp_neg (real_opp (real_mult (real_inv_pos T T_pos) (z0 s)))))),
  forall s : SS,
    real_eq (@fic_softmax_temp
               (fic_id_data SS sumf spp T T_pos D D_pos z0 energy0 Zc Zp H1 H2 H3) s)
            (@fic_boltzmann_dist
               (fic_id_data SS sumf spp T T_pos D D_pos z0 energy0 Zc Zp H1 H2 H3) s).
Proof.
  intros SS sumf spp T T_pos D D_pos z0 energy0 Zc Zp H1 H2 H3 s.
  exact (@fic_attention_is_gibbs_temp
           (fic_id_data SS sumf spp T T_pos D D_pos z0 energy0 Zc Zp H1 H2 H3)
           fic_real_exp_neg_compat s).
Defined.

(* ===================================================================== *)
(* Assumption audit: one line per theorem / carrier constant              *)
(* ===================================================================== *)

Print Assumptions fic_opp_mult_r.
Print Assumptions fic_attention_is_gibbs_temp.
Print Assumptions fic_real_exp_neg_compat.
Print Assumptions FepIdentificationReal.
Print Assumptions fic_id_to_req.
Print Assumptions fic_id_data.
Print Assumptions fic_attention_is_gibbs_temp_id.
Print Assumptions fic_attention_is_gibbs_temp_via_id.
