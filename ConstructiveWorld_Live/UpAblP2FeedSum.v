(* ========================================================================= *)
(* Module   : UpAblP2FeedSum                                                *)
(* Mission. Feed-summation block: strict positivity of the minimal single-  *)
(*            point SumOver instance (carrier [unit], at the abstract       *)
(*            RealInterfaceEnhanced level and at the concrete Real layer),  *)
(*            the full SumOver field discharge on that carrier, the        *)
(*            projection alignment of the landed Real instance fields,    *)
(*            cons-carried positivity of the alignment partition row, and *)
(*            the req-faced six-premise summation family.                 *)
(* Dependencies. S01_BaseRing (Id/classes/Set-level Not), S02_CauchyComplete*)
(*            (Real, real_* faces), S03_QExp (real_abs, real_inv_pos),     *)
(*            S07_RealSetoidExpLog (RealInterfaceEnhancedMod.RealEnhancedReal, *)
(*            real_mult_positive, real_exp_neg_pos), S08_RealMainlineDPO   *)
(*            (real_list_sum); UpAblZposReal (zabr_* faces); Stdlib init.  *)
(* References. ConstructiveWorld-Main UpAblP2FeedSum.v: statement names and *)
(*            faces carried over verbatim; the single-point state space    *)
(*            and SumOver instances are rebuilt in place (fsu_ssUnit /     *)
(*            fsu_ssUnit_elem / fsu_soUnit) since the landed tree does not *)
(*            host the upstream unit-carrier pack.                         *)
(* Constructivity. Statement faces are Set-carried end to end: every        *)
(*            predicate position is the decidable Q-carried form (real_lt  *)
(*            via QltT witnesses, req := real_eq via QeqT pointwise        *)
(*            bounds, real_le as the Set sum of the two); zero Prop        *)
(*            statements, zero axioms, zero classical logic, zero admits.  *)
(*            All data definitions are transparent; the proof pieces end   *)
(*            [Qed] as pure proof bridges over Set-carried statements      *)
(*            (precedent UpAblZposReal). [Not (Id l nil)] is the S01       *)
(*            Set-level negation (function into Empty_set), not Prop.      *)
(* Build. coqc -native-compiler no -q -Q <world root> "" UpAblP2FeedSum.v  *)
(* ========================================================================= *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import UpAblZposReal.

(* ================= Section 1. Strict positivity on the minimal SumOver instance ================= *)

(* Unit carrier uniqueness: the single-point state space has exactly one
   inhabitant up to [Id]. *)
Lemma fsu_unit_unique : forall a b : unit, Id a b.
Proof.
  intros a b.
  destruct a, b.
  reflexivity.
Qed.

(* Single-point state space over an arbitrary real interface: every
   structural field is the constant [tt] map, the metric is constant zero,
   and convergence is trivially decidable (the whole type [unit]). *)
Definition fsu_ssUnit {RI : RealInterface} : StateSpace RI :=
  {| S := unit;
     szero := tt;
     splus := fun _ _ => tt;
     smult := fun _ _ => tt;
     sopp := fun _ => tt;
     splus_assoc := fun _ _ _ => id_refl;
     splus_comm := fun _ _ => id_refl;
     splus_zero := fun a => fsu_unit_unique tt a;
     splus_opp := fun _ => id_refl;
     smult_one := fun a => fsu_unit_unique tt a;
     smult_assoc := fun _ _ _ => id_refl;
     smult_distrib_r := fun _ _ _ => id_refl;
     smult_distrib_l := fun _ _ _ => id_refl;
     smetric := fun _ _ => zero;
     smetric_sym := fun _ _ => id_refl;
     smetric_pos := fun _ _ => le_refl zero;
     smetric_zero := fun a b _ => fsu_unit_unique a b;
     smetric_triangle :=
       fun _ _ _ => le_id_r zero zero (plus zero zero) (id_sym (plus_zero zero)) (le_refl zero);
     clim := fun _ _ => unit;
     clim_unique := fun _ l1 l2 _ _ => fsu_unit_unique l1 l2;
     cauchy_complete_S := fun _ _ => existT (fun _ : unit => unit) tt tt |}.

(* The canonical element of the single-point state space (transparent so
   the sum instance below can project onto it). *)
Definition fsu_ssUnit_elem {RI : RealInterface} : @S RI fsu_ssUnit := tt.

(* Single-point SumOver instance: the sum of a family is its value at the
   unique point; every interface field holds by pointwise instantiation. *)
Definition fsu_soUnit {RI : RealInterface} : SumOver RI (@fsu_ssUnit RI) :=
  {| sum_over_S := fun f => f fsu_ssUnit_elem;
     sum_over_S_linear := fun a f => (@id_refl _ (mult a (f fsu_ssUnit_elem)));
     sum_over_S_add := fun f g => (@id_refl _ (plus (f fsu_ssUnit_elem) (g fsu_ssUnit_elem)));
     sum_over_S_ext := fun f g H => H fsu_ssUnit_elem;
     sum_over_S_le := fun f g H => H fsu_ssUnit_elem;
     sum_over_S_nonneg := fun f H => H fsu_ssUnit_elem;
     sum_over_S_zero_nonneg := fun f _ H0 s =>
       (match s as x return (Id (f x) zero) with
        | tt => H0
        end);
     abs_sum_le := fun f => le_refl (abs (f fsu_ssUnit_elem)) |}.

(* Strict sum positivity, original sentence shape, at the abstract enhanced
   interface level: itemwise strict positivity gives strict positivity of
   the single-point sum.  Non-emptiness comes from the carrier ontology
   ([fsu_ssUnit_elem]); no extra premise. *)
Theorem spd_slot_direct_unit :
  forall (REI : RealInterfaceEnhanced) (f : unit -> @R (@RI_base REI)),
    (forall s : unit, @lt (@RI_base REI) (@zero (@RI_base REI)) (f s)) ->
    @lt (@RI_base REI) (@zero (@RI_base REI))
        (@sum_over_S (@RI_base REI) fsu_ssUnit fsu_soUnit f).
Proof.
  intros REI f H.
  pose proof (H (fsu_ssUnit_elem (RI := @RI_base REI))) as Hw.
  exact Hw.
Qed.

(* ================= Section 2. Sum and strict positivity on the single-point concrete carrier ================= *)

(* Summation over the unit carrier at the concrete real layer: the
   single-point sum is the value at that point (definitional unfolding). *)
Definition spd_sum_unit (f : unit -> Real) : Real := f tt.

(* Strict sum positivity, original sentence shape, at the concrete real
   layer: itemwise strict positivity gives strict positivity of the sum.
   Non-emptiness comes from the carrier ontology ([tt : unit]). *)
Theorem spd_slot_unit_direct :
  forall f : unit -> Real,
    (forall s : unit, real_lt real_zero (f s)) ->
    real_lt real_zero (spd_sum_unit f).
Proof.
  intros f H.
  unfold spd_sum_unit.
  pose proof (H tt) as Hs.
  exact Hs.
Qed.

(* ================= Section 3. SumOver interface fields discharged on the single-point carrier ================= *)

(* Field linear: scalar multiplication distributes over the sum. *)
Lemma spd_field_linear :
  forall (a : Real) (f : unit -> Real),
    Id (spd_sum_unit (fun s => real_mult a (f s)))
       (real_mult a (spd_sum_unit f)).
Proof.
  intros a f.
  unfold spd_sum_unit.
  exact (id_cong (fun x => real_mult a x) (@id_refl _ (f tt))).
Qed.

(* Field add: addition distributes over the sum. *)
Lemma spd_field_add :
  forall f g : unit -> Real,
    Id (spd_sum_unit (fun s => real_plus (f s) (g s)))
       (real_plus (spd_sum_unit f) (spd_sum_unit g)).
Proof.
  intros f g.
  unfold spd_sum_unit.
  apply (id_trans
           (id_cong (fun x => real_plus x (g tt)) (@id_refl _ (f tt)))
           (id_cong (fun y => real_plus (f tt) y) (@id_refl _ (g tt)))).
Qed.

(* Field ext: pointwise identity gives identity of the sums (function
   properness). *)
Lemma spd_field_ext :
  forall f g : unit -> Real,
    (forall s : unit, Id (f s) (g s)) ->
    Id (spd_sum_unit f) (spd_sum_unit g).
Proof.
  intros f g H.
  unfold spd_sum_unit.
  pose proof (H tt) as Htt.
  exact Htt.
Qed.

(* Field le: pointwise order gives order of the sums (monotonicity). *)
Lemma spd_field_le :
  forall f g : unit -> Real,
    (forall s : unit, real_le (f s) (g s)) ->
    real_le (spd_sum_unit f) (spd_sum_unit g).
Proof.
  intros f g H.
  unfold spd_sum_unit.
  pose proof (H tt) as Hle.
  exact Hle.
Qed.

(* Field nonneg: pointwise nonnegativity gives nonnegativity of the sum. *)
Lemma spd_field_nonneg :
  forall f : unit -> Real,
    (forall s : unit, real_le real_zero (f s)) ->
    real_le real_zero (spd_sum_unit f).
Proof.
  intros f H.
  unfold spd_sum_unit.
  pose proof (H tt) as Hnn.
  exact Hnn.
Qed.

(* Field zero_nonneg: a zero sum of pointwise nonnegative terms is
   pointwise zero. *)
Lemma spd_field_zero_nonneg :
  forall f : unit -> Real,
    (forall s : unit, real_le real_zero (f s)) ->
    Id (spd_sum_unit f) real_zero ->
    forall s : unit, Id (f s) real_zero.
Proof.
  intros f _ Hsum s.
  destruct s.
  exact Hsum.
Qed.

(* Field abs: triangle inequality for the sum |sum f| <= sum |f|. *)
Lemma spd_field_abs :
  forall f : unit -> Real,
    real_le (real_abs (spd_sum_unit f))
            (spd_sum_unit (fun s => real_abs (f s))).
Proof.
  intros f.
  unfold spd_sum_unit.
  apply real_le_refl.
Qed.

(* Field seven (strict positivity) is [spd_slot_unit_direct] above; with the
   fields discharged the SumOver interface is fully realized on the
   single-point carrier, introducing no premise beyond the interface. *)

(* ================= Section 4. Instance projections aligned with the real-layer operations ================= *)

(* The zero projection of the landed Real instance is definitionally the
   real-layer zero. *)
Theorem spd_inst_zero_aligned :
  Id (@RealInterfaceEnhancedMod.zero
        RealInterfaceEnhancedMod.RealEnhancedReal)
     real_zero.
Proof.
  exact (@id_refl Real real_zero).
Qed.

(* The strict order projection of the landed Real instance is definitionally
   the real-layer strict order. *)
Theorem spd_inst_lt_aligned :
  forall (x y : Real)
         (Hs : @RealInterfaceEnhancedMod.lt
                 RealInterfaceEnhancedMod.RealEnhancedReal x y),
    real_lt x y.
Proof.
  intros x y Hs.
  exact Hs.
Qed.

(* ================= Section 5. Requirement-facing proposition: positivity of the cons-shaped partition row ================= *)

(* The real-layer counterpart of the S05 alignment partition row
   (sum_over_S mapped to real_list_sum, mult to real_mult, exp_neg to
   real_exp_neg, opp to real_opp, inv_pos to real_inv_pos; the advantage
   row enters as an abstract coefficient). *)
Definition spd_Z_rel (X : Set) (pi_t : X -> Real) (beta eta : Real)
  (beta_pos : real_lt real_zero beta) (adv : X -> Real) (l : list X) : Real :=
  real_list_sum X
    (fun s => real_mult (pi_t s)
       (real_exp_neg (real_opp
         (real_mult (real_mult eta (real_inv_pos beta beta_pos)) (adv s)))))
    l.

(* Real-layer counterpart of the S05 sum positivity step: assembled from
   real_mult_positive and real_exp_neg_pos (a positive weight times a
   positive exponential is positive); the positivity of the sum is given by
   the cons-carried fold lemma zabr_list_sum_pos_cons of UpAblZposReal. *)
Theorem spd_Z_rel_pos :
  forall (X : Set) (pi_t : X -> Real) (beta eta : Real)
         (beta_pos : real_lt real_zero beta) (adv : X -> Real)
         (l : list X) (w : X),
    (forall s : X, real_lt real_zero (pi_t s)) ->
    real_lt real_zero (spd_Z_rel X pi_t beta eta beta_pos adv (w :: l)).
Proof.
  intros X pi_t beta eta beta_pos adv l w Hpos.
  unfold spd_Z_rel.
  apply (zabr_list_sum_pos_cons X _ l w).
  intro s.
  apply real_mult_positive.
  - exact (Hpos s).
  - apply real_exp_neg_pos.
Qed.

(* ================= Section 6. Identity bridge and projection conversions ================= *)

(* Identity elimination: transport along [Id a b] into the real-layer
   equality face. *)
Lemma p2f_id_real_eq : forall a b : Real, Id a b -> real_eq a b.
Proof.
  intros a b H.
  induction H.
  apply real_eq_refl.
Qed.

(* The class-projection order faces and the real-layer order faces are
   bit-identical on the landed Real instance (definitional track switch);
   the body [exact H] is the shortest definitional closure. *)
Lemma p2f_proj_lt_of_real :
  forall x y : Real,
    real_lt x y ->
    @RealInterfaceEnhancedMod.lt RealInterfaceEnhancedMod.RealEnhancedReal x y.
Proof.
  intros x y H.
  exact H.
Qed.

Lemma p2f_real_lt_of_proj :
  forall x y : Real,
    @RealInterfaceEnhancedMod.lt RealInterfaceEnhancedMod.RealEnhancedReal x y ->
    real_lt x y.
Proof.
  intros x y H.
  exact H.
Qed.

Lemma p2f_proj_le_of_real :
  forall x y : Real,
    real_le x y ->
    @RealInterfaceEnhancedMod.le RealInterfaceEnhancedMod.RealEnhancedReal x y.
Proof.
  intros x y H.
  exact H.
Qed.

Lemma p2f_real_le_of_proj :
  forall x y : Real,
    @RealInterfaceEnhancedMod.le RealInterfaceEnhancedMod.RealEnhancedReal x y ->
    real_le x y.
Proof.
  intros x y H.
  exact H.
Qed.

Lemma p2f_proj_req_of_real :
  forall x y : Real,
    real_eq x y ->
    @RealInterfaceEnhancedMod.req RealInterfaceEnhancedMod.RealEnhancedReal x y.
Proof.
  intros x y H.
  exact H.
Qed.

Lemma p2f_real_eq_of_proj :
  forall x y : Real,
    @RealInterfaceEnhancedMod.req RealInterfaceEnhancedMod.RealEnhancedReal x y ->
    real_eq x y.
Proof.
  intros x y H.
  exact H.
Qed.

(* ================= Section 7. Id-faced SumOver sentence shape at the minimal instance ================= *)

(* Sentence shape as the named unfolding of the S04/S06 interface rows
   (R := @R RI, zero := @zero RI, lt := @lt RI, sum_over_S := @sum_over_S RI
   SS SO); the state space and sum instance are the minimal single-point
   world fsu_ssUnit / fsu_soUnit, interface parameters kept universally
   quantified. *)
Theorem p2f_S04_S06_slot_sum_over_S_pos :
  forall REI : RealInterfaceEnhanced,
    forall f : unit -> @R (@RI_base REI),
      (forall s : unit, @lt (@RI_base REI) (@zero (@RI_base REI)) (f s)) ->
      @lt (@RI_base REI) (@zero (@RI_base REI))
          (@sum_over_S (@RI_base REI) fsu_ssUnit fsu_soUnit f).
Proof.
  exact spd_slot_direct_unit.
Qed.

(* ================= Section 8. The six req-faced premises assembled on the landed instance ================= *)

(* Premise one, sum_ext: pointwise req equality gives req equality of the
   sums.  On the single-point carrier the sum is the point value, so the
   premise at [tt] gives it directly. *)
Theorem p2f_req_sum_ext :
  forall f g : unit -> Real,
    (forall s : unit,
       @RealInterfaceEnhancedMod.req RealInterfaceEnhancedMod.RealEnhancedReal
         (f s) (g s)) ->
    @RealInterfaceEnhancedMod.req RealInterfaceEnhancedMod.RealEnhancedReal
      (spd_sum_unit f) (spd_sum_unit g).
Proof.
  intros f g H.
  unfold spd_sum_unit.
  exact (H tt).
Qed.

(* Premise two, sum_add: the sum of the pointwise sum is the sum of the
   sums (req face); routed through [spd_field_add]. *)
Theorem p2f_req_sum_add :
  forall f g : unit -> Real,
    @RealInterfaceEnhancedMod.req RealInterfaceEnhancedMod.RealEnhancedReal
      (spd_sum_unit (fun s : unit =>
         @RealInterfaceEnhancedMod.plus RealInterfaceEnhancedMod.RealEnhancedReal
           (f s) (g s)))
      (@RealInterfaceEnhancedMod.plus RealInterfaceEnhancedMod.RealEnhancedReal
         (spd_sum_unit f) (spd_sum_unit g)).
Proof.
  intros f g.
  exact (match spd_field_add f g in Id _ y return
           real_eq (spd_sum_unit (fun s : unit => real_plus (f s) (g s))) y
         with id_refl => real_eq_refl _ end).
Qed.

(* Premise three, sum_linear: scalar multiplication commutes with the sum
   (req face); routed through [spd_field_linear]. *)
Theorem p2f_req_sum_linear :
  forall (a : Real) (f : unit -> Real),
    @RealInterfaceEnhancedMod.req RealInterfaceEnhancedMod.RealEnhancedReal
      (spd_sum_unit (fun s : unit =>
         @RealInterfaceEnhancedMod.mult RealInterfaceEnhancedMod.RealEnhancedReal
           a (f s)))
      (@RealInterfaceEnhancedMod.mult RealInterfaceEnhancedMod.RealEnhancedReal
         a (spd_sum_unit f)).
Proof.
  intros a f.
  exact (match spd_field_linear a f in Id _ y return
           real_eq (spd_sum_unit (fun s : unit => real_mult a (f s))) y
         with id_refl => real_eq_refl _ end).
Qed.

(* Premise four, sum_le: pointwise order gives order of the sums; routed
   through [spd_field_le] with the conversion lemmas. *)
Theorem p2f_req_sum_le :
  forall f g : unit -> Real,
    (forall s : unit,
       @RealInterfaceEnhancedMod.le RealInterfaceEnhancedMod.RealEnhancedReal
         (f s) (g s)) ->
    @RealInterfaceEnhancedMod.le RealInterfaceEnhancedMod.RealEnhancedReal
      (spd_sum_unit f) (spd_sum_unit g).
Proof.
  intros f g H.
  exact (spd_field_le f g H).
Qed.

(* Premise five, sum_zero_nonneg: a zero sum of pointwise nonnegative terms
   is pointwise zero.  On the single-point carrier the conclusion is the
   premise itself after [destruct s]; note the strength gap is recorded
   honestly: the donor [spd_field_zero_nonneg] takes the strong [Id]
   premise, so this req-faced form is discharged directly, not via it. *)
Theorem p2f_req_sum_zero_nonneg :
  forall f : unit -> Real,
    (forall s : unit,
       @RealInterfaceEnhancedMod.le RealInterfaceEnhancedMod.RealEnhancedReal
         (@RealInterfaceEnhancedMod.zero RealInterfaceEnhancedMod.RealEnhancedReal)
         (f s)) ->
    @RealInterfaceEnhancedMod.req RealInterfaceEnhancedMod.RealEnhancedReal
      (spd_sum_unit f)
      (@RealInterfaceEnhancedMod.zero RealInterfaceEnhancedMod.RealEnhancedReal) ->
    forall s : unit,
      @RealInterfaceEnhancedMod.req RealInterfaceEnhancedMod.RealEnhancedReal
        (f s)
        (@RealInterfaceEnhancedMod.zero RealInterfaceEnhancedMod.RealEnhancedReal).
Proof.
  intros f Hle Hsum s.
  destruct s as [u].
  unfold spd_sum_unit in Hsum.
  exact Hsum.
Qed.

(* Premise six, sum_pos: pointwise positivity gives positivity of the sum;
   routed through [spd_slot_unit_direct]. *)
Theorem p2f_req_sum_pos :
  forall f : unit -> Real,
    (forall s : unit,
       @RealInterfaceEnhancedMod.lt RealInterfaceEnhancedMod.RealEnhancedReal
         (@RealInterfaceEnhancedMod.zero RealInterfaceEnhancedMod.RealEnhancedReal)
         (f s)) ->
    @RealInterfaceEnhancedMod.lt RealInterfaceEnhancedMod.RealEnhancedReal
      (@RealInterfaceEnhancedMod.zero RealInterfaceEnhancedMod.RealEnhancedReal)
      (spd_sum_unit f).
Proof.
  intros f H.
  exact (spd_slot_unit_direct f H).
Qed.

(* ================= Section 9. Real-layer positivity paths (list carrier) ================= *)

(* Cons-carried shape: non-emptiness comes from the carrier ontology
   [w :: l], no extra premise; immediate from zabr_list_sum_pos_cons. *)
Theorem p2f_req_sum_pos_cons :
  forall (X : Set) (f : X -> Real) (l : list X) (w : X),
    (forall s : X,
       @RealInterfaceEnhancedMod.lt RealInterfaceEnhancedMod.RealEnhancedReal
         (@RealInterfaceEnhancedMod.zero RealInterfaceEnhancedMod.RealEnhancedReal)
         (f s)) ->
    @RealInterfaceEnhancedMod.lt RealInterfaceEnhancedMod.RealEnhancedReal
      (@RealInterfaceEnhancedMod.zero RealInterfaceEnhancedMod.RealEnhancedReal)
      (real_list_sum X f (w :: l)).
Proof.
  intros X f l w H.
  exact (zabr_list_sum_pos_cons X f l w H).
Qed.

(* Arbitrary-list shape: with the weakest realizable non-emptiness premise
   (the S01 Set-level negation of the nil identity); immediate from
   zabr_sum_over_S_pos. *)
Theorem p2f_req_sum_pos_list :
  forall (X : Set) (f : X -> Real) (l : list X),
    Not (Id l nil) ->
    (forall s : X,
       @RealInterfaceEnhancedMod.lt RealInterfaceEnhancedMod.RealEnhancedReal
         (@RealInterfaceEnhancedMod.zero RealInterfaceEnhancedMod.RealEnhancedReal)
         (f s)) ->
    @RealInterfaceEnhancedMod.lt RealInterfaceEnhancedMod.RealEnhancedReal
      (@RealInterfaceEnhancedMod.zero RealInterfaceEnhancedMod.RealEnhancedReal)
      (real_list_sum X f l).
Proof.
  intros X f l Hnn H.
  exact (zabr_sum_over_S_pos X f l Hnn H).
Qed.

(* ================= Section 10. Assumption audit (one Print Assumptions per theorem) ================= *)

Print Assumptions fsu_unit_unique.
Print Assumptions spd_slot_direct_unit.
Print Assumptions spd_slot_unit_direct.
Print Assumptions spd_field_linear.
Print Assumptions spd_field_add.
Print Assumptions spd_field_ext.
Print Assumptions spd_field_le.
Print Assumptions spd_field_nonneg.
Print Assumptions spd_field_zero_nonneg.
Print Assumptions spd_field_abs.
Print Assumptions spd_inst_zero_aligned.
Print Assumptions spd_inst_lt_aligned.
Print Assumptions spd_Z_rel_pos.
Print Assumptions p2f_id_real_eq.
Print Assumptions p2f_proj_lt_of_real.
Print Assumptions p2f_real_lt_of_proj.
Print Assumptions p2f_proj_le_of_real.
Print Assumptions p2f_real_le_of_proj.
Print Assumptions p2f_proj_req_of_real.
Print Assumptions p2f_real_eq_of_proj.
Print Assumptions p2f_S04_S06_slot_sum_over_S_pos.
Print Assumptions p2f_req_sum_ext.
Print Assumptions p2f_req_sum_add.
Print Assumptions p2f_req_sum_linear.
Print Assumptions p2f_req_sum_le.
Print Assumptions p2f_req_sum_zero_nonneg.
Print Assumptions p2f_req_sum_pos.
Print Assumptions p2f_req_sum_pos_cons.
Print Assumptions p2f_req_sum_pos_list.
