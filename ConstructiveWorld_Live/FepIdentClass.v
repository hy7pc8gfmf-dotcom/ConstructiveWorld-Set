(* =====================================================================
   FepIdentClass.v - named interface fields for the Fep identification
   conditions (paper 6 §6.5/§10.2).
   Mission.  the three modeling identifications of paper 6 §6.5
     (temperature match / energy as negative logits / partition-function
     match) become named fields of Class FepIdentification
     (fic_temp_match / fic_energy_neg / fic_partition_match, with the
     positivity premises named alongside), plus a concrete model
     instance and Id-form consumers (§10.2 open item 2: making
     identification a reusable object); the fic_ prefix guards against
     name clashes library-wide. key points: (A) three identification
     fields with named positivity premises; (B) the paper's §6.1/§6.3
     two-sided constructions as class-field definitions; (C) Instance
     FepIdentificationReal on the concrete Cauchy reals proves all
     three identifications constructively, a witness that
     identification is satisfiable rather than a theorem; (D) Id-form
     consumers run through the req := Id bridge.
   Dependencies.  S02 / S06 / S07 / TempSoftmaxInstantiation (existing library modules).
   References.  paper 6 (free-energy variational principle, constructive identification, formal version) §6.5/§10.2; S06.AttentionGibbsBridge attention_is_gibbs_temp.
   fic_id_bridge / fic_id_data / fic_attention_is_gibbs_temp_via_id: carriers removed per interface-generation — Id-bridge trio requires new development not present in current tree (Wave3 candidate).
   extraction disclosure: magic_ml = 8 is intrinsic — the fic_S : Set field erases to Obj.t under extraction, boxing the FepIdentificationReal f true / f false applications (not a wash debt).
   Constructivity.  fully constructive; statement faces carry no Prop
     (req / lt / le are Set-valued); no assumption faces of any kind;
     non-trivial (the exp compatibility lift, the seven-step group-law
     bridge for a·(−x) == −(a·x), inverse unification, genuine
     commutativity); assumption positions are explicit theorem
     arguments, not assumed facts.
   Build.  coqc -native-compiler no -q -Q . "" ; .vo magic
     [436f7121 000160bc].
   ===================================================================== *)
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
Require Import TempSoftmaxInstantiation.
Import RealInterfaceEnhancedMod.

(* interface alignment per SigMigrate_core precedent (field-wise
   Abbreviation/notation anchoring to the concrete twins assigned by the
   global Instance RealEnhancedReal; the drifted parameterized shell
   removed): this tree's RealInterfaceEnhancedSetoid is the argument-less
   Class on the global Real carrier (S07_RealSetoidExpLog.v:8696), so the
   Main-tree binder pairs Context (R : Set) {RIS : RealInterfaceEnhancedSetoid R}.
   and the @-projections at (R, RIS) are re-anchored to the concrete
   real_* operations; the fic_* face names are kept verbatim. statement
   names and proof bodies verbatim. *)
Abbreviation R := Real.

(* ===================================================================== *)
(* Section A: bringing the identification conditions into the library,   *)
(* ===================================================================== *)

Section FepIdentCore.

(* interface projection notations (fully explicit @, guarding against   *)
(*   elaborator implicit-argument ambiguity; valid inside this section) *)
Abbreviation ficreq := (fun x y => real_eq x y).
Abbreviation ficlt := (fun x y => real_lt x y).
Abbreviation ficzero := real_zero.
Abbreviation ficmult := (fun a b => real_mult a b).
Abbreviation ficopp := (fun a => real_opp a).
Abbreviation ficinv := (fun x Hx => real_inv_pos x Hx).
Abbreviation ficexpn := (fun a => real_exp_neg a).

(* ---- paper 6 §6.5/§10.2: the three identification conditions as
   three named fields. the fields come in three layers:
   - state space and summation apparatus (fic_S / fic_sumf /
     fic_sum_pos, honest interface slots);
   - modeling data (fic_T / fic_D / fic_z / fic_energy / fic_Z_thermo
     with their named positivity premises);
   - the three identification conditions (fic_temp_match /
     fic_energy_neg / fic_partition_match) in req form: at
     req := real_eq this is the Real-layer reading, at req := Id
     (fic_id_bridge, pruned) it is the paper's original Id statement face;
   - the right side of fic_partition_match is the temperature softmax
     partition (exp_pos_fn unfolding: exp_neg (opp (·))), verbatim
     isomorphic to partition_function_temp of paper §6.3. *)
Class FepIdentification : Type := {
  fic_S : Set;
  fic_sumf : (fic_S -> R) -> R;
  fic_sum_pos :
    forall f : fic_S -> R,
      (forall s : fic_S, ficlt ficzero (f s)) -> ficlt ficzero (fic_sumf f);
  fic_T : R;
  fic_T_pos : ficlt ficzero fic_T;
  fic_D : R;
  fic_D_pos : ficlt ficzero fic_D;
  fic_z : fic_S -> R;
  fic_energy : fic_S -> R;
  fic_Z_thermo : R;
  fic_Z_thermo_pos : ficlt ficzero fic_Z_thermo;
  (* ---- identification 1: temperature match (paper §6.3) ---- *)
  fic_temp_match : ficreq (ficinv fic_T fic_T_pos) (ficinv fic_D fic_D_pos);
  (* ---- identification 2: energy as negative logits (paper §6.2) ---- *)
  fic_energy_neg : forall s : fic_S, ficreq (fic_energy s) (ficopp (fic_z s));
  (* ---- identification 3: partition-function match (paper §6.3; right side = temperature softmax partition) ---- *)
  fic_partition_match :
    ficreq fic_Z_thermo
      (fic_sumf (fun s : fic_S =>
        ficexpn (ficopp (ficmult (ficinv fic_T fic_T_pos) (fic_z s)))))
}.

End FepIdentCore.

(* ===================================================================== *)
(* Section B: the two-sided constructions as class fields + the consumer *)
(* ===================================================================== *)

Section FepIdentConsumer.

Context {I : FepIdentification}.

Abbreviation ficreq := (fun x y => real_eq x y).
Abbreviation ficlt := (fun x y => real_lt x y).
Abbreviation ficzero := real_zero.
Abbreviation ficplus := (fun a b => real_plus a b).
Abbreviation ficmult := (fun a b => real_mult a b).
Abbreviation ficopp := (fun a => real_opp a).
Abbreviation ficinv := (fun x Hx => real_inv_pos x Hx).
Abbreviation ficexpn := (fun a => real_exp_neg a).

(* combinator aliases (fully explicit arguments, guarding against the    *)
(*   known missing-explicit-argument pitfall of this interface family)   *)
Let ficreqrefl := real_eq_refl.
Let ficreqsym := real_eq_sym.
Let ficreqtrans := real_eq_trans.
Let ficpluscompat := RealSetoid.real_eq_plus_compat_adapt.
Let ficmultcompat := RealSetoid.real_eq_mult_compat_adapt.
Let ficmultcomm := real_mult_comm.
Let ficplusassoc := real_plus_assoc.
Let ficpluscomm := real_plus_comm.
Let ficpluszero := real_plus_zero.
Let ficplusopp := real_plus_opp.
Let ficmultzero := real_mult_zero.
Let ficdistrib := real_distrib.
Let ficinvext := real_inv_pos_ext.
Let ficexpnpos := real_exp_neg_pos.

(* class-field projection aliases *)
Let Sc := @fic_S I.
Let sumf := @fic_sumf I.
Let T := @fic_T I.
Let T_pos := @fic_T_pos I.
Let D0 := @fic_D I.
Let Dpos := @fic_D_pos I.
Let z0 := @fic_z I.
Let energy0 := @fic_energy I.
Let Z0 := @fic_Z_thermo I.
Let Zpos := @fic_Z_thermo_pos I.

(* ---- auxiliary lemma: a·(−x) == −(a·x) (req face; the Setoid          *)
(*      Enhanced interface carries no opp_mult field, so this is proven  *)
(*      genuinely in seven group-law steps through distrib / mult_zero / *)
(*      plus_opp / assoc / comm / zero - a non-trivial supplement,       *)
(*      reused by identification 3 of the Real instance in Section C)    *)
Lemma fic_opp_mult_r :
  forall a x : R, ficreq (ficmult a (ficopp x)) (ficopp (ficmult a x)).
Proof.
  intros a x.
  (* intermediate goal: a·x + a·(−x) == 0 (distrib read backwards +
     plus_opp + mult_zero) *)
  assert (Huv : ficreq (ficplus (ficmult a x) (ficmult a (ficopp x))) ficzero).
  { exact (ficreqtrans (ficplus (ficmult a x) (ficmult a (ficopp x)))
             (ficmult a (ficplus x (ficopp x))) ficzero
             (ficreqsym _ _ (ficdistrib a x (ficopp x)))
             (ficreqtrans (ficmult a (ficplus x (ficopp x))) (ficmult a ficzero) ficzero
               (ficmultcompat a a (ficplus x (ficopp x)) ficzero (ficreqrefl a)
                 (ficplusopp x))
               (ficmultzero a))). }
  (* the four small steps toward v == −u (with v := a·(−x), u := a·x):
     v+0 == v+(u+(−u)) == (v+u)+(−u) == (u+v)+(−u) == 0+(−u) == −u *)
  assert (Hstep1 : ficreq (ficmult a (ficopp x))
                     (ficplus (ficmult a (ficopp x)) ficzero)).
  { exact (ficreqsym _ _ (ficpluszero (ficmult a (ficopp x)))). }
  assert (Hstep2 : ficreq (ficplus (ficmult a (ficopp x)) ficzero)
                     (ficplus (ficmult a (ficopp x))
                              (ficplus (ficmult a x) (ficopp (ficmult a x))))).
  { exact (ficpluscompat (ficmult a (ficopp x)) (ficmult a (ficopp x)) ficzero
             (ficplus (ficmult a x) (ficopp (ficmult a x)))
             (ficreqrefl (ficmult a (ficopp x)))
             (ficreqsym (ficplus (ficmult a x) (ficopp (ficmult a x))) ficzero
               (ficplusopp (ficmult a x)))). }
  assert (Hstep3 : ficreq (ficplus (ficmult a (ficopp x))
                                   (ficplus (ficmult a x) (ficopp (ficmult a x))))
                     (ficplus ficzero (ficopp (ficmult a x)))).
  { exact (ficreqtrans
             (ficplus (ficmult a (ficopp x))
                      (ficplus (ficmult a x) (ficopp (ficmult a x))))
             (ficplus (ficplus (ficmult a (ficopp x)) (ficmult a x))
                      (ficopp (ficmult a x)))
             (ficplus ficzero (ficopp (ficmult a x)))
             (ficplusassoc (ficmult a (ficopp x)) (ficmult a x) (ficopp (ficmult a x)))
             (ficreqtrans (ficplus (ficplus (ficmult a (ficopp x)) (ficmult a x))
                                   (ficopp (ficmult a x)))
                (ficplus (ficplus (ficmult a x) (ficmult a (ficopp x)))
                         (ficopp (ficmult a x)))
                (ficplus ficzero (ficopp (ficmult a x)))
                (ficpluscompat (ficplus (ficmult a (ficopp x)) (ficmult a x))
                   (ficplus (ficmult a x) (ficmult a (ficopp x)))
                   (ficopp (ficmult a x)) (ficopp (ficmult a x))
                   (ficpluscomm (ficmult a (ficopp x)) (ficmult a x))
                   (ficreqrefl (ficopp (ficmult a x))))
                (ficpluscompat (ficplus (ficmult a x) (ficmult a (ficopp x)))
                   ficzero
                   (ficopp (ficmult a x)) (ficopp (ficmult a x))
                   Huv (ficreqrefl (ficopp (ficmult a x)))))). }
  assert (Hstep4 : ficreq (ficplus ficzero (ficopp (ficmult a x)))
                     (ficopp (ficmult a x))).
  { exact (ficreqtrans (ficplus ficzero (ficopp (ficmult a x)))
             (ficplus (ficopp (ficmult a x)) ficzero) (ficopp (ficmult a x))
             (ficpluscomm ficzero (ficopp (ficmult a x)))
             (ficpluszero (ficopp (ficmult a x)))). }
  exact (ficreqtrans (ficmult a (ficopp x))
           (ficplus (ficmult a (ficopp x)) ficzero) (ficopp (ficmult a x)) Hstep1
           (ficreqtrans (ficplus (ficmult a (ficopp x)) ficzero)
              (ficplus (ficmult a (ficopp x))
                       (ficplus (ficmult a x) (ficopp (ficmult a x))))
              (ficopp (ficmult a x)) Hstep2
              (ficreqtrans (ficplus (ficmult a (ficopp x))
                                    (ficplus (ficmult a x) (ficopp (ficmult a x))))
                 (ficplus ficzero (ficopp (ficmult a x)))
                 (ficopp (ficmult a x)) Hstep3 Hstep4))).
Qed.

(* ---- paper §6.1/§6.3 two-sided constructions (as class fields) ---- *)
Definition fic_partition_function_temp : R :=
  sumf (fun s : Sc => ficexpn (ficopp (ficmult (ficinv T T_pos) (z0 s)))).

Definition fic_partition_function_temp_pos :
  ficlt ficzero fic_partition_function_temp :=
  @fic_sum_pos I
    (fun s : Sc => ficexpn (ficopp (ficmult (ficinv T T_pos) (z0 s))))
    (fun s => ficexpnpos (ficopp (ficmult (ficinv T T_pos) (z0 s)))).

Definition fic_softmax_temp (s : Sc) : R :=
  ficmult (ficexpn (ficopp (ficmult (ficinv T T_pos) (z0 s))))
          (ficinv fic_partition_function_temp fic_partition_function_temp_pos).

Definition fic_boltzmann_factor (s : Sc) : R :=
  ficexpn (ficmult (ficinv D0 Dpos) (energy0 s)).

Definition fic_boltzmann_dist (s : Sc) : R :=
  ficmult (ficinv Z0 Zpos) (fic_boltzmann_factor s).

(* ---- consumer theorem (the class-field form of paper §6.3             *)
(*   attention_is_gibbs_temp): with the three identifications in place   *)
(*   (fic_temp_match / fic_energy_neg / fic_partition_match fields), the *)
(*   temperature softmax equals the Boltzmann distribution pointwise.    *)
(*   the exp compatibility lift is an explicit theorem argument (a       *)
(*   premise-carrying machine on the req face; on the Id face it is      *)
(*   satisfied for free through id_cong; the via_id consumer is a        *)
(*   Wave3 candidate).                                                   *)
Theorem fic_attention_is_gibbs_temp :
  (forall x y : R, ficreq x y -> ficreq (ficexpn x) (ficexpn y)) ->
  forall s : Sc, ficreq (fic_softmax_temp s) (fic_boltzmann_dist s).
Proof.
  intros Hexp s.
  (* unifying the normalization inverses: inv(Z_thermo) == inv(the
     temperature partition) (identification 3 + inv_pos_ext) *)
  assert (Hie : ficreq (ficinv Z0 Zpos)
                       (ficinv fic_partition_function_temp fic_partition_function_temp_pos))
    by exact (ficinvext Z0 fic_partition_function_temp Zpos
               fic_partition_function_temp_pos (@fic_partition_match I)).
  unfold fic_softmax_temp, fic_boltzmann_dist, fic_boltzmann_factor.
  (* pointwise factor: exp(−invT·z) == exp(−invD·energy)
     (identification 2, energy = −logits + identification 1, temperature
     match + the opp-mult bridge, then the exp compatibility lift) *)
  assert (Hf : ficreq (ficexpn (ficopp (ficmult (ficinv T T_pos) (z0 s))))
                      (ficexpn (ficmult (ficinv D0 Dpos) (energy0 s)))).
  { apply Hexp.
    exact (ficreqtrans (ficopp (ficmult (ficinv T T_pos) (z0 s)))
             (ficmult (ficinv T T_pos) (ficopp (z0 s)))
             (ficmult (ficinv D0 Dpos) (energy0 s))
             (ficreqsym _ _ (fic_opp_mult_r (ficinv T T_pos) (z0 s)))
             (ficmultcompat (ficinv T T_pos) (ficinv D0 Dpos) (ficopp (z0 s)) (energy0 s)
                (@fic_temp_match I)
                (ficreqsym (energy0 s) (ficopp (z0 s))
                  (@fic_energy_neg I s)))). }
  (* closing by commutation + inverse unification: A·inv(P) == inv(Z)·B *)
  exact (ficreqtrans (ficmult (ficexpn (ficopp (ficmult (ficinv T T_pos) (z0 s))))
                              (ficinv fic_partition_function_temp fic_partition_function_temp_pos))
           (ficmult (ficinv fic_partition_function_temp fic_partition_function_temp_pos)
                    (ficexpn (ficopp (ficmult (ficinv T T_pos) (z0 s)))))
           (ficmult (ficinv Z0 Zpos) (ficexpn (ficmult (ficinv D0 Dpos) (energy0 s))))
           (ficmultcomm (ficexpn (ficopp (ficmult (ficinv T T_pos) (z0 s))))
                        (ficinv fic_partition_function_temp fic_partition_function_temp_pos))
           (ficmultcompat (ficinv fic_partition_function_temp fic_partition_function_temp_pos)
              (ficinv Z0 Zpos)
              (ficexpn (ficopp (ficmult (ficinv T T_pos) (z0 s))))
              (ficexpn (ficmult (ficinv D0 Dpos) (energy0 s)))
              (ficreqsym _ _ Hie) Hf)).
Qed.

End FepIdentConsumer.

(* ===================================================================== *)
(* Section C: the Real-layer instance FepIdentificationReal - the        *)
(*   constructive satisfiability witness of the three identifications   *)
(*   on the concrete Real carrier (req := real_eq reading, S07           *)
(*   RealEnhancedReal)                                                   *)
(* ===================================================================== *)

(* the exp compatibility lift, discharged at the Real layer in two steps
   (cauchy_real_exp_wd + req_opp_compat): the explicit theorem argument
   of fic_attention_is_gibbs_temp has a genuine supplier on concrete
   Real. *)
Lemma fic_real_exp_neg_compat :
  forall x y : Real,
    real_eq x y ->
    real_eq
      (real_exp_neg x)
      (real_exp_neg y).
Proof.
  intros x y H.
  exact (cauchy_real_exp_wd (real_opp x) (real_opp y)
           (RealSetoid.real_eq_opp_compat x y H)).
Qed.

(* instance body: fic_S := bool (two states), summation := binary plus;
   fic_T := fic_D := one (identification 1, temperature match, at the
   req_refl level); fic_energy := opp·one and fic_z := one
   (identification 2 at the req_refl level); fic_Z_thermo :=
   e^{−1·(−1)} + e^{−1·(−1)}, identification 3 through the pointwise
   fic_opp_mult_r bridge (1·(−1) == −(1·1)) plus a genuine proof of the
   exp compatibility lift (both branches same shape).
   Build_ taken directly: field values substituted into the expected
   types of the later fields (beta-reducible). *)
Instance FepIdentificationReal :
  FepIdentification.
Proof.
  apply (@Build_FepIdentification
    (* fic_S *)            bool
    (* fic_sumf *)         (fun f : bool -> Real => real_plus (f true) (f false))
    (* fic_sum_pos *)      (fun (f : bool -> Real)
                                (Hf : forall s : bool,
                                   real_lt
                                     (real_zero) (f s)) =>
                            RealSetoid.real_lt_id_l
                              (real_zero)
                              (real_plus
                                 (real_zero)
                                 (real_zero))
                              (real_plus (f true) (f false))
                              (real_eq_sym
                                 (real_plus
                                    (real_zero)
                                    (real_zero))
                                 (real_zero)
                                 (real_plus_zero
                                    (real_zero)))
                              (real_lt_plus_compat
                                 (real_zero) (f true)
                                 (real_zero) (f false)
                                 (Hf true) (Hf false)))
    (* fic_T *)            (real_one)
    (* fic_T_pos *)        (real_lt_zero_one)
    (* fic_D *)            (real_one)
    (* fic_D_pos *)        (real_lt_zero_one)
    (* fic_z *)            (fun _ : bool => real_one)
    (* fic_energy *)       (fun _ : bool =>
                              real_opp
                                (real_one))
    (* fic_Z_thermo *)     (real_plus
                              (real_exp_neg
                                 (real_mult
                                    (real_inv_pos
                                       (real_one)
                                       (real_lt_zero_one))
                                    (real_opp
                                       (real_one))))
                              (real_exp_neg
                                 (real_mult
                                    (real_inv_pos
                                       (real_one)
                                       (real_lt_zero_one))
                                    (real_opp
                                       (real_one)))))
    (* fic_Z_thermo_pos *) (real_plus_positive
                              (real_exp_neg
                                 (real_mult
                                    (real_inv_pos
                                       (real_one)
                                       (real_lt_zero_one))
                                    (real_opp
                                       (real_one))))
                              (real_exp_neg
                                 (real_mult
                                    (real_inv_pos
                                       (real_one)
                                       (real_lt_zero_one))
                                    (real_opp
                                       (real_one))))
                              (real_exp_neg_pos
                                 (real_mult
                                    (real_inv_pos
                                       (real_one)
                                       (real_lt_zero_one))
                                    (real_opp
                                       (real_one))))
                              (real_exp_neg_pos
                                 (real_mult
                                    (real_inv_pos
                                       (real_one)
                                       (real_lt_zero_one))
                                    (real_opp
                                       (real_one)))))
    (* fic_temp_match - identification 1: both sides are inv(one), req_refl level *)
    (real_eq_refl
       (real_inv_pos
          (real_one)
          (real_lt_zero_one)))
    (* fic_energy_neg - identification 2: energy = opp·z, req_refl level *)
    (fun _ : bool =>
       real_eq_refl
         (real_opp
            (real_one)))
    (* fic_partition_match - identification 3: the pointwise fic_opp_mult_r bridge under the exp compatibility lift, both branches same shape *)
    (RealSetoid.real_eq_plus_compat_adapt
       (real_exp_neg
          (real_mult
             (real_inv_pos
                (real_one)
                (real_lt_zero_one))
             (real_opp
                (real_one))))
       (real_exp_neg
          (real_opp
             (real_mult
                (real_inv_pos
                   (real_one)
                   (real_lt_zero_one))
                (real_one))))
       (real_exp_neg
          (real_mult
             (real_inv_pos
                (real_one)
                (real_lt_zero_one))
             (real_opp
                (real_one))))
       (real_exp_neg
          (real_opp
             (real_mult
                (real_inv_pos
                   (real_one)
                   (real_lt_zero_one))
                (real_one))))
       (fic_real_exp_neg_compat
          (real_mult
             (real_inv_pos
                (real_one)
                (real_lt_zero_one))
             (real_opp
                (real_one)))
          (real_opp
             (real_mult
                (real_inv_pos
                   (real_one)
                   (real_lt_zero_one))
                (real_one)))
          (@fic_opp_mult_r
             (real_inv_pos
                (real_one)
                (real_lt_zero_one))
             (real_one)))
       (fic_real_exp_neg_compat
          (real_mult
             (real_inv_pos
                (real_one)
                (real_lt_zero_one))
             (real_opp
                (real_one)))
          (real_opp
             (real_mult
                (real_inv_pos
                   (real_one)
                   (real_lt_zero_one))
                (real_one)))
          (@fic_opp_mult_r
             (real_inv_pos
                (real_one)
                (real_lt_zero_one))
             (real_one))))).
Defined.

(* ===================================================================== *)
(* Section D: Id-form consumer (the paper §6.2 original statement face) *)
(*   - base-theorem use (D2); D0/D1/D3 pruned per the interface-         *)
(*   generation ruling (Wave3 candidates)                                *)
(* ===================================================================== *)

(* D0/D1 registration: fic_id_bridge / fic_id_data are honestly pruned   *)
(* per the interface-generation ruling — the Id-bridge trio requires new *)
(* development not present in the current tree (Wave3 candidate).        *)

(* D2: with the three identifications in place, attention equals the
   Boltzmann distribution (the paper §6.2/§6.3 original Id statement
   face; the proven base theorem attention_is_gibbs_temp at
   S06.AttentionGibbsBridge is applied with all arguments explicit). *)
Theorem fic_attention_is_gibbs_temp_id :
  forall (RI : RealInterfaceEnhanced) (SS : StateSpace RI) (SO : SumOver RI SS),
  forall (spp : forall f : @S01_BaseRing.S RI SS -> @S01_BaseRing.R RI,
            (forall s : @S01_BaseRing.S RI SS,
               @S01_BaseRing.lt RI (@S01_BaseRing.zero RI) (f s)) ->
            @S01_BaseRing.lt RI (@S01_BaseRing.zero RI) (@sum_over_S RI SS SO f)),
  forall (T : @S01_BaseRing.R RI) (T_pos : @S01_BaseRing.lt RI (@S01_BaseRing.zero RI) T),
  forall (D : @S01_BaseRing.R RI) (D_pos : @S01_BaseRing.lt RI (@S01_BaseRing.zero RI) D),
  forall (energy0 z0 : @S01_BaseRing.S RI SS -> @S01_BaseRing.R RI),
  forall (Zp : @S01_BaseRing.lt RI (@S01_BaseRing.zero RI)
            (@Z_thermo RI SS SO D D_pos energy0)),
  Id (@S01_BaseRing.inv_pos RI T T_pos) (@S01_BaseRing.inv_pos RI D D_pos) ->
  (forall s : @S01_BaseRing.S RI SS,
     Id (energy0 s) (@S01_BaseRing.opp RI (z0 s))) ->
  Id (@Z_thermo RI SS SO D D_pos energy0)
     (@partition_function_temp RI SS SO T T_pos z0) ->
  forall s : @S01_BaseRing.S RI SS,
    Id (@softmax_temp RI SS SO spp T T_pos z0 s)
       (@boltzmann_dist_attn RI SS SO spp D D_pos energy0 s).
Proof.
  intros RI SS SO spp T T_pos D D_pos energy0 z0 Zp H1 H2 H3 s.
  exact (@attention_is_gibbs_temp RI SS SO spp T T_pos D D_pos energy0 z0 H1 H2 H3 s).
Qed.

(* ---- audit: assumption faces of the main pieces collected (PA >= 1;
   the out-of-section G3 check is a separate piece) ---- *)
Print Assumptions fic_attention_is_gibbs_temp.
Print Assumptions fic_attention_is_gibbs_temp_id.
Print Assumptions FepIdentificationReal.
