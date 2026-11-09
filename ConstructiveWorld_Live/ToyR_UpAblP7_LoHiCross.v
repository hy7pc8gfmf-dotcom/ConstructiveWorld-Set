(* ConstructiveWorld-Set -- softmax bound instances at unit temperature and unit spread. *)

(** * ToyR_UpAblP7_LoHiCross: toy instantiations of the P7 LoHi softmax bounds.

    Mission.  Instantiates the source softmax bounds at temperature 1 and
      spread 1 over an abstract positive exponential family: the crossing
      instance [uahlc_lo_lt_one_hi_one] of [lt lo one] with [lt one hi], the
      bounded instance [uahlc_omd_bounded_one] of [lt zero (minus one (mult
      lo lo))] with its upper side, and the full chain [uahlc_lo_one_hi_full].

    Dependencies.  Requires [S01_BaseRing], [S02_CauchyComplete],
      [S03_QExp], [S07_RealSetoidExpLog], [Paper7Ablation],
      [P7BoundedSoftmaxDeep], [ToyR_UpAblP7_LoHiSqueeze] of
      this development.

    References.  This development, ToyR_UpAblP7_LoHiCross.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" ToyR_UpAblP7_LoHiCross.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 000160bc] (9.3, od-verified). *)
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import Paper7Ablation.
Require Import P7BoundedSoftmaxDeep.
Require Import ToyR_UpAblP7_LoHiSqueeze.

(* Carrier adaptation (cure note, round-1 compile gate).  This tree's
   RealInterfaceEnhancedSetoid is the zero-argument Class over the
   concrete [Real] carrier (S07_RealSetoidExpLog, inside the
   RealInterfaceEnhancedMod module, with the global instance
   RealEnhancedReal); the source binder pair
     Context {R : Set} {RI : RealInterfaceEnhancedSetoid R}
   is therefore removed, [R] is bound to [Real] by abbreviation and the
   interface fields resolve through the concrete delta-equal field values
   of the global instance (ToyR_UpAblP7_LoHiSqueeze round-2 cure, same
   family, same bank).  All statement names and statement faces are kept
   verbatim; no Obj.magic, no Prop-ification. *)
Abbreviation R := Real.
(* Instance activated without importing the field short names: the section
   bank addresses the fields by their concrete delta-equal S02/S03/S07
   names (M34b canon). *)
Existing Instance RealInterfaceEnhancedMod.RealEnhancedReal.

(* ############ The LoHi instance bounds and the full sandwich chain ######## *)
(* The section signature is the union of the two source-section bundles,
   the RI bundle plus the four exponential-family items, at temperature 1 and
   spread 1: [one_pos] supplies [inv_pos], so [invT := inv_pos one one_pos] is
   the concrete reciprocal temperature; the exponential family [expf] stays
   abstract, as the development has no concrete instance yet. *)

Section UahlCross.

(* Binders (R : Set) and (RI : RealInterfaceEnhancedSetoid R) removed:
   zero-argument Class; carrier fixed by the top abbreviation R := Real, the
   fields resolving through the global instance RealEnhancedReal. *)
(* The section rebinds the interface projections as scoped [Let] synonyms of
   the concrete delta-equal S02/S03/S07 field values of the global instance
   (M34b canon), as in the UahlSbInst section of ToyR_UpAblP7_LoHiSqueeze. *)
Let zero : R := real_zero.
Let one : R := real_one.
Let plus : R -> R -> R := real_plus.
Let mult : R -> R -> R := real_mult.
Let opp : R -> R := real_opp.
Let lt : R -> R -> Set := real_lt.
Let le : R -> R -> Set := real_le.
Let req : R -> R -> Set := real_eq.
Let inv_pos : forall x : R, lt zero x -> R := real_inv_pos.
Let req_sym := real_eq_sym.
Let req_trans := real_eq_trans.
Let plus_comm := real_plus_comm.
Let plus_zero := real_plus_zero.
Let plus_opp := real_plus_opp.
Let mult_comm := real_mult_comm.
Let mult_one := real_mult_one.
Let mult_zero := real_mult_zero.
Let mult_positive := real_mult_positive.
Let lt_trans := real_lt_trans.
Let lt_id_l := RealSetoid.real_lt_id_l.
Let lt_id_r := RealSetoid.real_lt_id_r.
Let le_refl := real_le_refl.
Let lt_mult_compat := (fun a b c Hc Hab => real_mult_lt_compat a b c Hab Hc).
Let lt_zero_opp := real_lt_zero_opp.
Let inv_pos_pos := real_inv_pos_pos.
Let one_pos : lt zero one := real_lt_zero_one.

(* The exported form of [uahl_omd_bounded] carries one further trailing
   premise, so the section declares [lpc] explicitly. *)
Variable lpc : forall a b c d : R, lt a b -> le c d -> lt (plus a c) (plus b d).

Variable expf : R -> R.
Variable expf_pos : forall x : R, lt zero (expf x).
Variable expf_zero : req (expf zero) one.
Variable expf_mono_lt : forall a b : R, lt a b -> lt (expf a) (expf b).

Let invT := inv_pos one one_pos.
Let lo := expf (mult invT (opp one)).
Let hi := expf (mult invT one).

(* The section shadows [minus] with the verbatim expansion [plus a (opp b)],
   kept in section scope by the [Let] form. *)
Let minus (a b : R) : R := plus a (opp b).

(* First bound: the instance form of the source theorem lhs_lo_lt_one_hi.  The
   fully explicit application supplies both source-section bundles -- the RI
   bundle, temperature 1 and spread 1 (each by [one_pos]) and the
   exponential-family quadruple -- closing on
   [ToyR_UpAblP7_LoHiSqueeze.uahl_lo_lt_one_hi]. *)
Theorem uahlc_lo_lt_one_hi_one : And (lt lo one) (lt one hi).
Proof.
  exact (@uahl_lo_lt_one_hi one one_pos one one_pos
             expf expf_zero expf_mono_lt).
Qed.

(* Second bound: the instance form of the source theorem lhs_omd_bounded.  The
   fully explicit application supplies the whole bundle, including the trailing
   [lpc] premise of the exported form, and builds the instance with
   kappa = 1 - delta-star lying in (0, 1) in one step. *)
Theorem uahlc_omd_bounded_one :
  And (lt zero (minus one (mult lo lo)))
      (lt (minus one (mult lo lo)) one).
Proof.
  exact (@uahl_omd_bounded lpc one one_pos one one_pos
             expf expf_pos expf_zero expf_mono_lt).
Qed.

(* Third bound: the full instance chain of [lt lo one], [lt one hi] and
   [lt lo hi].  The left side reuses the left side of the first bound; the
   middle side turns the [req] face of [p7d_hi_gt_one] into [lt] inline; the
   right side reapplies [uahl_lo_lt_hi_one] with the RI bundle and the
   exponential-family quadruple given explicitly. *)
Theorem uahlc_lo_one_hi_full :
  And (lt lo one) (And (lt one hi) (lt lo hi)).
Proof.
  split.
  - exact (fst uahlc_lo_lt_one_hi_one).
  - split.
    + (* the [req] face of [p7d_hi_gt_one] inlines into [lt] in the proof body *)
      exact (lt_id_l one (expf zero) (expf (mult invT one))
               (req_sym (expf zero) one expf_zero)
               (expf_mono_lt zero (mult invT one)
                  (mult_positive invT one (inv_pos_pos one one_pos) one_pos))).
    + exact (@uahl_lo_lt_hi_one expf expf_zero expf_mono_lt).
Qed.

End UahlCross.

(* ---- assumption audit: one Print Assumptions per statement ---- *)
Print Assumptions uahlc_lo_lt_one_hi_one.
Print Assumptions uahlc_omd_bounded_one.
Print Assumptions uahlc_lo_one_hi_full.
