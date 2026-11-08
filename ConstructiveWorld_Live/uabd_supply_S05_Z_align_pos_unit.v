(* ConstructiveWorld-Set -- Z_align positivity: single-point instance world closure supply. *)

(** * uabd_supply_S05_Z_align_pos_unit: instance-level full resolution of the Z_align_pos slot.

    Mission.  On the unique concrete SumOver instance of the library
      ([uab_ssUnit] / [uab_soUnit], the single-point state space), strict
      positivity is closed with zero additional premises: (1)
      [uabd_uab_soUnit_sum_pos], the instance-level witness of the strict
      positivity the abstract interface does not carry (the [sum_over_S]
      definition face of [uab_soUnit] is a single factor row, so the
      pointwise premise substitutes directly); (2) [uabd_Z_align_pos_unit]
      closes by composing (1) with [mult_positive] and [exp_neg_pos].

    Dependencies.  S01_BaseRing (the [RealInterfaceEnhanced] class fields),
      S05_AlignmentGRPO ([Z_align]), and the G13 companion file (supplying
      [uab_ssUnit], [uab_soUnit], [uab_ssUnit_elem], each named in the
      Require lines).

    References.  The G13 companion file of this development; same-family
      precedent: the two-statement single-point resolution of partition
      positivity (companion library statements at lines 130 and 141).

    Constructivity.  All statements carried at the [Set] layer; proofs are explicit
      construction chains (definition-face unfolding + pointwise substitution +
      field composition), with no axioms, zero admission vocabulary, no classical logic.

    Build.  [coqc -q -Q <main vo tree> "" -Q . "" uabd_supply_S05_Z_align_pos_unit.v]
      with literal COQLIB/ROCQLIB environment exports; the artifact starts with
      [436f7121 000160bc]. *)
Require Import S01_BaseRing.
Require Import S05_AlignmentGRPO.
Require Import UpAblT13c_G13.

(* (1) the strict-positivity supply of the single-point SumOver instance *)
(*   (the abstract interface carries no strict-positivity field, so this *)
(*   file is the instance-level witness of that property) *)
Theorem uabd_uab_soUnit_sum_pos :
  forall {RI0 : RealInterfaceEnhanced}
         (f : @S RI0 (@uab_ssUnit (@RI_base RI0)) -> @R RI0),
    (forall s : @S RI0 (@uab_ssUnit (@RI_base RI0)), lt zero (f s)) ->
    lt zero (@sum_over_S RI0 (@uab_ssUnit (@RI_base RI0))
               (@uab_soUnit (@RI_base RI0)) f).
Proof.
  intros RI0 f H.
  exact (H (@uab_ssUnit_elem (@RI_base RI0))).
Qed.

(* (2) the closed form: Z_align positivity with zero additional premises *)
(*   (the single-point instance world; the whole chain lives in the library) *)
Theorem uabd_Z_align_pos_unit :
  forall {RI0 : RealInterfaceEnhanced}
         (reward : @S RI0 (@uab_ssUnit (@RI_base RI0)) -> @R RI0)
         (beta : @R RI0) (Hb : lt zero beta)
         (pi_ref : @S RI0 (@uab_ssUnit (@RI_base RI0)) -> @R RI0)
         (Hp : forall s : @S RI0 (@uab_ssUnit (@RI_base RI0)), lt zero (pi_ref s)),
    lt zero (@Z_align RI0 (@uab_ssUnit (@RI_base RI0)) (@uab_soUnit (@RI_base RI0))
                    reward beta Hb pi_ref).
Proof.
  intros RI0 reward beta Hb pi_ref Hp.
  unfold Z_align.
  apply uabd_uab_soUnit_sum_pos.
  intro s.
  exact (mult_positive (pi_ref s)
                       (@exp_neg RI0 (opp (mult (inv_pos beta Hb) (reward s))))
                       (Hp s)
                       (exp_neg_pos (opp (mult (inv_pos beta Hb) (reward s))))).
Qed.

Print Assumptions uabd_uab_soUnit_sum_pos.
Print Assumptions uabd_Z_align_pos_unit.
