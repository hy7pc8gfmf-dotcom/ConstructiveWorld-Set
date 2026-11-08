(* ConstructiveWorld-Set -- single-point instance-world closure supplies for alignment quantities. *)

(** * uabd_supply_S05_Z_align_pos_unit: closed Z_align positivity over the one-point SumOver instance world.

    Mission.  Instance-level complete resolution of the [Z_align] positivity slot: on the
      unique concrete SumOver instance of the development, the single-point state space
      [uab_ssUnit] with reduction law [uab_soUnit], it supplies closed positivity theorems
      with zero extra premises.  Statement [uabd_uab_soUnit_sum_pos] witnesses strict
      positivity of [sum_over_S] at the instance level, where the abstract interface
      carries no strict positivity field, by reading the definition face of [sum_over_S]
      on the one-point law as a single factor row.  Statement [uabd_Z_align_pos_unit]
      composes that witness with the interface positivity fields [mult_positive] and
      [exp_neg_pos] to close the assembly of [Z_align] positivity.

    Dependencies.  Requires [S01_BaseRing], [S05_AlignmentGRPO], and the [G13] companion
      module of this development; verbatim Require names are carried by the Require
      lines below.

    References.  This development, uabd_supply_S05_Z_align_pos_unit.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" uabd_supply_S05_Z_align_pos_unit.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 00015ff4]. *)
Require Import S01_BaseRing.
Require Import S05_AlignmentGRPO.
Require Import UpAblT13c_G13.

(* strict positivity supplied on the single-point SumOver instance: the abstract
   interface carries no strict positivity field, so this property is witnessed
   at the instance level *)
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

(* closed form: Z_align positivity with zero extra premises, on the single-point
   instance world, with the whole chain in the development *)
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
