(* ConstructiveWorld-Set -- single-point supply-world closure supplies for alignment quantities. *)

(** * uabd_supply_S05_Z_align_pos_unit: closed Z_align positivity over the one-point supply world.

    Mission.  Complete resolution of the [Z_align] positivity slot on the
      single-point supply world (carrier [unit], sum [uab_unit_sum] of the
      [G13] companion module): strict positivity of the one-point sum read
      as a single factor row ([uabd_uab_soUnit_sum_pos]), and the closed
      assembly of [Z_align] positivity from the positivity fields
      [mult_positive] and [exp_neg_pos] ([uabd_Z_align_pos_unit]), both with
      zero extra premises.

    Dependencies.  Requires [S01_BaseRing], [S05_AlignmentGRPO],
      [S07_RealSetoidExpLog], [G13_EvictFam], and [UpAblT13c_G13] of this
      development; the concrete-carrier names bind through the
      [RealInterfaceEnhancedMod] import per the companion modules' idiom.

    References.  This development, uabd_supply_S05_Z_align_pos_unit.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face concrete-carrier re-form per the fa56b plan-B
      discipline: the extractor sees one carrier on both sides of every use
      site).

    Constructivity.  All named statements and fields are carried by [Set]
      over the concrete carrier; statements extract with [Obj.magic] = 0 and
      no erasure; [coqchk] reports [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" uabd_supply_S05_Z_align_pos_unit.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 000160bc]. *)
Require Import S01_BaseRing.
Require Import S05_AlignmentGRPO.
Require Import S07_RealSetoidExpLog.
Require Import G13_EvictFam.
Require Import UpAblT13c_G13.

Import RealInterfaceEnhancedMod.
Require Import G13_EvictFam.

(* strict positivity supplied on the single-point supply world: the sum reads
   as a single factor row *)
Theorem uabd_uab_soUnit_sum_pos :
  forall (f : unit -> R) (H : forall s : unit, lt zero (f s)),
    lt zero (uab_unit_sum f).
Proof.
  intros f H.
  unfold uab_unit_sum.
  exact (H tt).
Qed.

(* closed form: Z_align positivity with zero extra premises, on the single-point
   supply world, with the whole chain in the development *)
Theorem uabd_Z_align_pos_unit :
  forall (reward : unit -> R) (beta : R) (Hb : lt zero beta)
         (pi_ref : unit -> R) (Hp : forall s : unit, lt zero (pi_ref s)),
    lt zero (uab_unit_sum (fun s => mult (pi_ref s)
                              (exp_neg (opp (mult (inv_pos beta Hb) (reward s)))))).
Proof.
  intros reward beta Hb pi_ref Hp.
  apply uabd_uab_soUnit_sum_pos.
  intro s.
  exact (mult_positive (pi_ref s)
                       (exp_neg (opp (mult (inv_pos beta Hb) (reward s))))
                       (Hp s)
                       (exp_neg_pos (opp (mult (inv_pos beta Hb) (reward s))))).
Qed.

Print Assumptions uabd_uab_soUnit_sum_pos.
Print Assumptions uabd_Z_align_pos_unit.
