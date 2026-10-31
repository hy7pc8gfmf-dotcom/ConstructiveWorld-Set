(* ========================================================================= *)
(*  uabd_supply_S05_Z_align_pos.v - positivity of the closed-form alignment  *)
(*  partition function: a general-interface-layer companion supply theorem   *)
(* ========================================================================= *)
(*   Mission. Companion supply for the Z_align_pos slot of the Alignment     *)
(*   node of S05_AlignmentGRPO (the statement lt zero Z_align). Z_align is   *)
(*   a closed-form definition: the sum of the pointwise products of the      *)
(*   pi_ref factor with the exp_neg factor. Every summand is pointwise       *)
(*   positive as a direct corollary of the interface positivity fields       *)
(*   (mult_positive, exp_neg_pos). This module resolves that slot as a       *)
(*   theorem via the two-step chain of the general sum-preserves-positivity  *)
(*   premise Hsum: pointwise positivity assembly, then instantiation of the  *)
(*   sum rule.                                                               *)
(*   Dependencies. S01_BaseRing (the RealInterfaceEnhanced and SumOver       *)
(*   class fields); S05_AlignmentGRPO (the closed-form definition of         *)
(*   Z_align in the form exported after its section closes). No further      *)
(*   Require.                                                                *)
(*   References. Baseline module uabd_supply_S05_Z_align_pos.v of the        *)
(*   ConstructiveWorld-Main tree; the statement is carried over verbatim     *)
(*   (census 1=1 ordered identity; the statement face is already canonical   *)
(*   in Set form, zero rewrites).                                            *)
(*   Constructivity. The statement lives entirely in Set: lt is the          *)
(*   Set-valued order of the real interface (lt : R -> R -> Set), and the    *)
(*   proof is an explicit construction chain with zero axioms, zero          *)
(*   admissions and no classical logic. The slot statement is supplied       *)
(*   non-trivially, citing the real in-library field chain instead of        *)
(*   restating assumptions; extraction yields no Obj.magic.                  *)
(*   Build. rocq c -native-compiler no -q -Q . "" uabd_supply_S05_Z_align_pos.v *)
(*   (Rocq 9.1 toolchain; single -Q root with an empty logical prefix).      *)

Require Import S01_BaseRing.
Require Import S05_AlignmentGRPO.

Theorem uabd_Z_align_pos_of_sum_pos :
  forall {RI : RealInterfaceEnhanced} {SS : StateSpace RI} {SO : SumOver RI SS}
         (reward : @S RI SS -> @R RI) (beta : @R RI)
         (Hb : lt zero beta) (pi_ref : @S RI SS -> @R RI)
         (Hp : forall s : @S RI SS, lt zero (pi_ref s))
         (Hsum : forall f : @S RI SS -> @R RI,
                 (forall s : @S RI SS, lt zero (f s)) ->
                 lt zero (@sum_over_S RI SS SO f)),
    lt zero (Z_align reward beta Hb pi_ref).
Proof.
  intros RI SS SO reward beta Hb pi_ref Hp Hsum.
  unfold Z_align.
  apply Hsum.
  intro s.
  exact (mult_positive (pi_ref s)
                       (@exp_neg RI (opp (mult (inv_pos beta Hb) (reward s))))
                       (Hp s)
                       (exp_neg_pos (opp (mult (inv_pos beta Hb) (reward s))))).
Qed.

Print Assumptions uabd_Z_align_pos_of_sum_pos.
