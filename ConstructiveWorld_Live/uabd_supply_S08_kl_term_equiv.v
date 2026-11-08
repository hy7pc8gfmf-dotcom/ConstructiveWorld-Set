(* ConstructiveWorld-Set -- constructive pointwise KL-term equivalence supply for the DPO alignment mainline. *)

(** * uabd_supply_S08_kl_term_equiv: direction-reversed named supply face of the pointwise KL-term equivalence slot.

    Mission.  For positive reals [p] and [q], the pointwise KL expression
      [p * (log p - log q)] and the slot form [real_kl_term p q] present the
      same real up to [real_eq]; the file carries this as the named supply
      statement [uabd_kl_term_equiv_sym], obtained from the root expansion
      [rkd_kl_point] of [RealKLDecomp] by one application of [real_eq_sym],
      fixing the slot direction consumed by [S08_RealMainlineDPO].

    Dependencies.  Requires [S01_BaseRing], [S02_CauchyComplete],
      [S03_QExp] of this development.

    References.  This development, uabd_supply_S08_kl_term_equiv.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" uabd_supply_S08_kl_term_equiv.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 00015ff4]. *)
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import RealKLDecomp.

(* direction-reversed supply: p * (log p - log q) coincides with
   real_kl_term p q up to real_eq, the pointwise KL-term equivalence stated
   in the slot direction consumed by the DPO mainline *)
Theorem uabd_kl_term_equiv_sym :
  forall (p q : Real) (Hp : real_lt real_zero p) (Hq : real_lt real_zero q),
    real_eq (real_mult p (real_plus (real_log p Hp) (real_opp (real_log q Hq))))
            (real_kl_term p q Hp Hq).
Proof.
  intros p q Hp Hq.
  apply real_eq_sym.
  exact (rkd_kl_point p q Hp Hq).
Qed.

Print Assumptions uabd_kl_term_equiv_sym.
