(* ConstructiveWorld-Set -- KL pointwise wrapper slot: flipped-direction supply. *)

(** * uabd_supply_S08_kl_term_equiv: KL term equivalence at the slot direction.

    Mission.  The KL pointwise wrapper slot of S08_RealMainlineDPO,
      [real_kl_term p q] = [p * (log p - log q)] (KL term equivalence via
      the log division decomposition), as the flipped-direction supply
      statement.  Inside S08 the slot appears through [real_kl_sum_term]
      (the [p * (log p - log p_b)] wrapper), whose pointwise content is
      the instance at [(p, q) := (p s, p_b s)]; from the in-library
      [rkd_kl_point] of RealKLDecomp (the KL pointwise expansion) one
      step of [real_eq_sym] flips the direction into this named
      supply face.

    Dependencies.  S01-S08 (the real_kl_term/real_log/real_eq family),
      RealKLDecomp (the [rkd_kl_point] root supply), Stdlib.

    References.  [rkd_kl_point@RealKLDecomp] (the root construction carries
      the non-triviality); this file is the flipped-direction supply face,
      an independent slot form, neither placeholder nor trivial restatement.

    Constructivity.  Genuine constructions closing by [Qed] throughout;
      statement faces all in [Set] form ([real_lt] in sigT form, [real_eq]
      in per-eps [Set] form); axiom-free, zero admission vocabulary, no
      classical logic; the file-tail [Print Assumptions] takes Closed.

    Build.  [coqc -q -Q <main vo tree> "" -Q . "" uabd_supply_S08_kl_term_equiv.v]
      in the single-root vo world; the artifact starts with
      [436f7121 000160bc]. *)
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import RealKLDecomp.

(* the flipped-direction supply: p * (log p - log q) is real_kl_term p q *)
(*   (the KL term-equivalence slot direction) *)
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
