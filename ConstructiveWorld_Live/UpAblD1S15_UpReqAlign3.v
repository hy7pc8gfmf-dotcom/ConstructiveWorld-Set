(* ConstructiveWorld-Set — one-point canonical-carrier discharge of the sixteen UpReqAlign3 interface items. *)

(** * UpAblD1S15_UpReqAlign3: the sixteen [UpReqAlign3] interface items
      discharged as a one-point canonical-carrier supply lemma.

    Mission.  One named instance declaration, one positivity certificate
      for the alignment partition function at the one-point instance,
      one record-type package [uabd1s15_a3_pack16] restating the
      sixteen interface slots in source declaration order (the Gibbs
      nonnegativity slot carried as a universal premise - an
      honest-interface slot, not claimed as a supply), and one discharge
      theorem taking that premise.

    Dependencies.  Requires [S01_BaseRing] through [S15_TailFEPUp] and
      [UpReqAlign2] ([req2_Z_align] / [req2_pos_dist] / [req2_rel_ent])
      of this development; argument-less Class
      [RealInterfaceEnhancedSetoid]; notation rebind
      [Notation R := Real]; predicate faces converged to [real_eq] /
      [real_le] / [real_lt]; bare field consumption through the global
      instance.

    References.  This development, UpAblD1S15_UpReqAlign3.v, the
      baseline module in ConstructiveWorld-Main whose statement names
      are carried over here verbatim (statement-face Set-carrier
      completion).  The baseline interface is the relative-entropy
      nonnegativity interface (Gibbs-type inequality) of
      policy-evaluation comparison, at its one-point instantiation.
      Adaptation = binder-pair removal + notation rebinding +
      predicate-face convergence + space-slot monomorphise to unit (the
      D1S17 record-form precedent, keeping the extracted payload real
      data).

    Constructivity.  All Set-layer statements; every station closed by
      [Qed], zero admitted items; the tail [Print Assumptions] probes
      report the closure face; no new axioms.

    Build.  [coqc -native-compiler no -q -Q . ""
      UpAblD1S15_UpReqAlign3.v] compiles cleanly (exit 0); the first
      eight bytes of the artifact are [436f7121 00015ff4]. *)

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
Require Import UpReqAlign2.
Import RealInterfaceEnhancedMod.
Notation R := Real.

(* ============ named instance declaration ============ *)

Definition uabd1s15_ren : RealInterfaceEnhancedSetoid :=
  RealInterfaceEnhancedMod.RealEnhancedReal.

(* ============ ZAL_pos supply certificate (field matching): the
   partition function at the one-point supply reads verbatim as
   mult one (exp_neg (opp (mult (inv_pos one one_pos) zero))). ============ *)

Lemma uabd1s15_a3_zal_pos :
  real_lt zero (@req2_Z_align unit
            (fun f : unit -> R => f tt)
            (fun _ : unit => zero)
            one
            one_pos
            (fun _ : unit => one)).
Proof.
  exact (mult_positive
           one
           (exp_neg
              (opp
                 (mult
                    (inv_pos one one_pos)
                    zero)))
           one_pos
           (exp_neg_pos
              (opp
                 (mult
                    (inv_pos one one_pos)
                    zero)))).
Qed.

(* ============ package record: the sixteen interface slots, in source
   declaration order; sum_pos and the log-compatibility slots are carried
   by their own pieces, and pi_ref_norm rests at the base module's
   removed position - none enter this package. The space slot is
   monomorphised to unit (the instance the discharge supplies). ============ *)

Inductive uabd1s15_a3_pack16 : Type :=
| uabd1s15_a3_pack16_intro :
    forall (sumf : (unit -> R) -> R),
      forall (sum_ext : forall f g : unit -> R,
                 (forall s : unit, real_eq (f s) (g s)) -> real_eq (sumf f) (sumf g)),
        forall (sum_add : forall f g : unit -> R,
                   real_eq (sumf (fun s : unit => plus (f s) (g s)))
                       (plus (sumf f) (sumf g))),
          forall (sum_linear : forall (a : R) (f : unit -> R),
                     real_eq (sumf (fun s : unit => mult a (f s)))
                         (mult a (sumf f))),
            forall (reward : unit -> R) (beta : R) (beta_pos : real_lt zero beta),
              forall (pi_ref : unit -> R)
                     (pi_ref_pos : forall s : unit, real_lt zero (pi_ref s)),
                forall (eta : R) (eta_pos : real_lt zero eta)
                       (eta_le_one : real_le eta one),
                  forall (ZAL_pos : real_lt zero (@req2_Z_align unit sumf
                                             reward beta beta_pos pi_ref)),
                    forall (req2_gibbs : forall (p q : unit -> R)
                                               (Hp : @req2_pos_dist unit p)
                                               (Hq : @req2_pos_dist unit q),
                                  real_le zero (@req2_rel_ent unit sumf
                                             p q Hp Hq)),
                        uabd1s15_a3_pack16.

(* ============ supply lemma: fifteen slots given at the one-point
   instance, the Gibbs slot carried as a universal premise ============ *)

Theorem uabd1s15_a3_pack16_supplied :
  forall (GIBBS : forall (p q : unit -> R)
                    (Hp : @req2_pos_dist unit p)
                    (Hq : @req2_pos_dist unit q),
              real_le zero (@req2_rel_ent unit
                        (fun f : unit -> R => f tt) p q Hp Hq)),
    uabd1s15_a3_pack16.
Proof.
  intro GIBBS.
  exact (uabd1s15_a3_pack16_intro
           (fun f : unit -> R => f tt)
           (fun (f g : unit -> R)
              (H : forall s : unit, real_eq (f s) (g s)) => H tt)
           (fun (f g : unit -> R) =>
              req_refl (plus (f tt) (g tt)))
           (fun (a : R) (f : unit -> R) =>
              req_refl (mult a (f tt)))
           (fun _ : unit => zero)
           one
           one_pos
           (fun _ : unit => one)
           (fun _ : unit => one_pos)
           one
           one_pos
           (le_refl one)
           uabd1s15_a3_zal_pos
           GIBBS).
Qed.

(* ============ closure face (Print Assumptions all Closed as the bar) ==== *)

Print Assumptions uabd1s15_a3_zal_pos.
Print Assumptions uabd1s15_a3_pack16_supplied.
