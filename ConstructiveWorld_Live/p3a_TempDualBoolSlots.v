(* ConstructiveWorld-Set — a two-point state-space instantiation of the four second-law sum slots. *)

(** * p3a_TempDualBoolSlots: the four quantified sum slots of the second
      law, instantiated on a two-point state space.

    Mission.  The minimal state-space instantiation for the second-law
      receiver upgrade: state space [bool], summation
      [p3a_bsum f := f true + f false]; the four sum slots
      [p3a_bsum_pos]/[p3a_bsum_ext]/[p3a_bsum_lin]/[p3a_bsum_add] carry
      genuine proofs, [p3a_bsum_list_feed] bridges to the list carrier,
      and the KL decomposition [real_entropy_deficit_kl_temp] is
      instantiated at full arity as [p3a_two_state_entropy_deficit_kl_zero].
      The list-carrier face is closed in [SecondLawQuantified]; the
      remaining slots are exactly any state-space instantiation.

    Dependencies.  Stdlib [QArith.QArith] and [Extraction] (the
      end-of-file extraction check); requires [S01_BaseRing] through
      [S15_TailFEPUp], [UpReqTempDefs], [UpReqEntropyDeficitTemp]; no
      [Require] beyond the original file.

    References.  This development, the ConstructiveWorld-Main baseline
      module of the same name; Theorem 10.13, the [S05_AlignmentGRPO] slots.

    Constructivity.  Set-layer statements, no classical logic, every
      proof closed by [Qed].  Disclosure: [p3a_bsum_ext] is a direct
      two-term assembly (explicit-witness caliber), faces unchanged;
      the end-of-file [Print Assumptions] block retained.

    Build.  [coqc -native-compiler no -q -Q . "" p3a_TempDualBoolSlots.v]
      compiles cleanly (exit 0), artifact bytes [436f7121 000160bc]. *)

From Stdlib Require Import QArith.QArith.
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
Require Import UpReqTempDefs.
Require Import UpReqEntropyDeficitTemp.

(* ---- The two-point finite-enumeration state space and its summation functional. ---- *)

Definition p3a_bsum (f : bool -> Real) : Real :=
  real_plus (f true) (f false).

(* ---- Slot 1, [sumpos]: positivity preservation. ---- *)

Lemma p3a_bsum_pos : forall f : bool -> Real,
  (forall s : bool, real_lt real_zero (f s)) ->
  real_lt real_zero (p3a_bsum f).
Proof.
  intros f Hf. unfold p3a_bsum.
  apply (real_eq_lt_lt real_zero (real_plus real_zero real_zero)).
  - apply real_eq_sym. apply real_plus_zero.
  - exact (real_lt_plus_compat real_zero (f true) real_zero (f false)
             (Hf true) (Hf false)).
Qed.

(* ---- Slot 2, [sumext]: extensionality. ---- *)

Lemma p3a_bsum_ext : forall f g : bool -> Real,
  (forall s : bool, real_eq (f s) (g s)) ->
  real_eq (p3a_bsum f) (p3a_bsum g).
Proof.
  intros f g Hfg.
  assert (Ht : real_eq (f true) (g true)).
  { exact (Hfg true). }
  assert (Hff : real_eq (f false) (g false)).
  { exact (Hfg false). }
  unfold p3a_bsum.
  exact (RealSetoid.real_eq_plus_compat (f true) (f false) (g true) (g false) Ht Hff).
Qed.

(* ---- Slot 3, [sumlinear]: linearity (distributivity plus reordering the factor). ---- *)

Lemma p3a_bsum_lin : forall (a : Real) (f : bool -> Real),
  real_eq (p3a_bsum (fun s : bool => real_mult a (f s)))
          (real_mult a (p3a_bsum f)).
Proof.
  intros a f. unfold p3a_bsum.
  apply (real_eq_trans
           (real_plus (real_mult a (f true)) (real_mult a (f false)))
           (real_plus (real_mult (f true) a) (real_mult (f false) a))).
  - apply RealSetoid.real_eq_plus_compat.
    + apply real_mult_comm.
    + apply real_mult_comm.
  - apply (real_eq_trans
             (real_plus (real_mult (f true) a) (real_mult (f false) a))
             (real_mult (real_plus (f true) (f false)) a)).
    + exact (real_distrib_r_local (f true) (f false) a).
    + exact (real_mult_comm (real_plus (f true) (f false)) a).
Qed.

(* ---- Slot 4, [sumadd]: additivity (rearranging four terms by associativity and commutativity). ---- *)

Lemma p3a_bsum_add : forall f g : bool -> Real,
  real_eq (p3a_bsum (fun s : bool => real_plus (f s) (g s)))
          (real_plus (p3a_bsum f) (p3a_bsum g)).
Proof.
  intros f g. unfold p3a_bsum.
  apply (real_eq_trans
           (real_plus (real_plus (f true) (g true))
                      (real_plus (f false) (g false)))
           (real_plus (f true)
                      (real_plus (g true) (real_plus (f false) (g false))))).
  - apply real_eq_sym. apply real_plus_assoc.
  - apply (real_eq_trans
             (real_plus (f true)
                        (real_plus (g true) (real_plus (f false) (g false))))
             (real_plus (f true)
                        (real_plus (f false) (real_plus (g true) (g false))))).
    + apply RealSetoid.real_eq_plus_compat.
      * apply real_eq_refl.
      * (* g true + (f false + g false) == f false + (g true + g false) *)
        apply (real_eq_trans
                 (real_plus (g true) (real_plus (f false) (g false)))
                 (real_plus (real_plus (g true) (f false)) (g false))).
        -- apply real_plus_assoc.
        -- apply (real_eq_trans
                    (real_plus (real_plus (g true) (f false)) (g false))
                    (real_plus (real_plus (f false) (g true)) (g false))).
           ++ apply RealSetoid.real_eq_plus_compat.
              ** apply real_plus_comm.
              ** apply real_eq_refl.
           ++ apply real_eq_sym. apply real_plus_assoc.
    + apply real_plus_assoc.
Qed.

(* ---- The conversion bridge: [bsum] to the [list] sum (the two-point enumeration [[true; false]] as input). ---- *)

Lemma p3a_bsum_list_feed : forall f : bool -> Real,
  real_eq (p3a_bsum f) (real_list_sum bool f (true :: false :: nil)).
Proof.
  intros f. unfold p3a_bsum. cbn [real_list_sum].
  apply (real_eq_trans (real_plus (f true) (f false))
           (real_plus (real_plus (f true) (f false)) real_zero)).
  - apply real_eq_sym. apply real_plus_zero.
  - apply real_eq_sym. apply real_plus_assoc.
Qed.

(* ---- Main statement: loading the entropy-deficit KL decomposition on  *)
(*      the two-point space ([real_entropy_deficit_kl_temp] applied at   *)
(*      full 13-argument arity — the four quantified sum slots of the    *)
(*      second law discharged on the finite-enumeration carrier). ---- *)

Theorem p3a_two_state_entropy_deficit_kl_zero :
  forall (T : Real) (Ht : real_lt real_zero T)
         (energy p : bool -> Real)
         (Hp : forall s : bool, real_lt real_zero (p s)),
    real_eq (p3a_bsum p) real_one ->
    real_eq (p3a_bsum (fun s : bool => real_mult (p s) (energy s)))
            (real_energy_exp_temp bool p3a_bsum p3a_bsum_pos T Ht energy) ->
    real_eq (real_minus_r
               (real_entropy_dist bool p3a_bsum
                  (real_boltzmann_dist_temp bool p3a_bsum p3a_bsum_pos T Ht energy)
                  (real_boltzmann_dist_temp_pos bool p3a_bsum p3a_bsum_pos T Ht energy))
               (real_entropy_dist bool p3a_bsum p Hp))
            (real_KL_temp bool p3a_bsum p3a_bsum_pos T Ht energy p Hp).
Proof.
  intros T Ht energy p Hp Hnormp Henergy.
  exact (real_entropy_deficit_kl_temp bool p3a_bsum p3a_bsum_pos
           p3a_bsum_ext p3a_bsum_lin p3a_bsum_add
           T Ht energy p Hp Hnormp Henergy).
Qed.

(* ---- Verification tail: the Print Assumptions caliber plus the extraction check. ---- *)

Print Assumptions p3a_bsum_add.
Print Assumptions p3a_two_state_entropy_deficit_kl_zero.
Print Assumptions p3a_bsum_list_feed.

From Stdlib Require Import Extraction.
Set Extraction Output Directory ".".
Extraction "p3a_tempdualboolslots.ml" p3a_two_state_entropy_deficit_kl_zero p3a_bsum_list_feed.
