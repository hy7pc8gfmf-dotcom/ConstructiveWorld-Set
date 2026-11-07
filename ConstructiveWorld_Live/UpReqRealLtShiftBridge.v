(* ConstructiveWorld-Set — Real-carrier strict-step (lt) resolution bridges. *)
(** * UpReqRealLtShiftBridge: strict-step instances resolved at the Real carrier.

    Mission.  (1) The weak positivity slot ([real_le 0 1]) lifted to
      [lt 0 1] through the Or decomposition of [real_le]
      ([rlsb_lt_zero_one_of_le]); (2) [0 < 1] shifted on both sides by
      +one to give [1 < 2] ([rlsb_lt_one_two], plus the weak-slot
      full-chain form [rlsb_lt_one_two_of_le]); (3) the Real-carrier
      instantiation of the mixed lt/le shift bridge
      ([rlsb_lt_plus_compat_lt_le]), literally isomorphic to the
      [lt_plus_compat_lt_le] slots of UpReqCauchy/UpEntropyGain.

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs]; requires
      [S01_BaseRing] through [S15_TailFEPUp] of this development.

    References.  This development, UpReqRealLtShiftBridge.v, the baseline
      module in ConstructiveWorld-Main whose statement names are carried
      over here verbatim; the abstract req interfaces carry no Or
      decomposition for le, so the strict steps cannot close at the
      interface level, while the Real layer [real_le = Or real_lt real_eq]
      (the S01 Set-layer Or, assembled in S02) is destructible and the
      slots resolve here (same statements as UpReqCauchy/UpEntropyGain).

    Constructivity.  The eq branch closes by the pointwise zero-is-not-one
      contradiction with no classical step; all statements are Set-carried;
      [rlsb_zero_ne_one] and [rlsb_lt_shift_rt] are auxiliary lemmas.

    Build.  [coqc -native-compiler no -q -Q ConstructiveWorld_Live ""
      UpReqRealLtShiftBridge.v] compiles cleanly (exit 0); the artifact
      starts with [436f7121 00015ff4]. *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
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

(* ============ Auxiliary lemma: zero is not one (a pointwise contradiction from real_eq zero one) ============ *)
(* real_eq x y := forall eps, 0<eps -> sigT N, forall n>=N, *)
(* Qabs (proj1 x n - proj1 y n) < eps (S02:396). With zero the constant-0 *)
(* sequence and one the constant-1 sequence, eps := 1 gives the pointwise *)
(* Q-layer contradiction 1 < 1 — a constructive conclusion, no classical step. *)
Lemma rlsb_zero_ne_one : Not (real_eq real_zero real_one).
Proof.
  intro H.
  assert (Heps : QltT 0 1%Q) by (apply Qlt_to_QltT; compute; reflexivity).
  destruct (H 1%Q Heps) as [N HN].
  assert (Hbad : QltT (Qabs (0%Q - 1%Q)) 1%Q).
  { exact (HN N%nat (NatLe_lift N%nat N%nat (le_n N%nat))). }
  unfold QltT in Hbad.
  apply QltT_to_Qlt in Hbad.
  compute in Hbad.
  discriminate Hbad.
Qed.

(* ============ (1) Lifting the weak slot: real_le zero one gives lt zero one ============ *)
(* Resolution at the Real-carrier layer for weak positivity slots of the le *)
(* shape (as req_two_pos): decompose the Or of real_le — the lt branch is *)
(* extracted directly; the eq branch closes by the zero-is-not-one *)
(* contradiction (an empty match on False produces the Set-layer lt; the *)
(* S02:3172 match-end precedent). The premise is carried. *)
Theorem rlsb_lt_zero_one_of_le :
  real_le real_zero real_one -> real_lt real_zero real_one.
Proof.
  intro Hle.
  unfold real_le in Hle.
  destruct Hle as [Hlt | Heq].
  - exact Hlt.
  - exact (match rlsb_zero_ne_one Heq with end).
Qed.

(* ============ Auxiliary lemma: right shift, lt a b gives lt (a+d) (b+d) ============ *)
(* The left-shift primitive real_lt_plus_translate (S07:6085) only adds d *)
(* on the left; the right shift goes through two comm reshapes: *)
(* (a+d) == (d+a) < (d+b) == (b+d). *)
Lemma rlsb_lt_shift_rt : forall a b d : Real,
  real_lt a b -> real_lt (real_plus a d) (real_plus b d).
Proof.
  intros a b d Hab.
  apply (RealSetoid.real_lt_id_l (real_plus a d) (real_plus d a)
           (real_plus b d) (real_plus_comm a d)).
  apply (RealSetoid.real_lt_id_r (real_plus d a) (real_plus d b)
           (real_plus b d) (real_plus_comm d b)).
  exact (real_lt_plus_translate d a b Hab).
Qed.

(* ============ (2) 1 < 2: the pure-lt both-sides shift (+one) of 0 < 1 ============ *)
(* two := one + one (the delta-expanded form of sfc_two, verbatim). *)
(* Shifting 0 < 1 on the left by +one gives 1 + 0 < 1 + 1; the plus_zero *)
(* reshape closes 1 < 1 + 1. *)
Theorem rlsb_lt_one_two : real_lt real_one (real_plus real_one real_one).
Proof.
  apply (RealSetoid.real_lt_id_l real_one
           (real_plus real_one real_zero)
           (real_plus real_one real_one)
           (real_eq_sym (real_plus real_one real_zero) real_one
                        (real_plus_zero real_one))).
  exact (real_lt_plus_translate real_one real_zero real_one real_lt_zero_one).
Qed.

(* ============ (2, weak) The full-chain resolution: the weak slot gives 1 < 2 (the resolution form of host slot 5) ============ *)
Theorem rlsb_lt_one_two_of_le :
  real_le real_zero real_one -> real_lt real_one (real_plus real_one real_one).
Proof.
  intro Hle.
  apply (RealSetoid.real_lt_id_l real_one
           (real_plus real_one real_zero)
           (real_plus real_one real_one)
           (real_eq_sym (real_plus real_one real_zero) real_one
                        (real_plus_zero real_one))).
  exact (real_lt_plus_translate real_one real_zero real_one
           (rlsb_lt_zero_one_of_le Hle)).
Qed.

(* ============ (3) The mixed-shift bridge, instantiated at the Real carrier ============ *)
(* The statement is literally isomorphic to the lt_plus_compat_lt_le slot of *)
(* UpReqCauchy.v:123 / UpEntropyGain.v:86: forall a b c d, lt a b -> le c d -> *)
(* lt (plus a c) (plus b d) (the req-to-real carrier instantiation). *)
(* The Or decomposition of real_le: the lt branch = left shift of a + right *)
(* shift of b + trans; the eq branch = eq_plus_compat transport (c == d) + *)
(* the right shift. *)
Theorem rlsb_lt_plus_compat_lt_le : forall a b c d : Real,
  real_lt a b -> real_le c d -> real_lt (real_plus a c) (real_plus b d).
Proof.
  intros a b c d Hab Hcd.
  unfold real_le in Hcd.
  destruct Hcd as [Hcdlt | Hcdeq].
  - apply (real_lt_trans (real_plus a c) (real_plus a d) (real_plus b d)).
    + exact (real_lt_plus_translate a c d Hcdlt).
    + exact (rlsb_lt_shift_rt a b d Hab).
  - apply (RealSetoid.real_lt_id_l (real_plus a c) (real_plus a d)
             (real_plus b d)).
    + exact (RealSetoid.real_eq_plus_compat a c a d (real_eq_refl a) Hcdeq).
    + exact (rlsb_lt_shift_rt a b d Hab).
Qed.

(* ============ Assumption audits (all four statements must read Closed) ============ *)
Print Assumptions rlsb_lt_zero_one_of_le.
Print Assumptions rlsb_lt_one_two.
Print Assumptions rlsb_lt_one_two_of_le.
Print Assumptions rlsb_lt_plus_compat_lt_le.
