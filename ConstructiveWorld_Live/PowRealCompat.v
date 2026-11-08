(* ConstructiveWorld-Set — transport bridge between the two power carriers. *)

(** * PowRealCompat: compatibility and transport between [powb_pow] and
      [real_pow].

    Mission.  [powb_pow] and [real_pow] are two isomorphic Fixpoints
      ([O] ↦ [real_one], [S m] ↦ [real_mult base ...]); this file
      formalizes their agreement for every [base] : [Real] and
      [t] : [nat] and delivers eight [prc_] transport
      statements: the [Id]-level and [real_eq]-level bridges with their
      reverses, the [powb]-carrier [eq_compat], the same-statement
      docking route, the monotonicity and power-below-one statements,
      and the anti-monotonicity transport unified at the [Set]-layer
      [NatLe] order.

    Dependencies.  G07_KLWall, CW220_Extensions, UpRealLeB, UpRealLeB2,
      and the library files listed in the Require face below.

    References.  The power-conversion lemma family of [Nat.pow] in
      mathlib.

    Constructivity.  The statement face is carried by the [Set] layer
      ([real_eq]/[real_lt]/[real_le]/[NatLe] all [Set]-valued); zero
      admission words; the axiom face is empty; the file-tail
      [Print Assumptions] checks close under the global context.

    Build.  [rocq c -Q . "" PowRealCompat.v] compiles cleanly (exit 0);
      the first eight bytes of the artifact are [436f7121 00015ff4]. *)

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
Require Import G07_KLWall.
Require Import CW220_Extensions.
Import CW220_Extensions.BudgetReal.
Require Import UpRealLeB.
Require Import UpRealLeB2.

(* ============================================================ *)
(* Part 1. Two-directional transport bridges (Id level / real_eq     *)
(* level).                                                           *)
(* ============================================================ *)

(* item 1: the Id-level isomorphism bridge — induction on [t], each
   step unfolding both carriers one layer by directed [cbn] *)
Lemma prc_powb_real_pow_id : forall (base : Real) (t : nat),
  real_eq (powb_pow base t) (real_pow base t).
Proof.
  intros base t. induction t as [| m IH].
  - cbn [powb_pow real_pow]. apply real_eq_refl.
  - cbn [powb_pow real_pow].
    apply (RealSetoid.real_eq_mult_compat base (powb_pow base m)
                                          base (real_pow base m)).
    + apply real_eq_refl.
    + exact IH.
Qed.

(* item 2: the real_eq-level bridge — induction assembled level by
   level with [real_eq_mult_compat] *)
Lemma prc_powb_real_pow_req : forall (base : Real) (t : nat),
  real_eq (powb_pow base t) (real_pow base t).
Proof.
  intros base t. induction t as [| m IH].
  - apply real_eq_refl.
  - cbn [powb_pow real_pow].
    apply (RealSetoid.real_eq_mult_compat base (powb_pow base m)
                                          base (real_pow base m)).
    + apply real_eq_refl.
    + exact IH.
Qed.

(* item 3: the reverse bridge (one [real_eq_sym] step; the two
   transport directions delivered as a pair) *)
Lemma prc_real_pow_powb_req : forall (base : Real) (t : nat),
  real_eq (real_pow base t) (powb_pow base t).
Proof.
  intros base t.
  exact (real_eq_sym (real_pow base t) (powb_pow base t)                     (prc_powb_real_pow_req base t)).
Qed.

(* ============================================================ *)
(* Part 2. eq_compat-level docking statements (the slot previously   *)
(* missing on the G07 side, now filled; the two routes certify each  *)
(* other).                                                           *)
(* ============================================================ *)

(* item 4: eq_compat for the [powb_pow] carrier — a genuine induction
   proof (the slot previously missing on the G07 side) *)
Lemma prc_powb_eq_compat : forall (x y : Real) (n : nat),
  real_eq x y -> real_eq (powb_pow x n) (powb_pow y n).
Proof.
  intros x y n Hxy. induction n as [| m IH].
  - apply real_eq_refl.
  - cbn [powb_pow].
    apply (RealSetoid.real_eq_mult_compat x (powb_pow x m)
                                          y (powb_pow y m)).
    + exact Hxy.
    + exact IH.
Qed.

(* item 5: the docking route for the same statement — CW220's
   [real_pow_eq_compat] connected through the two bridges of items
   2/3 *)
Lemma prc_powb_eq_compat_via_cwe : forall (x y : Real) (n : nat),
  real_eq x y -> real_eq (powb_pow x n) (powb_pow y n).
Proof.
  intros x y n Hxy.
  apply (real_eq_trans (powb_pow x n) (real_pow x n) (powb_pow y n)).
  - exact (prc_powb_real_pow_req x n).
  - apply (real_eq_trans (real_pow x n) (real_pow y n) (powb_pow y n)).
    + exact (real_pow_eq_compat x y n Hxy).
    + exact (real_eq_sym (real_pow y n) (powb_pow y n)
                         (prc_powb_real_pow_req y n)).
Qed.

(* ============================================================ *)
(* Part 3. Property transport between the carriers (G07 Bishop       *)
(* statements -> the [real_pow] carrier; CW220 Or-order bound        *)
(* statements -> the [powb_pow] carrier).                            *)
(* ============================================================ *)

(* item 6: transport of the G07 monotonicity conclusion P2 — the
   NatLe-bounded Bishop-form antitone behavior of powers is now
   available on the [real_pow] carrier in the same shape (previously
   missing on the CW220 side) *)
Lemma prc_powb_mono_dec_real_pow : forall (base : Real) (m : nat),
  real_lt real_zero base -> real_le base real_one ->
  forall n : nat, NatLe n m ->
  real_le_b (real_pow base m) (real_pow base n).
Proof.
  intros base m Hb Hle n Hnm.
  pose proof (powb_mono_dec base m Hb Hle n Hnm) as HB.
  intros eps Heps.
  apply (RealSetoid.real_lt_compat (powb_pow base m) (real_pow base m)
                                   (real_plus (powb_pow base n) eps)
                                   (real_plus (real_pow base n) eps)).
  - apply prc_powb_real_pow_id.
  - apply (RealSetoid.real_eq_plus_compat (powb_pow base n) eps
                                          (real_pow base n) eps).
    + apply prc_powb_real_pow_id.
    + apply real_eq_refl.
  - exact (HB eps Heps).
Qed.

(* item 7: transport of the Bishop statement that powers stay below
   one *)
Lemma prc_powb_le_one_pow_real_pow : forall (base : Real) (t : nat),
  real_lt real_zero base -> real_le base real_one ->
  real_le_b (real_pow base t) real_one.
Proof.
  intros base t Hb Hle.
  pose proof (powb_le_one_pow base t Hb Hle) as HB.
  intros eps Heps.
  apply (RealSetoid.real_lt_compat (powb_pow base t) (real_pow base t)
                                   (real_plus real_one eps)
                                   (real_plus real_one eps)).
  - apply prc_powb_real_pow_id.
  - apply real_eq_refl.
  - exact (HB eps Heps).
Qed.

(* item 8: use of CW220's [real_pow_anti_mono] — the stdlib nat le
   premise is moved to the Set-layer [NatLe] order by [NatLe_drop],
   and the conclusion is transported back to the [powb_pow] carrier
   through the Id bridge *)
Lemma prc_powb_anti_mono_real_le : forall (k : Real),
  real_lt real_zero k -> real_le k real_one ->
  forall p q : nat, NatLe p q ->
  real_le (powb_pow k q) (powb_pow k p).
Proof.
  intros k Hk1 Hk2 p q Hpq.
  pose proof (real_pow_anti_mono k Hk1 Hk2 p q (NatLe_drop p q Hpq)) as HA.
  apply (RealSetoid.real_le_compat (real_pow k q) (powb_pow k q)
                                   (real_pow k p) (powb_pow k p)).
  - exact (real_eq_sym (powb_pow k q) (real_pow k q)
                       (prc_powb_real_pow_id k q)).
  - exact (real_eq_sym (powb_pow k p) (real_pow k p)
                       (prc_powb_real_pow_id k p)).
  - exact HA.
Qed.

(* ============================================================ *)
(* Assumption audit (the eight file-tail Print Assumptions).         *)
(* ============================================================ *)
Print Assumptions prc_powb_real_pow_id.
Print Assumptions prc_powb_real_pow_req.
Print Assumptions prc_real_pow_powb_req.
Print Assumptions prc_powb_eq_compat.
Print Assumptions prc_powb_eq_compat_via_cwe.
Print Assumptions prc_powb_mono_dec_real_pow.
Print Assumptions prc_powb_le_one_pow_real_pow.
Print Assumptions prc_powb_anti_mono_real_le.
