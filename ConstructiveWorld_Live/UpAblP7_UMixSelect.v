(* ============================================================ *)
(* UpAblP7_UMixSelect.v — use-face reconstruction of UpReqUMixSelect.v:
   named use forms of ums_pow_budget and the concrete kappa := 1/2 instance.
   Mission.
   Fix the exit form of ums_pow_budget (substitute the declared premise,
   obtain the conclusion) as uabm_ums_pow_budget_slot_freeze; instantiate it
   on the req face (RealEnhancedReal) at kappa := 1/2, TV0 := budget := one
   as uabm_k_select_half, witnessing some k with (1/2)^k * 1 < 1; supply the
   nat-scale Arch bridge uabm_arch_scale: real_arch's const-form bound
   (forall B, exists n >= 2, B < const(n#1)) transported via mix_scale_eq_const
   and real_mult_one to the cmk_scale (S N) one form.  Use-face consumers:
   ums_pow_budget, cmk_pow_budget/cmk_scale/cmk_r_pow,
   real_lt_plus_compat_lt_le, real_arch, mix_scale_eq_const, real_mult_one.

   Dependencies.
   UpReqUMixSelect, UpReqConcMixSel, UpReqMixingTime, CW_ConstructiveWorld_219,
   S01_BaseRing, S04_RealExpLogConv (read-only; transitive S02..S15 chain).

   References.
   Constructive counterpart of the pow_lt_one reciprocal-decay witness
   (mathlib): the decay step count is produced constructively.

   Constructivity.
   Statements live in Set (lt/le are interface order fields R -> R -> Set;
   existence is sigT).  The declared premise lt_plus_compat_lt_le enters only
   in its exit form.  All proofs are genuine and transparent (Defined), with
   explicit eps witnesses (1/4, 1/4, 1/2) and the transport chain.
   Build.
   Rocq 9.3 coqc under the thermal guard, -Q <Set world root> "".
   ============================================================ *)

From Stdlib Require Import List.
From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
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
Require Import UpReqConcMixSel.
Require Import UpReqMixingTime.
Require Import UpReqUMixSelect.

(* ============================================================ *)
(* Section A (Id face): the named use form of the base theorem exit
   shape.  The section binds the Id-face accessors by their fully
   qualified names: after the transitive imports above, the bare names
   resolve to the req-face notations (R := Real, lt := real_lt,
   le := real_le) and to the imported req-face field accessors, so an
   unqualified binding would elaborate on the wrong face.  The section
   must also precede the import of RealInterfaceEnhancedMod below.
   On section close, RI remains the implicit argument of the exit
   theorem (all section binders are discharged by the section
   mechanism; the premise is passed as the first explicit argument). *)
(* ============================================================ *)

Section UabmIface.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.

Let R := @S01_BaseRing.R RI.
Let zero := @S01_BaseRing.zero RI.
Let one  := @S01_BaseRing.one RI.
Let plus := @S01_BaseRing.plus RI.
Let mult := @S01_BaseRing.mult RI.
Let lt   := @S01_BaseRing.lt RI.
Let le   := @S01_BaseRing.le RI.

Theorem uabm_ums_pow_budget_slot_freeze :
  (forall a b c d : R, lt a b -> le c d -> lt (plus a c) (plus b d)) ->
  forall kappa TV0 budget : R,
    lt zero kappa -> lt kappa one -> lt zero TV0 -> lt zero budget ->
    (forall x : R, lt zero x ->
       sigT (fun N : nat => lt x (ums_scale (Datatypes.S N) one))) ->
    sigT (fun k : nat => lt (mult (r_pow kappa k) TV0) budget).
Proof.
  intros Hwall.
  exact (ums_pow_budget Hwall).
Defined.

End UabmIface.

(* from here on the req-face bare names are enabled (Real-face
   statements below use them) *)
Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* Section 1: the kappa := 1/2 instance face (pointwise construction,
   the eps := 1/4 Q computation closes on constant columns). *)
(* ============================================================ *)

Definition uabm_half : Real := real_const (1#2)%Q.

(* 0 < 1/2: real_lt witness construction (eps := 1/4, constant columns
   pointwise constant) *)
Theorem uabm_half_pos : real_lt real_zero uabm_half.
Proof.
  unfold real_lt. exists (1#4)%Q. split.
  - apply Qlt_to_QltT. unfold Qlt. cbn. exact eq_refl.
  - exists 0%nat. intros n Hn.
    change (QltT (1#4)%Q (projT1 uabm_half n - projT1 real_zero n)).
    change (projT1 uabm_half n) with (1#2)%Q.
    change (projT1 real_zero n) with 0%Q.
    apply Qlt_to_QltT. unfold Qlt. cbn. exact eq_refl.
Defined.

(* 1/2 < 1: same shape (eps := 1/4, difference 1 - 1/2 = 1/2) *)
Theorem uabm_half_lt_one : real_lt uabm_half real_one.
Proof.
  unfold real_lt. exists (1#4)%Q. split.
  - apply Qlt_to_QltT. unfold Qlt. cbn. exact eq_refl.
  - exists 0%nat. intros n Hn.
    change (QltT (1#4)%Q (projT1 real_one n - projT1 uabm_half n)).
    change (projT1 real_one n) with 1%Q.
    change (projT1 uabm_half n) with (1#2)%Q.
    apply Qlt_to_QltT. unfold Qlt. cbn. exact eq_refl.
Defined.

(* 0 < 1 (premise instance for the TV0/budget slots of the final
   assembly) *)
Theorem uabm_one_pos : real_lt real_zero real_one.
Proof.
  unfold real_lt. exists (1#2)%Q. split.
  - apply Qlt_to_QltT. unfold Qlt. cbn. exact eq_refl.
  - exists 0%nat. intros n Hn.
    change (QltT (1#2)%Q (projT1 real_one n - projT1 real_zero n)).
    change (projT1 real_one n) with 1%Q.
    change (projT1 real_zero n) with 0%Q.
    apply Qlt_to_QltT. unfold Qlt. cbn. exact eq_refl.
Defined.

(* ============================================================ *)
(* Section 2: the req-face instance of the declared premise and the
   nat-scale Arch bridging lemma. *)
(* ============================================================ *)

(* the req-face instance of the declared premise lt_plus_compat_lt_le:
   real_lt_plus_compat_lt_le (same statement as the CmkMixSelect
   Variable of ConcMixSelFeed).  The statement face uses the explicit
   real_* names: after the import above the bare order names resolve to
   the interface field accessors, and accessor form versus constant
   form would split the extracted representation. *)
Definition uabm_wall :
  forall a b c d : Real,
    real_lt a b -> real_le c d ->
    real_lt (real_plus a c) (real_plus b d) :=
  real_lt_plus_compat_lt_le.

(* uabm_arch_scale: the nat-scale Arch bridging lemma.  real_arch gives
   the const-form upper bound (forall B, exists n >= 2,
   B < const(n#1)); via mix_scale_eq_const (mix_scale k w == const(k#1)
   * w) and real_mult_one (x * 1 == x) it is transported to the
   cmk_scale (S N) one form.  Three steps: cmk_scale and mix_scale
   have the same fold (equal instance fields, convertibly equal), the
   const * one product cancels, and the right end is rewritten along
   RealSetoid.real_lt_id_r. *)
Lemma uabm_arch_scale : forall x : Real,
  real_lt real_zero x ->
  sigT (fun N : nat => real_lt x (cmk_scale (Datatypes.S N) real_one)).
Proof.
  intros x Hx.
  destruct (real_arch x) as [n [H2n Hlt]].
  destruct n as [| m].
  - exfalso. inversion H2n.
  - exists m.
    apply (RealSetoid.real_lt_id_r x
             (real_const (Z.of_nat (Datatypes.S m) # 1))
             (cmk_scale (Datatypes.S m) real_one)).
    + apply real_eq_sym.
      apply (real_eq_trans
               (cmk_scale (Datatypes.S m) real_one)
               (real_mult (real_const (Z.of_nat (Datatypes.S m) # 1)) real_one)
               (real_const (Z.of_nat (Datatypes.S m) # 1))).
      * exact (mix_scale_eq_const (Datatypes.S m) real_one).
      * exact (real_mult_one (real_const (Z.of_nat (Datatypes.S m) # 1))).
    + exact Hlt.
Defined.

(* ============================================================ *)
(* Section 3: the main concrete assembly of the base theorem (the
   declared premise slot takes uabm_wall and kappa := 1/2).
   cmk_pow_budget is the req-face copy of ums_pow_budget; substituting
   uabm_wall into the declared premise slot and uabm_arch_scale into
   the Arch premise slot yields the concrete step-count witness at
   kappa = 1/2: sigT k, (1/2)^k * 1 < 1.  Fully closed. *)
(* ============================================================ *)

Theorem uabm_k_select_half :
  sigT (fun k : nat =>
    real_lt (real_mult (cmk_r_pow uabm_half k) real_one) real_one).
Proof.
  exact (cmk_pow_budget uabm_wall           uabm_half real_one real_one           uabm_half_pos uabm_half_lt_one uabm_one_pos uabm_one_pos           uabm_arch_scale).
Defined.

(* ============================================================ *)
(* Closing audit block: per-statement Print Assumptions, verifying the
   absence of unresolved premises. *)
(* ============================================================ *)

Print Assumptions uabm_ums_pow_budget_slot_freeze.
Print Assumptions uabm_half_pos.
Print Assumptions uabm_half_lt_one.
Print Assumptions uabm_one_pos.
Print Assumptions uabm_arch_scale.
Print Assumptions uabm_k_select_half.
