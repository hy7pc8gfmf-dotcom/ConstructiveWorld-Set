(* ============================================================
   AbsLeId -- Mission.  constructive fulfillment of a genuine
   gap left over from earlier verification: for the
   abs_ge_zero_id_cc interface argument slot of
   S06_DiffSamplingGibbs (forall a, le zero a -> Id (abs a) a;
   after Let-alias expansion = forall a : @R (@RI_base RI),
   @le (@RI_base RI) ...), this file delivers the abstract
   interface layer main theorem together with the concrete Real
   layer fulfillment.
   Dependencies.  S01_BaseRing, fa53_compat_abs, S02_CauchyComplete,
   S03_QExp, S07_RealSetoidExpLog.
   Constructivity.  All proofs close by Qed/Defined; zero axioms; no
   classical logic.
   Build.  rocq c -native-compiler no -Q <tree> "" AbsLeId.v
   Benchmark: fa53_compat_abs.v item 3 fa53_abs_ge_zero_id_dec --
   statement same shape (le zero a -> Id (abs a) a); its
   precondition is the optional extension class DecidableOrder
   (S01:329, Set-layer Or trichotomy); the main item of this file
   reuses it by reference (Require only, zero modification).
   Also delivered: (a) the reverse shape ali_abs_ge_zero_id_sym
   (id_sym canal); (b) the two S06 use-site wrapper shapes
   ali_abs_id_mult_l/r (direct matches for the id_cong
   applications at S06:4371 and S06:4447, sparing the downstream
   a manual id_cong assembly); (c) the concrete Real layer
   fulfillment ali_real_abs_ge_zero_id: real_le's Or encoding
   (S02:469) decided branch by branch -- the lt branch goes
   through real_abs_pos_req (S07:7289), the eq branch goes through
   real_eq_abs_compat (S07:410, must be qualified inside Module
   RealSetoid) + real_abs_zero_req (S07:7266) + a real_eq_sym/
   trans three-step chain.
   Constructive notes: the statement face is entirely Set layer
   (Or/Not use the S01:67-68 Set-layer definitions; real_lt is a
   sigT witness, S02:465); zero Prop leakage; no axioms / no
   admitted / no parameters / no conjectures / no abandoned
   proofs; fa53_compat_abs only Require-referenced, zero
   modification; original tree zero modification.
   The prefix ali_ has been collision-checked library-wide.
   Build recipe: Rocq 9.1 direct invocation (COQLIB/ROCQLIB
   pinned to the 9.1 library root), coqc -q -Q . "" <file>.v,
   cpu_guard tiered execution.
   ============================================================ *)

Require Import S01_BaseRing.
Require Import fa53_compat_abs.

(* ============ Layer 1: abstract interface layer (S06:4035 statement shape) ============ *)
(* Same context as fa53 (RI_base :> RealInterface subclass projection +      *)
(* Existing Instance resolving the bare names; DO is the optional           *)
(* decidable-order extension class).                                        *)
Section AbsLeIdAbstract.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {DO : DecidableOrder RI}.

(* ---- Main item: abs_ge_zero_id_cc statement same shape (reuses fa53 item 3) ---- *)
Theorem ali_abs_ge_zero_id : forall a : R, le zero a -> Id (abs a) a.
Proof.
  intros a Ha.
  exact (@fa53_abs_ge_zero_id_dec RI DO a Ha).
Qed.

(* ---- Reverse shape: le zero a -> a == |a| (what the other rewrite direction needs) ---- *)
Theorem ali_abs_ge_zero_id_sym : forall a : R, le zero a -> Id a (abs a).
Proof.
  intros a Ha.
  exact (id_sym (ali_abs_ge_zero_id a Ha)).
Qed.

(* ---- Use-site wrapper shape (left-multiplication slot): S06:4371 direct match ----
   The original text there is
     id_cong (fun x => mult (abs (f s)) x)
             (abs_ge_zero_id_cc (q_kernel s s') (q_kernel_nonneg s s'))
   -- this file pre-assembles the id_cong so the downstream feeds in one step. *)
Theorem ali_abs_id_mult_l : forall a b : R, le zero a -> Id (mult (abs a) b) (mult a b).
Proof.
  intros a b Ha.
  (* id_cong implicit x,y are fixed by p's endpoints (abs a / a); f must
     rewrite at the first argument of the multiplication *)
  exact (id_cong (fun w => mult w b) (ali_abs_ge_zero_id a Ha)).
Qed.

(* ---- Use-site wrapper shape (right-multiplication slot): S06:4447 direct match ---- *)
Theorem ali_abs_id_mult_r : forall a b : R, le zero b -> Id (mult a (abs b)) (mult a b).
Proof.
  intros a b Hb.
  exact (id_cong (fun w => mult a w) (ali_abs_ge_zero_id b Hb)).
Qed.

End AbsLeIdAbstract.

(* ============ Layer 2: concrete Real layer fulfillment ============ *)
(* Cauchy real layer (S02 Real := sigT (fun u : Qseq => cauchy u)):       *)
(* real_le = Or real_lt real_eq (S02:469, Set-layer Or), decided          *)
(* branch by branch.                                                      *)
(* Note: the Requires here are placed after the abstract section, to      *)
(* keep the concrete-layer names from shadowing the interface projection  *)
(* names.                                                                 *)
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.

Theorem ali_real_abs_ge_zero_id :
  forall a : Real, real_le real_zero a -> real_eq (real_abs a) a.
Proof.
  intros a H.
  unfold real_le in H.
  destruct H as [Hlt | Heq].
  - (* 0 < a: the strict pointwise item hands it over directly (S07:7289) *)
    exact (real_abs_pos_req a Hlt).
  - (* 0 == a: |a| ~ |0| ~ 0 ~ a (compat + zero_req + sym chain) *)
    apply (real_eq_trans _ (real_abs real_zero)).
    + apply (RealSetoid.real_eq_abs_compat a real_zero).
      apply real_eq_sym.
      exact Heq.
    + apply (real_eq_trans _ real_zero).
      * exact real_abs_zero_req.
      * exact Heq.
Qed.

(* ---- Self-check section: explicit in-file Print Assumptions declarations ---- *)
Print Assumptions ali_abs_ge_zero_id.
Print Assumptions ali_abs_ge_zero_id_sym.
Print Assumptions ali_abs_id_mult_l.
Print Assumptions ali_abs_id_mult_r.
Print Assumptions ali_real_abs_ge_zero_id.
