(* UpReqStrictStepGen.v -- strict-step generator family.                    *)
(* Mission.: interface-level named lemma family formalizing the eps-split   *)
(*   idiom of the Q layer as named pieces of the Real layer: the order and  *)
(*   multiplicative strict steps of the constants h := real_const (1#2),    *)
(*   q := real_const (1#4) (the Real-layer named counterparts of the inline *)
(*   eps/2, eps/4 idiom of the Q layer).                                    *)
(* Dependencies.: CW_ConstructiveWorld_219 (exported faces of S02/S07).     *)
(*   Standalone piece, complementary to UpReqRealLtShiftBridge: that piece  *)
(*   supplies Or-decomposition order-shift lemmas, this piece supplies      *)
(*   constant-multiplier strict steps; zero mutual Require.                 *)
(* References.: the half-split identities (half_add) and the constant       *)
(*   strict-order layer of mathlib; self-built here on the Cauchy real      *)
(*   layer of this library.                                                 *)
(* Constructivity.: Set-layer statements (real_lt/real_eq); every proof     *)
(*   ends in Qed; zero assumption slots; fully explicit term assembly,      *)
(*   extractable. Statement faces carry no Prop-valued comparisons; the     *)
(*   proof bodies consume only registered conversion lemmas of the tree     *)
(*   (Qlt_to_QltT of S02 and the RealSetoid faces of S07).                  *)
(* Build.: Rocq 9.1 direct invocation (toolchain env.sh of the same         *)
(*   source), every compile wrapped by the cpu_guard thermal protocol,      *)
(*   rocq c -native-compiler no -q.                                         *)

From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qring.
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

(* ============ Constant multipliers: Real carriers of the Q-layer eps-split idiom ============ *)
Definition ssg_h : Real := real_const (1#2)%Q.
Definition ssg_q : Real := real_const (1#4)%Q.

(* ============ Mnemonics: constant addition / constant unit (pointwise zero-difference pattern) ============ *)
Lemma ssg_eq_const_plus : forall c d : Q,
  real_eq (real_plus (real_const c) (real_const d)) (real_const (c + d)%Q).
Proof.
  intros c d.
  apply real_eq_of_zero_diff.
  intro n.
  apply qeq_imp_qeqT.
  simpl.
  ring.
Qed.

(* ============ Chain base: constant order (1/4 < 1/2 < 1) and positivity ============ *)
Lemma ssg_h_lt_one : real_lt ssg_h real_one.
Proof.
  apply (real_const_lt (1#2)%Q 1%Q).
  compute.
  reflexivity.
Qed.

Lemma ssg_q_lt_h : real_lt ssg_q ssg_h.
Proof.
  apply (real_const_lt (1#4)%Q (1#2)%Q).
  compute.
  reflexivity.
Qed.

Lemma ssg_q_lt_one : real_lt ssg_q real_one.
Proof.
  apply (real_lt_trans ssg_q ssg_h real_one ssg_q_lt_h ssg_h_lt_one).
Qed.

Lemma ssg_zero_lt_h : real_lt real_zero ssg_h.
Proof.
  apply real_const_pos.
  apply Qlt_to_QltT.
  compute.
  reflexivity.
Qed.

Lemma ssg_zero_lt_q : real_lt real_zero ssg_q.
Proof.
  apply real_const_pos.
  apply Qlt_to_QltT.
  compute.
  reflexivity.
Qed.

(* ============ Part 1, parameterized source: strict multiplication-by-unit cancellation p*c < p ============ *)
(* c<1 and 0<p imply p*c < p*1 == p (left-multiplication form of            *)
(* real_lt_mult_compat, plus rewriting).                                    *)
Lemma ssg_lt_mul_one : forall c p : Real,
  real_lt c real_one -> real_lt real_zero p ->
  real_lt (real_mult p c) p.
Proof.
  intros c p Hc Hp.
  apply (RealSetoid.real_lt_id_r (real_mult p c) (real_mult p real_one) p           (real_mult_one p)).
  exact (real_lt_mult_compat c real_one p Hp Hc).
Qed.

(* -- Part 1 instance: p/2 < p (half-amount strict inequality) -- *)
Lemma ssg_half_lt : forall p : Real,
  real_lt real_zero p -> real_lt (real_mult p ssg_h) p.
Proof.
  intros p Hp.
  exact (ssg_lt_mul_one ssg_h p ssg_h_lt_one Hp).
Qed.

(* -- Part 1 left-multiplication copy: c*p < p (c<1, 0<p) -- *)
Lemma ssg_lt_mul_one_l : forall c p : Real,
  real_lt c real_one -> real_lt real_zero p ->
  real_lt (real_mult c p) p.
Proof.
  intros c p Hc Hp.
  apply (RealSetoid.real_lt_id_r (real_mult c p)
           (real_mult real_one p) p).
  - exact (real_eq_trans (real_mult real_one p)
             (real_mult p real_one) p
             (real_mult_comm real_one p) (real_mult_one p)).
  - exact (real_mult_lt_compat c real_one p Hc Hp).
Qed.

(* ============ Part 2, splitting identity: p/2 + p/2 == p ============ *)
(* The half-sum constant (1/2)+(1/2) coincides pointwise with the unit via  *)
(* the Q-layer Qeq.                                                         *)
Lemma ssg_half_add : forall p : Real,
  real_eq (real_plus (real_mult p ssg_h) (real_mult p ssg_h)) p.
Proof.
  intros p.
  assert (Hhh : real_eq (real_plus ssg_h ssg_h) real_one).
  { apply (real_eq_trans (real_plus ssg_h ssg_h)
             (real_const ((1#2)%Q + (1#2)%Q)%Q) real_one).
    - exact (ssg_eq_const_plus (1#2)%Q (1#2)%Q).
    - apply real_eq_of_zero_diff.
      intro n.
      apply qeq_imp_qeqT.
      simpl.
      ring. }
  apply (real_eq_trans
           (real_plus (real_mult p ssg_h) (real_mult p ssg_h))
           (real_mult p real_one) p).
  - apply (real_eq_trans
             (real_plus (real_mult p ssg_h) (real_mult p ssg_h))
             (real_mult p (real_plus ssg_h ssg_h))
             (real_mult p real_one)).
    + exact (real_eq_sym (real_mult p (real_plus ssg_h ssg_h))
               (real_plus (real_mult p ssg_h) (real_mult p ssg_h))
               (real_distrib p ssg_h ssg_h)).
    + exact (RealSetoid.real_eq_mult_compat p
               (real_plus ssg_h ssg_h) p real_one
               (real_eq_refl p) Hhh).
  - exact (real_mult_one p).
Qed.

(* ============ Part 3, main theorem: half*eps + quarter*eps < eps ============ *)
(* The parameterized dependency shape targeted for consumption. Route:      *)
(*   h*e + q*e == e*h + e*q == e*(h+q) < e*one == e                         *)
(*   (constant chain (h+q) == 3/4 and 3/4 < 1, plus order-preserving        *)
(*   multiplication).                                                       *)
Lemma ssg_half_quarter_eps_lt : forall eps : Real,
  real_lt real_zero eps ->
  real_lt (real_plus (real_mult ssg_h eps) (real_mult ssg_q eps)) eps.
Proof.
  intros eps Heps.
  assert (Hhq : real_lt (real_plus ssg_h ssg_q) real_one).
  { apply (RealSetoid.real_lt_id_l (real_plus ssg_h ssg_q)
             (real_const ((1#2)%Q + (1#4)%Q)%Q) real_one
             (ssg_eq_const_plus (1#2)%Q (1#4)%Q)).
    apply (real_const_lt ((1#2)%Q + (1#4)%Q)%Q 1%Q).
    compute.
    reflexivity. }
  assert (Hre : real_eq (real_plus (real_mult ssg_h eps) (real_mult ssg_q eps))
                        (real_mult eps (real_plus ssg_h ssg_q))).
  { apply (real_eq_trans
             (real_plus (real_mult ssg_h eps) (real_mult ssg_q eps))
             (real_plus (real_mult eps ssg_h) (real_mult eps ssg_q))
             (real_mult eps (real_plus ssg_h ssg_q))).
    - exact (RealSetoid.real_eq_plus_compat
               (real_mult ssg_h eps) (real_mult ssg_q eps)
               (real_mult eps ssg_h) (real_mult eps ssg_q)
               (real_mult_comm ssg_h eps) (real_mult_comm ssg_q eps)).
    - exact (real_eq_sym
               (real_mult eps (real_plus ssg_h ssg_q))
               (real_plus (real_mult eps ssg_h) (real_mult eps ssg_q))
               (real_distrib eps ssg_h ssg_q)). }
  apply (RealSetoid.real_lt_id_l
           (real_plus (real_mult ssg_h eps) (real_mult ssg_q eps))
           (real_mult eps (real_plus ssg_h ssg_q)) eps Hre).
  apply (RealSetoid.real_lt_id_r
           (real_mult eps (real_plus ssg_h ssg_q))
           (real_mult eps real_one) eps
           (real_mult_one eps)).
  exact (real_mult_lt_compat_l (real_plus ssg_h ssg_q) real_one eps
           Hhq Heps).
Qed.

(* ============ Part 4, standard strict chain (ready-made strict steps) ============ *)
(* q*eps < eps: quarter multiplication-by-unit cancellation (0<1, then the  *)
(* q<1/2<1 chain, via the Part 1 source module).                            *)
Lemma ssg_quarter_eps_lt : forall eps : Real,
  real_lt real_zero eps -> real_lt (real_mult ssg_q eps) eps.
Proof.
  intros eps Heps.
  exact (ssg_lt_mul_one_l ssg_q eps ssg_q_lt_one Heps).
Qed.

(* h*eps < eps: half-amount twin (Part 1 source module instantiated at      *)
(* c:=h).                                                                   *)
Lemma ssg_half_eps_lt : forall eps : Real,
  real_lt real_zero eps -> real_lt (real_mult ssg_h eps) eps.
Proof.
  intros eps Heps.
  exact (ssg_lt_mul_one_l ssg_h eps ssg_h_lt_one Heps).
Qed.

(* ============ Assumption-closure check (all eight statements Closed = pass criterion) ==== *)
Print Assumptions ssg_eq_const_plus.
Print Assumptions ssg_lt_mul_one.
Print Assumptions ssg_half_lt.
Print Assumptions ssg_lt_mul_one_l.
Print Assumptions ssg_half_add.
Print Assumptions ssg_half_quarter_eps_lt.
Print Assumptions ssg_quarter_eps_lt.
Print Assumptions ssg_half_eps_lt.
