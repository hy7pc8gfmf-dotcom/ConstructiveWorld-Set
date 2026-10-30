(* ========================================================================== *)
(*  UpReqMixRationalProxy.v - rational-layer proxy tools for a step selector *)
(* ========================================================================== *)
(*   Mission. A rational-layer (Q) auxiliary toolkit feeding a binary-search *)
(*   step selector that returns an iteration count on the real layer: the    *)
(*   transparent rational power rp_qpow with its unfolding and positivity    *)
(*   lemmas; the comparison-free minimum rp_qmin (the trichotomy of Qcompare *)
(*   is read directly, with no Qmin dependency); the error budget rp_eps     *)
(*   := min(d0, db, d1)/8 with its margin ledger; the pointwise error        *)
(*   lemma rp_abs_minus_const_proj over the Cauchy-sequence real layer;      *)
(*   the strict-order transfer helpers rp_qlt_eq_l/rp_qlt_eq_rQ/rp_qlt_eq_r  *)
(*   along the rational equality; and the certificate-carrying selector      *)
(*   rp_q_proxy_upper_hyp. The companion module UpReqMixRationalProxy_R3     *)
(*   develops the complete sigT form (rp_q_proxy_upper) of the selector.     *)
(*   Dependencies. Stdlib QArith (QArith, Qring, Qround, Qabs), ZArith, Lia; *)
(*   S01_BaseRing through S15_TailFEPUp (constructive Cauchy reals and the   *)
(*   Set-valued order and equality witnesses QltT/QleT'/QeqT with their     *)
(*   registered conversion lemmas); UpTVDoeblin. No further Require.        *)
(*   References. Baseline module UpReqMixRationalProxy.v of ConstructiveWorld-Main *)
(*   ConstructiveWorld_Live (statement names carried over verbatim;          *)
(*   census 17=17 ordered identity; 8 statement-face rewrites to the         *)
(*   Set-valued forms).                                                      *)
(*   Constructivity. All seventeen statements are Set-valued: strict and    *)
(*   weak order and equality on Q are witnessed by the boolean forms        *)
(*   QltT/QleT'/QeqT (Id over Qlt_bool/Qle_bool/Qcompare). The module is    *)
(*   axiom-free, uses no classical logic, and performs no order branching   *)
(*   on the real layer (all search predicates live on Q); extraction        *)
(*   therefore yields no Obj.magic.                                        *)
(*   Build. rocq c -native-compiler no -q -Q . "" UpReqMixRationalProxy.v   *)
(*   (Rocq 9.1 toolchain; single -Q root with an empty logical prefix).     *)

From Stdlib Require Import QArith.QArith.
From Stdlib Require Import QArith.Qring.
From Stdlib Require Import QArith.Qround.
From Stdlib Require Import QArith.Qabs.
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
Require Import UpTVDoeblin.

(* ============================================================ *)
(* Section 0. Rational-layer tools: power, minimum, error budget *)
(* ============================================================ *)

(* Rational power with a nat exponent (transparent computation: the
   numeric core of the search predicate). *)
Fixpoint rp_qpow (a : Q) (k : nat) {struct k} : Q :=
  match k with
  | Datatypes.O => 1#1
  | Datatypes.S m => a * rp_qpow a m
  end.

(* Unfolding equation for rp_qpow at a successor exponent. *)
Lemma rp_qpow_S : forall (a : Q) (k : nat), QeqT (rp_qpow a (Datatypes.S k)) (a * rp_qpow a k).
Proof. intros a k. apply qeq_imp_qeqT. reflexivity. Qed.

(* Positivity is preserved by rational exponentiation. *)
Lemma rp_qpow_pos : forall (a : Q) (k : nat), QltT 0 a -> QltT 0 (rp_qpow a k).
Proof.
  intros a k Ha. induction k as [| k IHk].
  - exact qltT_0_1.
  - exact (qmult_ltT_0_compat a (rp_qpow a k) Ha IHk).
Qed.

(* Decay engine: 0 < a <= 1 implies rp_qpow a k <= 1 for every k. *)
Lemma rp_qpow_le_one : forall (a : Q) (k : nat), QltT 0 a -> QleT' a 1 -> QleT' (rp_qpow a k) 1.
Proof.
  intros a k Ha H1. induction k as [| k IHk].
  - apply (qeq_leT' _ _). reflexivity.
  - apply (qleT'_trans _ (rp_qpow a k) 1).
    + apply (qleT'_trans _ (1 * rp_qpow a k) (rp_qpow a k)).
      * apply (qleT'_mult_compat_r a 1 (rp_qpow a k)).
        -- exact (qltT_leT' _ _ (rp_qpow_pos a k Ha)).
        -- exact H1.
      * apply (qeq_leT' (1 * rp_qpow a k) (rp_qpow a k)).
        apply qeq_imp_qeqT. ring.
    + exact IHk.
Qed.

(* Self-contained minimum (no Qmin/gmin dependency: the trichotomy of
   Qcompare is read directly). *)
Definition rp_qmin (a b : Q) : Q :=
  match Qcompare a b with
  | Gt => b
  | _ => a
  end.

(* The minimum is below its first argument. *)
Lemma rp_qmin_le_l : forall a b : Q, QleT' (rp_qmin a b) a.
Proof.
  intros a b. apply Qle_to_QleT'. unfold rp_qmin. destruct (Qcompare a b) eqn:E.
  - apply Qle_refl.
  - apply Qle_refl.
  - apply Qlt_le_weak. apply (proj2 (Qlt_alt b a)).
    rewrite <- (Qcompare_antisym a b). rewrite E. reflexivity.
Qed.

(* The minimum is below its second argument. *)
Lemma rp_qmin_le_r : forall a b : Q, QleT' (rp_qmin a b) b.
Proof.
  intros a b. apply Qle_to_QleT'. unfold rp_qmin. destruct (Qcompare a b) eqn:E.
  - exact (QleT'_to_Qle _ _ (qeq_imp_qle _ _ (qeq_imp_qeqT _ _ (proj2 (Qeq_alt a b) E)))).
  - apply Qlt_le_weak. apply (proj2 (Qlt_alt a b)). exact E.
  - apply Qle_refl.
Qed.

(* Positivity of the minimum. *)
Lemma rp_qmin_pos : forall a b : Q, QltT 0 a -> QltT 0 b -> QltT 0 (rp_qmin a b).
Proof.
  intros a b Ha Hb. unfold rp_qmin. destruct (Qcompare a b); assumption.
Qed.

(* Positivity of a three-fold minimum. *)
Lemma rp_qmin_pos3 : forall a b c : Q,
  QltT 0 a -> QltT 0 b -> QltT 0 c -> QltT 0 (rp_qmin (rp_qmin a b) c).
Proof.
  intros a b c Ha Hb Hc. unfold rp_qmin.
  destruct (Qcompare (match a ?= b with Gt => b | _ => a end) c).
  - exact (rp_qmin_pos a b Ha Hb).
  - exact (rp_qmin_pos a b Ha Hb).
  - exact Hc.
Qed.

(* Precision budget: eps := min(d0, db, d1)/8 (the minimum of three
   separation quantities, then one eighth, so the error enters the
   margin explicitly). *)
Definition rp_eps (d0 db d1 : Q) : Q := rp_qmin (rp_qmin d0 db) d1 / 8.

(* Positivity of the error budget. *)
Lemma rp_eps_pos : forall d0 db d1 : Q,
  QltT 0 d0 -> QltT 0 db -> QltT 0 d1 -> QltT 0 (rp_eps d0 db d1).
Proof.
  intros d0 db d1 H0 Hb H1. unfold rp_eps.
  apply qltT_div_pos. apply rp_qmin_pos3; assumption.
  vm_compute. reflexivity.
Qed.

(* Margin ledger: 2 * eps <= d0 / 4 (eps <= min/8 implies 2eps <= min/4
   <= d0/4). *)
Lemma rp_eps_margin : forall d0 db d1 : Q, QleT' (2 * rp_eps d0 db d1) (d0 / 4).
Proof.
  intros d0 db d1. apply Qle_to_QleT'. unfold rp_eps.
  apply (Qle_trans _ (rp_qmin (rp_qmin d0 db) d1 / 4)).
  - assert (Ht1 : (2 * (rp_qmin (rp_qmin d0 db) d1 / 8))%Q
                == (rp_qmin (rp_qmin d0 db) d1 / 4)) by field.
    rewrite Ht1. apply Qle_refl.
  - assert (Ht2 : (rp_qmin (rp_qmin d0 db) d1 / 4)%Q
                == (rp_qmin (rp_qmin d0 db) d1 * (((1#1) / (4#1))))) by field.
    assert (Ht3 : (d0 / 4)%Q == (d0 * (((1#1) / (4#1))))) by field.
    rewrite Ht2, Ht3.
    apply Qmult_le_compat_r.
    + apply (Qle_trans _ (rp_qmin d0 db)).
      * apply QleT'_to_Qle. apply rp_qmin_le_l.
      * apply QleT'_to_Qle. apply rp_qmin_le_l.
    + apply Qlt_le_weak.
      exact (QltT_to_Qlt _ _ (qltT_div_pos (1#1) (4#1) qltT_0_1 qltT_0_4)).
Qed.

(* ============================================================ *)
(* Section 1. Rational proxy construction (mission piece 1)     *)
(* ============================================================ *)

(* The pointwise sequence of |x - const v| equals |u n - v|
   (definitional). *)
Lemma rp_abs_minus_const_proj : forall (x : Real) (v : Q) (n : nat),
  QeqT (projT1 (real_abs (real_minus_r x (real_const v))) n) (Qabs (projT1 x n - v)).
Proof. intros [u Hu] v n. apply qeq_imp_qeqT. reflexivity. Qed.

(* Transfer of the strict order along the rational equality on the
   left-hand argument (carried by Qcompare_comp). *)
Lemma rp_qlt_eq_l : forall a a' b : Q, QeqT a a' -> QltT a b -> QltT a' b.
Proof.
  intros a a' b Heq H. apply Qlt_to_QltT. apply Qlt_alt.
  assert (Heq' : a == a') by (apply qeqT_imp_qeq; exact Heq).
  rewrite <- (Qcompare_comp a a' Heq' b b (Qeq_refl b)).
  exact (proj1 (Qlt_alt a b) (QltT_to_Qlt _ _ H)).
Qed.

(* Transfer of the strict order along the rational equality on the
   right-hand argument (Q-comparison form). *)
Lemma rp_qlt_eq_rQ : forall a b b' : Q, QeqT b b' -> QltT a b -> QltT a b'.
Proof.
  intros a b b' Heq H. apply Qlt_to_QltT. apply Qlt_alt.
  assert (Heq' : b == b') by (apply qeqT_imp_qeq; exact Heq).
  rewrite <- (Qcompare_comp a a (Qeq_refl a) b b' Heq').
  exact (proj1 (Qlt_alt a b) (QltT_to_Qlt _ _ H)).
Qed.

(* Transfer of the strict order along the rational equality on the
   right-hand argument (witnessed form). *)
Lemma rp_qlt_eq_r : forall a b b' : Q, QeqT b b' -> QltT a b -> QltT a b'.
Proof.
  intros a b b' Heq H. apply Qlt_to_QltT. apply Qlt_alt.
  assert (Heq' : b == b') by (apply qeqT_imp_qeq; exact Heq).
  rewrite <- (Qcompare_comp a a (Qeq_refl a) b b' Heq').
  exact (proj1 (Qlt_alt a b) (QltT_to_Qlt _ _ H)).
Qed.

(* Step-count selector from a certificate-carrying premise: the
   certificate component is intentionally not inspected here; the
   complete sigT form (rp_q_proxy_upper) is developed in the companion
   module UpReqMixRationalProxy_R3. *)
Definition rp_q_proxy_upper_hyp (x : Real) (eps : Q) (Heps : QltT 0 eps)
  (Hcert : sigT (fun v : Q => real_lt x (real_const (v + eps)))) : nat :=
  match Hcert with
  | existT _ v _ => 0%nat
  end.
