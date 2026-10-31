(* ========================================================================= *)
(*  abl_pint_realview.v - Real-side readout bridge for Q-valued integrals.  *)
(*  Mission. The integral layer is Q-face dominant (PolyIntegral pint_      *)
(*  family, PintMono pm_ engine) while its Real side is empty; this piece   *)
(*  reads Q integral values into the Real universe - a readout bridge,      *)
(*  not a port, not an engine (genuine Real integration is piece 2-B,       *)
(*  phase-two note PolyIntegral:64). Stations: pir_integral_real            *)
(*  (definition), pir_const_qeqT (shared QeqT-to-real_eq lift),             *)
(*  pir_integral_mono_real (coefficient-wise premise, PintMono:297),        *)
(*  pir_integral_one_real, pir_integral_pos_real (PintMono:354).            *)
(*  Dependencies. All registered, zero externals: S01_BaseRing;             *)
(*  S02_CauchyComplete (Real, real faces, QltT/QleT'/QeqT, bridges,         *)
(*  real_const_proj, q_abs_self_zero, real_eq_trans, real_eq_of_zero_diff,  *)
(*  real_one, real_zero); PolyIntegral (pint_integral, pint_pow_poly,       *)
(*  pint_coeff, pint_integral_one); PintMono (pm_pointwise_le_integral,     *)
(*  pm_integral_pos_strict); S07; Stdlib QArith; full chain imported.       *)
(*  References. Canonical T-forms per the E-STAGING-1484 decision tree.     *)
(*  Three bridge fixes vs measured tree signatures (pristine probe first):  *)
(*  q_abs_self_zero now QeqT (S02:2052), wrapped by qeqT_imp_qeq (S02:147,  *)
(*  idiom S02:2069); the QltT strict arm walks Qlt_to_QltT (S02:60) before  *)
(*  Qlt_alt; real_eq_of_zero_diff now takes a QeqT premise (S02:2383),      *)
(*  discharged wrapping qeq_imp_qeqT (S02:131); all bridges registered.     *)
(*  Constructivity. Statement face pure Set, zero classical logic, zero     *)
(*  unproved premises; real_le is the Or-form Set predicate (arms via       *)
(*  real_const_lt / pir_const_qeqT); real_one vs real_const (1#1) not       *)
(*  definitionally equal - integral(1) walks real_eq_trans both arms.       *)
(*  Build. ulimit -s 65532; rocq c -native-compiler no -q -Q . ""           *)
(*  abl_pint_realview.v (seat world, cpu_guard wrapper, Rocq 9.1.0).        *)
(* ========================================================================= *)

From Stdlib Require Import QArith.QArith QArith.Qabs Lists.List Arith.Arith.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import PolyIntegral.
Require Import PintMono.
Require Import S07_RealSetoidExpLog.

(* ============================================================ *)
(*  Piece 1 (definition piece): the Real-embedded readout of a  *)
(*  Q-valued integral. Statement face follows the draft         *)
(*  pint_integral_real verbatim (pir_ prefix per the naming     *)
(*  convention, semantics unchanged): the constant Cauchy       *)
(*  sequence real_const carries the Q integral value,           *)
(*  Real := sigT Cauchy reals (S02).                            *)
(* ============================================================ *)
Definition pir_integral_real (p : list Q) : Real :=
  real_const (pint_integral p).

(* ============================================================ *)
(*  Piece 2 (shared small piece): QeqT constant lift to         *)
(*  real_eq. All Q-layer accounting (self-difference zero plus  *)
(*  the Qcompare_comp reshaping, same recipe as the real_const  *)
(*  definition body) is prepared inside asserts first (no       *)
(*  pointwise items); the N = 0 arm then folds projT1           *)
(*  (real_const c) n down to c by the definitional change       *)
(*  (real_const_proj is reflexivity-provable). QltT is an Id    *)
(*  bool face with no Proper reshaping registration: rewrite /  *)
(*  setoid_rewrite inside QltT goals is barred (first recorded  *)
(*  instance, see the build report).                            *)
(* ============================================================ *)
Lemma pir_const_qeqT : forall c d : Q,
  QeqT c d -> real_eq (real_const c) (real_const d).
Proof.
  intros c d Hcd eps Heps.
  assert (Hcd0 : c == d) by (apply qeqT_imp_qeq; exact Hcd).
  assert (Hab : Qabs (c - d) == 0).
  { apply (Qeq_trans (Qabs (c - d)) (Qabs (d - d)) 0).
    - apply Qabs_wd. rewrite Hcd0. reflexivity.
    - apply qeqT_imp_qeq. apply q_abs_self_zero. }
  assert (Hcmp : Qcompare (Qabs (c - d)) eps = Lt).
  { rewrite (Qcompare_comp (Qabs (c - d)) 0 Hab eps eps (Qeq_refl eps)).
    apply Qlt_alt. exact (QltT_to_Qlt 0 eps Heps). }
  exists 0%nat. intros n Hn.
  change (QltT (Qabs (c - d)) eps).
  unfold QltT, Qlt_bool. rewrite Hcmp. reflexivity.
Qed.

(* ============================================================ *)
(*  Piece 3 support: QleT' constant lift to real_le (recipe:    *)
(*  Or assembly - the real_lt and real_eq arms each land on an  *)
(*  in-service piece). The draft's QleT'-to-(Qlt or Qeq) split  *)
(*  cannot walk the Qle division in this environment: Qle is    *)
(*  the single Z.le proposition (S02 note; a Prop division is   *)
(*  barred from Set); instead walk the Qcompare three-way       *)
(*  decision (comparison : Set, destructible, zero classical    *)
(*  logic): Eq discharges the real_eq arm, Lt discharges the    *)
(*  real_lt arm, Gt is annihilated against the boolean          *)
(*  reflection of QleT'.                                        *)
(* ============================================================ *)
Lemma pir_const_le : forall c d : Q,
  QleT' c d -> real_le (real_const c) (real_const d).
Proof.
  intros c d Hcd.
  unfold QleT' in Hcd.
  destruct (Qcompare c d) eqn:E.
  - right. apply pir_const_qeqT. apply qeq_imp_qeqT.
    apply Qeq_alt. exact E.
  - left. apply real_const_lt. apply Qlt_to_QltT. apply Qlt_alt. exact E.
  - exfalso.
    unfold Qle_bool in Hcd. rewrite E in Hcd. inversion Hcd.
Qed.

(* ============================================================ *)
(*  Piece 3 main piece: the Real-face hookup of monotonicity.   *)
(*  Premise = coefficient-wise order (audit note 4: the         *)
(*  PintMono premise forall i, QleT' (pint_coeff p i)           *)
(*  (pint_coeff q i), equal-length-free - not a pointwise       *)
(*  function order; the statement face does not overclaim       *)
(*  strength). The PintMono monotonicity engine is consumed,    *)
(*  never re-proved (one-journal discipline).                   *)
(* ============================================================ *)
Theorem pir_integral_mono_real : forall p q : list Q,
  (forall i : nat, QleT' (pint_coeff p i) (pint_coeff q i)) ->
  real_le (pir_integral_real p) (pir_integral_real q).
Proof.
  intros p q Hcoeff.
  unfold pir_integral_real.
  apply pir_const_le.
  exact (pm_pointwise_le_integral p q Hcoeff).
Qed.

(* ============================================================ *)
(*  Piece 4-a: the Real reading of integral(1) == 1 (the        *)
(*  pint_integral_one lift). real_one (the sequence fun _ => 1) *)
(*  and real_const (1#1) are not definitionally equal           *)
(*  (heterogeneous existT proof slots), so walk real_eq_trans   *)
(*  with both arms: the constant-identity arm (piece 2) plus    *)
(*  the pointwise zero-difference arm (real_eq_of_zero_diff;    *)
(*  the projT1 real_one projection closes by cbn, same as the   *)
(*  S07 precedent).                                             *)
(* ============================================================ *)
Theorem pir_integral_one_real :
  real_eq (pir_integral_real (pint_pow_poly 0)) real_one.
Proof.
  unfold pir_integral_real.
  apply (real_eq_trans
           (real_const (pint_integral (pint_pow_poly 0)))
           (real_const (1 # 1))
           real_one).
  - apply pir_const_qeqT. exact pint_integral_one.
  - apply real_eq_of_zero_diff. intros n.
    assert (Hc1 : projT1 (real_const (1 # 1)) n == (1 # 1))
      by (apply qeqT_imp_qeq; apply real_const_proj).
    assert (Ho1 : projT1 real_one n == 1) by (cbn [projT1]; reflexivity).
    assert (Hd : projT1 (real_const (1 # 1)) n - projT1 real_one n == 0).
    { rewrite Hc1. rewrite Ho1. ring. }
    exact (qeq_imp_qeqT _ _ Hd).
Qed.

(* ============================================================ *)
(*  Piece 4-b: the non-negativity reading (strict form): all    *)
(*  coefficients QltT 0 implies 0 < the Real reading            *)
(*  (pm_integral_pos_strict plus real_const_pos; statement      *)
(*  face real_lt with the witness carried by sigT, Set).        *)
(* ============================================================ *)
Theorem pir_integral_pos_real : forall p : list Q,
  (forall i : nat, QltT 0 (pint_coeff p i)) ->
  real_lt real_zero (pir_integral_real p).
Proof.
  intros p H.
  unfold pir_integral_real.
  exact (real_const_pos (pint_integral p) (pm_integral_pos_strict p H)).
Qed.

(* ============================================================ *)
(*  Assumption audit record: Print Assumptions (compile-time    *)
(*  stdout, rechecked at verification).                         *)
(* ============================================================ *)

Print Assumptions pir_const_qeqT.
Print Assumptions pir_integral_mono_real.
Print Assumptions pir_integral_one_real.
Print Assumptions pir_integral_pos_real.
