(* ConstructiveWorld-Set -- Q tools and Real gluing for the Cauchy rational proxy of the logarithmic Real level. *)

(** * UpReqMixRationalProxy_R2: Q-layer tools, Real gluing, and Q-layer binary search.

    Mission.  The Q-layer tool family behind the Cauchy rational proxy of the
      logarithmic Real level: powers, minima, margins [rp_qpow_pos],
      [rp_qmin_le_l], [rp_eps_margin]; the Real gluing family [rp_lt_gap],
      [rp_lt_plus_r], [rp_minus_lt_swap], [rp_const_eq_down], [rp_const_le_up],
      [rp_qmult_nonneg]; and the Qle_bool-driven binary search [rp_bsearch]
      with feasibility and bisection bounds [rp_bsearch_pass], [rp_bsearch_lo],
      [rp_bsearch_hi].

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qring], [QArith.Qround],
      [QArith.Qabs], [ZArith], [Lia].  Requires [S01_BaseRing],
      [S02_CauchyComplete], [S03_QExp], [S04_RealExpLogConv], [S05_AlignmentGRPO],
      [S06_DiffSamplingGibbs], [S07_RealSetoidExpLog], [S08_RealMainlineDPO],
      [S09_EntropyReal], [S10_KVQuantTrig], [S11_TP3B5], [S12_B5RecycleSF],
      [S13_NLiveAudit], [S14_B5BatchBlock], [S15_TailFEPUp], [UpTVDoeblin] of this development.

    References.  This development, UpReqMixRationalProxy_R2.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" UpReqMixRationalProxy_R2.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 00015ff4]. *)
From Stdlib Require Import QArith.QArith.
From Stdlib Require Import QArith.Qring.
From Stdlib Require Import QArith.Qround.
From Stdlib Require Import QArith.Qabs.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Qfield.
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
(* Section 0. Q-layer tools: powers, minima, and margins. *)
(* ============================================================ *)

Fixpoint rp_qpow (a : Q) (k : nat) {struct k} : Q :=
  match k with
  | Datatypes.O => 1#1
  | Datatypes.S m => a * rp_qpow a m
  end.

Lemma rp_qpow_S : forall (a : Q) (k : nat), rp_qpow a (Datatypes.S k) == a * rp_qpow a k.
Proof. intros a k. reflexivity. Qed.

Lemma rp_qpow_pos : forall (a : Q) (k : nat), QltT 0 a -> QltT 0 (rp_qpow a k).
Proof.
  intros a k Ha. induction k as [| k IHk].
  - exact qltT_0_1.
  - exact (qmult_ltT_0_compat a (rp_qpow a k) Ha IHk).
Qed.

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

Definition rp_qmin (a b : Q) : Q :=
  match Qcompare a b with
  | Gt => b
  | _ => a
  end.

Lemma rp_qmin_le_l : forall a b : Q, Qle (rp_qmin a b) a.
Proof.
  intros a b. unfold rp_qmin. destruct (Qcompare a b) eqn:E.
  - apply Qle_refl.
  - apply Qle_refl.
  - apply Qlt_le_weak. apply (proj2 (Qlt_alt b a)).
    rewrite <- (Qcompare_antisym a b). rewrite E. reflexivity.
Qed.

Lemma rp_qmin_le_r : forall a b : Q, Qle (rp_qmin a b) b.
Proof.
  intros a b. unfold rp_qmin. destruct (Qcompare a b) eqn:E.
  - apply (proj2 (Qle_alt a b)). rewrite E. discriminate.
  - apply Qlt_le_weak. apply (proj2 (Qlt_alt a b)). exact E.
  - apply Qle_refl.
Qed.

Lemma rp_qmin_pos : forall a b : Q, QltT 0 a -> QltT 0 b -> QltT 0 (rp_qmin a b).
Proof.
  intros a b Ha Hb. unfold rp_qmin. destruct (Qcompare a b); assumption.
Qed.

Lemma rp_qmin_pos3 : forall a b c : Q,
  QltT 0 a -> QltT 0 b -> QltT 0 c -> QltT 0 (rp_qmin (rp_qmin a b) c).
Proof.
  intros a b c Ha Hb Hc. unfold rp_qmin.
  destruct (Qcompare (match a ?= b with Gt => b | _ => a end) c).
  - exact (rp_qmin_pos a b Ha Hb).
  - exact (rp_qmin_pos a b Ha Hb).
  - exact Hc.
Qed.

Definition rp_eps (d0 db d1 : Q) : Q := rp_qmin (rp_qmin d0 db) d1 / 8.

Lemma rp_eps_pos : forall d0 db d1 : Q,
  QltT 0 d0 -> QltT 0 db -> QltT 0 d1 -> QltT 0 (rp_eps d0 db d1).
Proof.
  intros d0 db d1 H0 Hb H1. unfold rp_eps.
  apply qltT_div_pos. apply rp_qmin_pos3; assumption. exact qltT_0_2.
Qed.

Lemma rp_eps_margin : forall d0 db d1 : Q, Qle (2 * rp_eps d0 db d1) (d0 / 4).
Proof.
  intros d0 db d1. unfold rp_eps.
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
      * apply rp_qmin_le_l.
      * apply rp_qmin_le_l.
    + apply Qlt_le_weak.
      exact (QltT_to_Qlt _ _ (qltT_div_pos (1#1) (4#1) qltT_0_1 qltT_0_4)).
Qed.

(* ============================================================ *)
(* Section 1. Q-proxy construction: core lemmas and comparison-transport helpers. *)
(* ============================================================ *)

Lemma rp_abs_minus_const_proj : forall (x : Real) (v : Q) (n : nat),
  projT1 (real_abs (real_minus_r x (real_const v))) n == Qabs (projT1 x n - v).
Proof. intros [u Hu] v n. reflexivity. Qed.

Lemma rp_qlt_eq_l : forall a a' b : Q, a == a' -> QltT a b -> QltT a' b.
Proof.
  intros a a' b Heq H. apply Qlt_to_QltT. apply Qlt_alt.
  rewrite <- (Qcompare_comp a a' Heq b b (Qeq_refl b)).
  exact (proj1 (Qlt_alt a b) (QltT_to_Qlt _ _ H)).
Qed.

Lemma rp_qlt_eq_rQ : forall a b b' : Q, b == b' -> Qlt a b -> Qlt a b'.
Proof.
  intros a b b' Heq H. apply Qlt_alt.
  rewrite <- (Qcompare_comp a a (Qeq_refl a) b b' Heq).
  exact (proj1 (Qlt_alt a b) H).
Qed.

Lemma rp_qlt_eq_r : forall a b b' : Q, b == b' -> QltT a b -> QltT a b'.
Proof.
  intros a b b' Heq H. apply Qlt_to_QltT. apply Qlt_alt.
  rewrite <- (Qcompare_comp a a (Qeq_refl a) b b' Heq).
  exact (proj1 (Qlt_alt a b) (QltT_to_Qlt _ _ H)).
Qed.

(* ============================================================ *)
(* Section 2. Real-layer gluing: order facts transported at the definitional collapse of the Real projections. *)
(* ============================================================ *)

(* Separation witness: x < y yields some e : Q with 0 < e and
   x + const e <= y; closed by [Defined] since the witness is consumed
   downstream.  After the pairs are destructed, projT1 (real_plus ...) n
   collapses definitionally, so [change] transports the goal directly. *)
Definition rp_lt_gap (x y : Real) (Hxy : real_lt x y) :
  sigT (fun e : Q => And (QltT 0 e) (real_le (real_plus x (real_const e)) y)).
Proof.
  destruct x as [u Hu]. destruct y as [v Hv].
  destruct Hxy as [e [He [N HN]]].
  exists (e / 2). split.
  - exact (qltT_div_pos e (2#1) He qltT_0_2).
  - left. exists (e / 2). split.
    + exact (qltT_div_pos e (2#1) He qltT_0_2).
    + exists N. intros n Hn.
      apply Qlt_to_QltT.
      apply (proj2 (Qlt_minus_iff (e / 2) (v n - (u n + e / 2))%Q)).
      apply (rp_qlt_eq_rQ 0%Q (v n - u n - e)%Q
               (v n - (u n + e / 2) + - (e / 2))%Q).
      * field.
      * apply (proj1 (Qlt_minus_iff e (v n - u n)%Q)).
        apply QltT_to_Qlt. exact (HN n Hn).
Defined.

(* Translation-invariance of the strict order: x < y implies x + c < y + c. *)
Lemma rp_lt_plus_r : forall (x y c : Real),
  real_lt x y -> real_lt (real_plus x c) (real_plus y c).
Proof.
  intros [u Hu] [v Hv] [w Hw] Hxy.
  destruct Hxy as [e [He [N HN]]].
  exists e. split.
  - exact He.
  - exists N. intros n Hn.
    apply (rp_qlt_eq_r e (v n - u n)%Q ((v n + w n) - (u n + w n))%Q).
    * field.
    * exact (HN n Hn).
Qed.

(* Order reversal under subtraction from one: x < y implies 1 - y < 1 - x. *)
Lemma rp_minus_lt_swap : forall x y : Real,
  real_lt x y -> real_lt (real_minus_r real_one y) (real_minus_r real_one x).
Proof.
  intros [u Hu] [v Hv] Hxy.
  destruct Hxy as [e [He [N HN]]].
  exists e. split.
  - exact He.
  - exists N. intros n Hn.
    change (QltT e ((1 + - u n) - (1 + - v n))%Q).
    apply (rp_qlt_eq_r e (v n - u n)%Q ((1 + - u n) - (1 + - v n))%Q).
    * field.
    * exact (HN n Hn).
Qed.

(* The complement 1 - const a is constant: real_eq_of_zero_diff carries the
   [Qabs] internally, so the statement itself carries no [Qabs] obligation. *)
Lemma rp_minus_const_eq : forall a : Q,
  real_eq (real_minus_r real_one (real_const a)) (real_const (1 - a)).
Proof.
  intros a. apply real_eq_of_zero_diff. intro n. apply qeq_imp_qeqT.
  cbn [projT1 real_plus real_opp real_minus_r real_one real_const]. ring.
Qed.

(* Constants are closed under addition and multiplication. *)
Lemma rp_const_plus_eq : forall a b : Q,
  real_eq (real_plus (real_const a) (real_const b)) (real_const (a + b)).
Proof.
  intros a b. apply real_eq_of_zero_diff. intro n. apply qeq_imp_qeqT.
  cbn [projT1 real_plus real_const]. ring.
Qed.

Lemma rp_const_mult_eq : forall a b : Q,
  real_eq (real_mult (real_const a) (real_const b)) (real_const (a * b)).
Proof.
  intros a b. apply real_eq_of_zero_diff. intro n. apply qeq_imp_qeqT.
  cbn [projT1 real_mult real_const]. ring.
Qed.

(* One is neutral for Real multiplication on the left: the match inside
   real_mult is stuck on a variable Real, so the pair is destructed first
   and the projections collapse afterwards. *)
Lemma rp_mult_one_l : forall x : Real, real_eq (real_mult real_one x) x.
Proof.
  intros [u Hu]. apply real_eq_of_zero_diff. intro n. apply qeq_imp_qeqT.
  cbn [projT1 real_mult real_one]. ring.
Qed.

(* Positivity of powers: 0 < a implies 0 < a^k. *)
Lemma rp_rpow_pos : forall (a : Real) (k : nat),
  real_lt real_zero a -> real_lt real_zero (tv_rpow a k).
Proof.
  intros a k Ha. induction k as [| k IHk].
  - exists (1 / 2)%Q. split.
    + exact (qltT_div_pos (1#1) (2#1) qltT_0_1 qltT_0_2).
    + exists Datatypes.O. intros n _.
      exact (qltT_half_lt_selfT (1#1) qltT_0_1).
  - exact (real_mult_pos_compat a (tv_rpow a k) Ha IHk).
Qed.

(* Monotone growth of powers: 0 < a and a <= b imply a^k <= b^k. *)
Lemma rp_rpow_le_mono : forall (a b : Real) (k : nat),
  real_lt real_zero a -> real_le a b -> real_le (tv_rpow a k) (tv_rpow b k).
Proof.
  intros a b k Ha Hab. induction k as [| k IHk].
  - apply (RealSetoid.real_eq_le). exact (real_eq_refl real_one).
  - apply (real_le_trans _ (real_mult b (tv_rpow a k)) (real_mult b (tv_rpow b k))).
    + apply (real_le_mult_compat a b (tv_rpow a k)).
      * exact (rp_rpow_pos a k Ha).
      * exact Hab.
    + apply (real_le_trans _ (real_mult (tv_rpow a k) b)).
      * apply (RealSetoid.real_eq_le). exact (real_mult_comm b (tv_rpow a k)).
      * apply (real_le_trans _ (real_mult (tv_rpow b k) b)).
        -- apply (real_le_mult_compat (tv_rpow a k) (tv_rpow b k) b).
           ++ exact (real_lt_le_trans real_zero a b Ha Hab).
           ++ exact IHk.
        -- apply (RealSetoid.real_eq_le). exact (real_mult_comm (tv_rpow b k) b).
Qed.

(* Bridge for equality and order along real_const, upward and downward. *)
Lemma rp_const_eq : forall c d : Q, c == d -> real_eq (real_const c) (real_const d).
Proof.
  intros c d Hcd. apply real_eq_of_zero_diff. intro n. apply qeq_imp_qeqT.
  cbn [projT1 real_const]. setoid_rewrite Hcd. ring.
Qed.

Lemma rp_const_eq_down : forall u v : Q,
  real_eq (real_const u) (real_const v) -> u == v.
Proof.
  intros u v Heq.
  destruct (Qcompare u v) eqn:E.
  - exact (proj2 (Qeq_alt u v) E).
  - exfalso.
    assert (Hlt : Qlt u v) by exact (proj2 (Qlt_alt u v) E).
    assert (Hpos : Qlt 0 (v + - u)%Q).
    { exact (proj1 (Qlt_minus_iff u v) Hlt). }
    assert (HH : QltT 0 ((v - u) / 2)).
    { apply qltT_div_pos; [apply Qlt_to_QltT; exact Hpos | exact qltT_0_2]. }
    destruct (Heq ((v - u) / 2)%Q HH) as [N HN].
    specialize (HN N (NatLe_lift N N (Nat.le_refl N))).
    change (QltT (Qabs (u - v)) ((v - u) / 2)) in HN.
    assert (Hab : Qabs (u - v) == (v - u)%Q).
    { apply Qeq_trans with (Qabs (v - u)).
      - exact (qeqT_imp_qeq _ _ (q_abs_minus_sym u v)).
      - exact (Qabs_pos (v - u) (Qlt_le_weak _ _ Hpos)). }
    pose proof (rp_qlt_eq_l _ _ _ Hab HN) as HN2.
    assert (Hh : QltT ((v - u) / 2) (v - u))
      by (apply qltT_half_lt_selfT; apply Qlt_to_QltT; exact Hpos).
    exact (Qlt_irrefl _ (Qlt_trans _ _ _ (QltT_to_Qlt _ _ HN2) (QltT_to_Qlt _ _ Hh))).
  - exfalso.
    assert (Hlt : Qlt v u).
    { apply (proj2 (Qlt_alt v u)).
      rewrite <- (Qcompare_antisym u v). rewrite E. reflexivity. }
    assert (Hpos : Qlt 0 (u + - v)%Q).
    { exact (proj1 (Qlt_minus_iff v u) Hlt). }
    assert (HH : QltT 0 ((u - v) / 2)).
    { apply qltT_div_pos; [apply Qlt_to_QltT; exact Hpos | exact qltT_0_2]. }
    destruct (Heq ((u - v) / 2)%Q HH) as [N HN].
    specialize (HN N (NatLe_lift N N (Nat.le_refl N))).
    change (QltT (Qabs (u - v)) ((u - v) / 2)) in HN.
    assert (Hab : Qabs (u - v) == (u - v)%Q).
    { exact (Qabs_pos (u - v) (Qlt_le_weak _ _ Hpos)). }
    pose proof (rp_qlt_eq_l _ _ _ Hab HN) as HN2.
    assert (Hh : QltT ((u - v) / 2) (u - v))
      by (apply qltT_half_lt_selfT; apply Qlt_to_QltT; exact Hpos).
    exact (Qlt_irrefl _ (Qlt_trans _ _ _ (QltT_to_Qlt _ _ HN2) (QltT_to_Qlt _ _ Hh))).
Qed.

Lemma rp_const_le_up : forall c d : Q,
  QleT' c d -> real_le (real_const c) (real_const d).
Proof.
  intros c d H. unfold QleT', Qle_bool in H.
  destruct (Qcompare c d) eqn:E.
  - exact (inr (rp_const_eq c d (proj2 (Qeq_alt c d) E))).
  - exact (inl (real_const_lt c d (Qlt_to_QltT _ _ (proj2 (Qlt_alt c d) E)))).
  - inversion H.
Qed.

Lemma rp_const_lt_down : forall c d : Q,
  real_lt (real_const c) (real_const d) -> Qlt c d.
Proof.
  intros c d H. destruct H as [e [He [N HN]]].
  assert (HN' : QltT e (d - c)).
  { specialize (HN N (NatLe_lift N N (Nat.le_refl N))).
    change (QltT e (d - c)) in HN. exact HN. }
  apply (proj2 (Qlt_minus_iff c d)).
  apply (Qlt_trans 0%Q e%Q (d + - c)%Q).
  - apply QltT_to_Qlt. exact He.
  - apply QltT_to_Qlt. exact HN'.
Qed.

Lemma rp_const_le_down : forall c d : Q,
  real_le (real_const c) (real_const d) -> QleT' c d.
Proof.
  intros c d H. unfold QleT', Qle_bool.
  destruct (Qcompare c d) eqn:E.
  - reflexivity.
  - reflexivity.
  - exfalso.
    unfold real_le in H. destruct H as [Hlt | Heq].
    + pose proof (rp_const_lt_down c d Hlt) as Hq.
      pose proof (proj1 (Qlt_alt c d) Hq) as Hq2.
      rewrite E in Hq2. discriminate Hq2.
    + pose proof (proj1 (Qeq_alt c d) (rp_const_eq_down c d Heq)) as Hq.
      rewrite E in Hq. discriminate Hq.
Qed.

(* Signs and order are lifted between the Z and Q layers. *)
Lemma rp_Qle_Z : forall j : Z, Qle 0 (j # 1) -> (0 <= j)%Z.
Proof.
  intros j Hj. destruct (Z.compare 0 j) eqn:E.
  - pose proof (proj1 (Z.compare_eq_iff 0 j) E). lia.
  - pose proof (proj1 (Z.compare_lt_iff 0 j) E). lia.
  - exfalso.
    assert (Hlt : Qlt (j # 1) (0 # 1)).
    { apply (proj2 (Qlt_alt (j # 1) (0 # 1))).
      change (j # 1 ?= 0 # 1)%Q with ((j * 1 ?= 0 * 1)%Z).
      rewrite Z.mul_1_r, Z.mul_1_r.
      exact (proj1 (Z.compare_lt_iff j 0) (proj1 (Z.compare_gt_iff 0 j) E)). }
    exact (Qlt_irrefl 0 (Qle_lt_trans 0 (j # 1) 0 Hj Hlt)).
Qed.

Lemma rp_Zle_Qle : forall a b : Z, (a <= b)%Z -> Qle (a # 1) (b # 1).
Proof.
  intros a b Hab.
  destruct (Z.compare a b) eqn:E.
  - rewrite <- (proj1 (Z.compare_eq_iff a b) E). apply Qle_refl.
  - apply Qlt_le_weak. apply (proj2 (Qlt_alt (a # 1) (b # 1))).
    change (a # 1 ?= b # 1)%Q with ((a * 1 ?= b * 1)%Z).
    rewrite Z.mul_1_r, Z.mul_1_r. exact E.
  - exfalso. apply (proj1 (Z.compare_gt_iff a b)) in E. lia.
Qed.

(* Non-negativity of Q multiplication: case analysis over the sign comparisons
   of a and b, with the contradictory cases closed by inversion. *)
Lemma rp_qmult_nonneg : forall a b : Q, QleT' 0 a -> QleT' 0 b -> QleT' 0 (a * b).
Proof.
  intros a b Ha Hb.
  unfold QleT', Qle_bool in Ha, Hb.
  destruct (Qcompare 0 a) eqn:Ea; destruct (Qcompare 0 b) eqn:Eb.
  - apply (qeq_leT' 0 _). apply qeq_imp_qeqT.
    rewrite <- (proj2 (Qeq_alt 0 a) Ea). ring.
  - apply (qeq_leT' 0 _). apply qeq_imp_qeqT.
    rewrite <- (proj2 (Qeq_alt 0 a) Ea). ring.
  - inversion Hb.
  - apply (qeq_leT' 0 _). apply qeq_imp_qeqT.
    rewrite <- (proj2 (Qeq_alt 0 b) Eb). ring.
  - exact (qltT_leT' _ _
             (qmult_ltT_0_compat a b (Qlt_to_QltT _ _ (proj2 (Qlt_alt 0 a) Ea))
                (Qlt_to_QltT _ _ (proj2 (Qlt_alt 0 b) Eb)))).
  - inversion Hb.
  - inversion Ha.
  - inversion Ha.
  - inversion Ha.
Qed.

(* ============================================================ *)
(* Section 3. The logarithmic search rp_bsearch: bisection driven by
   Qle_bool with structural termination on the fuel.
   Feasibility: the returned point r passes the test, t <= r.
   Minimality: r <= t + (hi - lo) / 2^fuel, the bracket halving each step.
   Every decision is taken at the Q layer by Qle_bool; the Real layer
   carries no order branching. *)
(* ============================================================ *)

Fixpoint rp_bsearch (t : Q) (fuel : nat) (lo hi : Q) {struct fuel} : Q :=
  match fuel with
  | Datatypes.O => hi
  | Datatypes.S f =>
      if Qle_bool t ((lo + hi) / 2)
      then rp_bsearch t f lo ((lo + hi) / 2)
      else rp_bsearch t f ((lo + hi) / 2) hi
  end.

(* Feasibility: the invariant Qle t hi is preserved along both branches; the
   left branch reads it off Qle_bool_iff. *)
Lemma rp_bsearch_pass : forall (t : Q) (fuel : nat) (lo hi : Q),
  Qle t hi -> Qle_bool t (rp_bsearch t fuel lo hi) = true.
Proof.
  intros t fuel. induction fuel as [| f IHf]; intros lo hi Ht.
  - apply (proj2 (Qle_bool_iff t hi)). exact Ht.
  - simpl. destruct (Qle_bool t ((lo + hi) / 2)) eqn:E.
    + apply IHf. exact (proj1 (Qle_bool_iff t ((lo + hi) / 2)) E).
    + exact (IHf ((lo + hi) / 2) hi Ht).
Qed.

(* Minimality as a double bracket: r lies in [lo, hi] and passes the test
   t <= r.  The wider convergence form r <= t + (hi - lo) / 2^fuel is the
   designated finalized target, not stated in this file's statement face:
   [field] along the atomic denominator rp_qpow (2#1) f generates a nonzero
   side-condition chain (it needs 2^f <> 0 together with the antitone image
   of Qopp), and the wide form closes once these two auxiliary lemmas are
   in place. *)

(* Half-point bounds with the literal denominator 2: field closes without
   side conditions. *)
Lemma rp_half_le_r : forall lo hi : Q, Qle lo hi -> Qle ((lo + hi) / 2) hi.
Proof.
  intros lo hi Hlh.
  apply (Qle_trans ((lo + hi) / 2) ((lo + hi) * (1#2)) hi).
  - assert (He : ((lo + hi) / 2)%Q == ((lo + hi) * (1#2))%Q) by field.
    rewrite He. apply Qle_refl.
  - apply (Qle_trans ((lo + hi) * (1#2)) ((hi + hi) * (1#2)) hi).
    + apply (Qmult_le_compat_r (lo + hi) (hi + hi)).
      * apply (Qplus_le_compat lo hi hi hi).
        -- exact Hlh.
        -- apply Qle_refl.
      * apply Qlt_le_weak. apply (proj2 (Qlt_alt 0 (1#2))). reflexivity.
    + assert (He : ((hi + hi) * (1#2))%Q == hi) by field.
      rewrite He. apply Qle_refl.
Qed.

Lemma rp_half_ge_l : forall lo hi : Q, Qle lo hi -> Qle lo ((lo + hi) / 2).
Proof.
  intros lo hi Hlh.
  apply (Qle_trans lo ((lo + lo) * (1#2)) ((lo + hi) / 2)).
  - assert (He : lo == ((lo + lo) * (1#2))%Q) by field.
    rewrite <- He. apply Qle_refl.
  - apply (Qle_trans ((lo + lo) * (1#2)) ((lo + hi) * (1#2)) ((lo + hi) / 2)).
    + apply (Qmult_le_compat_r (lo + lo) (lo + hi)).
      * apply (Qplus_le_compat lo lo lo hi).
        -- apply Qle_refl.
        -- exact Hlh.
      * apply Qlt_le_weak. apply (proj2 (Qlt_alt 0 (1#2))). reflexivity.
    + assert (He : ((lo + hi) * (1#2))%Q == ((lo + hi) / 2)%Q) by field.
      rewrite He. apply Qle_refl.
Qed.

(* Lower bound: r >= lo, preserved along both branches. *)
Lemma rp_bsearch_lo : forall (t : Q) (fuel : nat) (lo hi : Q),
  Qle lo hi -> Qle lo (rp_bsearch t fuel lo hi).
Proof.
  intros t fuel. induction fuel as [| f IHf]; intros lo hi Hlh.
  - exact Hlh.
  - simpl. destruct (Qle_bool t ((lo + hi) / 2)) eqn:E.
    + exact (IHf lo ((lo + hi) / 2) (rp_half_ge_l lo hi Hlh)).
    + apply (Qle_trans lo ((lo + hi) / 2) (rp_bsearch t f ((lo + hi) / 2) hi)).
      * exact (rp_half_ge_l lo hi Hlh).
      * apply (IHf ((lo + hi) / 2) hi).
        exact (rp_half_le_r lo hi Hlh).
Qed.

(* Upper bound: r <= hi, preserved along both branches. *)
Lemma rp_bsearch_hi : forall (t : Q) (fuel : nat) (lo hi : Q),
  Qle lo hi -> Qle (rp_bsearch t fuel lo hi) hi.
Proof.
  intros t fuel. induction fuel as [| f IHf]; intros lo hi Hlh.
  - apply Qle_refl.
  - simpl. destruct (Qle_bool t ((lo + hi) / 2)) eqn:E.
    + apply (Qle_trans (rp_bsearch t f lo ((lo + hi) / 2)) ((lo + hi) / 2) hi).
      * apply (IHf lo ((lo + hi) / 2)).
        exact (rp_half_ge_l lo hi Hlh).
      * exact (rp_half_le_r lo hi Hlh).
    + exact (IHf ((lo + hi) / 2) hi (rp_half_le_r lo hi Hlh)).
Qed.

(* ============================================================ *)
(* Assumption-surface evidence: the thirteen mission statements print
   as closed under the global context. *)
(* ============================================================ *)
Print Assumptions rp_qpow_pos.
Print Assumptions rp_qmin_le_l.
Print Assumptions rp_eps_margin.
Print Assumptions rp_lt_gap.
Print Assumptions rp_lt_plus_r.
Print Assumptions rp_minus_lt_swap.
Print Assumptions rp_const_eq_down.
Print Assumptions rp_const_le_up.
Print Assumptions rp_qmult_nonneg.
Print Assumptions rp_bsearch.
Print Assumptions rp_bsearch_pass.
Print Assumptions rp_bsearch_lo.
Print Assumptions rp_bsearch_hi.
