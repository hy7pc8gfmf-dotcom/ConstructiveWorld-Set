(* ConstructiveWorld-Set -- KLWallClosed: the closed end of the KL wall
   (the zero-degenerate branch of the power-monotonicity closure). *)
(** * KLWallClosed: closed-end assembly of the KL-wall power contraction,
    carried on Set.

    Mission.  The Real-carrier global closed-end theorem
      [klc_closed_powb_mono] ((1-eta)^{t1} <=_B (1-eta)^t on the whole
      carrier, under 0 <= eta <= 1), the two Q-carrier branch theorems
      [klc_strict_branch] (strict-shrink) and [klc_one_branch]
      (zero-degenerate), the Q-carrier assembly [klc_closed_Q]
      (decidable split x uniform contraction x branch-extra
      certificate, packaged as a [sigT] pair), and the weak-premise
      lemmas [klc_powb_mono_weak] and [klc_le_mult_r_weak].

    Dependencies.  The chain S01..S15 of this development,
      [UpRealLeB], [UpRealLeB2] and [G07_KLWall]; Stdlib [PeanoNat],
      [QArith.Qring], [Lia], [Extraction].

    References.  ConstructiveWorld-Main [KLWallClosed]; handling of the
      geometric contraction-rate eta = 1 endpoint with a zero
      degenerate branch (closed-end repair of a Pinsker-type proof).

    Constructivity.  All statements are carried by Set (order
      predicates and equality are Set-valued, no Prop leakage); every
      proof ends in [Qed]; no axioms, nothing left open, no classical
      logic; [Print Assumptions] reports Closed for the six main
      statements.

    Build.  [rocq c -native-compiler no -q -Q . "" KLWallClosed.v] on
      Rocq 9.1.0, compilation wrapped by the cpu_guard wrapper. *)

From Stdlib Require Import PeanoNat.
From Stdlib Require Import QArith.Qring.
From Stdlib Require Import Lia.
From Stdlib Require Import Extraction.
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
Require Import UpRealLeB.
Require Import UpRealLeB2.
Require Import G07_KLWall.

(* ============================================================ *)
(* Part A: three Q-layer reshaping lemmas (the decidable split        *)
(*         behind the two closed-end branches)                        *)
(* ============================================================ *)

(* eta < 1 (QltT) gives 0 < 1-eta (QltT): the Q-layer source of the strict-branch positivity certificate *)
Lemma klc_q_lt_zero_minus : forall eta : Q,
  QltT eta (1#1) -> QltT (0#1) (1 - eta)%Q.
Proof.
  intros eta H. apply Qlt_to_QltT.
  apply (proj1 (Qlt_minus_iff eta (1#1))).
  apply QltT_to_Qlt. exact H.
Qed.

(* eta <= 1 (QleT') gives 0 <= 1-eta (QleT'): Qopp reversal + left translation + ring reshaping *)
Lemma klc_q_bound_lower : forall eta : Q,
  QleT' eta (1#1) -> QleT' (0#1) (1 - eta)%Q.
Proof.
  intros eta H. apply Qle_to_QleT'.
  assert (H1 : Qle eta (1#1)) by (apply QleT'_to_Qle; exact H).
  pose proof (Qopp_le_compat eta (1#1) H1) as Ho.
  (* 9.1 adaptation: the stdlib name Qplus_le_compat_l was merged into
     Qplus_le_compat (x<=y -> z<=t -> x+z<=y+t) with the right factor
     taken by reflexivity; the conclusion shape is aligned with the goal
     by ring reshaping (the argument-order difference on the Z carrier
     of Q is not interchangeable) *)
  pose proof (Qplus_le_compat (Qopp (1#1)) (Qopp eta) (1#1) (1#1) Ho (Qle_refl (1#1))) as Hp.
  assert (E0 : (Qplus (Qopp (1#1)) (1#1))%Q == (0#1)) by ring.
  assert (E0b : (Qplus (Qopp eta) (1#1))%Q == (Qplus (1#1) (Qopp eta))%Q) by ring.
  rewrite E0, E0b in Hp. exact Hp.
Qed.

(* 0 <= eta (QleT') gives 1-eta <= 1 (QleT'): Qopp reversal + left translation + ring reshaping *)
Lemma klc_q_bound_upper : forall eta : Q,
  QleT' (0#1) eta -> QleT' (1 - eta)%Q (1#1).
Proof.
  intros eta H. apply Qle_to_QleT'.
  assert (H0 : Qle (0#1) eta) by (apply QleT'_to_Qle; exact H).
  pose proof (Qopp_le_compat (0#1) eta H0) as Ho.
  assert (Ez : (Qopp (0#1))%Q == (0#1)) by ring.
  rewrite Ez in Ho.
  pose proof (Qplus_le_compat (1#1) (1#1) (Qopp eta) (0#1) (Qle_refl (1#1)) Ho) as Hp.
  assert (E1 : (Qplus (1#1) (0#1))%Q == (1#1)) by ring.
  rewrite E1 in Hp.
  exact Hp.
Qed.

(* ============================================================ *)
(* Part B: three real_const order-transfer lemmas (lifting the        *)
(*         Q-carrier contraction rate into the Real layer)            *)
(* ============================================================ *)

Lemma klc_const_eq : forall c d : Q,
  QeqT c d -> real_eq (real_const c) (real_const d).
Proof.
  intros c d H. unfold QeqT in H.
  destruct (Qcompare c d) eqn:E; try rewrite E in H; simpl in H.
  - (* Eq branch: after the Qeq_alt reflection the pointwise constant difference is zero *)
    apply real_eq_of_zero_diff. intro n.
    apply qeq_imp_qeqT.
    rewrite (qeqT_imp_qeq _ _ (real_const_proj c n)),
            (qeqT_imp_qeq _ _ (real_const_proj d n)).
    rewrite (proj2 (Qeq_alt c d) E). ring.
  - inversion H.
  - inversion H.
Qed.

(* Order along real_const is transferred from QleT' to real_le (Or(lt,eq) assembled branch by branch) *)
Lemma klc_const_le : forall c d : Q,
  QleT' c d -> real_le (real_const c) (real_const d).
Proof.
  intros c d H. unfold QleT', Qle_bool in H.
  destruct (Qcompare c d) eqn:E; try rewrite E in H; simpl in H.
  - (* Eq branch: real_const equality reshaping *)
    assert (HQ : QeqT c d) by (unfold QeqT; rewrite E; exact H).
    exact (inr (klc_const_eq c d HQ)).
  - (* Lt branch: the strict order of real_const passes through directly *)
    assert (HL : Qlt c d) by (apply Qlt_alt; exact E).
    exact (inl (real_const_lt c d (Qlt_to_QltT _ _ HL))).
  - (* Gt is refuted by the reflection of QleT' *)
    destruct (id_false_true H).
Qed.

(* The closed-end decidable split: the three-way Qcompare split yields
   exactly one of the strict branch / the zero-degenerate branch.
   The second branch takes QeqT (the bool-reflection form) -- the Id
   branch of the S02 QleT is not constructively available for a variable
   eta (the same verdict as the upstream note), so this lemma is a
   constructible refinement of QleT. *)
Lemma klc_split_one : forall eta : Q,
  QleT' eta (1#1) -> sum (QltT eta (1#1)) (QeqT eta (1#1)).
Proof.
  intros eta H. unfold QleT', Qle_bool in H.
  destruct (Qcompare eta (1#1)) eqn:E; try rewrite E in H; simpl in H.
  - (* Eq branch: the zero-degenerate branch (bool-reflection form) *)
    assert (HQ : QeqT eta (1#1)) by (unfold QeqT; rewrite E; exact H).
    exact (inr HQ).
  - (* Lt branch: the strict-shrink branch *)
    assert (HL : QltT eta (1#1)) by (unfold QltT, Qlt_bool; rewrite E; exact H).
    exact (inl HL).
  - (* Gt is refuted by the reflection of QleT' *)
    destruct (id_false_true H).
Qed.

(* ============================================================ *)
(* Part C: Real-layer weak order algebra (the closed-end core under   *)
(*         the weak premise 0 <= eta <= 1; the trichotomy law is      *)
(*         never used)                                                *)
(* ============================================================ *)

Lemma klc_le_refl : forall x : Real, real_le x x.
Proof. intros x. exact (inr (real_eq_refl x)). Qed.

Lemma klc_le_id_l : forall a b c : Real,
  real_eq a b -> real_le b c -> real_le a c.
Proof.
  intros a b c Hab Hbc. unfold real_le in Hbc. destruct Hbc as [Hlt | Heq].
  - exact (inl (real_eq_lt_lt a b c Hab Hlt)).
  - exact (inr (real_eq_trans a b c Hab Heq)).
Qed.

Lemma klc_le_id_r : forall a b c : Real,
  real_eq b c -> real_le a b -> real_le a c.
Proof.
  intros a b c Hbc Hab. unfold real_le in Hab. destruct Hab as [Hlt | Heq].
  - exact (inl (real_lt_eq_lt a b c Hlt Hbc)).
  - exact (inr (real_eq_trans a b c Heq Hbc)).
Qed.

(* Weak right-monotonicity of multiplication: a <= b and 0 <= c give
   a*c <= b*c.  All four branches of Or(lt,eq) are assembled: the
   lt*lt branch goes through real_mult_lt_compat; the branches
   containing eq go through real_eq_mult_compat + real_mult_zero(_l)
   equality reshaping -- zero exact comparisons. *)
Lemma klc_le_mult_r_weak : forall a b c : Real,
  real_le a b -> real_le real_zero c ->
  real_le (real_mult a c) (real_mult b c).
Proof.
  intros a b c Hab Hc. unfold real_le in Hab, Hc.
  destruct Hab as [Hlt | Heq]; destruct Hc as [Hc | Hc0].
  - exact (inl (real_mult_lt_compat a b c Hlt Hc)).
  - assert (HL : real_eq (real_mult a c) real_zero).
    { apply (real_eq_trans _ (real_mult a real_zero) _).
      - exact (RealSetoid.real_eq_mult_compat a c a real_zero
                 (real_eq_refl a) (real_eq_sym _ _ Hc0)).
      - apply real_mult_zero. }
    assert (HR : real_eq (real_mult b c) real_zero).
    { apply (real_eq_trans _ (real_mult b real_zero) _).
      - exact (RealSetoid.real_eq_mult_compat b c b real_zero
                 (real_eq_refl b) (real_eq_sym _ _ Hc0)).
      - apply real_mult_zero. }
    exact (inr (real_eq_trans (real_mult a c) real_zero (real_mult b c)
                  HL (real_eq_sym _ _ HR))).
  - exact (inr (RealSetoid.real_eq_mult_compat a c b c Heq (real_eq_refl c))).
  - exact (inr (RealSetoid.real_eq_mult_compat a c b c Heq (real_eq_refl c))).
Qed.

(* Multiplication is closed under non-negativity: 0 <= a and 0 <= b give 0 <= a*b (all four Or branches assembled the same way) *)
Lemma klc_mult_nonneg : forall a b : Real,
  real_le real_zero a -> real_le real_zero b ->
  real_le real_zero (real_mult a b).
Proof.
  intros a b Ha Hb. unfold real_le in Ha, Hb.
  destruct Ha as [Ha | Ha0]; destruct Hb as [Hb | Hb0].
  - exact (inl (real_mult_positive a b Ha Hb)).
  - assert (HL : real_eq (real_mult a b) real_zero).
    { apply (real_eq_trans _ (real_mult a real_zero) _).
      - exact (RealSetoid.real_eq_mult_compat a b a real_zero
                 (real_eq_refl a) (real_eq_sym _ _ Hb0)).
      - apply real_mult_zero. }
    exact (inr (real_eq_sym _ _ HL)).
  - assert (HL : real_eq (real_mult a b) real_zero).
    { apply (real_eq_trans _ (real_mult real_zero b) _).
      - exact (RealSetoid.real_eq_mult_compat a b real_zero b
                 (real_eq_sym _ _ Ha0) (real_eq_refl b)).
      - apply (real_eq_trans (real_mult real_zero b)
                 (real_mult b real_zero) real_zero).
        + apply real_mult_comm.
        + apply real_mult_zero. }
    exact (inr (real_eq_sym _ _ HL)).
  - assert (HL : real_eq (real_mult a b) real_zero).
    { apply (real_eq_trans _ (real_mult real_zero b) _).
      - exact (RealSetoid.real_eq_mult_compat a b real_zero b
                 (real_eq_sym _ _ Ha0) (real_eq_refl b)).
      - apply (real_eq_trans (real_mult real_zero b)
                 (real_mult b real_zero) real_zero).
        + apply real_mult_comm.
        + apply real_mult_zero. }
    exact (inr (real_eq_sym _ _ HL)).
Qed.

(* Weak positivity induction: 0 <= base gives 0 <= base^t (the global powb_pow form, zero strict-positivity premise) *)
Lemma klc_powb_nonneg : forall (base : Real) (t : nat),
  real_le real_zero base -> real_le real_zero (powb_pow base t).
Proof.
  intros base t Hb. induction t as [| m IH].
  - exact (inl real_lt_zero_one).
  - cbn [powb_pow]. exact (klc_mult_nonneg base (powb_pow base m) Hb IH).
Qed.

(* The unconditional reshaping base for (1-eta)+eta == 1 (the same
   Heqsum chain as G07 powb_one_minus_eta_base_le_one:
   assoc/comm/plus_opp/plus_zero, with no premises) *)
Lemma klc_one_minus_eta_plus_eta_eq_one : forall eta : Real,
  real_eq (real_plus (real_plus real_one (real_opp eta)) eta) real_one.
Proof.
  intro eta.
  apply (real_eq_trans _ (real_plus real_one (real_plus (real_opp eta) eta)) _).
  - apply real_eq_sym. apply real_plus_assoc.
  - apply (real_eq_trans _ (real_plus real_one (real_plus eta (real_opp eta))) _).
    + apply (RealSetoid.real_eq_plus_compat real_one
               (real_plus (real_opp eta) eta) real_one
               (real_plus eta (real_opp eta))).
      * apply real_eq_refl.
      * apply real_plus_comm.
    + apply (real_eq_trans _ (real_plus real_one real_zero) _).
      * apply (RealSetoid.real_eq_plus_compat real_one
                 (real_plus eta (real_opp eta)) real_one real_zero).
        -- apply real_eq_refl.
        -- apply real_plus_opp.
      * apply real_plus_zero.
Qed.

(* The closed-end upper bound: 0 <= eta gives 1-eta <= 1 (the weak form
   of the main G07 theorem -- the lt branch: (1-eta) < (1-eta)+eta == 1;
   the eq branch (eta==0): (1-eta) == (1-eta)+eta == 1) *)
Lemma klc_one_minus_eta_le_one_weak : forall eta : Real,
  real_le real_zero eta ->
  real_le (real_plus real_one (real_opp eta)) real_one.
Proof.
  intros eta H0. unfold real_le in H0. destruct H0 as [Hlt | Heq].
  - pose proof (real_lt_plus_r_zero (real_plus real_one (real_opp eta)) eta
                  Hlt) as Hlt0.
    exact (inl (real_lt_eq_lt (real_plus real_one (real_opp eta))
                  (real_plus (real_plus real_one (real_opp eta)) eta)
                  real_one Hlt0 (klc_one_minus_eta_plus_eta_eq_one eta))).
  - assert (He1 : real_eq (real_plus real_one (real_opp eta))
                    (real_plus (real_plus real_one (real_opp eta)) eta)).
    { apply (real_eq_trans _ (real_plus (real_plus real_one (real_opp eta))
                                real_zero) _).
      - apply real_eq_sym. apply real_plus_zero.
      - apply (RealSetoid.real_eq_plus_compat
                 (real_plus real_one (real_opp eta)) real_zero
                 (real_plus real_one (real_opp eta)) eta
                 (real_eq_refl (real_plus real_one (real_opp eta))) Heq). }
    exact (inr (real_eq_trans (real_plus real_one (real_opp eta))
                  (real_plus (real_plus real_one (real_opp eta)) eta)
                  real_one He1 (klc_one_minus_eta_plus_eta_eq_one eta))).
Qed.

(* The closed-end lower bound: eta <= 1 gives 0 <= 1-eta (Qopp reversal +
   addition compatibility + the (1+-1)==0 reshaping; the eta==1 branch
   supplies the Or right component, the equation 0 == 1-1 -- the <=
   certificate form of the zero-degenerate branch) *)
Lemma klc_one_minus_eta_nonneg_weak : forall eta : Real,
  real_le eta real_one ->
  real_le real_zero (real_plus real_one (real_opp eta)).
Proof.
  intros eta H1.
  pose proof (real_opp_le_compat eta real_one H1) as Hopp.
  pose proof (real_le_plus_compat real_one real_one
                (real_opp real_one) (real_opp eta)
                (klc_le_refl real_one) Hopp) as Hp.
  exact (klc_le_id_l (real_plus real_one (real_opp real_one)) real_zero
           (real_plus real_one (real_opp eta)) (real_plus_opp real_one) Hp).
Qed.

(* ============================================================ *)
(* Part D: the powb weak-monotonicity core (an isomorphic copy of     *)
(*   powb_mono_dec with the strict premise removed: the strict        *)
(*   positivity premise real_lt real_zero base is weakened to real_le *)
(*   throughout -- the zero-degenerate branch base==0 is absorbed,    *)
(*   and the strict-positivity certificate named by the upstream      *)
(*   note is no longer needed)                                        *)
(* ============================================================ *)

(* base^{S n} <=_B base^n (weak-premise form: base*u <= 1*u == u; finished by <=_B transitivity) *)
Lemma klc_sub_one_weak : forall (base : Real) (n : nat),
  real_le real_zero base -> real_le base real_one ->
  real_le_b (powb_pow base (Datatypes.S n)) (powb_pow base n).
Proof.
  intros base n H0 H1. cbn [powb_pow]. unfold real_le_b. intros eps Heps.
  pose proof (klc_powb_nonneg base n H0) as Hunonneg.
  pose proof (klc_le_mult_r_weak base real_one (powb_pow base n) H1
                Hunonneg) as Hmul.
  pose proof (klc_le_id_r (real_mult base (powb_pow base n))
                (real_mult real_one (powb_pow base n)) (powb_pow base n)
                (real_eq_trans (real_mult real_one (powb_pow base n))
                   (real_mult (powb_pow base n) real_one)
                   (powb_pow base n)
                   (real_mult_comm real_one (powb_pow base n))
                   (real_mult_one (powb_pow base n))) Hmul) as Hle.
  pose proof (real_le_to_le_b (real_mult base (powb_pow base n))
                (powb_pow base n) Hle) as HB1.
  pose proof (real_le_to_le_b (powb_pow base n)
                (real_plus (powb_pow base n) eps)
                (inl (real_lt_plus_r_zero (powb_pow base n) eps Heps))) as HB2.
  exact (HB1 eps Heps).
Qed.

(* base^t <=_B 1 (weak-premise form) *)
Lemma klc_le_one_pow_weak : forall (base : Real) (t : nat),
  real_le real_zero base -> real_le base real_one ->
  real_le_b (powb_pow base t) real_one.
Proof.
  intros base t H0 H1. induction t as [| m IH].
  - exact (powb_le_b_refl real_one).
  - apply (real_le_b_trans (powb_pow base (Datatypes.S m))
             (powb_pow base m) real_one).
    + exact (klc_sub_one_weak base m H0 H1).
    + exact IH.
Qed.

(* The full power-monotonicity statement (the Set-carrier order bound NatLe; a branch-by-branch copy of powb_mono_dec, weak premise) *)
Lemma klc_powb_mono_weak : forall (base : Real) (m : nat),
  real_le real_zero base -> real_le base real_one ->
  forall n : nat, NatLe n m ->
  real_le_b (powb_pow base m) (powb_pow base n).
Proof.
  intros base m H0 H1. induction m as [| m IH]; intros n Hnm.
  - destruct n as [| n1].
    + exact (powb_le_b_refl (powb_pow base 0)).
    + (* NatLe (S n1) 0 is exactly the empty case, discharged by id_false_true *)
      destruct (id_false_true Hnm).
  - destruct n as [| n1].
    + exact (klc_le_one_pow_weak base (Datatypes.S m) H0 H1).
    + destruct (Nat.leb (Datatypes.S n1) m) eqn:E2.
      * (* S n1 <= m: the transitivity chain klc_sub_one_weak + IH *)
        apply (real_le_b_trans (powb_pow base (Datatypes.S m))
                 (powb_pow base m) (powb_pow base (Datatypes.S n1))).
        -- exact (klc_sub_one_weak base m H0 H1).
        -- apply IH.
           apply (NatLe_lift (Datatypes.S n1) m).
           apply (proj1 (Nat.leb_le (Datatypes.S n1) m)). exact E2.
      * (* n1 = m: after the Nat antisymmetry back-substitution, reflexivity *)
        pose proof (proj1 (Nat.leb_gt (Datatypes.S n1) m) E2) as Hgt.
        pose proof (NatLe_drop n1 m Hnm) as Hn1m.
        pose proof (Nat.le_antisymm n1 m Hn1m
                     (proj1 (Nat.lt_succ_r m n1) Hgt)) as Heq.
        rewrite Heq.
        exact (powb_le_b_refl (powb_pow base (Datatypes.S m))).
Qed.

(* ============================================================ *)
(* Part E: the main theorems.                                         *)
(*   E.1 the Real-carrier closed-end global form: under 0 <= eta <= 1 *)
(*       (the real_le Set-layer Or encoding), (1-eta)^{t1} <=_B       *)
(*       (1-eta)^t -- the zero-degenerate branch is absorbed by the   *)
(*       weak monotonicity, which is exactly the <=_B form of the     *)
(*       separate zero-degenerate branch required by the upstream     *)
(*       note.                                                        *)
(*   E.2/E.3 the two Q-carrier branch theorems (the strict-shrink     *)
(*       branch + the zero-degenerate non-increasing branch).         *)
(*   E.4 the Q-carrier closed-end assembly: decidable split x uniform *)
(*       contraction x branch-extra certificate, packaged as a sigT.  *)
(* ============================================================ *)

Theorem klc_closed_powb_mono : forall (eta : Real) (t t1 : nat),
  real_le real_zero eta -> real_le eta real_one -> NatLe t t1 ->
  real_le_b (powb_pow (real_plus real_one (real_opp eta)) t1)
            (powb_pow (real_plus real_one (real_opp eta)) t).
Proof.
  intros eta t t1 H0 H1 Hle.
  exact (klc_powb_mono_weak (real_plus real_one (real_opp eta)) t1
           (klc_one_minus_eta_nonneg_weak eta H1)
           (klc_one_minus_eta_le_one_weak eta H0) t Hle).
Qed.

(* The strict-shrink branch: 0 <= eta < 1 (Q carrier) gives the strict
   positivity certificate 1-eta > 0 plus the full <=_B contraction.
   The strict positivity certificate is exactly what the upstream
   verdict found missing (the Real layer cannot separate 1-eta==0 from
   1-eta>0) -- on the Q carrier it is obtained constructively by the
   decidable Qcompare split. *)
Theorem klc_strict_branch : forall (eta : Q) (t t1 : nat),
  QleT' (0#1) eta -> QltT eta (1#1) -> NatLe t t1 ->
  prod (real_lt real_zero (real_const (1 - eta)%Q))
       (real_le_b (powb_pow (real_const (1 - eta)%Q) t1)
                  (powb_pow (real_const (1 - eta)%Q) t)).
Proof.
  intros eta t t1 H0 Hlt Hle. split.
  - exact (real_const_pos (1 - eta)%Q (klc_q_lt_zero_minus eta Hlt)).
  - apply (klc_powb_mono_weak (real_const (1 - eta)%Q) t1).
    + apply klc_const_le. apply Qle_to_QleT'.
      apply Qlt_le_weak.
      apply (proj1 (Qlt_minus_iff eta (1#1))).
      apply QltT_to_Qlt. exact Hlt.
    + apply klc_const_le. exact (klc_q_bound_upper eta H0).
    + exact Hle.
Qed.

(* The zero-degenerate non-increasing branch: eta == 1 (QeqT) gives 1-eta == 0, a constant-zero power chain, where <=_B monotonicity holds trivially *)
Theorem klc_one_branch : forall (eta : Q) (t t1 : nat),
  QeqT eta (1#1) -> NatLe t t1 ->
  real_le_b (powb_pow (real_const (1 - eta)%Q) t1)
            (powb_pow (real_const (1 - eta)%Q) t).
Proof.
  intros eta t t1 Heq Hle. unfold QeqT in Heq.
  destruct (Qcompare eta (1#1)) eqn:E; try rewrite E in Heq; simpl in Heq.
  - (* Eq branch: eta == 1 gives 1-eta == 0, a constant-zero power chain *)
    pose proof (proj2 (Qeq_alt eta (1#1)) E) as Het.
    assert (Hz : (1 - eta)%Q == (0#1)) by (rewrite Het; ring).
    assert (Hb1 : QleT' (0#1) (1 - eta)%Q)
      by (apply Qle_to_QleT'; rewrite Hz; apply Qle_refl).
    assert (Hb2 : QleT' (1 - eta)%Q (1#1))
      by (apply Qle_to_QleT'; rewrite Hz; unfold Qle; simpl; lia).
    apply (klc_powb_mono_weak (real_const (1 - eta)%Q) t1).
    + apply klc_const_le. exact Hb1.
    + apply klc_const_le. exact Hb2.
    + exact Hle.
  - inversion Heq.
  - inversion Heq.
Qed.

(* The closed-end assembly (Q carrier): 0 <= eta <= 1 gives the sigT
   combination "decidable-split certificate s x (uniform <=_B
   contraction x branch-extra certificate)":
   the inl branch appends (1-eta)^{t1} > 0 (the strict positivity
   certificate -- the constructive arrival of the piece the upstream
   note found missing),
   the inr branch appends unit (trivial for the zero-degenerate branch). *)
Theorem klc_closed_Q : forall (eta : Q) (t t1 : nat),
  QleT' (0#1) eta -> QleT' eta (1#1) -> NatLe t t1 ->
  sigT (fun s : sum (QltT eta (1#1)) (QeqT eta (1#1)) =>
    prod (real_le_b (powb_pow (real_const (1 - eta)%Q) t1)
                    (powb_pow (real_const (1 - eta)%Q) t))
         (match s return Set with
          | inl _ => real_lt real_zero (powb_pow (real_const (1 - eta)%Q) t1)
          | inr _ => unit
          end)).
Proof.
  intros eta t t1 H0 H1 Hle.
  pose proof (klc_split_one eta H1) as Hs.
  exists Hs. split.
  - (* The uniform <=_B contraction: shared by both branches (the weak monotonicity holds globally) *)
    apply (klc_powb_mono_weak (real_const (1 - eta)%Q) t1).
    + apply klc_const_le. exact (klc_q_bound_lower eta H1).
    + apply klc_const_le. exact (klc_q_bound_upper eta H0).
    + exact Hle.
  - (* The branch-extra certificates *)
    destruct Hs as [Hlt | Heq].
    + exact (powb_pos_lt (real_const (1 - eta)%Q) t1
               (real_const_pos (1 - eta)%Q (klc_q_lt_zero_minus eta Hlt))).
    + exact tt.
Qed.

(* ============================================================ *)
(* Verification audit: the extraction must show an Obj.magic count    *)
(* of 0, and [Print Assumptions] of the statements must report the    *)
(* closed context.                                                    *)
(* ============================================================ *)

Extraction "klc_G3.ml" klc_closed_powb_mono klc_closed_Q klc_strict_branch
  klc_one_branch klc_split_one klc_powb_mono_weak.

Print Assumptions klc_closed_powb_mono.
Print Assumptions klc_closed_Q.
Print Assumptions klc_strict_branch.
Print Assumptions klc_one_branch.
Print Assumptions klc_split_one.
Print Assumptions klc_powb_mono_weak.
