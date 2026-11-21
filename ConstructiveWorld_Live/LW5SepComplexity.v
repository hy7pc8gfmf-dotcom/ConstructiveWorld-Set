(* LW5SepComplexity -- minimal window-order separation of pi_L from the rationals:
   Mission.  Over the envelope column eps_n := 1/(n+1) of the Leibniz partial
     sums of pi, build windows lo_n := 4*pie_partial(M_n+1) - eps_n/4 and
     hi_n := 4*pie_partial(M_n) + eps_n/4 with M_n := 2*pie_modulus(eps_n/2)+1;
     provide the boolean deciders lw5n_inwin / lw5n_sep_dec, the bounded search
     lw5n_find with budget lw5n_bnd, the budgeted run lw5n_nsep with its
     upper-bound / hit / no-passing / least-index theorems, the pointwise
     correctness lw5n_inwin_close_pt, the certificate lw5n_outwin_sepdist, the
     growth cells with modulus chains pie_modulus(eps_n/{2,4,8}) =
     {8n+9,16n+17,32n+33}, the shape theorems, the transport corollaries and
     the budget caliber lw5n_bnd_caliber; the growth-law faces are future work
     (statement notes at their definition site).
   Dependencies.  Stdlib QArith.QArith, QArith.Qabs, QArith.Qround, ZArith.ZArith,
     Arith.Arith, Bool.Bool, Lia, Extraction, Lqa; and LW0LeibWindow, PiEnvelope,
     LW0MLicBridge, S01_BaseRing, S02_CauchyComplete, S03_QExp, S10_KVQuantTrig,
     S11_TP3B5, LW2SepTransport, UpReqIrrationalCriterion of this development.
   References.  PiEnvelope.v pi_rational_envelope (shared envelope witness;
     lw5n_win_pi re-derives the endpoints); LW0LeibWindow.v leiblw_dist_set
     (the leiblw_Id judgment face and boolean decider technique);
     LW2SepTransport.v lw2t_sep_transport_k (instantiated at k = 2, 4, 8).
   Constructivity.  Zero axioms, zero admissions, zero classical logic.  Every
     named statement is carried by Set: Q order by QltT'/QleT' or QleT, Q
     identities by QeqT, nat and Z identities by Id / leiblw_Id, nat order by
     NatLe and the local NatLt face lw5n_NatLt, conjunctions by And := prod,
     real statements by real_lt / real_eq / sigT; definitions and constructive
     theorems are transparent (Defined); proof bodies use stdlib Prop order
     lemmas plus Lia / Nia / Lqa; extraction gives Obj.magic = 0 on both faces
     and Print Assumptions Closed everywhere.
   Build.  coqc -q -Q <ConstructiveWorld_Live root> "" LW5SepComplexity.v compiles
     cleanly (exit 0); Q scope opens globally via QArith, nat notations %nat. *)

From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               ZArith.ZArith Arith.Arith Bool.Bool.
From Stdlib Require Import Lia.
Require Import LW0LeibWindow.
Require Import PiEnvelope.
Require Import LW0MLicBridge.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.

(* ============================================================ *)
(* Judgment-face helpers: elim/intro bridges between the Set     *)
(* carriers (Id, leiblw_Id, QltT', QeqT, NatLt) and the proof-   *)
(* position faces (Leibniz equality, Prop Q order, nat order).   *)
(* ============================================================ *)

(* leiblw_Id elimination: read the judgment face out as Leibniz equality. *)
Lemma lw5n_leib_id_eq : forall (A : Type) (x y : A), leiblw_Id x y -> x = y.
Proof.
  intros A x y H. destruct H. reflexivity.
Defined.

(* Id introduction: lift Leibniz equality into the Set judgment face. *)
Lemma lw5n_eq_id : forall (A : Set) (x y : A), x = y -> Id x y.
Proof. intros A x y H. rewrite H. apply id_refl. Defined.

(* QltT' read-out into Prop Qlt (two carrier steps: QltT' -> QltT -> Qlt). *)
Lemma lw5n_qltT'_qlt : forall x y : Q, QltT' x y -> Qlt x y.
Proof. intros x y H. apply QltT_to_Qlt. apply QltT'_to_Qlt. exact H. Defined.

(* QeqT symmetry over the QeqT face. *)
Lemma lw5n_qeqT_sym : forall x y : Q, QeqT x y -> QeqT y x.
Proof.
  intros x y H. apply qeq_imp_qeqT. apply Qeq_sym. apply (qeqT_imp_qeq _ _ H).
Defined.

(* Read-out of the in-window boolean under the Id face into Prop Qle. *)
Lemma lw5n_qleb_inv : forall x y : Q, leiblw_Id (leiblw_Qleb x y) true -> Qle x y.
Proof.
  intros x y H. unfold leiblw_Qleb in H.
  destruct (Qcompare_spec x y) as [Heq|Hlt|Hgt].
  - unfold Qeq, Qle in *. cbn [Qnum Qden] in *. nia.
  - apply Qlt_le_weak. exact Hlt.
  - exfalso. inversion H.
Defined.

(* Equality-face variant of the read-out, for hypotheses produced by the *)
(* boolean conjunction analysis. *)
Lemma lw5n_qleb_inv_eq : forall x y : Q, leiblw_Qleb x y = true -> Qle x y.
Proof.
  intros x y H. apply lw5n_qleb_inv. apply leiblw_eq_id. exact H.
Defined.

(* Local NatLt judgment face (the boolean decision identity for nat <), *)
(* with the elim/intro twin pair over the NatLe carrier.                *)
Definition lw5n_NatLt (n m : nat) : Set := Id (Nat.ltb n m) true.

Lemma lw5n_natlt_lt : forall a b : nat, lw5n_NatLt a b -> (a < b)%nat.
Proof.
  intros a b H. apply (proj1 (Nat.ltb_lt a b)).
  apply (id_eq_SI bool (Nat.ltb a b) true H).
Defined.

Lemma lw5n_natlt_elim : forall a b : nat, lw5n_NatLt a b -> NatLe (Datatypes.S a) b.
Proof.
  intros a b H. apply NatLe_lift. apply lw5n_natlt_lt in H. lia.
Defined.

Lemma lw5n_natlt_intro : forall a b : nat, (a < b)%nat -> lw5n_NatLt a b.
Proof.
  intros a b H. apply lw5n_eq_id. apply (proj2 (Nat.ltb_lt a b)). exact H.
Defined.

(* ============================================================ *)
(* Section 1. the window family: the envelope column eps_n and   *)
(* the explicit endpoints                                        *)
(* ============================================================ *)

Definition lw5n_eps (n : nat) : Q := (1 # Pos.of_succ_nat n)%Q.

Definition lw5n_M (n : nat) : nat := 2 * pie_modulus (lw5n_eps n / 2) + 1.

Definition lw5n_lo (n : nat) : Q :=
  (4 * pie_partial (lw5n_M n + 1) - lw5n_eps n / 4)%Q.

Definition lw5n_hi (n : nat) : Q :=
  (4 * pie_partial (lw5n_M n) + lw5n_eps n / 4)%Q.

Lemma lw5n_eps_pos : forall n : nat, QltT' 0 (lw5n_eps n).
Proof.
  intros n. apply Qlt_to_QltT'. unfold Qlt, lw5n_eps. simpl. lia.
Defined.

Lemma lw5n_eps2_pos : forall n : nat, QltT' 0 (lw5n_eps n / 2)%Q.
Proof.
  intros n. apply Qlt_to_QltT'. unfold Qdiv.
  apply (Qmult_lt_0_compat (lw5n_eps n) (/ (2 # 1))).
  - apply lw5n_qltT'_qlt. apply lw5n_eps_pos.
  - apply Qinv_lt_0_compat. unfold Qlt. simpl. lia.
Defined.

Lemma lw5n_eps4_pos : forall n : nat, QltT' 0 (lw5n_eps n / 4)%Q.
Proof.
  intros n. apply Qlt_to_QltT'. unfold Qdiv.
  apply (Qmult_lt_0_compat (lw5n_eps n) (/ (4 # 1))).
  - apply lw5n_qltT'_qlt. apply lw5n_eps_pos.
  - apply Qinv_lt_0_compat. unfold Qlt. simpl. lia.
Defined.

Lemma lw5n_eps_antitone : forall n : nat, QleT' (lw5n_eps (Datatypes.S n)) (lw5n_eps n).
Proof.
  intros n. apply Qle_to_QleT'. unfold lw5n_eps, Qle. cbn [Qnum Qden].
  rewrite !Z.mul_1_l.
  replace (Pos.of_succ_nat (Datatypes.S n))
    with (Pos.succ (Pos.of_succ_nat n)) by reflexivity.
  rewrite Pos2Z.inj_succ.
  replace (Z.succ (Z.pos (Pos.of_succ_nat n)))
    with (Z.pos (Pos.of_succ_nat n) + 1)%Z by reflexivity.
  lia.
Defined.

(* integrality of 4/(eps_n/2): the doubled denominator of eps_n/2 makes  *)
(* the 4-fold quotient exactly 8n+8                                      *)
Lemma lw5n_four_div_half : forall n : nat,
  QeqT (4 / (lw5n_eps n / 2))%Q ((Z.of_nat (8 * n + 8) # 1)%Q).
Proof.
  intros n.
  apply qeq_imp_qeqT.
  assert (H1 : (lw5n_eps n / 2)%Q == (1 # (Pos.of_succ_nat n * 2))%Q).
  { unfold lw5n_eps, Qdiv, Qinv, Qmult. cbn [Qnum Qden]. reflexivity. }
  rewrite H1.
  unfold Qdiv, Qinv, Qmult, Qeq. cbn [Qnum Qden].
  rewrite !Z.mul_1_r.
  rewrite Pos2Z.inj_mul.
  pose proof (lw5n_leib_id_eq _ _ _ (leiblw_pos_succ n)) as Hps. rewrite Hps.
  replace (Z.of_nat (8 * n + 8)) with (8 * Z.of_nat (Datatypes.S n))%Z.
  - ring.
  - replace (8 * n + 8)%nat with (8 * Datatypes.S n)%nat by lia.
    symmetry. apply Nat2Z.inj_mul.
Defined.

(* explicit modulus assignment: pie_modulus(eps_n/2) = 8n+9              *)
(* (4/(eps_n/2) is exactly integral, truncated by Qceiling)              *)
Lemma lw5n_modulus_val : forall n : nat,
  Id (pie_modulus (lw5n_eps n / 2)) (Datatypes.S (8 * n + 8)%nat).
Proof.
  intros n.
  assert (Hx := lw5n_four_div_half n).
  assert (Hz' : Qceiling ((Z.of_nat (8 * n + 8) # 1)%Q) = Z.of_nat (8 * n + 8)).
  { pose proof (Qle_ceiling (Z.of_nat (8 * n + 8) # 1)%Q) as Hub.
    pose proof (Qceiling_lt (Z.of_nat (8 * n + 8) # 1)%Q) as Hlt.
    cbn [inject_Z] in Hub, Hlt.
    apply (leiblw_qmake_le _ _ _ _) in Hub.
    leiblw_id_inv_in Hub. apply (proj1 (Z.leb_le _ _)) in Hub.
    apply (leiblw_qmake_lt _ _ _ _) in Hlt.
    leiblw_id_inv_in Hlt. apply (proj1 (Z.ltb_lt _ _)) in Hlt.
    rewrite !Z.mul_1_r in Hub, Hlt.
    lia. }
  assert (Hz : Qceiling (4 / (lw5n_eps n / 2)) = Z.of_nat (8 * n + 8)).
  { assert (Hle1 : Qle (4 / (lw5n_eps n / 2)) (Z.of_nat (8 * n + 8) # 1)%Q)
      by (apply QleT'_to_Qle; apply qeq_le; exact Hx).
    assert (Hle2 : Qle (Z.of_nat (8 * n + 8) # 1)%Q (4 / (lw5n_eps n / 2)))
      by (apply QleT'_to_Qle; apply qeq_le; apply lw5n_qeqT_sym; exact Hx).
    pose proof (Qceiling_resp_le _ _ Hle1) as K1.
    pose proof (Qceiling_resp_le _ _ Hle2) as K2.
    rewrite Hz' in K1, K2. lia. }
  apply lw5n_eq_id. unfold pie_modulus. rewrite Hz. f_equal.
  apply Nat2Z.inj.
  apply Z2Nat.id. apply Nat2Z.is_nonneg.
Defined.

Lemma lw5n_M_val : forall n : nat, Id (lw5n_M n) (16 * n + 19)%nat.
Proof.
  intros n. apply lw5n_eq_id. unfold lw5n_M.
  rewrite (id_eq_SI nat _ _ (lw5n_modulus_val n)). lia.
Defined.

(* closed form of the adjacent-endpoint distance:                        *)
(* 4*S_M - 4*S_{M+1} = 4*pie_mag(M) for odd M                            *)
Lemma lw5n_gap4 : forall n : nat,
  QeqT (4 * pie_partial (lw5n_M n) - 4 * pie_partial (lw5n_M n + 1))%Q
       (4 * pie_mag (lw5n_M n))%Q.
Proof.
  intros n.
  apply qeq_imp_qeqT.
  assert (Hi : (lw5n_M n + 1)%nat = Datatypes.S (lw5n_M n)) by lia.
  rewrite Hi.
  setoid_replace (4 * pie_partial (lw5n_M n) - 4 * pie_partial (Datatypes.S (lw5n_M n)))
    with (- (4 * (pie_partial (Datatypes.S (lw5n_M n)) - pie_partial (lw5n_M n)))) by field.
  rewrite (qeqT_imp_qeq _ _ (pie_gap1 (lw5n_M n))).
  assert (Hs : pie_term (lw5n_M n) == (- pie_mag (lw5n_M n))%Q).
  { unfold lw5n_M, pie_term, pie_mag, Qdiv.
    rewrite (qeqT_imp_qeq _ _ (atan_sign_odd (pie_modulus (lw5n_eps n / 2)))). ring. }
  rewrite Hs. ring.
Defined.

(* window property 1: pi_L lies strictly inside every window             *)
(* (endpoints re-derived, after pi_rational_envelope)                    *)
Lemma lw5n_win_pi : forall n : nat,
  And (real_lt (real_const (lw5n_lo n)) cauchy_real_pi_leibniz)
      (real_lt cauchy_real_pi_leibniz (real_const (lw5n_hi n))).
Proof.
  intros n.
  split.
  - apply (pie_real_lower_gen (pie_modulus (lw5n_eps n / 2))
             (lw5n_eps n / 4) (lw5n_lo n)).
    + apply lw5n_qltT'_qlt. apply lw5n_eps4_pos.
    + unfold lw5n_lo.
      replace (lw5n_M n + 1)%nat with (2 * pie_modulus (lw5n_eps n / 2) + 2)%nat
        by (unfold lw5n_M; rewrite (id_eq_SI nat _ _ (lw5n_modulus_val n)); lia).
      apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
  - apply (pie_real_upper_gen (pie_modulus (lw5n_eps n / 2))
             (lw5n_eps n / 4) (lw5n_hi n)).
    + apply lw5n_qltT'_qlt. apply lw5n_eps4_pos.
    + unfold lw5n_hi. apply Qle_refl.
Defined.

(* window property 2: the window width is below eps_n                    *)
Lemma lw5n_win_width : forall n : nat, QltT' (lw5n_hi n - lw5n_lo n) (lw5n_eps n).
Proof.
  intros n.
  pose proof (lw5n_qltT'_qlt _ _ (lw5n_eps2_pos n)) as Hc2.
  assert (Hb : Qlt (4 * pie_mag (lw5n_M n)) (lw5n_eps n / 2)%Q).
  { apply (Qle_lt_trans _ (4 * pie_mag (pie_modulus (lw5n_eps n / 2))) _).
    - apply QleT'_to_Qle. apply pie_mult4_le. apply QleT'_to_Qle.
      apply pie_mag_antitone. unfold lw5n_M. lia.
    - apply QltT_to_Qlt. apply (pie_modulus_bound (lw5n_eps n / 2) Hc2). }
  apply Qlt_to_QltT'.
  unfold lw5n_hi, lw5n_lo.
  setoid_replace ((4 * pie_partial (lw5n_M n) + lw5n_eps n / 4)
                  - (4 * pie_partial (lw5n_M n + 1) - lw5n_eps n / 4))
    with ((4 * pie_partial (lw5n_M n) - 4 * pie_partial (lw5n_M n + 1))
          + (lw5n_eps n / 4 + lw5n_eps n / 4)) by field.
  rewrite (qeqT_imp_qeq _ _ (lw5n_gap4 n)), (qeqT_imp_qeq _ _ (pie_q_add_halves (lw5n_eps n))).
  apply (proj2 (Qlt_minus_iff (4 * pie_mag (lw5n_M n) + lw5n_eps n / 2) (lw5n_eps n))).
  setoid_replace (lw5n_eps n - (4 * pie_mag (lw5n_M n) + lw5n_eps n / 2))
    with (lw5n_eps n / 2 - 4 * pie_mag (lw5n_M n)) by field.
  exact (proj1 (Qlt_minus_iff (4 * pie_mag (lw5n_M n)) (lw5n_eps n / 2)) Hb).
Defined.

(* window property 3: the window width is positive                       *)
Lemma lw5n_width_pos : forall n : nat, QltT' 0 (lw5n_hi n - lw5n_lo n).
Proof.
  intros n.
  pose proof (lw5n_qltT'_qlt _ _ (lw5n_eps2_pos n)) as Hc2.
  pose proof (pie_mag_pos (lw5n_M n)) as Hm.
  assert (Ha : Qlt 0 (4 * pie_mag (lw5n_M n))).
  { apply (Qmult_lt_0_compat 4 (pie_mag (lw5n_M n))).
    - unfold Qlt. simpl. lia.
    - apply QltT_to_Qlt. exact Hm. }
  apply Qlt_to_QltT'.
  unfold lw5n_hi, lw5n_lo.
  setoid_replace ((4 * pie_partial (lw5n_M n) + lw5n_eps n / 4)
                  - (4 * pie_partial (lw5n_M n + 1) - lw5n_eps n / 4))
    with ((4 * pie_partial (lw5n_M n) - 4 * pie_partial (lw5n_M n + 1))
          + (lw5n_eps n / 4 + lw5n_eps n / 4)) by field.
  rewrite (qeqT_imp_qeq _ _ (lw5n_gap4 n)), (qeqT_imp_qeq _ _ (pie_q_add_halves (lw5n_eps n))).
  apply (Qlt_trans 0 (4 * pie_mag (lw5n_M n)) _).
  - exact Ha.
  - pose proof (pie_qplus_lt_r (4 * pie_mag (lw5n_M n)) 0 (lw5n_eps n / 2) Hc2) as H1.
    apply QltT_to_Qlt in H1.
    setoid_replace (4 * pie_mag (lw5n_M n) + 0) with (4 * pie_mag (lw5n_M n)) in H1 by field.
    exact H1.
Defined.

(* window property 4: the window column is nested -- when n <= n', the   *)
(* inner window is contained in the outer window                         *)
Lemma lw5n_win_nested : forall n n' : nat, NatLe n n' ->
  And (QleT' (lw5n_lo n) (lw5n_lo n')) (QleT' (lw5n_hi n') (lw5n_hi n)).
Proof.
  intros n n' Hnn'.
  apply NatLe_drop in Hnn'.
  assert (Hpm : (pie_modulus (lw5n_eps n / 2) <= pie_modulus (lw5n_eps n' / 2))%nat)
    by (rewrite !(id_eq_SI nat _ _ (lw5n_modulus_val _)); lia).
  assert (Hev : QleT' (4 * pie_partial (lw5n_M n + 1))
                      (4 * pie_partial (lw5n_M n' + 1))).
  { replace (lw5n_M n + 1)%nat
      with (2 * (pie_modulus (lw5n_eps n / 2) + 1))%nat
      by (unfold lw5n_M; rewrite (id_eq_SI nat _ _ (lw5n_modulus_val n)); lia).
    replace (lw5n_M n' + 1)%nat
      with (2 * (pie_modulus (lw5n_eps n / 2) + 1
                 + (pie_modulus (lw5n_eps n' / 2) - pie_modulus (lw5n_eps n / 2))))%nat
      by (unfold lw5n_M; rewrite !(id_eq_SI nat _ _ (lw5n_modulus_val _)); lia).
    apply pie_mult4_le. apply QleT'_to_Qle.
    apply (pie_even_mono (pie_modulus (lw5n_eps n' / 2) - pie_modulus (lw5n_eps n / 2))
                         (pie_modulus (lw5n_eps n / 2) + 1)). }
  assert (Hod : QleT' (4 * pie_partial (lw5n_M n')) (4 * pie_partial (lw5n_M n))).
  { replace (lw5n_M n')%nat
      with (2 * (pie_modulus (lw5n_eps n / 2)
                 + (pie_modulus (lw5n_eps n' / 2) - pie_modulus (lw5n_eps n / 2))) + 1)%nat
      by (unfold lw5n_M; rewrite !(id_eq_SI nat _ _ (lw5n_modulus_val _)); lia).
    replace (lw5n_M n)%nat with (2 * pie_modulus (lw5n_eps n / 2) + 1)%nat
      by (unfold lw5n_M; rewrite (id_eq_SI nat _ _ (lw5n_modulus_val n)); lia).
    apply pie_mult4_le. apply QleT'_to_Qle.
    apply (pie_odd_mono (pie_modulus (lw5n_eps n' / 2) - pie_modulus (lw5n_eps n / 2))
                        (pie_modulus (lw5n_eps n / 2))). }
  assert (Hq4 : Qle (lw5n_eps n' / 4) (lw5n_eps n / 4)).
  { apply (Qmult_le_compat_r (lw5n_eps n') (lw5n_eps n) (/ (4 # 1))).
    - assert (Hgen : forall k : nat, Qle (lw5n_eps (n + k)%nat) (lw5n_eps n)).
      { intros k. induction k as [|k IHk].
        - rewrite Nat.add_0_r. apply Qle_refl.
        - replace (n + Datatypes.S k)%nat with (Datatypes.S (n + k)) by lia.
          exact (Qle_trans (lw5n_eps (Datatypes.S (n + k)))
                           (lw5n_eps (n + k)) (lw5n_eps n)
                           (QleT'_to_Qle _ _ (lw5n_eps_antitone (n + k))) IHk). }
      replace n' with (n + (n' - n))%nat by lia.
      apply Hgen.
    - apply (Qlt_le_weak 0 (/ (4 # 1))). apply Qinv_lt_0_compat.
      unfold Qlt. simpl. lia. }
  split.
  - apply Qle_to_QleT'.
    unfold lw5n_lo.
    setoid_replace (4 * pie_partial (lw5n_M n + 1) - lw5n_eps n / 4)
      with (4 * pie_partial (lw5n_M n + 1) + (- (lw5n_eps n / 4))) by field.
    setoid_replace (4 * pie_partial (lw5n_M n' + 1) - lw5n_eps n' / 4)
      with (4 * pie_partial (lw5n_M n' + 1) + (- (lw5n_eps n' / 4))) by field.
    apply (Qplus_le_compat (4 * pie_partial (lw5n_M n + 1))
                           (4 * pie_partial (lw5n_M n' + 1))
                           (- (lw5n_eps n / 4)) (- (lw5n_eps n' / 4))).
    + exact (QleT'_to_Qle _ _ Hev).
    + destruct (lw5n_eps n) as [e1 e2]; destruct (lw5n_eps n') as [f1 f2].
      unfold Qle in Hq4 |- *. cbn [Qnum Qden] in Hq4 |- *.
      unfold Qopp. cbn [Qnum Qden]. lia.
  - apply Qle_to_QleT'.
    unfold lw5n_hi.
    apply (Qle_trans _ (4 * pie_partial (lw5n_M n') + lw5n_eps n / 4) _).
    + apply (Qplus_le_compat (4 * pie_partial (lw5n_M n'))
                             (4 * pie_partial (lw5n_M n'))
                             (lw5n_eps n' / 4) (lw5n_eps n / 4)).
      * apply Qle_refl.
      * exact Hq4.
    + apply (Qplus_le_compat (4 * pie_partial (lw5n_M n'))
                             (4 * pie_partial (lw5n_M n))
                             (lw5n_eps n / 4) (lw5n_eps n / 4)).
      * exact (QleT'_to_Qle _ _ Hod).
      * apply Qle_refl.
Defined.

(* ============================================================ *)
(* Section 2. the boolean in-window / out-of-window deciders      *)
(* (leiblw_Qleb on both sides)                                    *)
(* ============================================================ *)

Definition lw5n_inwin (q : Q) (n : nat) : bool :=
  andb (leiblw_Qleb (lw5n_lo n) q) (leiblw_Qleb q (lw5n_hi n)).

Definition lw5n_sep_dec (q : Q) (n : nat) : bool := negb (lw5n_inwin q n).

Lemma lw5n_Qleb_false_lt : forall x y : Q, leiblw_Qleb x y = false -> QltT' y x.
Proof.
  intros x y H. unfold leiblw_Qleb in H.
  destruct (Qcompare x y) eqn:E.
  - try rewrite E in H. cbn in H. discriminate H.
  - try rewrite E in H. cbn in H. discriminate H.
  - apply Qlt_to_QltT. apply (proj2 (Qgt_alt x y)). exact E.
Defined.

(* in-window implies close-point (correctness content of the window test *)
(* derived from the envelope residual bound, Q projection form): when q   *)
(* falls inside window n, the envelope projection column lw0m_xL enters   *)
(* pointwise into the eps_n neighborhood of q from the envelope order of  *)
(* M_n on                                                                 *)
Lemma lw5n_inwin_close_pt : forall (q : Q) (n : nat) (d : Q), QltT' 0 d ->
  leiblw_Id (lw5n_inwin q n) true ->
  sigT (fun N : nat => forall k : nat, NatLe N k ->
    QltT' (Qabs (lw0m_xL k - q)) (lw5n_eps n)).
Proof.
  intros q n d Hd Hin.
  leiblw_id_inv_in Hin. unfold lw5n_inwin in Hin.
  apply andb_true_iff in Hin. destruct Hin as [Hl Hh].
  apply lw5n_qleb_inv_eq in Hl. apply lw5n_qleb_inv_eq in Hh.
  pose proof (lw5n_win_width n) as Hw. apply lw5n_qltT'_qlt in Hw.
  pose proof (lw5n_eps4_pos n) as Hc4.
  assert (HhiS : (4 * pie_partial (2 * pie_modulus (lw5n_eps n / 2) + 1)
                  == lw5n_hi n - lw5n_eps n / 4)%Q)
    by (unfold lw5n_hi, lw5n_M; ring).
  assert (HloS : (4 * pie_partial (2 * pie_modulus (lw5n_eps n / 2) + 2)
                  == lw5n_lo n + lw5n_eps n / 4)%Q).
  { unfold lw5n_lo, lw5n_M.
    replace (2 * pie_modulus (lw5n_eps n / 2) + 1 + 1)%nat
      with (2 * pie_modulus (lw5n_eps n / 2) + 2)%nat by lia.
    ring. }
  exists (pie_modulus (lw5n_eps n / 2)). intros k Hk.
  apply NatLe_drop in Hk.
  apply Qlt_to_QltT'.
  assert (Hev1 : QleT' (4 * pie_partial (2 * pie_modulus (lw5n_eps n / 2) + 2))
                       (4 * pie_partial (2 * k + 2))).
  { replace (2 * pie_modulus (lw5n_eps n / 2) + 2)%nat
      with (2 * (pie_modulus (lw5n_eps n / 2) + 1))%nat by lia.
    replace (2 * k + 2)%nat
      with (2 * (pie_modulus (lw5n_eps n / 2) + 1
                 + (k - pie_modulus (lw5n_eps n / 2))))%nat by lia.
    apply pie_mult4_le. apply QleT'_to_Qle.
    apply (pie_even_mono (k - pie_modulus (lw5n_eps n / 2))
                         (pie_modulus (lw5n_eps n / 2) + 1)). }
  assert (Hev2 : QleT' (4 * pie_partial (2 * k + 2))
                       (4 * pie_partial (2 * pie_modulus (lw5n_eps n / 2) + 1))).
  { replace (2 * k + 2)%nat with (2 * (k + 1))%nat by lia.
    apply pie_mult4_le. apply QleT'_to_Qle.
    apply (pie_even_le_odd (k + 1) (pie_modulus (lw5n_eps n / 2))). }
  assert (Hub : Qle (lw0m_xL k - q)
                    (lw5n_eps n - lw5n_eps n / 4)).
  { apply (Qle_trans _ (4 * pie_partial (2 * pie_modulus (lw5n_eps n / 2) + 1) - q) _).
    - exact (proj2 (Qplus_le_l _ _ _)
               (Qle_trans (lw0m_xL k) ((4 * pie_partial (2 * k + 2))%Q)
                          (4 * pie_partial (2 * pie_modulus (lw5n_eps n / 2) + 1))
                          (QleT'_to_Qle _ _ (qeq_le _ _ (pie_v_eq k)))
                          (QleT'_to_Qle _ _ Hev2))).
    - setoid_replace (4 * pie_partial (2 * pie_modulus (lw5n_eps n / 2) + 1))
        with (lw5n_hi n - lw5n_eps n / 4) by exact HhiS.
      apply (Qle_trans _ ((lw5n_hi n - lw5n_eps n / 4) - lw5n_lo n) _).
      + apply (proj2 (Qplus_le_r _ _ _)).
        exact (Qopp_le_compat (lw5n_lo n) q Hl).
      + setoid_replace ((lw5n_hi n - lw5n_eps n / 4) - lw5n_lo n)
          with ((lw5n_hi n - lw5n_lo n) - lw5n_eps n / 4) by field.
        apply Qlt_le_weak.
        apply (proj2 (Qlt_minus_iff _ _)).
        setoid_replace ((lw5n_eps n - lw5n_eps n / 4)
                        - ((lw5n_hi n - lw5n_lo n) - lw5n_eps n / 4))
          with (lw5n_eps n - (lw5n_hi n - lw5n_lo n)) by field.
        exact (proj1 (Qlt_minus_iff (lw5n_hi n - lw5n_lo n) (lw5n_eps n)) Hw). }
  assert (Hlb : Qle (q - lw0m_xL k)
                    (lw5n_eps n - lw5n_eps n / 4)).
  { apply (Qle_trans _ (q - 4 * pie_partial (2 * pie_modulus (lw5n_eps n / 2) + 2)) _).
    - exact (proj2 (Qplus_le_r _ _ _)
               (Qopp_le_compat ((4 * pie_partial (2 * pie_modulus (lw5n_eps n / 2) + 2))%Q)
                               (lw0m_xL k)
                               (Qle_trans (4 * pie_partial (2 * pie_modulus (lw5n_eps n / 2) + 2))
                                          ((4 * pie_partial (2 * k + 2))%Q) (lw0m_xL k)
                                          (QleT'_to_Qle _ _ Hev1)
                                          (QleT'_to_Qle _ _
                                            (qeq_le _ _ (lw5n_qeqT_sym _ _ (pie_v_eq k))))))).
    - setoid_replace (4 * pie_partial (2 * pie_modulus (lw5n_eps n / 2) + 2))
        with (lw5n_lo n + lw5n_eps n / 4) by exact HloS.
      apply (Qle_trans _ ((lw5n_hi n - lw5n_lo n) - lw5n_eps n / 4) _).
      + setoid_replace (q - (lw5n_lo n + lw5n_eps n / 4))
          with ((q - lw5n_lo n) - lw5n_eps n / 4) by field.
        apply (proj2 (Qle_minus_iff _ _)).
        setoid_replace (((lw5n_hi n - lw5n_lo n) - lw5n_eps n / 4)
                        - ((q - lw5n_lo n) - lw5n_eps n / 4))
          with (lw5n_hi n - q) by field.
        exact (proj1 (Qle_minus_iff q (lw5n_hi n)) Hh).
      + apply Qlt_le_weak.
        apply (proj2 (Qlt_minus_iff _ _)).
        setoid_replace ((lw5n_eps n - lw5n_eps n / 4)
                        - ((lw5n_hi n - lw5n_lo n) - lw5n_eps n / 4))
          with (lw5n_eps n - (lw5n_hi n - lw5n_lo n)) by field.
        exact (proj1 (Qlt_minus_iff (lw5n_hi n - lw5n_lo n) (lw5n_eps n)) Hw). }
  apply (Qle_lt_trans _ (lw5n_eps n - lw5n_eps n / 4) (lw5n_eps n)).
  - apply QleT'_to_Qle. apply leiblw_qabs_bound.
    + exact Hub.
    + setoid_replace (- (lw0m_xL k - q))
        with (q - lw0m_xL k) by field.
      exact Hlb.
  - apply (proj2 (Qlt_minus_iff (lw5n_eps n - lw5n_eps n / 4) (lw5n_eps n))).
    setoid_replace (lw5n_eps n - (lw5n_eps n - lw5n_eps n / 4))
      with (lw5n_eps n / 4) by field.
    apply lw5n_qltT'_qlt. exact Hc4.
Defined.

(* ============================================================ *)
(* Section 3. the bounded linear search and the minimal           *)
(* separating window order                                        *)
(*   lw5n_find tests lw5n_sep_dec at successive orders from n and *)
(*   returns n when the fuel runs out (returning the budget       *)
(*   endpoint); the budget lw5n_bnd takes the envelope order at   *)
(*   eps := 1/(denominator q + 1).  Budget sufficiency (a         *)
(*   separating witness falls inside the budget) is not claimed   *)
(*   here; the theorems below hold for an arbitrary budget.       *)
(* ============================================================ *)

Fixpoint lw5n_find (q : Q) (n fuel : nat) : nat :=
  match fuel with
  | 0%nat => n
  | Datatypes.S f =>
      if lw5n_sep_dec q n then n else lw5n_find q (Datatypes.S n) f
  end.

(* the budget denominator takes the successor of Qden q *)
Definition lw5n_dlt (q : Q) : Q :=
  ((1 # 1) / (Z.pos (Pos.succ (Qden q)) # 1))%Q.

Definition lw5n_bnd (q : Q) : nat := Datatypes.S (pie_modulus (lw5n_dlt q)).

(* unfolding equation: one step of the search (structural conversion     *)
(* face; consumers rewrite through the equality read-out)                *)
Lemma lw5n_find_S : forall (q : Q) (n f : nat),
  Id (lw5n_find q n (Datatypes.S f))
     ((if lw5n_sep_dec q n then n else lw5n_find q (Datatypes.S n) f)%nat).
Proof. intros q n f. apply id_refl. Defined.

Definition lw5n_nsep (q : Q) : nat := lw5n_find q 0 (lw5n_bnd q).

(* search upper bound: find never exceeds n + fuel *)
Lemma lw5n_find_ub : forall (q : Q) (fuel n : nat),
  NatLe (lw5n_find q n fuel) (n + fuel)%nat.
Proof.
  intros q fuel. induction fuel as [|f IH]; intros n.
  - simpl. apply NatLe_lift. lia.
  - rewrite (id_eq_SI nat _ _ (lw5n_find_S q n f)).
    destruct (lw5n_sep_dec q n).
    + apply NatLe_lift. lia.
    + specialize (IH (Datatypes.S n)). apply NatLe_drop in IH.
      apply NatLe_lift. lia.
Defined.

(* hit: when some order n0 of [n, n+fuel] separates, find stops at a     *)
(* separating order and does not step past n0                            *)
Lemma lw5n_find_hit : forall (q : Q) (fuel n n0 : nat),
  NatLe n n0 -> NatLe n0 (n + fuel)%nat ->
  leiblw_Id (lw5n_sep_dec q n0) true ->
  And (leiblw_Id (lw5n_sep_dec q (lw5n_find q n fuel)) true)
      (leiblw_Id (Nat.leb (lw5n_find q n fuel) n0) true).
Proof.
  intros q fuel. induction fuel as [|f IH]; intros n n0 Hn1 Hn2 Hhit.
  - apply NatLe_drop in Hn1. apply NatLe_drop in Hn2.
    assert (Heq : n = n0) by lia. subst n0. simpl.
    split; [exact Hhit|].
    apply leiblw_id_eq. apply Nat.leb_le. lia.
  - rewrite (id_eq_SI nat _ _ (lw5n_find_S q n f)).
    destruct (lw5n_sep_dec q n) eqn:E.
    + split.
      * rewrite E. apply leiblw_id_intro.
      * apply leiblw_id_eq. apply Nat.leb_le. apply NatLe_drop in Hn1. lia.
    + apply IH.
      * destruct (Nat.eq_dec n n0) as [Heq|Hne].
        -- subst n0. leiblw_id_inv_in Hhit. rewrite E in Hhit.
           discriminate Hhit.
        -- apply NatLe_lift. apply NatLe_drop in Hn1. lia.
      * apply NatLe_lift. apply NatLe_drop in Hn2. lia.
      * exact Hhit.
Defined.

(* minimality: when find stops at a separating order, no order of        *)
(* [n, find) separates                                                   *)
Lemma lw5n_find_min : forall (q : Q) (fuel n m : nat),
  NatLe n m -> lw5n_NatLt m (lw5n_find q n fuel) ->
  leiblw_Id (lw5n_sep_dec q m) false.
Proof.
  intros q fuel. induction fuel as [|f IH]; intros n m Hn1 Hlt.
  - apply NatLe_drop in Hn1. apply lw5n_natlt_lt in Hlt. simpl in Hlt. lia.
  - destruct (lw5n_sep_dec q n) eqn:E.
    + apply NatLe_drop in Hn1. apply lw5n_natlt_lt in Hlt.
      rewrite (id_eq_SI nat _ _ (lw5n_find_S q n f)) in Hlt.
      rewrite E in Hlt. cbn in Hlt. lia.
    + rewrite (id_eq_SI nat _ _ (lw5n_find_S q n f)) in Hlt.
      rewrite E in Hlt. cbn in Hlt.
      destruct (Nat.eq_dec n m) as [Heq|Hne].
      * subst m. rewrite E. apply leiblw_id_intro.
      * apply (IH (Datatypes.S n) m).
        -- apply NatLe_lift. apply NatLe_drop in Hn1. lia.
        -- exact Hlt.
Defined.

(* run upper bound: nsep never exceeds the budget *)
Theorem lw5n_nsep_bound : forall q : Q,
  NatLe (lw5n_nsep q) (lw5n_bnd q).
Proof.
  intros q. unfold lw5n_nsep.
  pose proof (lw5n_find_ub q (lw5n_bnd q) 0) as H. apply NatLe_drop in H.
  apply NatLe_lift. lia.
Defined.

(* hit theorem: when a separating order exists inside the budget, nsep   *)
(* stops at a separating order *)
Theorem lw5n_nsep_hit : forall (q : Q) (n0 : nat),
  NatLe n0 (lw5n_bnd q) ->
  leiblw_Id (lw5n_sep_dec q n0) true ->
  leiblw_Id (lw5n_sep_dec q (lw5n_nsep q)) true.
Proof.
  intros q n0 Hb Hhit. unfold lw5n_nsep.
  destruct (lw5n_find_hit q (lw5n_bnd q) 0 n0 (NatLe_lift _ _ (Nat.le_0_l n0)) Hb Hhit)
    as [H _].
  exact H.
Defined.

(* no-passing theorem: nsep does not step past any separating order      *)
(* inside the budget *)
Theorem lw5n_nsep_least : forall (q : Q) (n0 : nat),
  NatLe n0 (lw5n_bnd q) ->
  leiblw_Id (lw5n_sep_dec q n0) true ->
  NatLe (lw5n_nsep q) n0.
Proof.
  intros q n0 Hb Hhit.
  apply NatLe_lift. apply (proj1 (Nat.leb_le (lw5n_nsep q) n0)).
  destruct (lw5n_find_hit q (lw5n_bnd q) 0 n0 (NatLe_lift _ _ (Nat.le_0_l n0)) Hb Hhit)
    as [_ H].
  exact (lw5n_leib_id_eq _ _ _ H).
Defined.

(* least-index characterization: the least separating order inside the   *)
(* budget is returned by nsep verbatim, as the Set-face judgment equality *)
Theorem lw5n_nsep_minimal : forall (q : Q) (n0 : nat),
  NatLe n0 (lw5n_bnd q) ->
  leiblw_Id (lw5n_sep_dec q n0) true ->
  (forall m : nat, lw5n_NatLt m n0 -> leiblw_Id (lw5n_sep_dec q m) false) ->
  leiblw_Id (lw5n_nsep q) n0.
Proof.
  intros q n0 Hb Hn Hmin.
  assert (Hhit := lw5n_nsep_hit q n0 Hb Hn).
  assert (Hle := lw5n_nsep_least q n0 Hb Hn).
  destruct (Nat.eq_dec (lw5n_nsep q) n0) as [E|E].
  - rewrite E. apply leiblw_id_intro.
  - exfalso.
    apply NatLe_drop in Hle.
    assert (Hlt : (lw5n_nsep q < n0)%nat) by lia.
    specialize (Hmin _ (lw5n_natlt_intro _ _ Hlt)).
    assert (Ht : lw5n_sep_dec q (lw5n_nsep q) = true)
      by exact (lw5n_leib_id_eq _ _ _ Hhit).
    rewrite Ht in Hmin. inversion Hmin.
Defined.

(* ============================================================ *)
(* Section 4. the growth-law faces (cell definitions and the      *)
(* three-tier notes; closed proofs are future work)               *)
(*   cell m: [4*S_{2m+2}, 4*S_{2m+1}], of width 4*pie_mag(2m+1),  *)
(*   the distance of the adjacent partial sums (the closed form   *)
(*   family of lw5n_gap4).                                        *)
(* ============================================================ *)

Definition lw5n_cell_hi (m : nat) : Q := (4 * pie_partial (2 * m + 1))%Q.

Definition lw5n_cell_lo (m : nat) : Q := (4 * pie_partial (2 * m + 2))%Q.

(* growth-law statement notes (proofs are future work):
   tier 1. obstacle bounds: when q falls into cell m
     (lw5n_cell_lo m <= q <= lw5n_cell_hi m, both on QleT') and the cell
     order is compatible with the window order, lw5n_sep_dec q n = false.
     Method: pie_even_mono (lo-side containment) + pie_tail4 (hi-side
     residual bound) + the Q arithmetic of eps_n; combined with Section 3
     this yields a lower bound: a separating order inside the budget
     forces n_sep q above the minimal order leaving the cell.
   tier 2. parameterized upper bound: put lw5n_B c := S (pie_modulus
     (c/2)); given 0 < c and a pointwise certificate of the distance from
     pi_L to q at least c (Q projection form: forall d > 0, exists N,
     forall k >= N, c < |lw0m_xL k - q|), some n0 <= lw5n_B c separates.
     Method: in-window implies close-point (lw5n_inwin_close_pt), the
     window must be left where the width drops below c;
     pie_modulus_bound guarantees that the window at order B c has width
     below c.
   tier 3. closed growth law: inserting the closed form c(q) of the
     separation order into tier 2 gives the explicit band
     n_sep q <= B(c(q)), composed with tier 1 into
     n_lo(cell(q)) <= n_sep q <= B(c(q)).  The upper bound is not
     optimal; neither exact optimality nor asymptotic tightness is
     claimed. *)

(* ============================================================ *)
(* Section 5. computational spot checks, extraction, and the      *)
(* assumption audit                                               *)
(* ============================================================ *)

From Stdlib Require Import Extraction.

Eval vm_compute in (lw5n_lo 0, lw5n_hi 0).
Eval vm_compute in (lw5n_lo 3, (lw5n_hi 3, lw5n_nsep (19 # 6)%Q)).

Separate Extraction lw5n_sep_dec lw5n_find lw5n_nsep lw5n_bnd lw5n_lo lw5n_hi.

Print Assumptions lw5n_win_pi.
Print Assumptions lw5n_win_width.
Print Assumptions lw5n_win_nested.
Print Assumptions lw5n_inwin_close_pt.
Print Assumptions lw5n_nsep_bound.
Print Assumptions lw5n_nsep_hit.
Print Assumptions lw5n_nsep_least.
Print Assumptions lw5n_nsep_minimal.

(* ============================================================ *)
(* Section 6. shape theorems (the family_separation junction):    *)
(* the order, width and transport faces of window separation      *)
(* ============================================================ *)

Require Import LW2SepTransport.
Require Import UpReqIrrationalCriterion.
From Stdlib Require Import Lqa.

(* the three transport calibers (contraction factors): k3 = 2 for the    *)
(* compatible specialization; k1 = 4 for the window-endpoint slack       *)
(* caliber; k2 = 8 for the budget-kernel composition caliber            *)
(* (c*Qinv(2*4) = c/8).                                                  *)
Definition lw5n_k3 : Q := 2%Q.
Definition lw5n_k1 : Q := 4%Q.
Definition lw5n_k2 : Q := 8%Q.

Lemma lw5n_QleT_k3 : QleT 2 lw5n_k3.
Proof. unfold lw5n_k3. exact (inr id_refl). Defined.

Lemma lw5n_QleT_k1 : QleT 2 lw5n_k1.
Proof. unfold lw5n_k1. left. apply Qlt_to_QltT. unfold Qlt. simpl. lia. Defined.

Lemma lw5n_QleT_k2 : QleT 2 lw5n_k2.
Proof. unfold lw5n_k2. left. apply Qlt_to_QltT. unfold Qlt. simpl. lia. Defined.

(* both directions of the leiblw_Qleb bridge: the true direction with    *)
(* its Set-face premise, and the contrapositive false direction          *)
Lemma lw5n_Qle_Qleb_true : forall x y : Q, QleT' x y -> leiblw_Qleb x y = true.
Proof.
  intros x y H. apply QleT'_to_Qle in H. unfold leiblw_Qleb.
  destruct (Qcompare_spec x y) as [Heq|Hlt|Hgt].
  - reflexivity.
  - reflexivity.
  - exfalso. unfold Qgt, Qle in *. cbn [Qnum Qden] in *. nia.
Defined.

Lemma lw5n_Qlt_Qleb_false : forall x y : Q, QltT' y x -> leiblw_Qleb x y = false.
Proof.
  intros x y H. apply lw5n_qltT'_qlt in H. unfold leiblw_Qleb.
  destruct (Qcompare_spec x y) as [Heq|Hlt|Hgt].
  - exfalso. rewrite Heq in H. unfold Qlt in H. cbn [Qnum Qden] in H. lia.
  - exfalso. unfold Qlt in H, Hlt. cbn [Qnum Qden] in H, Hlt. lia.
  - reflexivity.
Defined.

(* modulus antitone brick: a smaller radius never shrinks the order      *)
(* budget (first-hand at pie_modulus).  The premise c' > 0 guards the    *)
(* direction (counterexample c' = -5, c = 1: Qle c' c holds while the    *)
(* modulus claim fails); both consumers hold the positivity of c'        *)
(* themselves.  The Qinv antitone step is computed on numerator and      *)
(* denominator directly.                                                 *)
Lemma lw5n_modulus_antitone : forall c c' : Q, QltT' 0 c -> QltT' 0 c' -> QleT' c' c ->
  NatLe (pie_modulus c) (pie_modulus c').
Proof.
  intros c c' Hc Hc' Hle.
  apply lw5n_qltT'_qlt in Hc. apply lw5n_qltT'_qlt in Hc'.
  apply QleT'_to_Qle in Hle.
  assert (Hx1 : Qle (4 / c) (4 / c')).
  { destruct c as [cn cd]; destruct c' as [c'n c'd].
    unfold Qlt in Hc, Hc'. cbn [Qnum Qden] in Hc, Hc'.
    unfold Qle in Hle. cbn [Qnum Qden] in Hle.
    unfold Qdiv, Qinv, Qmult, Qle. cbn.
    destruct cn as [|p|p]; destruct c'n as [|p'|p']; cbn in *; lia. }
  assert (Hx2 : (Qceiling (4 / c) <= Qceiling (4 / c'))%Z)
    by (apply Qceiling_resp_le; exact Hx1).
  assert (Hcz : (0 <= Qceiling (4 / c))%Z).
  { assert (Hq0 : Qlt 0 (4 / c)).
    { unfold Qdiv. apply (Qmult_lt_0_compat 4 (Qinv c)).
      - unfold Qlt. simpl. lia.
      - apply Qinv_lt_0_compat. exact Hc. }
    assert (Hcq : Qle 0 (Qceiling (4 / c) # 1)).
    { apply (Qle_trans 0 (4 / c) (Qceiling (4 / c) # 1)).
      - apply (Qlt_le_weak 0 (4 / c)). exact Hq0.
      - apply Qle_ceiling. }
    unfold Qle in Hcq. simpl in Hcq. lia. }
  assert (Hc'z : (0 <= Qceiling (4 / c'))%Z).
  { assert (Hq0 : Qlt 0 (4 / c')).
    { unfold Qdiv. apply (Qmult_lt_0_compat 4 (Qinv c')).
      - unfold Qlt. simpl. lia.
      - apply Qinv_lt_0_compat. exact Hc'. }
    assert (Hcq : Qle 0 (Qceiling (4 / c') # 1)).
    { apply (Qle_trans 0 (4 / c') (Qceiling (4 / c') # 1)).
      - apply (Qlt_le_weak 0 (4 / c')). exact Hq0.
      - apply Qle_ceiling. }
    unfold Qle in Hcq. simpl in Hcq. lia. }
  assert (Hz : (Z.to_nat (Qceiling (4 / c)) <= Z.to_nat (Qceiling (4 / c')))%nat)
    by (apply (proj1 (Z2Nat.inj_le _ _ Hcz Hc'z) Hx2)).
  apply NatLe_lift. unfold pie_modulus. lia.
Defined.

(* Section 6.1 monotonicity: along the nested window column the          *)
(* separation boundary rises monotonically and the in-window side falls  *)
(* monotonically (And := prod verbatim)                                  *)
Theorem lw5n_shape_mono : forall (q : Q) (m n : nat), NatLe m n ->
  And (leiblw_Id (lw5n_sep_dec q m) true -> leiblw_Id (lw5n_sep_dec q n) true)
      (leiblw_Id (lw5n_inwin q n) true -> leiblw_Id (lw5n_inwin q m) true).
Proof.
  intros q m n Hmn.
  destruct (lw5n_win_nested m n Hmn) as [Hlo Hhi].
  split.
  - intros Hs. leiblw_id_inv_in Hs.
    unfold lw5n_sep_dec in Hs. apply negb_true_iff in Hs.
    unfold lw5n_inwin in Hs.
    destruct (leiblw_Qleb (lw5n_lo m) q) eqn:E1.
    + cbn [andb] in Hs. apply lw5n_Qleb_false_lt in Hs.
      apply leiblw_id_eq. unfold lw5n_sep_dec, lw5n_inwin.
      rewrite (lw5n_Qlt_Qleb_false q (lw5n_hi n)
                 (Qlt_to_QltT _ _
                   (Qle_lt_trans (lw5n_hi n) (lw5n_hi m) q
                      (QleT'_to_Qle _ _ Hhi) (lw5n_qltT'_qlt _ _ Hs)))).
      rewrite andb_false_r. cbn [negb]. reflexivity.
    + apply lw5n_Qleb_false_lt in E1.
      apply leiblw_id_eq. unfold lw5n_sep_dec, lw5n_inwin.
      rewrite (lw5n_Qlt_Qleb_false (lw5n_lo n) q
                 (Qlt_to_QltT _ _
                   (Qlt_le_trans q (lw5n_lo m) (lw5n_lo n)
                      (lw5n_qltT'_qlt _ _ E1) (QleT'_to_Qle _ _ Hlo)))).
      cbn [andb negb]. reflexivity.
  - intros Hi. leiblw_id_inv_in Hi. unfold lw5n_inwin in Hi.
    apply andb_true_iff in Hi. destruct Hi as [Hl Hh].
    apply lw5n_qleb_inv_eq in Hl. apply lw5n_qleb_inv_eq in Hh.
    apply leiblw_id_eq. unfold lw5n_inwin.
    rewrite (lw5n_Qle_Qleb_true (lw5n_lo m) q
               (Qle_to_QleT' _ _ (Qle_trans (lw5n_lo m) (lw5n_lo n) q
                  (QleT'_to_Qle _ _ Hlo) Hl))).
    rewrite (lw5n_Qle_Qleb_true q (lw5n_hi m)
               (Qle_to_QleT' _ _ (Qle_trans q (lw5n_hi n) (lw5n_hi m)
                  Hh (QleT'_to_Qle _ _ Hhi)))).
    reflexivity.
Defined.

(* Section 6.2 inversion band: the separation verdict and the n_sep      *)
(* order are in exact duality under the budget.  The unconditional form  *)
(* of the second component fails (fuel-exhaustion counterexample); the   *)
(* existence of a separating order n0 is carried as a theorem-grade      *)
(* premise (the honest boundary).                                        *)
Theorem lw5n_shape_inversion : forall (q : Q) (n n0 : nat),
  NatLe n0 (lw5n_bnd q) -> leiblw_Id (lw5n_sep_dec q n0) true ->
  And (NatLe n (lw5n_bnd q) ->
       (leiblw_Id (lw5n_sep_dec q n) true ->
        leiblw_Id (Nat.leb (lw5n_nsep q) n) true))
      (NatLe (lw5n_nsep q) n -> leiblw_Id (lw5n_sep_dec q n) true).
Proof.
  intros q n n0 Hb0 Hs0. split.
  - intros Hb Hs. apply leiblw_id_eq. apply Nat.leb_le.
    apply NatLe_drop. exact (lw5n_nsep_least q n Hb Hs).
  - intros Hle.
    destruct (lw5n_shape_mono q (lw5n_nsep q) n Hle) as [Hmono _].
    exact (Hmono (lw5n_nsep_hit q n0 Hb0 Hs0)).
Defined.

(* Section 6.3 the cell obstacle: m >= 8n+9 implies that cell m is       *)
(* contained in window n.  Constant chain: M n = 16n+19 (lw5n_M_val);    *)
(* 8n+9 <= m implies 2m+1 >= 16n+19 = M n (odd column pie_odd_mono) and  *)
(* 2m+2 >= 16n+20 = M n + 1 (even column pie_even_mono).  No tail4       *)
(* term: both sides are pure column monotonicity.                        *)
Theorem lw5n_cell_obstacle : forall (q : Q) (m n : nat),
  NatLe (8 * n + 9) m -> QleT' (lw5n_cell_lo m) q -> QleT' q (lw5n_cell_hi m) ->
  leiblw_Id (lw5n_sep_dec q n) false.
Proof.
  intros q m n Hge Hloq Hqhi.
  apply NatLe_drop in Hge.
  assert (Ha : Qle (lw5n_lo n) (lw5n_cell_lo m)).
  { unfold lw5n_lo, lw5n_cell_lo.
    assert (Hcore : Qle (4 * pie_partial (lw5n_M n + 1))
                        (4 * pie_partial (2 * m + 2))).
    { replace (lw5n_M n + 1)%nat with (2 * (8 * n + 10))%nat
        by (rewrite (id_eq_SI nat _ _ (lw5n_M_val n)); lia).
      (* even-column taming: the pie_even_mono d j shape needs
         2*(j+d) = 2m+2 with d := m-(8n+9); under 8n+9 <= m the
         arithmetic closes at (m-(8n+9))+(8n+9) = m, i.e.
         2*(8n+10)+d = 2m+2 *)
      assert (Hd : ((m - (8 * n + 9)) + (8 * n + 9))%nat = m) by lia.
      remember (m - (8 * n + 9))%nat as d eqn:Hde.
      replace (2 * m + 2)%nat with (2 * ((8 * n + 10) + d))%nat by lia.
      apply QleT'_to_Qle. apply pie_mult4_le. apply QleT'_to_Qle.
      apply (pie_even_mono d (8 * n + 10)). }
    pose proof (lw5n_eps4_pos n) as He4.
    apply lw5n_qltT'_qlt in He4. apply Qlt_le_weak in He4. lra. }
  assert (Hb : Qle (lw5n_cell_hi m) (lw5n_hi n)).
  { unfold lw5n_hi, lw5n_cell_hi.
    assert (Hcore : Qle (4 * pie_partial (2 * m + 1))
                        (4 * pie_partial (lw5n_M n))).
    { assert (Hd : ((m - (8 * n + 9)) + (8 * n + 9))%nat = m) by lia.
      remember (m - (8 * n + 9))%nat as d eqn:Hde.
      replace (2 * m + 1)%nat with (2 * ((8 * n + 9) + d) + 1)%nat by lia.
      replace (lw5n_M n)%nat with (2 * (8 * n + 9) + 1)%nat
        by (rewrite (id_eq_SI nat _ _ (lw5n_M_val n)); lia).
      apply QleT'_to_Qle. apply pie_mult4_le. apply QleT'_to_Qle.
      apply (pie_odd_mono d (8 * n + 9)). }
    pose proof (lw5n_eps4_pos n) as He4.
    apply lw5n_qltT'_qlt in He4. apply Qlt_le_weak in He4. lra. }
  assert (Hin : lw5n_inwin q n = true).
  { unfold lw5n_inwin.
    rewrite (lw5n_Qle_Qleb_true (lw5n_lo n) q
               (Qle_to_QleT' _ _
                 (Qle_trans (lw5n_lo n) (lw5n_cell_lo m) q Ha
                    (QleT'_to_Qle _ _ Hloq)))).
    rewrite (lw5n_Qle_Qleb_true q (lw5n_hi n)
               (Qle_to_QleT' _ _
                 (Qle_trans q (lw5n_cell_hi m) (lw5n_hi n)
                    (QleT'_to_Qle _ _ Hqhi) Hb))).
    reflexivity. }
  unfold lw5n_sep_dec. rewrite Hin. reflexivity.
Defined.

(* lower-bound law: when a separating order n0 exists inside the budget, *)
(* the cell order is pressed below 8*n0+9 (contrapositive of the cell    *)
(* obstacle + lia close)                                                 *)
Theorem lw5n_shape_lower : forall (q : Q) (m n0 : nat),
  NatLe n0 (lw5n_bnd q) -> leiblw_Id (lw5n_sep_dec q n0) true ->
  QleT' (lw5n_cell_lo m) q -> QleT' q (lw5n_cell_hi m) ->
  lw5n_NatLt m (8 * n0 + 9)%nat.
Proof.
  intros q m n0 Hb Hs Hlo Hhi.
  apply NatLe_drop in Hb.
  destruct (Nat.leb (8 * n0 + 9) m) eqn:E.
  - exfalso.
    apply Nat.leb_le in E.
    pose proof (lw5n_cell_obstacle q m n0 (NatLe_lift _ _ E) Hlo Hhi) as Hf.
    leiblw_id_inv_in Hs. rewrite Hs in Hf. inversion Hf.
  - apply Nat.leb_gt in E. apply lw5n_natlt_intro. lia.
Defined.

(* Section 6.3 the shape-theorem band (Set-faced; the composition of the *)
(* cell-obstacle contrapositive with nsep_least and nsep_hit)            *)
Theorem lw5n_shape_band : forall (q : Q) (m n0 : nat),
  QleT' (lw5n_cell_lo m) q -> QleT' q (lw5n_cell_hi m) ->
  NatLe n0 (lw5n_bnd q) -> leiblw_Id (lw5n_sep_dec q n0) true ->
  And (lw5n_NatLt m (8 * n0 + 9)%nat)
      (And (NatLe (lw5n_nsep q) n0)
           (leiblw_Id (lw5n_sep_dec q (lw5n_nsep q)) true)).
Proof.
  intros q m n0 Hlo Hhi Hb Hs. split.
  - exact (lw5n_shape_lower q m n0 Hb Hs Hlo Hhi).
  - split.
    + exact (lw5n_nsep_least q n0 Hb Hs).
    + exact (lw5n_nsep_hit q n0 Hb Hs).
Defined.

(* Section 6.4 the eps_n joint constant chain: the modulus values were   *)
(* frozen after vm_compute cross-checks (C1=(17,17) C2=(65,65)           *)
(* C3=(33,33) C4=(129,129)); 16n+17 / 32n+33 match the measurements.     *)
Lemma lw5n_four_div_quarter : forall n : nat,
  QeqT (4 / (lw5n_eps n / 4))%Q ((Z.of_nat (16 * n + 16) # 1)%Q).
Proof.
  intros n.
  apply qeq_imp_qeqT.
  assert (H1 : (lw5n_eps n / 4)%Q == (1 # (Pos.of_succ_nat n * 4))%Q).
  { unfold lw5n_eps, Qdiv, Qinv, Qmult. cbn [Qnum Qden]. reflexivity. }
  rewrite H1.
  unfold Qdiv, Qinv, Qmult, Qeq. cbn [Qnum Qden].
  rewrite !Z.mul_1_r.
  rewrite Pos2Z.inj_mul.
  pose proof (lw5n_leib_id_eq _ _ _ (leiblw_pos_succ n)) as Hps. rewrite Hps.
  replace (Z.pos 4) with 4%Z by reflexivity.
  replace (Z.of_nat (16 * n + 16)) with (16 * Z.of_nat (Datatypes.S n))%Z.
  - ring.
  - replace (16 * n + 16)%nat with (16 * Datatypes.S n)%nat by lia.
    symmetry. apply Nat2Z.inj_mul.
Defined.

(* explicit modulus chain, second opening: pie_modulus(eps_n/4) = 16n+17 *)
Lemma lw5n_modulus_div4_val : forall n : nat,
  Id (pie_modulus (lw5n_eps n / 4)) (16 * n + 17)%nat.
Proof.
  intros n.
  assert (Hx := lw5n_four_div_quarter n).
  assert (Hz' : Qceiling ((Z.of_nat (16 * n + 16) # 1)%Q) = Z.of_nat (16 * n + 16)).
  { pose proof (Qle_ceiling (Z.of_nat (16 * n + 16) # 1)%Q) as Hub.
    pose proof (Qceiling_lt (Z.of_nat (16 * n + 16) # 1)%Q) as Hlt.
    cbn [inject_Z] in Hub, Hlt.
    apply (leiblw_qmake_le _ _ _ _) in Hub.
    leiblw_id_inv_in Hub. apply (proj1 (Z.leb_le _ _)) in Hub.
    apply (leiblw_qmake_lt _ _ _ _) in Hlt.
    leiblw_id_inv_in Hlt. apply (proj1 (Z.ltb_lt _ _)) in Hlt.
    rewrite !Z.mul_1_r in Hub, Hlt.
    lia. }
  assert (Hz : Qceiling (4 / (lw5n_eps n / 4)) = Z.of_nat (16 * n + 16)).
  { assert (Hle1 : Qle (4 / (lw5n_eps n / 4)) (Z.of_nat (16 * n + 16) # 1)%Q)
      by (apply QleT'_to_Qle; apply qeq_le; exact Hx).
    assert (Hle2 : Qle (Z.of_nat (16 * n + 16) # 1)%Q (4 / (lw5n_eps n / 4)))
      by (apply QleT'_to_Qle; apply qeq_le; apply lw5n_qeqT_sym; exact Hx).
    pose proof (Qceiling_resp_le _ _ Hle1) as K1.
    pose proof (Qceiling_resp_le _ _ Hle2) as K2.
    rewrite Hz' in K1, K2. lia. }
  assert (Hs : pie_modulus (lw5n_eps n / 4) = Datatypes.S (16 * n + 16)%nat).
  { unfold pie_modulus. rewrite Hz. f_equal.
    apply Nat2Z.inj.
    apply Z2Nat.id. apply Nat2Z.is_nonneg. }
  apply lw5n_eq_id. rewrite Hs. lia.
Defined.

Lemma lw5n_four_div_eighth : forall n : nat,
  QeqT (4 / (lw5n_eps n / 8))%Q ((Z.of_nat (32 * n + 32) # 1)%Q).
Proof.
  intros n.
  apply qeq_imp_qeqT.
  assert (H1 : (lw5n_eps n / 8)%Q == (1 # (Pos.of_succ_nat n * 8))%Q).
  { unfold lw5n_eps, Qdiv, Qinv, Qmult. cbn [Qnum Qden]. reflexivity. }
  rewrite H1.
  unfold Qdiv, Qinv, Qmult, Qeq. cbn [Qnum Qden].
  rewrite !Z.mul_1_r.
  rewrite Pos2Z.inj_mul.
  pose proof (lw5n_leib_id_eq _ _ _ (leiblw_pos_succ n)) as Hps. rewrite Hps.
  replace (Z.pos 8) with 8%Z by reflexivity.
  replace (Z.of_nat (32 * n + 32)) with (32 * Z.of_nat (Datatypes.S n))%Z.
  - ring.
  - replace (32 * n + 32)%nat with (32 * Datatypes.S n)%nat by lia.
    symmetry. apply Nat2Z.inj_mul.
Defined.

(* explicit modulus chain, third opening: pie_modulus(eps_n/8) = 32n+33  *)
Lemma lw5n_modulus_div8_val : forall n : nat,
  Id (pie_modulus (lw5n_eps n / 8)) (32 * n + 33)%nat.
Proof.
  intros n.
  assert (Hx := lw5n_four_div_eighth n).
  assert (Hz' : Qceiling ((Z.of_nat (32 * n + 32) # 1)%Q) = Z.of_nat (32 * n + 32)).
  { pose proof (Qle_ceiling (Z.of_nat (32 * n + 32) # 1)%Q) as Hub.
    pose proof (Qceiling_lt (Z.of_nat (32 * n + 32) # 1)%Q) as Hlt.
    cbn [inject_Z] in Hub, Hlt.
    apply (leiblw_qmake_le _ _ _ _) in Hub.
    leiblw_id_inv_in Hub. apply (proj1 (Z.leb_le _ _)) in Hub.
    apply (leiblw_qmake_lt _ _ _ _) in Hlt.
    leiblw_id_inv_in Hlt. apply (proj1 (Z.ltb_lt _ _)) in Hlt.
    rewrite !Z.mul_1_r in Hub, Hlt.
    lia. }
  assert (Hz : Qceiling (4 / (lw5n_eps n / 8)) = Z.of_nat (32 * n + 32)).
  { assert (Hle1 : Qle (4 / (lw5n_eps n / 8)) (Z.of_nat (32 * n + 32) # 1)%Q)
      by (apply QleT'_to_Qle; apply qeq_le; exact Hx).
    assert (Hle2 : Qle (Z.of_nat (32 * n + 32) # 1)%Q (4 / (lw5n_eps n / 8)))
      by (apply QleT'_to_Qle; apply qeq_le; apply lw5n_qeqT_sym; exact Hx).
    pose proof (Qceiling_resp_le _ _ Hle1) as K1.
    pose proof (Qceiling_resp_le _ _ Hle2) as K2.
    rewrite Hz' in K1, K2. lia. }
  assert (Hs : pie_modulus (lw5n_eps n / 8) = Datatypes.S (32 * n + 32)%nat).
  { unfold pie_modulus. rewrite Hz. f_equal.
    apply Nat2Z.inj.
    apply Z2Nat.id. apply Nat2Z.is_nonneg. }
  apply lw5n_eq_id. rewrite Hs. lia.
Defined.

(* Section 6.5 the family_separation junction: the out-of-window         *)
(* separation certificate, the transport contraction, and the budget     *)
(* caliber                                                               *)

(* out-of-window = separation certificate (real-layer lift; the          *)
(* separation distance is carried by the slack of lw5n_win_pi with no    *)
(* halving).  The two disjunct cases are handled by a boolean eqn split   *)
(* (the or-introduction shape is not eliminable in the Set goal).        *)
Theorem lw5n_outwin_sepdist : forall (q : Q) (n : nat),
  leiblw_Id (lw5n_sep_dec q n) true ->
  sigT (fun c : Q => And (QltT 0 c)
    (real_lt (real_const c) (real_metric cauchy_real_pi_leibniz (real_const q)))).
Proof.
  intros q n Hs.
  leiblw_id_inv_in Hs. unfold lw5n_sep_dec in Hs.
  apply negb_true_iff in Hs. unfold lw5n_inwin in Hs.
  destruct (lw5n_win_pi n) as [Hlo_pi Hhi_pi].
  destruct (leiblw_Qleb (lw5n_lo n) q) eqn:E1.
  - cbn [andb] in Hs.
    apply lw5n_Qleb_false_lt in Hs. apply lw5n_qltT'_qlt in Hs.
    destruct Hhi_pi as [eps0 [He0 [N0 HN0]]].
    exists (q - lw5n_hi n)%Q. split.
    + apply Qlt_to_QltT. pose proof (QltT_to_Qlt 0 eps0 He0). lra.
    + exists eps0. split.
      * exact He0.
      * exists N0. intros k Hk.
        pose proof (HN0 k Hk) as Hpt. apply QltT_to_Qlt in Hpt.
        change (Qlt eps0 (lw5n_hi n - projT1 cauchy_real_pi_leibniz k)) in Hpt.
        apply Qlt_to_QltT.
        change (Qlt eps0
                  (Qabs (projT1 cauchy_real_pi_leibniz k - q)
                   - (q - lw5n_hi n))%Q).
        apply (Qabs_case (projT1 cauchy_real_pi_leibniz k - q)).
        { intro Hp. lra. }
        { intro Hp. lra. }
  - apply lw5n_Qleb_false_lt in E1. apply lw5n_qltT'_qlt in E1.
    destruct Hlo_pi as [eps0 [He0 [N0 HN0]]].
    exists (lw5n_lo n - q)%Q. split.
    + apply Qlt_to_QltT. pose proof (QltT_to_Qlt 0 eps0 He0). lra.
    + exists eps0. split.
      * exact He0.
      * exists N0. intros k Hk.
        pose proof (HN0 k Hk) as Hpt. apply QltT_to_Qlt in Hpt.
        change (Qlt eps0 (projT1 cauchy_real_pi_leibniz k - lw5n_lo n)) in Hpt.
        apply Qlt_to_QltT.
        change (Qlt eps0
                  (Qabs (projT1 cauchy_real_pi_leibniz k - q)
                   - (lw5n_lo n - q))%Q).
        apply (Qabs_case (projT1 cauchy_real_pi_leibniz k - q)).
        { intro Hp. lra. }
        { intro Hp. lra. }
Defined.

(* n_sep transport law (the junction main statement): a three-layer      *)
(* transform of the certificate, the radius and the budget; not a new    *)
(* function n_sep^Y (the Y-side window family is not instantiated)       *)
Theorem lw5n_nsep_transform : forall (Y : Real) (q : Q) (n : nat) (k : Q),
  real_eq cauchy_real_pi_leibniz Y -> QleT 2 k ->
  leiblw_Id (lw5n_sep_dec q n) true ->
  sigT (fun c : Q => And (QltT 0 c)
    (real_lt (real_const (c / k)%Q) (real_metric Y (real_const q)))).
Proof.
  intros Y q n k Hseq Hk Hs.
  destruct (lw5n_outwin_sepdist q n Hs) as [c [Hc Hsep]].
  exists c. split.
  - exact Hc.
  - exact (lw2t_sep_transport_k cauchy_real_pi_leibniz Y q c k Hc Hk Hseq Hsep).
Defined.

Theorem lw5n_nsep_transform_k3 : forall (Y : Real) (q : Q) (n : nat),
  real_eq cauchy_real_pi_leibniz Y ->
  leiblw_Id (lw5n_sep_dec q n) true ->
  sigT (fun c : Q => And (QltT 0 c)
    (real_lt (real_const (c / 2)%Q) (real_metric Y (real_const q)))).
Proof.
  intros Y q n Hseq Hs.
  exact (lw5n_nsep_transform Y q n lw5n_k3 Hseq lw5n_QleT_k3 Hs).
Defined.

Theorem lw5n_nsep_transform_k1 : forall (Y : Real) (q : Q) (n : nat),
  real_eq cauchy_real_pi_leibniz Y ->
  leiblw_Id (lw5n_sep_dec q n) true ->
  sigT (fun c : Q => And (QltT 0 c)
    (real_lt (real_const (c / 4)%Q) (real_metric Y (real_const q)))).
Proof.
  intros Y q n Hseq Hs.
  exact (lw5n_nsep_transform Y q n lw5n_k1 Hseq lw5n_QleT_k1 Hs).
Defined.

Theorem lw5n_nsep_transform_k2 : forall (Y : Real) (q : Q) (n : nat),
  real_eq cauchy_real_pi_leibniz Y ->
  leiblw_Id (lw5n_sep_dec q n) true ->
  sigT (fun c : Q => And (QltT 0 c)
    (real_lt (real_const (c / 8)%Q) (real_metric Y (real_const q)))).
Proof.
  intros Y q n Hseq Hs.
  exact (lw5n_nsep_transform Y q n lw5n_k2 Hseq lw5n_QleT_k2 Hs).
Defined.

(* caliber close-out: shrinking the radius k-fold never shrinks the      *)
(* order budget, by modulus antitonicity (reconciled with the explicit   *)
(* chain of Section 6.4)                                                 *)
Corollary lw5n_bnd_caliber : forall (c : Q) (k : Q), QltT' 0 c -> QleT 2 k ->
  NatLe (pie_modulus (c / 2)) (pie_modulus (c / k / 2)).
Proof.
  intros c k Hc Hk.
  assert (Hc2 : QltT' 0 (c / 2)%Q).
  { apply Qlt_to_QltT'. unfold Qdiv.
    apply (Qmult_lt_0_compat c (Qinv (2 # 1))).
    - exact (lw5n_qltT'_qlt 0 c Hc).
    - apply Qinv_lt_0_compat. unfold Qlt. simpl. lia. }
  assert (Hck : QltT' 0 (c / k / 2)%Q).
  { apply Qlt_to_QltT'. unfold Qdiv.
    apply (Qmult_lt_0_compat (c * Qinv k) (Qinv (2 # 1))).
    - apply (Qmult_lt_0_compat c (Qinv k)).
      + exact (lw5n_qltT'_qlt 0 c Hc).
      + apply Qinv_lt_0_compat.
        pose proof Hk as Hkc. destruct Hkc as [Hklt | Hkid].
        * apply QltT_to_Qlt in Hklt. lra.
        * destruct Hkid. unfold Qlt. simpl. lia.
    - apply Qinv_lt_0_compat. unfold Qlt. simpl. lia. }
  assert (Hle1 : Qle (c / k)%Q c).
  { unfold Qdiv.
    apply (Qle_trans _ (Qinv k * c)%Q).
    - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qmult_comm.
    - apply (Qle_trans _ (1 * c)%Q).
      + apply (Qmult_le_compat_r (Qinv k) 1 c).
        * pose proof (lw2t_k_inv2_le k Hk) as Hk2.
          apply QleT'_to_Qle in Hk2. lra.
        * pose proof (lw5n_qltT'_qlt 0 c Hc) as Hcp. apply Qlt_le_weak. exact Hcp.
      + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qmult_1_l. }
  assert (Hle2 : Qle (c / k / 2)%Q (c / 2)%Q).
  { unfold Qdiv.
    apply (Qmult_le_compat_r (c * Qinv k) c (Qinv (2 # 1))).
    - exact Hle1.
    - apply (Qlt_le_weak 0 (Qinv (2 # 1))). apply Qinv_lt_0_compat.
      unfold Qlt. simpl. lia. }
  apply lw5n_modulus_antitone.
  - exact Hc2.
  - exact Hck.
  - apply Qle_to_QleT'. exact Hle2.
Defined.

(* mid-file assumption audit (first of the two rounds; the anchor is the *)
(* set of statements closed so far, at the tail of Section 6.5) *)
Print Assumptions lw5n_QleT_k3.
Print Assumptions lw5n_QleT_k1.
Print Assumptions lw5n_QleT_k2.
Print Assumptions lw5n_modulus_antitone.
Print Assumptions lw5n_shape_mono.
Print Assumptions lw5n_shape_inversion.
Print Assumptions lw5n_cell_obstacle.
Print Assumptions lw5n_shape_lower.
Print Assumptions lw5n_shape_band.
Print Assumptions lw5n_modulus_div4_val.
Print Assumptions lw5n_modulus_div8_val.
Print Assumptions lw5n_outwin_sepdist.
Print Assumptions lw5n_nsep_transform.
Print Assumptions lw5n_nsep_transform_k3.
Print Assumptions lw5n_nsep_transform_k1.
Print Assumptions lw5n_nsep_transform_k2.
Print Assumptions lw5n_bnd_caliber.

(* ============================================================ *)
(* Section 7. computational spot checks, extraction, and the      *)
(* assumption audit (the second anchor; the Section 5 block is    *)
(* unchanged)                                                     *)
(* ============================================================ *)

Eval vm_compute in (lw5n_cell_lo 0, lw5n_cell_hi 0).
Eval vm_compute in (lw5n_sep_dec (22 # 7)%Q 5, lw5n_inwin (22 # 7)%Q 5).
Eval vm_compute in (pie_modulus (lw5n_eps 3 / 4)%Q, (16 * 3 + 17)%nat).

Separate Extraction lw5n_inwin lw5n_k3 lw5n_k1 lw5n_k2 lw5n_cell_hi lw5n_cell_lo.

Print Assumptions lw5n_win_pi.
Print Assumptions lw5n_win_width.
Print Assumptions lw5n_win_nested.
Print Assumptions lw5n_inwin_close_pt.
Print Assumptions lw5n_nsep_bound.
Print Assumptions lw5n_nsep_hit.
Print Assumptions lw5n_nsep_least.
Print Assumptions lw5n_nsep_minimal.
Print Assumptions lw5n_shape_mono.
Print Assumptions lw5n_shape_inversion.
Print Assumptions lw5n_cell_obstacle.
Print Assumptions lw5n_shape_lower.
Print Assumptions lw5n_shape_band.
Print Assumptions lw5n_modulus_div4_val.
Print Assumptions lw5n_modulus_div8_val.
Print Assumptions lw5n_modulus_antitone.
Print Assumptions lw5n_outwin_sepdist.
Print Assumptions lw5n_nsep_transform.
Print Assumptions lw5n_nsep_transform_k3.
Print Assumptions lw5n_nsep_transform_k1.
Print Assumptions lw5n_nsep_transform_k2.
Print Assumptions lw5n_bnd_caliber.
Print Assumptions lw5n_QleT_k3.
Print Assumptions lw5n_QleT_k1.
Print Assumptions lw5n_QleT_k2.
