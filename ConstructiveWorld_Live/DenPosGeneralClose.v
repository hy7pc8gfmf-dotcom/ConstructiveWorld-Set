(* ConstructiveWorld-Set -- DenPosGeneralClose: the collected denominator-positivity proposition family and its instantiation carriers. *)

(** * DenPosGeneralClose: the pdpa_ strict-positivity family and the dpc_ citation-forwarding pieces.

    Mission.  The proposition families [pdpa_c0_nz], [pdpa_c0_one],
      [pdpa_R0_two], [pdpa_c1_2_c0], [pdpa_R_ge_2], [pdpa_term_decay],
      [pdpa_g1_lt_g0], [pdpa_den0_one], [pdpa_den_pos_strict], closed by the
      dpc_ citation-forwarding pieces: [dpc_den_pos_close] forwards by
      exact, [dpc_den_pos_close_alt] is the independent in-library second
      route, [dpc_pds_den1_pos_sentinel] the instance-check sentinel.

    Dependencies.  The library pieces listed by the in-file Require face
      (S01_BaseRing .. S15_TailFEPUp, UpReqPadeExp, UpReqAltSumPos,
      UpReqPadeDenPos, DenPosGeneral; Stdlib QArith, Arith, Lia).

    References.  Pade approximant denominator positivity on 0 <= x < 2 via
      the alternating-sum strict-decrease scheme; this development,
      DenPosGeneralClose.v, the baseline ConstructiveWorld-Main module
      (statement names carried over verbatim; sixteen tactic sites adapted
      by the S02 face bridges QltT_to_Qlt / qeq_imp_qeqT / qeqT_imp_qeq,
      first-hand Locate/Check evidence).

    Constructivity.  All proofs closed by [Qed], zero admission lexemes, no
      classical logic; the statement face is carried at the Set layer, zero
      [Prop] leakage.

    Build.  Rocq 9.1 direct [coqc -native-compiler no -q -Q . ""] (cpu_guard
      load capping); the artifact starts with [436f7121 000160bc]. *)
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
Require Import UpReqPadeExp UpReqAltSumPos UpReqPadeDenPos.
Require Import DenPosGeneral.

(* ================= §1 the pdpa_c0_nz family ================= *)
From Stdlib Require Import QArith.QArith Arith.Arith Lia.

(* Part 0: the special coefficient values (c_0 == 1, the first-pair ratio
   R n 0 == 2, and c_1 * 2 == c_0) *)

(* c_0 <> 0 (a Qeq-form negative; supplied directly from the folded face:
   pdp_coeff_pos_any is unconditionally positive for every k) *)
Lemma pdpa_c0_nz : forall n : nat, ~ (pade_coeff n 0%nat == 0%Q).
Proof.
  intros n Heq. apply (Qlt_not_eq 0%Q (pade_coeff n 0%nat)).
  - apply QltT_to_Qlt. apply pdp_coeff_pos_any.
  - apply Qeq_sym. exact Heq.
Qed.

(* c_0 == 1: pade_coeff n 0 = (2n)!*n!/((2n)!*(0!*n!)) -- closed by the
   Qmult_comp termwise assembly plus Qmult_inv_r (q_fact 0 == 1 is resolved
   by the conversion, so no rewriting is needed) *)
Lemma pdpa_c0_one : forall n : nat, pade_coeff n 0%nat == 1%Q.
Proof.
  intro n. unfold pade_coeff, Qdiv.
  replace (2 * n - 0)%nat with (2 * n)%nat by lia.
  replace (n - 0)%nat with n%nat by lia.
  apply (Qeq_trans
    (q_fact (2 * n) * q_fact n *
     Qinv (q_fact (2 * n) * (q_fact 0 * q_fact n)))
    (q_fact (2 * n) * (q_fact 0 * q_fact n) *
     Qinv (q_fact (2 * n) * (q_fact 0 * q_fact n)))).
  - apply (Qmult_comp (q_fact (2 * n) * q_fact n)
             (q_fact (2 * n) * (q_fact 0 * q_fact n))).
    + apply (Qmult_comp (q_fact (2 * n)) (q_fact (2 * n))
               (Qeq_refl (q_fact (2 * n))) (q_fact n) (q_fact 0 * q_fact n)).
      * apply Qeq_sym.
        apply (Qeq_trans (q_fact 0 * q_fact n) (1%Q * q_fact n) (q_fact n)).
        -- apply (Qmult_comp (q_fact 0) 1%Q (Qeq_refl (q_fact 0))
                    (q_fact n) (q_fact n) (Qeq_refl (q_fact n))).
        -- apply Qmult_1_l.
    + apply Qeq_refl.
  - apply (Qmult_inv_r (q_fact (2 * n) * (q_fact 0 * q_fact n))).
    intro Heq. apply (Qlt_not_eq 0%Q (q_fact (2 * n) * (q_fact 0 * q_fact n))).
    + apply (Qmult_lt_0_compat (q_fact (2 * n)) (q_fact 0 * q_fact n)).
      * apply QltT_to_Qlt. apply q_fact_pos.
      * apply (Qmult_lt_0_compat (q_fact 0) (q_fact n)); apply QltT_to_Qlt;
        apply q_fact_pos.
    + apply Qeq_sym. exact Heq.
Qed.

(* The exact first-pair ratio: pdp_R n 0 == 2 ((2n)*(1/n) == 2 -- at the Z
   layer S(2n-1) == 2*S(n-1) is settled by lia, and the tail closes by
   Qmult_inv_r) *)
Lemma pdpa_R0_two : forall n : nat, (1 <= n)%nat -> pdp_R n 0%nat == 2%Q.
Proof.
  intros n Hn. unfold pdp_R.
  assert (EA : (Z.of_nat (Datatypes.S (2 * n - Datatypes.S 0)) # 1)%Q ==
               ((2 # 1)%Q * (Z.of_nat (Datatypes.S (n - Datatypes.S 0)) # 1))%Q).
  { unfold Qeq. cbn [Qnum Qden Qmult Pos.mul]. lia. }
  rewrite EA.
  replace (Z.of_nat (Datatypes.S 0) # 1)%Q with 1%Q by reflexivity.
  apply (Qeq_trans
    (((2 # 1)%Q * (Z.of_nat (Datatypes.S (n - Datatypes.S 0)) # 1))%Q * 1%Q *
     Qinv ((Z.of_nat (Datatypes.S (n - Datatypes.S 0)) # 1))%Q)
    (2%Q * ((Z.of_nat (Datatypes.S (n - Datatypes.S 0)) # 1)%Q *
            Qinv ((Z.of_nat (Datatypes.S (n - Datatypes.S 0)) # 1))%Q))).
  - ring.
  - apply (Qeq_trans
      (2%Q * ((Z.of_nat (Datatypes.S (n - Datatypes.S 0)) # 1)%Q *
              Qinv ((Z.of_nat (Datatypes.S (n - Datatypes.S 0)) # 1))%Q))
      (2%Q * 1%Q) 2%Q).
    + apply (Qmult_comp 2%Q 2%Q (Qeq_refl 2%Q)
               ((Z.of_nat (Datatypes.S (n - Datatypes.S 0)) # 1)%Q *
                Qinv ((Z.of_nat (Datatypes.S (n - Datatypes.S 0)) # 1))%Q)
               1%Q
               (Qmult_inv_r (Z.of_nat (Datatypes.S (n - Datatypes.S 0)) # 1)%Q
                            (fun Habs => Empty_set_ind (fun _ => False)
                                        (pdp_ZS1_nz (n - Datatypes.S 0)
                                        (qeq_imp_qeqT _ _ Habs))))).
    + ring.
Qed.

(* The algebraic core of the first-pair strictness: c_1 * 2 == c_0 (the
   Qeq redirection of pdp_coeff_ratio n 0 plus the pdpa_R0_two
   substitution, assembled termwise by Qmult_comp) *)
Lemma pdpa_c1_2_c0 : forall n : nat, (1 <= n)%nat ->
  pade_coeff n 1%nat * 2%Q == pade_coeff n 0%nat.
Proof.
  intros n Hn.
  apply (Qeq_trans (pade_coeff n 1%nat * 2%Q)
                   (pade_coeff n 1%nat * pdp_R n 0%nat)
                   (pade_coeff n 0%nat)).
  - apply (Qmult_comp (pade_coeff n 1%nat) (pade_coeff n 1%nat)
             (Qeq_refl (pade_coeff n 1%nat)) 2%Q (pdp_R n 0%nat)
             (Qeq_sym (pdp_R n 0%nat) 2%Q (pdpa_R0_two n Hn))).
  - apply Qeq_sym. apply qeqT_imp_qeq. apply pdp_coeff_ratio. lia.
Qed.

(* Part 1: the ratio lower bound refined from 1 up to 2, and the term decay
   over the whole range x <= 2 *)

(* The ratio lower bound refined: 0 <= k < n implies 2 <= pdp_R n k
   (refining the 1 lower bound of pdpa_R_ge_1 up to 2: 2(n-k) <= (2n-k)(k+1)
   iff k(2n+1-k) >= 0, which holds for all k >= 0 with k <= n-1; closed by
   nia) *)
Lemma pdpa_R_ge_2 : forall n k : nat, (k < n)%nat -> QleT' 2%Q (pdp_R n k).
Proof.
  intros n k Hk. unfold pdp_R.
  assert (Hdinv : QleT' 0
    (Qinv ((Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1)%Q))).
  { apply qltT_leT'. apply Qlt_to_QltT. apply Qinv_lt_0_compat.
    unfold Qlt. cbn [Qnum Qden]. lia. }
  assert (Hlit : QleT'
    (((2 # 1)%Q * (Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1))%Q)
    ((Z.of_nat (Datatypes.S (2 * n - Datatypes.S k)) # 1)%Q *
     (Z.of_nat (Datatypes.S k) # 1)%Q)).
  { apply Qle_to_QleT'. unfold Qle.
    cbn [Qnum Qden Qmult Pos.mul]. nia. }
  apply (qleT'_trans 2%Q
    (((2 # 1)%Q * (Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1))%Q *
     Qinv ((Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1))%Q)
    ((Z.of_nat (Datatypes.S (2 * n - Datatypes.S k)) # 1)%Q *
     (Z.of_nat (Datatypes.S k) # 1)%Q *
     Qinv ((Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1))%Q)).
  - apply qeq_leT'. apply qeq_imp_qeqT.
    apply (Qeq_trans 2%Q
      (2%Q * ((Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1)%Q *
              Qinv ((Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1))%Q))
      (((2 # 1)%Q * (Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1))%Q *
       Qinv ((Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1))%Q)).
    + apply (Qeq_trans 2%Q (2%Q * 1%Q)
               (2%Q * ((Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1)%Q *
                       Qinv ((Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1))%Q))).
      * ring.
      * apply (Qmult_comp 2%Q 2%Q (Qeq_refl 2%Q) 1%Q
                 ((Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1)%Q *
                  Qinv ((Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1))%Q)
                 (Qeq_sym ((Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1)%Q *
                           Qinv ((Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1))%Q)
                          1%Q
                          (Qmult_inv_r (Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1)%Q
                                       (fun Habs => Empty_set_ind (fun _ => False)
                                                   (pdp_ZS1_nz (n - Datatypes.S k)
                                                   (qeq_imp_qeqT _ _ Habs)))))).
    + ring.
  - apply (pdp_qmult_le_compat_r _ _
             (Qinv ((Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1))%Q)).
    + exact Hlit.
    + exact Hdinv.
Qed.

(* Term decay (over the whole range x <= 2): k < n and 0 <= x < 2 imply
   t_{k+1} <= t_k.  Canceling the ratio (the completing step of the leftover
   item b): t_{k+1} = c_{k+1}*(x*x^k) <= c_{k+1}*(R*x^k) (two uses of
   qleT'_mult: x <= 2 <= R) == (c_{k+1}*R)*x^k == c_k*x^k (rewritten by
   pdp_coeff_ratio). *)
Lemma pdpa_term_decay : forall (n k : nat) (x : Q),
  (k < n)%nat -> QleT' 0 x -> QltT x 2 ->
  QleT' (pdp_g n x (Datatypes.S k)) (pdp_g n x k).
Proof.
  intros n k x Hk Hx Hx2.
  assert (E1 : (Datatypes.S k <=? n)%nat = true) by (apply Nat.leb_le; lia).
  assert (E2 : (k <=? n)%nat = true) by (apply Nat.leb_le; lia).
  unfold pdp_g. rewrite E1, E2.
  assert (Hxq : QleT' 0 (q_pow x k))
    by (apply q_pow_nonneg; exact Hx).
  assert (HxR : QleT' x (pdp_R n k)).
  { apply (qleT'_trans x 2%Q (pdp_R n k)).
    - apply qltT_leT'. exact Hx2.
    - apply pdpa_R_ge_2. exact Hk. }
  apply (qleT'_trans
    (pade_coeff n (Datatypes.S k) * q_pow x (Datatypes.S k))
    (pade_coeff n (Datatypes.S k) * (pdp_R n k * q_pow x k))
    (pade_coeff n k * q_pow x k)).
  - apply (qleT'_mult_compat_l (x * q_pow x k) (pdp_R n k * q_pow x k)
             (pade_coeff n (Datatypes.S k))).
    + apply qltT_leT'. apply pdp_coeff_pos_any.
    + apply (qleT'_mult_compat_r x (pdp_R n k) (q_pow x k) Hxq HxR).
  - apply qeq_leT'. apply qeq_imp_qeqT.
    apply (Qeq_trans (pade_coeff n (Datatypes.S k) * (pdp_R n k * q_pow x k))
                     ((pade_coeff n (Datatypes.S k) * pdp_R n k) * q_pow x k)
                     (pade_coeff n k * q_pow x k)).
    + ring.
    + apply (Qmult_comp (pade_coeff n (Datatypes.S k) * pdp_R n k)
               (pade_coeff n k)
               (Qeq_sym (pade_coeff n k)
                        (pade_coeff n (Datatypes.S k) * pdp_R n k)
                        (qeqT_imp_qeq _ _ (pdp_coeff_ratio n k Hk)))
               (q_pow x k) (q_pow x k) (Qeq_refl (q_pow x k))).
Qed.

(* First-pair strictness: 1 <= n and x < 2 imply t_1 <T t_0.
   c_1*x <T c_1*2 (qltT_mult_ltT_compat_r, 0 < c_1) == (transported on both
   sides by Qmult_comm / qltT_eq_compat) c_1*x <T c_0, then reshaped through
   the pdp_g unfolding (q_pow x 1 == x, q_pow x 0 == 1). *)
Lemma pdpa_g1_lt_g0 : forall (n : nat) (x : Q),
  (1 <= n)%nat -> QltT x 2 -> QltT (pdp_g n x 1%nat) (pdp_g n x 0%nat).
Proof.
  intros n x Hn Hx2.
  assert (E1 : (1 <=? n)%nat = true) by (apply Nat.leb_le; lia).
  assert (E0 : (0 <=? n)%nat = true) by (apply Nat.leb_le; lia).
  assert (Hp0 : q_pow x 0%nat == 1%Q) by apply Qeq_refl.
  assert (Hp1 : q_pow x 1%nat == x).
  { apply (Qeq_trans (q_pow x 1%nat) (x * q_pow x 0%nat) x).
    - apply qeqT_imp_qeq. apply q_pow_succ.
    - apply (Qeq_trans (x * q_pow x 0%nat) (x * 1%Q) x).
      + apply (Qmult_comp x x (Qeq_refl x) (q_pow x 0%nat) 1%Q Hp0).
      + ring. }
  assert (Eg1 : pdp_g n x 1%nat == pade_coeff n 1%nat * x).
  { unfold pdp_g. rewrite E1.
    apply (Qmult_comp (pade_coeff n 1%nat) (pade_coeff n 1%nat)
             (Qeq_refl (pade_coeff n 1%nat)) (q_pow x 1%nat) x Hp1). }
  assert (Eg0 : pdp_g n x 0%nat == pade_coeff n 0%nat).
  { unfold pdp_g. rewrite E0.
    apply (Qeq_trans (pade_coeff n 0%nat * q_pow x 0%nat)
                     (pade_coeff n 0%nat * 1%Q) (pade_coeff n 0%nat)).
    - apply (Qmult_comp (pade_coeff n 0%nat) (pade_coeff n 0%nat)
               (Qeq_refl (pade_coeff n 0%nat)) (q_pow x 0%nat) 1%Q Hp0).
    - ring. }
  assert (Hm1 : pade_coeff n 1%nat * q_pow x 1%nat == pade_coeff n 1%nat * x).
  { apply (Qmult_comp (pade_coeff n 1%nat) (pade_coeff n 1%nat)
             (Qeq_refl (pade_coeff n 1%nat)) (q_pow x 1%nat) x Hp1). }
  assert (Hstep : QltT (x * pade_coeff n 1%nat) (2%Q * pade_coeff n 1%nat))
    by (apply (qltT_mult_ltT_compat_r x 2%Q (pade_coeff n 1%nat));
        [apply pdp_coeff_pos_any | exact Hx2]).
  assert (Hr1 : QltT (x * pade_coeff n 1%nat) (pade_coeff n 1%nat * 2%Q))
    by (apply (qltT_eq_compat_r (pade_coeff n 1%nat * 2%Q)
                 (2%Q * pade_coeff n 1%nat) (x * pade_coeff n 1%nat));
        [apply qeq_imp_qeqT; apply Qmult_comm | exact Hstep]).
  assert (Hr2 : QltT (x * pade_coeff n 1%nat) (pade_coeff n 0%nat))
    by (apply (qltT_eq_compat_r (pade_coeff n 0%nat)
                 (pade_coeff n 1%nat * 2%Q) (x * pade_coeff n 1%nat));
        [apply qeq_imp_qeqT; apply Qeq_sym; apply pdpa_c1_2_c0; exact Hn
        | exact Hr1]).
  assert (Hl1 : QltT (pade_coeff n 1%nat * x) (pade_coeff n 0%nat))
    by (apply (qltT_eq_compat_l (x * pade_coeff n 1%nat)
                 (pade_coeff n 1%nat * x) (pade_coeff n 0%nat));
        [apply qeq_imp_qeqT; apply Qmult_comm | exact Hr2]).
  assert (Hl2 : QltT (pade_coeff n 1%nat * q_pow x 1%nat) (pade_coeff n 0%nat))
    by (apply (qltT_eq_compat_l (pade_coeff n 1%nat * x)
                 (pade_coeff n 1%nat * q_pow x 1%nat) (pade_coeff n 0%nat));
        [apply qeq_imp_qeqT; apply Qeq_sym; exact Hm1 | exact Hl1]).
  assert (Hm1r : pade_coeff n 1%nat * q_pow x 1%nat == pdp_g n x 1%nat).
  { apply (Qeq_trans (pade_coeff n 1%nat * q_pow x 1%nat)
             (pade_coeff n 1%nat * x) (pdp_g n x 1%nat)).
    - exact Hm1.
    - apply Qeq_sym. exact Eg1. }
  assert (Hl3 : QltT (pdp_g n x 1%nat) (pade_coeff n 0%nat))
    by (apply (qltT_eq_compat_l (pade_coeff n 1%nat * q_pow x 1%nat)
                 (pdp_g n x 1%nat) (pade_coeff n 0%nat));
        [exact (qeq_imp_qeqT _ _ Hm1r) | exact Hl2]).
  apply (qltT_eq_compat_r (pdp_g n x 0%nat) (pade_coeff n 0%nat)
            (pdp_g n x 1%nat) (qeq_imp_qeqT _ _ Eg0) Hl3).
Qed.

(* Part 2: the n = 0 special case and the main theorem *)

(* pade_den 0 x == 1 (the single term of sum_upto 1: after the three
   rewrites q_pow (-1) 0 == 1, q_pow x 0 == 1, c_0 == 1, closed by ring) *)
Lemma pdpa_den0_one : forall x : Q, pade_den 0 x == 1%Q.
Proof.
  intro x. unfold pade_den.
  cbn [sum_upto q_pow].
  rewrite pdpa_c0_one.
  ring.
Qed.

(* Main theorem: 0 <= x < 2 implies 0 <T the denominator (for every n).
   n = 0: den == 1 closes directly; n >= 1: resolved by instantiating
   altsum_pos_strict -- every term nonnegative (pdp_g_nonneg), every term
   nonincreasing (k < n goes through pdpa_term_decay, k >= n goes through
   the pdp_g_decay_hi zeroed segment), the first pair strict
   (pdpa_g1_lt_g0), and 2 <= S n; the pade_den bridge (pdp_den_altsum)
   returns to the original shape. *)
Theorem pdpa_den_pos_strict : forall (n : nat) (x : Q),
  QleT 0 x -> QltT x 2 -> QltT 0 (pade_den n x).
Proof.
  intros n x Hx0 Hx2.
  destruct n as [| m].
  - apply (qeq_ltT 1%Q (pade_den 0%nat x)).
    + apply qeq_imp_qeqT. apply Qeq_sym. apply pdpa_den0_one.
    + apply qltT_0_1.
  - assert (Hxa : QleT' 0 x) by (apply altsum_QleT_to_QleT'; exact Hx0).
    assert (Hb : pade_den (Datatypes.S m) x ==
                 altsum (pdp_g (Datatypes.S m) x)
                        (Datatypes.S (Datatypes.S m)))
      by (apply qeqT_imp_qeq; apply pdp_den_altsum).
    apply (qeq_ltT (altsum (pdp_g (Datatypes.S m) x)
                            (Datatypes.S (Datatypes.S m)))
                   (pade_den (Datatypes.S m) x)).
    + apply qeq_imp_qeqT. apply Qeq_sym. exact Hb.
    + apply (altsum_pos_strict (pdp_g (Datatypes.S m) x)
                 (Datatypes.S (Datatypes.S m))).
      * intro k. apply pdp_g_nonneg. exact Hxa.
      * intro k. destruct (Nat.leb (Datatypes.S k) (Datatypes.S m)) eqn:E.
        -- apply (pdpa_term_decay (Datatypes.S m) k x).
           ++ apply Nat.leb_le in E. lia.
           ++ exact Hxa.
           ++ exact Hx2.
        -- apply (pdp_g_decay_hi (Datatypes.S m) x k).
           ++ exact Hxa.
           ++ apply Nat.leb_gt in E. lia.
      * apply (pdpa_g1_lt_g0 (Datatypes.S m) x).
        -- lia.
        -- exact Hx2.
      * lia.
Qed.

(* The original-form bridge for the leftover item a: 0 <= x < 1 implies the
   same conclusion (the upper bound transported through x < 1 <= 2) *)
Corollary pdpa_den_pos_strict_lt1 : forall (n : nat) (x : Q),
  QleT 0 x -> QltT x 1 -> QltT 0 (pade_den n x).
Proof.
  intros n x Hx0 Hx1.
  apply pdpa_den_pos_strict.
  - exact Hx0.
  - assert (H12 : QleT' 1%Q 2%Q).
    { apply Qle_to_QleT'. unfold Qle. cbn [Qnum Qden]. lia. }
    exact (qltT_leT'_ltT x 1%Q 2%Q Hx1 H12).
Qed.

(* G4 evidence: every piece carries zero external unproven assumptions *)
Print Assumptions pdpa_c0_nz.
Print Assumptions pdpa_c0_one.
Print Assumptions pdpa_R0_two.
Print Assumptions pdpa_c1_2_c0.
Print Assumptions pdpa_R_ge_2.
Print Assumptions pdpa_term_decay.
Print Assumptions pdpa_g1_lt_g0.
Print Assumptions pdpa_den0_one.
Print Assumptions pdpa_den_pos_strict.
Print Assumptions pdpa_den_pos_strict_lt1.
(* ================= §2 the dpc_den_pos_close family ================= *)
From Stdlib Require Import QArith.QArith Arith.Arith Lia.

(* The citation-forwarding main piece: the unified closed form of the
   strict tier -- the statement face is verbatim-isomorphic to
   pdpa_den_pos_strict, every argument forwarded by exact, zero new proof
   (the theorem face settled at the source-4 coordinate). *)
Theorem dpc_den_pos_close : forall (n : nat) (x : Q),
  QleT 0 x -> QltT x (2#1) -> QltT 0 (pade_den n x).
Proof. exact pdpa_den_pos_strict. Qed.

(* The citation-forwarding cross-witness: the same statement face is
   independently reachable through the supplementary source-5 (the dpg_
   piece, with n = 0 going through pdpa_den0_one) -- a two-route in-library
   demonstration for the strict tier. *)
Theorem dpc_den_pos_close_alt : forall (n : nat) (x : Q),
  QleT 0 x -> QltT x (2#1) -> QltT 0 (pade_den n x).
Proof.
  intros n x Hx H2.
  destruct n as [| m].
  - apply (qeq_ltT 1%Q (pade_den 0%nat x)).
    + apply qeq_imp_qeqT. apply Qeq_sym. apply pdpa_den0_one.
    + apply qltT_0_1.
  - apply (dpg_den_pos_strict_T (Datatypes.S m) x).
    + lia.
    + exact Hx.
    + exact H2.
Qed.

(* The statement face (QltT 0 x -> QltT x 2 -> QltT 0 (pade_den 1 x)) is
   instantiated directly from the general strict tier -- the sentinel that
   the general piece is instantiated back on home ground, honoring the
   promised clause. *)
Theorem dpc_pds_den1_pos_sentinel : forall x : Q,
  QltT 0 x -> QltT x (2#1) -> QltT 0 (pade_den 1%nat x).
Proof.
  intros x H0 H2.
  apply (dpc_den_pos_close 1%nat x).
  - left. exact H0.
  - exact H2.
Qed.

(* ===== G1 evidence: the citation chain is entirely in-library Closed pieces ===== *)
Print Assumptions dpc_den_pos_close.
Print Assumptions dpc_den_pos_close_alt.
Print Assumptions dpc_pds_den1_pos_sentinel.
