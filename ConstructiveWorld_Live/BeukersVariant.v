(* ==========================================================================)
   BeukersVariant.v - Set-face canonical form of the (1+t)^(n+1) variant
   Beukers approximation series (Q layer).
   Mission. The variant integral I'_n := integral over [0,1] of
     t^n(1-t)^n/(1+t)^(n+1) dt; all-positive series expansion
     I'_n = sum_{m>=0} C(n+m,n) * B(n+2m+1, 2n+1); the truncated carrier
     bv_carrier n M integrates exactly to the partial series sum (exact
     QeqT), monotone in M, strictly positive. True-normalized conclusion:
     ln2 - p_n/q~_n == I'_n/q~_n (no 2-power factor); the 2-power form
     bv_x2pow is incompatible with it (bv_x2pow_sep1: bv_x2pow 1 == 1/3
     < 2/3 == bv_x 1); anchors p: 0, 2, 9, 131/3 and x: 0, 2/3, 9/13.
     This seat washes the surveyed mechanical face (10 stations: seven
     Qeq statements lifted to QeqT, three bare nat equalities lifted to
     Id), proof-body bridges wrapped per signatures measured in the born
     world (probe_bks3_sig); the two toy-proof ablation pieces
     (bv_pos_cint, bv_zeros_int0) preserved.
   Dependencies. S01_BaseRing, S02_CauchyComplete, S03_QExp, S07_RealSetoidExpLog (Id bridge source, enbig2 BeukersLists precedent), PolyIntegral, PadeErrorIntegral, BeukersLists (enbig2 English version), PintMono (Set tree source).
   References. Coefficient combinatorics of Beukers-type Pade approximation (Delannoy numbers, Beta integrals).
   Constructivity. Every main theorem ends in Qed with zero acknowledged premises (Print Assumptions block at file end re-audits closure); main conclusions ride the Q-layer Set face (QeqT/QltT/QleT'), the Qeq/Qle/Qlt support lemmas are Prop-face, reasoning only; extractable.
   Build. rocq c -native-compiler no -q -Q . "" BeukersVariant.v inside the fresh-born seat world (S01-S15 chain plus PolyIntegral, PadeErrorIntegral, PintMono, BeukersLists) under the cpu_guard wrapper; tree .vo files are never rewritten.
   ========================================================================== *)

From Stdlib Require Import QArith.QArith Lists.List Arith.Arith ZArith.ZArith Lia.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp.
Require Import PolyIntegral.
Require Import PadeErrorIntegral BeukersLists PintMono.
Require Import S07_RealSetoidExpLog.

Open Scope nat_scope.

(* ============================================================ *)
(* Sec A. Series shaping: the series term bv_term = C(n+m,n)*B(n+2m+1, 2n+1) *)
(*   and its positivity                                                      *)
(* ============================================================ *)

Definition bv_term (n m : nat) : Q :=
  ((Z.of_nat (bkC (n + m) n) # 1) *
     (q_fact (n + 2 * m) * q_fact (2 * n + 1) / q_fact (3 * n + 2 * m + 2)))%Q.

(* bv_term n m == C(n+m,n) * integral t^{n+2m}(1-t)^{2n+1} (via pei_beta_value *)
(* down to pint_integral)                                                      *)
Lemma bv_term_value : forall n m : nat,
  QeqT (bv_term n m)
       (((Z.of_nat (bkC (n + m) n) # 1) *
           pint_integral (pei_list (n + 2 * m) (2 * n + 1)))%Q).
Proof.
  intros n m. apply qeq_imp_qeqT. unfold bv_term.
  rewrite (qeqT_imp_qeq _ _ (pei_beta_value (n + 2 * m) (2 * n + 1))).
  replace ((n + 2 * m) + (2 * n + 1) + 1)%nat with (3 * n + 2 * m + 2)%nat by lia.
  reflexivity.
Qed.

(** bv_term_pos: the series term is strictly positive -- bkC >= 1 multiplied  *)
(* by q_fact positivity.                                                      *)
Theorem bv_term_pos : forall n m : nat, QltT 0 (bv_term n m).
Proof.
  intros n m. apply Qlt_to_QltT. unfold bv_term. unfold Qdiv.
  apply Qmult_lt_0_compat.
  - assert (Hb : NatLe 1 (bkC (n + m) n)) by (apply bkC_pos; apply NatLe_lift; lia).
    pose proof (NatLe_drop _ _ Hb) as HbP.
    assert (Hz : (0 <= Z.of_nat (bkC (n + m) n))%Z) by apply Nat2Z.is_nonneg.
    unfold Qlt. cbn [Qnum Qden Qmult Pos.mul]. lia.
  - apply Qmult_lt_0_compat.
    + apply Qmult_lt_0_compat; apply QltT_to_Qlt; apply q_fact_pos.
    + apply Qinv_lt_0_compat. apply QltT_to_Qlt. apply q_fact_pos.
Qed.

(* ============================================================ *)
(* Sec B. Truncated carrier: bv_pad (two zero coefficients appended) and      *)
(*   bv_carrier (same shape as pei_eb_list)                                   *)
(* ============================================================ *)

Definition bv_pad (p : list Q) : list Q := pei_ztail (pei_ztail p).

Lemma bv_pad_eval : forall (p : list Q) (x : Q),
  QeqT (pint_eval (bv_pad p) x) (pint_eval p x).
Proof.
  intros p x. apply qeq_imp_qeqT. unfold bv_pad.
  rewrite (qeqT_imp_qeq _ _ (pei_eval_ztail (pei_ztail p) x)),
          (qeqT_imp_qeq _ _ (pei_eval_ztail p x)).
  reflexivity.
Qed.

Lemma bv_pad_int : forall p : list Q,
  QeqT (pint_integral (bv_pad p)) (pint_integral p).
Proof.
  intro p. apply qeq_imp_qeqT. unfold bv_pad.
  rewrite (qeqT_imp_qeq _ _ (pei_integral_ztail (pei_ztail p))),
          (qeqT_imp_qeq _ _ (pei_integral_ztail p)).
  reflexivity.
Qed.

Lemma bv_pad_length : forall p : list Q,
  Id (length (bv_pad p)) (length p + 2)%nat.
Proof.
  intro p. apply RealSetoid.eq_Id. unfold bv_pad, pei_ztail.
  rewrite app_length, app_length. cbn [length]. lia.
Qed.

(* bv_carrier n M: coefficient list of the partial sum                        *)
(* sum_{m<=M} C(n+m,n) t^{n+2m}(1-t)^{2n+1} (pei_eb_list shape)               *)
Fixpoint bv_carrier (n M : nat) : list Q :=
  match M with
  | 0 => pint_scale ((Z.of_nat (bkC (n + 0) n) # 1)%Q)
                    (pei_list (n + 2 * 0) (2 * n + 1))
  | Datatypes.S m =>
      pint_add (pint_scale ((Z.of_nat (bkC (n + Datatypes.S m) n) # 1)%Q)
                           (pei_list (n + 2 * Datatypes.S m) (2 * n + 1)))
               (bv_pad (bv_carrier n m))
  end.

Lemma bv_carrier_length : forall n M : nat,
  Id (length (bv_carrier n M)) (3 * n + 2 * M + 2)%nat.
Proof.
  intros n M. induction M as [| m IH].
  - apply RealSetoid.eq_Id.
    change (bv_carrier n 0)
      with (pint_scale ((Z.of_nat (bkC (n + 0) n) # 1)%Q)
                       (pei_list (n + 2 * 0) (2 * n + 1))).
    rewrite (RealSetoid.Id_eq _ _
              (pei_scale_length ((Z.of_nat (bkC (n + 0) n) # 1)%Q)
                                (pei_list (n + 2 * 0) (2 * n + 1)))),
            (RealSetoid.Id_eq _ _
              (pei_list_length (n + 2 * 0) (2 * n + 1))).
    lia.
  - apply RealSetoid.eq_Id.
    change (bv_carrier n (Datatypes.S m))
      with (pint_add (pint_scale ((Z.of_nat (bkC (n + Datatypes.S m) n) # 1)%Q)
                                 (pei_list (n + 2 * Datatypes.S m) (2 * n + 1)))
                     (bv_pad (bv_carrier n m))).
    assert (HL : Id (length (pint_scale ((Z.of_nat (bkC (n + Datatypes.S m) n) # 1)%Q)
                                        (pei_list (n + 2 * Datatypes.S m) (2 * n + 1))))
                    (length (bv_pad (bv_carrier n m)))).
    { apply RealSetoid.eq_Id.
      rewrite (RealSetoid.Id_eq _ _
                (pei_scale_length ((Z.of_nat (bkC (n + Datatypes.S m) n) # 1)%Q)
                                  (pei_list (n + 2 * Datatypes.S m) (2 * n + 1)))),
              (RealSetoid.Id_eq _ _
                (pei_list_length (n + 2 * Datatypes.S m) (2 * n + 1))),
              (RealSetoid.Id_eq _ _ (bv_pad_length (bv_carrier n m))),
              (RealSetoid.Id_eq _ _ IH).
      lia. }
    rewrite (RealSetoid.Id_eq _ _ (pei_add_length
              (pint_scale ((Z.of_nat (bkC (n + Datatypes.S m) n) # 1)%Q)
                          (pei_list (n + 2 * Datatypes.S m) (2 * n + 1)))
              (bv_pad (bv_carrier n m)) HL)),
            (RealSetoid.Id_eq _ _
              (pei_scale_length ((Z.of_nat (bkC (n + Datatypes.S m) n) # 1)%Q)
                                (pei_list (n + 2 * Datatypes.S m) (2 * n + 1)))),
            (RealSetoid.Id_eq _ _
              (pei_list_length (n + 2 * Datatypes.S m) (2 * n + 1))).
    lia.
Qed.

(** bv_carrier_eval: pointwise value == t^n(1-t)^{2n+1} *                     *)
(* sum_{m<=M} C(n+m,n)(t^2)^m (negative-binomial-type truncation).            *)
Theorem bv_carrier_eval : forall (n M : nat) (t : Q),
  QeqT (pint_eval (bv_carrier n M) t)
       (q_pow t n * q_pow (1 - t)%Q (2 * n + 1) *
         bk_psQ (fun m : nat => (Z.of_nat (bkC (n + m) n) # 1)%Q)
                (Datatypes.S M) (t * t)%Q).
Proof.
  intros n M. induction M as [| m IH]; intro t.
  - apply qeq_imp_qeqT.
    change (bv_carrier n 0)
      with (pint_scale ((Z.of_nat (bkC (n + 0) n) # 1)%Q)
                       (pei_list (n + 2 * 0) (2 * n + 1))).
    change (bk_psQ (fun m0 : nat => (Z.of_nat (bkC (n + m0) n) # 1)%Q)
                   (Datatypes.S 0) (t * t)%Q)
      with (0 + (Z.of_nat (bkC (n + 0) n) # 1) * 1)%Q.
    rewrite (qeqT_imp_qeq _ _
              (pei_eval_scale ((Z.of_nat (bkC (n + 0) n) # 1)%Q)
                              (pei_list (n + 2 * 0) (2 * n + 1)) t)).
    rewrite (qeqT_imp_qeq _ _ (pei_beta_eval (n + 2 * 0) (2 * n + 1) t)).
    replace (n + 2 * 0)%nat with n%nat by lia.
    ring.
  - apply qeq_imp_qeqT.
    change (bv_carrier n (Datatypes.S m))
      with (pint_add (pint_scale ((Z.of_nat (bkC (n + Datatypes.S m) n) # 1)%Q)
                                 (pei_list (n + 2 * Datatypes.S m) (2 * n + 1)))
                     (bv_pad (bv_carrier n m))).
    rewrite (qeqT_imp_qeq _ _
              (pei_eval_add
                 (pint_scale ((Z.of_nat (bkC (n + Datatypes.S m) n) # 1)%Q)
                             (pei_list (n + 2 * Datatypes.S m) (2 * n + 1)))
                 (bv_pad (bv_carrier n m)) t)).
    rewrite (qeqT_imp_qeq _ _
              (pei_eval_scale ((Z.of_nat (bkC (n + Datatypes.S m) n) # 1)%Q)
                              (pei_list (n + 2 * Datatypes.S m) (2 * n + 1)) t)).
    rewrite (qeqT_imp_qeq _ _
              (pei_beta_eval (n + 2 * Datatypes.S m) (2 * n + 1) t)).
    rewrite (qeqT_imp_qeq _ _ (bv_pad_eval (bv_carrier n m) t)).
    rewrite (qeqT_imp_qeq _ _ (IH t)).
    assert (HpsQ : bk_psQ (fun m0 : nat => (Z.of_nat (bkC (n + m0) n) # 1)%Q)
                          (Datatypes.S (Datatypes.S m)) (t * t)%Q
                   == bk_psQ (fun m0 : nat => (Z.of_nat (bkC (n + m0) n) # 1)%Q)
                          (Datatypes.S m) (t * t)%Q
                      + (Z.of_nat (bkC (n + Datatypes.S m) n) # 1)%Q
                          * q_pow (t * t)%Q (Datatypes.S m))
      by reflexivity.
    rewrite HpsQ.
    rewrite (qeqT_imp_qeq _ _ (q_pow_add t n (2 * Datatypes.S m))).
    replace (2 * Datatypes.S m)%nat with (Datatypes.S m + Datatypes.S m)%nat by lia.
    rewrite (qeqT_imp_qeq _ _ (q_pow_add t (Datatypes.S m) (Datatypes.S m))).
    rewrite <- (qeqT_imp_qeq _ _ (bk_q_pow_mul t t (Datatypes.S m))).
    ring.
Qed.

(* ============================================================ *)
(* Sec C. Truncated integral: bv_carrier_value exact value, bv_sum_mono       *)
(*   monotone in M, bv_sum_pos strictly positive                              *)
(* ============================================================ *)

Fixpoint bv_zeros (L : nat) : list Q :=
  match L with
  | 0 => nil
  | Datatypes.S m => 0%Q :: bv_zeros m
  end.

Lemma bv_zeros_length : forall L : nat, Id (length (bv_zeros L)) L.
Proof.
  induction L as [| l IH].
  - apply RealSetoid.eq_Id. reflexivity.
  - apply RealSetoid.eq_Id. cbn [bv_zeros length].
    rewrite (RealSetoid.Id_eq _ _ IH). reflexivity.
Qed.

Lemma bv_zeros_int : forall (L k : nat),
  QeqT (pint_integral_from (bv_zeros L) k) 0%Q.
Proof.
  induction L as [| l IH]; intros k.
  - apply qeq_imp_qeqT. reflexivity.
  - apply qeq_imp_qeqT. cbn [bv_zeros pint_integral_from].
    unfold pint_monomial_int.
    rewrite (qeqT_imp_qeq _ _ (pint_zero_div (Z.of_nat (Datatypes.S k) # 1))).
    rewrite Qplus_0_l. exact (qeqT_imp_qeq _ _ (IH (Datatypes.S k))).
Qed.

Theorem bv_zeros_int0 : forall L : nat, QeqT (pint_integral (bv_zeros L)) 0%Q.
Proof. intro L. unfold pint_integral. exact (bv_zeros_int L 0). Qed.

Lemma bv_c_pos_le : forall n m : nat, QleT' 0 ((Z.of_nat (bkC (n + m) n) # 1)%Q).
Proof.
  intros n m. apply Qle_to_QleT'. unfold Qle. cbn [Qnum Qden Qmult Pos.mul].
  assert (Hb : NatLe 1 (bkC (n + m) n)) by (apply bkC_pos; apply NatLe_lift; lia).
  pose proof (NatLe_drop _ _ Hb) as HbP.
  assert (Hz : (0 <= Z.of_nat (bkC (n + m) n))%Z) by apply Nat2Z.is_nonneg.
  lia.
Qed.

Lemma bv_pos_cint : forall n m : nat,
  QleT' 0 (pint_integral (pei_list (n + 2 * m) (2 * n + 1))).
Proof.
  intros n m.
  exact (Qle_to_QleT' 0
    (pint_integral (pei_list (n + 2 * m) (2 * n + 1)))
    (Qlt_le_weak 0 (pint_integral (pei_list (n + 2 * m) (2 * n + 1)))
       (QltT_to_Qlt 0 (pint_integral (pei_list (n + 2 * m) (2 * n + 1)))
          (pei_beta_pos (n + 2 * m) (2 * n + 1))))).
Qed.

(** bv_carrier_value: the truncated integral == the partial series sum        *)
(* sum_{m<=M} bv_term n m (exact QeqT).                                       *)
Theorem bv_carrier_value : forall n M : nat,
  QeqT (pint_integral (bv_carrier n M))
       (sum_upto (Datatypes.S M) (fun m : nat => bv_term n m)).
Proof.
  intros n M. induction M as [| m IH].
  - apply qeq_imp_qeqT.
    change (bv_carrier n 0)
      with (pint_scale ((Z.of_nat (bkC (n + 0) n) # 1)%Q)
                       (pei_list (n + 2 * 0) (2 * n + 1))).
    change (sum_upto (Datatypes.S 0) (fun m0 : nat => bv_term n m0))
      with (0 + bv_term n 0)%Q.
    rewrite (qeqT_imp_qeq _ _
              (pint_integral_scale ((Z.of_nat (bkC (n + 0) n) # 1)%Q)
                                   (pei_list (n + 2 * 0) (2 * n + 1)))).
    rewrite (qeqT_imp_qeq _ _ (pei_beta_value (n + 2 * 0) (2 * n + 1))).
    unfold bv_term.
    replace (n + 2 * 0)%nat with n%nat by lia.
    replace (3 * n + 2 * 0 + 2)%nat with (n + (2 * n + 1) + 1)%nat by lia.
    ring.
  - apply qeq_imp_qeqT.
    change (bv_carrier n (Datatypes.S m))
      with (pint_add (pint_scale ((Z.of_nat (bkC (n + Datatypes.S m) n) # 1)%Q)
                                 (pei_list (n + 2 * Datatypes.S m) (2 * n + 1)))
                     (bv_pad (bv_carrier n m))).
    change (sum_upto (Datatypes.S (Datatypes.S m)) (fun m0 : nat => bv_term n m0))
      with (sum_upto (Datatypes.S m) (fun m0 : nat => bv_term n m0)
              + bv_term n (Datatypes.S m))%Q.
    assert (HL : length (pint_scale ((Z.of_nat (bkC (n + Datatypes.S m) n) # 1)%Q)
                                    (pei_list (n + 2 * Datatypes.S m) (2 * n + 1)))
                 = length (bv_pad (bv_carrier n m))).
    { pose proof (RealSetoid.Id_eq _ _
              (pei_scale_length ((Z.of_nat (bkC (n + Datatypes.S m) n) # 1)%Q)
                                (pei_list (n + 2 * Datatypes.S m) (2 * n + 1)))) as H1.
      pose proof (RealSetoid.Id_eq _ _
              (pei_list_length (n + 2 * Datatypes.S m) (2 * n + 1))) as H2.
      pose proof (RealSetoid.Id_eq _ _ (bv_pad_length (bv_carrier n m))) as H3.
      pose proof (RealSetoid.Id_eq _ _ (bv_carrier_length n m)) as H4.
      lia. }
    rewrite (qeqT_imp_qeq _ _ (pint_integral_add _ _ HL)).
    rewrite (qeqT_imp_qeq _ _ (bv_pad_int (bv_carrier n m))).
    rewrite (qeqT_imp_qeq _ _
              (pint_integral_scale ((Z.of_nat (bkC (n + Datatypes.S m) n) # 1)%Q)
                                   (pei_list (n + 2 * Datatypes.S m) (2 * n + 1)))).
    rewrite (qeqT_imp_qeq _ _
              (pei_beta_value (n + 2 * Datatypes.S m) (2 * n + 1))),
            (qeqT_imp_qeq _ _ IH).
    unfold bv_term.
    replace ((n + 2 * Datatypes.S m) + (2 * n + 1) + 1)%nat
      with (3 * n + 2 * Datatypes.S m + 2)%nat by lia.
    ring.
Qed.

(** bv_sum_mono: the truncated integral is monotone in M (QleT'); composed    *)
(* from PintMono pm_scale_mono, pm_add_mono and the same-value movers         *)
(* pm_qle_wd_l, pm_qle_wd_r.                                                  *)
Theorem bv_sum_mono : forall n M : nat,
  QleT' (pint_integral (bv_carrier n M))
        (pint_integral (bv_carrier n (Datatypes.S M))).
Proof.
  intros n M.
  change (pint_integral (bv_carrier n (Datatypes.S M)))
    with (pint_integral (pint_add
             (pint_scale ((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q)
                         (pei_list (n + 2 * Datatypes.S M) (2 * n + 1)))
             (bv_pad (bv_carrier n M)))).
  assert (Hlen : length (pint_scale ((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q)
                                    (pei_list (n + 2 * Datatypes.S M) (2 * n + 1)))
                 = length (bv_pad (bv_carrier n M))).
  { pose proof (RealSetoid.Id_eq _ _
          (pei_scale_length ((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q)
                            (pei_list (n + 2 * Datatypes.S M) (2 * n + 1)))) as H1.
    pose proof (RealSetoid.Id_eq _ _
          (pei_list_length (n + 2 * Datatypes.S M) (2 * n + 1))) as H2.
    pose proof (RealSetoid.Id_eq _ _ (bv_pad_length (bv_carrier n M))) as H3.
    pose proof (RealSetoid.Id_eq _ _ (bv_carrier_length n M)) as H4.
    lia. }
  assert (HId1 : Id (length (bv_zeros (3 * n + 2 * M + 2 + 2)))
                    (length (bv_pad (bv_carrier n M)))).
  { apply RealSetoid.eq_Id.
    pose proof (RealSetoid.Id_eq _ _
          (bv_zeros_length (3 * n + 2 * M + 2 + 2))) as H1.
    pose proof (RealSetoid.Id_eq _ _ (bv_pad_length (bv_carrier n M))) as H2.
    pose proof (RealSetoid.Id_eq _ _ (bv_carrier_length n M)) as H3.
    lia. }
  assert (HId2 : Id (length (pint_scale ((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q)
                                        (pei_list (n + 2 * Datatypes.S M) (2 * n + 1))))
                    (length (bv_pad (bv_carrier n M)))).
  { exact (RealSetoid.eq_Id _ _ Hlen). }
  (* Middle step HleX: 0 <= C(n+M,n) * the Beta integral, via bv_c_pos_le,    *)
  (* bv_pos_cint and pm_scale_mono.                                           *)
  assert (HleX : QleT' 0 (pint_integral
                    (pint_scale ((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q)
                                (pei_list (n + 2 * Datatypes.S M) (2 * n + 1))))).
  { apply (pm_qle_wd_r
             (((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q *
               pint_integral (pei_list (n + 2 * Datatypes.S M) (2 * n + 1)))%Q)
             (pint_integral (pint_scale ((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q)
                                        (pei_list (n + 2 * Datatypes.S M) (2 * n + 1))))
             0%Q).
    - apply Qeq_sym. apply qeqT_imp_qeq.
      apply (pint_integral_scale ((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q)
                                 (pei_list (n + 2 * Datatypes.S M) (2 * n + 1))).
    - apply (pm_qle_wd_l
               (pint_integral (pint_scale ((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q)
                                          (bv_zeros (3 * n + 2 * M + 2 + 2))))
               0%Q
               (((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q *
                 pint_integral (pei_list (n + 2 * Datatypes.S M) (2 * n + 1)))%Q)).
      + transitivity (((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q *
                       pint_integral (bv_zeros (3 * n + 2 * M + 2 + 2)))%Q).
        * apply qeqT_imp_qeq.
          apply (pint_integral_scale ((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q)
                                     (bv_zeros (3 * n + 2 * M + 2 + 2))).
        * rewrite (qeqT_imp_qeq _ _ (bv_zeros_int0 (3 * n + 2 * M + 2 + 2))). apply Qmult_0_r.
      + apply (pm_qle_wd_r
                 (pint_integral (pint_scale ((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q)
                                            (pei_list (n + 2 * Datatypes.S M) (2 * n + 1))))
                 (((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q *
                   pint_integral (pei_list (n + 2 * Datatypes.S M) (2 * n + 1)))%Q)
                 (pint_integral (pint_scale ((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q)
                                            (bv_zeros (3 * n + 2 * M + 2 + 2))))).
        * apply qeqT_imp_qeq.
          apply (pint_integral_scale ((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q)
                                     (pei_list (n + 2 * Datatypes.S M) (2 * n + 1))).
        * apply (pm_scale_mono ((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q)
                   (bv_zeros (3 * n + 2 * M + 2 + 2))
                   (pei_list (n + 2 * Datatypes.S M) (2 * n + 1))).
          -- apply bv_c_pos_le.
          -- apply (pm_qle_wd_l 0%Q _ _).
             ++ apply Qeq_sym. exact (qeqT_imp_qeq _ _ (bv_zeros_int0 (3 * n + 2 * M + 2 + 2))).
             ++ apply bv_pos_cint. }
  (* Middle step Hmove: the integral of bv_zeros plus bv_pad (bv_carrier n M) *)
  (* equals pint_integral (bv_carrier n M).                                   *)
  assert (Hmove : pint_integral (pint_add (bv_zeros (3 * n + 2 * M + 2 + 2))
                                          (bv_pad (bv_carrier n M)))
                 == pint_integral (bv_carrier n M)).
  { assert (HLz : length (bv_zeros (3 * n + 2 * M + 2 + 2))
                  = length (bv_pad (bv_carrier n M))).
    { pose proof (RealSetoid.Id_eq _ _
            (bv_zeros_length (3 * n + 2 * M + 2 + 2))) as H1.
      pose proof (RealSetoid.Id_eq _ _ (bv_pad_length (bv_carrier n M))) as H2.
      pose proof (RealSetoid.Id_eq _ _ (bv_carrier_length n M)) as H3.
      lia. }
    rewrite (qeqT_imp_qeq _ _ (pint_integral_add _ _ HLz)).
    rewrite (qeqT_imp_qeq _ _ (bv_zeros_int0 (3 * n + 2 * M + 2 + 2))).
    rewrite (qeqT_imp_qeq _ _ (bv_pad_int (bv_carrier n M))).
    ring. }
  apply (pm_qle_wd_l
           (pint_integral (pint_add (bv_zeros (3 * n + 2 * M + 2 + 2))
                                    (bv_pad (bv_carrier n M))))
           (pint_integral (bv_carrier n M))
           (pint_integral (pint_add
                (pint_scale ((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q)
                            (pei_list (n + 2 * Datatypes.S M) (2 * n + 1)))
                (bv_pad (bv_carrier n M))))).
  - exact Hmove.
  - apply (pm_add_mono (bv_zeros (3 * n + 2 * M + 2 + 2))
             (pint_scale ((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q)
                         (pei_list (n + 2 * Datatypes.S M) (2 * n + 1)))
             (bv_pad (bv_carrier n M)) (bv_pad (bv_carrier n M))).
    + exact HId1.
    + exact HId2.
    + apply (pm_qle_wd_l 0%Q _ _).
      * apply Qeq_sym. exact (qeqT_imp_qeq _ _ (bv_zeros_int0 (3 * n + 2 * M + 2 + 2))).
      * exact HleX.
    + apply qleT'_refl.
Qed.

(* bv_sum_upto_pos: the partial sum is strictly positive (induction on M; via *)
(* bv_term_pos and pei_lt_le_plus)                                            *)
Lemma bv_sum_upto_pos : forall n M : nat,
  QltT 0 (sum_upto (Datatypes.S M) (fun m : nat => bv_term n m)).
Proof.
  intros n. induction M as [| m IH].
  - change (sum_upto (Datatypes.S 0) (fun m0 : nat => bv_term n m0))
      with (0 + bv_term n 0)%Q.
    apply (pei_qeq_lt (bv_term n 0) (0 + bv_term n 0)%Q 0%Q).
    + apply qeq_imp_qeqT. ring.
    + exact (bv_term_pos n 0).
  - change (sum_upto (Datatypes.S (Datatypes.S m)) (fun m0 : nat => bv_term n m0))
      with (sum_upto (Datatypes.S m) (fun m0 : nat => bv_term n m0)
              + bv_term n (Datatypes.S m))%Q.
    apply pei_lt_le_plus.
    + exact IH.
    + apply Qle_to_QleT'. apply Qlt_le_weak. apply QltT_to_Qlt. apply bv_term_pos.
Qed.

(** bv_sum_pos: the truncated integral is strictly positive -- switch to the  *)
(* partial sum via bv_carrier_value, then apply bv_sum_upto_pos.              *)
Theorem bv_sum_pos : forall n M : nat,
  QltT 0 (pint_integral (bv_carrier n M)).
Proof.
  intros n M.
  apply (pei_qeq_lt (sum_upto (Datatypes.S M) (fun m : nat => bv_term n m))
                    (pint_integral (bv_carrier n M)) 0%Q).
  - apply qeq_imp_qeqT. apply Qeq_sym.
    exact (qeqT_imp_qeq _ _ (bv_carrier_value n M)).
  - exact (bv_sum_upto_pos n M).
Qed.

(* ============================================================ *)
(* Sec D. ln2 coefficient discrete kernel: bv_delannoy_eq_qtilde              *)
(*   (ascending Delannoy sum == q~_n)                                         *)
(*   bv_D_asc n == sum_{a<=n} C(n,a)^2 * 2^a (order adjusted via bk_psd_ext,  *)
(*   bk_Qn_sym); coefficient identity: [u^n](u-1)^n(2-u)^n =                  *)
(*   sum_{a+b=n} C(n,a)C(n,b)2^{n-b}(-1)^{n-a+b}; taking b=n-a the sign       *)
(*   (-1)^{2n-2a}=1, hence = sum_a C(n,a)^2 2^a = D_n = q~_n.                 *)
(* ============================================================ *)

Definition bv_D_asc (n : nat) : nat :=
  bk_psd (fun k => bkC n (n - k) * bkC n (n - k)) (Datatypes.S n).

Theorem bv_delannoy_eq_qtilde : forall n : nat,
  QeqT ((Z.of_nat (bv_D_asc n) # 1)%Q) ((Z.of_nat (bk_Qn_qtilde n) # 1)%Q).
Proof.
  intro n. apply qeq_imp_qeqT. unfold bv_D_asc.
  assert (H : Id (bk_psd (fun k => bkC n (n - k) * bkC n (n - k)) (Datatypes.S n))
                 (bk_psd (fun k => bkC n k * bkC n k) (Datatypes.S n))).
  { apply bk_psd_ext. intros k Hk.
    assert (Hle : k <= n) by (pose proof (NatLe_drop _ _ Hk); lia).
    pose proof (RealSetoid.Id_eq _ _ (bk_Qn_sym n k (NatLe_lift _ _ Hle))) as Hq.
    rewrite <- Hq. reflexivity. }
  pose proof (RealSetoid.Id_eq _ _ H) as Hp.
  rewrite Hp. reflexivity.
Qed.

(* ============================================================ *)
(* Sec E. Numerator closed form bv_p (Laurent coefficient signed sum) and     *)
(*   the numerical anchor group                                               *)
(*   p_n = -sum_{j<>n, j<=2n} c_j(2^{j-n}-1)/(j-n) (anchors p: 0, 2, 9, 131/3)*)
(* ============================================================ *)

Fixpoint bv_negpow (k : nat) : Q :=
  match k with
  | 0 => 1%Q
  | Datatypes.S k' => (- bv_negpow k')%Q
  end.

(* Signed powers of 2 (Z exponent) *)
Definition bv_q2 (k : Z) : Q :=
  match Z.leb 0 k with
  | true => q_pow (2 # 1)%Q (Z.to_nat k)
  | false => 1%Q / q_pow (2 # 1)%Q (Z.to_nat (Z.opp k))
  end.

(* Laurent coefficient c_j = (-1)^{n+j} *                                     *)
(* sum_{a<=j, a<=n, j-a<=n} C(n,a)C(n,j-a)2^{n-(j-a)}                         *)
Definition bv_c (n j : nat) : Q :=
  bv_negpow (n + j) *
  bk_psQ (fun a : nat =>
            if andb (Nat.leb a n) (Nat.leb (j - a) n)
            then ((Z.of_nat (bkC n a * bkC n (j - a)) # 1) *
                  q_pow (2 # 1)%Q (n - (j - a)))%Q
            else 0%Q)
         (Datatypes.S j) 1%Q.

Definition bv_p (n : nat) : Q :=
  (- bk_psQ (fun j : nat =>
               if Nat.eqb j n then 0%Q
               else (bv_c n j *
                     ((bv_q2 (Z.of_nat j - Z.of_nat n)%Z - 1%Q) /
                      ((Z.of_nat j - Z.of_nat n)%Z # 1))%Q))
            (Datatypes.S (2 * n)) 1%Q)%Q.

(* True-normalized approximant x_n := p_n/q~_n (shape: no 2-power factor) *)
Definition bv_x (n : nat) : Q := bv_p n / (Z.of_nat (bk_Qn_qtilde n) # 1)%Q.

(* bv_x2pow: the 2-power normalized form x''_n := p_n/(2^n q~_n), incompatible *)
(* with the true-normalized form (see bv_x2pow_sep1)                           *)
Definition bv_x2pow (n : nat) : Q :=
  bv_p n / (q_pow (2 # 1)%Q n * (Z.of_nat (bk_Qn_qtilde n) # 1))%Q.

(* ---- Numerical anchor group (each anchor decided exactly by vm_compute) ---- *)

Theorem bv_q1_anchor : QeqT ((Z.of_nat (bk_Qn_qtilde 1) # 1)%Q) (3 # 1)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem bv_c11_anchor : QeqT (bv_c 1 1) (3 # 1)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem bv_c22_anchor : QeqT (bv_c 2 2) (13 # 1)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem bv_c33_anchor : QeqT (bv_c 3 3) (63 # 1)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem bv_p0_anchor : QeqT (bv_p 0) 0%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem bv_p1_anchor : QeqT (bv_p 1) (2 # 1)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem bv_p2_anchor : QeqT (bv_p 2) (9 # 1)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem bv_p3_anchor : QeqT (bv_p 3) (131 # 3)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem bv_x0_anchor : QeqT (bv_x 0) 0%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem bv_x1_anchor : QeqT (bv_x 1) (2 # 3)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem bv_x2_anchor : QeqT (bv_x 2) (9 # 13)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

(* Cross-variant check: bv_p 2 == 9, consistent with the original variant     *)
(* relation r_2 == 2^3 * p_2 == 72.                                           *)
Theorem bv_cross2_anchor : QeqT ((bv_p 2 * (Z.of_nat 8 # 1))%Q) (72 # 1)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

(** bv_x2pow_sep1: separation witness -- bv_x2pow 1 == 1/3 < 2/3 == bv_x 1    *)
(* (QltT, Set face).                                                          *)
Theorem bv_x2pow_sep1 : QltT (bv_x2pow 1) (bv_x 1).
Proof. vm_compute. reflexivity. Qed.

(* ============================================================ *)
(* Assumption audit: the Print Assumptions outputs below must be              *)
(* zero-dependency (closure recheck).                                         *)
(* ============================================================ *)

Print Assumptions bv_delannoy_eq_qtilde.
Print Assumptions bv_term_pos.
Print Assumptions bv_carrier_eval.
Print Assumptions bv_carrier_value.
Print Assumptions bv_sum_mono.
Print Assumptions bv_sum_pos.
Print Assumptions bv_p3_anchor.
Print Assumptions bv_x2pow_sep1.
