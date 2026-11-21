(* ========================================================================== *)
(* PsQReindex.v -- coefficient reindexing and decay lemmas for the Beukers    *)
(*   variant series, carried on the rational layer.                           *)
(*                                                                            *)
(* Mission. The base-change identity rx_psQ_reindex (the rising-power psQ     *)
(*   sum with reversed index against the falling-power form, for general n),  *)
(*   the diagonal-coefficient main piece rx_bv_c_diag (bv_c n n == q~_n for   *)
(*   general n, as a QeqT carrier), the term-ratio cross-decay chain          *)
(*   rx_bkC_ratio / rx_decay_nat / rx_term_decayQ giving a constructive       *)
(*   Q-layer monotone decrease of the partial-sum terms bv_term, and the      *)
(*   numeric anchors rx_qtilde3_anchor / rx_c33_qtilde3 /                     *)
(*   rx_term_decay_anchor.                                                    *)
(* Dependencies. S01_BaseRing, S02_CauchyComplete, S03_QExp,                  *)
(*   S07_RealSetoidExpLog (Id/eq conversion source, per BeukersIdentity),     *)
(*   PadeErrorIntegral, BeukersLists, BeukersVariant;                         *)
(*   Stdlib QArith, Lists.List, Arith, ZArith, Lia.                           *)
(* References. Delannoy-number and Pade-approximation coefficient identities  *)
(*   (combinatorics).                                                         *)
(* Constructivity. Every statement face rides a Set-layer carrier: QeqT for   *)
(*   rational equality, QltT/QleT' for the strict/non-strict rational order,  *)
(*   Id for natural equality and NatLe for the natural order; internal        *)
(*   reasoning may use propositional faces with the extracted information     *)
(*   preserved by the carriers. No axioms, no classical logic. All pieces     *)
(*   end Defined (transparent), so the certificate data stays extractable.    *)
(* Build. coqc -Q . "" PsQReindex.v over one flat -Q world root, under the    *)
(*   cpu_guard wrapper.                                                       *)
(* ========================================================================== *)

From Stdlib Require Import QArith.QArith Lists.List Arith.Arith ZArith.ZArith Lia.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import PadeErrorIntegral BeukersLists BeukersVariant.

(* QArith leaks Q_scope (bare numerals would parse as Q constructors); reopen
   nat first so the counting arguments below read as natural numbers. *)
Open Scope nat_scope.

(* ============================================================ *)
(* Section A. bk_psQ toolkit: pointwise extension / head        *)
(*   stripping / common-factor extraction.                      *)
(* ============================================================ *)

(* Pointwise rational equality below the window bound implies equality of
   the windowed sums (k < N is carried as NatLe (S k) N). *)
Lemma rx_psQ_ext_lt : forall (N : nat) (f g : nat -> Q) (z : Q),
  (forall k : nat, NatLe (Datatypes.S k) N -> QeqT (f k) (g k)) ->
  QeqT (bk_psQ f N z) (bk_psQ g N z).
Proof.
  intros N. induction N as [| N IH]; intros f g z H.
  - apply qeq_imp_qeqT. reflexivity.
  - cbn [bk_psQ].
    apply qeq_imp_qeqT.
    assert (HIHp : forall k : nat, NatLe (Datatypes.S k) N -> QeqT (f k) (g k)).
    { intros k Hk. apply H. apply NatLe_lift.
      apply (Nat.le_le_succ_r (Datatypes.S k) N). apply (NatLe_drop _ _ Hk). }
    rewrite (qeqT_imp_qeq _ _ (IH f g z HIHp)).
    rewrite (qeqT_imp_qeq _ _ (H N (NatLe_refl (Datatypes.S N)))).
    reflexivity.
Defined.

(* Head stripping: bk_psQ g (S N) z == g 0 + z * sum_{k<N} g (S k) * z^k. *)
Lemma rx_psQ_shift : forall (N : nat) (g : nat -> Q) (z : Q),
  QeqT (bk_psQ g (Datatypes.S N) z)
       (g 0 + z * bk_psQ (fun k : nat => g (Datatypes.S k)) N z).
Proof.
  intros N. induction N as [| N IH]; intros g z.
  - apply qeq_imp_qeqT. cbn [bk_psQ q_pow]. ring.
  - apply qeq_imp_qeqT.
    change (bk_psQ g (Datatypes.S (Datatypes.S N)) z)
      with ((bk_psQ g (Datatypes.S N) z
              + g (Datatypes.S N) * q_pow z (Datatypes.S N))%Q).
    change (bk_psQ (fun k : nat => g (Datatypes.S k)) (Datatypes.S N) z)
      with ((bk_psQ (fun k : nat => g (Datatypes.S k)) N z
              + g (Datatypes.S N) * q_pow z N)%Q).
    change (q_pow z (Datatypes.S N)) with (z * q_pow z N)%Q.
    rewrite (qeqT_imp_qeq _ _ (IH g z)). ring.
Defined.

(* Common-factor extraction: sum c * h(k) * z^k == c * sum h(k) * z^k. *)
Lemma rx_psQ_scale : forall (N : nat) (c : Q) (h : nat -> Q) (z : Q),
  QeqT (bk_psQ (fun k : nat => (c * h k)%Q) N z) (c * bk_psQ h N z)%Q.
Proof.
  intros N. induction N as [| N IH]; intros c h z.
  - apply qeq_imp_qeqT. cbn [bk_psQ]. ring.
  - apply qeq_imp_qeqT.
    change (bk_psQ (fun k : nat => (c * h k)%Q) (Datatypes.S N) z)
      with ((bk_psQ (fun k : nat => (c * h k)%Q) N z
              + c * h N * q_pow z N)%Q).
    change (bk_psQ h (Datatypes.S N) z)
      with ((bk_psQ h N z + h N * q_pow z N)%Q).
    change (q_pow z (Datatypes.S N)) with (z * q_pow z N)%Q.
    rewrite (qeqT_imp_qeq _ _ (IH c h z)). ring.
Defined.

(* ============================================================ *)
(* Section B. Main piece 1: the reindex base-change lemma       *)
(*   (rising-power index reversal).                             *)
(* ============================================================ *)

Theorem rx_psQ_reindex : forall (n : nat) (g : nat -> Q),
  QeqT (bk_psQ (fun k : nat => (g (Nat.sub n k) * q_pow (2 # 1)%Q k)%Q)
               (Datatypes.S n) 1%Q)
       (bk_psQ (fun k : nat => (g k * q_pow (2 # 1)%Q (Nat.sub n k))%Q)
               (Datatypes.S n) 1%Q).
Proof.
  intros n. induction n as [| n IH]; intros g.
  - apply qeq_imp_qeqT. cbn [bk_psQ q_pow Nat.sub]. ring.
  - apply qeq_imp_qeqT.
    (* Left side: head stripping -- g (S n) + 2 * sum_{k<=n} g (n-k) * 2^k. *)
    rewrite (qeqT_imp_qeq _ _
               (rx_psQ_shift (Datatypes.S n)
                  (fun k : nat =>
                     (g (Nat.sub (Datatypes.S n) k) * q_pow (2 # 1)%Q k)%Q)
                  1%Q)).
    cbv beta.
    replace (Nat.sub (Datatypes.S n) 0) with (Datatypes.S n) by lia.
    replace (q_pow (2 # 1)%Q 0) with 1%Q by reflexivity.
    assert (Hb : bk_psQ (fun k : nat =>
                           (g (Nat.sub (Datatypes.S n) (Datatypes.S k))
                              * q_pow (2 # 1)%Q (Datatypes.S k))%Q)
                        (Datatypes.S n) 1%Q
                 == (2 # 1)%Q * bk_psQ (fun k : nat =>
                                           (g (Nat.sub n k) * q_pow (2 # 1)%Q k)%Q)
                                       (Datatypes.S n) 1%Q).
    { transitivity (bk_psQ (fun k : nat =>
                              ((2 # 1)%Q * (g (Nat.sub n k) * q_pow (2 # 1)%Q k))%Q)
                           (Datatypes.S n) 1%Q).
      - apply qeqT_imp_qeq. apply rx_psQ_ext_lt. intros k Hk. apply qeq_imp_qeqT.
        replace (Nat.sub (Datatypes.S n) (Datatypes.S k)) with (n - k) by lia.
        cbn [q_pow]. ring.
      - apply qeqT_imp_qeq. apply rx_psQ_scale. }
    rewrite Hb. rewrite (qeqT_imp_qeq _ _ (IH g)).
    (* Right side: tail stripping -- 2 * sum_{k<=n} g(k) * 2^(n-k) + g (S n). *)
    assert (Hrhs : bk_psQ (fun k : nat =>
                             (g k * q_pow (2 # 1)%Q (Nat.sub (Datatypes.S n) k))%Q)
                          (Datatypes.S (Datatypes.S n)) 1%Q
                   == (2 # 1)%Q * bk_psQ (fun k : nat =>
                                             (g k * q_pow (2 # 1)%Q (Nat.sub n k))%Q)
                                         (Datatypes.S n) 1%Q
                      + g (Datatypes.S n)).
    { change (bk_psQ (fun k : nat =>
                        (g k * q_pow (2 # 1)%Q (Nat.sub (Datatypes.S n) k))%Q)
                     (Datatypes.S (Datatypes.S n)) 1%Q)
        with ((bk_psQ (fun k : nat =>
                         (g k * q_pow (2 # 1)%Q (Nat.sub (Datatypes.S n) k))%Q)
                     (Datatypes.S n) 1%Q
              + g (Datatypes.S n)
                   * q_pow (2 # 1)%Q (Nat.sub (Datatypes.S n) (Datatypes.S n))
                   * q_pow (1 # 1)%Q (Datatypes.S n))%Q).
      replace (Nat.sub (Datatypes.S n) (Datatypes.S n)) with 0%nat by lia.
      cbn [q_pow].
      rewrite (qeqT_imp_qeq _ _ (bk_q_pow_one n)).
      assert (Hc : bk_psQ (fun k : nat =>
                             (g k * q_pow (2 # 1)%Q (Nat.sub (Datatypes.S n) k))%Q)
                          (Datatypes.S n) 1%Q
                   == (2 # 1)%Q * bk_psQ (fun k : nat =>
                                             (g k * q_pow (2 # 1)%Q (Nat.sub n k))%Q)
                                         (Datatypes.S n) 1%Q).
      { transitivity (bk_psQ (fun k : nat =>
                                ((2 # 1)%Q * (g k * q_pow (2 # 1)%Q (n - k)))%Q)
                             (Datatypes.S n) 1%Q).
        - apply qeqT_imp_qeq. apply rx_psQ_ext_lt. intros k Hk. apply qeq_imp_qeqT.
          pose proof (NatLe_drop _ _ Hk) as Hk'.
          replace (Nat.sub (Datatypes.S n) k) with (Datatypes.S (n - k)) by lia.
          cbn [q_pow]. ring.
        - apply qeqT_imp_qeq. apply rx_psQ_scale. }
      rewrite Hc. ring. }
    rewrite Hrhs. ring.
Defined.

(* ============================================================ *)
(* Section C. Corollary of main piece 1: bv_c n n == q~_n       *)
(*   (general n, QeqT Set face).                                *)
(* ============================================================ *)

Lemma rx_negpow_double : forall k : nat, QeqT (bv_negpow (k + k)) 1%Q.
Proof.
  intro k. induction k as [| k IH].
  - apply qeq_imp_qeqT. reflexivity.
  - apply qeq_imp_qeqT.
    replace (Datatypes.S k + Datatypes.S k)
      with (Datatypes.S (Datatypes.S (k + k))) by lia.
    cbn [bv_negpow]. rewrite (qeqT_imp_qeq _ _ IH). ring.
Defined.

(* The Q-image of the falling-power nat sum is the rising-power weighted
   bk_psQ (the reversed variant of bk_half_psd). *)
Lemma rx_psdQ_desc : forall (n : nat) (h : nat -> nat),
  QeqT ((Z.of_nat (bk_psd h (Datatypes.S n)) # 1)%Q)
       (bk_psQ (fun k : nat =>
                  ((Z.of_nat (h k) # 1) * q_pow (2 # 1)%Q (n - k))%Q)
            (Datatypes.S n) 1%Q).
Proof.
  intros n. induction n as [| n IH]; intros h.
  - apply qeq_imp_qeqT.
    cbn [bk_psd bk_psQ q_pow Nat.sub].
    replace (2 * 0)%nat with 0%nat by lia.
    cbn [Nat.add]. ring.
  - apply qeq_imp_qeqT.
    change (Z.of_nat (bk_psd h (Datatypes.S (Datatypes.S n))) # 1)
      with ((Z.of_nat (2 * bk_psd h (Datatypes.S n) + h (Datatypes.S n)) # 1))%Q.
    change (bk_psQ (fun k : nat =>
                      ((Z.of_nat (h k) # 1) * q_pow (2 # 1)%Q (Datatypes.S n - k))%Q)
                 (Datatypes.S (Datatypes.S n)) 1%Q)
      with ((bk_psQ (fun k : nat =>
                       ((Z.of_nat (h k) # 1) * q_pow (2 # 1)%Q (Datatypes.S n - k))%Q)
                   (Datatypes.S n) 1%Q
            + (Z.of_nat (h (Datatypes.S n)) # 1)
                 * q_pow (2 # 1)%Q (Datatypes.S n - Datatypes.S n)
                 * q_pow (1 # 1)%Q (Datatypes.S n))%Q).
    replace (Datatypes.S n - Datatypes.S n) with 0%nat by lia.
    cbn [q_pow].
    rewrite (qeqT_imp_qeq _ _ (bk_q_pow_one n)).
    repeat rewrite Qmult_1_r.
    assert (Hc : bk_psQ (fun k : nat =>
                           ((Z.of_nat (h k) # 1)
                              * q_pow (2 # 1)%Q (Datatypes.S n - k))%Q)
                        (Datatypes.S n) 1%Q
                 == (2 # 1)%Q * bk_psQ (fun k : nat =>
                                           ((Z.of_nat (h k) # 1)
                                              * q_pow (2 # 1)%Q (n - k))%Q)
                                       (Datatypes.S n) 1%Q).
    { transitivity (bk_psQ (fun k : nat =>
                              ((2 # 1)%Q
                                 * ((Z.of_nat (h k) # 1)
                                    * q_pow (2 # 1)%Q (n - k)))%Q)
                           (Datatypes.S n) 1%Q).
      - apply qeqT_imp_qeq. apply rx_psQ_ext_lt. intros k Hk. apply qeq_imp_qeqT.
        pose proof (NatLe_drop _ _ Hk) as Hk'.
        replace (Datatypes.S n - k) with (Datatypes.S (n - k)) by lia.
        cbn [q_pow]. ring.
      - apply qeqT_imp_qeq. apply rx_psQ_scale. }
    rewrite Hc. rewrite <- (qeqT_imp_qeq _ _ (IH h)).
    replace (2 # 1)%Q with (Z.of_nat 2 # 1)%Q by reflexivity.
    rewrite (qeqT_imp_qeq _ _ (bk_Qmul_nat 2 (bk_psd h (Datatypes.S n)))).
    symmetry.
    exact (qeqT_imp_qeq _ _
             (bk_Qadd_nat (2 * bk_psd h (Datatypes.S n)) (h (Datatypes.S n)))).
Defined.

(* Main corollary: the Laurent diagonal coefficient bv_c n n == q~_n. *)
Theorem rx_bv_c_diag : forall n : nat,
  QeqT (bv_c n n) ((Z.of_nat (bk_Qn_qtilde n) # 1)%Q).
Proof.
  intro n. apply qeq_imp_qeqT. unfold bv_c.
  assert (Hnp : QeqT (bv_negpow (n + n)) 1%Q) by apply rx_negpow_double.
  rewrite (qeqT_imp_qeq _ _ Hnp). rewrite Qmult_1_l.
  (* Pointwise normalization: the gate is true, the 2-power index n-(n-a)
     folds to a, and the product order is restored by commutativity. *)
  transitivity (bk_psQ (fun k : nat =>
                          ((Z.of_nat (bkC n (n - k) * bkC n k) # 1)
                             * q_pow (2 # 1)%Q k)%Q)
                       (Datatypes.S n) 1%Q).
  { apply qeqT_imp_qeq. apply rx_psQ_ext_lt. intros a Ha. cbv beta.
    apply qeq_imp_qeqT.
    pose proof (NatLe_drop _ _ Ha) as Ha0.
    assert (Ha1 : Nat.leb a n = true) by (apply Nat.leb_le; lia).
    assert (Ha2 : Nat.leb (n - a) n = true) by (apply Nat.leb_le; lia).
    rewrite Ha1, Ha2. cbn [andb].
    replace (n - (n - a)) with a by lia.
    replace (bkC n a * bkC n (n - a)) with (bkC n (n - a) * bkC n a)
      by (rewrite Nat.mul_comm; reflexivity).
    reflexivity. }
  (* Reindex: rising-power index reversal (the lambda shape matches the
     reindex lemma statement). *)
  transitivity (bk_psQ (fun k : nat =>
                          ((fun i : nat =>
                              (Z.of_nat (bkC n i * bkC n (n - i)) # 1)%Q)
                             (Nat.sub n k) * q_pow (2 # 1)%Q k)%Q)
                       (Datatypes.S n) 1%Q).
  { apply qeqT_imp_qeq. apply rx_psQ_ext_lt. intros k Hk. cbv beta.
    apply qeq_imp_qeqT.
    pose proof (NatLe_drop _ _ Hk) as Hk'.
    replace (n - (n - k)) with k by lia. reflexivity. }
  assert (Hri := rx_psQ_reindex n
                   (fun i : nat => (Z.of_nat (bkC n i * bkC n (n - i)) # 1)%Q)).
  rewrite (qeqT_imp_qeq _ _ Hri).
  (* Falling-power nat sum carrier + symmetric placement == q~_n. *)
  transitivity (Z.of_nat (bk_psd (fun k : nat => bkC n k * bkC n (n - k))
                                  (Datatypes.S n)) # 1).
  { symmetry. apply qeqT_imp_qeq.
    apply (rx_psdQ_desc n (fun i : nat => bkC n i * bkC n (n - i))). }
  assert (Hext : Id (bk_psd (fun k : nat => bkC n k * bkC n (n - k)) (Datatypes.S n))
                   (bk_psd (fun k : nat => bkC n k * bkC n k) (Datatypes.S n))).
  { apply bk_psd_ext. intros k Hk. cbv beta.
    assert (Hkle : NatLe k n) by (pose proof (NatLe_drop _ _ Hk); apply NatLe_lift; lia).
    rewrite <- (RealSetoid.Id_eq _ _ (bk_Qn_sym n k Hkle)).
    reflexivity. }
  rewrite (RealSetoid.Id_eq _ _ Hext). unfold bk_Qn_qtilde. reflexivity.
Defined.

(* Numeric anchor: q~_3 == 63 (cross-checks the diagonal at n = 3). *)
Theorem rx_qtilde3_anchor : QeqT ((Z.of_nat (bk_Qn_qtilde 3) # 1)%Q) (63 # 1)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Defined.

(* Diagonal numeric anchor: bv_c 3 3 == q~_3 (instance of the general piece). *)
Theorem rx_c33_qtilde3 : QeqT (bv_c 3 3) ((Z.of_nat (bk_Qn_qtilde 3) # 1)%Q).
Proof. apply rx_bv_c_diag. Defined.

(* ============================================================ *)
(* Section D. Piece 2: the term-ratio cross-decay chain (the    *)
(*   machine carrier for the convergence-bridge strictness).    *)
(* ============================================================ *)

(* Zeroth column C(j, 0) = 1. *)
Lemma rx_bkC_col0 : forall j : nat, Id (bkC j 0) 1.
Proof.
  intros j. destruct j as [| j'].
  - apply RealSetoid.eq_Id. reflexivity.
  - apply RealSetoid.eq_Id. reflexivity.
Defined.

(* Sub-diagonal C(S j, j) = S j. *)
Lemma rx_bkC_subdiag : forall j : nat, Id (bkC (Datatypes.S j) j) (Datatypes.S j).
Proof.
  intros j. induction j as [| j IH].
  - apply RealSetoid.eq_Id. reflexivity.
  - apply RealSetoid.eq_Id.
    change (bkC (Datatypes.S (Datatypes.S j)) (Datatypes.S j))
      with (bkC (Datatypes.S j) j + bkC (Datatypes.S j) (Datatypes.S j)).
    rewrite (RealSetoid.Id_eq _ _ (bkC_diag (Datatypes.S j))).
    rewrite (RealSetoid.Id_eq _ _ IH). lia.
Defined.

(* Second column C(j, 1) = j. *)
Lemma rx_bkC_row1 : forall j : nat, Id (bkC j 1) j.
Proof.
  intros j. induction j as [| j IH].
  - apply RealSetoid.eq_Id. reflexivity.
  - apply RealSetoid.eq_Id.
    change (bkC (Datatypes.S j) 1) with (bkC j 0 + bkC j 1).
    rewrite (RealSetoid.Id_eq _ _ (rx_bkC_col0 j)).
    rewrite (RealSetoid.Id_eq _ _ IH). lia.
Defined.

(* Absorption identity: C(j,k) * (j-k) == C(j,k+1) * (k+1) for k+1 <= j. *)
Lemma rx_bkC_absorb : forall j k : nat,
  NatLe (Datatypes.S k) j ->
  Id (bkC j k * (j - k)) (bkC j (Datatypes.S k) * Datatypes.S k).
Proof.
  induction j as [| j IH]; intros k Hk.
  - pose proof (NatLe_drop _ _ Hk) as Hk'. apply RealSetoid.eq_Id. lia.
  - destruct k as [| k'].
    + apply RealSetoid.eq_Id.
      change (bkC (Datatypes.S j) 0) with 1%nat.
      change (bkC (Datatypes.S j) (Datatypes.S 0)) with (bkC j 0 + bkC j 1).
      change (Datatypes.S j - 0) with (Datatypes.S j).
      rewrite (RealSetoid.Id_eq _ _ (rx_bkC_col0 j)).
      rewrite (RealSetoid.Id_eq _ _ (rx_bkC_row1 j)). lia.
    + apply RealSetoid.eq_Id. cbn [bkC Nat.sub].
      destruct (le_lt_dec (Datatypes.S (Datatypes.S k')) j) as [Hjj | Hjj].
      * assert (IH1 := IH k' (NatLe_lift (Datatypes.S k') j ltac:(lia))).
        assert (IH2 := IH (Datatypes.S k')
                          (NatLe_lift (Datatypes.S (Datatypes.S k')) j ltac:(lia))).
        assert (HspL : (bkC j k' + bkC j (Datatypes.S k')) * (j - k')
                     = bkC j k' * (j - k') + bkC j (Datatypes.S k') * (j - k')) by ring.
        assert (HspR : (bkC j (Datatypes.S k') + bkC j (Datatypes.S (Datatypes.S k')))
                         * Datatypes.S (Datatypes.S k')
                     = bkC j (Datatypes.S k') * Datatypes.S (Datatypes.S k')
                       + bkC j (Datatypes.S (Datatypes.S k'))
                         * Datatypes.S (Datatypes.S k')) by ring.
        rewrite HspL, (RealSetoid.Id_eq _ _ IH1), HspR,
                <- (RealSetoid.Id_eq _ _ IH2).
        rewrite <- (Nat.mul_add_distr_l (bkC j (Datatypes.S k'))
                      (Datatypes.S k') (j - k')).
        replace (Datatypes.S k' + (j - k')) with (Datatypes.S j) by lia.
        rewrite <- (Nat.mul_add_distr_l (bkC j (Datatypes.S k'))
                      (Datatypes.S (Datatypes.S k')) (j - Datatypes.S k')).
        replace (Datatypes.S (Datatypes.S k') + (j - Datatypes.S k'))
          with (Datatypes.S j) by lia.
        reflexivity.
      * pose proof (NatLe_drop _ _ Hk) as Hk''.
        assert (Hk'j : Datatypes.S k' = j) by lia. subst j.
        rewrite (RealSetoid.Id_eq _ _ (rx_bkC_subdiag k')).
        rewrite (RealSetoid.Id_eq _ _ (bkC_diag (Datatypes.S k'))).
        rewrite (RealSetoid.Id_eq _ _
                   (bkC_out (Datatypes.S k') (Datatypes.S (Datatypes.S k'))
                              (NatLe_refl (Datatypes.S (Datatypes.S k'))))).
        replace (Datatypes.S k' - k') with 1%nat by lia.
        lia.
Defined.

(* Ratio identity: C(j+1,k) * (j+1-k) == C(j,k) * (j+1) for k <= j. *)
Lemma rx_bkC_ratio : forall j k : nat,
  NatLe k j ->
  Id (bkC (Datatypes.S j) k * (Datatypes.S j - k)) (bkC j k * Datatypes.S j).
Proof.
  induction j as [| j IH]; intros k Hk.
  - pose proof (NatLe_drop _ _ Hk) as Hk'.
    assert (Hk0 : k = 0) by lia. subst k.
    apply RealSetoid.eq_Id. reflexivity.
  - destruct k as [| k'].
    + apply RealSetoid.eq_Id. reflexivity.
    + apply RealSetoid.eq_Id.
      change (bkC (Datatypes.S (Datatypes.S j)) (Datatypes.S k'))
        with (bkC (Datatypes.S j) k' + bkC (Datatypes.S j) (Datatypes.S k')).
      change (Datatypes.S (Datatypes.S j) - Datatypes.S k')
        with (Datatypes.S j - k').
      destruct (le_lt_dec (Datatypes.S k') j) as [Hle | Hlt].
      * assert (Hab := rx_bkC_absorb j k' (NatLe_lift _ _ Hle)).
        assert (IH1 := IH k' (NatLe_lift k' j ltac:(lia))).
        assert (Hsp : (bkC (Datatypes.S j) k' + bkC (Datatypes.S j) (Datatypes.S k'))
                        * (Datatypes.S j - k')
                    = bkC (Datatypes.S j) k' * (Datatypes.S j - k')
                      + bkC (Datatypes.S j) (Datatypes.S k') * (Datatypes.S j - k')) by ring.
        rewrite Hsp, (RealSetoid.Id_eq _ _ IH1).
        assert (HB : bkC (Datatypes.S j) (Datatypes.S k')
                   = bkC j k' + bkC j (Datatypes.S k')) by reflexivity.
        rewrite HB.
        rewrite (Nat.mul_add_distr_r (bkC j k') (bkC j (Datatypes.S k'))
                   (Datatypes.S j - k')).
        rewrite (Nat.mul_add_distr_r (bkC j k') (bkC j (Datatypes.S k'))
                   (Datatypes.S (Datatypes.S j))).
        replace (Datatypes.S j - k') with (Datatypes.S (j - k')) by lia.
        remember (Nat.sub j k') as d eqn:Hddef.
        assert (Hdrel : Datatypes.S d + k' = Datatypes.S k' + d) by lia.
        replace (Datatypes.S (Datatypes.S j)) with (Datatypes.S d + Datatypes.S k') by lia.
        replace (Datatypes.S j) with (Datatypes.S d + k') by lia.
        rewrite (Nat.mul_add_distr_l (bkC j k') (Datatypes.S d) k').
        rewrite (Nat.mul_add_distr_l (bkC j (Datatypes.S k'))
                   (Datatypes.S d) (Datatypes.S k')).
        rewrite <- (RealSetoid.Id_eq _ _ Hab).
        nia.
      * pose proof (NatLe_drop _ _ Hk) as Hk''.
        assert (Hkj : k' = j) by lia. subst k'.
        rewrite (RealSetoid.Id_eq _ _ (rx_bkC_subdiag j)).
        rewrite (RealSetoid.Id_eq _ _ (bkC_diag (Datatypes.S j))).
        replace (Datatypes.S j - j) with 1%nat by lia.
        lia.
Defined.

(* Key cubic inequality for the all-positive coefficients (expansion of
   m = n + d; every difference term is positive; ring + lia close it). *)
Lemma rx_key_d : forall n d : nat,
  NatLe ((n + (n + d) + 1) * ((n + 2 * (n + d) + 1) * (n + 2 * (n + d) + 2)))
        (((3 * n + 2 * (n + d) + 3) * (3 * n + 2 * (n + d) + 4)) * ((n + d) + 1)).
Proof.
  intros n d.
  assert (Hexp : (n + (n + d) + 1) * ((n + 2 * (n + d) + 1) * (n + 2 * (n + d) + 2))
                 + (7 * n * n * n + 12 * n * n * d + 4 * n * d * d + 33 * n * n
                    + 36 * n * d + 34 * n + 8 * d * d + 18 * d + 10)
               = ((3 * n + 2 * (n + d) + 3) * (3 * n + 2 * (n + d) + 4))
                 * ((n + d) + 1)) by ring.
  assert (HP : 0 <= (7 * n * n * n + 12 * n * n * d + 4 * n * d * d + 33 * n * n
                     + 36 * n * d + 34 * n + 8 * d * d + 18 * d + 10))
    by apply Nat.le_0_l.
  natle_solve.
Defined.

(* Decay kernel over nat: n <= m implies
   C(n+m+1,n) * (n+2m+1)(n+2m+2) <= C(n+m,n) * (3n+2m+3)(3n+2m+4). *)
Lemma rx_decay_nat : forall n m : nat,
  NatLe n m ->
  NatLe (bkC (Datatypes.S (n + m)) n * ((n + 2 * m + 1) * (n + 2 * m + 2)))
        (bkC (n + m) n * ((3 * n + 2 * m + 3) * (3 * n + 2 * m + 4))).
Proof.
  intros n m Hnm.
  assert (Hr := rx_bkC_ratio (n + m) n (NatLe_lift n (n + m) ltac:(lia))).
  replace (Datatypes.S (n + m) - n) with (m + 1) in Hr by lia.
  replace (Datatypes.S (n + m)) with (n + m + 1) in Hr by lia.
  assert (Hkey : (n + m + 1) * ((n + 2 * m + 1) * (n + 2 * m + 2))
                 <= ((3 * n + 2 * m + 3) * (3 * n + 2 * m + 4)) * (m + 1)).
  { pose proof (NatLe_drop _ _ Hnm) as Hnm'.
    replace m with (n + (m - n)) by lia.
    apply (NatLe_drop _ _ (rx_key_d n (m - n))). }
  assert (HswapL : bkC (Datatypes.S (n + m)) n
                     * ((n + 2 * m + 1) * (n + 2 * m + 2)) * (m + 1)
                 = bkC (Datatypes.S (n + m)) n * (m + 1)
                     * ((n + 2 * m + 1) * (n + 2 * m + 2))) by ring.
  assert (Hstep : bkC (Datatypes.S (n + m)) n
                    * ((n + 2 * m + 1) * (n + 2 * m + 2)) * (m + 1)
                  <= bkC (n + m) n * ((3 * n + 2 * m + 3) * (3 * n + 2 * m + 4))
                       * (m + 1)).
  { rewrite HswapL.
    replace (Datatypes.S (n + m)) with (n + m + 1) by lia.
    rewrite (RealSetoid.Id_eq _ _ Hr).
    rewrite <- (Nat.mul_assoc (bkC (n + m) n) (n + m + 1)
                  ((n + 2 * m + 1) * (n + 2 * m + 2))).
    rewrite <- (Nat.mul_assoc (bkC (n + m) n)
                  ((3 * n + 2 * m + 3) * (3 * n + 2 * m + 4)) (m + 1)).
    apply Nat.mul_le_mono_l. exact Hkey. }
  apply NatLe_lift.
  destruct (le_lt_dec (bkC (Datatypes.S (n + m)) n
                         * ((n + 2 * m + 1) * (n + 2 * m + 2)))
                      (bkC (n + m) n
                         * ((3 * n + 2 * m + 3) * (3 * n + 2 * m + 4))))
    as [Hle | Hlt].
  - exact Hle.
  - exfalso.
    assert (Hlt2 := proj1 (Nat.mul_lt_mono_pos_r (m + 1) _ _ ltac:(lia)) Hlt).
    exact (Nat.lt_irrefl _ (Nat.le_lt_trans _ _ _ Hstep Hlt2)).
Defined.

(* Strict positivity of the image of a positive integer with unit denominator. *)
Lemma rx_Qlt_Z1 : forall z : Z, (0 < z)%Z -> QltT 0 (z # 1)%Q.
Proof.
  intros z Hz. apply Qlt_to_QltT. unfold Qlt. cbn [Qnum Qden].
  rewrite !Z.mul_1_r. exact Hz.
Defined.

(* Decay at the rational layer: n <= m implies bv_term n (S m) <= bv_term n m
   (QleT' Set face). *)
Theorem rx_term_decayQ : forall n m : nat,
  NatLe n m -> QleT' (bv_term n (Datatypes.S m)) (bv_term n m).
Proof.
  intros n m Hnm. apply Qle_to_QleT'.
  assert (HposD : (0 < Z.of_nat (3 * n + 2 * m + 3))%Z) by lia.
  assert (HposE : (0 < Z.of_nat (3 * n + 2 * m + 4))%Z) by lia.
  assert (Hpm : (0 < (1 / (Z.of_nat (3 * n + 2 * m + 3) # 1))
                    * (1 / (Z.of_nat (3 * n + 2 * m + 4) # 1)))%Q).
  { apply Qmult_lt_0_compat.
    - unfold Qdiv. rewrite Qmult_1_l. apply Qinv_lt_0_compat.
        apply (QltT_to_Qlt _ _ (rx_Qlt_Z1 _ HposD)).
    - unfold Qdiv. rewrite Qmult_1_l. apply Qinv_lt_0_compat.
        apply (QltT_to_Qlt _ _ (rx_Qlt_Z1 _ HposE)). }
  assert (Hpm0 : (0 <= (1 / (Z.of_nat (3 * n + 2 * m + 3) # 1))
                      * (1 / (Z.of_nat (3 * n + 2 * m + 4) # 1)))%Q)
    by (apply Qlt_le_weak; exact Hpm).
  assert (HshapeS : bv_term n (Datatypes.S m)
    == ((Z.of_nat (bkC (Datatypes.S (n + m)) n) # 1)
          * ((Z.of_nat (n + 2 * m + 1) # 1) * (Z.of_nat (n + 2 * m + 2) # 1)
               * ((1 / (Z.of_nat (3 * n + 2 * m + 3) # 1))
                  * (1 / (Z.of_nat (3 * n + 2 * m + 4) # 1)))))
          * (q_fact (n + 2 * m) * q_fact (2 * n + 1) / q_fact (3 * n + 2 * m + 2))).
  { unfold bv_term, Qdiv.
    replace (n + Datatypes.S m) with (Datatypes.S (n + m)) by lia.
    replace (n + 2 * Datatypes.S m)
      with (Datatypes.S (Datatypes.S (n + 2 * m))) by lia.
    replace (3 * n + 2 * Datatypes.S m + 2)
      with (Datatypes.S (Datatypes.S (3 * n + 2 * m + 2))) by lia.
    rewrite (qeqT_imp_qeq _ _ (q_fact_succ (Datatypes.S (n + 2 * m)))),
            (qeqT_imp_qeq _ _ (q_fact_succ (n + 2 * m))).
    rewrite (qeqT_imp_qeq _ _ (q_fact_succ (Datatypes.S (3 * n + 2 * m + 2)))),
            (qeqT_imp_qeq _ _ (q_fact_succ (3 * n + 2 * m + 2))).
    rewrite !Qinv_mult_distr.
    replace (Datatypes.S (Datatypes.S (n + 2 * m))) with (n + 2 * m + 2) by lia.
    replace (Datatypes.S (n + 2 * m)) with (n + 2 * m + 1) by lia.
    replace (Datatypes.S (Datatypes.S (3 * n + 2 * m + 2)))
      with (3 * n + 2 * m + 4) by lia.
    replace (Datatypes.S (3 * n + 2 * m + 2)) with (3 * n + 2 * m + 3) by lia.
    ring. }
  assert (HshapeT : bv_term n m
    == (Z.of_nat (bkC (n + m) n) # 1)
         * (q_fact (n + 2 * m) * q_fact (2 * n + 1) / q_fact (3 * n + 2 * m + 2))).
  { unfold bv_term, Qdiv. reflexivity. }
  assert (Hdec1 : (Z.of_nat (bkC (Datatypes.S (n + m)) n) # 1)
                    * ((Z.of_nat (n + 2 * m + 1) # 1)
                       * (Z.of_nat (n + 2 * m + 2) # 1))
                  == (Z.of_nat (bkC (Datatypes.S (n + m)) n
                                   * ((n + 2 * m + 1) * (n + 2 * m + 2))) # 1)).
  { rewrite (qeqT_imp_qeq _ _ (bk_Qmul_nat (n + 2 * m + 1) (n + 2 * m + 2))).
    rewrite (qeqT_imp_qeq _ _
               (bk_Qmul_nat (bkC (Datatypes.S (n + m)) n)
                            ((n + 2 * m + 1) * (n + 2 * m + 2)))).
    reflexivity. }
  assert (Hdec2 : (Z.of_nat (bkC (n + m) n) # 1)
                    * ((Z.of_nat (3 * n + 2 * m + 3) # 1)
                       * (Z.of_nat (3 * n + 2 * m + 4) # 1))
                  == (Z.of_nat (bkC (n + m) n
                                   * ((3 * n + 2 * m + 3) * (3 * n + 2 * m + 4))) # 1)).
  { rewrite (qeqT_imp_qeq _ _ (bk_Qmul_nat (3 * n + 2 * m + 3) (3 * n + 2 * m + 4))).
    rewrite (qeqT_imp_qeq _ _
               (bk_Qmul_nat (bkC (n + m) n)
                            ((3 * n + 2 * m + 3) * (3 * n + 2 * m + 4)))).
    reflexivity. }
  assert (HdecQ : Qle ((Z.of_nat (bkC (Datatypes.S (n + m)) n) # 1)
                         * ((Z.of_nat (n + 2 * m + 1) # 1)
                            * (Z.of_nat (n + 2 * m + 2) # 1)))
                      ((Z.of_nat (bkC (n + m) n) # 1)
                         * ((Z.of_nat (3 * n + 2 * m + 3) # 1)
                            * (Z.of_nat (3 * n + 2 * m + 4) # 1)))).
  { assert (H0q : Qle (Z.of_nat (bkC (Datatypes.S (n + m)) n
                                 * ((n + 2 * m + 1) * (n + 2 * m + 2))) # 1)
                      (Z.of_nat (bkC (n + m) n
                                   * ((3 * n + 2 * m + 3) * (3 * n + 2 * m + 4))) # 1)).
    { apply QleT'_to_Qle.
      exact (bk_Qle_nat
               (bkC (Datatypes.S (n + m)) n * ((n + 2 * m + 1) * (n + 2 * m + 2)))
               (bkC (n + m) n * ((3 * n + 2 * m + 3) * (3 * n + 2 * m + 4)))
               (rx_decay_nat n m Hnm)). }
    rewrite <- Hdec1 in H0q. rewrite <- Hdec2 in H0q. exact H0q. }
  assert (HinvP : ((Z.of_nat (3 * n + 2 * m + 3) # 1)
                     * (Z.of_nat (3 * n + 2 * m + 4) # 1))
                    * ((1 / (Z.of_nat (3 * n + 2 * m + 3) # 1))
                       * (1 / (Z.of_nat (3 * n + 2 * m + 4) # 1)))
                  == 1%Q).
  { unfold Qdiv.
    rewrite !Qmult_1_l.
    rewrite <- (Qinv_mult_distr (Z.of_nat (3 * n + 2 * m + 3) # 1)
                                (Z.of_nat (3 * n + 2 * m + 4) # 1)).
    apply Qmult_inv_r.
    assert (HposAB : Qlt 0 ((Z.of_nat (3 * n + 2 * m + 3) # 1)
                              * (Z.of_nat (3 * n + 2 * m + 4) # 1))).
    { apply Qmult_lt_0_compat.
      - unfold Qlt. cbn [Qnum Qden]. rewrite !Z.mul_1_r. exact HposD.
      - unfold Qlt. cbn [Qnum Qden]. rewrite !Z.mul_1_r. exact HposE. }
    intro Hc. apply (Qlt_not_eq 0%Q _ HposAB). exact (Qeq_sym _ _ Hc). }
  assert (Hmul : Qle (((Z.of_nat (bkC (Datatypes.S (n + m)) n) # 1)
                         * ((Z.of_nat (n + 2 * m + 1) # 1)
                            * (Z.of_nat (n + 2 * m + 2) # 1)))
                        * ((1 / (Z.of_nat (3 * n + 2 * m + 3) # 1))
                           * (1 / (Z.of_nat (3 * n + 2 * m + 4) # 1))))
                      (((Z.of_nat (bkC (n + m) n) # 1)
                         * ((Z.of_nat (3 * n + 2 * m + 3) # 1)
                            * (Z.of_nat (3 * n + 2 * m + 4) # 1)))
                        * ((1 / (Z.of_nat (3 * n + 2 * m + 3) # 1))
                           * (1 / (Z.of_nat (3 * n + 2 * m + 4) # 1))))).
  { apply Qmult_le_compat_r; assumption. }
  assert (E2 : (((Z.of_nat (bkC (n + m) n) # 1)
                   * ((Z.of_nat (3 * n + 2 * m + 3) # 1)
                      * (Z.of_nat (3 * n + 2 * m + 4) # 1)))
                  * ((1 / (Z.of_nat (3 * n + 2 * m + 3) # 1))
                     * (1 / (Z.of_nat (3 * n + 2 * m + 4) # 1))))
               == (Z.of_nat (bkC (n + m) n) # 1)).
  { rewrite <- (Qmult_assoc (Z.of_nat (bkC (n + m) n) # 1)
                  ((Z.of_nat (3 * n + 2 * m + 3) # 1)
                     * (Z.of_nat (3 * n + 2 * m + 4) # 1))
                  ((1 / (Z.of_nat (3 * n + 2 * m + 3) # 1))
                   * (1 / (Z.of_nat (3 * n + 2 * m + 4) # 1)))).
    rewrite HinvP. apply Qmult_1_r. }
  rewrite HshapeS, HshapeT.
  apply Qmult_le_compat_r.
  - apply (Qle_trans _ (((Z.of_nat (bkC (n + m) n) # 1)
                           * ((Z.of_nat (3 * n + 2 * m + 3) # 1)
                              * (Z.of_nat (3 * n + 2 * m + 4) # 1)))
                          * ((1 / (Z.of_nat (3 * n + 2 * m + 3) # 1))
                             * (1 / (Z.of_nat (3 * n + 2 * m + 4) # 1))))).
    + apply (Qle_trans _ (((Z.of_nat (bkC (Datatypes.S (n + m)) n) # 1)
                              * ((Z.of_nat (n + 2 * m + 1) # 1)
                                   * (Z.of_nat (n + 2 * m + 2) # 1))
                              * ((1 / (Z.of_nat (3 * n + 2 * m + 3) # 1))
                                   * (1 / (Z.of_nat (3 * n + 2 * m + 4) # 1)))))).
      { apply (QleT'_to_Qle _ _). apply qeq_imp_qle. apply qeq_imp_qeqT. ring. }
      { exact Hmul. }
    + rewrite E2. apply Qle_refl.
  - apply Qlt_le_weak.
    unfold Qdiv.
    apply Qmult_lt_0_compat.
    + apply Qmult_lt_0_compat; apply QltT_to_Qlt; apply q_fact_pos.
    + apply Qinv_lt_0_compat. apply QltT_to_Qlt. apply q_fact_pos.
Defined.

(* Numeric anchor: the decay is strict at n = m = 2 (a separating QltT
   witness). *)
Theorem rx_term_decay_anchor : QltT (bv_term 2 3) (bv_term 2 2).
Proof. vm_compute. reflexivity. Defined.

(* ============================================================ *)
(* Assumption audit: Print Assumptions                          *)
(* ============================================================ *)

Print Assumptions rx_psQ_reindex.
Print Assumptions rx_bv_c_diag.
Print Assumptions rx_term_decayQ.
Print Assumptions rx_term_decay_anchor.
