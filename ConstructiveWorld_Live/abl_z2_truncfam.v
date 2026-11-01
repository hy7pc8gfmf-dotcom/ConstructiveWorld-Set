(* abl_z2_truncfam.v -- Taylor truncation and remainder separation for  *)
(* the zeta(2) irrationality double-integral family (Beukers).          *)
(** * abl_z2_truncfam: Taylor truncation and remainder separation for the
    Beukers zeta(2) polynomial family.
    Mission.  For n, M >= 0 and rational t, write A(n,M,t) = sum_{m<=M}
    C(n+m,n)*t^m (zb2_ps), U(n,M,t) = sum_{m<=M} C(n+m,n+1)*t^m
    (zb2_psu), P(n,M,t) = sum_{i<=n} C(M+i,i)*(1-t)^i (zb2_pq), C the
    binomial coefficient.  Proved: (1) geometric case (1-t)*A(0,M,t) =
    1 - t^(M+1); (2) Pascal case A(n+1,M,t) = A(n,M,t) + U(n,M,t);
    (3) shift case, by induction on M: t*A - (1-t)*U =
    t^(M+1)*C(n+M+1,n+1), its Pascal step C(N,n) + C(N,n+1) =
    C(N+1,n+1) closed by an explicit combinatorial certificate;
    (4) master identity (induction on n, M generalized): on 0 <= t <= 1,
    (1-t)^(n+1)*A + t^(M+1)*P = 1, the division-free form of the
    truncated Taylor sum, read as 1 - (1-t)^(n+1)*A = t^(M+1)*P;
    (5) order facts P >= 0 and (1-t)^(n+1)*A <= 1 (Set-level QleT').
    Dependencies.  Stdlib (QArith, ZArith, Arith, Lia); S01_BaseRing;
    S02_CauchyComplete (QleT' bridge, transfer family); S03_QExp (q_pow);
    BeukersLists (bkC binomial coefficients, bk_psQ indexed sums).
    No external certificate checkers, no real-number layer, no classical logic.
    References.  Beukers, A note on the irrationality of zeta(2) and
    zeta(3), Bull. London Math. Soc. 11 (1979): Taylor truncation step
    of the polynomial family.
    Constructivity.  Purely constructive, no assumption-bearing
    statements; main statement surface is Qeq equalities and Set-level
    order witnesses QleT'; nonlinear combinatorial steps are closed
    by explicit Pascal-identity certificates; no ordered-field
    decision procedure.
    Build.  rocq c -native-compiler no -q -Q <world root> ""
    abl_z2_truncfam.v (Rocq 9.1.0, load-wrapped, single -Q root). *)

From Stdlib Require Import QArith.QArith ZArith.ZArith Arith.Arith Lia.
From Stdlib Require Import Setoid.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp BeukersLists.

Open Scope Q_scope.

(* ============================================================ *)
(* Section 0.  Elementary pieces: the zero case of the binomial
   coefficient, rational images of sums, and the Pascal identity. *)
(* ============================================================ *)

(* Zero case of the binomial coefficient: C(n,0) = 1 for all n. *)
Lemma zb2_bkC_zero : forall n : nat, bkC n 0 = 1%nat.
Proof.
  intros n. destruct n as [| n'].
  - reflexivity.
  - reflexivity.
Qed.

(* Rational image of a coefficient sum: Q images with unit
   denominator distribute over nat addition. *)
Lemma zb2_ofC_add : forall a b : nat,
  (Z.of_nat (a + b) # 1) == ((Z.of_nat a # 1) + (Z.of_nat b # 1))%Q.
Proof.
  intros a b. unfold Qeq. cbn [Qnum Qden Qplus Pos.mul].
  rewrite !Z.mul_1_r, !Nat2Z.inj_add. reflexivity.
Qed.

(* Rational image of the Pascal identity: C(N+1,n+1) = C(N,n) + C(N,n+1). *)
Lemma zb2_pascalC : forall N n : nat,
  (Z.of_nat (bkC (Datatypes.S N) (Datatypes.S n)) # 1)
  == ((Z.of_nat (bkC N n) # 1) + (Z.of_nat (bkC N (Datatypes.S n)) # 1))%Q.
Proof.
  intros N n.
  (* tree-gen bridge: the Pascal shift lemma is Id-shaped (BeukersLists
     L104); consume the Id form directly, no eq write-back. *)
  pose proof (bkC_pascal_shift N (Datatypes.S n)
              : Id ((bkC N n + bkC N (Datatypes.S n))%nat)
                   (bkC (Datatypes.S N) (Datatypes.S n))) as Hc.
  rewrite <- zb2_ofC_add.
  rewrite (S07_RealSetoidExpLog.RealSetoid.Id_eq _ _ Hc). reflexivity.
Qed.

(* Nonnegativity of the rational image of binomial coefficients
   (Set-level witness). *)
Lemma zb2_bkC_Q_nonneg : forall n k : nat, QleT' 0 ((Z.of_nat (bkC n k) # 1)%Q).
Proof.
  intros n k. apply Qle_to_QleT'. unfold Qle. cbn [Qnum Qden Qmult Pos.mul].
  destruct (le_lt_dec k n) as [Hle | Hlt].
  - assert (Hb : (1 <= bkC n k)%nat)
      by (apply NatLe_drop, bkC_pos, NatLe_lift; exact Hle).
    lia.
  - rewrite (S07_RealSetoidExpLog.RealSetoid.Id_eq _ _
               (bkC_out n k (NatLe_lift _ _ Hlt))). cbn [Z.of_nat]. lia.
Qed.

(* Right-hand rewriting for Set-level order witnesses: from x == y,
   QleT' z x implies QleT' z y for any z. *)
Lemma zb2_qleT'_wd_r : forall x y z : Q, x == y -> QleT' z x -> QleT' z y.
Proof.
  intros x y z Hxy Hz. apply Qle_to_QleT'.
  apply (Qle_trans z x y).
  - apply QleT'_to_Qle. exact Hz.
  - exact (QleT'_to_Qle _ _ (qeq_imp_qle _ _ (qeq_imp_qeqT _ _ Hxy))).
Qed.

(* Pointwise-addition extensionality of indexed sums: f k == (g k + h k)
   termwise implies sum f == sum g + sum h. *)
Lemma zb2_bk_psQ_add : forall (f g h : nat -> Q) (N : nat) (z : Q),
  (forall k : nat, (k < N)%nat -> f k == (g k + h k)%Q) ->
  bk_psQ f N z == (bk_psQ g N z + bk_psQ h N z)%Q.
Proof.
  intros f g h N. revert f g h.
  induction N as [| N IH]; intros f g h z Hfg.
  - reflexivity.
  - cbn [bk_psQ].
    rewrite (IH f g h z) by (intros k Hk; apply Hfg; lia).
    rewrite (Hfg N) by lia. ring.
Qed.

(* ============================================================ *)
(* Section 1.  The three truncation-family definitions
   (interface surface, signatures fixed). *)
(* ============================================================ *)

Definition zb2_ps (n M : nat) (t : Q) : Q :=
  bk_psQ (fun m => (Z.of_nat (bkC (n + m) n) # 1)) (Datatypes.S M) t.

Definition zb2_psu (n M : nat) (t : Q) : Q :=
  bk_psQ (fun m => (Z.of_nat (bkC (n + m) (Datatypes.S n)) # 1)) (Datatypes.S M) t.

Definition zb2_pq (n M : nat) (t : Q) : Q :=
  bk_psQ (fun i => (Z.of_nat (bkC (M + i) i) # 1)) (Datatypes.S n) (1 - t).

(* Peeling the last term (definitional): A(n,M+1,t) = A(n,M,t) +
   C(n+M+1,n)*t^(M+1). *)
Lemma zb2_ps_unfold : forall n M t,
  zb2_ps n (Datatypes.S M) t
  == (zb2_ps n M t
      + (Z.of_nat (bkC (n + Datatypes.S M) n) # 1) * q_pow t (Datatypes.S M))%Q.
Proof.
  intros n M t. unfold zb2_ps. cbn [bk_psQ]. reflexivity.
Qed.

(* Peeling the last term (definitional): U(n,M+1,t) = U(n,M,t) +
   C(n+M+1,n+1)*t^(M+1). *)
Lemma zb2_psu_unfold : forall n M t,
  zb2_psu n (Datatypes.S M) t
  == (zb2_psu n M t
      + (Z.of_nat (bkC (n + Datatypes.S M) (Datatypes.S n)) # 1)
        * q_pow t (Datatypes.S M))%Q.
Proof.
  intros n M t. unfold zb2_psu. cbn [bk_psQ]. reflexivity.
Qed.

(* ============================================================ *)
(* Section 2.  Equality surface: the geometric, Pascal, and shift cases. *)
(* ============================================================ *)

(* Geometric case: (1-t)*sum_{m<=M} t^m = 1 - t^(M+1). *)
Lemma zb2_ps_geom : forall M t,
  (1 - t) * zb2_ps 0 M t == 1 - q_pow t (Datatypes.S M).
Proof.
  intros M. induction M as [| M IH]; intro t.
  - unfold zb2_ps. cbn [bk_psQ q_pow Nat.add bkC Z.of_nat]. ring.
  - rewrite zb2_ps_unfold.
    transitivity (((1 - t) * zb2_ps 0 M t
                   + (1 - t) * ((Z.of_nat (bkC (0 + Datatypes.S M) 0) # 1)
                                * q_pow t (Datatypes.S M)))%Q).
    + ring.
    + rewrite IH.
      replace (Z.of_nat (bkC (0 + Datatypes.S M) 0) # 1) with (1 # 1)%Q
        by (rewrite zb2_bkC_zero; reflexivity).
      rewrite (qeqT_imp_qeq _ _ (q_pow_succ t (Datatypes.S M))). ring.
Qed.

(* Pascal case: A(n+1,M,t) = A(n,M,t) + U(n,M,t). *)
Lemma zb2_ps_pascal : forall n M t,
  zb2_ps (Datatypes.S n) M t == (zb2_ps n M t + zb2_psu n M t)%Q.
Proof.
  intros n M t. apply zb2_bk_psQ_add. intros k Hk.
  replace (Datatypes.S n + k)%nat with (Datatypes.S (n + k))%nat by reflexivity.
  rewrite (zb2_pascalC (n + k) n). ring.
Qed.

(* Pascal step (definitional): P(n+1,M,t) = P(n,M,t) +
   C(M+n+1,n+1)*(1-t)^(n+1). *)
Lemma zb2_pq_step : forall n M t,
  zb2_pq (Datatypes.S n) M t
  == (zb2_pq n M t
      + (Z.of_nat (bkC (M + Datatypes.S n) (Datatypes.S n)) # 1)
        * q_pow (1 - t) (Datatypes.S n))%Q.
Proof.
  intros n M t. unfold zb2_pq. cbn [bk_psQ]. reflexivity.
Qed.

(* Shift case: t*A - (1-t)*U = t^(M+1)*C(n+M+1,n+1), by induction on M;
   the base case uses the out-of-range fact C(n,n+1) = 0 and the
   diagonal fact, the step case the Pascal-identity certificate. *)
Lemma zb2_shift : forall n M t,
  t * zb2_ps n M t - (1 - t) * zb2_psu n M t
  == (q_pow t (Datatypes.S M)
      * (Z.of_nat (bkC (n + Datatypes.S M) (Datatypes.S n)) # 1))%Q.
Proof.
  intros n M. revert n.
  induction M as [| M IH]; intros n t.
  - unfold zb2_ps, zb2_psu. cbn [bk_psQ q_pow].
    rewrite Nat.add_0_r.
    rewrite (S07_RealSetoidExpLog.RealSetoid.Id_eq _ _ (bkC_diag n)).
    rewrite (S07_RealSetoidExpLog.RealSetoid.Id_eq _ _
               (bkC_out n (Datatypes.S n)
                  (NatLe_lift _ _ (Nat.lt_succ_diag_r n)))).
    replace (n + Datatypes.S 0)%nat with (Datatypes.S n)%nat by lia.
    rewrite (S07_RealSetoidExpLog.RealSetoid.Id_eq _ _ (bkC_diag (Datatypes.S n))).
    cbn [Z.of_nat]. ring.
  - rewrite zb2_ps_unfold. rewrite zb2_psu_unfold.
    transitivity (((t * zb2_ps n M t - (1 - t) * zb2_psu n M t)
                   + t * ((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)
                          * q_pow t (Datatypes.S M))
                   + t * ((Z.of_nat (bkC (n + Datatypes.S M) (Datatypes.S n)) # 1)
                          * q_pow t (Datatypes.S M))
                   - ((Z.of_nat (bkC (n + Datatypes.S M) (Datatypes.S n)) # 1)
                      * q_pow t (Datatypes.S M)))%Q).
    + ring.
    + rewrite IH.
      replace (n + Datatypes.S (Datatypes.S M))%nat
        with (Datatypes.S (n + Datatypes.S M))%nat by lia.
      rewrite (zb2_pascalC (n + Datatypes.S M) n).
      rewrite (qeqT_imp_qeq _ _ (q_pow_succ t (Datatypes.S M))). ring.
Qed.

(* ============================================================ *)
(* Section 3.  Master identity and order surface. *)
(* ============================================================ *)

(* Auxiliary identity for the upper bound, with s' = (1-t)^(n+1):
   (1-t)*s'*U = t*(s'*A) - s'*(t^(M+1)*C(n+M+1,n+1)); a rewrite
   of the shift case. *)
Lemma zb2_shift_su : forall n M t,
  (1 - t) * q_pow (1 - t) (Datatypes.S n) * zb2_psu n M t
  == (t * (q_pow (1 - t) (Datatypes.S n) * zb2_ps n M t)
      - q_pow (1 - t) (Datatypes.S n)
        * (q_pow t (Datatypes.S M)
           * (Z.of_nat (bkC (n + Datatypes.S M) (Datatypes.S n)) # 1)))%Q.
Proof.
  intros n M t. rewrite <- (zb2_shift n M t). ring.
Qed.

(* Master identity: on 0 <= t <= 1, (1-t)^(n+1)*A + t^(M+1)*P = 1.
   Algebraic reading: 1 - (1-t)^(n+2)*(A+U) = [1 - (1-t)^(n+1)*A] +
   (1-t)^(n+1)*[t*A - (1-t)*U]; the first bracket on the right becomes
   t^(M+1)*P by the induction assumption, the second becomes
   t^(M+1)*C(n+M+1,n+1) by the shift case, cancelling the new term
   of the Pascal step. *)
Lemma zb2_master : forall n M t, 0 <= t <= 1 ->
  q_pow (1 - t) (Datatypes.S n) * zb2_ps n M t
  + q_pow t (Datatypes.S M) * zb2_pq n M t == 1.
Proof.
  intros n M t Ht. revert M.
  induction n as [| n IH]; intro M.
  - unfold zb2_pq. cbn [bk_psQ].
    change (q_pow (1 - t) (Datatypes.S 0)) with ((1 - t) * 1)%Q.
    change (q_pow (1 - t) 0) with 1%Q.
    assert (Hm : (1 - t) * 1 * zb2_ps 0 M t == (1 - t) * zb2_ps 0 M t) by ring.
    rewrite Hm. rewrite zb2_ps_geom.
    replace (Z.of_nat (bkC (M + 0) 0) # 1) with (1 # 1)%Q
      by (rewrite Nat.add_0_r; rewrite zb2_bkC_zero; reflexivity).
    ring.
  - assert (E := zb2_shift_su n M t).
    rewrite zb2_ps_pascal. rewrite zb2_pq_step.
    rewrite (qeqT_imp_qeq _ _ (q_pow_succ (1 - t) (Datatypes.S n))).
    replace (Z.of_nat (bkC (M + Datatypes.S n) (Datatypes.S n)) # 1)
      with (Z.of_nat (bkC (n + Datatypes.S M) (Datatypes.S n)) # 1)
      by (replace (M + Datatypes.S n)%nat with (n + Datatypes.S M)%nat by lia;
          reflexivity).
    transitivity (((q_pow (1 - t) (Datatypes.S n) * zb2_ps n M t
                    + q_pow t (Datatypes.S M) * zb2_pq n M t)
                   - t * (q_pow (1 - t) (Datatypes.S n) * zb2_ps n M t)
                   + (1 - t) * q_pow (1 - t) (Datatypes.S n) * zb2_psu n M t
                   + q_pow t (Datatypes.S M)
                     * ((Z.of_nat (bkC (n + Datatypes.S M) (Datatypes.S n)) # 1)
                        * q_pow (1 - t) (Datatypes.S n)))%Q).
    + ring.
    + rewrite (IH M). rewrite E. ring.
Qed.

(* Nonnegativity of P: termwise C(M+i,i)*(1-t)^i >= 0. *)
Lemma zb2_pq_ge0 : forall n M t, 0 <= t <= 1 -> QleT' 0 (zb2_pq n M t).
Proof.
  intros n. induction n as [| n IH]; intros M t Ht.
  - unfold zb2_pq. cbn [bk_psQ q_pow].
    rewrite Nat.add_0_r.
    apply (zb2_qleT'_wd_r (Z.of_nat (bkC M 0) # 1)
             ((0 + (Z.of_nat (bkC M 0) # 1) * 1)%Q) 0).
    + ring.
    + apply zb2_bkC_Q_nonneg.
  - apply (zb2_qleT'_wd_r
             ((zb2_pq n M t
               + (Z.of_nat (bkC (M + Datatypes.S n) (Datatypes.S n)) # 1)
                 * q_pow (1 - t) (Datatypes.S n))%Q)
             (zb2_pq (Datatypes.S n) M t) 0).
    + exact (Qeq_sym _ _ (zb2_pq_step n M t)).
    + apply Qle_to_QleT'.
      destruct Ht as [Ht0 Ht1].
      assert (Hsub : Qle 0 (1 - t)).
      { unfold Qle in *. cbn [Qnum Qden Qminus Qplus Qopp Qmult] in *. lia. }
      apply (Qplus_le_compat 0 (zb2_pq n M t) 0
               ((Z.of_nat (bkC (M + Datatypes.S n) (Datatypes.S n)) # 1)
                * q_pow (1 - t) (Datatypes.S n))).
      * apply QleT'_to_Qle. apply IH. split; assumption.
      * apply Qmult_le_0_compat.
        -- apply QleT'_to_Qle. apply zb2_bkC_Q_nonneg.
        -- apply QleT'_to_Qle. apply (q_pow_nonneg (1 - t) (Datatypes.S n)).
           apply Qle_to_QleT'. exact Hsub.
Qed.

(* Division-free upper bound for the partial sum: (1-t)^(n+1)*A <= 1,
   from the master identity 1 = (1-t)^(n+1)*A + t^(M+1)*P and the
   fact t^(M+1)*P >= 0. *)
Lemma zb2_ps_bound : forall n M t, 0 <= t <= 1 ->
  QleT' (q_pow (1 - t) (Datatypes.S n) * zb2_ps n M t) 1.
Proof.
  intros n M t Ht.
  apply (zb2_qleT'_wd_r
           (q_pow (1 - t) (Datatypes.S n) * zb2_ps n M t
            + q_pow t (Datatypes.S M) * zb2_pq n M t) 1
           (q_pow (1 - t) (Datatypes.S n) * zb2_ps n M t)).
  - exact (zb2_master n M t Ht).
  - apply qleT'_plus_nonneg_rT.
    apply Qle_to_QleT'. apply Qmult_le_0_compat.
    + apply QleT'_to_Qle. apply (q_pow_nonneg t (Datatypes.S M)).
      apply Qle_to_QleT'. destruct Ht as [Ht0 _]. exact Ht0.
    + apply QleT'_to_Qle. apply zb2_pq_ge0. exact Ht.
Qed.

(* Numerical anchor: A(1,1,1/2) = C(1,1) + C(2,1)*(1/2) = 1 + 1 = 2. *)
Lemma zb2_ps_anchor1 : zb2_ps 1 1 (1 # 2) == 2.
Proof.
  vm_compute. reflexivity.
Qed.

(* ============================================================ *)
(* Section 4.  Tail block: dependency self-audit of the main
   statements (Print Assumptions). *)
(* ============================================================ *)

Print Assumptions zb2_ps_geom.
Print Assumptions zb2_ps_pascal.
Print Assumptions zb2_pq_step.
Print Assumptions zb2_shift.
Print Assumptions zb2_master.
Print Assumptions zb2_pq_ge0.
Print Assumptions zb2_ps_bound.
Print Assumptions zb2_ps_anchor1.
