(* ConstructiveWorld-Set -- truncation master identities with the arctan kernel shift. *)

(** * b1_trunc_master: the division-free truncation master identity and its arctan kernel shift.

    Mission.  The division-free master identity [(1 - t)^(n+1) * A(n,M,t) +
      t^(M+1) * P(n,M,t) = 1] with [A(n,M,t) = sum_{k < S M} C(n+k,n) * t^k]
      and [P(n,M,t) = sum_{i < S n} C(M+i,i) * (1-t)^i] holds unconditionally
      in [t] as the pure [Q] identity [b1_master]; the arctan shift
      [t := -(x*x)] gives [b1_master_arctan] and the positivity limb
      ([b1_pq_ge0], [b1_pq_ge0_arctan], [b1_ps_bound]).

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs], [ZArith.ZArith],
      [Arith.Arith], [Setoid], [Morphisms], [Qfield], [Lia]; requires
      [S01_BaseRing], [S02_CauchyComplete], [S03_QExp], [BeukersLists], [b1_kernel_pointwise].

    References.  The baseline module in ConstructiveWorld-Main whose
      statement names are carried over here verbatim.

    Constructivity.  Disclosure is per item, not blanket.  [Set]-carried via
      the [QleT']/[QeqT] carriers over [Q] (witnesses as data):
      [b1_bkC_Q_nonneg], [b1_qleT'_wd_r], [b1_pq_ge0], [b1_pq_ge0_arctan],
      [b1_ps_bound], [b1_master_anchor_110], [b1_master_anchor_11half],
      [b1_pq_anchor].  [Prop]-face ([Qeq]/[eq] identity, reasoning only,
      erased under extraction): [b1_master], [b1_master_arctan], and the
      support lemmas [b1_bkC_zero], [b1_ofC_add], [b1_pascalC],
      [b1_bk_psQ_add], [b1_ps_unfold], [b1_psu_unfold], [b1_ps_geom],
      [b1_ps_pascal], [b1_pq_step], [b1_shift], [b1_shift_su].  [b1_ps],
      [b1_psu], [b1_pq] are [Q]-valued data.  [coqchk] reports [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" b1_trunc_master.v] exits 0; artifact magic [436f7121 000160bc]. *)

From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith Arith.Arith.
From Stdlib Require Import Setoid Morphisms Qfield Lia.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import BeukersLists.
Require Import b1_kernel_pointwise.

Open Scope Q_scope.

(* ========== Section 0. Toolkit: the rational image of [bkC] and pointwise sums ========== *)

(* binomial coefficients at the zero lower index stay at one *)
Lemma b1_bkC_zero : forall n : nat, bkC n 0 = 1%nat.
Proof.
  intros n. destruct n as [| n'].
  - reflexivity.
  - reflexivity.
Qed.

(* the rational image with unit denominator distributes over index addition *)
Lemma b1_ofC_add : forall a b : nat,
  (Z.of_nat (a + b) # 1) == ((Z.of_nat a # 1) + (Z.of_nat b # 1))%Q.
Proof.
  intros a b. unfold Qeq. cbn [Qnum Qden Qplus Pos.mul].
  rewrite !Z.mul_1_r, !Nat2Z.inj_add. reflexivity.
Qed.

(* the rational image of the Pascal identity: [C(N+1,n+1) = C(N,n) + C(N,n+1)] *)
Lemma b1_pascalC : forall N n : nat,
  (Z.of_nat (bkC (Datatypes.S N) (Datatypes.S n)) # 1)
  == ((Z.of_nat (bkC N n) # 1) + (Z.of_nat (bkC N (Datatypes.S n)) # 1))%Q.
Proof.
  intros N n.
  assert (He : (bkC N n + bkC N (Datatypes.S n))%nat
               = bkC (Datatypes.S N) (Datatypes.S n)).
  { pose proof (bkC_pascal_shift N (Datatypes.S n)) as Hc.
    change (Id ((bkC N n + bkC N (Datatypes.S n))%nat)
              (bkC (Datatypes.S N) (Datatypes.S n))) in Hc.
    destruct Hc. reflexivity. }
  rewrite <- He. rewrite <- b1_ofC_add. reflexivity.
Qed.

(* nonnegativity of the rational image of binomial coefficients, as a [QleT'] witness *)
Lemma b1_bkC_Q_nonneg : forall n k : nat, QleT' 0 ((Z.of_nat (bkC n k) # 1)%Q).
Proof.
  intros n k. apply Qle_to_QleT'. unfold Qle. cbn [Qnum Qden Qmult Pos.mul].
  destruct (le_lt_dec k n) as [Hle | Hlt].
  - assert (Hb : (1 <= bkC n k)%nat)
      by (apply NatLe_drop; apply bkC_pos; apply NatLe_lift; exact Hle).
    lia.
  - assert (He : bkC n k = 0%nat)
      by (destruct (bkC_out n k (NatLe_lift _ _ Hlt)); reflexivity).
    rewrite He. cbn [Z.of_nat]. lia.
Qed.

(* rewriting the right end of a [QleT'] order witness along a rational equality *)
Lemma b1_qleT'_wd_r : forall x y z : Q, x == y -> QleT' z x -> QleT' z y.
Proof.
  intros x y z Hxy Hz. apply Qle_to_QleT'.
  apply (Qle_trans z x y).
  - apply QleT'_to_Qle. exact Hz.
  - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. exact Hxy.
Qed.

(* pointwise additivity of the indexed sum [bk_psQ] *)
Lemma b1_bk_psQ_add : forall (f g h : nat -> Q) (N : nat) (z : Q),
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

(* ========== Section 1. The three series of the truncation family (interface signatures) ========== *)

(* the truncated sum [A(n,M,t) = sum_{k < S M} C(n+k,n) * t^k] *)
Definition b1_ps (n M : nat) (t : Q) : Q :=
  bk_psQ (fun m => (Z.of_nat (bkC (n + m) n) # 1)) (Datatypes.S M) t.

(* the companion sum [U(n,M,t) = sum_{k < S M} C(n+k,n+1) * t^k], the Pascal partner of [A] *)
Definition b1_psu (n M : nat) (t : Q) : Q :=
  bk_psQ (fun m => (Z.of_nat (bkC (n + m) (Datatypes.S n)) # 1)) (Datatypes.S M) t.

(* the remainder polynomial [P(n,M,t) = sum_{i < S n} C(M+i,i) * (1-t)^i] *)
Definition b1_pq (n M : nat) (t : Q) : Q :=
  bk_psQ (fun i => (Z.of_nat (bkC (M + i) i) # 1)) (Datatypes.S n) (1 - t).

(* stripping the last term, definitionally: [A(n,M+1,t) = A(n,M,t) + C(n+M+1,n) * t^(M+1)] *)
Lemma b1_ps_unfold : forall n M t,
  b1_ps n (Datatypes.S M) t
  == (b1_ps n M t
      + (Z.of_nat (bkC (n + Datatypes.S M) n) # 1) * q_pow t (Datatypes.S M))%Q.
Proof.
  intros n M t. unfold b1_ps. cbn [bk_psQ]. reflexivity.
Qed.

(* stripping the last term: [U(n,M+1,t) = U(n,M,t) + C(n+M+1,n+1) * t^(M+1)] *)
Lemma b1_psu_unfold : forall n M t,
  b1_psu n (Datatypes.S M) t
  == (b1_psu n M t
      + (Z.of_nat (bkC (n + Datatypes.S M) (Datatypes.S n)) # 1)
        * q_pow t (Datatypes.S M))%Q.
Proof.
  intros n M t. unfold b1_psu. cbn [bk_psQ]. reflexivity.
Qed.

(* ========== Section 2. The identity faces: the geometric sum, Pascal additivity, and the shift identity ========== *)

(* the geometric tier: [(1 - t) * A(0,M,t) = 1 - t^(M+1)] *)
Lemma b1_ps_geom : forall M t,
  (1 - t) * b1_ps 0 M t == 1 - q_pow t (Datatypes.S M).
Proof.
  intros M. induction M as [| M IH]; intro t.
  - unfold b1_ps. cbn [bk_psQ q_pow Nat.add bkC Z.of_nat]. ring.
  - rewrite b1_ps_unfold.
    transitivity (((1 - t) * b1_ps 0 M t
                   + (1 - t) * ((Z.of_nat (bkC (0 + Datatypes.S M) 0) # 1)
                                * q_pow t (Datatypes.S M)))%Q).
    + ring.
    + rewrite IH.
      replace (Z.of_nat (bkC (0 + Datatypes.S M) 0) # 1) with (1 # 1)%Q
        by (rewrite b1_bkC_zero; reflexivity).
      cbn [q_pow]. ring.
Qed.

(* the Pascal tier: [A(n+1,M,t) = A(n,M,t) + U(n,M,t)] *)
Lemma b1_ps_pascal : forall n M t,
  b1_ps (Datatypes.S n) M t == (b1_ps n M t + b1_psu n M t)%Q.
Proof.
  intros n M t. apply b1_bk_psQ_add. intros k Hk.
  replace (Datatypes.S n + k)%nat with (Datatypes.S (n + k))%nat by reflexivity.
  rewrite (b1_pascalC (n + k) n). ring.
Qed.

(* the Pascal step for [P], definitionally: [P(n+1,M,t) = P(n,M,t) + C(M+n+1,n+1) * (1-t)^(n+1)] *)
Lemma b1_pq_step : forall n M t,
  b1_pq (Datatypes.S n) M t
  == (b1_pq n M t
      + (Z.of_nat (bkC (M + Datatypes.S n) (Datatypes.S n)) # 1)
        * q_pow (1 - t) (Datatypes.S n))%Q.
Proof.
  intros n M t. unfold b1_pq. cbn [bk_psQ]. reflexivity.
Qed.

(* the shift tier: [t * A - (1 - t) * U = t^(M+1) * C(n+M+1,n+1)] *)
Lemma b1_shift : forall n M t,
  t * b1_ps n M t - (1 - t) * b1_psu n M t
  == (q_pow t (Datatypes.S M)
      * (Z.of_nat (bkC (n + Datatypes.S M) (Datatypes.S n)) # 1))%Q.
Proof.
  intros n M. revert n.
  induction M as [| M IH]; intros n t.
  - unfold b1_ps, b1_psu. cbn [bk_psQ q_pow].
    rewrite Nat.add_0_r.
    assert (Hd : bkC n n = 1%nat) by (destruct (bkC_diag n); reflexivity).
    assert (H0 : bkC n (Datatypes.S n) = 0%nat)
      by (destruct (bkC_out n (Datatypes.S n)
                      (NatLe_lift _ _ (le_n (Datatypes.S n)))); reflexivity).
    assert (Hd2 : bkC (Datatypes.S n) (Datatypes.S n) = 1%nat)
      by (destruct (bkC_diag (Datatypes.S n)); reflexivity).
    replace (n + Datatypes.S 0)%nat with (Datatypes.S n)%nat by lia.
    rewrite Hd, H0, Hd2. cbn [Z.of_nat]. ring.
  - rewrite b1_ps_unfold. rewrite b1_psu_unfold.
    transitivity (((t * b1_ps n M t - (1 - t) * b1_psu n M t)
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
      rewrite (b1_pascalC (n + Datatypes.S M) n).
      change (q_pow t (Datatypes.S (Datatypes.S M)))
        with (t * q_pow t (Datatypes.S M))%Q.
      ring.
Qed.

(* a reshaped form of the shift identity, the helper identity for the upper bound *)
Lemma b1_shift_su : forall n M t,
  (1 - t) * q_pow (1 - t) (Datatypes.S n) * b1_psu n M t
  == (t * (q_pow (1 - t) (Datatypes.S n) * b1_ps n M t)
      - q_pow (1 - t) (Datatypes.S n)
        * (q_pow t (Datatypes.S M)
           * (Z.of_nat (bkC (n + Datatypes.S M) (Datatypes.S n)) # 1)))%Q.
Proof.
  intros n M t. rewrite <- (b1_shift n M t). ring.
Qed.

(* ========== Section 3. The master identity, unconditionally in [t] ========== *)

(* the master identity [(1 - t)^(n+1) * A + t^(M+1) * P = 1], a pure [Q]
   algebraic identity holding for every [t].  the algebra reads
   [1 - (1-t)^(n+2) * (A + U) = (1 - (1-t)^(n+1) * A) + (1-t)^(n+1) * (t*A - (1-t)*U)]:
   the first bracket becomes [t^(M+1) * P] by the induction premise, the second
   bracket becomes [t^(M+1) * C(n+M+1,n+1)] by the shift tier, and both cancel
   against the new term introduced by the Pascal step. *)
Theorem b1_master : forall n M t,
  q_pow (1 - t) (Datatypes.S n) * b1_ps n M t
  + q_pow t (Datatypes.S M) * b1_pq n M t == 1.
Proof.
  intros n M t. revert M.
  induction n as [| n IH]; intro M.
  - unfold b1_pq. cbn [bk_psQ].
    change (q_pow (1 - t) (Datatypes.S 0)) with ((1 - t) * 1)%Q.
    change (q_pow (1 - t) 0) with 1%Q.
    assert (Hm : (1 - t) * 1 * b1_ps 0 M t == (1 - t) * b1_ps 0 M t) by ring.
    rewrite Hm. rewrite b1_ps_geom.
    replace (Z.of_nat (bkC (M + 0) 0) # 1) with (1 # 1)%Q
      by (rewrite Nat.add_0_r; rewrite b1_bkC_zero; reflexivity).
    ring.
  - assert (E := b1_shift_su n M t).
    rewrite b1_ps_pascal. rewrite b1_pq_step.
    change (q_pow (1 - t) (Datatypes.S (Datatypes.S n)))
      with ((1 - t) * q_pow (1 - t) (Datatypes.S n))%Q.
    replace (Z.of_nat (bkC (M + Datatypes.S n) (Datatypes.S n)) # 1)
      with (Z.of_nat (bkC (n + Datatypes.S M) (Datatypes.S n)) # 1)
      by (replace (M + Datatypes.S n)%nat with (n + Datatypes.S M)%nat by lia;
          reflexivity).
    transitivity (((q_pow (1 - t) (Datatypes.S n) * b1_ps n M t
                    + q_pow t (Datatypes.S M) * b1_pq n M t)
                   - t * (q_pow (1 - t) (Datatypes.S n) * b1_ps n M t)
                   + (1 - t) * q_pow (1 - t) (Datatypes.S n) * b1_psu n M t
                   + q_pow t (Datatypes.S M)
                     * ((Z.of_nat (bkC (n + Datatypes.S M) (Datatypes.S n)) # 1)
                        * q_pow (1 - t) (Datatypes.S n)))%Q).
    + ring.
    + rewrite (IH M). rewrite E. ring.
Qed.

(* ========== Section 4. The positivity limb (the [t <= 1] domain, including the arctan shift domain [t := -(x*x)]) ========== *)

(* nonnegativity of [P], term by term: [C(M+i,i) * (1-t)^i >= 0] as soon as [t <= 1] *)
Lemma b1_pq_ge0 : forall n M t, QleT' t 1 -> QleT' 0 (b1_pq n M t).
Proof.
  intros n. induction n as [| n IH]; intros M t Ht.
  - unfold b1_pq. cbn [bk_psQ q_pow].
    rewrite Nat.add_0_r.
    apply (b1_qleT'_wd_r ((Z.of_nat (bkC M 0) # 1))
             ((0 + (Z.of_nat (bkC M 0) # 1) * 1)%Q) 0).
    + ring.
    + apply b1_bkC_Q_nonneg.
  - apply (b1_qleT'_wd_r
             ((b1_pq n M t
               + (Z.of_nat (bkC (M + Datatypes.S n) (Datatypes.S n)) # 1)
                 * q_pow (1 - t) (Datatypes.S n))%Q)
             (b1_pq (Datatypes.S n) M t) 0).
    + exact (Qeq_sym _ _ (b1_pq_step n M t)).
    + apply Qle_to_QleT'.
      assert (Hsub : QleT' 0 (1 - t)) by exact (b1_sub_ge0 t Ht).
      apply (Qplus_le_compat 0 (b1_pq n M t) 0
               ((Z.of_nat (bkC (M + Datatypes.S n) (Datatypes.S n)) # 1)
                * q_pow (1 - t) (Datatypes.S n))).
      * apply QleT'_to_Qle. apply IH. exact Ht.
      * apply Qmult_le_0_compat.
        -- apply QleT'_to_Qle. apply b1_bkC_Q_nonneg.
        -- apply QleT'_to_Qle. apply (q_pow_nonneg (1 - t) (Datatypes.S n)). exact Hsub.
Qed.

(* positivity on the arctan shift domain: [P(n,M,-(x*x)) >= 0] for every [x],
   since [-(x*x) <= 1] holds for every [x] *)
Lemma b1_pq_ge0_arctan : forall (n M : nat) (x : Q), QleT' 0 (b1_pq n M (-(x * x))).
Proof.
  intros n M x.
  apply (b1_pq_ge0 n M (-(x * x))).
  apply Qle_to_QleT'.
  apply (Qle_trans (-(x * x)) 0 1).
  - exact (Qopp_le_compat 0 (x * x) (QleT'_to_Qle _ _ (b1_qsq_nonneg x))).
  - apply Qlt_le_weak. apply QltT_to_Qlt. exact b1_0lt1.
Qed.

(* ========== Section 5. The arctan kernel shift instance (the division-free remainder split) ========== *)

(* the shifted master identity [(1 + x*x)^(n+1) * A(n,M,-(x*x)) + (-(x*x))^(M+1) * P(n,M,-(x*x)) = 1],
   the division-free reading of
   [1/(1+x*x)^(n+1) = A(n,M,-(x*x)) + (-(x*x))^(M+1) * P / (1+x*x)^(n+1)]. *)
Theorem b1_master_arctan : forall (n M : nat) (x : Q),
  q_pow (1 + x * x) (Datatypes.S n) * b1_ps n M (-(x * x))
  + q_pow (-(x * x)) (Datatypes.S M) * b1_pq n M (-(x * x)) == 1.
Proof.
  intros n M x.
  pose proof (b1_master n M (-(x * x))) as Hm.
  setoid_replace (1 - (-(x * x)))%Q with (1 + x * x)%Q in Hm by ring.
  exact Hm.
Qed.

(* the division-free upper bound, the counterpart of item 5 of the zb2 tower:
   [0 <= t <= 1] gives [(1-t)^(n+1) * A <= 1] *)
Theorem b1_ps_bound : forall n M t,
  QleT' 0 t -> QleT' t 1 ->
  QleT' (q_pow (1 - t) (Datatypes.S n) * b1_ps n M t) 1.
Proof.
  intros n M t Ht0 Ht1.
  apply (b1_qleT'_wd_r
           (q_pow (1 - t) (Datatypes.S n) * b1_ps n M t
            + q_pow t (Datatypes.S M) * b1_pq n M t) 1
           (q_pow (1 - t) (Datatypes.S n) * b1_ps n M t)).
  - exact (b1_master n M t).
  - apply qleT'_plus_nonneg_rT.
    apply Qle_to_QleT'. apply Qmult_le_0_compat.
    + apply QleT'_to_Qle. apply (q_pow_nonneg t (Datatypes.S M)). exact Ht0.
    + apply QleT'_to_Qle. apply (b1_pq_ge0 n M t). exact Ht1.
Qed.

(* ========== Section 6. Numerical anchors (independently recomputed cross-checks) ========== *)

(* anchor one: [n = 1, M = 0, x = 1] gives [(1+1)^2 * A(1,0,-1) + (-1)^1 * P(1,0,-1) = 4 * 1 - 3 = 1] *)
Lemma b1_master_anchor_110 :
  QeqT (q_pow (1 + (1 * 1)) (Datatypes.S 1) * b1_ps 1 0 (-(1 * 1))
        + q_pow (-(1 * 1)) (Datatypes.S 0) * b1_pq 1 0 (-(1 * 1))) (1 # 1).
Proof. apply qeq_imp_qeqT. reflexivity. Qed.

(* anchor two: [n = 1, M = 1, t = 1/2] gives [(1/2)^2 * A + (1/2)^2 * P = 1] with
   [A(1,1,1/2) = 1 + 2 * (1/2) = 2] and [P(1,1,1/2) = 1 + 2 * (1/2) = 2], so the
   two weighted terms sum to one *)
Lemma b1_master_anchor_11half :
  QeqT (q_pow (1 - (1 # 2)) (Datatypes.S 1) * b1_ps 1 1 (1 # 2)
        + q_pow (1 # 2) (Datatypes.S 1) * b1_pq 1 1 (1 # 2)) (1 # 1).
Proof. apply qeq_imp_qeqT. reflexivity. Qed.

(* anchor three, a positivity instance for [P]: [P(2,3,-4) = 1 + 4 * 5 + 10 * 25 = 271 > 0] *)
Lemma b1_pq_anchor :
  QeqT (b1_pq 2 3 (-(4 * 1))) (271 # 1).
Proof. apply qeq_imp_qeqT. reflexivity. Qed.

(* ========== Section 7. In-file checks and the assumption audit ========== *)

Check b1_master.
Check b1_master_arctan.
Check b1_pq_ge0.
Check b1_pq_ge0_arctan.
Check b1_ps_bound.
Check b1_ps_geom.
Check b1_shift.

Print Assumptions b1_master.
Print Assumptions b1_master_arctan.
Print Assumptions b1_pq_ge0.
Print Assumptions b1_pq_ge0_arctan.
Print Assumptions b1_ps_bound.
