(* ConstructiveWorld-Set -- truncation identities for the Beukers-type single-integral witness family for ln2. *)

(** * abl_lnt_truncfam: truncation identities for the Beukers-type ln2 witness family.

    Mission.  The algebraic side of the Beukers-type ln2 single integral: the
      truncation families [lnt_ps], [lnt_psu], [lnt_pq]; the geometric, Pascal
      and shift faces [lnt_ps_geom], [lnt_ps_pascal], [lnt_shift]; the master
      identity [lnt_master] (1+t)^(n+1)B + (-t)^(M+1)Q = 1 with no premise; the
      separation face [lnt_remainder_sep]; the order face [lnt_pq_ge0]; and the
      t=1 Bezout faces [lnt_bezout_odd], [lnt_bezout_even] docking the series.

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs], [ZArith.ZArith],
      [Arith.Arith], [Lia], [Setoid].  Requires [S01_BaseRing],
      [S02_CauchyComplete], [S03_QExp], [BeukersLists], [abl_z2_truncfam],
      [PolyIntegral], [UpReqLn2Irrational], [Ln2Bridge] of this development.

    References.  This development, abl_lnt_truncfam.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" abl_lnt_truncfam.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 00015ff4]. *)
From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith Arith.Arith Lia.
From Stdlib Require Import Setoid.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp BeukersLists
  abl_z2_truncfam.
Require Import PolyIntegral.

Open Scope Q_scope.

(* ============================================================ *)
(* Section 1. The three truncation families: the zb2 families evaluated at -t              *)
(* ============================================================ *)

(* B(n,M,t) = sum over m <= M of (-1)^m C(n+m,n) t^m, the Taylor truncation of 1/(1+t)^(n+1). *)
Definition lnt_ps (n M : nat) (t : Q) : Q :=
  zb2_ps n M (0 - t).

(* Bu(n,M,t) = sum over m <= M of (-1)^m C(n+m,n+1) t^m, the companion family of the Pascal face. *)
Definition lnt_psu (n M : nat) (t : Q) : Q :=
  zb2_psu n M (0 - t).

(* Q(n,M,t) = sum over i <= n of C(M+i,i) (1+t)^i, the remainder polynomial family. *)
Definition lnt_pq (n M : nat) (t : Q) : Q :=
  zb2_pq n M (0 - t).

(* Bridge for the change of variables: (1+t)^k = (1-(0-t))^k; q_pow treats its base as an atom, so the bridge passes by induction on k. *)
Lemma lnt_one_pt_bridge : forall (t : Q) (k : nat),
  q_pow (1 - (0 - t)) k == q_pow (1 + t) k.
Proof.
  intros t k. induction k as [| k IH].
  - reflexivity.
  - rewrite (qeqT_imp_qeq _ _ (q_pow_succ (1 - (0 - t)) k)).
    rewrite (qeqT_imp_qeq _ _ (q_pow_succ (1 + t) k)).
    transitivity ((1 - (0 - t)) * q_pow (1 + t) k)%Q.
    + rewrite IH. ring.
    + ring.
Qed.

(* Stripping the last term, definitionally: B(n,M+1,t) = B(n,M,t) + C(n+M+1,n) (-t)^(M+1). *)
Lemma lnt_ps_unfold : forall n M t,
  lnt_ps n (Datatypes.S M) t
  == (lnt_ps n M t
      + (Z.of_nat (bkC (n + Datatypes.S M) n) # 1)
        * q_pow (0 - t) (Datatypes.S M))%Q.
Proof.
  intros n M t. unfold lnt_ps. exact (zb2_ps_unfold n M (0 - t)).
Qed.

(* Stripping the last term, definitionally: Bu(n,M+1,t) = Bu(n,M,t) + C(n+M+1,n+1) (-t)^(M+1). *)
Lemma lnt_psu_unfold : forall n M t,
  lnt_psu n (Datatypes.S M) t
  == (lnt_psu n M t
      + (Z.of_nat (bkC (n + Datatypes.S M) (Datatypes.S n)) # 1)
        * q_pow (0 - t) (Datatypes.S M))%Q.
Proof.
  intros n M t. unfold lnt_psu. exact (zb2_psu_unfold n M (0 - t)).
Qed.

(* ============================================================ *)
(* Section 2. The equality faces: geometric, Pascal and shift, instances of the zb2 lemmas at -t            *)
(* ============================================================ *)

(* Geometric face: (1+t) times the sum over m <= M of (-t)^m equals 1 - (-t)^(M+1). *)
Lemma lnt_ps_geom : forall M t,
  (1 + t) * lnt_ps 0 M t == 1 - q_pow (0 - t) (Datatypes.S M).
Proof.
  intros M t. unfold lnt_ps.
  transitivity ((1 - (0 - t)) * zb2_ps 0 M (0 - t))%Q.
  - ring.
  - exact (zb2_ps_geom M (0 - t)).
Qed.

(* Pascal face: B(n+1,M,t) = B(n,M,t) + Bu(n,M,t). *)
Lemma lnt_ps_pascal : forall n M t,
  lnt_ps (Datatypes.S n) M t == (lnt_ps n M t + lnt_psu n M t)%Q.
Proof.
  intros n M t. unfold lnt_ps, lnt_psu. exact (zb2_ps_pascal n M (0 - t)).
Qed.

(* Pascal step, definitionally: Q(n+1,M,t) = Q(n,M,t) + C(M+n+1,n+1) (1+t)^(n+1). *)
Lemma lnt_pq_step : forall n M t,
  lnt_pq (Datatypes.S n) M t
  == (lnt_pq n M t
      + (Z.of_nat (bkC (M + Datatypes.S n) (Datatypes.S n)) # 1)
        * q_pow (1 + t) (Datatypes.S n))%Q.
Proof.
  intros n M t. unfold lnt_pq.
  rewrite <- (lnt_one_pt_bridge t (Datatypes.S n)).
  exact (zb2_pq_step n M (0 - t)).
Qed.

(* Shift face: (-t) B - (1+t) Bu = (-t)^(M+1) C(n+M+1,n+1). *)
Lemma lnt_shift : forall n M t,
  (0 - t) * lnt_ps n M t - (1 + t) * lnt_psu n M t
  == (q_pow (0 - t) (Datatypes.S M)
      * (Z.of_nat (bkC (n + Datatypes.S M) (Datatypes.S n)) # 1))%Q.
Proof.
  intros n M t. unfold lnt_ps, lnt_psu.
  transitivity (((0 - t) * zb2_ps n M (0 - t)
                 - (1 - (0 - t)) * zb2_psu n M (0 - t))%Q).
  - ring.
  - exact (zb2_shift n M (0 - t)).
Qed.

(* Shift face rearranged for the induction step of the master identity: multiply the shift face by (1+t)^(n+1) and rearrange. *)
Lemma lnt_shift_su : forall n M t,
  (1 + t) * q_pow (1 + t) (Datatypes.S n) * lnt_psu n M t
  == ((0 - t) * (q_pow (1 + t) (Datatypes.S n) * lnt_ps n M t)
      - q_pow (1 + t) (Datatypes.S n)
        * (q_pow (0 - t) (Datatypes.S M)
           * (Z.of_nat (bkC (n + Datatypes.S M) (Datatypes.S n)) # 1)))%Q.
Proof.
  intros n M t. unfold lnt_ps, lnt_psu.
  rewrite <- (lnt_one_pt_bridge t (Datatypes.S n)).
  transitivity (((1 - (0 - t)) * q_pow (1 - (0 - t)) (Datatypes.S n)
                 * zb2_psu n M (0 - t))%Q).
  - ring.
  - exact (zb2_shift_su n M (0 - t)).
Qed.

(* ============================================================ *)
(* Section 3. The master identity and the remainder separation                                                *)
(* ============================================================ *)

(* Master identity: (1+t)^(n+1) B + (-t)^(M+1) Q = 1, for every rational t.
   Algebraic reading: 1 - (1+t)^(n+2) (B+Bu) = [1 - (1+t)^(n+1) B] +
   (1+t)^(n+1) [(-t) B - (1+t) Bu]; the first bracket on the right becomes
   (-t)^(M+1) Q by the induction premise and the second becomes
   (-t)^(M+1) C(n+M+1,n+1) by the shift face, cancelling the new term of the
   Pascal step. *)
Lemma lnt_master : forall n M t,
  q_pow (1 + t) (Datatypes.S n) * lnt_ps n M t
  + q_pow (0 - t) (Datatypes.S M) * lnt_pq n M t == 1.
Proof.
  intros n M t. revert M.
  induction n as [| n IH]; intro M.
  - unfold lnt_pq. unfold zb2_pq. cbn [bk_psQ].
    change (q_pow (1 + t) (Datatypes.S 0)) with ((1 + t) * 1)%Q.
    change (q_pow (1 - (0 - t)) 0) with 1%Q.
    assert (Hm : (1 + t) * 1 * lnt_ps 0 M t == (1 + t) * lnt_ps 0 M t) by ring.
    rewrite Hm. rewrite lnt_ps_geom.
    replace (Z.of_nat (bkC (M + 0) 0) # 1) with (1 # 1)%Q
      by (rewrite Nat.add_0_r; rewrite zb2_bkC_zero; reflexivity).
    ring.
  - assert (E := lnt_shift_su n M t).
    rewrite lnt_ps_pascal. rewrite lnt_pq_step.
    rewrite (qeqT_imp_qeq _ _ (q_pow_succ (1 + t) (Datatypes.S n))).
    replace (Z.of_nat (bkC (M + Datatypes.S n) (Datatypes.S n)) # 1)
      with (Z.of_nat (bkC (n + Datatypes.S M) (Datatypes.S n)) # 1)
      by (replace (M + Datatypes.S n)%nat with (n + Datatypes.S M)%nat by lia;
          reflexivity).
    transitivity (((q_pow (1 + t) (Datatypes.S n) * lnt_ps n M t
                    + q_pow (0 - t) (Datatypes.S M) * lnt_pq n M t)
                   - (0 - t) * (q_pow (1 + t) (Datatypes.S n) * lnt_ps n M t)
                   + (1 + t) * q_pow (1 + t) (Datatypes.S n) * lnt_psu n M t
                   + q_pow (0 - t) (Datatypes.S M)
                     * ((Z.of_nat (bkC (n + Datatypes.S M) (Datatypes.S n)) # 1)
                        * q_pow (1 + t) (Datatypes.S n)))%Q).
    + ring.
    + rewrite (IH M). rewrite E. ring.
Qed.

(* Explicit separation of the remainder: 1 - (1+t)^(n+1) B = (-t)^(M+1) Q.
   The truncation error thus carries the factor (-t)^(M+1) exactly, the
   algebraic root of the decay estimates used by the later integral face. *)
Lemma lnt_remainder_sep : forall n M t,
  1 - q_pow (1 + t) (Datatypes.S n) * lnt_ps n M t
  == q_pow (0 - t) (Datatypes.S M) * lnt_pq n M t.
Proof.
  intros n M t.
  remember (q_pow (1 + t) (Datatypes.S n) * lnt_ps n M t)%Q as A eqn:HA.
  remember (q_pow (0 - t) (Datatypes.S M) * lnt_pq n M t)%Q as B eqn:HB.
  assert (Hm : A + B == 1).
  { rewrite HA. rewrite HB. exact (lnt_master n M t). }
  rewrite <- Hm. ring.
Qed.

(* ============================================================ *)
(* Section 4. The order face: nonnegativity of the remainder family, QleT' witnesses at the Set level                              *)
(* ============================================================ *)

(* Q >= 0: each term C(M+i,i) (1+t)^i is nonnegative, under the premise 1+t >= 0. *)
Lemma lnt_pq_ge0 : forall n M t, Qle 0 (1 + t) -> QleT' 0 (lnt_pq n M t).
Proof.
  intros n. induction n as [| n IH]; intros M t H.
  - unfold lnt_pq. unfold zb2_pq. cbn [bk_psQ q_pow]. rewrite Nat.add_0_r.
    apply (zb2_qleT'_wd_r (Z.of_nat (bkC M 0) # 1)
             ((0 + (Z.of_nat (bkC M 0) # 1) * 1)%Q) 0).
    + ring.
    + apply zb2_bkC_Q_nonneg.
  - apply (zb2_qleT'_wd_r
             ((lnt_pq n M t
               + (Z.of_nat (bkC (M + Datatypes.S n) (Datatypes.S n)) # 1)
                 * q_pow (1 + t) (Datatypes.S n))%Q)
             (lnt_pq (Datatypes.S n) M t) 0).
    + exact (Qeq_sym _ _ (lnt_pq_step n M t)).
    + apply Qle_to_QleT'.
      apply (Qplus_le_compat 0 (lnt_pq n M t) 0
               ((Z.of_nat (bkC (M + Datatypes.S n) (Datatypes.S n)) # 1)
                * q_pow (1 + t) (Datatypes.S n))).
      * apply QleT'_to_Qle. apply IH. exact H.
      * apply Qmult_le_0_compat.
        -- apply QleT'_to_Qle. apply zb2_bkC_Q_nonneg.
        -- apply QleT'_to_Qle. apply (q_pow_nonneg (1 + t) (Datatypes.S n)).
           apply Qle_to_QleT'. exact H.
Qed.

(* Corollary of the order face: Q >= 0 whenever 0 <= t, the directly usable form on the integration interval [0,1]. *)
Lemma lnt_pq_ge0_pos : forall n M t, Qle 0 t -> QleT' 0 (lnt_pq n M t).
Proof.
  intros n M t H. apply lnt_pq_ge0.
  assert (H1 : Qle 0 (1 + t)).
  { unfold Qle in *. cbn [Qnum Qden Qplus Qopp Qmult] in *. lia. }
  exact H1.
Qed.

(* ============================================================ *)
(* Section 5. Numerical cross-checks: vm_compute recomputation guarding the definitional faces                    *)
(* ============================================================ *)

(* B(1,1,1/2) = C(1,1) - C(2,1) (1/2) = 1 - 1 = 0. *)
Lemma lnt_ps_anchor1 : lnt_ps 1 1 (1 # 2) == 0.
Proof. vm_compute. reflexivity. Qed.

(* Q(1,1,1/2) = C(1,0) + C(2,1) (3/2) = 1 + 3 = 4. *)
Lemma lnt_pq_anchor1 : lnt_pq 1 1 (1 # 2) == 4.
Proof. vm_compute. reflexivity. Qed.

(* Instance of the master identity: (3/2)^2 times 0 plus (1/4) times 4 equals 1. *)
Lemma lnt_master_anchor1 :
  q_pow (1 + (1 # 2)) 2 * lnt_ps 1 1 (1 # 2)
  + q_pow (0 - (1 # 2)) 2 * lnt_pq 1 1 (1 # 2) == 1.
Proof. vm_compute. reflexivity. Qed.

(* ============================================================ *)
(* Section 6. Closedness self-check of the main statements                                            *)
(* ============================================================ *)

Print Assumptions lnt_one_pt_bridge.
Print Assumptions lnt_ps_unfold.
Print Assumptions lnt_psu_unfold.
Print Assumptions lnt_ps_geom.
Print Assumptions lnt_ps_pascal.
Print Assumptions lnt_pq_step.
Print Assumptions lnt_shift.
Print Assumptions lnt_shift_su.
Print Assumptions lnt_master.
Print Assumptions lnt_remainder_sep.
Print Assumptions lnt_pq_ge0.
Print Assumptions lnt_pq_ge0_pos.
Print Assumptions lnt_ps_anchor1.
Print Assumptions lnt_pq_anchor1.
Print Assumptions lnt_master_anchor1.

(* ============================================================ *)
(* Section 7. Parity faces of the sign of the remainder                                       *)
(* ============================================================ *)

(* Even-power change of variables: (0-t)^(2k) = t^(2k), by induction on k. *)
Lemma lnt_qpow_opp_even : forall (t : Q) (k : nat),
  q_pow (0 - t) (k + k) == q_pow t (k + k).
Proof.
  intros t k. induction k as [| k IH].
  - reflexivity.
  - replace (Datatypes.S k + Datatypes.S k)%nat
      with (Datatypes.S (Datatypes.S (k + k)))%nat by lia.
    cbn [q_pow]. rewrite IH. ring.
Qed.

(* Odd-power change of variables: (0-t)^(2k+1) = -t^(2k+1), derived in one step from the even-power face. *)
Lemma lnt_qpow_opp_odd : forall (t : Q) (k : nat),
  q_pow (0 - t) (Datatypes.S (k + k)) == 0 - q_pow t (Datatypes.S (k + k)).
Proof.
  intros t k.
  rewrite (qeqT_imp_qeq _ _ (q_pow_succ (0 - t) (k + k))).
  rewrite (qeqT_imp_qeq _ _ (q_pow_succ t (k + k))).
  rewrite (lnt_qpow_opp_even t k). ring.
Qed.

(* Odd M face (M = 2k+1): the remainder sign is positive, 1 - (1+t)^(n+1) B = t^(2k+2) Q. *)
Lemma lnt_rem_sign_odd : forall (n k : nat) (t : Q),
  1 - q_pow (1 + t) (Datatypes.S n) * lnt_ps n (Datatypes.S k + k) t
  == q_pow t (Datatypes.S (Datatypes.S (k + k)))
     * lnt_pq n (Datatypes.S k + k) t.
Proof.
  intros n k t.
  transitivity (q_pow (0 - t) (Datatypes.S (Datatypes.S (k + k)))
                * lnt_pq n (Datatypes.S k + k) t)%Q.
  - rewrite <- (lnt_remainder_sep n (Datatypes.S k + k) t). reflexivity.
  - replace (Datatypes.S (Datatypes.S (k + k)))%nat
      with (Datatypes.S k + Datatypes.S k)%nat by lia.
    rewrite (lnt_qpow_opp_even t (Datatypes.S k)). reflexivity.
Qed.

(* Even M face (M = 2k): the remainder sign is negative, 1 - (1+t)^(n+1) B = -t^(2k+1) Q. *)
Lemma lnt_rem_sign_even : forall (n k : nat) (t : Q),
  1 - q_pow (1 + t) (Datatypes.S n) * lnt_ps n (k + k) t
  == (0 - q_pow t (Datatypes.S (k + k))) * lnt_pq n (k + k) t.
Proof.
  intros n k t.
  transitivity (q_pow (0 - t) (Datatypes.S (k + k)) * lnt_pq n (k + k) t)%Q.
  - rewrite <- (lnt_remainder_sep n (k + k) t). reflexivity.
  - rewrite (lnt_qpow_opp_odd t k). reflexivity.
Qed.

(* ============================================================ *)
(* Section 8. Upper bounds for the truncation sums, split by the parity of M                                    *)
(* ============================================================ *)

(* Left-endpoint change of variables for the Set-level order witness, dual to the right-endpoint form zb2_qleT'_wd_r. *)
Lemma lnt_qleT'_wd_l : forall x y z : Q, x == y -> QleT' y z -> QleT' x z.
Proof.
  intros x y z Hxy Hy. apply Qle_to_QleT'.
  apply (Qle_trans x y z).
  - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. exact Hxy.
  - apply QleT'_to_Qle. exact Hy.
Qed.

(* Unit bound for powers: 0 <= t <= 1 implies t^m <= 1, by induction on m. *)
Lemma lnt_qpow_le_one : forall (t : Q) (m : nat), Qle 0 t -> Qle t 1 ->
  QleT' (q_pow t m) 1.
Proof.
  intros t m H0 H1. induction m as [| m IH].
  - apply qleT'_refl.
  - change (q_pow t (Datatypes.S m)) with (t * q_pow t m)%Q.
    assert (Hu : Qle (q_pow t m) 1) by (apply QleT'_to_Qle; exact IH).
    assert (Hq0 : Qle 0 (q_pow t m))
      by (apply QleT'_to_Qle; apply (q_pow_nonneg t m); apply Qle_to_QleT'; exact H0).
    assert (Hstep : QleT' (t * q_pow t m) (q_pow t m * 1)).
    { apply (zb2_qleT'_wd_r (1 * q_pow t m)%Q (q_pow t m * 1)%Q (t * q_pow t m)%Q).
      - ring.
      - apply Qle_to_QleT'. exact (Qmult_le_compat_r t 1 (q_pow t m) H1 Hq0). }
    apply (qleT'_trans (t * q_pow t m) (q_pow t m * 1) 1 Hstep).
    apply (zb2_qleT'_wd_r (1 * 1)%Q 1 (q_pow t m * 1)%Q).
    + ring.
    + apply Qle_to_QleT'.
      exact (Qmult_le_compat_r (q_pow t m) 1 1 Hu (QleT'_to_Qle _ _ Qle_0_1)).
Qed.

(* The correction term is controlled: 1 + t^(M+1) Q <= 1 + Q, for 0 <= t <= 1 and Q >= 0. *)
Lemma lnt_ps_ub_shift : forall (n M : nat) (t : Q), Qle 0 t -> Qle t 1 ->
  QleT' (1 + q_pow t (Datatypes.S M) * lnt_pq n M t) (1 + lnt_pq n M t).
Proof.
  intros n M t H0 H1.
  apply (zb2_qleT'_wd_r (1 + 1 * lnt_pq n M t)%Q (1 + lnt_pq n M t)%Q
                        (1 + q_pow t (Datatypes.S M) * lnt_pq n M t)%Q).
  - ring.
  - apply qleT'_plus_compat.
    + apply qleT'_refl.
    + apply (qleT'_mult_compat_r (q_pow t (Datatypes.S M)) 1 (lnt_pq n M t)).
      * exact (lnt_pq_ge0_pos n M t H0).
      * apply lnt_qpow_le_one; assumption.
Qed.

(* Direct upper bound in the odd M face: the remainder t^(2k+2) Q >= 0 gives (1+t)^(n+1) B <= 1. *)
Lemma lnt_ps_ub_direct : forall (n k : nat) (t : Q), Qle 0 t ->
  QleT' (q_pow (1 + t) (Datatypes.S n) * lnt_ps n (Datatypes.S k + k) t) 1.
Proof.
  intros n k t Ht.
  apply (zb2_qleT'_wd_r
           (q_pow (1 + t) (Datatypes.S n) * lnt_ps n (Datatypes.S k + k) t
            + q_pow t (Datatypes.S (Datatypes.S (k + k)))
              * lnt_pq n (Datatypes.S k + k) t)%Q 1
           (q_pow (1 + t) (Datatypes.S n) * lnt_ps n (Datatypes.S k + k) t)).
  - rewrite <- (lnt_rem_sign_odd n k t). ring.
  - apply qleT'_plus_nonneg_rT. apply Qle_to_QleT'. apply Qmult_le_0_compat.
    + apply QleT'_to_Qle. apply (q_pow_nonneg t (Datatypes.S (Datatypes.S (k + k)))).
      apply Qle_to_QleT'. exact Ht.
    + apply QleT'_to_Qle. apply lnt_pq_ge0_pos. exact Ht.
Qed.

(* Corrected upper bound in the even M face: the remainder -t^(2k+1) Q <= 0
   voids the direct bound, and instead (1+t)^(n+1) B <= 1 + Q holds. *)
Lemma lnt_ps_ub_qabs : forall (n k : nat) (t : Q), Qle 0 t -> Qle t 1 ->
  QleT' (q_pow (1 + t) (Datatypes.S n) * lnt_ps n (k + k) t)
        (1 + lnt_pq n (k + k) t).
Proof.
  intros n k t H0 H1.
  apply (lnt_qleT'_wd_l
           (q_pow (1 + t) (Datatypes.S n) * lnt_ps n (k + k) t)
           (1 + q_pow t (Datatypes.S (k + k)) * lnt_pq n (k + k) t)%Q
           (1 + lnt_pq n (k + k) t)).
  - transitivity (1 - (0 - q_pow t (Datatypes.S (k + k))) * lnt_pq n (k + k) t)%Q.
    + rewrite <- (lnt_rem_sign_even n k t). ring.
    + ring.
  - exact (lnt_ps_ub_shift n (k + k) t H0 H1).
Qed.

(* ============================================================ *)
(* Section 9. The M-uniform form of the absolute value of the remainder                                         *)
(* ============================================================ *)

(* Absolute value of a negated power: the absolute value of (0-t)^m is t^m for t >= 0, by induction on m. *)
Lemma lnt_qabs_opp_pow : forall (t : Q) (m : nat), Qle 0 t ->
  Qabs (q_pow (0 - t) m) == q_pow t m.
Proof.
  intros t m Ht. induction m as [| m IH].
  - apply Qabs_pos. apply QleT'_to_Qle. apply Qle_0_1.
  - change (q_pow (0 - t) (Datatypes.S m)) with ((0 - t) * q_pow (0 - t) m)%Q.
    change (q_pow t (Datatypes.S m)) with (t * q_pow t m)%Q.
    rewrite (Qabs_Qmult (0 - t) (q_pow (0 - t) m)). rewrite IH.
    assert (Ha : Qabs (0 - t) == t).
    { transitivity (Qabs (- t))%Q.
      - apply (Qabs_wd (0 - t) (- t)). ring.
      - rewrite (Qabs_opp t). apply Qabs_pos. exact Ht. }
    rewrite Ha. reflexivity.
Qed.

(* The M-uniform absolute-value identity for the remainder: the absolute value
   of 1 - (1+t)^(n+1) B is t^(M+1) Q for t >= 0; the alternation of the sign
   with the parity of M dissolves inside the absolute value. *)
Lemma lnt_rem_abs : forall (n M : nat) (t : Q), Qle 0 t ->
  Qabs (1 - q_pow (1 + t) (Datatypes.S n) * lnt_ps n M t)
  == q_pow t (Datatypes.S M) * lnt_pq n M t.
Proof.
  intros n M t Ht.
  transitivity (Qabs (q_pow (0 - t) (Datatypes.S M) * lnt_pq n M t))%Q.
  - apply (Qabs_wd (1 - q_pow (1 + t) (Datatypes.S n) * lnt_ps n M t)
                   (q_pow (0 - t) (Datatypes.S M) * lnt_pq n M t)
                   (lnt_remainder_sep n M t)).
  - rewrite (Qabs_Qmult (q_pow (0 - t) (Datatypes.S M)) (lnt_pq n M t)).
    rewrite (lnt_qabs_opp_pow t (Datatypes.S M) Ht).
    assert (Hq : Qabs (lnt_pq n M t) == lnt_pq n M t)
      by (apply Qabs_pos; apply QleT'_to_Qle; apply lnt_pq_ge0_pos; exact Ht).
    rewrite Hq. reflexivity.
Qed.

(* ============================================================ *)
(* Section 10. Closedness self-check of the additional main statements                                      *)
(* ============================================================ *)

Print Assumptions lnt_qpow_opp_even.
Print Assumptions lnt_qpow_opp_odd.
Print Assumptions lnt_rem_sign_odd.
Print Assumptions lnt_rem_sign_even.
Print Assumptions lnt_qleT'_wd_l.
Print Assumptions lnt_qpow_le_one.
Print Assumptions lnt_ps_ub_shift.
Print Assumptions lnt_ps_ub_direct.
Print Assumptions lnt_ps_ub_qabs.
Print Assumptions lnt_qabs_opp_pow.
Print Assumptions lnt_rem_abs.

(* ============================================================ *)
(* Section 11. The integral face and the decay face, closed-form constants for the kernel on [0,1]                               *)
(* ============================================================ *)

(* Section 11.0, the integral face on the PolyIntegral base: the integral mass
   of the decay kernel t^(M+1) over [0,1] equals 1/(M+2) explicitly. The
   integral base of the development covers the polynomial face, pint_integral
   with the correctness of the integral of x^k = 1/(k+1) on record; rational
   integrands lie outside its domain, so the decay face carries the integral
   as an explicit upper-bound constant: the closed form c(n) = (n!)^2/(2n+1)!
   is used directly (Sections 11.1-11.2), avoiding an integral construction. *)
Lemma lnt_kernel_mass : forall M : nat,
  QeqT (pint_integral (pint_pow_poly (Datatypes.S M)))
       (1 / (Z.of_nat (Datatypes.S (Datatypes.S M)) # 1)).
Proof. intro M. exact (pint_integral_pow_poly (Datatypes.S M)). Qed.

Lemma lnt_kernel_mass_Q : forall M : nat,
  pint_integral (pint_pow_poly (Datatypes.S M))
  == 1 / (Z.of_nat (Datatypes.S (Datatypes.S M)) # 1).
Proof. intro M. apply qeqT_imp_qeq. exact (lnt_kernel_mass M). Qed.

(* Section 11.1, the closed-form decay constants: cden n = (2n+1) C(2n,n) and
   cfac n = 1/cden n, the closed value (n!)^2/(2n+1)! of the Beukers kernel,
   the integral of t^n(1-t)^n over [0,1]. *)
Definition lnt_cden (n : nat) : nat := (2 * n + 1) * bkC (n + n) n.
Definition lnt_cfac (n : nat) : Q := Qinv ((Z.of_nat (lnt_cden n)) # 1)%Q.

(* Pascal doubling: C(2n+2,n+1) >= 2 C(2n,n). *)
Lemma lnt_binom_double : forall n : nat,
  (2 * bkC (n + n) n
   <= bkC (Datatypes.S (Datatypes.S (n + n))) (Datatypes.S n))%nat.
Proof.
  intro n. destruct n as [| n].
  - cbn. lia.
  - assert (Hp : (bkC (Datatypes.S (Datatypes.S (Datatypes.S n + Datatypes.S n)))
                   (Datatypes.S (Datatypes.S n))
                  = bkC (Datatypes.S (Datatypes.S n + Datatypes.S n))
                    (Datatypes.S n)
                  + bkC (Datatypes.S (Datatypes.S n + Datatypes.S n))
                    (Datatypes.S (Datatypes.S n)))%nat).
    { rewrite (bkC_pascal_shift (Datatypes.S (Datatypes.S n + Datatypes.S n))
                 (Datatypes.S (Datatypes.S n))). reflexivity. }
    rewrite Hp.
    assert (Hr : (bkC (Datatypes.S (Datatypes.S n + Datatypes.S n))
                   (Datatypes.S (Datatypes.S n))
                 = bkC (Datatypes.S n + Datatypes.S n) (Datatypes.S n)
                   + bkC (Datatypes.S n + Datatypes.S n)
                     (Datatypes.S (Datatypes.S n)))%nat).
    { rewrite (bkC_pascal_shift (Datatypes.S n + Datatypes.S n)
                 (Datatypes.S (Datatypes.S n))). reflexivity. }
    rewrite Hr.
    assert (Hq : (bkC (Datatypes.S (Datatypes.S n + Datatypes.S n))
                   (Datatypes.S n)
                 = bkC (Datatypes.S n + Datatypes.S n) n
                   + bkC (Datatypes.S n + Datatypes.S n) (Datatypes.S n))%nat).
    { rewrite (bkC_pascal_shift (Datatypes.S n + Datatypes.S n)
                 (Datatypes.S n)). reflexivity. }
    rewrite Hq. lia.
Qed.

(* C(2n,n) >= 2^n. *)
Lemma lnt_binom_ge_pow2 : forall n : nat, (2 ^ n <= bkC (n + n) n)%nat.
Proof.
  intro n. induction n as [| n IH].
  - cbn. lia.
  - assert (Hd := lnt_binom_double n).
    replace (Datatypes.S n + Datatypes.S n)%nat
      with (Datatypes.S (Datatypes.S (n + n)))%nat in Hd by lia.
    replace (Datatypes.S n + Datatypes.S n)%nat
      with (Datatypes.S (Datatypes.S (n + n)))%nat by lia.
    replace (2 ^ Datatypes.S n)%nat with (2 * 2 ^ n)%nat
      by (apply eq_sym; apply Nat.pow_succ_r').
    apply Nat.le_trans with (m := (2 * bkC (n + n) n)%nat).
    + apply Nat.mul_le_mono.
      * lia.
      * exact IH.
    + exact Hd.
Qed.

(* cden n >= 1. *)
Lemma lnt_cden_1 : forall n : nat, (1 <= lnt_cden n)%nat.
Proof.
  intro n. unfold lnt_cden.
  assert (Hb : (1 <= bkC (n + n) n)%nat)
    by (apply NatLe_drop; apply bkC_pos; apply NatLe_lift; lia).
  assert (Hp : (1 * bkC (n + n) n <= (2 * n + 1) * bkC (n + n) n)%nat)
    by (apply Nat.mul_le_mono; lia).
  assert (Hr : (1 * bkC (n + n) n = bkC (n + n) n)%nat) by ring.
  lia.
Qed.

(* cden n >= 2^n. *)
Lemma lnt_cden_ge_pow2 : forall n : nat, (2 ^ n <= lnt_cden n)%nat.
Proof.
  intro n. unfold lnt_cden.
  apply Nat.le_trans with (m := (bkC (n + n) n)%nat).
  - apply lnt_binom_ge_pow2.
  - assert (Hm : (1 * bkC (n + n) n <= (2 * n + 1) * bkC (n + n) n)%nat)
      by (apply Nat.mul_le_mono; lia).
    transitivity ((1 * bkC (n + n) n)%nat).
    + lia.
    + exact Hm.
Qed.

(* The Q-image of cden is positive, the QltT face. *)
Lemma lnt_cden_Qpos : forall n : nat, QltT 0 ((Z.of_nat (lnt_cden n)) # 1)%Q.
Proof.
  intro n. apply Qlt_to_QltT. unfold Qlt. cbn [Qnum Qden].
  assert (H := lnt_cden_1 n). lia.
Qed.

(* cfac n = 1/cden n is positive. *)
Lemma lnt_cfac_pos : forall n : nat, QltT 0 (lnt_cfac n).
Proof.
  intro n. apply Qlt_to_QltT. apply Qinv_lt_0_compat.
  apply QltT_to_Qlt. apply lnt_cden_Qpos.
Qed.

(* 2^n >= 1. *)
Lemma lnt_pow2_ge1 : forall n : nat, (1 <= 2 ^ n)%nat.
Proof.
  intro n. induction n as [| n IH].
  - cbn. lia.
  - rewrite Nat.pow_succ_r'. lia.
Qed.

(* Product identity bridge for (1/2)^n: q_pow (1/2) n and 2^n are mutually inverse. *)
Lemma lnt_qpow_half_inv : forall n : nat,
  q_pow (1 # 2)%Q n * ((Z.of_nat (2 ^ n)) # 1)%Q == (1 # 1)%Q.
Proof.
  intro n. induction n as [| n IH].
  - reflexivity.
  - rewrite (qeqT_imp_qeq _ _ (q_pow_succ (1 # 2) n)).
    assert (E2 : ((Z.of_nat (2 ^ Datatypes.S n)) # 1)%Q
                 == ((2 # 1) * ((Z.of_nat (2 ^ n)) # 1))%Q).
    { replace (Z.of_nat (2 ^ Datatypes.S n))%Z
        with (2 * Z.of_nat (2 ^ n))%Z
        by (rewrite Nat.pow_succ_r'; rewrite Nat2Z.inj_mul; reflexivity).
      reflexivity. }
    rewrite E2.
    transitivity (((1 # 2) * (2 # 1))%Q
                  * (q_pow (1 # 2)%Q n * ((Z.of_nat (2 ^ n)) # 1)%Q))%Q.
    + ring.
    + rewrite IH. ring.
Qed.

(* Upper bound: cfac n = 1/cden n <= (1/2)^n, by the double-inverse reversal: D2 <= D implies 1/D <= 1/D2. *)
Lemma lnt_cfac_budget : forall n : nat,
  QleT' (lnt_cfac n) (q_pow (1 # 2)%Q n).
Proof.
  intro n. apply Qle_to_QleT'. unfold lnt_cfac.
  assert (Hle : Qle ((Z.of_nat (2 ^ n)) # 1) ((Z.of_nat (lnt_cden n)) # 1)).
  { unfold Qle. cbn [Qnum Qden].
    assert (Hn := lnt_cden_ge_pow2 n). lia. }
  assert (HD2pos : Qlt 0 ((Z.of_nat (2 ^ n)) # 1)).
  { unfold Qlt. cbn [Qnum Qden].
    assert (Hp1 := lnt_pow2_ge1 n). lia. }
  set (D := ((Z.of_nat (lnt_cden n)) # 1)%Q) in *.
  assert (HD2ne : ~ (((Z.of_nat (2 ^ n)) # 1)%Q == 0%Q)).
  { intro He. apply (Qlt_not_eq 0 ((Z.of_nat (2 ^ n)) # 1)%Q).
    - exact HD2pos.
    - apply Qeq_sym. exact He. }
  assert (Einv2 : ((Z.of_nat (2 ^ n)) # 1)%Q
                  * Qinv ((Z.of_nat (2 ^ n)) # 1)%Q == 1%Q)
    by (apply Qmult_inv_r; exact HD2ne).
  assert (HDne : ~ (D == 0%Q)).
  { intro He.
    apply (Qlt_not_eq 0 D).
    - apply QltT_to_Qlt. apply lnt_cden_Qpos.
    - apply Qeq_sym. exact He. }
  assert (EinvD : D * Qinv D == 1%Q) by (apply Qmult_inv_r; exact HDne).
  assert (Eform := lnt_qpow_half_inv n).
  assert (Ew : q_pow (1 # 2)%Q n == Qinv ((Z.of_nat (2 ^ n)) # 1)%Q).
  { transitivity (q_pow (1 # 2)%Q n
                  * (((Z.of_nat (2 ^ n)) # 1)%Q
                     * Qinv ((Z.of_nat (2 ^ n)) # 1)%Q))%Q.
    - rewrite Einv2. ring.
    - rewrite (Qmult_assoc (q_pow (1 # 2)%Q n) ((Z.of_nat (2 ^ n)) # 1)
                (Qinv ((Z.of_nat (2 ^ n)) # 1))).
      rewrite Eform. ring. }
  rewrite Ew.
  set (D2 := ((Z.of_nat (2 ^ n)) # 1)%Q) in *.
  assert (Hpr : Qle 0 (Qinv D2 * Qinv D)).
  { apply Qmult_le_0_compat.
    - apply Qlt_le_weak. apply Qinv_lt_0_compat. exact HD2pos.
    - apply Qlt_le_weak. apply Qinv_lt_0_compat. apply QltT_to_Qlt.
      apply lnt_cden_Qpos. }
  assert (Hmul := Qmult_le_compat_r D2 D (Qinv D2 * Qinv D) Hle Hpr).
  apply (Qle_trans (Qinv D) (D2 * (Qinv D2 * Qinv D))%Q).
  - assert (Ech : (Qinv D == D2 * (Qinv D2 * Qinv D))%Q).
    { rewrite (Qmult_assoc D2 (Qinv D2) (Qinv D)). rewrite Einv2. ring. }
    exact (QleT'_to_Qle _ _ (qeq_imp_qle _ _ (qeq_imp_qeqT _ _ Ech))).
  - apply (Qle_trans (D2 * (Qinv D2 * Qinv D))%Q
             (D * (Qinv D2 * Qinv D))%Q).
    + exact Hmul.
    + assert (Ech2 : (D * (Qinv D2 * Qinv D) == Qinv D2)%Q).
      { rewrite (Qmult_comm (Qinv D2) (Qinv D)).
        rewrite (Qmult_assoc D (Qinv D) (Qinv D2)).
        rewrite EinvD. ring. }
      exact (QleT'_to_Qle _ _ (qeq_imp_qle _ _ (qeq_imp_qeqT _ _ Ech2))).
Qed.

(* ============================================================ *)
(* Section 12. Closedness self-check of the Section 11 main statements                                      *)
(* ============================================================ *)

Print Assumptions lnt_kernel_mass.
Print Assumptions lnt_kernel_mass_Q.
Print Assumptions lnt_binom_double.
Print Assumptions lnt_binom_ge_pow2.
Print Assumptions lnt_cden_1.
Print Assumptions lnt_pow2_ge1.
Print Assumptions lnt_cden_ge_pow2.
Print Assumptions lnt_cden_Qpos.
Print Assumptions lnt_cfac_pos.
Print Assumptions lnt_qpow_half_inv.
Print Assumptions lnt_cfac_budget.

(* ============================================================ *)
(* Section 13. Supply-face preforms: theta alignment, integer carrier at t=1, explicit lower-bound sequences                 *)
(* ============================================================ *)

(* Alignment of the theta upper bound: the truncation-family bound (1/2)^n aligns with the supply-face tier (4/5)^n, by monotonicity of powers. *)
Lemma lnt_theta_align : forall n : nat,
  QleT' (q_pow (1 # 2)%Q n) (q_pow (4 # 5)%Q n).
Proof.
  intro n. apply (q_pow_mono (1 # 2) (4 # 5) n).
  - apply Qle_to_QleT'. unfold Qle. cbn [Qnum Qden]. lia.
  - apply Qle_to_QleT'. unfold Qle. cbn [Qnum Qden]. lia.
Qed.

(* Integer-carrier bridge at t=1: q_pow 2 n and the Q-image of 2^n agree
   pointwise. At t=1 the master identity reads (1+1)^(n+1) B(n,M,1) +
   (-1)^(M+1) Q(n,M,1) = 1, the integer-coefficient Bezout face; this bridge
   moves the power on the left to its Z-image carrier. *)
Lemma lnt_qpow_two_Z : forall n : nat,
  q_pow (1 + 1)%Q n == ((Z.of_nat (2 ^ n)) # 1)%Q.
Proof.
  intro n. induction n as [| n IH].
  - reflexivity.
  - rewrite (qeqT_imp_qeq _ _ (q_pow_succ (1 + 1) n)).
    replace ((Z.of_nat (2 ^ Datatypes.S n)) # 1)%Q
      with ((2 # 1) * ((Z.of_nat (2 ^ n)) # 1))%Q.
    + rewrite IH. ring.
    + replace (Z.of_nat (2 ^ Datatypes.S n))%Z
        with (2 * Z.of_nat (2 ^ n))%Z.
      * reflexivity.
      * rewrite Nat.pow_succ_r'. rewrite Nat2Z.inj_mul. reflexivity.
Qed.

(* Linear lower bound for 2^n: n + 1 <= 2^n, the nat-face engine behind the explicit lower-bound sequence. *)
Lemma lnt_pow2_ge_lin : forall n : nat, (Datatypes.S n <= 2 ^ n)%nat.
Proof.
  intro n. induction n as [| n IH].
  - cbn. lia.
  - rewrite Nat.pow_succ_r'. lia.
Qed.

(* Making the lower-bound sequence explicit: cfac n <= 1/(n+1). The chain is
   the upper bound cfac n <= (1/2)^n (lnt_cfac_budget), the product identity
   (1/2)^n = 1/2^n, and the double-inverse reversal: n+1 <= 2^n implies
   1/2^n <= 1/(n+1), with both endpoints positive. *)
Lemma lnt_cfac_le_inv : forall n : nat,
  QleT' (lnt_cfac n) (Qinv ((Z.of_nat (Datatypes.S n)) # 1)%Q).
Proof.
  intro n. apply Qle_to_QleT'. unfold lnt_cfac.
  assert (HD1pos : Qlt 0 ((Z.of_nat (Datatypes.S n)) # 1)%Q).
  { unfold Qlt. cbn [Qnum Qden]. lia. }
  assert (HD1ne : ~ (((Z.of_nat (Datatypes.S n)) # 1)%Q == 0%Q)).
  { intro He. apply (Qlt_not_eq 0 ((Z.of_nat (Datatypes.S n)) # 1)%Q).
    - exact HD1pos.
    - apply Qeq_sym. exact He. }
  assert (EinvD1 : ((Z.of_nat (Datatypes.S n)) # 1)%Q
                   * Qinv ((Z.of_nat (Datatypes.S n)) # 1)%Q == 1%Q)
    by (apply Qmult_inv_r; exact HD1ne).
  assert (HDcpos : Qlt 0 ((Z.of_nat (lnt_cden n)) # 1)%Q).
  { apply QltT_to_Qlt. apply lnt_cden_Qpos. }
  assert (HDcne : ~ (((Z.of_nat (lnt_cden n)) # 1)%Q == 0%Q)).
  { intro He. apply (Qlt_not_eq 0 ((Z.of_nat (lnt_cden n)) # 1)%Q).
    - exact HDcpos.
    - apply Qeq_sym. exact He. }
  assert (EinvDc : ((Z.of_nat (lnt_cden n)) # 1)%Q
                   * Qinv ((Z.of_nat (lnt_cden n)) # 1)%Q == 1%Q)
    by (apply Qmult_inv_r; exact HDcne).
  assert (Hle : Qle ((Z.of_nat (Datatypes.S n)) # 1)
                    ((Z.of_nat (lnt_cden n)) # 1)%Q).
  { unfold Qle. cbn [Qnum Qden].
    assert (Hl := lnt_pow2_ge_lin n).
    assert (Hc := lnt_cden_ge_pow2 n). lia. }
  assert (Hpr : Qle 0 (Qinv ((Z.of_nat (Datatypes.S n)) # 1)%Q
                        * Qinv ((Z.of_nat (lnt_cden n)) # 1)%Q)).
  { apply Qmult_le_0_compat.
    - apply Qlt_le_weak. apply Qinv_lt_0_compat. exact HD1pos.
    - apply Qlt_le_weak. apply Qinv_lt_0_compat. exact HDcpos. }
  assert (Hmul := Qmult_le_compat_r ((Z.of_nat (Datatypes.S n)) # 1)
                    ((Z.of_nat (lnt_cden n)) # 1)
                    (Qinv ((Z.of_nat (Datatypes.S n)) # 1)%Q
                     * Qinv ((Z.of_nat (lnt_cden n)) # 1)%Q) Hle Hpr).
  apply (Qle_trans (Qinv ((Z.of_nat (lnt_cden n)) # 1)%Q)
           (((Z.of_nat (Datatypes.S n)) # 1)%Q
             * (Qinv ((Z.of_nat (Datatypes.S n)) # 1)%Q
                * Qinv ((Z.of_nat (lnt_cden n)) # 1)%Q))%Q).
  - assert (Ech : (Qinv ((Z.of_nat (lnt_cden n)) # 1)%Q
                   == ((Z.of_nat (Datatypes.S n)) # 1)%Q
                      * (Qinv ((Z.of_nat (Datatypes.S n)) # 1)%Q
                         * Qinv ((Z.of_nat (lnt_cden n)) # 1)%Q))%Q).
    { rewrite (Qmult_assoc ((Z.of_nat (Datatypes.S n)) # 1)
                (Qinv ((Z.of_nat (Datatypes.S n)) # 1))
                (Qinv ((Z.of_nat (lnt_cden n)) # 1))).
      rewrite EinvD1. ring. }
    exact (QleT'_to_Qle _ _ (qeq_imp_qle _ _ (qeq_imp_qeqT _ _ Ech))).
  - apply (Qle_trans (((Z.of_nat (Datatypes.S n)) # 1)%Q
             * (Qinv ((Z.of_nat (Datatypes.S n)) # 1)%Q
                * Qinv ((Z.of_nat (lnt_cden n)) # 1)%Q))%Q
           (((Z.of_nat (lnt_cden n)) # 1)%Q
             * (Qinv ((Z.of_nat (Datatypes.S n)) # 1)%Q
                * Qinv ((Z.of_nat (lnt_cden n)) # 1)%Q))%Q).
    + exact Hmul.
    + assert (Ech2 : (((Z.of_nat (lnt_cden n)) # 1)%Q
                       * (Qinv ((Z.of_nat (Datatypes.S n)) # 1)%Q
                          * Qinv ((Z.of_nat (lnt_cden n)) # 1)%Q))%Q
                      == Qinv ((Z.of_nat (Datatypes.S n)) # 1)%Q).
      { rewrite (Qmult_comm (Qinv ((Z.of_nat (Datatypes.S n)) # 1))
                  (Qinv ((Z.of_nat (lnt_cden n)) # 1))).
        rewrite (Qmult_assoc ((Z.of_nat (lnt_cden n)) # 1)
                  (Qinv ((Z.of_nat (lnt_cden n)) # 1))
                  (Qinv ((Z.of_nat (Datatypes.S n)) # 1))).
        rewrite EinvDc. ring. }
      exact (QleT'_to_Qle _ _ (qeq_imp_qle _ _ (qeq_imp_qeqT _ _ Ech2))).
Qed.

(* ============================================================ *)
(* Section 14. Closedness self-check of the Section 13 main statements                                      *)
(* ============================================================ *)

Print Assumptions lnt_theta_align.
Print Assumptions lnt_qpow_two_Z.
Print Assumptions lnt_pow2_ge_lin.
Print Assumptions lnt_cfac_le_inv.
Require Import UpReqLn2Irrational.

(* ============================================================ *)
(* Section 15. The Bezout face at t=1, the algebraic body joining the truncation identity to the ln2 series            *)
(* ============================================================ *)

(* Unit face of powers: 1^m = 1, moving powers to their values at t=1. *)
Lemma lnt_qpow_one : forall m : nat, q_pow 1 m == 1.
Proof.
  intro m. induction m as [| m IH].
  - reflexivity.
  - rewrite (qeqT_imp_qeq _ _ (q_pow_succ 1 m)). rewrite IH. ring.
Qed.

(* Bezout face, odd tier: 2^(n+1) B(n,2k+1,1) + Q(n,2k+1,1) = 1, in Z-image
   carrier form. At t=1 the master identity gives (-1)^(2k+2) = 1 and moves
   2^(n+1) to its integer image: the integer Bezout relation behind the
   truncation value B(n,2k+1,1) = (1 - Q)/2^(n+1). *)
Lemma lnt_bezout_odd : forall (n k : nat),
  ((Z.of_nat (2 ^ Datatypes.S n)) # 1) * lnt_ps n (Datatypes.S k + k) 1
  + lnt_pq n (Datatypes.S k + k) 1 == 1.
Proof.
  intros n k.
  assert (E := lnt_master n (Datatypes.S k + k) 1).
  rewrite (lnt_qpow_two_Z (Datatypes.S n)) in E.
  replace (Datatypes.S (Datatypes.S k + k))%nat
    with (Datatypes.S k + Datatypes.S k)%nat in E by lia.
  rewrite (lnt_qpow_opp_even 1 (Datatypes.S k)) in E.
  rewrite (lnt_qpow_one (Datatypes.S k + Datatypes.S k)) in E.
  rewrite (Qmult_1_l (lnt_pq n (Datatypes.S k + k) 1)) in E.
  exact E.
Qed.

(* Bezout face, even tier: 2^(n+1) B(n,2k,1) - Q(n,2k,1) = 1, from
   (-1)^(2k+1) = -1. Reading the two tiers together: the truncation value is
   always a rational number with denominator 2^(n+1). *)
Lemma lnt_bezout_even : forall (n k : nat),
  ((Z.of_nat (2 ^ Datatypes.S n)) # 1) * lnt_ps n (k + k) 1
  + (0 - lnt_pq n (k + k) 1) == 1.
Proof.
  intros n k.
  assert (E := lnt_master n (k + k) 1).
  rewrite (lnt_qpow_two_Z (Datatypes.S n)) in E.
  rewrite (lnt_qpow_opp_odd 1 k) in E.
  rewrite (lnt_qpow_one (Datatypes.S (k + k))) in E.
  assert (Em : ((0 - 1) * lnt_pq n (k + k) 1)%Q
               == (0 - lnt_pq n (k + k) 1)) by ring.
  rewrite Em in E. exact E.
Qed.

(* Uniform absolute-value face on the right: the absolute value of
   1 - 2^(n+1) B(n,M,1) equals Q(n,M,1), in Z-image form uniform in M; the
   sign alternation with the parity of M dissolves inside the absolute value. *)
Lemma lnt_rem_abs_one : forall (n M : nat),
  Qabs (1 - ((Z.of_nat (2 ^ Datatypes.S n)) # 1) * lnt_ps n M 1)
  == lnt_pq n M 1.
Proof.
  intros n M.
  assert (E := lnt_rem_abs n M 1 (QleT'_to_Qle _ _ Qle_0_1)).
  rewrite (lnt_qpow_two_Z (Datatypes.S n)) in E.
  rewrite (lnt_qpow_one (Datatypes.S M)) in E.
  rewrite (Qmult_1_l (lnt_pq n M 1)) in E.
  exact E.
Qed.

(* Explicit gap lower bound on the right: Q(n,M,1) >= 1. The constant term of
   the remainder family at t=1 carries the base case, every term is
   nonnegative, and induction closes: the integer gap face saying that the
   truncation value differs from a multiple of 2^(n+1) by at least 1. *)
Lemma lnt_pq_one_ge1 : forall (n M : nat), QleT' 1 (lnt_pq n M 1).
Proof.
  intro n. induction n as [| n IH]; intro M.
  - unfold lnt_pq. unfold zb2_pq. cbn [bk_psQ q_pow]. rewrite Nat.add_0_r.
    replace (Z.of_nat (bkC M 0) # 1) with (1 # 1)%Q
      by (rewrite zb2_bkC_zero; reflexivity).
    apply (zb2_qleT'_wd_r 1 ((1 # 1) * 1)%Q 1).
    + ring.
    + apply qleT'_refl.
  - apply (zb2_qleT'_wd_r
             ((lnt_pq n M 1
               + (Z.of_nat (bkC (M + Datatypes.S n) (Datatypes.S n)) # 1)
                 * q_pow (1 + 1) (Datatypes.S n))%Q)
             (lnt_pq (Datatypes.S n) M 1) 1).
    + exact (Qeq_sym _ _ (lnt_pq_step n M 1)).
    + apply Qle_to_QleT'.
      apply (Qplus_le_compat 1 (lnt_pq n M 1) 0
               ((Z.of_nat (bkC (M + Datatypes.S n) (Datatypes.S n)) # 1)
                * q_pow (1 + 1) (Datatypes.S n))).
      * exact (QleT'_to_Qle 1 (lnt_pq n M 1) (IH M)).
      * apply Qmult_le_0_compat.
        -- apply QleT'_to_Qle. apply zb2_bkC_Q_nonneg.
        -- assert (H01 : Qle 0 ((1 + 1)%Q)).
           ++ unfold Qle. cbn [Qnum Qden Qplus Qmult]. lia.
           ++ exact (QleT'_to_Qle _ _
                  (q_pow_nonneg (1 + 1) (Datatypes.S n) (Qle_to_QleT' _ _ H01))).
Qed.

(* Scale transfer for the k-th projection of the series: the absolute value of
   2^(n+1) x_k - 2^(n+1) B(n,M,1) equals 2^(n+1) times the absolute value of
   x_k - B(n,M,1), where x_k = ln2i_x k runs through the partial sums of the
   ln2 series. This splits the absolute value at the common scale 2^(n+1)
   between the truncation value and the series, preparing the supply side for
   line projections reading as the absolute value of A x - B. *)
Lemma lnt_ln2i_proj_gap : forall (n M k : nat),
  Qabs (((Z.of_nat (2 ^ Datatypes.S n)) # 1) * ln2i_x k
        - ((Z.of_nat (2 ^ Datatypes.S n)) # 1) * lnt_ps n M 1)
  == ((Z.of_nat (2 ^ Datatypes.S n)) # 1)
     * Qabs ((ln2i_x k - lnt_ps n M 1)%Q).
Proof.
  intros n M k.
  assert (Ha : Qle 0 ((Z.of_nat (2 ^ Datatypes.S n)) # 1)).
  { pose proof (ln2i_powZ_pos (Datatypes.S n)) as Hp.
    unfold Qle. cbn [Qnum Qden]. lia. }
  transitivity (Qabs (((Z.of_nat (2 ^ Datatypes.S n)) # 1)
                      * (ln2i_x k - lnt_ps n M 1)%Q))%Q.
  - apply (Qabs_wd (((Z.of_nat (2 ^ Datatypes.S n)) # 1) * ln2i_x k
                    - ((Z.of_nat (2 ^ Datatypes.S n)) # 1)
                      * lnt_ps n M 1)%Q
                   (((Z.of_nat (2 ^ Datatypes.S n)) # 1)
                    * (ln2i_x k - lnt_ps n M 1))%Q).
    ring.
  - rewrite (Qabs_Qmult ((Z.of_nat (2 ^ Datatypes.S n)) # 1)
              ((ln2i_x k - lnt_ps n M 1)%Q)).
    rewrite (Qabs_pos ((Z.of_nat (2 ^ Datatypes.S n)) # 1) Ha).
    reflexivity.
Qed.

(* ============================================================ *)
(* Section 16. Closedness self-check of the Section 15 main statements                                      *)
(* ============================================================ *)

Print Assumptions lnt_qpow_one.
Print Assumptions lnt_bezout_odd.
Print Assumptions lnt_bezout_even.
Print Assumptions lnt_rem_abs_one.
Print Assumptions lnt_pq_one_ge1.
Print Assumptions lnt_ln2i_proj_gap.
Require Import Ln2Bridge.

(* ============================================================ *)
(* Section 17. Transfer bridges for the eventual-slack form of real_le and line-projection docking faces of the truncation pairs                  *)
(* ============================================================ *)

(* Integer-carrier witness for the remainder family: Q(n,M,1) is always a
   rational number with denominator 1, a Z witness in the Set-level sigT.
   The induction face: the constant term is 1 and every term bkC times
   2^(n+1) is integral; rationals with denominator 1 are closed under
   addition and multiplication, as the Qmake arithmetic unfolds. *)
Lemma lnt_pq_zpair : forall (n M : nat),
  sigT (fun j : Z => lnt_pq n M 1 == (j # 1)%Q).
Proof.
  intro n. induction n as [| n IH]; intro M.
  - exists 1%Z. unfold lnt_pq. unfold zb2_pq. cbn [bk_psQ q_pow].
    rewrite Nat.add_0_r.
    replace (Z.of_nat (bkC M 0) # 1) with (1 # 1)%Q
      by (rewrite zb2_bkC_zero; reflexivity).
    ring.
  - destruct (IH M) as [j Hj].
    exists (j + Z.of_nat (bkC (M + Datatypes.S n) (Datatypes.S n))
              * Z.of_nat (2 ^ Datatypes.S n))%Z.
    rewrite (lnt_pq_step n M 1). rewrite Hj.
    rewrite (lnt_qpow_two_Z (Datatypes.S n)).
    unfold Qplus, Qmult, Qeq. cbn [Qnum Qden Pos.mul]. lia.
Qed.

(* Transfer bridge for the eventual-slack form of real_le, upper-bound
   direction: if the line-projection readings stay above the power constant
   by more than a positive e eventually and uniformly, then real_le takes
   the strict separation branch, assembled directly from the real_lt
   encoding. This is the last hop from the Q-level eventual face to a
   real_le statement. *)
Lemma lnt_line_upper_slack : forall (A B : nat -> Z) (n : nat) (th e : Q) (N : nat),
  QltT 0 e ->
  (forall k : nat, NatLe N k ->
    QltT e ((q_pow th n
             - Qabs (((A n) # 1)%Q * ln2i_x k - ((B n) # 1)%Q))%Q)) ->
  real_le (ln2b_line A B n) (real_const (q_pow th n)).
Proof.
  intros A B n th e N He0 Hface.
  left. unfold real_lt. exists e. split.
  - exact He0.
  - exists N. intros k Hk.
    apply Qlt_to_QltT.
    rewrite (qeqT_imp_qeq _ _ (real_const_proj (q_pow th n) k)).
    rewrite (qeqT_imp_qeq _ _ (ln2b_line_pt A B n k)).
    exact (QltT_to_Qlt _ _ (Hface k Hk)).
Qed.

(* Transfer bridge for the eventual-slack form of real_le, lower-bound
   direction: if the overshoot of the line-projection readings past the
   constant c stays above a positive e eventually and uniformly, then
   c <= the line takes the strict separation branch. *)
Lemma lnt_line_lower_slack : forall (A B : nat -> Z) (n : nat) (c e : Q) (N : nat),
  QltT 0 e ->
  (forall k : nat, NatLe N k ->
    QltT e ((Qabs (((A n) # 1)%Q * ln2i_x k - ((B n) # 1)%Q) - c)%Q)) ->
  real_le (real_const c) (ln2b_line A B n).
Proof.
  intros A B n c e N He0 Hface.
  left. unfold real_lt. exists e. split.
  - exact He0.
  - exists N. intros k Hk.
    apply Qlt_to_QltT.
    rewrite (qeqT_imp_qeq _ _ (real_const_proj c k)).
    rewrite (qeqT_imp_qeq _ _ (ln2b_line_pt A B n k)).
    exact (QltT_to_Qlt _ _ (Hface k Hk)).
Qed.

(* Line-projection identity, odd tier: for the truncation pair (2^(n+1), 1-j),
   with j the integer witness of Q(n,2k+1,1), the line-projection reading is
   exactly the scale-transfer form 2^(n+1) times the absolute value of
   x_k - B(n,2k+1,1). The chain: the Bezout face 2^(n+1) B + Q = 1 converts
   the integer witness into (1-j)#1 == 2^(n+1) B, and the scale-transfer face
   closes the argument. *)
Lemma lnt_line_truncdock_proj_odd : forall (n k : nat) (j : Z),
  lnt_pq n (Datatypes.S k + k) 1 == (j # 1)%Q ->
  projT1 (ln2b_line (fun _ : nat => (Z.of_nat (2 ^ Datatypes.S n))%Z)
                    (fun _ : nat => (1 - j)%Z) (Datatypes.S k + k)) k
  == ((Z.of_nat (2 ^ Datatypes.S n)) # 1)
     * Qabs ((ln2i_x k - lnt_ps n (Datatypes.S k + k) 1)%Q).
Proof.
  intros n k j Hj.
  assert (Ept := ln2b_line_pt (fun _ : nat => (Z.of_nat (2 ^ Datatypes.S n))%Z)
                              (fun _ : nat => (1 - j)%Z)
                              (Datatypes.S k + k) k).
  cbv beta in Ept. rewrite (qeqT_imp_qeq _ _ Ept).
  assert (Ebez := lnt_bezout_odd n k). rewrite Hj in Ebez.
  assert (E2 : ((Z.of_nat (2 ^ Datatypes.S n)) # 1)
               * lnt_ps n (Datatypes.S k + k) 1 == (1 - (j # 1))%Q).
  { transitivity ((((Z.of_nat (2 ^ Datatypes.S n)) # 1)
                   * lnt_ps n (Datatypes.S k + k) 1 + (j # 1))%Q
                  - (j # 1))%Q.
    - ring.
    - rewrite Ebez. ring. }
  assert (Ebr : (((1 - j)%Z) # 1)%Q == (1 - (j # 1))%Q)
    by (unfold Qminus, Qopp, Qplus, Qeq; cbn [Qnum Qden Pos.mul]; lia).
  rewrite Ebr. rewrite <- E2.
  exact (lnt_ln2i_proj_gap n (Datatypes.S k + k) k).
Qed.

(* Line-projection identity, even tier: for the truncation pair (2^(n+1), 1+j),
   with j the integer witness of Q(n,2k,1), the line-projection reading is
   exactly the scale-transfer form 2^(n+1) times the absolute value of
   x_k - B(n,2k,1); the even-tier Bezout face 2^(n+1) B - Q = 1 converts the
   integer witness into (1+j)#1 == 2^(n+1) B. *)
Lemma lnt_line_truncdock_proj_even : forall (n k : nat) (j : Z),
  lnt_pq n (k + k) 1 == (j # 1)%Q ->
  projT1 (ln2b_line (fun _ : nat => (Z.of_nat (2 ^ Datatypes.S n))%Z)
                    (fun _ : nat => (1 + j)%Z) (k + k)) k
  == ((Z.of_nat (2 ^ Datatypes.S n)) # 1)
     * Qabs ((ln2i_x k - lnt_ps n (k + k) 1)%Q).
Proof.
  intros n k j Hj.
  assert (Ept := ln2b_line_pt (fun _ : nat => (Z.of_nat (2 ^ Datatypes.S n))%Z)
                              (fun _ : nat => (1 + j)%Z) (k + k) k).
  cbv beta in Ept. rewrite (qeqT_imp_qeq _ _ Ept).
  assert (Ebez := lnt_bezout_even n k). rewrite Hj in Ebez.
  assert (E2 : ((Z.of_nat (2 ^ Datatypes.S n)) # 1)
               * lnt_ps n (k + k) 1 == (1 + (j # 1))%Q).
  { transitivity ((((Z.of_nat (2 ^ Datatypes.S n)) # 1)
                   * lnt_ps n (k + k) 1 + (0 - (j # 1)))%Q
                  + (j # 1))%Q.
    - ring.
    - rewrite Ebez. ring. }
  assert (Ebr : (((1 + j)%Z) # 1)%Q == (1 + (j # 1))%Q)
    by (unfold Qminus, Qopp, Qplus, Qeq; cbn [Qnum Qden Pos.mul]; lia).
  rewrite Ebr. rewrite <- E2.
  exact (lnt_ln2i_proj_gap n (k + k) k).
Qed.

(* ============================================================ *)
(* Section 18. Closedness self-check of the Section 17 main statements                                      *)
(* ============================================================ *)

Print Assumptions lnt_pq_zpair.
Print Assumptions lnt_line_upper_slack.
Print Assumptions lnt_line_lower_slack.
Print Assumptions lnt_line_truncdock_proj_odd.
Print Assumptions lnt_line_truncdock_proj_even.
