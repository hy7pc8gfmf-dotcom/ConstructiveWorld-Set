(* ================================================================== *)
(* ========================================================================= *)
(*  ArctanGeomTail - a geometric tail bound for arctan partial sums          *)
(* ========================================================================= *)

(** * ArctanGeomTail: geometric tail bound for arctan partial sums.

    Mission. [atg_tail_geom]: for [|x| < 1] (QltT, strict) and [m <= n],
    the difference of partial sums satisfies
    |S_n - S_m| <= c_{m+1} * 1/(1-x^2), where
    c_k := atan_mag k x = |x|^{2k+1}/(2k+1) and r := x*x.  The existing
    library only provides the slow harmonic bound atan_tail_bound_le
    (<= 1/(2m+3)); this file builds a genuine geometric ratio chain from the
    single-step ratio identity atan_mag_succ_geom.

    Dependencies. S01_BaseRing, S02_CauchyComplete, S03_QExp,
    S10_KVQuantTrig, S11_TP3B5; stdlib QArith, Qabs, Setoid, Lia.

    References. ConstructiveWorld-Main ConstructiveWorld_Live/ArctanGeomTail.v
    (statement names carried over verbatim).

    Constructivity. All statements are Set-carried (QltT in, QleT' out);
    proofs are Qed-closed with no axioms; the whole development stays in the
    rationals with no limits.  [Print Assumptions] on all statements reports
    a closed global context.

    Build. Rocq 9.1: [coqc -native-compiler no -q -Q . "" ArctanGeomTail.v].
 *)
(* ================================================================== *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Setoid.
From Stdlib Require Import Lia.

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.

(* ============================================================ *)
(* ===== Section 1. Normalization helpers (manual Qdiv/Qopp term ordering) ===== *)
(* ============================================================ *)

(* ---- |x|*|x| == x*x (squared absolute value; case on the sign of x) ---- *)
Lemma atg_sq_abs : forall x : Q, QeqT (Qabs x * Qabs x) (x * x).
Proof.
  intro x. apply qeq_imp_qeqT.
  destruct (Qlt_le_dec 0 x) as [Hpos | Hnonpos].
  - rewrite Qabs_pos by (apply Qlt_le_weak; exact Hpos). reflexivity.
  - rewrite Qabs_neg by exact Hnonpos. ring.
Qed.

(* ---- 0 < 1 (literal) ---- *)
Lemma atg_0_lt_1 : QltT 0 1.
Proof. apply Qlt_to_QltT. unfold Qlt; simpl; lia. Qed.

(* ---- y < 1 implies 0 < 1 - y (normalize through -y+y and -y+1) ---- *)
Lemma atg_one_minus_pos : forall y : Q, Qlt y 1 -> QltT 0 (1 - y).
Proof.
  intros y Hy.
  assert (Ht : QltT ((- y)%Q + y) ((- y)%Q + 1)).
  { apply (qleT'_plus_ltT_ltT ((- y)%Q) ((- y)%Q) y 1).
    - apply qleT'_refl.
    - apply Qlt_to_QltT. exact Hy. }
  assert (E1 : (- y)%Q + y == 0) by ring.
  assert (E2 : (1 - y)%Q == (- y)%Q + 1) by ring.
  exact (qltT_eq_compat_l ((- y)%Q + y) 0 (1 - y)%Q (qeq_imp_qeqT _ _ E1)
           (qltT_eq_compat_r (1 - y)%Q ((- y)%Q + 1) ((- y)%Q + y)
              (qeq_imp_qeqT _ _ E2) Ht)).
Qed.

(* ---- |x| < 1 implies x*x < 1 ---- *)
Lemma atg_absx_sq_lt : forall x : Q, Qlt (Qabs x) 1 -> QltT (x * x) 1.
Proof.
  intros x Hx.
  assert (Ha : Qle 0 (Qabs x)) by apply Qabs_nonneg.
  destruct (Qlt_le_dec 0 (Qabs x)) as [Hpos | Hge].
  - (* 0 < |x| < 1: |x|^2 < 1*|x| < 1*1 *)
    assert (Ht1 : QltT (Qabs x * Qabs x) (1 * Qabs x)).
    { apply (qltT_mult_ltT_compat_r (Qabs x) 1 (Qabs x)).
      - apply Qlt_to_QltT. exact Hpos.
      - apply Qlt_to_QltT. exact Hx. }
    assert (Ht2 : QltT (Qabs x * 1) (1 * 1)).
    { apply (qltT_mult_ltT_compat_r (Qabs x) 1 1).
      - exact atg_0_lt_1.
      - apply Qlt_to_QltT. exact Hx. }
    assert (E12 : Qabs x * 1 == 1 * Qabs x) by ring.
    assert (Ht3 : QltT (Qabs x * Qabs x) (1 * 1)).
    { apply (qleT'_ltT_ltT (Qabs x * Qabs x) (Qabs x * 1) (1 * 1)).
      - apply qltT_leT'.
        exact (qltT_eq_compat_r (Qabs x * 1) (1 * Qabs x)
                                (Qabs x * Qabs x) (qeq_imp_qeqT _ _ E12) Ht1).
      - exact Ht2. }
    apply (qltT_eq_compat_l (Qabs x * Qabs x) (x * x) 1).
    + exact (atg_sq_abs x).
    + apply (qltT_eq_compat_r (1 * 1) 1 (Qabs x * Qabs x)).
      * apply qeq_imp_qeqT. ring.
      * exact Ht3.
  - (* |x| = 0: x*x == 0 < 1 *)
    assert (HzeroQ : Qeq 0 (Qabs x)) by (apply Qle_antisym; [ exact Ha | exact Hge ]). 
    assert (E0 : 0 == x * x).
    { rewrite <- (qeqT_imp_qeq _ _ (atg_sq_abs x)). rewrite <- HzeroQ. ring. }
    apply (qltT_eq_compat_l 0 (x * x) 1).
    + exact (qeq_imp_qeqT _ _ E0).
    + exact atg_0_lt_1.
Qed.

(* ============================================================ *)
(* ===== Section 2. Monotone ratio control (engine: atan_mag_succ_geom) ===== *)
(* ============================================================ *)

(* ---- Single-step ratio: c_{k+1} <= r*c_k (needs only r = x^2 >= 0) ---- *)
Lemma atg_mag_ratio : forall (x : Q) (k : nat), Qle 0 (x * x) ->
  QleT' (atan_mag (Datatypes.S k) x) (x * x * atan_mag k x).
Proof.
  intros x k Hr0. apply Qle_to_QleT'.
  rewrite (qeqT_imp_qeq _ _ (atan_mag_succ_geom x k)).
  unfold atan_mag.
  assert (Ediv : x * x * (q_pow (Qabs x) (2 * k + 1) / (Z.of_nat (2 * k + 1) # 1)) ==
                 (x * x * q_pow (Qabs x) (2 * k + 1)) / (Z.of_nat (2 * k + 1) # 1))
    by (unfold Qdiv; ring).
  rewrite Ediv.
  apply QleT'_to_Qle.
  apply (q_le_div_le ((Qabs x * Qabs x) * q_pow (Qabs x) (2 * k + 1))
                     (Z.of_nat (2 * k + 3) # 1)
                     (x * x * q_pow (Qabs x) (2 * k + 1))
                     (Z.of_nat (2 * k + 1) # 1)).
  - apply Qlt_to_QltT. unfold Qlt; simpl; lia.
  - apply Qlt_to_QltT. unfold Qlt; simpl; lia.
  - (* (a^2*A)*d1 <= (x^2*A)*d2 with A := q_pow (Qabs x) (2k+1) >= 0 *)
    apply Qle_to_QleT'.
    apply (Qle_trans _ ((x * x * q_pow (Qabs x) (2 * k + 1)) *
                        (Z.of_nat (2 * k + 1) # 1)) _).
    + rewrite (qeqT_imp_qeq _ _ (atg_sq_abs x)). apply Qle_refl.
    + apply QleT'_to_Qle.
      apply (sc_qmult_le_l (Z.of_nat (2 * k + 1) # 1)
                           (Z.of_nat (2 * k + 3) # 1)
                           (x * x * q_pow (Qabs x) (2 * k + 1))).
      * unfold Qle; simpl; lia.
      * apply Qmult_le_0_compat.
        -- exact Hr0.
        -- apply QleT'_to_Qle. apply q_pow_nonneg.
           apply Qle_to_QleT'. apply Qabs_nonneg.
Qed.

(* ---- Ratio iteration: c_{m+j} <= r^j * c_m ---- *)
Lemma atg_mag_pow : forall (x : Q) (m j : nat), Qle 0 (x * x) ->
  QleT' (atan_mag ((m + j)%nat) x) (q_pow (x * x) j * atan_mag m x).
Proof.
  intros x m j Hr0. apply Qle_to_QleT'.
  induction j as [| j IH].
  - replace ((m + 0)%nat) with m by lia.
    replace (q_pow (x * x) 0%nat) with 1 by reflexivity.
    apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
  - replace ((m + Datatypes.S j)%nat) with (Datatypes.S ((m + j)%nat)) by lia.
    rewrite (qeqT_imp_qeq _ _ (q_pow_succ (x * x) j)).
    apply (Qle_trans _ ((x * x) * atan_mag ((m + j)%nat) x) _).
    + apply QleT'_to_Qle. apply atg_mag_ratio. exact Hr0.
    + apply (Qle_trans _ ((x * x) * (q_pow (x * x) j * atan_mag m x)) _).
      * apply QleT'_to_Qle.
        apply (sc_qmult_le_l (atan_mag ((m + j)%nat) x)
                             (q_pow (x * x) j * atan_mag m x) (x * x)).
        -- exact IH.
        -- exact Hr0.
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
Qed.

(* ============================================================ *)
(* ===== Section 3. General-base geometric sum: closed form and tail bound ===== *)
(* ============================================================ *)

Fixpoint atg_geo_fin (r : Q) (d : nat) : Q :=
  match d with
  | 0%nat => 0
  | Datatypes.S e => atg_geo_fin r e + q_pow r e
  end.

(* ---- Closed form: g_d*(1-r) == 1-r^d ---- *)
Lemma atg_geo_fin_closed : forall (r : Q) (d : nat),
  QeqT (atg_geo_fin r d * (1 - r)) (1 - q_pow r d).
Proof.
  intros r d. apply qeq_imp_qeqT.
  induction d as [| d IH].
  - replace (q_pow r 0%nat) with 1 by reflexivity.
    replace (atg_geo_fin r 0%nat) with 0 by reflexivity.
    ring.
  - change (atg_geo_fin r (Datatypes.S d) * (1 - r))
      with ((atg_geo_fin r d + q_pow r d) * (1 - r)).
    assert (Hd : (atg_geo_fin r d + q_pow r d) * (1 - r) ==
                 atg_geo_fin r d * (1 - r) + q_pow r d * (1 - r)) by ring.
    rewrite Hd.
    rewrite IH.
    rewrite (qeqT_imp_qeq _ _ (q_pow_succ r d)).
    ring.
Qed.

(* ---- Tail bound: 0 <= r and 0 < 1-r imply g_d <= 1/(1-r) ---- *)
Lemma atg_geo_fin_le_div : forall (r : Q) (d : nat), Qle 0 r -> Qlt 0 (1 - r) ->
  QleT' (atg_geo_fin r d) (1 / (1 - r)).
Proof.
  intros r d Hr0 Hr1pos. apply Qle_to_QleT'.
  assert (Hinv : Qinv 1 == 1) by reflexivity.
  assert (Hdiv1 : atg_geo_fin r d / 1 == atg_geo_fin r d).
  { unfold Qdiv. rewrite Hinv. apply Qmult_1_r. }
  apply (Qle_trans _ (atg_geo_fin r d / 1) _).
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
    exact (Qeq_sym (atg_geo_fin r d / 1) (atg_geo_fin r d) Hdiv1).
  - apply QleT'_to_Qle.
    apply (q_le_div_le (atg_geo_fin r d) 1 1 (1 - r)).
    + exact atg_0_lt_1.
    + exact (Qlt_to_QltT _ _ Hr1pos).
    + apply Qle_to_QleT'.
      apply (Qle_trans _ (1 - q_pow r d) _).
      * apply QleT'_to_Qle. apply qeq_le.
        exact (atg_geo_fin_closed r d).
      * apply (Qle_trans _ (1 - q_pow r d + q_pow r d) _).
        -- apply Qle_plus_nonneg_r.
           apply QleT'_to_Qle. apply q_pow_nonneg. apply Qle_to_QleT'.
           exact Hr0.
        -- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
Qed.

(* ============================================================ *)
(* ===== Section 4. Trigonometric plus geometric chain (engine: arctan_term_abs) ===== *)
(* ============================================================ *)

Lemma atg_tail_aux : forall (x : Q) (m d : nat), Qle 0 (x * x) ->
  QleT' (Qabs (arctan_partial ((m + d)%nat) x - arctan_partial m x))
      (atan_mag (Datatypes.S m) x * atg_geo_fin (x * x) d).
Proof.
  intros x m d Hr0. apply Qle_to_QleT'.
  induction d as [| d IH].
  - (* d = 0: |S_m - S_m| = 0 <= c_{m+1}*0 *)
    replace ((m + 0)%nat) with m by lia.
    replace (atg_geo_fin (x * x) 0%nat) with 0 by reflexivity.
    apply (Qle_trans _ 0 _).
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
      assert (Hz : arctan_partial m x - arctan_partial m x == 0) by ring.
      rewrite Hz. reflexivity.
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
  - (* d -> S d: triangle inequality, ratio iteration, one geometric step *)
    replace ((m + Datatypes.S d)%nat) with (Datatypes.S ((m + d)%nat)) by lia.
    assert (Hstep : arctan_partial (Datatypes.S ((m + d)%nat)) x ==
                    arctan_partial ((m + d)%nat) x +
                    arctan_term (Datatypes.S ((m + d)%nat)) x) by reflexivity.
    rewrite Hstep.
    setoid_replace ((arctan_partial ((m + d)%nat) x +
                     arctan_term (Datatypes.S ((m + d)%nat)) x) - arctan_partial m x)
      with ((arctan_partial ((m + d)%nat) x - arctan_partial m x) +
            arctan_term (Datatypes.S ((m + d)%nat)) x) by ring.
    apply (Qle_trans _ (Qabs (arctan_partial ((m + d)%nat) x - arctan_partial m x) +
                        Qabs (arctan_term (Datatypes.S ((m + d)%nat)) x)) _).
    + apply Qabs_triangle.
    + assert (Hp : Qle (atan_mag (Datatypes.S ((m + d)%nat)) x)
                       (q_pow (x * x) d * atan_mag (Datatypes.S m) x)).
      { replace (Datatypes.S ((m + d)%nat)) with (Datatypes.S m + d)%nat by lia.
        apply QleT'_to_Qle. apply atg_mag_pow. exact Hr0. }
      apply (Qle_trans _ (atan_mag (Datatypes.S m) x * atg_geo_fin (x * x) d +
                          atan_mag (Datatypes.S ((m + d)%nat)) x) _).
      * apply Qplus_le_compat.
        -- exact IH.
        -- apply QleT'_to_Qle. apply qeq_le.
          apply arctan_term_abs.
      * apply (Qle_trans _ (atan_mag (Datatypes.S m) x * atg_geo_fin (x * x) d +
                            q_pow (x * x) d * atan_mag (Datatypes.S m) x) _).
        -- apply Qplus_le_compat.
           ++ apply Qle_refl.
           ++ exact Hp.
        -- replace (atg_geo_fin (x * x) (Datatypes.S d))
             with (atg_geo_fin (x * x) d + q_pow (x * x) d) by reflexivity.
           apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
Qed.

(* ============================================================ *)
(* ===== Section 5. Main statement: geometric tail bound (QltT in, QleT' out) ===== *)
(* ============================================================ *)

Lemma atg_tail_geom : forall (x : Q) (m n : nat), QltT (Qabs x) 1 -> (m <= n)%nat ->
  QleT' (Qabs (arctan_partial n x - arctan_partial m x))
        (atan_mag (Datatypes.S m) x * (1 / (1 - x * x))).
Proof.
  intros x m n Hx Hmn.
  apply Qle_to_QleT'.
  assert (Hsq : Qle (x * x) 1)
    by (apply QleT'_to_Qle; apply atan_sq_le_one;
        apply (qltT_leT' (Qabs x) 1); exact Hx).
  assert (Hr0 : Qle 0 (x * x)) by (apply QleT'_to_Qle; apply Qsquare_nonneg).
  assert (Hlt : Qlt (x * x) 1)
    by (apply (QltT_to_Qlt (x * x) 1); apply atg_absx_sq_lt;
        apply (QltT_to_Qlt (Qabs x) 1); exact Hx).
  assert (Hr1 : Qlt 0 (1 - x * x))
    by (apply (QltT_to_Qlt 0 (1 - x * x)); apply atg_one_minus_pos; exact Hlt).
  apply (Qle_trans _ (atan_mag (Datatypes.S m) x *
                      atg_geo_fin (x * x) (n - m)%nat) _).
  - (* Main chain: |S_n - S_m| <= c_{m+1} * g_{n-m} *)
    remember (n - m)%nat as d eqn:Ed.
    assert (E : (m + d)%nat = n) by lia.
    rewrite <- E.
    apply QleT'_to_Qle. apply atg_tail_aux. exact Hr0.
  - (* Tail transfer: g_{n-m} <= 1/(1-r) gives c_{m+1}*g <= c_{m+1}/(1-r) *)
    apply QleT'_to_Qle.
    apply (sc_qmult_le_l (atg_geo_fin (x * x) (n - m)%nat) (1 / (1 - x * x))
                         (atan_mag (Datatypes.S m) x)).
    + apply QleT'_to_Qle. apply (atg_geo_fin_le_div (x * x) (n - m)%nat Hr0 Hr1).
    + apply QleT'_to_Qle. apply atan_mag_nonneg.
Qed.

(* ============================================================ *)
(* ===== Section 6. Assumption audit ===== *)
(* ============================================================ *)

Print Assumptions atg_tail_geom.
Print Assumptions atg_tail_aux.
Print Assumptions atg_mag_ratio.
Print Assumptions atg_mag_pow.
Print Assumptions atg_geo_fin_closed.
Print Assumptions atg_geo_fin_le_div.
