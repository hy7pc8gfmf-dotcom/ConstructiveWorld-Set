(* Five-field pointer | Module: piu1891_eggeom_release.v.
   Mission. Explicit literal witness separating cos_pi_half (the inner zero of pi over two,
   interval (3/2, 5/3)) from the literal 5/3: uniform-bound constant literal C := 8,
   half-ratio window level literal N := 10, separation eps := (1/400)/8 = 1/3200; the
   constant is doubled to lift to the separation between real_pi_geom and 10/3 (the
   eg-premise shape required at the LW0LeibSeparation leibsep_q_kernel site). Four
   statement layers: literal series uniform bound (B=2, C=8) -> Q-layer pointwise form
   (cos_zero_seq face) -> cos-layer real_lt wrapping -> real_pi_geom-layer real_lt form.
   Dependencies. Stdlib QArith/Qabs/Qminmax/Lia/ZArith/Arith/Lqa/Setoid; S01_BaseRing
   (NatLe/NatLe_drop); S02_CauchyComplete (QltT/real_lt/Qlt_to_QltT/Qle_to_QleT'/
   QleT'_to_Qle); S03_QExp (exp_series/q_pow/q_fact/exp_series_mono/exp_series_tail_le/
   exp_tail_abs_geom2); S07_RealSetoidExpLog (log_eps/log_eps_lt_delta/
   real_lt_mult_compat/real_const_lt); S10_KVQuantTrig (cos_zero_seq/cos_pi_half/
   real_pi_geom/sc_cos_zero_upper_margin_gen/cos_root_pt_bound/cos_zero_upper/
   cos_zero_abs_le_two/cos_pi_half_proj).
   References. S10_KVQuantTrig :9302 real_lt_cos_pi_half_five_thirds (its eps = (1/400)/C
   resolves C and window level N as existential witnesses; this piece fixes both
   literally as 8 and 9 via the explicit tail bound exp_tail_abs_geom2 and closed-form
   log_eps); S10 :9372 real_pi_geom_lt_ten_thirds (lifting chain copied verbatim).
   Constructivity. Assumption-free, free of classical logic; every exported statement
   closes under the global context. Uniform bound via the explicit tail-sum lemma
   exp_tail_abs_geom2 (no new induction); Q face an explicit chain (Qlt_trans/
   Qlt_minus_iff/Qlt_shift_div_l/q_neq_of_lt); closed Q leaves via vm_compute; nat face
   lia for auxiliary steps. Statement-face note: piu1891_exp2_tail_cond keeps its premise
   in bare nat-inequality form (5 <= t)%nat beside the migrated QleT' conclusion,
   verbatim as sourced; the other four stations carry canonical migrated faces.
   Build. rocq c -native-compiler no -q -Q . "" piu1891_eggeom_release.v in the flat
   world directory (born dependency closure); COQLIB/ROCQLIB unset; every launch under
   the thermal queue guard. Naming: piu1891_ prefix. *)

From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qminmax.
From Stdlib Require Import Lia ZArith Arith.Arith Lqa Setoid.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import S10_KVQuantTrig.

(* ========== Section 1: literal series uniform bound -- B=2 partial sums <= 8.
   exp_series mm 2 = sum over k <= mm of 2^k/k!; for mm >= 5 the tail-sum lemma
   exp_tail_abs_geom2 (A:=2, m:=5) bounds the tail by (2^5/5!)*2 = 8/15, while
   exp_series 5 2 = 109/15, so the total is 39/5 <= 8; for mm < 5 use
   monotonicity. ========== *)

Lemma piu1891_exp2_tail_cond : forall t : nat, (5 <= t)%nat ->
  QleT' ((1 + 1)%Q * 2%Q) ((Z.of_nat (t + 1) # 1)%Q).
Proof.
  intros t Ht.
  apply Qle_to_QleT'.
  change (Qle (4 # 1) ((Z.of_nat (t + 1) # 1)%Q)).
  assert (Hz : (4 <= Z.of_nat (t + 1))%Z) by (apply Z2Nat.inj_le; lia).
  unfold Qle. cbn [Qnum Qden]. lia.
Qed.

Theorem piu1891_exp_series2_le8 : forall mm : nat,
  QleT' (exp_series mm 2) (8 # 1)%Q.
Proof.
  intros mm.
  apply Qle_to_QleT'.
  assert (H02 : QleT' 0 2) by (apply Qle_to_QleT'; unfold Qle; cbn [Qnum Qden]; lia).
  assert (Hcond : forall t : nat, NatLe 5 t ->
           QleT' ((1 + 1)%Q * 2%Q) ((Z.of_nat (t + 1) # 1)%Q))
    by (intros t Ht; apply piu1891_exp2_tail_cond; apply NatLe_drop; exact Ht).
  destruct (Nat.leb 5 mm) eqn:E.
  - apply Nat.leb_le in E.
    assert (Hd : Qle (exp_series mm 2 - exp_series 5 2)
                     ((q_pow 2 5 / q_fact 5) * (1 + 1))%Q).
    { apply (Qle_trans _ (exp_tail_abs 5 mm 2)).
      - apply QleT'_to_Qle. apply (exp_series_tail_le 2 5 mm H02 E).
      - apply QleT'_to_Qle. apply (exp_tail_abs_geom2 2 5 mm H02 Hcond E). }
    apply (Qle_trans _ (exp_series 5 2 + (q_pow 2 5 / q_fact 5) * (1 + 1))%Q).
    + apply (proj2 (Qle_minus_iff (exp_series mm 2)
                    (exp_series 5 2 + (q_pow 2 5 / q_fact 5) * (1 + 1))%Q)).
      setoid_replace (exp_series 5 2 + (q_pow 2 5 / q_fact 5) * (1 + 1)
                      + -(exp_series mm 2))
        with ((q_pow 2 5 / q_fact 5) * (1 + 1)
              - (exp_series mm 2 - exp_series 5 2)) by ring.
      apply (proj1 (Qle_minus_iff (exp_series mm 2 - exp_series 5 2)
                                  ((q_pow 2 5 / q_fact 5) * (1 + 1)))).
      exact Hd.
    + vm_compute. discriminate.
  - apply Nat.leb_gt in E.
    apply (Qle_trans _ (exp_series 5 2)).
    + apply QleT'_to_Qle. apply (exp_series_mono 2 mm 5 H02). lia.
    + vm_compute. discriminate.
Qed.

(* ========== Section 2: Q-layer pointwise form, cos_zero_seq n < 5/3 - 1/3200
   for n >= 10. The half-ratio decay log_eps n = (1/2)^(S n) takes the literal
   level t := 9 ((1/2)^9 = 1/512 < 1/400); the margin lemma is instantiated at
   the literal C := 8, giving separation constant (1/400)/8 = 1/3200. ========== *)

Theorem piu1891_egcos_lit : forall n : nat, NatLe 10 n ->
  QltT (1 # 3200)%Q ((5 # 3)%Q - cos_zero_seq n)%Q.
Proof.
  assert (HC1 : QleT' 1 (8 # 1)%Q)
    by (apply Qle_to_QleT'; unfold Qle; cbn [Qnum Qden]; lia).
  assert (HC : forall mm : nat, QleT' (exp_series mm 2) (8 # 1)%Q)
    by (intros mm; apply piu1891_exp_series2_le8).
  assert (Ht : QltT (1 * q_pow (1 / 2)%Q 9) (1 / 400))
    by (apply Qlt_to_QltT; vm_compute; reflexivity).
  intros n Hn.
  assert (Hlog : Qlt (log_eps n) (1 / 400)).
  { apply QltT_to_Qlt.
    apply (log_eps_lt_delta (1 / 400) 9 n).
    - exact Ht.
    - apply NatLe_drop. exact Hn. }
  destruct (cos_root_pt_bound n) as [N1 HN1].
  set (k := Nat.max 4 N1).
  assert (Hk4 : (4 <= k)%nat) by (unfold k; apply Nat.le_max_l).
  assert (HkN1 : (N1 <= k)%nat) by (unfold k; apply Nat.le_max_r).
  assert (Hroot : Qlt (Qabs (cos_partial k (cos_zero_seq n) - 0)) (log_eps n))
    by (apply QltT_to_Qlt; apply (HN1 k (NatLe_lift _ _ HkN1))).
  assert (Hz53 : Qlt (cos_zero_seq n) (5 / 3)) by (apply QltT_to_Qlt; apply cos_zero_upper).
  assert (HzT : QleT' (Qabs (cos_zero_seq n)) 2)
    by (apply cos_zero_abs_le_two).
  assert (Hmgn : Qlt ((3 / 400) / (8 # 1)%Q) (5 / 3 - cos_zero_seq n)).
  { apply QltT_to_Qlt.
    apply (sc_cos_zero_upper_margin_gen (8 # 1)%Q n k (cos_zero_seq n)
           Hk4 HC1 HC Hlog HzT Hroot Hz53). }
  assert (Heps : Qlt (1 # 3200)%Q ((3 # 400)%Q / (8 # 1)%Q))
    by (vm_compute; reflexivity).
  assert (Hfinal : Qlt (1 # 3200)%Q (5 / 3 - cos_zero_seq n)).
  { apply (Qlt_trans _ ((3 # 400)%Q / (8 # 1)%Q)).
    - exact Heps.
    - exact Hmgn. }
  apply Qlt_to_QltT.
  exact Hfinal.
Qed.

(* ========== Section 3: real-layer wrapping and the real_pi_geom lifting form.
   The real_lt wrapping takes literal eps = 1/3200 and literal window level 10;
   the lifting chain follows S10 real_pi_geom_lt_ten_thirds verbatim
   (real_lt_mult_compat with multiplication by the constant real_const 2,
   paired with the pointwise equation 2*(5/3) == 10/3). ========== *)

Theorem piu1891_coshalf_lit : real_lt cos_pi_half (real_const (5 / 3)).
Proof.
  unfold real_lt.
  exists (1 # 3200)%Q.
  split.
  - apply Qlt_to_QltT. vm_compute. reflexivity.
  - exists 10%nat.
    intros n Hn.
    apply Qlt_to_QltT.
    setoid_replace (projT1 (real_const (5 / 3)) n - projT1 cos_pi_half n)
      with (5 / 3 - cos_zero_seq n).
    + apply (QltT_to_Qlt _ _). exact (piu1891_egcos_lit n Hn).
    + apply Qeq_sym.
      assert (Hp : projT1 cos_pi_half n == cos_zero_seq n)
        by (apply qeqT_imp_qeq; apply cos_pi_half_proj).
      assert (Hc : projT1 (real_const (5 / 3)) n == 5 / 3)
        by (apply (qeqT_imp_qeq _ _ (real_const_proj (5 / 3) n))).
      rewrite Hc. rewrite Hp. reflexivity.
Qed.

Theorem piu1891_eggeom_lit : real_lt real_pi_geom (real_const (10 / 3)).
Proof.
  unfold real_pi_geom.
  apply (real_lt_eq_lt _ (real_mult (real_const 2) (real_const (5 / 3))) _).
  - apply (real_lt_mult_compat cos_pi_half (real_const (5 / 3)) (real_const 2)).
    + apply real_const_lt. exact qltT_0_2.
    + exact piu1891_coshalf_lit.
  - apply real_eq_of_zero_diff. intro n.
    apply qeq_imp_qeqT.
    rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_const 2) (real_const (5 / 3)) n)).
    rewrite (qeqT_imp_qeq _ _ (real_const_proj 2 n)). rewrite (qeqT_imp_qeq _ _ (real_const_proj (5 / 3) n)).
    rewrite (qeqT_imp_qeq _ _ (real_const_proj (10 / 3) n)). field.
Qed.

(* ========== compile-exit checks ========== *)

Check piu1891_exp2_tail_cond.
Check piu1891_exp_series2_le8.
Check piu1891_egcos_lit.
Check piu1891_coshalf_lit.
Check piu1891_eggeom_lit.

Print Assumptions piu1891_exp2_tail_cond.
Print Assumptions piu1891_exp_series2_le8.
Print Assumptions piu1891_egcos_lit.
Print Assumptions piu1891_coshalf_lit.
Print Assumptions piu1891_eggeom_lit.
