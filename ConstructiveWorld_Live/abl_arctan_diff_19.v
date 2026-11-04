(* ==========================================================================)
   abl_arctan_diff_19.v — arctan 差公式件续片（9a-乙 四未竟项接续）
   使命: 接 abl_arctan_diff_16 的四个未竟项，按序推进：
     未竟项① 内点一致 delta 增量估计【本片闭合，两件】：X16 件 1 的 delta
     在语句面系 forall u → ∃delta（∃ 居 ∀u 内侧），主件 Qed 不透明后两件
     不同 u 的 delta 不可证等——一致化绕开 b3rr 主件、自其证明体直推：
     (a) abl9_atan_incr_step_cond 条件化步界引理（delta 的两条逐点后承升为
     假设，点值链逐字自 b3rr 主体转录）；(b) abl9_atan_deriv_uniform
     Region-relativized 一致 delta 实例（∃delta 提到 ∀u 外侧，
     delta := min((1−r)/2, eps·k(r)) 显式构造，k=1/(4(Cr+1)) 与 u 无关，
     min 解包复用 X16 abl9_min_lt_l/r）。
     未竟项② 链式规则【推进：Q 核四件闭合】：w(u):=(u−v)/(1+uv) 的无除法
     多项式恒等核两件（1+w² 通分分子；w 增量通分分子）＋分母非零条件下的
     除法形两件（field 闭合）；Real 层证书桥余部登记未竟。
     未竟项③ 常值判据链式版【未闭合，登记】：依赖①的一致 delta（本片已备），
     N 等步链构造未竟。未竟项④ 端点闭合【未闭合，登记】：9b 装配域
     1+x(x+h)≥3/4 下 |w|<1 严格内，内点版即可配平，端点件可免。
     主目标 abl9_atan_diff_formula 未闭合，登记未竟。
   依赖: S01_BaseRing–S11_TP3B5、abl_arctan_diff_16；Stdlib QArith、List、
     Setoid、Lia、Qminmax、GenericMinMax、Extraction。
   构造性: 全件 Qed 闭合（六引理零承认式语句）；继承 X16 的 Set 层零 Prop
     泄露口径；可提取（尾 Print Assumptions + Recursive Extraction，
     判据 Closed + Obj.magic 0）。
   编译配方: source Live/toolchain/env.sh && bash cpu_guard.sh --
     rocq c -q -native-compiler no -Q /tmp/x19pool "" abl_arctan_diff_19.v
     （隔离池 /tmp/x19pool=真拷 x16pool 现势链 13 vo，S01–S11 与现势库
     逐一 SAME；Require 链退回 S11 单链。）
   ========================================================================== *)
(* 【陈旧申报勘注（abl9 陈旧申报勘注补录组）】主式 abl9_atan_diff_formula 已由 abl9_atan_diff_a2_56.v L1871–2364 A2 形零前件闭合（闭合日期见注册册字段行；PA 全 Closed、件58 L231–232 活码使用、A2B3 决议136 在役）；本处系闭合当日之前陈旧申报，照录留痕禁删除；定论=abl9 主式深勘报告 §一。四未竟项①②③④及主目标已全链闭合（积木归宿表见abl9 主式深勘报告 §三），本申报旧文照录。 *)

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
Require Import abl_arctan_diff_16.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               Lists.List Bool.Bool Arith.Arith.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax Structures.GenericMinMax.
From Stdlib Require Import Extraction.

(* ============================================================ *)
(* 未竟项①·件 a：条件化步界引理                                      *)
(*   前件=k 的两条界（0<k 免除——本引理不用；Cr·k≤1/4 用）＋          *)
(*   delta 的两条逐点后承（|h|<(1−r)/2、|h|<eps·k 的实层形），        *)
(*   结论=内点导数步界（与 X16 件 1 结论逐字同构，u 变元）。          *)
(*   证明体=b3rr 主件点值链转录（delta 途经理仅此两发 min 解包）。    *)
(* ============================================================ *)
Lemma abl9_atan_incr_step_cond :
  forall (r : Q) (Hr0 : Qle 0 r) (Hr1 : Qlt r 1),
  forall (eps : Real) (k : Q), real_lt real_zero eps ->
  Qle (b3rr_C2 ((1 # 2) * (1 + r)) * k) (1 # 4) ->
  forall (delta : Real),
  (forall (h0 : Real), real_lt (real_abs h0) delta ->
     real_lt (real_abs h0) (real_const ((1 # 2) * (1 - r)))) ->
  (forall (h0 : Real), real_lt (real_abs h0) delta ->
     real_lt (real_abs h0) (real_mult eps (real_const k))) ->
  forall (u : Real) (Hu : forall n : nat, QleT' (Qabs (projT1 u n)) r),
  forall (h : Real), real_lt (real_abs h) delta ->
  forall (Huh : forall n : nat, QleT' (Qabs (projT1 (real_plus u h) n)) 1),
  forall (eps' : Real), real_lt real_zero eps' ->
  real_le (real_abs (real_plus (cauchy_real_arctan (real_plus u h) Huh)
                     (real_opp (real_plus (cauchy_real_arctan u
                                            (b3rr_dom_r1 u r Hu Hr1))
                                (real_mult h (real_inv_pos
                                   (real_plus real_one (real_mult u u))
                                   (b3r_one_sq_real_pos u)))))))
          (real_plus (real_mult eps (real_abs h)) eps').
Proof.
  intros r Hr0 Hr1 eps k Heps HkC delta Hhalf Hkbound u Hu h Hh Huh eps' Heps'.

  set (Cr := b3rr_C2 ((1 # 2) * (1 + r))).
  assert (HCr0 : Qle 0 Cr).
  { unfold Cr. apply QleT'_to_Qle.
    apply (b3rr_C2_0 ((1 # 2) * (1 + r))).
    - apply QleT'_to_Qle. apply (b3rr_M0 r). exact Hr0.
    - apply QltT_to_Qlt. apply (b3rr_M_lt1 r). exact Hr1. }
  assert (HCrK : Qle (Cr * k) (1 # 4)) by exact HkC.
  destruct Heps as [eps1 [Heps1 [N1 HN1]]].
  destruct Heps' as [eps1' [Heps1' [N1' HN1']]].
  (* —— delta 两条件实层直取（b3rr 的两发 min 解包至此升为假设） —— *)
  destruct (Hhalf h Hh) as [e2 [He2 [N2 HN2]]].
  destruct (Hkbound h Hh) as [e3 [He3 [N3 HN3]]].
  destruct (real_inv_proj (real_plus real_one (real_mult u u))
             (b3r_one_sq_real_pos u)) as [Ninv HNinv].
  assert (Hh2 : Qlt 0 (Qmult eps1' (Qinv 2))).
  { apply (Qmult_lt_0_compat eps1' (Qinv 2)).
    - apply QltT_to_Qlt. exact Heps1'.
    - apply Qinv_lt_0_compat. unfold Qlt. simpl. lia. }
  destruct (b3rr_qdecay r (Qmult eps1' (Qinv 2)) Hr0 Hr1 Hh2) as [Ng HNg].
  set (eta := Qmult eps1' (Qinv 2)).
  assert (Heta_pos : QltT 0 eta).
  { unfold eta. apply Qlt_to_QltT. exact Hh2. }
  left.
  exists eta. split.
  + exact Heta_pos.
  + exists (Nat.max (Nat.max (Nat.max N1 N1') (Nat.max N2 N3))
              (Nat.max Ninv Ng)).
    intros n Hn.
    apply NatLe_drop in Hn.
    assert (Hn1 : (N1 <= n)%nat) by lia.
    assert (Hn1' : (N1' <= n)%nat) by lia.
    assert (Hn2 : (N2 <= n)%nat) by lia.
    assert (Hn3 : (N3 <= n)%nat) by lia.
    assert (Hninv : (Ninv <= n)%nat) by lia.
    assert (Hng : (Ng <= n)%nat) by lia.
    set (un := projT1 u n). set (hn := projT1 h n).
    set (en := projT1 eps n). set (en' := projT1 eps' n).
    set (yn := un + hn).
    set (Dform := arctan_partial n yn - arctan_partial n un
                    - hn * Qinv (1 + un * un)).
    set (wreal := real_inv_pos (real_plus real_one (real_mult u u))
                    (b3r_one_sq_real_pos u)).
    (* 正性：en ≥ 0、en' > eps1' *)
    assert (HN1e : QltT eps1 en).
    { apply Qlt_to_QltT.
      apply (Qlt_le_trans eps1 (Qminus (projT1 eps n) (projT1 real_zero n)) en).
      - apply QltT_to_Qlt. exact (HN1 n (NatLe_lift _ _ Hn1)).
      - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
        cbn [real_zero real_const projT1]. unfold en. ring. }
    assert (Hen0 : Qle 0 en).
    { apply Qlt_le_weak. apply (Qlt_trans 0 eps1 en).
      - apply QltT_to_Qlt. exact Heps1.
      - apply QltT_to_Qlt. exact HN1e. }
    assert (HN1'e : QltT eps1' en').
    { apply Qlt_to_QltT.
      apply (Qlt_le_trans eps1' (Qminus (projT1 eps' n) (projT1 real_zero n)) en').
      - apply QltT_to_Qlt. exact (HN1' n (NatLe_lift _ _ Hn1')).
      - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
        cbn [real_zero real_const projT1]. unfold en'. ring. }
    (* 见证→点界：|hn| ≤ (1−r)/2、|hn| ≤ en·k *)
    assert (Hq2 : Qlt e2 (Qminus ((1 # 2) * (1 - r)) (Qabs hn))).
    { apply (Qlt_le_trans e2
               (Qminus (projT1 (real_const ((1 # 2) * (1 - r))) n)
                       (projT1 (real_abs h) n))
               (Qminus ((1 # 2) * (1 - r)) (Qabs hn))).
      - apply QltT_to_Qlt. apply (HN2 n (NatLe_lift _ _ Hn2)).
      - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
        rewrite (qeqT_imp_qeq _ _ (real_abs_proj h n)).
        cbn [real_zero real_const projT1]. reflexivity. }
    assert (Hhn_half : Qlt (Qabs hn) ((1 # 2) * (1 - r))).
    { apply (Qlt_le_trans (Qabs hn) (Qminus ((1 # 2) * (1 - r)) e2)
                          ((1 # 2) * (1 - r))).
      - apply QltT_to_Qlt. apply (q_lt_minus_shift e2 ((1 # 2) * (1 - r)) (Qabs hn)).
        apply Qlt_to_QltT. exact Hq2.
      - assert (He20 : Qle 0 e2) by (apply Qlt_le_weak; apply QltT_to_Qlt; exact He2).
        apply (Qle_trans (Qminus ((1 # 2) * (1 - r)) e2)
                         (Qplus (Qminus ((1 # 2) * (1 - r)) e2) e2)
                         ((1 # 2) * (1 - r))).
        + apply (Qle_trans (Qminus ((1 # 2) * (1 - r)) e2)
                           (Qplus (Qminus ((1 # 2) * (1 - r)) e2) 0)
                           (Qplus (Qminus ((1 # 2) * (1 - r)) e2) e2)).
          * apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
          * apply (Qplus_le_compat (Qminus ((1 # 2) * (1 - r)) e2)
                                   (Qminus ((1 # 2) * (1 - r)) e2) 0 e2
                                   (Qle_refl _) He20).
        + apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring. }
    assert (Hhn_half_le : Qle (Qabs hn) ((1 # 2) * (1 - r)))
      by (apply Qlt_le_weak; exact Hhn_half).
    assert (Hhn1 : Qle (Qabs hn) 1).
    { apply (Qle_trans _ ((1 # 2) * (1 - r)) _).
      - exact Hhn_half_le.
      - apply QleT'_to_Qle. apply (b3rr_1mr_half_le1 r). exact Hr0. }
    assert (Hq3 : Qlt e3 (Qminus (Qmult en k) (Qabs hn))).
    { apply (Qlt_le_trans e3
               (Qminus (projT1 (real_mult eps (real_const k)) n)
                       (projT1 (real_abs h) n))
               (Qminus (Qmult en k) (Qabs hn))).
      - apply QltT_to_Qlt. apply (HN3 n (NatLe_lift _ _ Hn3)).
      - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
        rewrite (qeqT_imp_qeq _ _ (real_abs_proj h n)).
        rewrite (qeqT_imp_qeq _ _ (real_mult_proj eps (real_const k) n)).
        unfold en.
        cbn [real_zero real_const projT1]. reflexivity. }
    assert (Hhn_k : Qlt (Qabs hn) (Qmult en k)).
    { apply (Qlt_le_trans (Qabs hn) (Qminus (Qmult en k) e3) (Qmult en k)).
      - apply QltT_to_Qlt. apply (q_lt_minus_shift e3 (Qmult en k) (Qabs hn)).
        apply Qlt_to_QltT. exact Hq3.
      - assert (He30 : Qle 0 e3) by (apply Qlt_le_weak; apply QltT_to_Qlt; exact He3).
        apply (Qle_trans (Qminus (Qmult en k) e3)
                         (Qplus (Qminus (Qmult en k) e3) e3)
                         (Qmult en k)).
        + apply (Qle_trans (Qminus (Qmult en k) e3)
                           (Qplus (Qminus (Qmult en k) e3) 0)
                           (Qplus (Qminus (Qmult en k) e3) e3)).
          * apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
          * apply (Qplus_le_compat (Qminus (Qmult en k) e3)
                                   (Qminus (Qmult en k) e3) 0 e3
                                   (Qle_refl _) He30).
        + apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring. }
    assert (Hhn_kle : Qle (Qabs hn) (Qmult en k)) by (apply Qlt_le_weak; exact Hhn_k).
    (* 域：|un| ≤ r *)
    assert (Hun_r : Qle (Qabs un) r).
    { apply (QleT'_to_Qle (Qabs un) r). apply Hu. }
    assert (Hhvn0 : Qle 0 (Qabs hn)) by apply Qabs_nonneg.
    assert (Henhn0 : Qle 0 (Qmult en (Qabs hn))).
    { apply (Qmult_le_0_compat en (Qabs hn)). exact Hen0. exact Hhvn0. }
    (* 投影恒等（A 侧） *)
    assert (Hrepl : projT1 (real_abs (real_plus (cauchy_real_arctan (real_plus u h) Huh)
                (real_opp (real_plus (cauchy_real_arctan u (b3rr_dom_r1 u r Hu Hr1))
                            (real_mult h wreal))))) n ==
                Qabs (arctan_partial n yn - arctan_partial n un - hn * Qinv (1 + un * un))).
    { unfold yn, un, hn, wreal.
      rewrite (qeqT_imp_qeq _ _ (real_abs_proj (real_plus (cauchy_real_arctan (real_plus u h) Huh)
                (real_opp (real_plus (cauchy_real_arctan u (b3rr_dom_r1 u r Hu Hr1))
                            (real_mult h (real_inv_pos (real_plus real_one (real_mult u u))
                                                       (b3r_one_sq_real_pos u)))))) n)).
      rewrite (qeqT_imp_qeq _ _ (real_plus_proj (cauchy_real_arctan (real_plus u h) Huh)
                (real_opp (real_plus (cauchy_real_arctan u (b3rr_dom_r1 u r Hu Hr1))
                            (real_mult h (real_inv_pos (real_plus real_one (real_mult u u))
                                                       (b3r_one_sq_real_pos u))))) n)).
      rewrite (qeqT_imp_qeq _ _ (real_opp_proj (real_plus (cauchy_real_arctan u (b3rr_dom_r1 u r Hu Hr1))
                            (real_mult h (real_inv_pos (real_plus real_one (real_mult u u))
                                                       (b3r_one_sq_real_pos u)))) n)).
      rewrite (qeqT_imp_qeq _ _ (real_plus_proj (cauchy_real_arctan u (b3rr_dom_r1 u r Hu Hr1))
                            (real_mult h (real_inv_pos (real_plus real_one (real_mult u u))
                                                       (b3r_one_sq_real_pos u))) n)).
      rewrite (qeqT_imp_qeq _ _ (real_mult_proj h (real_inv_pos (real_plus real_one (real_mult u u))
                                                       (b3r_one_sq_real_pos u)) n)).
      rewrite (qeqT_imp_qeq _ _ (arctan_real_proj (real_plus u h) Huh n)).
      rewrite (qeqT_imp_qeq _ _ (arctan_real_proj u (b3rr_dom_r1 u r Hu Hr1) n)).
      rewrite (qeqT_imp_qeq _ _ (real_plus_proj u h n)).
      rewrite (qeqT_imp_qeq _ _ (HNinv n (NatLe_lift _ _ Hninv))).
      rewrite (qeqT_imp_qeq _ _ (real_plus_proj real_one (real_mult u u) n)).
      rewrite (qeqT_imp_qeq _ _ (real_mult_proj u u n)).
      rewrite (qeqT_imp_qeq _ _ (b3r_one_proj n)).
      apply Qabs_wd. ring. }
    (* B 侧投影 *)
    assert (HB : projT1 (real_plus (real_mult eps (real_abs h)) eps') n
                 == en * Qabs hn + en').
    { unfold en, en', hn.
      setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult eps (real_abs h)) eps' n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj eps (real_abs h) n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj h n)).
      cbn [real_zero real_const projT1]. ring. }
    (* 点主界 1：Cr·|hn|² ≤ en·|hn|·(1/4) *)
    assert (Hcbn : Qle (Qmult Cr (Qmult (Qabs hn) (Qabs hn)))
                       (Qmult (Qmult en (Qabs hn)) (1 # 4))).
    { apply (Qle_trans _ (Qmult Cr (Qmult (Qmult en k) (Qabs hn))) _).
      - apply QleT'_to_Qle. apply (b3_qmult_le_l (Qmult (Qabs hn) (Qabs hn))
                             (Qmult (Qmult en k) (Qabs hn)) Cr).
        + exact HCr0.
        + apply (Qmult_le_compat_r (Qabs hn) (Qmult en k) (Qabs hn)).
          * exact Hhn_kle.
          * exact Hhvn0.
      - apply (Qle_trans _ (Qmult (Qmult en (Qabs hn)) (Qmult Cr k)) _).
        + apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
        + apply QleT'_to_Qle. apply (b3_qmult_le_l (Qmult Cr k) (1 # 4) (Qmult en (Qabs hn))).
          * exact Henhn0.
          * exact HCrK. }
    (* 点主界 2：r^{2(Sn)} ≤ eta（n ≥ Ng ⟹ 2(Sn) ≥ Ng） *)
    assert (Hdec2 : Qle (q_pow r (2 * Datatypes.S n)) eta).
    { apply QleT'_to_Qle. apply (HNg ((2 * Datatypes.S n)%nat)).
      apply NatLe_lift. lia. }
    assert (Hpow14 : Qle (Qmult (Qabs hn) (q_pow r (2 * Datatypes.S n)))
                         (q_pow r (2 * Datatypes.S n))).
    { apply (Qle_trans _ (Qmult 1 (q_pow r (2 * Datatypes.S n))) _).
      - apply (Qmult_le_compat_r (Qabs hn) 1 (q_pow r (2 * Datatypes.S n))).
        + exact Hhn1.
        + apply QleT'_to_Qle. apply q_pow_nonneg. apply Qle_to_QleT'. exact Hr0.
      - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring. }
    (* 主点界：|D_n| ≤ en·|hn| + eta *)
    assert (Hm1 : Qle
      (Qabs (arctan_partial n yn - arctan_partial n un - hn * Qinv (1 + un * un)))
      (Qplus (Qmult Cr (Qmult (Qabs hn) (Qabs hn)))
             (Qmult (Qabs hn) (q_pow r (2 * Datatypes.S n))))).
    { unfold yn. apply QleT'_to_Qle.
      apply (b3rr_core_r n un hn r Hr0 Hr1 Hun_r Hhn_half_le). }
    assert (Hm2 : Qle
      (Qplus (Qmult Cr (Qmult (Qabs hn) (Qabs hn)))
             (Qmult (Qabs hn) (q_pow r (2 * Datatypes.S n))))
      (Qplus (Qmult (Qmult en (Qabs hn)) (1 # 4))
             (Qmult (Qabs hn) (q_pow r (2 * Datatypes.S n))))).
    { apply Qplus_le_compat. exact Hcbn. apply Qle_refl. }
    assert (Hm3 : Qle
      (Qplus (Qmult (Qmult en (Qabs hn)) (1 # 4))
             (Qmult (Qabs hn) (q_pow r (2 * Datatypes.S n))))
      (Qplus (Qmult (Qmult en (Qabs hn)) (1 # 4))
             (q_pow r (2 * Datatypes.S n)))).
    { apply Qplus_le_compat. apply Qle_refl. exact Hpow14. }
    assert (Hm4 : Qle
      (Qplus (Qmult (Qmult en (Qabs hn)) (1 # 4))
             (q_pow r (2 * Datatypes.S n)))
      (Qplus (Qmult (Qmult en (Qabs hn)) (1 # 4)) eta)).
    { apply Qplus_le_compat. apply Qle_refl. exact Hdec2. }
    assert (Hm5 : Qle (Qmult (Qmult en (Qabs hn)) (1 # 4)) (Qmult en (Qabs hn))).
    { apply (Qle_trans _ (Qmult (Qmult en (Qabs hn)) 1) _).
      - apply QleT'_to_Qle. apply (b3_qmult_le_l (1 # 4) 1 (Qmult en (Qabs hn))).
        + exact Henhn0.
        + unfold Qle. simpl. lia.
      - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring. }
    assert (Hm6 : Qle
      (Qplus (Qmult (Qmult en (Qabs hn)) (1 # 4)) eta)
      (Qplus (Qmult en (Qabs hn)) eta)).
    { apply Qplus_le_compat. exact Hm5. apply Qle_refl. }
    assert (Hmain : Qle
      (Qabs (arctan_partial n yn - arctan_partial n un - hn * Qinv (1 + un * un)))
      (Qplus (Qmult en (Qabs hn)) eta)).
    { apply (Qle_trans _ (Qplus (Qmult Cr (Qmult (Qabs hn) (Qabs hn)))
             (Qmult (Qabs hn) (q_pow r (2 * Datatypes.S n)))) _).
      - exact Hm1.
      - apply (Qle_trans _ (Qplus (Qmult (Qmult en (Qabs hn)) (1 # 4))
             (Qmult (Qabs hn) (q_pow r (2 * Datatypes.S n)))) _).
        + exact Hm2.
        + apply (Qle_trans _ (Qplus (Qmult (Qmult en (Qabs hn)) (1 # 4))
               (q_pow r (2 * Datatypes.S n))) _).
          * exact Hm3.
          * apply (Qle_trans _ (Qplus (Qmult (Qmult en (Qabs hn)) (1 # 4)) eta) _).
            -- exact Hm4.
            -- exact Hm6. }
    (* Hfin：eta < (en·|hn| + en') − |D_n| *)
    assert (Hfin : Qlt eta
        (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qabs Dform))).
    { apply (Qlt_le_trans eta
        (Qminus (Qplus (Qmult en (Qabs hn)) en')
                (Qplus (Qmult en (Qabs hn)) eta))
        (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qabs Dform))).
      - apply (proj2 (Qlt_minus_iff eta
          (Qminus (Qplus (Qmult en (Qabs hn)) en')
                  (Qplus (Qmult en (Qabs hn)) eta)))).
        assert (Heq : Qminus (Qminus (Qplus (Qmult en (Qabs hn)) en')
                             (Qplus (Qmult en (Qabs hn)) eta)) eta ==
                  Qminus en' (Qmult eta (1 + 1))) by ring.
        rewrite Heq.
        apply (proj1 (Qlt_minus_iff (Qmult eta (1 + 1)) en')).
        assert (HX : Qmult eta (1 + 1) == eps1') by (unfold eta; field).
        rewrite HX.
        apply QltT_to_Qlt. exact HN1'e.
      - apply (proj2 (Qle_minus_iff
            (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qplus (Qmult en (Qabs hn)) eta))
            (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qabs Dform)))).
        assert (Heq2 : Qminus (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qabs Dform))
                              (Qminus (Qplus (Qmult en (Qabs hn)) en')
                                      (Qplus (Qmult en (Qabs hn)) eta)) ==
                        Qminus (Qplus (Qmult en (Qabs hn)) eta) (Qabs Dform)) by ring.
        rewrite Heq2.
        apply (proj1 (Qle_minus_iff (Qabs Dform) (Qplus (Qmult en (Qabs hn)) eta))).
        exact Hmain. }
    (* 投影桥（RHS − LHS）==（B − |D|） *)
    assert (Hrepl2 : Qeq
        (Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                (projT1 (real_abs (real_plus (cauchy_real_arctan (real_plus u h) Huh)
                (real_opp (real_plus (cauchy_real_arctan u (b3rr_dom_r1 u r Hu Hr1))
                            (real_mult h wreal))))) n))
        (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qabs Dform))).
    { apply (Qminus_comp (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                         (Qplus (Qmult en (Qabs hn)) en') HB
                         (projT1 (real_abs (real_plus (cauchy_real_arctan (real_plus u h) Huh)
                         (real_opp (real_plus (cauchy_real_arctan u (b3rr_dom_r1 u r Hu Hr1))
                                     (real_mult h wreal))))) n)
                         (Qabs Dform) Hrepl). }
    apply Qlt_to_QltT.
    assert (Hqfinal : Qlt eta
        (Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                (projT1 (real_abs (real_plus (cauchy_real_arctan (real_plus u h) Huh)
                (real_opp (real_plus (cauchy_real_arctan u (b3rr_dom_r1 u r Hu Hr1))
                            (real_mult h wreal))))) n))).
    { apply (Qlt_le_trans eta
        (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qabs Dform))
        (Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                (projT1 (real_abs (real_plus (cauchy_real_arctan (real_plus u h) Huh)
                (real_opp (real_plus (cauchy_real_arctan u (b3rr_dom_r1 u r Hu Hr1))
                            (real_mult h wreal))))) n))).
      - exact Hfin.
      - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. apply Qeq_sym. exact Hrepl2. }
    exact Hqfinal.
Qed.

(* ============================================================ *)
(* 未竟项①·件 b：Region-relativized 一致 delta 实例（本片主交付）      *)
(*   ∃delta 提到 ∀u 外侧——delta := min((1−r)/2, eps·k(r)) 与 u 无关   *)
(*   （k=1/(4(Cr+1))，Cr=b3rr_C2((1+r)/2) 只依赖 r），供未竟项③ N 等   *)
(*   步链逐点取用。                                                   *)
(* ============================================================ *)
Lemma abl9_atan_deriv_uniform :
  forall (rho : Q) (Hrho0 : Qle 0 rho) (Hrho1 : Qlt rho 1),
  forall (eps : Real), real_lt real_zero eps ->
  sigT (fun delta : Real =>
    And (real_lt real_zero delta)
        (forall (u : Real) (Hu : forall n : nat, QleT' (Qabs (projT1 u n)) rho),
          forall (h : Real), real_lt (real_abs h) delta ->
          forall (Huh : forall n : nat,
                    QleT' (Qabs (projT1 (real_plus u h) n)) 1),
          forall (eps' : Real), real_lt real_zero eps' ->
          real_le (real_abs (real_plus (cauchy_real_arctan (real_plus u h) Huh)
                     (real_opp (real_plus (cauchy_real_arctan u
                                            (b3rr_dom_r1 u rho Hu Hrho1))
                                (real_mult h (real_inv_pos
                                   (real_plus real_one (real_mult u u))
                                   (b3r_one_sq_real_pos u)))))))
                  (real_plus (real_mult eps (real_abs h)) eps'))).
Proof.
  intros rho Hrho0 Hrho1 eps Heps.
  set (Cr := b3rr_C2 ((1 # 2) * (1 + rho))).
  assert (HCr0 : Qle 0 Cr).
  { unfold Cr. apply QleT'_to_Qle.
    apply (b3rr_C2_0 ((1 # 2) * (1 + rho))).
    - apply QleT'_to_Qle. apply (b3rr_M0 rho). exact Hrho0.
    - apply QltT_to_Qlt. apply (b3rr_M_lt1 rho). exact Hrho1. }
  set (k := Qinv (4 * (Cr + 1))).
  assert (Hk_pos : Qlt 0 k).
  { unfold k. apply Qinv_lt_0_compat.
    apply (Qmult_lt_0_compat 4 (Cr + 1)).
    - unfold Qlt. simpl. lia.
    - apply (Qlt_le_trans 0 1 (Cr + 1)).
      + unfold Qlt. simpl. lia.
      + apply (Qle_trans 1 (0 + 1) (Cr + 1)).
        * apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
        * apply Qplus_le_compat. exact HCr0. apply Qle_refl. }
  assert (HCrK : Qle (Cr * k) (1 # 4)).
  { unfold k. apply QleT'_to_Qle. exact (b3rr_CK Cr HCr0). }
  set (rk := real_const k).
  exists (real_min (real_const ((1 # 2) * (1 - rho))) (real_mult eps rk)). split.
  - apply real_min_pos.
    + apply real_const_pos_f1.
      apply (Qmult_lt_0_compat (1 # 2) (1 - rho)).
      * unfold Qlt. simpl. lia.
      * apply (proj1 (Qlt_minus_iff rho 1)). exact Hrho1.
    + apply real_mult_positive.
      * exact Heps.
      * unfold rk. apply real_const_pos_f1. exact Hk_pos.
  - intros u Hu h Hh Huh eps' Heps'.
    apply (abl9_atan_incr_step_cond rho Hrho0 Hrho1 eps k Heps HCrK
             (real_min (real_const ((1 # 2) * (1 - rho))) (real_mult eps rk))).
    + intros h0 Hh0.
      exact (abl9_min_lt_l (real_const ((1 # 2) * (1 - rho)))
              (real_mult eps rk) (real_abs h0) Hh0).
    + intros h0 Hh0.
      exact (abl9_min_lt_r (real_const ((1 # 2) * (1 - rho)))
              (real_mult eps rk) (real_abs h0) Hh0).
    + exact Hh.
    + exact Heps'.
Qed.

(* ============================================================ *)
(* 未竟项②·Q 核两件（链式规则的通分分子多项式恒等核，无除法形）        *)
(*   设 w(u):=(u−v)/(1+uv)，则 1+w(u)²=(1+u²)(1+v²)/(1+uv)²，        *)
(*   w(u+h)−w(u)=h(1+v²)/((1+(u+h)v)(1+uv))——分母非零条件下的       *)
(*   Q 层恒等式；其纯多项式核=下列两件（判别基建核：多项式规范形）。  *)
(* ============================================================ *)
Lemma abl9_wsq_ring_id : forall u v : Q,
  QeqT ((1 + u * v) * (1 + u * v) + (u - v) * (u - v))
       ((1 + u * u) * (1 + v * v)).
Proof. intros u v. apply qeq_imp_qeqT. ring. Qed.

Lemma abl9_wincr_ring_id : forall u v h : Q,
  QeqT ((u + h - v) * (1 + u * v) - (u - v) * (1 + (u + h) * v))
       (h * (1 + v * v)).
Proof. intros u v h. apply qeq_imp_qeqT. ring. Qed.

(* 未竟项②·Q 核除法形（分母非零条件下的通分恒等式，field 闭合）——          *)
(*   Real 层证书桥（real_inv_pos_ext 对齐）的直接输入形。                  *)
Lemma abl9_wsq_div_id : forall u v : Q, ~ (1 + u * v == 0) ->
  QeqT (1 + (u - v) * (u - v) / ((1 + u * v) * (1 + u * v)))
       ((1 + u * u) * (1 + v * v) / ((1 + u * v) * (1 + u * v))).
Proof.
  intros u v Hne. apply qeq_imp_qeqT.
  assert (Hne2 : ~ ((1 + u * v) * (1 + u * v) == 0)).
  { intros Hp. destruct (Qmult_integral (1 + u * v) (1 + u * v) Hp) as [Hz | Hz].
    - apply Hne. exact Hz.
    - apply Hne. exact Hz. }
  field; try assumption.
Qed.

Lemma abl9_wincr_div_id : forall u v h : Q,
  ~ (1 + (u + h) * v == 0) -> ~ (1 + u * v == 0) ->
  QeqT ((u + h - v) / (1 + (u + h) * v) - (u - v) / (1 + u * v))
       (h * (1 + v * v) / ((1 + (u + h) * v) * (1 + u * v))).
Proof.
  intros u v h H1 H2. apply qeq_imp_qeqT.
  assert (Hne2 : ~ ((1 + (u + h) * v) * (1 + u * v) == 0)).
  { intros Hp. destruct (Qmult_integral (1 + (u + h) * v) (1 + u * v) Hp) as [Hz | Hz].
    - apply H1. exact Hz.
    - apply H2. exact Hz. }
  field. split; assumption.
Qed.

(* ============================================================ *)
(* 终验 · 承认面 + 提取检验                                          *)
(*   对账三联：Lemma 名清单 6 = Qed 计数 6 = PA 语句 6，零差。        *)
(* ============================================================ *)
Print Assumptions abl9_atan_incr_step_cond.
Print Assumptions abl9_atan_deriv_uniform.
Print Assumptions abl9_wsq_ring_id.
Print Assumptions abl9_wincr_ring_id.
Print Assumptions abl9_wsq_div_id.
Print Assumptions abl9_wincr_div_id.

(* 提取检验（判据 = 输出 Obj.magic 计数 0） *)
Recursive Extraction abl9_atan_deriv_uniform abl9_wsq_ring_id abl9_wincr_ring_id
  abl9_wsq_div_id abl9_wincr_div_id.
