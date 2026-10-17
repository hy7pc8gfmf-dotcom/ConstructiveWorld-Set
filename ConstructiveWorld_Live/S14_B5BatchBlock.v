(* ============================================================ *)
(* S14_B5BatchBlock.v —— B5 批块装配：arctan/指数/log 透明链复刻件、  *)
(*   有理点零值契约件与 δ 链预算（构造性 Set 层）。                    *)
(* ── 使命：b5dQ_E_rational_zero（0<q<1 ⟹ real_E (real_const q) == 0）；*)
(*   b5dQ_Hmod/b5dQ_Hstep 步界证书族；b5dS_E_zero_on_unit；同名非平凡  *)
(*   替换件（替换定理 b5d1_Heps4 / b5d1_Heps8 / b5d1_Heps16 /          *)
(*   b5dE_zero_le_one 共 4 条，语句与声明序不变；Heps 族 Q 层正性就地    *)
(*   直构，b5dE_zero_le_one 逐点代数直构）。                            *)
(* ── 依赖：S01–S13；Stdlib（QArith、List、Bool、Arith、Setoid、      *)
(*   Morphisms、Lia）。                                                 *)
(* ── 构造性注记：零承认件、零经典逻辑；替换仅及上列 4 条证明体，        *)
(*   声明面与其余定理一律不动；文件尾附假设面打印锚。                    *)
(* ── 编译配方：全字面 COQLIB/ROCQLIB 双 export 后 coqc -Q             *)
(*   ../../Live_X "" -Q . "" S14_B5BatchBlock.v。                       *)
(* ============================================================ *)
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
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               Lists.List Bool.Bool Arith.Arith.
Import ListNotations.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax.
Import PropositionConvergenceCore.
From Stdlib Require Import Lqa.
Opaque Qred.


(* ============================================================ *)
(* 块 item5（前缀 b5d1_——主件 b5d1_b3rr_atan_deriv_lin）——来源：演变/.ablation/sc2_parallel/sc2_b5a_ode/sc2_b5a_item5.v。 *)
(* ============================================================ *)

(* ============================================================ *)
(* §0 实例证书装配（r := 1/2、x := real_const 0、eps := 1/4）   *)
(* ============================================================ *)

(* r ≥ 0：Qle 0 (1#2) *)
Lemma b5d1_Hr0 : Qle 0 (1 # 2).
Proof. unfold Qle. simpl. lia. Qed.

(* r < 1：Qlt (1#2) 1 *)
Lemma b5d1_Hr1 : Qlt (1 # 2) 1.
Proof. unfold Qlt. simpl. lia. Qed.

(* 逐点域证书：|projT1 (real_const 0) n| ≤ r（QleT' 形式） *)
Lemma b5d1_Hxr0 : forall n : nat, QleT' (Qabs (projT1 (real_const 0) n)) (1 # 2).
Proof.
  intro n.
  assert (Hz : projT1 (real_const 0) n == 0) by reflexivity.
  apply Qle_to_QleT'.
  apply (Qle_trans (Qabs (projT1 (real_const 0) n)) (Qabs 0) (1 # 2)).
  - apply qeq_imp_qle. apply (Qabs_wd (projT1 (real_const 0) n) 0). exact Hz.
  - apply (Qle_trans (Qabs 0) 0 (1 # 2)).
    + apply qeq_imp_qle. change (Qabs 0 == 0). cbn. reflexivity.
    + unfold Qle. simpl. lia.
Qed.

(* eps 正性（Q 层）：Qlt 0 e，e ∈ {1/4, 1/8, 1/16} *)
Lemma b5d1_Hepsq4 : Qlt 0 (1 # 4).
Proof. unfold Qlt. simpl. lia. Qed.

Lemma b5d1_Hepsq8 : Qlt 0 (1 # 8).
Proof. unfold Qlt. simpl. lia. Qed.

Lemma b5d1_Hepsq16 : Qlt 0 (1 # 16).
Proof. unfold Qlt. simpl. lia. Qed.

(* eps 证书：real_lt real_zero (real_const e)（Real 层正性） *)
Lemma b5d1_Heps4 : real_lt real_zero (real_const (1 # 4)).
Proof.
  apply real_const_pos_f1.
  (* ToyR 替换：Q 层正性就地直构（消 b5d1_Hepsq4 转发跳） *)
  unfold Qlt. simpl. lia.
Qed.

Lemma b5d1_Heps8 : real_lt real_zero (real_const (1 # 8)).
Proof.
  apply real_const_pos_f1.
  (* ToyR 替换：Q 层正性就地直构（消 b5d1_Hepsq8 转发跳） *)
  unfold Qlt. simpl. lia.
Qed.

Lemma b5d1_Heps16 : real_lt real_zero (real_const (1 # 16)).
Proof.
  apply real_const_pos_f1.
  (* ToyR 替换：Q 层正性就地直构（消 b5d1_Hepsq16 转发跳） *)
  unfold Qlt. simpl. lia.
Qed.

(* ============================================================ *)
(* §1 B3 主件：b3rr_real_arctan_deriv_linear 证明体机器抽取       *)
(*   （ConstructiveWorld.v L71860–72180，零手抄），Qed→Defined，   *)
(*   改名 b5d1_b3rr_atan_deriv_lin（原名唯一出现处即 Lemma 头，   *)
(*   体内零自引用；支撑引理全部来自根 CW.ConstructiveWorld）。     *)
(*   Defined ⇒ sigT 见证可计算 ⇒ projT1 输出显式 δ 表达式。       *)
(* ============================================================ *)
Lemma b5d1_b3rr_atan_deriv_lin :
  forall (r : Q) (Hr0 : Qle 0 r) (Hr1 : Qlt r 1),
  forall (x : Real),
  forall (Hxb : forall n : nat, QleT' (Qabs (projT1 x n)) r),
  forall (eps : Real), real_lt real_zero eps ->
  sigT (fun delta : Real =>
    And (real_lt real_zero delta)
        (forall (h : Real), real_lt (real_abs h) delta ->
          forall (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1),
          forall (eps' : Real), real_lt real_zero eps' ->
          real_le (real_abs (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                     (real_opp (real_plus (cauchy_real_arctan x (b3rr_dom_r1 x r Hxb Hr1))
                                 (real_mult h (real_inv_pos (real_plus real_one (real_mult x x))
                                                           (b3r_one_sq_real_pos x)))))))
                  (real_plus (real_mult eps (real_abs h)) eps'))).
Proof.
  intros r Hr0 Hr1 x Hxb eps Heps.
  set (Cr := b3rr_C2 ((1 # 2) * (1 + r))).
  assert (HCr0 : Qle 0 Cr).
  { unfold Cr. apply (b3rr_C2_0 ((1 # 2) * (1 + r))).
    - apply (b3rr_M0 r). exact Hr0.
    - apply (b3rr_M_lt1 r). exact Hr1. }
  set (k := Qinv (4 * (Cr + 1))).
  assert (Hk_pos : Qlt 0 k).
  { unfold k. apply Qinv_lt_0_compat.
    apply (Qmult_lt_0_compat 4 (Cr + 1)).
    - unfold Qlt. simpl. lia.
    - apply (Qlt_le_trans 0 1 (Cr + 1)).
      + unfold Qlt. simpl. lia.
      + apply (Qle_trans 1 (0 + 1) (Cr + 1)).
        * apply qeq_imp_qle. ring.
        * apply Qplus_le_compat. exact HCr0. apply Qle_refl. }
  assert (HCrK : Qle (Cr * k) (1 # 4)).
  { unfold k. exact (b3rr_CK Cr HCr0). }
  assert (Hk0 : Qle 0 k) by (apply Qlt_le_weak; exact Hk_pos).
  set (rk := real_const k).
  assert (Hrk_pos : real_lt real_zero rk).
  { unfold rk. apply real_const_pos_f1. exact Hk_pos. }
  set (delta := real_min (real_const ((1 # 2) * (1 - r))) (real_mult eps rk)).
  exists delta. split.
  - (* 0 < delta *)
    unfold delta, rk.
    apply real_min_pos.
    + apply real_const_pos_f1.
      apply (Qmult_lt_0_compat (1 # 2) (1 - r)).
      * unfold Qlt. simpl. lia.
      * apply (proj1 (Qlt_minus_iff r 1)). exact Hr1.
    + apply real_mult_positive. exact Heps. exact Hrk_pos.
  - intros h Hh Hxh eps' Heps'.
    left.
    destruct Heps as [eps1 [Heps1 [N1 HN1]]].
    destruct Heps' as [eps1' [Heps1' [N1' HN1']]].
    assert (Hh_l : real_lt (real_abs h) (real_const ((1 # 2) * (1 - r))))
      by (unfold delta in Hh; apply (real_min_lt_l h (real_const ((1 # 2) * (1 - r))) (real_mult eps rk)); exact Hh).
    assert (Hh_r : real_lt (real_abs h) (real_mult eps rk))
      by (unfold delta in Hh; apply (real_min_lt_r h (real_const ((1 # 2) * (1 - r))) (real_mult eps rk)); exact Hh).
    destruct Hh_l as [e2 [He2 [N2 HN2]]].
    destruct Hh_r as [e3 [He3 [N3 HN3]]].
    destruct (real_inv_proj (real_plus real_one (real_mult x x)) (b3r_one_sq_real_pos x)) as [Ninv HNinv].
    assert (Hh2 : Qlt 0 (Qmult eps1' (Qinv 2))).
    { apply (Qmult_lt_0_compat eps1' (Qinv 2)).
      - apply QltT_to_Qlt. exact Heps1'.
      - apply Qinv_lt_0_compat. unfold Qlt. simpl. lia. }
    destruct (b3rr_qdecay r (Qmult eps1' (Qinv 2)) Hr0 Hr1 Hh2) as [Ng HNg].
    set (eta := Qmult eps1' (Qinv 2)).
    assert (Heta_pos : QltT 0 eta).
    { unfold eta. apply Qlt_to_QltT. exact Hh2. }
    exists eta. split.
    + exact Heta_pos.
    + exists (Nat.max (Nat.max (Nat.max N1 N1') (Nat.max N2 N3)) (Nat.max Ninv Ng)).
      intros n Hn.
      apply NatLe_drop in Hn.
      assert (Hn1 : (N1 <= n)%nat) by lia.
      assert (Hn1' : (N1' <= n)%nat) by lia.
      assert (Hn2 : (N2 <= n)%nat) by lia.
      assert (Hn3 : (N3 <= n)%nat) by lia.
      assert (Hninv : (Ninv <= n)%nat) by lia.
      assert (Hng : (Ng <= n)%nat) by lia.
      set (un := projT1 x n). set (hn := projT1 h n).
      set (en := projT1 eps n). set (en' := projT1 eps' n).
      set (yn := un + hn).
      set (Dform := arctan_partial n yn - arctan_partial n un - hn * Qinv (1 + un * un)).
      set (wreal := real_inv_pos (real_plus real_one (real_mult x x)) (b3r_one_sq_real_pos x)).
      (* 正性：en ≥ 0、en' > eps1' *)
      assert (HN1e : QltT eps1 en).
      { apply Qlt_to_QltT.
        apply (Qlt_le_trans eps1 (Qminus (projT1 eps n) (projT1 real_zero n)) en).
        - apply QltT_to_Qlt. exact (HN1 n (NatLe_lift _ _ Hn1)).
        - apply qeq_imp_qle. cbn [real_zero real_const projT1]. unfold en. ring. }
      assert (Hen0 : Qle 0 en).
      { apply Qlt_le_weak. apply (Qlt_trans 0 eps1 en).
        - apply QltT_to_Qlt. exact Heps1.
        - apply QltT_to_Qlt. exact HN1e. }
      assert (HN1'e : QltT eps1' en').
      { apply Qlt_to_QltT.
        apply (Qlt_le_trans eps1' (Qminus (projT1 eps' n) (projT1 real_zero n)) en').
        - apply QltT_to_Qlt. exact (HN1' n (NatLe_lift _ _ Hn1')).
        - apply qeq_imp_qle. cbn [real_zero real_const projT1]. unfold en'. ring. }
      (* 见证→点界：|hn| ≤ (1−r)/2、|hn| ≤ en·k *)
      assert (Hq2 : Qlt e2 (Qminus ((1 # 2) * (1 - r)) (Qabs hn))).
      { apply (Qlt_le_trans e2 (Qminus (projT1 (real_const ((1 # 2) * (1 - r))) n) (projT1 (real_abs h) n))
                             (Qminus ((1 # 2) * (1 - r)) (Qabs hn))).
        - apply QltT_to_Qlt. apply (HN2 n (NatLe_lift _ _ Hn2)).
        - apply qeq_imp_qle.
          rewrite (real_abs_proj h n). cbn [real_zero real_const projT1]. reflexivity. }
      assert (Hhn_half : Qlt (Qabs hn) ((1 # 2) * (1 - r))).
      { apply (Qlt_le_trans (Qabs hn) (Qminus ((1 # 2) * (1 - r)) e2) ((1 # 2) * (1 - r))).
        - apply (q_lt_minus_shift e2 ((1 # 2) * (1 - r)) (Qabs hn)). exact Hq2.
        - assert (He20 : Qle 0 e2) by (apply Qlt_le_weak; apply QltT_to_Qlt; exact He2).
          apply (Qle_trans (Qminus ((1 # 2) * (1 - r)) e2)
                           (Qplus (Qminus ((1 # 2) * (1 - r)) e2) e2)
                           ((1 # 2) * (1 - r))).
          + apply (Qle_trans (Qminus ((1 # 2) * (1 - r)) e2)
                             (Qplus (Qminus ((1 # 2) * (1 - r)) e2) 0)
                             (Qplus (Qminus ((1 # 2) * (1 - r)) e2) e2)).
            * apply qeq_imp_qle. ring.
            * apply (Qplus_le_compat (Qminus ((1 # 2) * (1 - r)) e2)
                                     (Qminus ((1 # 2) * (1 - r)) e2) 0 e2
                                     (Qle_refl _) He20).
          + apply qeq_imp_qle. ring. }
      assert (Hhn_half_le : Qle (Qabs hn) ((1 # 2) * (1 - r))) by (apply Qlt_le_weak; exact Hhn_half).
      assert (Hhn1 : Qle (Qabs hn) 1).
      { apply (Qle_trans _ ((1 # 2) * (1 - r)) _).
        - exact Hhn_half_le.
        - apply (b3rr_1mr_half_le1 r). exact Hr0. }
      assert (Hq3 : Qlt e3 (Qminus (Qmult en k) (Qabs hn))).
      { apply (Qlt_le_trans e3 (Qminus (projT1 (real_mult eps rk) n) (projT1 (real_abs h) n))
                             (Qminus (Qmult en k) (Qabs hn))).
        - apply QltT_to_Qlt. apply (HN3 n (NatLe_lift _ _ Hn3)).
        - apply qeq_imp_qle.
          rewrite (real_abs_proj h n).
          unfold rk, en.
          setoid_rewrite (real_mult_proj eps (real_const k) n).
          cbn [real_zero real_const projT1]. reflexivity. }
      assert (Hhn_k : Qlt (Qabs hn) (Qmult en k)).
      { apply (Qlt_le_trans (Qabs hn) (Qminus (Qmult en k) e3) (Qmult en k)).
        - apply (q_lt_minus_shift e3 (Qmult en k) (Qabs hn)). exact Hq3.
        - assert (He30 : Qle 0 e3) by (apply Qlt_le_weak; apply QltT_to_Qlt; exact He3).
          apply (Qle_trans (Qminus (Qmult en k) e3) (Qplus (Qminus (Qmult en k) e3) e3)
                           (Qmult en k)).
          + apply (Qle_trans (Qminus (Qmult en k) e3) (Qplus (Qminus (Qmult en k) e3) 0)
                             (Qplus (Qminus (Qmult en k) e3) e3)).
            * apply qeq_imp_qle. ring.
            * apply (Qplus_le_compat (Qminus (Qmult en k) e3) (Qminus (Qmult en k) e3) 0 e3
                     (Qle_refl _) He30).
          + apply qeq_imp_qle. ring. }
      assert (Hhn_kle : Qle (Qabs hn) (Qmult en k)) by (apply Qlt_le_weak; exact Hhn_k).
      (* 域：|un| ≤ r *)
      assert (Hun_r : Qle (Qabs un) r).
      { apply (QleT'_to_Qle (Qabs un) r). apply Hxb. }
      assert (Hhvn0 : Qle 0 (Qabs hn)) by apply Qabs_nonneg.
      assert (Henhn0 : Qle 0 (Qmult en (Qabs hn))).
      { apply (Qmult_le_0_compat en (Qabs hn)). exact Hen0. exact Hhvn0. }
      (* 投影恒等（A 侧） *)
      assert (Hrepl : projT1 (real_abs (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                  (real_opp (real_plus (cauchy_real_arctan x (b3rr_dom_r1 x r Hxb Hr1))
                              (real_mult h wreal))))) n ==
                  Qabs (arctan_partial n yn - arctan_partial n un - hn * Qinv (1 + un * un))).
      { unfold yn, un, hn, wreal.
        rewrite (real_abs_proj (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                  (real_opp (real_plus (cauchy_real_arctan x (b3rr_dom_r1 x r Hxb Hr1))
                              (real_mult h (real_inv_pos (real_plus real_one (real_mult x x))
                                                         (b3r_one_sq_real_pos x)))))) n).
        rewrite (real_plus_proj (cauchy_real_arctan (real_plus x h) Hxh)
                  (real_opp (real_plus (cauchy_real_arctan x (b3rr_dom_r1 x r Hxb Hr1))
                              (real_mult h (real_inv_pos (real_plus real_one (real_mult x x))
                                                         (b3r_one_sq_real_pos x))))) n).
        rewrite (real_opp_proj (real_plus (cauchy_real_arctan x (b3rr_dom_r1 x r Hxb Hr1))
                              (real_mult h (real_inv_pos (real_plus real_one (real_mult x x))
                                                         (b3r_one_sq_real_pos x)))) n).
        rewrite (real_plus_proj (cauchy_real_arctan x (b3rr_dom_r1 x r Hxb Hr1))
                              (real_mult h (real_inv_pos (real_plus real_one (real_mult x x))
                                                         (b3r_one_sq_real_pos x))) n).
        rewrite (real_mult_proj h (real_inv_pos (real_plus real_one (real_mult x x))
                                                         (b3r_one_sq_real_pos x)) n).
        rewrite (arctan_real_proj (real_plus x h) Hxh n).
        rewrite (arctan_real_proj x (b3rr_dom_r1 x r Hxb Hr1) n).
        rewrite (real_plus_proj x h n).
        rewrite (HNinv n Hninv).
        rewrite (real_plus_proj real_one (real_mult x x) n).
        rewrite (real_mult_proj x x n).
        rewrite (b3r_one_proj n).
        apply Qabs_wd. ring. }
      (* B 侧投影 *)
      assert (HB : projT1 (real_plus (real_mult eps (real_abs h)) eps') n == en * Qabs hn + en').
      { unfold en, en', hn.
        setoid_rewrite (real_plus_proj (real_mult eps (real_abs h)) eps' n).
        setoid_rewrite (real_mult_proj eps (real_abs h) n).
        setoid_rewrite (real_abs_proj h n).
        cbn [real_zero real_const projT1]. ring. }
      (* 点主界 1：Cr·|hn|² ≤ en·|hn|·(1/4) *)
      assert (Hcbn : Qle (Qmult Cr (Qmult (Qabs hn) (Qabs hn)))
                         (Qmult (Qmult en (Qabs hn)) (1 # 4))).
      { apply (Qle_trans _ (Qmult Cr (Qmult (Qmult en k) (Qabs hn))) _).
        - (* |hn|·|hn| ≤ (en·k)·|hn|（右乘 |hn| ≥ 0），再左乘 Cr ≥ 0 *)
          apply (b3_qmult_le_l (Qmult (Qabs hn) (Qabs hn))
                               (Qmult (Qmult en k) (Qabs hn)) Cr).
          + exact HCr0.
          + apply (Qmult_le_compat_r (Qabs hn) (Qmult en k) (Qabs hn)).
            * exact Hhn_kle.
            * exact Hhvn0.
        - (* Cr·((en·k)·|hn|) == en·|hn|·(Cr·k) ≤ en·|hn|·(1/4) *)
          apply (Qle_trans _ (Qmult (Qmult en (Qabs hn)) (Qmult Cr k)) _).
          + apply qeq_imp_qle. ring.
          + apply (b3_qmult_le_l (Qmult Cr k) (1 # 4) (Qmult en (Qabs hn))).
            * exact Henhn0.
            * exact HCrK. }
      (* 点主界 2：r^{2(Sn)} ≤ eta（n ≥ Ng ⟹ 2(Sn) ≥ Ng） *)
      assert (Hdec2 : Qle (q_pow r (2 * Datatypes.S n)) eta).
      { apply (HNg ((2 * Datatypes.S n)%nat)). lia. }
      assert (Hpow14 : Qle (Qmult (Qabs hn) (q_pow r (2 * Datatypes.S n)))
                           (q_pow r (2 * Datatypes.S n))).
      { apply (Qle_trans _ (Qmult 1 (q_pow r (2 * Datatypes.S n))) _).
        - apply (Qmult_le_compat_r (Qabs hn) 1 (q_pow r (2 * Datatypes.S n))).
          + exact Hhn1.
          + apply q_pow_nonneg. exact Hr0.
        - apply qeq_imp_qle. ring. }
      (* 主点界：|D_n| ≤ en·|hn| + eta *)
      assert (Hm1 : Qle
        (Qabs (arctan_partial n yn - arctan_partial n un - hn * Qinv (1 + un * un)))
        (Qplus (Qmult Cr (Qmult (Qabs hn) (Qabs hn)))
               (Qmult (Qabs hn) (q_pow r (2 * Datatypes.S n))))).
      { unfold yn. apply (b3rr_core_r n un hn r Hr0 Hr1 Hun_r Hhn_half_le). }
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
        - apply (b3_qmult_le_l (1 # 4) 1 (Qmult en (Qabs hn))).
          + exact Henhn0.
          + unfold Qle. simpl. lia.
        - apply qeq_imp_qle. ring. }
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
        - (* eta < (en|hn|+en') − (en|hn|+eta) == en' − 2eta，由 en' > eps1' == 2eta *)
          apply (proj2 (Qlt_minus_iff eta
              (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qplus (Qmult en (Qabs hn)) eta)))).
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
                                (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qplus (Qmult en (Qabs hn)) eta)) ==
                          Qminus (Qplus (Qmult en (Qabs hn)) eta) (Qabs Dform)) by ring.
          rewrite Heq2.
          apply (proj1 (Qle_minus_iff (Qabs Dform) (Qplus (Qmult en (Qabs hn)) eta))).
          exact Hmain. }
      (* 投影桥（RHS − LHS）==（B − |D|） *)
      assert (Hrepl2 : Qeq
          (Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                  (projT1 (real_abs (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                  (real_opp (real_plus (cauchy_real_arctan x (b3rr_dom_r1 x r Hxb Hr1))
                              (real_mult h wreal))))) n))
          (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qabs Dform))).
      { apply (Qminus_comp (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                           (Qplus (Qmult en (Qabs hn)) en') HB
                           (projT1 (real_abs (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                           (real_opp (real_plus (cauchy_real_arctan x (b3rr_dom_r1 x r Hxb Hr1))
                                       (real_mult h wreal))))) n)
                           (Qabs Dform) Hrepl). }
      apply Qlt_to_QltT.
      assert (Hqfinal : Qlt eta
          (Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                  (projT1 (real_abs (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                  (real_opp (real_plus (cauchy_real_arctan x (b3rr_dom_r1 x r Hxb Hr1))
                              (real_mult h wreal))))) n))).
      { apply (Qlt_le_trans eta
          (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qabs Dform))
          (Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                  (projT1 (real_abs (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                  (real_opp (real_plus (cauchy_real_arctan x (b3rr_dom_r1 x r Hxb Hr1))
                              (real_mult h wreal))))) n))).
        - exact Hfin.
        - apply qeq_imp_qle. apply Qeq_sym. exact Hrepl2. }
      exact Hqfinal.

Defined.
(* ============================================================ *)
(* §2 显式 δ 下界证书族（真 Qed）                                *)
(* 实例：r := 1/2、x := real_const 0、eps := real_const e，       *)
(*   e ∈ {1/4, 1/8, 1/16}。                                       *)
(*   δ_e := projT1 (b5d1_b3rr_atan_deriv_lin (1#2) ... e ...)     *)
(*        == real_min (real_const ((1#2)·(1−1/2)))                *)
(*                    (real_mult (real_const e)                  *)
(*                               (real_const k(1/2)))            *)
(*   数值：k(1/2) = Qinv(4·(b3rr_C2(3/4)+1)) = 49/1732；          *)
(*   δ_{1/4} == 49/6928（≈7.07e−3）——P-d0 实证实例；              *)
(*   δ_{1/8} == 49/13856；δ_{1/16} == 49/27712（vm_compute 求值）。*)
(* 证据链：Defined 拷贝 → projT1 可计算（cbn）→ 闭式 Q 求值       *)
(*   （vm_compute）→ 逐点恒等 → real_eq → real_le 下界证书         *)
(*   （F1 取用形态 = real_le (real_const c) δ）。                  *)
(* ============================================================ *)

(* ---- 实例 δ 的具名见证（透明 Definition，闭式）——eps = 1/4 ---- *)
Definition b5d1_d4 : Real :=
  projT1 (b5d1_b3rr_atan_deriv_lin (1 # 2) b5d1_Hr0 b5d1_Hr1
            (real_const 0) b5d1_Hxr0 (real_const (1 # 4)) b5d1_Heps4).

(* 逐点恒等：projT1 b5d1_d4 n == 49#6928（全 n，无尾指标） *)
Lemma b5d1_d4_pt : forall n : nat, projT1 b5d1_d4 n == (49 # 6928).
Proof.
  intro n.
  cbn [projT1 b5d1_d4].
  vm_compute.
  reflexivity.
Qed.

(* real_eq：real_const (49#6928) ≈ b5d1_d4 *)
Lemma b5d1_d4_eq : real_eq (real_const (49 # 6928)) b5d1_d4.
Proof.
  apply real_eq_of_zero_diff.
  intro n.
  rewrite (b5d1_d4_pt n).
  cbn [projT1 real_const].
  reflexivity.
Qed.

(* 结论：δ_{1/4} ≥ real_const (49#6928)（real_le 右支：real_eq） *)
Lemma b5d1_d4_lb : real_le (real_const (49 # 6928)) b5d1_d4.
Proof.
  right. exact b5d1_d4_eq.
Qed.

(* ---- 实例 δ：eps = 1/8 ---- *)
Definition b5d1_d8 : Real :=
  projT1 (b5d1_b3rr_atan_deriv_lin (1 # 2) b5d1_Hr0 b5d1_Hr1
            (real_const 0) b5d1_Hxr0 (real_const (1 # 8)) b5d1_Heps8).

(* 逐点恒等：projT1 b5d1_d8 n == 49#13856 *)
Lemma b5d1_d8_pt : forall n : nat, projT1 b5d1_d8 n == (49 # 13856).
Proof.
  intro n.
  cbn [projT1 b5d1_d8].
  vm_compute.
  reflexivity.
Qed.

(* real_eq：real_const (49#13856) ≈ b5d1_d8 *)
Lemma b5d1_d8_eq : real_eq (real_const (49 # 13856)) b5d1_d8.
Proof.
  apply real_eq_of_zero_diff.
  intro n.
  rewrite (b5d1_d8_pt n).
  cbn [projT1 real_const].
  reflexivity.
Qed.

(* 结论：δ_{1/8} ≥ real_const (49#13856) *)
Lemma b5d1_d8_lb : real_le (real_const (49 # 13856)) b5d1_d8.
Proof.
  right. exact b5d1_d8_eq.
Qed.

(* ---- 实例 δ：eps = 1/16 ---- *)
Definition b5d1_d16 : Real :=
  projT1 (b5d1_b3rr_atan_deriv_lin (1 # 2) b5d1_Hr0 b5d1_Hr1
            (real_const 0) b5d1_Hxr0 (real_const (1 # 16)) b5d1_Heps16).

(* 逐点恒等：projT1 b5d1_d16 n == 49#27712 *)
Lemma b5d1_d16_pt : forall n : nat, projT1 b5d1_d16 n == (49 # 27712).
Proof.
  intro n.
  cbn [projT1 b5d1_d16].
  vm_compute.
  reflexivity.
Qed.

(* real_eq：real_const (49#27712) ≈ b5d1_d16 *)
Lemma b5d1_d16_eq : real_eq (real_const (49 # 27712)) b5d1_d16.
Proof.
  apply real_eq_of_zero_diff.
  intro n.
  rewrite (b5d1_d16_pt n).
  cbn [projT1 real_const].
  reflexivity.
Qed.

(* 结论：δ_{1/16} ≥ real_const (49#27712) *)
Lemma b5d1_d16_lb : real_le (real_const (49 # 27712)) b5d1_d16.
Proof.
  right. exact b5d1_d16_eq.
Qed.

(* 附注：0 < δ_e 可由 lb + real_const 正性复证；本族留作证书
   模式示范——δ-C/δ-D 对目标实例（x := real_const 0、eps := 其
   它有理常值）复制本 §2 三件即得（每实例 ~12 行机械追加）。 *)

(* ============================================================ *)
(* 块 item14（前缀 b5dD_——主件 b5dD_vdh_pts_r_exp）——来源：演变/.ablation/sc2_parallel/sc2_b5a_ode/sc2_b5a_item14.v。 *)
(* ============================================================ *)

(* ============================================================ *)
(* C8a b5dD_atan_deriv_b5a_r_exp（Defined 透明）                 *)
(* 拷贝源：213 根 b5c_atan_deriv_b5a_r（ConstructiveWorld.v      *)
(*   L79198–79255，58 行，机器抽取零手抄）；语句不变。            *)
(* 体内 destruct 源：b3rr_real_arctan_deriv_linear（根 Qed） →   *)
(*   b5d1_b3rr_atan_deriv_lin（上游 sc2_b5a_item5，Defined 透明，  *)
(*   δ-A item5 L98–419）；收尾 Qed→Defined（透明化是目的）。      *)
(* 注：b5c_inv_pos_cert_eq/b5a_one_plus_sq_pos/RealSetoid 族等    *)
(*   支撑全留根 CW（零拷贝）；本件为纯透传层。                   *)
(* ============================================================ *)

Lemma b5dD_atan_deriv_b5a_r_exp :
  forall (r : Q) (Hr0 : Qle 0 r) (Hr1 : Qlt r 1),
  forall (x : Real) (Hxr : forall n : nat, QleT' (Qabs (projT1 x n)) r),
  forall (eps : Real), real_lt real_zero eps ->
  sigT (fun delta : Real => And (real_lt real_zero delta)
    (forall (h : Real), real_lt (real_abs h) delta ->
      forall (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1),
      forall (eps' : Real), real_lt real_zero eps' ->
      real_le (real_abs (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                 (real_opp (real_plus (cauchy_real_arctan x (b3rr_dom_r1 x r Hxr Hr1))
                            (real_mult (real_inv_pos (real_plus real_one (real_mult x x))
                                                      (b5a_one_plus_sq_pos x)) h)))))
              (real_plus (real_mult eps (real_abs h)) eps'))).
Proof.
  intros r Hr0 Hr1 x Hxr eps Heps.
  destruct (b5d1_b3rr_atan_deriv_lin r Hr0 Hr1 x Hxr eps Heps)
    as [delta [Hd0 Hd]].
  exists delta. split.
  - exact Hd0.
  - intros h Hh Hxh eps' Heps'.
    set (I3 := real_inv_pos (real_plus real_one (real_mult x x)) (b3r_one_sq_real_pos x)).
    set (I5 := real_inv_pos (real_plus real_one (real_mult x x)) (b5a_one_plus_sq_pos x)).
    assert (Hinv : real_eq I5 I3).
    { unfold I5, I3. apply b5c_inv_pos_cert_eq. }
    assert (Hsl : real_eq (real_mult I5 h) (real_mult h I3)).
    { apply (real_eq_trans (real_mult I5 h) (real_mult h I5) (real_mult h I3)).
      - apply real_mult_comm.
      - apply (RealSetoid.real_eq_mult_compat h I5 h I3 (real_eq_refl h) Hinv). }
    apply (RealSetoid.real_le_compat
             (real_abs (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                        (real_opp (real_plus (cauchy_real_arctan x (b3rr_dom_r1 x r Hxr Hr1))
                                   (real_mult h I3)))))
             (real_abs (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                        (real_opp (real_plus (cauchy_real_arctan x (b3rr_dom_r1 x r Hxr Hr1))
                                   (real_mult I5 h)))))
             (real_plus (real_mult eps (real_abs h)) eps')
             (real_plus (real_mult eps (real_abs h)) eps')).
    { apply RealSetoid.real_eq_abs_compat.
      apply (RealSetoid.real_eq_plus_compat
               (cauchy_real_arctan (real_plus x h) Hxh)
               (real_opp (real_plus (cauchy_real_arctan x (b3rr_dom_r1 x r Hxr Hr1))
                                    (real_mult h I3)))
               (cauchy_real_arctan (real_plus x h) Hxh)
               (real_opp (real_plus (cauchy_real_arctan x (b3rr_dom_r1 x r Hxr Hr1))
                                    (real_mult I5 h)))).
      - apply real_eq_refl.
      - apply RealSetoid.real_eq_opp_compat.
        apply (RealSetoid.real_eq_plus_compat
                 (cauchy_real_arctan x (b3rr_dom_r1 x r Hxr Hr1))
                 (real_mult h I3)
                 (cauchy_real_arctan x (b3rr_dom_r1 x r Hxr Hr1))
                 (real_mult I5 h)).
        + apply real_eq_refl.
        + apply real_eq_sym. exact Hsl. }
    { apply real_eq_refl. }
    { unfold I3.
      exact (Hd h Hh Hxh eps' Heps'). }
Defined.

(* ============================================================ *)
(* C8b b5dD_vdh_pts_r_exp（Defined 透明）                        *)
(* 拷贝源：213 根 b5c_vdh_pts_r（ConstructiveWorld.v             *)
(*   L79265–79338，74 行，机器抽取零手抄）；语句不变（k2/k2p 已   *)
(*   显式入参）。                                                *)
(* 体内 destruct 源：b5c_atan_deriv_b5a_r（根 Qed） → 本文件 C8a  *)
(*   b5dD_atan_deriv_b5a_r_exp（Defined 透明）；收尾 Qed→Defined。*)
(* ============================================================ *)

Lemma b5dD_vdh_pts_r_exp : forall (r : Q) (Hr0 : Qle 0 r) (Hr1 : Qlt r 1)
  (x : Real) (Hxr : forall n : nat, QleT' (Qabs (projT1 x n)) r)
  (eps : Real) (Heps : real_lt real_zero eps)
  (k2 k2p : Q) (Hk2 : QltT 0 k2) (Hk2p : QltT 0 k2p),

  sigT (fun δa : Real => And (real_lt real_zero δa)
    (forall (h : Real), real_lt (real_abs h) δa ->
      forall (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1),
      forall (eps' : Real), real_lt real_zero eps' ->
      sigT (fun N : nat => forall n : nat, NatLe N n ->
        Qle (Qabs (Qminus (b5i_vn x h n) (Qmult (b5i_dn x n) (projT1 h n))))
            (Qplus (Qmult (Qmult (projT1 eps n) k2) (Qabs (projT1 h n)))
                   (Qmult (Qmult 2 k2p) (projT1 eps' n)))))).
Proof.
  intros r Hr0 Hr1 x Hxr eps Heps k2 k2p Hk2 Hk2p.
  set (Hx := b3rr_dom_r1 x r Hxr Hr1).
  set (eps2 := real_mult eps (real_const k2)).
  assert (Heps2 : real_lt real_zero eps2).
  { unfold eps2. apply real_mult_positive.
    - exact Heps.
    - apply real_const_pos. exact Hk2. }
  destruct (b5dD_atan_deriv_b5a_r_exp r Hr0 Hr1 x Hxr eps2 Heps2) as [δa [Hδa0 Hδa]].
  exists δa.
  split.
  - exact Hδa0.
  - intros h Hhδ Hxh eps' Heps'.
    set (eps2' := real_mult eps' (real_const k2p)).
    assert (Heps2' : real_lt real_zero eps2').
    { unfold eps2'. apply real_mult_positive.
      - exact Heps'.
      - apply real_const_pos. exact Hk2p. }
    set (V := real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                (real_opp (real_plus (cauchy_real_arctan x Hx)
                           (real_mult (real_inv_pos (real_plus real_one (real_mult x x))
                                                     (b5a_one_plus_sq_pos x)) h)))).
    assert (Habs : real_le (real_abs V)
                    (real_plus (real_mult eps2 (real_abs h)) eps2')).
    { unfold V, eps2, eps2'.
      exact (Hδa h Hhδ Hxh (real_mult eps' (real_const k2p)) Heps2'). }
    destruct (b5i_abs_le_pointwise V (real_plus (real_mult eps2 (real_abs h)) eps2')
               Habs eps2' Heps2') as [N HN].
    exists N.
    intros n Hn.
    set (en := projT1 eps n).
    set (en' := projT1 eps' n).
    set (hn := projT1 h n).
    assert (Hpt : Qle (Qabs (projT1 V n))
                      (Qplus (Qmult (Qmult en k2) (Qabs hn))
                             (Qmult (Qmult 2 k2p) en'))).
    { apply (Qle_trans (Qabs (projT1 V n))
                       (Qplus (projT1 (real_plus (real_mult eps2 (real_abs h)) eps2') n)
                              (projT1 eps2' n))
                       (Qplus (Qmult (Qmult en k2) (Qabs hn))
                              (Qmult (Qmult 2 k2p) en'))).
      - exact (HN n Hn).
      - apply qeq_imp_qle.
        setoid_rewrite (real_plus_proj (real_mult eps2 (real_abs h)) eps2' n).
        setoid_rewrite (real_mult_proj eps2 (real_abs h) n).
        setoid_rewrite (real_abs_proj h n).
        unfold eps2, eps2'.
        setoid_rewrite (real_mult_proj eps (real_const k2) n).
        rewrite (real_const_proj k2 n).
        setoid_rewrite (real_mult_proj eps' (real_const k2p) n).
        rewrite (real_const_proj k2p n).
        cbn [projT1].
        unfold en, en', hn.
        ring. }
    (* V 的 proj 与 b5i_vdh_absV 的 proj 定义性同（b5a_atan_d 展开） *)
    apply (b5i_vdh_absV x Hx h Hxh n
             (Qplus (Qmult (Qmult en k2) (Qabs hn))
                    (Qmult (Qmult 2 k2p) en'))).
    unfold b5a_atan_d, V in Hpt.
    exact Hpt.
Defined.

(* ============================================================ *)
(* end sc2_b5a_item14.v · δ-D1a C8 透明基座 *)
(* ============================================================ *)

(* ============================================================ *)
(* 块 item17（前缀 b5dG_——主件 b5dG_sin_atan_diff_closed_r_exp）——来源：演变/.ablation/sc2_parallel/sc2_b5a_ode/sc2_b5a_item17.v。 *)
(* ============================================================ *)

(* ============================================================ *)
(* C1t：b5dG_sin_atan_diff_closed_r_exp（Defined 透明）          *)
(* 拷贝源：上游 sc2_b5a_item9 C1 b5d5_sin_atan_diff_closed_r_expl *)
(*   （item9 L54–311，机器抽取零手抄）；语句不变（expl 形）。      *)
(* 体内 vdh destruct 源：b5c_vdh_pts_r（根 Qed）→ 本依赖          *)
(*   b5dD_vdh_pts_r_exp（上游 sc2_b5a_item14 C8b，Defined 透明）； *)
(*   收尾 Qed→Defined（透明化是目的）。                           *)
(* ============================================================ *)
Lemma b5dG_sin_atan_diff_closed_r_exp :
  forall (r : Q) (Hr0 : Qle 0 r) (Hr1 : Qlt r 1),
  forall (x : Real) (Hxr : forall n : nat, QleT' (Qabs (projT1 x n)) r),
  forall (Ms Mc C4 : Q),
  Qlt 0 Ms -> Qlt 0 Mc -> Qle 0 C4 -> QleT' 1 C4 ->
  (forall j : nat, QleT' (exp_series j 4) C4) ->
  (forall n : nat, Qle (Qabs (sin_partial n (arctan_partial n (projT1 x n)))) Ms) ->
  (forall n : nat, Qle (Qabs (cos_partial n (arctan_partial n (projT1 x n)))) Mc) ->
  forall (eps : Real), real_lt real_zero eps ->
  sigT (fun delta : Real => And (real_lt real_zero delta)
    (forall (h : Real), real_lt (real_abs h) delta ->
      forall (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1),
      forall (eps' : Real), real_lt real_zero eps' ->
      real_le (real_abs (b5a_comp_err_sin x (b3rr_dom_r1 x r Hxr Hr1) h Hxh))
              (real_plus (real_mult eps (real_abs h)) eps'))).
Proof.
  intros r Hr0 Hr1 x Hxr Ms Mc C4 HMsQ HMcQ HC40 HC4ge1 HC4 HMs_all HMc_all eps Heps.
  set (Hx := b3rr_dom_r1 x r Hxr Hr1).
  destruct (b5c_d_proj_le_one x) as [Nd Hd].
  destruct (b5n_eps_proj_lt eps Heps) as [e0 [He0T [Ne0 He0lt]]].
  assert (HMs0 : Qle 0 Ms). { apply Qlt_le_weak. exact HMsQ. }
  assert (HMc0 : Qle 0 Mc). { apply Qlt_le_weak. exact HMcQ. }
  set (S := Qplus Ms Mc).
  assert (HSlt : Qlt 0 S). { unfold S. nra. }
  set (K1e := Qplus (Qmult Ms (Qplus (Qmult 4 C4) 2))
                    (Qmult Mc (Qplus (Qmult 4 C4) 4))).
  assert (HK1_0 : Qle 0 K1e). { unfold K1e. nra. }
  set (kδ := Qinv (Qmult 512 (Qplus S 1))).
  set (k2 := Qinv (Qmult (Qmult 512 (Qplus S 1))
                         (Qplus (Qplus (Qmult 3 S) Mc) 1))).
  set (k2p := Qinv (Qmult (Qmult 1024 (Qplus K1e 1))
                          (Qplus (Qplus (Qmult 3 S) Mc) 1))).
  assert (HkδT : QltT 0 kδ).
  { unfold kδ. apply Qlt_to_QltT. apply Qinv_lt_0_compat. nra. }
  assert (Hk2T : QltT 0 k2).
  { unfold k2. apply Qlt_to_QltT. apply Qinv_lt_0_compat. nra. }
  assert (Hk2pT : QltT 0 k2p).
  { unfold k2p. apply Qlt_to_QltT. apply Qinv_lt_0_compat. nra. }
  assert (Hk2Q : Qle 0 k2). { apply Qlt_le_weak. apply QltT_to_Qlt. exact Hk2T. }
  assert (Hk2pQ : Qlt 0 k2p). { apply QltT_to_Qlt. exact Hk2pT. }
  (* 全局预算：coef（quad）、coefC（crude）、8k2p·K1（crude 强制） *)
  assert (HcoefQ : Qle (Qplus (Qmult (Qmult 2 (Qplus Ms Mc)) kδ)
                               (Qmult (Qplus (Qmult 3 (Qplus Ms Mc)) Mc) k2)) 1).
  { apply (Qle_trans (Qplus (Qmult (Qmult 2 (Qplus Ms Mc)) kδ)
                             (Qmult (Qplus (Qmult 3 (Qplus Ms Mc)) Mc) k2))
                     (Qplus (1 # 2) (1 # 2))
                     1).
    { apply Qplus_le_compat.
      { apply (b5n_2S_kδ_le S HSlt). }
      { apply (b5n_3S_Mc_k2_le S Mc HSlt HMc0). } }
    { nra. } }
  assert (HcoefC : Qle (Qmult Mc k2) 1).
  { apply (Qle_trans (Qmult Mc k2) (1 # 2) 1).
    { apply (b5n_Mc_k2_le S Mc HSlt HMc0). }
    { unfold Qle. simpl. lia. } }
  assert (Hk2pK1 : Qle (Qmult (Qmult 8 k2p)
                              (Qplus (Qmult Ms (Qplus (Qmult 4 C4) 2))
                                     (Qmult Mc (Qplus (Qmult 4 C4) 4)))) 1).
  { apply (b5n_8k2p_K1_le S Mc K1e HSlt HMc0 HK1_0). }
  (* δ 组装：0 < 各分量 *)
  assert (H12T : QltT 0 (1 # 2)) by (apply Qlt_to_QltT; unfold Qlt; simpl; lia).
  assert (H14T : QltT 0 (1 # 4)) by (apply Qlt_to_QltT; unfold Qlt; simpl; lia).
  destruct (b5dD_vdh_pts_r_exp r Hr0 Hr1 x Hxr eps Heps k2 k2p Hk2T Hk2pT) as [δa [Hδa0 Hδa]].
  assert (Hc12r : real_lt real_zero (real_const (1 # 2))).
  { apply real_const_pos. exact H12T. }
  assert (Hepskδ : real_lt real_zero (real_mult eps (real_const kδ))).
  { apply real_mult_positive.
    { exact Heps. }
    { apply real_const_pos. exact HkδT. } }
  assert (Hqtr : real_lt real_zero
            (real_mult (real_const (1 # 4))
                       (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
                                     (b5i_one_plus_eps2_pos eps k2 Heps Hk2T)))).
  { apply real_mult_positive.
    { apply real_const_pos. exact H14T. }
    { apply real_inv_pos_pos. } }
  set (delta := real_min
        (real_min (real_min δa (real_const (1 # 2)))
                  (real_mult eps (real_const kδ)))
        (real_mult (real_const (1 # 4))
                   (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
                                 (b5i_one_plus_eps2_pos eps k2 Heps Hk2T)))).
  assert (Hdpos : real_lt real_zero delta).
  { unfold delta.
    apply real_min_pos.
    { apply real_min_pos.
      { apply real_min_pos.
        { exact Hδa0. }
        { exact Hc12r. } }
      { exact Hepskδ. } }
    { exact Hqtr. } }
  exists delta.
  split.
  { exact Hdpos. }
  { intros h Hh Hxh eps' Heps'.
    destruct (b5n_eps_proj_lt eps' Heps') as [e1 [He1T [Ne1 He1lt]]].
    set (eta := Qmult (1 # 8) e1).
    assert (HetaT : QltT 0 eta).
    { unfold eta. apply Qlt_to_QltT.
      apply (Qmult_lt_0_compat (1 # 8) e1).
      { unfold Qlt. simpl. lia. }
      { apply QltT_to_Qlt. exact He1T. } }
    (* h 相对 δ 的四层 min 提取 *)
    assert (HhA : real_lt (real_abs h)
             (real_min (real_min δa (real_const (1 # 2))) (real_mult eps (real_const kδ)))).
    { apply (real_min_lt_l h
               (real_min (real_min δa (real_const (1 # 2))) (real_mult eps (real_const kδ)))
               (real_mult (real_const (1 # 4))
                          (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
                                        (b5i_one_plus_eps2_pos eps k2 Heps Hk2T)))).
      exact Hh. }
    assert (HhE : real_lt (real_abs h)
             (real_mult (real_const (1 # 4))
                        (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
                                      (b5i_one_plus_eps2_pos eps k2 Heps Hk2T)))).
    { apply (real_min_lt_r h
               (real_min (real_min δa (real_const (1 # 2))) (real_mult eps (real_const kδ)))
               (real_mult (real_const (1 # 4))
                          (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
                                        (b5i_one_plus_eps2_pos eps k2 Heps Hk2T)))).
      exact Hh. }
    assert (HhAA : real_lt (real_abs h) (real_min δa (real_const (1 # 2)))).
    { apply (real_min_lt_l h (real_min δa (real_const (1 # 2)))
                           (real_mult eps (real_const kδ))).
      exact HhA. }
    assert (Hhlr : real_lt (real_abs h) (real_mult eps (real_const kδ))).
    { apply (real_min_lt_r h (real_min δa (real_const (1 # 2)))
                           (real_mult eps (real_const kδ))).
      exact HhA. }
    assert (Hhda : real_lt (real_abs h) δa).
    { apply (real_min_lt_l h δa (real_const (1 # 2))). exact HhAA. }
    assert (Hh12 : real_lt (real_abs h) (real_const (1 # 2))).
    { apply (real_min_lt_r h δa (real_const (1 # 2))). exact HhAA. }
    (* X：b5n_h_pts *)
    destruct (b5n_h_pts h eps kδ k2 Heps HkδT Hk2T Hhlr Hh12 HhE) as [Nh HNh].
    (* Y：arctan' 于 eps2 := eps·k2 / eps2' := eps'·k2p *)
    destruct (Hδa h Hhda Hxh eps' Heps') as [Nw HNw].
    (* 列误差列 *)
    destruct (b5i_rs_addcol x Hx h Hxh eta HetaT) as [Nc HNc].
    (* 逐点预算（对 eps' 见证） *)
    assert (Hen'g : forall n : nat, NatLe Ne1 n -> Qle 0 (projT1 eps' n)).
    { intros n Hn.
      apply (Qle_trans 0 e1 (projT1 eps' n)).
      { apply Qlt_le_weak. apply QltT_to_Qlt. exact He1T. }
      { apply Qlt_le_weak. exact (He1lt n Hn). } }
    assert (HcolQ8_all : forall n : nat, NatLe Ne1 n ->
            Qle eta (Qmult (1 # 8) (projT1 eps' n))).
    { intros n Hn.
      unfold eta.
      apply (sc_qmult_le_l e1 (projT1 eps' n) (1 # 8)).
      { apply Qlt_le_weak. exact (He1lt n Hn). }
      { unfold Qle. simpl. lia. } }
    assert (HaddQ_all : forall n : nat, NatLe Ne1 n ->
            Qle (Qmult (Qplus (Qmult 3 (Qplus Ms Mc)) Mc)
                       (Qmult (Qmult 2 k2p) (projT1 eps' n)))
                (Qmult (1 # 32) (projT1 eps' n))).
    { intros n Hn.
      apply (Qle_trans
               (Qmult (Qplus (Qmult 3 (Qplus Ms Mc)) Mc)
                      (Qmult (Qmult 2 k2p) (projT1 eps' n)))
               (Qmult (Qmult (Qplus (Qmult 3 S) Mc) (Qmult 2 k2p))
                      (projT1 eps' n))
               (Qmult (1 # 32) (projT1 eps' n))).
      { apply qeq_imp_qle. unfold S. ring. }
      { apply (Qmult_le_compat_r
                 (Qmult (Qplus (Qmult 3 S) Mc) (Qmult 2 k2p))
                 (1 # 32) (projT1 eps' n)).
        { apply (b5n_3S_Mc_2k2p_le S Mc K1e HSlt HMc0 HK1_0). }
        { exact (Hen'g n Hn). } } }
    assert (HaddC_all : forall n : nat, NatLe Ne1 n ->
            Qle (Qmult Mc (Qmult (Qmult 2 k2p) (projT1 eps' n)))
                (Qmult (1 # 32) (projT1 eps' n))).
    { intros n Hn.
      apply (Qle_trans
               (Qmult Mc (Qmult (Qmult 2 k2p) (projT1 eps' n)))
               (Qmult (Qmult Mc (Qmult 2 k2p)) (projT1 eps' n))
               (Qmult (1 # 32) (projT1 eps' n))).
      { apply qeq_imp_qle. ring. }
      { apply (Qmult_le_compat_r (Qmult Mc (Qmult 2 k2p)) (1 # 32)
                                 (projT1 eps' n)).
        { apply (b5n_Mc_2k2p_le S Mc K1e HSlt HMc0 HK1_0). }
        { exact (Hen'g n Hn). } } }
    (* 主装配：real_le → real_lt（左支），见证 eta *)
    set (Nmax := Nat.max (Nat.max Ne0 Ne1) (Nat.max (Nat.max Nh Nw) (Nat.max Nc Nd))).
    left.
    exists eta.
    split.
    { exact HetaT. }
    { exists Nmax.
      intros n Hn.
      apply NatLe_drop in Hn.
      set (en := projT1 eps n).
      set (en' := projT1 eps' n).
      set (hn := Qabs (projT1 h n)).
      set (Dn := Qabs (projT1 (b5a_comp_err_sin x Hx h Hxh) n)).
      assert (HnNe0 : NatLe Ne0 n) by (apply NatLe_lift; lia).
      assert (HnNe1 : NatLe Ne1 n) by (apply NatLe_lift; lia).
      assert (HnNh : NatLe Nh n) by (apply NatLe_lift; lia).
      assert (HnNw : NatLe Nw n) by (apply NatLe_lift; lia).
      assert (HnNc : NatLe Nc n) by (apply NatLe_lift; lia).
      assert (HnNd : (Nd <= n)%nat) by lia.
      assert (Hen0 : Qle 0 en).
      { unfold en. apply (Qle_trans 0 e0 (projT1 eps n)).
        { apply Qlt_le_weak. apply QltT_to_Qlt. exact He0T. }
        { apply Qlt_le_weak. exact (He0lt n HnNe0). } }
      assert (Hen'0 : Qle 0 en').
      { unfold en'. exact (Hen'g n HnNe1). }
      destruct (HNh n HnNh) as [Hhδn [Hh12n Hhqn]].
      (* Z：per-n 主界 *)
      assert (Hmain : Qle (Qabs (projT1 (b5a_comp_err_sin x Hx h Hxh) n))
                          (Qplus (Qmult en (Qabs (projT1 h n))) (Qmult (3 # 4) en'))).
      { apply (b5n_pern_main x Hx h Hxh n Ms Mc C4 eta kδ k2 k2p en en').
        { exact (HMs_all n). }
        { exact (HMc_all n). }
        { exact HC4. }
        { exact HC40. }
        { exact (HNc n HnNc). }
        { exact (QleT'_to_Qle _ _ Hhδn). }
        { exact (QleT'_to_Qle _ _ Hh12n). }
        { exact (QleT'_to_Qle _ _ Hhqn). }
        { exact (HNw n HnNw). }
        { unfold b5i_dn. exact (Hd n HnNd). }
        { exact Hen0. }
        { exact Hen'0. }
        { exact Hk2Q. }
        { exact Hk2pQ. }
        { exact HcoefQ. }
        { exact HcoefC. }
        { exact (HcolQ8_all n HnNe1). }
        { exact (HaddQ_all n HnNe1). }
        { exact (HaddC_all n HnNe1). }
        { exact Hk2pK1. } }
      (* margin：eta < (1/4)en'；Hfin：eta < (en·hn + en') − Dn *)
      assert (Hq4e : Qlt eta (Qmult (1 # 4) en')).
      { unfold eta, en'. apply (b5n_quarter_gt e1 (projT1 eps' n)).
        { apply QltT_to_Qlt. exact He1T. }
        { exact (He1lt n HnNe1). } }
      assert (Hfin : Qlt eta (Qminus (Qplus (Qmult en hn) en') Dn)).
      { apply (b5n_close Dn hn en en' eta).
        { unfold Dn. exact Hmain. }
        { unfold en'. exact Hq4e. } }
      assert (Hrepl : Qeq (Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                                  (projT1 (real_abs (b5a_comp_err_sin x Hx h Hxh)) n))
                          (Qminus (Qplus (Qmult en hn) en') Dn)).
      { unfold en, en', hn, Dn.
        setoid_rewrite (real_plus_proj (real_mult eps (real_abs h)) eps' n).
        setoid_rewrite (real_mult_proj eps (real_abs h) n).
        setoid_rewrite (real_abs_proj h n).
        setoid_rewrite (real_abs_proj (b5a_comp_err_sin x Hx h Hxh) n).
        ring. }
      apply Qlt_to_QltT.
      apply (Qlt_le_trans eta
             (Qminus (Qplus (Qmult en hn) en') Dn)
             (Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                     (projT1 (real_abs (b5a_comp_err_sin x Hx h Hxh)) n))).
      { exact Hfin. }
      { apply qeq_imp_qle. apply Qeq_sym. exact Hrepl. } } }
Defined.
(* ============================================================ *)
(* C2t：b5dG_cos_atan_diff_closed_r_exp（Defined 透明）          *)
(* 拷贝源：上游 sc2_b5a_item9 C2 b5d5_cos_atan_diff_closed_r_expl *)
(*   （item9 L318–575，机器抽取零手抄）；语句不变（expl 形）。     *)
(* 体内 vdh destruct 源：b5c_vdh_pts_r（根 Qed）→ 本依赖          *)
(*   b5dD_vdh_pts_r_exp（上游 sc2_b5a_item14 C8b，Defined 透明）； *)
(*   收尾 Qed→Defined（透明化是目的）。                           *)
(* ============================================================ *)
Lemma b5dG_cos_atan_diff_closed_r_exp :
  forall (r : Q) (Hr0 : Qle 0 r) (Hr1 : Qlt r 1),
  forall (x : Real) (Hxr : forall n : nat, QleT' (Qabs (projT1 x n)) r),
  forall (Ms Mc C4 : Q),
  Qlt 0 Ms -> Qlt 0 Mc -> Qle 0 C4 -> QleT' 1 C4 ->
  (forall j : nat, QleT' (exp_series j 4) C4) ->
  (forall n : nat, Qle (Qabs (sin_partial n (arctan_partial n (projT1 x n)))) Ms) ->
  (forall n : nat, Qle (Qabs (cos_partial n (arctan_partial n (projT1 x n)))) Mc) ->
  forall (eps : Real), real_lt real_zero eps ->
  sigT (fun delta : Real => And (real_lt real_zero delta)
    (forall (h : Real), real_lt (real_abs h) delta ->
      forall (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1),
      forall (eps' : Real), real_lt real_zero eps' ->
      real_le (real_abs (b5a_comp_err_cos x (b3rr_dom_r1 x r Hxr Hr1) h Hxh))
              (real_plus (real_mult eps (real_abs h)) eps'))).
Proof.
  intros r Hr0 Hr1 x Hxr Ms Mc C4 HMsQ HMcQ HC40 HC4ge1 HC4 HMs_all HMc_all eps Heps.
  set (Hx := b3rr_dom_r1 x r Hxr Hr1).
  destruct (b5c_d_proj_le_one x) as [Nd Hd].
  destruct (b5n_eps_proj_lt eps Heps) as [e0 [He0T [Ne0 He0lt]]].
  assert (HMs0 : Qle 0 Ms). { apply Qlt_le_weak. exact HMsQ. }
  assert (HMc0 : Qle 0 Mc). { apply Qlt_le_weak. exact HMcQ. }
  set (S := Qplus Ms Mc).
  assert (HSlt : Qlt 0 S). { unfold S. nra. }
  set (K1e := Qplus (Qmult Mc (Qplus (Qmult 4 C4) 2))
                    (Qmult Ms (Qplus (Qmult 4 C4) 4))).
  assert (HK1_0 : Qle 0 K1e). { unfold K1e. nra. }
  set (kδ := Qinv (Qmult 512 (Qplus S 1))).
  set (k2 := Qinv (Qmult (Qmult 512 (Qplus S 1))
                         (Qplus (Qplus (Qmult 3 S) Ms) 1))).
  set (k2p := Qinv (Qmult (Qmult 1024 (Qplus K1e 1))
                          (Qplus (Qplus (Qmult 3 S) Ms) 1))).
  assert (HkδT : QltT 0 kδ).
  { unfold kδ. apply Qlt_to_QltT. apply Qinv_lt_0_compat. nra. }
  assert (Hk2T : QltT 0 k2).
  { unfold k2. apply Qlt_to_QltT. apply Qinv_lt_0_compat. nra. }
  assert (Hk2pT : QltT 0 k2p).
  { unfold k2p. apply Qlt_to_QltT. apply Qinv_lt_0_compat. nra. }
  assert (Hk2Q : Qle 0 k2). { apply Qlt_le_weak. apply QltT_to_Qlt. exact Hk2T. }
  assert (Hk2pQ : Qlt 0 k2p). { apply QltT_to_Qlt. exact Hk2pT. }
  (* 全局预算：coef（quad）、coefC（crude）、8k2p·K1e（crude 强制） *)
  assert (HcoefQ : Qle (Qplus (Qmult (Qmult 2 (Qplus Ms Mc)) kδ)
                               (Qmult (Qplus (Qmult 3 (Qplus Ms Mc)) Ms) k2)) 1).
  { apply (Qle_trans (Qplus (Qmult (Qmult 2 (Qplus Ms Mc)) kδ)
                            (Qmult (Qplus (Qmult 3 (Qplus Ms Mc)) Ms) k2))
                     (Qplus (1 # 2) (1 # 2))
                     1).
    { apply Qplus_le_compat.
      { apply (b5n_2S_kδ_le S HSlt). }
      { apply (b5n_3S_Mc_k2_le S Ms HSlt HMs0). } }
    { nra. } }
  assert (HcoefC : Qle (Qmult Ms k2) 1).
  { apply (Qle_trans (Qmult Ms k2) (1 # 2) 1).
    { apply (b5n_Mc_k2_le S Ms HSlt HMs0). }
    { unfold Qle. simpl. lia. } }
  assert (Hk2pK1 : Qle (Qmult (Qmult 8 k2p)
                              (Qplus (Qmult Mc (Qplus (Qmult 4 C4) 2))
                                     (Qmult Ms (Qplus (Qmult 4 C4) 4)))) 1).
  { apply (b5n_8k2p_K1_le S Ms K1e HSlt HMs0 HK1_0). }
  (* δ 组装：0 < 各分量 *)
  assert (H12T : QltT 0 (1 # 2)) by (apply Qlt_to_QltT; unfold Qlt; simpl; lia).
  assert (H14T : QltT 0 (1 # 4)) by (apply Qlt_to_QltT; unfold Qlt; simpl; lia).
  destruct (b5dD_vdh_pts_r_exp r Hr0 Hr1 x Hxr eps Heps k2 k2p Hk2T Hk2pT) as [δa [Hδa0 Hδa]].
  assert (Hc12r : real_lt real_zero (real_const (1 # 2))).
  { apply real_const_pos. exact H12T. }
  assert (Hepskδ : real_lt real_zero (real_mult eps (real_const kδ))).
  { apply real_mult_positive.
    { exact Heps. }
    { apply real_const_pos. exact HkδT. } }
  assert (Hqtr : real_lt real_zero
            (real_mult (real_const (1 # 4))
                       (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
                                     (b5i_one_plus_eps2_pos eps k2 Heps Hk2T)))).
  { apply real_mult_positive.
    { apply real_const_pos. exact H14T. }
    { apply real_inv_pos_pos. } }
  set (delta := real_min
        (real_min (real_min δa (real_const (1 # 2)))
                  (real_mult eps (real_const kδ)))
        (real_mult (real_const (1 # 4))
                   (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
                                 (b5i_one_plus_eps2_pos eps k2 Heps Hk2T)))).
  assert (Hdpos : real_lt real_zero delta).
  { unfold delta.
    apply real_min_pos.
    { apply real_min_pos.
      { apply real_min_pos.
        { exact Hδa0. }
        { exact Hc12r. } }
      { exact Hepskδ. } }
    { exact Hqtr. } }
  exists delta.
  split.
  { exact Hdpos. }
  { intros h Hh Hxh eps' Heps'.
    destruct (b5n_eps_proj_lt eps' Heps') as [e1 [He1T [Ne1 He1lt]]].
    set (eta := Qmult (1 # 8) e1).
    assert (HetaT : QltT 0 eta).
    { unfold eta. apply Qlt_to_QltT.
      apply (Qmult_lt_0_compat (1 # 8) e1).
      { unfold Qlt. simpl. lia. }
      { apply QltT_to_Qlt. exact He1T. } }
    (* h 相对 δ 的四层 min 提取 *)
    assert (HhA : real_lt (real_abs h)
             (real_min (real_min δa (real_const (1 # 2))) (real_mult eps (real_const kδ)))).
    { apply (real_min_lt_l h
               (real_min (real_min δa (real_const (1 # 2))) (real_mult eps (real_const kδ)))
               (real_mult (real_const (1 # 4))
                          (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
                                        (b5i_one_plus_eps2_pos eps k2 Heps Hk2T)))).
      exact Hh. }
    assert (HhE : real_lt (real_abs h)
             (real_mult (real_const (1 # 4))
                        (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
                                      (b5i_one_plus_eps2_pos eps k2 Heps Hk2T)))).
    { apply (real_min_lt_r h
               (real_min (real_min δa (real_const (1 # 2))) (real_mult eps (real_const kδ)))
               (real_mult (real_const (1 # 4))
                          (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
                                        (b5i_one_plus_eps2_pos eps k2 Heps Hk2T)))).
      exact Hh. }
    assert (HhAA : real_lt (real_abs h) (real_min δa (real_const (1 # 2)))).
    { apply (real_min_lt_l h (real_min δa (real_const (1 # 2)))
                           (real_mult eps (real_const kδ))).
      exact HhA. }
    assert (Hhlr : real_lt (real_abs h) (real_mult eps (real_const kδ))).
    { apply (real_min_lt_r h (real_min δa (real_const (1 # 2)))
                           (real_mult eps (real_const kδ))).
      exact HhA. }
    assert (Hhda : real_lt (real_abs h) δa).
    { apply (real_min_lt_l h δa (real_const (1 # 2))). exact HhAA. }
    assert (Hh12 : real_lt (real_abs h) (real_const (1 # 2))).
    { apply (real_min_lt_r h δa (real_const (1 # 2))). exact HhAA. }
    (* X：b5n_h_pts *)
    destruct (b5n_h_pts h eps kδ k2 Heps HkδT Hk2T Hhlr Hh12 HhE) as [Nh HNh].
    (* Y：arctan' 于 eps2 := eps·k2 / eps2' := eps'·k2p *)
    destruct (Hδa h Hhda Hxh eps' Heps') as [Nw HNw].
    (* 列误差列（cos 侧） *)
    destruct (b5d_rs_addcol_cos x Hx h Hxh eta HetaT) as [Nc HNc].
    (* 逐点预算（对 eps' 见证） *)
    assert (Hen'g : forall n : nat, NatLe Ne1 n -> Qle 0 (projT1 eps' n)).
    { intros n Hn.
      apply (Qle_trans 0 e1 (projT1 eps' n)).
      { apply Qlt_le_weak. apply QltT_to_Qlt. exact He1T. }
      { apply Qlt_le_weak. exact (He1lt n Hn). } }
    assert (HcolQ8_all : forall n : nat, NatLe Ne1 n ->
            Qle eta (Qmult (1 # 8) (projT1 eps' n))).
    { intros n Hn.
      unfold eta.
      apply (sc_qmult_le_l e1 (projT1 eps' n) (1 # 8)).
      { apply Qlt_le_weak. exact (He1lt n Hn). }
      { unfold Qle. simpl. lia. } }
    assert (HaddQ_all : forall n : nat, NatLe Ne1 n ->
            Qle (Qmult (Qplus (Qmult 3 (Qplus Ms Mc)) Ms)
                       (Qmult (Qmult 2 k2p) (projT1 eps' n)))
                (Qmult (1 # 32) (projT1 eps' n))).
    { intros n Hn.
      apply (Qle_trans
               (Qmult (Qplus (Qmult 3 (Qplus Ms Mc)) Ms)
                      (Qmult (Qmult 2 k2p) (projT1 eps' n)))
               (Qmult (Qmult (Qplus (Qmult 3 S) Ms) (Qmult 2 k2p))
                      (projT1 eps' n))
               (Qmult (1 # 32) (projT1 eps' n))).
      { apply qeq_imp_qle. unfold S. ring. }
      { apply (Qmult_le_compat_r
                 (Qmult (Qplus (Qmult 3 S) Ms) (Qmult 2 k2p))
                 (1 # 32) (projT1 eps' n)).
        { apply (b5n_3S_Mc_2k2p_le S Ms K1e HSlt HMs0 HK1_0). }
        { exact (Hen'g n Hn). } } }
    assert (HaddC_all : forall n : nat, NatLe Ne1 n ->
            Qle (Qmult Ms (Qmult (Qmult 2 k2p) (projT1 eps' n)))
                (Qmult (1 # 32) (projT1 eps' n))).
    { intros n Hn.
      apply (Qle_trans
               (Qmult Ms (Qmult (Qmult 2 k2p) (projT1 eps' n)))
               (Qmult (Qmult Ms (Qmult 2 k2p)) (projT1 eps' n))
               (Qmult (1 # 32) (projT1 eps' n))).
      { apply qeq_imp_qle. ring. }
      { apply (Qmult_le_compat_r (Qmult Ms (Qmult 2 k2p)) (1 # 32)
                                 (projT1 eps' n)).
        { apply (b5n_Mc_2k2p_le S Ms K1e HSlt HMs0 HK1_0). }
        { exact (Hen'g n Hn). } } }
    (* 主装配：real_le → real_lt（左支），见证 eta *)
    set (Nmax := Nat.max (Nat.max Ne0 Ne1) (Nat.max (Nat.max Nh Nw) (Nat.max Nc Nd))).
    left.
    exists eta.
    split.
    { exact HetaT. }
    { exists Nmax.
      intros n Hn.
      apply NatLe_drop in Hn.
      set (en := projT1 eps n).
      set (en' := projT1 eps' n).
      set (hn := Qabs (projT1 h n)).
      set (Dn := Qabs (projT1 (b5a_comp_err_cos x Hx h Hxh) n)).
      assert (HnNe0 : NatLe Ne0 n) by (apply NatLe_lift; lia).
      assert (HnNe1 : NatLe Ne1 n) by (apply NatLe_lift; lia).
      assert (HnNh : NatLe Nh n) by (apply NatLe_lift; lia).
      assert (HnNw : NatLe Nw n) by (apply NatLe_lift; lia).
      assert (HnNc : NatLe Nc n) by (apply NatLe_lift; lia).
      assert (HnNd : (Nd <= n)%nat) by lia.
      assert (Hen0 : Qle 0 en).
      { unfold en. apply (Qle_trans 0 e0 (projT1 eps n)).
        { apply Qlt_le_weak. apply QltT_to_Qlt. exact He0T. }
        { apply Qlt_le_weak. exact (He0lt n HnNe0). } }
      assert (Hen'0 : Qle 0 en').
      { unfold en'. exact (Hen'g n HnNe1). }
      destruct (HNh n HnNh) as [Hhδn [Hh12n Hhqn]].
      (* Z：per-n 主界（cos 版） *)
      assert (Hmain : Qle (Qabs (projT1 (b5a_comp_err_cos x Hx h Hxh) n))
                          (Qplus (Qmult en (Qabs (projT1 h n))) (Qmult (3 # 4) en'))).
      { apply (b5d_pern_main_cos x Hx h Hxh n Ms Mc C4 eta kδ k2 k2p en en').
        { exact (HMs_all n). }
        { exact (HMc_all n). }
        { exact HC4. }
        { exact HC40. }
        { exact (HNc n HnNc). }
        { exact (QleT'_to_Qle _ _ Hhδn). }
        { exact (QleT'_to_Qle _ _ Hh12n). }
        { exact (QleT'_to_Qle _ _ Hhqn). }
        { exact (HNw n HnNw). }
        { unfold b5i_dn. exact (Hd n HnNd). }
        { exact Hen0. }
        { exact Hen'0. }
        { exact Hk2Q. }
        { exact Hk2pQ. }
        { exact HcoefQ. }
        { exact HcoefC. }
        { exact (HcolQ8_all n HnNe1). }
        { exact (HaddQ_all n HnNe1). }
        { exact (HaddC_all n HnNe1). }
        { exact Hk2pK1. } }
      (* margin：eta < (1/4)en'；Hfin：eta < (en·hn + en') − Dn *)
      assert (Hq4e : Qlt eta (Qmult (1 # 4) en')).
      { unfold eta, en'. apply (b5n_quarter_gt e1 (projT1 eps' n)).
        { apply QltT_to_Qlt. exact He1T. }
        { exact (He1lt n HnNe1). } }
      assert (Hfin : Qlt eta (Qminus (Qplus (Qmult en hn) en') Dn)).
      { apply (b5n_close Dn hn en en' eta).
        { unfold Dn. exact Hmain. }
        { unfold en'. exact Hq4e. } }
      assert (Hrepl : Qeq (Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                                  (projT1 (real_abs (b5a_comp_err_cos x Hx h Hxh)) n))
                          (Qminus (Qplus (Qmult en hn) en') Dn)).
      { unfold en, en', hn, Dn.
        setoid_rewrite (real_plus_proj (real_mult eps (real_abs h)) eps' n).
        setoid_rewrite (real_mult_proj eps (real_abs h) n).
        setoid_rewrite (real_abs_proj h n).
        setoid_rewrite (real_abs_proj (b5a_comp_err_cos x Hx h Hxh) n).
        ring. }
      apply Qlt_to_QltT.
      apply (Qlt_le_trans eta
             (Qminus (Qplus (Qmult en hn) en') Dn)
             (Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                     (projT1 (real_abs (b5a_comp_err_cos x Hx h Hxh)) n))).
      { exact Hfin. }
      { apply qeq_imp_qle. apply Qeq_sym. exact Hrepl. } } }
Defined.
(* ============================================================ *)
(* end sc2_b5a_item17.v · δ-D1b sin/cos-atan expl 透明层 *)
(* ============================================================ *)

(* ============================================================ *)
(* 块 item23（前缀 b5dM_——主件 b5dM_real_const_pos）——来源：演变/.ablation/sc2_parallel/sc2_b5a_ode/sc2_b5a_item23.v。 *)
(* ============================================================ *)

(* ============================================================ *)
(* 件 1 b5dM_real_const_pos（Defined 透明）                     *)
(* 拷贝源：根 real_const_pos（ConstructiveWorld.v L36290；体     *)
(*   L36291–36314）。语句逐字；体近逐字（体内零根 Qed 见证       *)
(*   destruct——纯 Q 层推理 + qeq_le/ring/field，透明）；收尾     *)
(*   Defined。见证首分量 = c/2（显式），N := 0（显式）⟹ 值路径   *)
(*   可算（检验 ①：(1#4) → (1#8)）。                            *)
(* —— D3 消融裁定（AB2 判据4-P3）：本件与 S07 根件        *)
(*   real_const_pos 语句逐字同、体逐字同（唯一差=本件 Defined/      *)
(*   根件 Qed＋根件体多一行目标注释）；但透明性=语义承载面：        *)
(*   b5dQ_margin 链 cbn δ 列表（本文件 L9445/9486/9546）显式        *)
(*   unfolding 本件以暴露见证 c/2 ⟹ redirect 至 Qed 根件即值       *)
(*   路径受阻（E317 判例同型：不透明证书内嵌值路径 ⟹ stuck、        *)
(*   换源 rc=1）。结论=保留双件：本件为透明证书正典，S07 根件为     *)
(*   命题面正典，互不替代；后继 AB 扫描禁再标红为可 redirect 件。   *)
(* ============================================================ *)
Lemma b5dM_real_const_pos : forall (c : Q), QltT 0 c -> real_lt real_zero (real_const c).
Proof.
  intros c Hc.
  assert (Hhalf : Qlt 0 (c / 2)).
  { apply Qlt_shift_div_l; [change (Qlt 0 2); compute; reflexivity | simpl; apply QltT_to_Qlt; exact Hc]. }
  exists (c / 2). split.
  - apply Qlt_to_QltT. exact Hhalf.
  - exists 0%nat. intros n Hn. apply Qlt_to_QltT.
    apply (Qlt_le_trans _ (c / 2 + c / 2) _).
    + apply (Qle_lt_trans _ (c / 2 + 0) _).
      * apply qeq_le. ring.
      * apply (proj2 (Qplus_lt_r 0 (c / 2) (c / 2)) Hhalf).
    + apply qeq_le.
      assert (Hc' : projT1 (real_const c) n == c) by (apply real_const_proj).
      assert (Hz' : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
      setoid_rewrite Hc'. setoid_rewrite Hz'.
      unfold Qminus. transitivity (c + 0).
      * field.
      * assert (Hopp0 : Qopp 0%Q == 0%Q).
        { transitivity (Qred (Qmake 0 1)).
          - reflexivity.
          - apply Qred_correct. }
        rewrite Hopp0. reflexivity.
Defined.

(* ============================================================ *)
(* 件 2 b5dM_real_two_pos_local（Defined 透明）                 *)
(* 拷贝源：根 real_two_pos_local（ConstructiveWorld.v L44573；  *)
(*   体 L44574–44579 禁抄——根体经 real_eq_lt_lt /               *)
(*   real_lt_plus_compat / real_lt_zero_one（根 Qed 链）⟹ 见证   *)
(*   首分量不透明）。直构显式见证：exists (1#2) + N := 0，两分支 *)
(*   全闭式计算（样板 = 上游 sc2_b5a_item20 J0 b5dJ_two_pos_exp  *)
(*   L77–84）；Defined 收尾 ⟹                                    *)
(*   projT1 (real_inv_pos (1+1) 本件) n 全 n 可算 = Qinv 2。     *)
(* ============================================================ *)
Lemma b5dM_real_two_pos_local : real_lt real_zero (real_plus real_one real_one).
Proof.
  unfold real_lt.
  exists (1 # 2).
  split.
  - vm_compute. constructor.
  - exists 0%nat. intros n Hn. vm_compute. constructor.
Defined.

(* ============================================================ *)
(* 件 3 b5dM_b5i_one_plus_eps2_pos（Defined 透明）              *)
(* 拷贝源：根 b5i_one_plus_eps2_pos（ConstructiveWorld.v        *)
(*   L76147；体 L76151–76185）。语句逐字；体近逐字（体内仅       *)
(*   destruct 输入 Heps——合法，实例化后具体化；见证已显式        *)
(*   exists (1#2)，N := 输入 N1）；收尾 Defined。               *)
(* 值路径：projT1 (本件 eps k2 Heps Hk2) = (1#2)（与输入无关，   *)
(*   检验 ③ 实证）；N1 来自输入 Heps destruct——输入为透明链时   *)
(*   （如件 1 拷贝）整链可归约。                                *)
(* ============================================================ *)
Lemma b5dM_b5i_one_plus_eps2_pos : forall (eps : Real) (k2 : Q),
  real_lt real_zero eps -> QltT 0 k2 ->
  real_lt real_zero (real_plus real_one (real_mult eps (real_const k2))).
Proof.
  intros eps k2 Heps Hk2.
  destruct Heps as [eps1 [Heps1 [N1 HN1]]].
  unfold real_lt.
  exists (1 # 2).
  split.
  - apply Qlt_to_QltT. unfold Qlt. simpl. lia.
  - exists N1.
    intros n Hn.
    apply Qlt_to_QltT.
    assert (Hen : Qlt 0 (projT1 eps n)).
    { apply (Qlt_le_trans 0 eps1 (projT1 eps n)).
      - apply QltT_to_Qlt. exact Heps1.
      - apply (Qle_trans eps1 (Qminus (projT1 eps n) (projT1 real_zero n)) (projT1 eps n)).
        + apply Qlt_le_weak. apply QltT_to_Qlt. exact (HN1 n Hn).
        + apply qeq_le. cbn [projT1 real_zero]. ring. }
    apply (Qlt_le_trans (1 # 2) 1
                        (Qminus (projT1 (real_plus real_one (real_mult eps (real_const k2))) n)
                                (projT1 real_zero n))).
    + unfold Qlt. simpl. lia.
    + apply (Qle_trans 1 (Qplus 1 (Qmult (projT1 eps n) k2))
                       (Qminus (projT1 (real_plus real_one (real_mult eps (real_const k2))) n)
                               (projT1 real_zero n))).
      * apply (Qle_trans 1 (Qplus 1 0) (Qplus 1 (Qmult (projT1 eps n) k2))).
        -- apply qeq_le. ring.
        -- apply Qplus_le_compat.
           ++ apply Qle_refl.
           ++ apply (Qmult_le_0_compat (projT1 eps n) k2).
              ** apply (Qlt_le_weak 0 (projT1 eps n)). exact Hen.
              ** apply Qlt_le_weak. apply QltT_to_Qlt. exact Hk2.
      * apply qeq_le.
        setoid_rewrite (real_plus_proj real_one (real_mult eps (real_const k2)) n).
        setoid_rewrite (real_mult_proj eps (real_const k2) n).
        rewrite (real_const_proj k2 n).
        cbn [projT1 real_one projT1 real_zero].
        ring.
Defined.

(* ============================================================ *)
(* 件 4 b5dM_b5n_eps_proj_lt（Defined 透明）                    *)
(* 拷贝源：根 b5n_eps_proj_lt（ConstructiveWorld.v L78874；体    *)
(*   L78877–78888）。语句逐字（NatLe 逐字勿改）；体近逐字（仅    *)
(*   destruct 输入 Heps；e := 输入 eps1、N := 输入 N 透传）；     *)
(*   收尾 Defined。                                             *)
(* 值路径：e := projT1 输入见证——输入为件 1 拷贝（Defined）时    *)
(*   (real_const (1#4)) → e = (1#8)（检验 ④ 实证）。            *)
(* ============================================================ *)
Lemma b5dM_b5n_eps_proj_lt : forall (eps : Real), real_lt real_zero eps ->
  sigT (fun e : Q => And (QltT 0 e) (sigT (fun N : nat =>
    forall n : nat, NatLe N n -> Qlt e (projT1 eps n)))).
Proof.
  intros eps Heps.
  destruct Heps as [e [He [N HN]]].
  exists e. split.
  { exact He. }
  { exists N. intros n Hn.
    assert (Hsub : Qlt e (Qminus (projT1 eps n) (projT1 real_zero n))).
    { apply QltT_to_Qlt. exact (HN n Hn). }
    apply (Qlt_le_trans e (Qminus (projT1 eps n) (projT1 real_zero n)) (projT1 eps n)).
    { exact Hsub. }
    { apply qeq_le. cbn [projT1 real_zero]. ring. } }
Defined.

(* ============================================================ *)
(* 件 5 b5dM_b5c_d_proj_le_one（Defined 透明）                  *)
(* 拷贝源：根 b5c_d_proj_le_one（ConstructiveWorld.v L74897；    *)
(*   体 L74900–74929 禁抄——根 L74903 destruct real_inv_proj     *)
(*   （根 Qed）⟹ N 不透明）。直构 exists 0%nat（界对 ∀n 全真）： *)
(*   unfold b5a_atan_d（定义性 == real_inv_pos (1+x·x)           *)
(*     (b5a_one_plus_sq_pos x)）；destruct (b5a_one_plus_sq_pos   *)
(*   x)（Qed 见证 case 分析合法——不进值路径：exists 0%nat 先行， *)
(*   destruct 落在第二分量证明内）+ destruct x（case 分析使坐标   *)
(*   可归约）+ cbn 归约出 if Nat.leb N0 n 分两支（m := n / N0）； *)
(*   两支同证 Qle (Qabs (Qinv (1 + u m·u m))) 1：u m ≥ 1 经       *)
(*   b5c_one_sq_proj_ge_one（根 L74912 用法，∀m 全真）⟹           *)
(*   Qinv (u m) ∈ (0,1]：Qabs_pos（正性经 Qlt_le_trans 0 1）     *)
(*   + b5c_qinv_le_one + qeq_imp_qle——模板 = 根 L74919–28 链。   *)
(* ============================================================ *)
Lemma b5dM_b5c_d_proj_le_one : forall (x : Real),
  sigT (fun N : nat => forall n : nat, (N <= n)%nat ->
    Qle (Qabs (projT1 (b5a_atan_d x) n)) 1).
Proof.
  intro x.
  unfold b5a_atan_d.
  exists 0%nat.
  intros n Hn.
  destruct (b5a_one_plus_sq_pos x) as [e0 [He0 [N0 HN0]]].
  destruct x as [u Hu].
  assert (Hbd : forall m : nat,
           Qle (Qabs (Qinv (Qplus 1%Q (Qmult (u m) (u m))))) 1).
  { intro m.
    assert (Hge1 : Qle 1 (Qplus 1%Q (Qmult (u m) (u m)))).
    { apply (b5c_one_sq_proj_ge_one (existT (fun s : Qseq => cauchy s) u Hu) m). }
    assert (Hpos : Qlt 0 (Qplus 1%Q (Qmult (u m) (u m)))).
    { apply (Qlt_le_trans 0 1 (Qplus 1%Q (Qmult (u m) (u m)))).
      - unfold Qlt. simpl. lia.
      - exact Hge1. }
    apply (Qle_trans (Qabs (Qinv (Qplus 1%Q (Qmult (u m) (u m)))))
                     (Qinv (Qplus 1%Q (Qmult (u m) (u m))))
                     1).
    - apply qeq_imp_qle.
      apply (Qabs_pos (Qinv (Qplus 1%Q (Qmult (u m) (u m))))).
      apply (Qlt_le_weak 0 (Qinv (Qplus 1%Q (Qmult (u m) (u m))))).
      apply Qinv_lt_0_compat. exact Hpos.
    - apply (b5c_qinv_le_one (Qplus 1%Q (Qmult (u m) (u m)))).
      + exact Hpos.
      + exact Hge1. }
  cbn [projT1 real_inv_pos real_plus real_mult real_one].
  destruct (Nat.leb N0 n) eqn:E.
  - exact (Hbd n).
  - exact (Hbd N0).
Defined.

(* ============================================================ *)
(* 块 item19（前缀 b5dI_——主件 b5dI_E_diff_closed_r_exp）——来源：演变/.ablation/sc2_parallel/sc2_b5a_ode/sc2_b5a_item19.v。 *)
(* ============================================================ *)

Lemma b5dI_sA_proj_le : forall (x : Real)
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
  (n : nat) (M : Q),
  Qle (Qabs (sin_partial n (arctan_partial n (projT1 x n)))) M ->
  Qle (Qabs (projT1 (cauchy_real_sin (cauchy_real_arctan x Hx)) n)) M.
Proof.
  intros x Hx n M Hle.
  apply (Qle_trans (Qabs (projT1 (cauchy_real_sin (cauchy_real_arctan x Hx)) n))
                   (Qabs (sin_partial n (arctan_partial n (projT1 x n))))
                   M).
  - apply qeq_le.
    apply (Qabs_wd (projT1 (cauchy_real_sin (cauchy_real_arctan x Hx)) n)
                   (sin_partial n (arctan_partial n (projT1 x n)))).
    rewrite (real_sin_proj (cauchy_real_arctan x Hx) n).
    apply (sc_sin_partial_wd n (projT1 (cauchy_real_arctan x Hx) n)
                             (arctan_partial n (projT1 x n))).
    rewrite (arctan_real_proj x Hx n).
    reflexivity.
  - exact Hle.
Qed.

(* v3 helper：b5n_h_pts（根 L78570，语句内嵌根 b5i_one_plus_eps2_pos 见证）
   需要根叶形假设 |h| < (1#4)·real_inv_pos (1+eps·k2) (b5i_one_plus_eps2_pos …)；
   值路径 δ 叶已换 b5dM_ 透明件 ⟹ 两叶 real_eq（real_inv_pos_ext 与见证无关，
   仅需基底 real_eq 自反）——桥接 lemma（Defined 透明，纯证明侧）。 *)
Lemma b5dI_inv_leaf_witness_eq : forall (eps : Real) (k2 : Q)
  (Heps : real_lt real_zero eps) (Hk2 : QltT 0 k2),
  real_eq
    (real_mult (real_const (1 # 4))
       (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
                     (b5dM_b5i_one_plus_eps2_pos eps k2 Heps Hk2)))
    (real_mult (real_const (1 # 4))
       (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
                     (b5i_one_plus_eps2_pos eps k2 Heps Hk2))).
Proof.
  intros eps k2 Heps Hk2.
  apply (RealSetoid.real_eq_mult_compat
           (real_const (1 # 4))
           (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
                         (b5dM_b5i_one_plus_eps2_pos eps k2 Heps Hk2))
           (real_const (1 # 4))
           (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
                         (b5i_one_plus_eps2_pos eps k2 Heps Hk2))).
  - apply real_eq_refl.
  - apply (real_inv_pos_ext
             (real_plus real_one (real_mult eps (real_const k2)))
             (real_plus real_one (real_mult eps (real_const k2)))
             (b5dM_b5i_one_plus_eps2_pos eps k2 Heps Hk2)
             (b5i_one_plus_eps2_pos eps k2 Heps Hk2)).
    apply real_eq_refl.
Defined.

(* v3 helper（§4 预案 (a)）：real_mult_positive 根 Qed（L39518→Qed L39529）——
   E-diff 三 assert 站（HepsS/HepsC/Hepskδ）传入 C1t/C2t 叶调用，其见证在值路径
   被 b5dM_b5i_one_plus_eps2_pos / real_inv_pos 逐层 destruct ⟹ 根 opaque 使 match
   stuck。透明重证件：语句逐字 = 根 L39518；体同构根 real_mult_pos_compat
   （L34988–35040，同语句）直构显式见证（destruct 输入 Ha/Hb 取 e := e1·e2、
   N := Nat.max N1 N2；去根体 real_norm_bounded 死依赖；Q 层 Qmult_lt_compat_nonneg
   桥），Defined 收尾。 *)
Lemma b5dI_real_mult_positive_exp : forall a b : Real,
  real_lt real_zero a -> real_lt real_zero b -> real_lt real_zero (real_mult a b).
Proof.
  intros a b Ha Hb.
  destruct Ha as [e1 [He1 [N1 HN1]]].
  destruct Hb as [e2 [He2 [N2 HN2]]].
  assert (Hpos : Qlt 0 (e1 * e2)).
  { apply Qmult_lt_0_compat; [exact (QltT_to_Qlt _ _ He1) | exact (QltT_to_Qlt _ _ He2)]. }
  unfold real_lt.
  exists (e1 * e2).
  split.
  - apply Qlt_to_QltT. exact Hpos.
  - exists (Nat.max N1 N2).
    intros n Hn.
    apply Qlt_to_QltT.
    assert (Hm : Qeq (projT1 (real_mult a b) n) (Qmult (projT1 a n) (projT1 b n)))
      by (apply real_mult_proj).
    setoid_rewrite Hm.
    assert (Hz0 : Qeq (projT1 real_zero n) 0) by (cbn [projT1]; reflexivity).
    assert (Hz0' : Qeq (Qmult (projT1 a n) (projT1 b n) - projT1 real_zero n)
                       (Qmult (projT1 a n) (projT1 b n))).
    { setoid_rewrite Hz0. unfold Qminus. ring. }
    setoid_rewrite Hz0'.
    assert (Ha1 : QltT e1 (projT1 a n)).
    { apply Qlt_to_QltT.
      apply (Qlt_le_trans e1 (projT1 a n - projT1 real_zero n) (projT1 a n)).
      { apply QltT_to_Qlt. apply (HN1 n). apply NatLe_lift.
        apply (Nat.le_trans _ (Nat.max N1 N2) _); [apply Nat.le_max_l | exact (NatLe_drop _ _ Hn)]. }
      { apply qeq_le. setoid_rewrite Hz0. unfold Qminus. ring. } }
    assert (Hb1 : QltT e2 (projT1 b n)).
    { apply Qlt_to_QltT.
      apply (Qlt_le_trans e2 (projT1 b n - projT1 real_zero n) (projT1 b n)).
      { apply QltT_to_Qlt. apply (HN2 n). apply NatLe_lift.
        apply (Nat.le_trans _ (Nat.max N1 N2) _); [apply Nat.le_max_r | exact (NatLe_drop _ _ Hn)]. }
      { apply qeq_le. setoid_rewrite Hz0. unfold Qminus. ring. } }
    apply (Qmult_lt_compat_nonneg e1 (projT1 a n) e2 (projT1 b n)).
    + split.
      * apply (Qlt_le_weak 0 e1). exact (QltT_to_Qlt _ _ He1).
      * apply QltT_to_Qlt. exact Ha1.
    + split.
      * apply (Qlt_le_weak 0 e2). exact (QltT_to_Qlt _ _ He2).
      * apply QltT_to_Qlt. exact Hb1.
Defined.

Lemma b5dI_sin_atan_diff_closed_r_exp :
  forall (r : Q) (Hr0 : Qle 0 r) (Hr1 : Qlt r 1),
  forall (x : Real) (Hxr : forall n : nat, QleT' (Qabs (projT1 x n)) r),
  forall (Ms Mc C4 : Q),
  Qlt 0 Ms -> Qlt 0 Mc -> Qle 0 C4 -> QleT' 1 C4 ->
  (forall j : nat, QleT' (exp_series j 4) C4) ->
  (forall n : nat, Qle (Qabs (sin_partial n (arctan_partial n (projT1 x n)))) Ms) ->
  (forall n : nat, Qle (Qabs (cos_partial n (arctan_partial n (projT1 x n)))) Mc) ->
  forall (eps : Real), real_lt real_zero eps ->
  sigT (fun delta : Real => And (real_lt real_zero delta)
    (forall (h : Real), real_lt (real_abs h) delta ->
      forall (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1),
      forall (eps' : Real), real_lt real_zero eps' ->
      real_le (real_abs (b5a_comp_err_sin x (b3rr_dom_r1 x r Hxr Hr1) h Hxh))
              (real_plus (real_mult eps (real_abs h)) eps'))).
Proof.
  intros r Hr0 Hr1 x Hxr Ms Mc C4 HMsQ HMcQ HC40 HC4ge1 HC4 HMs_all HMc_all eps Heps.
  set (Hx := b3rr_dom_r1 x r Hxr Hr1).
  assert (HMs0 : Qle 0 Ms). { apply Qlt_le_weak. exact HMsQ. }
  assert (HMc0 : Qle 0 Mc). { apply Qlt_le_weak. exact HMcQ. }
  set (S := Qplus Ms Mc).
  assert (HSlt : Qlt 0 S). { unfold S. nra. }
  set (K1e := Qplus (Qmult Ms (Qplus (Qmult 4 C4) 2))
                    (Qmult Mc (Qplus (Qmult 4 C4) 4))).
  assert (HK1_0 : Qle 0 K1e). { unfold K1e. nra. }
  set (kδ := Qinv (Qmult 512 (Qplus S 1))).
  set (k2 := Qinv (Qmult (Qmult 512 (Qplus S 1))
                         (Qplus (Qplus (Qmult 3 S) Mc) 1))).
  set (k2p := Qinv (Qmult (Qmult 1024 (Qplus K1e 1))
                          (Qplus (Qplus (Qmult 3 S) Mc) 1))).
  assert (HkδT : QltT 0 kδ).
  { unfold kδ. apply Qlt_to_QltT. apply Qinv_lt_0_compat. nra. }
  assert (Hk2T : QltT 0 k2).
  { unfold k2. apply Qlt_to_QltT. apply Qinv_lt_0_compat. nra. }
  assert (Hk2pT : QltT 0 k2p).
  { unfold k2p. apply Qlt_to_QltT. apply Qinv_lt_0_compat. nra. }
  assert (Hk2Q : Qle 0 k2). { apply Qlt_le_weak. apply QltT_to_Qlt. exact Hk2T. }
  assert (Hk2pQ : Qlt 0 k2p). { apply QltT_to_Qlt. exact Hk2pT. }
  (* 全局预算：coef（quad）、coefC（crude）、8k2p·K1（crude 强制） *)
  assert (HcoefQ : Qle (Qplus (Qmult (Qmult 2 (Qplus Ms Mc)) kδ)
                               (Qmult (Qplus (Qmult 3 (Qplus Ms Mc)) Mc) k2)) 1).
  { apply (Qle_trans (Qplus (Qmult (Qmult 2 (Qplus Ms Mc)) kδ)
                             (Qmult (Qplus (Qmult 3 (Qplus Ms Mc)) Mc) k2))
                     (Qplus (1 # 2) (1 # 2))
                     1).
    { apply Qplus_le_compat.
      { apply (b5n_2S_kδ_le S HSlt). }
      { apply (b5n_3S_Mc_k2_le S Mc HSlt HMc0). } }
    { nra. } }
  assert (HcoefC : Qle (Qmult Mc k2) 1).
  { apply (Qle_trans (Qmult Mc k2) (1 # 2) 1).
    { apply (b5n_Mc_k2_le S Mc HSlt HMc0). }
    { unfold Qle. simpl. lia. } }
  assert (Hk2pK1 : Qle (Qmult (Qmult 8 k2p)
                              (Qplus (Qmult Ms (Qplus (Qmult 4 C4) 2))
                                     (Qmult Mc (Qplus (Qmult 4 C4) 4)))) 1).
  { apply (b5n_8k2p_K1_le S Mc K1e HSlt HMc0 HK1_0). }
  (* δ 组装：0 < 各分量 *)
  assert (H12T : QltT 0 (1 # 2)) by (apply Qlt_to_QltT; unfold Qlt; simpl; lia).
  assert (H14T : QltT 0 (1 # 4)) by (apply Qlt_to_QltT; unfold Qlt; simpl; lia).
  destruct (b5dD_vdh_pts_r_exp r Hr0 Hr1 x Hxr eps Heps k2 k2p Hk2T Hk2pT) as [δa [Hδa0 Hδa]].
  assert (Hc12r : real_lt real_zero (real_const (1 # 2))).
  { apply b5dM_real_const_pos. exact H12T. }
  assert (Hepskδ : real_lt real_zero (real_mult eps (real_const kδ))).
  { apply real_mult_positive.
    { exact Heps. }
    { apply b5dM_real_const_pos. exact HkδT. } }
  assert (Hqtr : real_lt real_zero
            (real_mult (real_const (1 # 4))
                       (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
                                     (b5dM_b5i_one_plus_eps2_pos eps k2 Heps Hk2T)))).
  { apply real_mult_positive.
    { apply b5dM_real_const_pos. exact H14T. }
    { apply real_inv_pos_pos. } }
  set (delta := real_min
        (real_min (real_min δa (real_const (1 # 2)))
                  (real_mult eps (real_const kδ)))
        (real_mult (real_const (1 # 4))
                   (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
                                 (b5dM_b5i_one_plus_eps2_pos eps k2 Heps Hk2T)))).
  assert (Hdpos : real_lt real_zero delta).
  { unfold delta.
    apply real_min_pos.
    { apply real_min_pos.
      { apply real_min_pos.
        { exact Hδa0. }
        { exact Hc12r. } }
      { exact Hepskδ. } }
    { exact Hqtr. } }
  exists delta.
  split.
  { exact Hdpos. }
  { intros h Hh Hxh eps' Heps'.
  destruct (b5dM_b5c_d_proj_le_one x) as [Nd Hd].
  destruct (b5dM_b5n_eps_proj_lt eps Heps) as [e0 [He0T [Ne0 He0lt]]].
    destruct (b5dM_b5n_eps_proj_lt eps' Heps') as [e1 [He1T [Ne1 He1lt]]].
    set (eta := Qmult (1 # 8) e1).
    assert (HetaT : QltT 0 eta).
    { unfold eta. apply Qlt_to_QltT.
      apply (Qmult_lt_0_compat (1 # 8) e1).
      { unfold Qlt. simpl. lia. }
      { apply QltT_to_Qlt. exact He1T. } }
    (* h 相对 δ 的四层 min 提取 *)
    assert (HhA : real_lt (real_abs h)
             (real_min (real_min δa (real_const (1 # 2))) (real_mult eps (real_const kδ)))).
    { apply (real_min_lt_l h
               (real_min (real_min δa (real_const (1 # 2))) (real_mult eps (real_const kδ)))
               (real_mult (real_const (1 # 4))
                          (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
                                        (b5dM_b5i_one_plus_eps2_pos eps k2 Heps Hk2T)))).
      exact Hh. }
    assert (HhE : real_lt (real_abs h)
             (real_mult (real_const (1 # 4))
                        (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
                                      (b5dM_b5i_one_plus_eps2_pos eps k2 Heps Hk2T)))).
    { apply (real_min_lt_r h
               (real_min (real_min δa (real_const (1 # 2))) (real_mult eps (real_const kδ)))
               (real_mult (real_const (1 # 4))
                          (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
                                        (b5dM_b5i_one_plus_eps2_pos eps k2 Heps Hk2T)))).
      exact Hh. }
    assert (HhAA : real_lt (real_abs h) (real_min δa (real_const (1 # 2)))).
    { apply (real_min_lt_l h (real_min δa (real_const (1 # 2)))
                           (real_mult eps (real_const kδ))).
      exact HhA. }
    assert (Hhlr : real_lt (real_abs h) (real_mult eps (real_const kδ))).
    { apply (real_min_lt_r h (real_min δa (real_const (1 # 2)))
                           (real_mult eps (real_const kδ))).
      exact HhA. }
    assert (Hhda : real_lt (real_abs h) δa).
    { apply (real_min_lt_l h δa (real_const (1 # 2))). exact HhAA. }
    assert (Hh12 : real_lt (real_abs h) (real_const (1 # 2))).
    { apply (real_min_lt_r h δa (real_const (1 # 2))). exact HhAA. }
    (* X：b5n_h_pts（根语句内嵌根见证 ⟹ 根叶形 Hhq_r 经桥接导出） *)
    assert (Hhq_r : real_lt (real_abs h)
             (real_mult (real_const (1 # 4))
                        (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
                                      (b5i_one_plus_eps2_pos eps k2 Heps Hk2T)))).
    { apply (real_lt_le_trans (real_abs h)
             (real_mult (real_const (1 # 4))
                        (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
                                      (b5dM_b5i_one_plus_eps2_pos eps k2 Heps Hk2T)))
             (real_mult (real_const (1 # 4))
                        (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
                                      (b5i_one_plus_eps2_pos eps k2 Heps Hk2T)))).
      { exact HhE. }
      { apply RealSetoid.real_eq_le.
        exact (b5dI_inv_leaf_witness_eq eps k2 Heps Hk2T). } }
    destruct (b5n_h_pts h eps kδ k2 Heps HkδT Hk2T Hhlr Hh12 Hhq_r) as [Nh HNh].
    (* Y：arctan' 于 eps2 := eps·k2 / eps2' := eps'·k2p *)
    destruct (Hδa h Hhda Hxh eps' Heps') as [Nw HNw].
    (* 列误差列 *)
    destruct (b5i_rs_addcol x Hx h Hxh eta HetaT) as [Nc HNc].
    (* 逐点预算（对 eps' 见证） *)
    assert (Hen'g : forall n : nat, NatLe Ne1 n -> Qle 0 (projT1 eps' n)).
    { intros n Hn.
      apply (Qle_trans 0 e1 (projT1 eps' n)).
      { apply Qlt_le_weak. apply QltT_to_Qlt. exact He1T. }
      { apply Qlt_le_weak. exact (He1lt n Hn). } }
    assert (HcolQ8_all : forall n : nat, NatLe Ne1 n ->
            Qle eta (Qmult (1 # 8) (projT1 eps' n))).
    { intros n Hn.
      unfold eta.
      apply (sc_qmult_le_l e1 (projT1 eps' n) (1 # 8)).
      { apply Qlt_le_weak. exact (He1lt n Hn). }
      { unfold Qle. simpl. lia. } }
    assert (HaddQ_all : forall n : nat, NatLe Ne1 n ->
            Qle (Qmult (Qplus (Qmult 3 (Qplus Ms Mc)) Mc)
                       (Qmult (Qmult 2 k2p) (projT1 eps' n)))
                (Qmult (1 # 32) (projT1 eps' n))).
    { intros n Hn.
      apply (Qle_trans
               (Qmult (Qplus (Qmult 3 (Qplus Ms Mc)) Mc)
                      (Qmult (Qmult 2 k2p) (projT1 eps' n)))
               (Qmult (Qmult (Qplus (Qmult 3 S) Mc) (Qmult 2 k2p))
                      (projT1 eps' n))
               (Qmult (1 # 32) (projT1 eps' n))).
      { apply qeq_imp_qle. unfold S. ring. }
      { apply (Qmult_le_compat_r
                 (Qmult (Qplus (Qmult 3 S) Mc) (Qmult 2 k2p))
                 (1 # 32) (projT1 eps' n)).
        { apply (b5n_3S_Mc_2k2p_le S Mc K1e HSlt HMc0 HK1_0). }
        { exact (Hen'g n Hn). } } }
    assert (HaddC_all : forall n : nat, NatLe Ne1 n ->
            Qle (Qmult Mc (Qmult (Qmult 2 k2p) (projT1 eps' n)))
                (Qmult (1 # 32) (projT1 eps' n))).
    { intros n Hn.
      apply (Qle_trans
               (Qmult Mc (Qmult (Qmult 2 k2p) (projT1 eps' n)))
               (Qmult (Qmult Mc (Qmult 2 k2p)) (projT1 eps' n))
               (Qmult (1 # 32) (projT1 eps' n))).
      { apply qeq_imp_qle. ring. }
      { apply (Qmult_le_compat_r (Qmult Mc (Qmult 2 k2p)) (1 # 32)
                                 (projT1 eps' n)).
        { apply (b5n_Mc_2k2p_le S Mc K1e HSlt HMc0 HK1_0). }
        { exact (Hen'g n Hn). } } }
    (* 主装配：real_le → real_lt（左支），见证 eta *)
    set (Nmax := Nat.max (Nat.max Ne0 Ne1) (Nat.max (Nat.max Nh Nw) (Nat.max Nc Nd))).
    left.
    exists eta.
    split.
    { exact HetaT. }
    { exists Nmax.
      intros n Hn.
      apply NatLe_drop in Hn.
      set (en := projT1 eps n).
      set (en' := projT1 eps' n).
      set (hn := Qabs (projT1 h n)).
      set (Dn := Qabs (projT1 (b5a_comp_err_sin x Hx h Hxh) n)).
      assert (HnNe0 : NatLe Ne0 n) by (apply NatLe_lift; lia).
      assert (HnNe1 : NatLe Ne1 n) by (apply NatLe_lift; lia).
      assert (HnNh : NatLe Nh n) by (apply NatLe_lift; lia).
      assert (HnNw : NatLe Nw n) by (apply NatLe_lift; lia).
      assert (HnNc : NatLe Nc n) by (apply NatLe_lift; lia).
      assert (HnNd : (Nd <= n)%nat) by lia.
      assert (Hen0 : Qle 0 en).
      { unfold en. apply (Qle_trans 0 e0 (projT1 eps n)).
        { apply Qlt_le_weak. apply QltT_to_Qlt. exact He0T. }
        { apply Qlt_le_weak. exact (He0lt n HnNe0). } }
      assert (Hen'0 : Qle 0 en').
      { unfold en'. exact (Hen'g n HnNe1). }
      destruct (HNh n HnNh) as [Hhδn [Hh12n Hhqn]].
      (* Z：per-n 主界 *)
      assert (Hmain : Qle (Qabs (projT1 (b5a_comp_err_sin x Hx h Hxh) n))
                          (Qplus (Qmult en (Qabs (projT1 h n))) (Qmult (3 # 4) en'))).
      { apply (b5n_pern_main x Hx h Hxh n Ms Mc C4 eta kδ k2 k2p en en').
        { exact (HMs_all n). }
        { exact (HMc_all n). }
        { exact HC4. }
        { exact HC40. }
        { exact (HNc n HnNc). }
        { exact (QleT'_to_Qle _ _ Hhδn). }
        { exact (QleT'_to_Qle _ _ Hh12n). }
        { exact (QleT'_to_Qle _ _ Hhqn). }
        { exact (HNw n HnNw). }
        { unfold b5i_dn. exact (Hd n HnNd). }
        { exact Hen0. }
        { exact Hen'0. }
        { exact Hk2Q. }
        { exact Hk2pQ. }
        { exact HcoefQ. }
        { exact HcoefC. }
        { exact (HcolQ8_all n HnNe1). }
        { exact (HaddQ_all n HnNe1). }
        { exact (HaddC_all n HnNe1). }
        { exact Hk2pK1. } }
      (* margin：eta < (1/4)en'；Hfin：eta < (en·hn + en') − Dn *)
      assert (Hq4e : Qlt eta (Qmult (1 # 4) en')).
      { unfold eta, en'. apply (b5n_quarter_gt e1 (projT1 eps' n)).
        { apply QltT_to_Qlt. exact He1T. }
        { exact (He1lt n HnNe1). } }
      assert (Hfin : Qlt eta (Qminus (Qplus (Qmult en hn) en') Dn)).
      { apply (b5n_close Dn hn en en' eta).
        { unfold Dn. exact Hmain. }
        { unfold en'. exact Hq4e. } }
      assert (Hrepl : Qeq (Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                                  (projT1 (real_abs (b5a_comp_err_sin x Hx h Hxh)) n))
                          (Qminus (Qplus (Qmult en hn) en') Dn)).
      { unfold en, en', hn, Dn.
        setoid_rewrite (real_plus_proj (real_mult eps (real_abs h)) eps' n).
        setoid_rewrite (real_mult_proj eps (real_abs h) n).
        setoid_rewrite (real_abs_proj h n).
        setoid_rewrite (real_abs_proj (b5a_comp_err_sin x Hx h Hxh) n).
        ring. }
      apply Qlt_to_QltT.
      apply (Qlt_le_trans eta
             (Qminus (Qplus (Qmult en hn) en') Dn)
             (Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                     (projT1 (real_abs (b5a_comp_err_sin x Hx h Hxh)) n))).
      { exact Hfin. }
      { apply qeq_imp_qle. apply Qeq_sym. exact Hrepl. } } }
Defined.

Lemma b5dI_cos_atan_diff_closed_r_exp :
  forall (r : Q) (Hr0 : Qle 0 r) (Hr1 : Qlt r 1),
  forall (x : Real) (Hxr : forall n : nat, QleT' (Qabs (projT1 x n)) r),
  forall (Ms Mc C4 : Q),
  Qlt 0 Ms -> Qlt 0 Mc -> Qle 0 C4 -> QleT' 1 C4 ->
  (forall j : nat, QleT' (exp_series j 4) C4) ->
  (forall n : nat, Qle (Qabs (sin_partial n (arctan_partial n (projT1 x n)))) Ms) ->
  (forall n : nat, Qle (Qabs (cos_partial n (arctan_partial n (projT1 x n)))) Mc) ->
  forall (eps : Real), real_lt real_zero eps ->
  sigT (fun delta : Real => And (real_lt real_zero delta)
    (forall (h : Real), real_lt (real_abs h) delta ->
      forall (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1),
      forall (eps' : Real), real_lt real_zero eps' ->
      real_le (real_abs (b5a_comp_err_cos x (b3rr_dom_r1 x r Hxr Hr1) h Hxh))
              (real_plus (real_mult eps (real_abs h)) eps'))).
Proof.
  intros r Hr0 Hr1 x Hxr Ms Mc C4 HMsQ HMcQ HC40 HC4ge1 HC4 HMs_all HMc_all eps Heps.
  set (Hx := b3rr_dom_r1 x r Hxr Hr1).
  assert (HMs0 : Qle 0 Ms). { apply Qlt_le_weak. exact HMsQ. }
  assert (HMc0 : Qle 0 Mc). { apply Qlt_le_weak. exact HMcQ. }
  set (S := Qplus Ms Mc).
  assert (HSlt : Qlt 0 S). { unfold S. nra. }
  set (K1e := Qplus (Qmult Mc (Qplus (Qmult 4 C4) 2))
                    (Qmult Ms (Qplus (Qmult 4 C4) 4))).
  assert (HK1_0 : Qle 0 K1e). { unfold K1e. nra. }
  set (kδ := Qinv (Qmult 512 (Qplus S 1))).
  set (k2 := Qinv (Qmult (Qmult 512 (Qplus S 1))
                         (Qplus (Qplus (Qmult 3 S) Ms) 1))).
  set (k2p := Qinv (Qmult (Qmult 1024 (Qplus K1e 1))
                          (Qplus (Qplus (Qmult 3 S) Ms) 1))).
  assert (HkδT : QltT 0 kδ).
  { unfold kδ. apply Qlt_to_QltT. apply Qinv_lt_0_compat. nra. }
  assert (Hk2T : QltT 0 k2).
  { unfold k2. apply Qlt_to_QltT. apply Qinv_lt_0_compat. nra. }
  assert (Hk2pT : QltT 0 k2p).
  { unfold k2p. apply Qlt_to_QltT. apply Qinv_lt_0_compat. nra. }
  assert (Hk2Q : Qle 0 k2). { apply Qlt_le_weak. apply QltT_to_Qlt. exact Hk2T. }
  assert (Hk2pQ : Qlt 0 k2p). { apply QltT_to_Qlt. exact Hk2pT. }
  (* 全局预算：coef（quad）、coefC（crude）、8k2p·K1e（crude 强制） *)
  assert (HcoefQ : Qle (Qplus (Qmult (Qmult 2 (Qplus Ms Mc)) kδ)
                               (Qmult (Qplus (Qmult 3 (Qplus Ms Mc)) Ms) k2)) 1).
  { apply (Qle_trans (Qplus (Qmult (Qmult 2 (Qplus Ms Mc)) kδ)
                            (Qmult (Qplus (Qmult 3 (Qplus Ms Mc)) Ms) k2))
                     (Qplus (1 # 2) (1 # 2))
                     1).
    { apply Qplus_le_compat.
      { apply (b5n_2S_kδ_le S HSlt). }
      { apply (b5n_3S_Mc_k2_le S Ms HSlt HMs0). } }
    { nra. } }
  assert (HcoefC : Qle (Qmult Ms k2) 1).
  { apply (Qle_trans (Qmult Ms k2) (1 # 2) 1).
    { apply (b5n_Mc_k2_le S Ms HSlt HMs0). }
    { unfold Qle. simpl. lia. } }
  assert (Hk2pK1 : Qle (Qmult (Qmult 8 k2p)
                              (Qplus (Qmult Mc (Qplus (Qmult 4 C4) 2))
                                     (Qmult Ms (Qplus (Qmult 4 C4) 4)))) 1).
  { apply (b5n_8k2p_K1_le S Ms K1e HSlt HMs0 HK1_0). }
  (* δ 组装：0 < 各分量 *)
  assert (H12T : QltT 0 (1 # 2)) by (apply Qlt_to_QltT; unfold Qlt; simpl; lia).
  assert (H14T : QltT 0 (1 # 4)) by (apply Qlt_to_QltT; unfold Qlt; simpl; lia).
  destruct (b5dD_vdh_pts_r_exp r Hr0 Hr1 x Hxr eps Heps k2 k2p Hk2T Hk2pT) as [δa [Hδa0 Hδa]].
  assert (Hc12r : real_lt real_zero (real_const (1 # 2))).
  { apply b5dM_real_const_pos. exact H12T. }
  assert (Hepskδ : real_lt real_zero (real_mult eps (real_const kδ))).
  { apply real_mult_positive.
    { exact Heps. }
    { apply b5dM_real_const_pos. exact HkδT. } }
  assert (Hqtr : real_lt real_zero
            (real_mult (real_const (1 # 4))
                       (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
                                     (b5dM_b5i_one_plus_eps2_pos eps k2 Heps Hk2T)))).
  { apply real_mult_positive.
    { apply b5dM_real_const_pos. exact H14T. }
    { apply real_inv_pos_pos. } }
  set (delta := real_min
        (real_min (real_min δa (real_const (1 # 2)))
                  (real_mult eps (real_const kδ)))
        (real_mult (real_const (1 # 4))
                   (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
                                 (b5dM_b5i_one_plus_eps2_pos eps k2 Heps Hk2T)))).
  assert (Hdpos : real_lt real_zero delta).
  { unfold delta.
    apply real_min_pos.
    { apply real_min_pos.
      { apply real_min_pos.
        { exact Hδa0. }
        { exact Hc12r. } }
      { exact Hepskδ. } }
    { exact Hqtr. } }
  exists delta.
  split.
  { exact Hdpos. }
  { intros h Hh Hxh eps' Heps'.
  destruct (b5dM_b5c_d_proj_le_one x) as [Nd Hd].
  destruct (b5dM_b5n_eps_proj_lt eps Heps) as [e0 [He0T [Ne0 He0lt]]].
    destruct (b5dM_b5n_eps_proj_lt eps' Heps') as [e1 [He1T [Ne1 He1lt]]].
    set (eta := Qmult (1 # 8) e1).
    assert (HetaT : QltT 0 eta).
    { unfold eta. apply Qlt_to_QltT.
      apply (Qmult_lt_0_compat (1 # 8) e1).
      { unfold Qlt. simpl. lia. }
      { apply QltT_to_Qlt. exact He1T. } }
    (* h 相对 δ 的四层 min 提取 *)
    assert (HhA : real_lt (real_abs h)
             (real_min (real_min δa (real_const (1 # 2))) (real_mult eps (real_const kδ)))).
    { apply (real_min_lt_l h
               (real_min (real_min δa (real_const (1 # 2))) (real_mult eps (real_const kδ)))
               (real_mult (real_const (1 # 4))
                          (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
                                        (b5dM_b5i_one_plus_eps2_pos eps k2 Heps Hk2T)))).
      exact Hh. }
    assert (HhE : real_lt (real_abs h)
             (real_mult (real_const (1 # 4))
                        (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
                                      (b5dM_b5i_one_plus_eps2_pos eps k2 Heps Hk2T)))).
    { apply (real_min_lt_r h
               (real_min (real_min δa (real_const (1 # 2))) (real_mult eps (real_const kδ)))
               (real_mult (real_const (1 # 4))
                          (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
                                        (b5dM_b5i_one_plus_eps2_pos eps k2 Heps Hk2T)))).
      exact Hh. }
    assert (HhAA : real_lt (real_abs h) (real_min δa (real_const (1 # 2)))).
    { apply (real_min_lt_l h (real_min δa (real_const (1 # 2)))
                           (real_mult eps (real_const kδ))).
      exact HhA. }
    assert (Hhlr : real_lt (real_abs h) (real_mult eps (real_const kδ))).
    { apply (real_min_lt_r h (real_min δa (real_const (1 # 2)))
                           (real_mult eps (real_const kδ))).
      exact HhA. }
    assert (Hhda : real_lt (real_abs h) δa).
    { apply (real_min_lt_l h δa (real_const (1 # 2))). exact HhAA. }
    assert (Hh12 : real_lt (real_abs h) (real_const (1 # 2))).
    { apply (real_min_lt_r h δa (real_const (1 # 2))). exact HhAA. }
    (* X：b5n_h_pts（根语句内嵌根见证 ⟹ 根叶形 Hhq_r 经桥接导出） *)
    assert (Hhq_r : real_lt (real_abs h)
             (real_mult (real_const (1 # 4))
                        (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
                                      (b5i_one_plus_eps2_pos eps k2 Heps Hk2T)))).
    { apply (real_lt_le_trans (real_abs h)
             (real_mult (real_const (1 # 4))
                        (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
                                      (b5dM_b5i_one_plus_eps2_pos eps k2 Heps Hk2T)))
             (real_mult (real_const (1 # 4))
                        (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
                                      (b5i_one_plus_eps2_pos eps k2 Heps Hk2T)))).
      { exact HhE. }
      { apply RealSetoid.real_eq_le.
        exact (b5dI_inv_leaf_witness_eq eps k2 Heps Hk2T). } }
    destruct (b5n_h_pts h eps kδ k2 Heps HkδT Hk2T Hhlr Hh12 Hhq_r) as [Nh HNh].
    (* Y：arctan' 于 eps2 := eps·k2 / eps2' := eps'·k2p *)
    destruct (Hδa h Hhda Hxh eps' Heps') as [Nw HNw].
    (* 列误差列（cos 侧） *)
    destruct (b5d_rs_addcol_cos x Hx h Hxh eta HetaT) as [Nc HNc].
    (* 逐点预算（对 eps' 见证） *)
    assert (Hen'g : forall n : nat, NatLe Ne1 n -> Qle 0 (projT1 eps' n)).
    { intros n Hn.
      apply (Qle_trans 0 e1 (projT1 eps' n)).
      { apply Qlt_le_weak. apply QltT_to_Qlt. exact He1T. }
      { apply Qlt_le_weak. exact (He1lt n Hn). } }
    assert (HcolQ8_all : forall n : nat, NatLe Ne1 n ->
            Qle eta (Qmult (1 # 8) (projT1 eps' n))).
    { intros n Hn.
      unfold eta.
      apply (sc_qmult_le_l e1 (projT1 eps' n) (1 # 8)).
      { apply Qlt_le_weak. exact (He1lt n Hn). }
      { unfold Qle. simpl. lia. } }
    assert (HaddQ_all : forall n : nat, NatLe Ne1 n ->
            Qle (Qmult (Qplus (Qmult 3 (Qplus Ms Mc)) Ms)
                       (Qmult (Qmult 2 k2p) (projT1 eps' n)))
                (Qmult (1 # 32) (projT1 eps' n))).
    { intros n Hn.
      apply (Qle_trans
               (Qmult (Qplus (Qmult 3 (Qplus Ms Mc)) Ms)
                      (Qmult (Qmult 2 k2p) (projT1 eps' n)))
               (Qmult (Qmult (Qplus (Qmult 3 S) Ms) (Qmult 2 k2p))
                      (projT1 eps' n))
               (Qmult (1 # 32) (projT1 eps' n))).
      { apply qeq_imp_qle. unfold S. ring. }
      { apply (Qmult_le_compat_r
                 (Qmult (Qplus (Qmult 3 S) Ms) (Qmult 2 k2p))
                 (1 # 32) (projT1 eps' n)).
        { apply (b5n_3S_Mc_2k2p_le S Ms K1e HSlt HMs0 HK1_0). }
        { exact (Hen'g n Hn). } } }
    assert (HaddC_all : forall n : nat, NatLe Ne1 n ->
            Qle (Qmult Ms (Qmult (Qmult 2 k2p) (projT1 eps' n)))
                (Qmult (1 # 32) (projT1 eps' n))).
    { intros n Hn.
      apply (Qle_trans
               (Qmult Ms (Qmult (Qmult 2 k2p) (projT1 eps' n)))
               (Qmult (Qmult Ms (Qmult 2 k2p)) (projT1 eps' n))
               (Qmult (1 # 32) (projT1 eps' n))).
      { apply qeq_imp_qle. ring. }
      { apply (Qmult_le_compat_r (Qmult Ms (Qmult 2 k2p)) (1 # 32)
                                 (projT1 eps' n)).
        { apply (b5n_Mc_2k2p_le S Ms K1e HSlt HMs0 HK1_0). }
        { exact (Hen'g n Hn). } } }
    (* 主装配：real_le → real_lt（左支），见证 eta *)
    set (Nmax := Nat.max (Nat.max Ne0 Ne1) (Nat.max (Nat.max Nh Nw) (Nat.max Nc Nd))).
    left.
    exists eta.
    split.
    { exact HetaT. }
    { exists Nmax.
      intros n Hn.
      apply NatLe_drop in Hn.
      set (en := projT1 eps n).
      set (en' := projT1 eps' n).
      set (hn := Qabs (projT1 h n)).
      set (Dn := Qabs (projT1 (b5a_comp_err_cos x Hx h Hxh) n)).
      assert (HnNe0 : NatLe Ne0 n) by (apply NatLe_lift; lia).
      assert (HnNe1 : NatLe Ne1 n) by (apply NatLe_lift; lia).
      assert (HnNh : NatLe Nh n) by (apply NatLe_lift; lia).
      assert (HnNw : NatLe Nw n) by (apply NatLe_lift; lia).
      assert (HnNc : NatLe Nc n) by (apply NatLe_lift; lia).
      assert (HnNd : (Nd <= n)%nat) by lia.
      assert (Hen0 : Qle 0 en).
      { unfold en. apply (Qle_trans 0 e0 (projT1 eps n)).
        { apply Qlt_le_weak. apply QltT_to_Qlt. exact He0T. }
        { apply Qlt_le_weak. exact (He0lt n HnNe0). } }
      assert (Hen'0 : Qle 0 en').
      { unfold en'. exact (Hen'g n HnNe1). }
      destruct (HNh n HnNh) as [Hhδn [Hh12n Hhqn]].
      (* Z：per-n 主界（cos 版） *)
      assert (Hmain : Qle (Qabs (projT1 (b5a_comp_err_cos x Hx h Hxh) n))
                          (Qplus (Qmult en (Qabs (projT1 h n))) (Qmult (3 # 4) en'))).
      { apply (b5d_pern_main_cos x Hx h Hxh n Ms Mc C4 eta kδ k2 k2p en en').
        { exact (HMs_all n). }
        { exact (HMc_all n). }
        { exact HC4. }
        { exact HC40. }
        { exact (HNc n HnNc). }
        { exact (QleT'_to_Qle _ _ Hhδn). }
        { exact (QleT'_to_Qle _ _ Hh12n). }
        { exact (QleT'_to_Qle _ _ Hhqn). }
        { exact (HNw n HnNw). }
        { unfold b5i_dn. exact (Hd n HnNd). }
        { exact Hen0. }
        { exact Hen'0. }
        { exact Hk2Q. }
        { exact Hk2pQ. }
        { exact HcoefQ. }
        { exact HcoefC. }
        { exact (HcolQ8_all n HnNe1). }
        { exact (HaddQ_all n HnNe1). }
        { exact (HaddC_all n HnNe1). }
        { exact Hk2pK1. } }
      (* margin：eta < (1/4)en'；Hfin：eta < (en·hn + en') − Dn *)
      assert (Hq4e : Qlt eta (Qmult (1 # 4) en')).
      { unfold eta, en'. apply (b5n_quarter_gt e1 (projT1 eps' n)).
        { apply QltT_to_Qlt. exact He1T. }
        { exact (He1lt n HnNe1). } }
      assert (Hfin : Qlt eta (Qminus (Qplus (Qmult en hn) en') Dn)).
      { apply (b5n_close Dn hn en en' eta).
        { unfold Dn. exact Hmain. }
        { unfold en'. exact Hq4e. } }
      assert (Hrepl : Qeq (Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                                  (projT1 (real_abs (b5a_comp_err_cos x Hx h Hxh)) n))
                          (Qminus (Qplus (Qmult en hn) en') Dn)).
      { unfold en, en', hn, Dn.
        setoid_rewrite (real_plus_proj (real_mult eps (real_abs h)) eps' n).
        setoid_rewrite (real_mult_proj eps (real_abs h) n).
        setoid_rewrite (real_abs_proj h n).
        setoid_rewrite (real_abs_proj (b5a_comp_err_cos x Hx h Hxh) n).
        ring. }
      apply Qlt_to_QltT.
      apply (Qlt_le_trans eta
             (Qminus (Qplus (Qmult en hn) en') Dn)
             (Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                     (projT1 (real_abs (b5a_comp_err_cos x Hx h Hxh)) n))).
      { exact Hfin. }
      { apply qeq_imp_qle. apply Qeq_sym. exact Hrepl. } } }
Defined.

Lemma b5dI_E_diff_closed_r_exp :
  forall (r : Q) (Hr0 : Qle 0 r) (Hr1 : Qlt r 1),
  forall (x : Real) (Hxr : forall n : nat, QleT' (Qabs (projT1 x n)) r),
  forall (Msr Mc C4 : Q),
  Qlt 0 Msr -> Qlt 0 Mc -> Qle 0 C4 -> QleT' 1 C4 ->
  (forall j : nat, QleT' (exp_series j 4) C4) ->
  (forall n : nat, Qle (Qabs (sin_partial n (arctan_partial n (projT1 x n)))) Msr) ->
  (forall n : nat, Qle (Qabs (cos_partial n (arctan_partial n (projT1 x n)))) Mc) ->
  forall (eps : Real), real_lt real_zero eps ->
  sigT (fun delta : Real => And (real_lt real_zero delta)
    (forall (h : Real), real_lt (real_abs h) delta ->
      forall (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1),
      forall (eps' : Real), real_lt real_zero eps' ->
      real_le (real_abs (real_plus (b5a_E (real_plus x h) Hxh)
                 (real_opp (real_plus (b5a_E x (b3rr_dom_r1 x r Hxr Hr1))
                            (real_mult (real_mult x (b5a_E x (b3rr_dom_r1 x r Hxr Hr1)))
                                       (real_mult (b5a_atan_d x) h))))))
              (real_plus (real_mult eps (real_abs h)) eps'))).
Proof.
  intros r Hr0 Hr1 x Hxr Msr Mc C4 HMsr_pos HMcQ HC40 HC4ge1 HC4 HMsr_all HMc_all eps Heps.
  set (Hx := b3rr_dom_r1 x r Hxr Hr1).
  assert (HMsrQ : Qlt 0 Msr). { exact HMsr_pos. }
  assert (HMsr0 : Qle 0 Msr). { apply Qlt_le_weak. exact HMsrQ. }
  (* 常数与预算 *)
  set (S := Msr).
  assert (HSlt : Qlt 0 S). { unfold S. exact HMsrQ. }
  set (kδ := Qinv (Qmult 512 (Qplus S 1))).
  assert (HkδT : QltT 0 kδ).
  { unfold kδ. apply Qlt_to_QltT. apply Qinv_lt_0_compat. nra. }
  assert (Hkδ0 : Qle 0 kδ). { apply Qlt_le_weak. apply QltT_to_Qlt. exact HkδT. }
  assert (HMsrkδ : Qle (Qmult Msr kδ) (1 # 4)).
  { assert (H2 : Qle (Qmult (Qmult 2 S) kδ) (1 # 2)).
    { apply (b5n_2S_kδ_le S HSlt). }
    apply (Qle_trans (Qmult Msr kδ) (Qmult (1 # 2) (Qmult (Qmult 2 S) kδ)) (1 # 4)).
    { apply qeq_imp_qle. unfold S. ring. }
    { apply (Qle_trans (Qmult (1 # 2) (Qmult (Qmult 2 S) kδ))
                       (Qmult (1 # 2) (1 # 2))
                       (1 # 4)).
      { apply (sc_qmult_le_l (Qmult (Qmult 2 S) kδ) (1 # 2) (1 # 2)).
        { exact H2. }
        { unfold Qle. simpl. lia. } }
      { apply qeq_imp_qle. ring. } } }
  assert (Hcoef : Qle (Qplus (Qplus (1 # 4) (1 # 4)) (Qmult Msr kδ)) 1).
  { nra. }
  assert (Hadd : Qle (Qplus (Qplus (Qplus (1 # 8) (1 # 8)) (1 # 16)) (1 # 16)) (3 # 4)).
  { nra. }
  assert (HkT4 : QltT 0 (1 # 4)) by (apply Qlt_to_QltT; unfold Qlt; simpl; lia).
  assert (HkT8 : QltT 0 (1 # 8)) by (apply Qlt_to_QltT; unfold Qlt; simpl; lia).
  assert (HkT16 : QltT 0 (1 # 16)) by (apply Qlt_to_QltT; unfold Qlt; simpl; lia).
  (* sin / cos 闭式实例化（系数份额 eps/4） *)
  assert (HepsS : real_lt real_zero (real_mult eps (real_const (1 # 4)))).
  { apply b5dI_real_mult_positive_exp. { exact Heps. } { apply b5dM_real_const_pos. exact HkT4. } }
  assert (HepsC : real_lt real_zero (real_mult eps (real_const (1 # 4)))).
  { apply b5dI_real_mult_positive_exp. { exact Heps. } { apply b5dM_real_const_pos. exact HkT4. } }
  destruct (b5dI_sin_atan_diff_closed_r_exp r Hr0 Hr1 x Hxr
             Msr Mc C4 HMsr_pos HMcQ HC40 HC4ge1 HC4 HMsr_all HMc_all
             (real_mult eps (real_const (1 # 4))) HepsS) as [δS [HδS0 HδS]].
  destruct (b5dI_cos_atan_diff_closed_r_exp r Hr0 Hr1 x Hxr
             Msr Mc C4 HMsr_pos HMcQ HC40 HC4ge1 HC4 HMsr_all HMc_all
             (real_mult eps (real_const (1 # 4))) HepsC) as [δC [HδC0 HδC]].
  assert (Hepskδ : real_lt real_zero (real_mult eps (real_const kδ))).
  { apply b5dI_real_mult_positive_exp. { exact Heps. } { apply b5dM_real_const_pos. exact HkδT. } }
  set (delta := real_min (real_min δS δC) (real_mult eps (real_const kδ))).
  assert (Hdpos : real_lt real_zero delta).
  { unfold delta.
    apply real_min_pos.
    { apply real_min_pos. { exact HδS0. } { exact HδC0. } }
    { exact Hepskδ. } }
  exists delta.
  split.
  { exact Hdpos. }
  { intros h Hh Hxh eps' Heps'.
  destruct (b5dM_b5c_d_proj_le_one x) as [Nd Hd].
  destruct (b5dM_b5n_eps_proj_lt eps Heps) as [e0 [He0T [Ne0 He0lt]]].
    destruct (b5dM_b5n_eps_proj_lt eps' Heps') as [e1 [He1T [Ne1 He1lt]]].
    set (eta := Qmult (1 # 8) e1).
    assert (HetaT : QltT 0 eta).
    { unfold eta. apply Qlt_to_QltT.
      apply (Qmult_lt_0_compat (1 # 8) e1).
      { unfold Qlt. simpl. lia. }
      { apply QltT_to_Qlt. exact He1T. } }
    (* |h| 相对 δ 的 min 提取：δS / δC / eps·kδ *)
    assert (HhA : real_lt (real_abs h) (real_min δS δC)).
    { apply (real_min_lt_l h (real_min δS δC) (real_mult eps (real_const kδ))).
      exact Hh. }
    assert (Hhlr : real_lt (real_abs h) (real_mult eps (real_const kδ))).
    { apply (real_min_lt_r h (real_min δS δC) (real_mult eps (real_const kδ))).
      exact Hh. }
    assert (HhδS : real_lt (real_abs h) δS).
    { apply (real_min_lt_l h δS δC). exact HhA. }
    assert (HhδC : real_lt (real_abs h) δC).
    { apply (real_min_lt_r h δS δC). exact HhA. }
    (* sin 份额：闭式 + 逐点转换（松弛 shS := eps'·(1/16)） *)
    assert (HepsS'' : real_lt real_zero (real_mult eps' (real_const (1 # 8)))).
    { apply real_mult_positive. { exact Heps'. } { apply b5dM_real_const_pos. exact HkT8. } }
    assert (HshS : real_lt real_zero (real_mult eps' (real_const (1 # 16)))).
    { apply real_mult_positive. { exact Heps'. } { apply b5dM_real_const_pos. exact HkT16. } }
    destruct (b5i_abs_le_pointwise (b5a_comp_err_sin x Hx h Hxh)
               (real_plus (real_mult (real_mult eps (real_const (1 # 4))) (real_abs h))
                          (real_mult eps' (real_const (1 # 8))))
               (HδS h HhδS Hxh (real_mult eps' (real_const (1 # 8))) HepsS'')
               (real_mult eps' (real_const (1 # 16))) HshS) as [Ns HNs].
    (* cos 份额：闭式 + 逐点转换 *)
    assert (HepsC'' : real_lt real_zero (real_mult eps' (real_const (1 # 8)))).
    { apply real_mult_positive. { exact Heps'. } { apply b5dM_real_const_pos. exact HkT8. } }
    assert (HshC : real_lt real_zero (real_mult eps' (real_const (1 # 16)))).
    { apply real_mult_positive. { exact Heps'. } { apply b5dM_real_const_pos. exact HkT16. } }
    destruct (b5i_abs_le_pointwise (b5a_comp_err_cos x Hx h Hxh)
               (real_plus (real_mult (real_mult eps (real_const (1 # 4))) (real_abs h))
                          (real_mult eps' (real_const (1 # 8))))
               (HδC h HhδC Hxh (real_mult eps' (real_const (1 # 8))) HepsC'')
               (real_mult eps' (real_const (1 # 16))) HshC) as [Nc HNc].
    (* |h_n| ≤ en·kδ；dec 逐点恒等 N *)
    destruct (b5i_h_le_enk h eps kδ Hhlr HkδT) as [Nhδ HNhδ].
    destruct (b5e_E_dec_proj x Hx h Hxh) as [Ndec HNdec].
    (* 逐点预算（对 eps' 见证） *)
    assert (Hen'g : forall n : nat, NatLe Ne1 n -> Qle 0 (projT1 eps' n)).
    { intros n Hn.
      apply (Qle_trans 0 e1 (projT1 eps' n)).
      { apply Qlt_le_weak. apply QltT_to_Qlt. exact He1T. }
      { apply Qlt_le_weak. exact (He1lt n Hn). } }
    set (Nmax := Nat.max (Nat.max Ne0 Ne1)
                 (Nat.max (Nat.max Ndec Nhδ) (Nat.max (Nat.max Ns Nc) Nd))).
    (* 主装配：real_le → real_lt（左支），见证 eta *)
    left.
    exists eta.
    split.
    { exact HetaT. }
    { exists Nmax.
      intros n Hn.
      apply NatLe_drop in Hn.
      set (en := projT1 eps n).
      set (en' := projT1 eps' n).
      set (hn := Qabs (projT1 h n)).
      set (Dn := Qabs (projT1 (b5e_E_err x Hx h Hxh) n)).
      assert (HnNe0 : NatLe Ne0 n) by (apply NatLe_lift; lia).
      assert (HnNe1 : NatLe Ne1 n) by (apply NatLe_lift; lia).
      assert (HnNs : NatLe Ns n) by (apply NatLe_lift; lia).
      assert (HnNc : NatLe Nc n) by (apply NatLe_lift; lia).
      assert (HnNhδ : NatLe Nhδ n) by (apply NatLe_lift; lia).
      assert (HnNdec : NatLe Ndec n) by (apply NatLe_lift; lia).
      assert (HnNd : (Nd <= n)%nat) by lia.
      assert (Hen0 : Qle 0 en).
      { unfold en. apply (Qle_trans 0 e0 (projT1 eps n)).
        { apply Qlt_le_weak. apply QltT_to_Qlt. exact He0T. }
        { apply Qlt_le_weak. exact (He0lt n HnNe0). } }
      assert (Hen'0 : Qle 0 en').
      { unfold en'. exact (Hen'g n HnNe1). }
      assert (Hhδn : Qle (Qabs (projT1 h n)) (Qmult en kδ)).
      { unfold en. exact (HNhδ n HnNhδ). }
      (* 逐点份额界展开（sin） *)
      assert (Hrs : Qle (Qabs (projT1 (b5a_comp_err_sin x Hx h Hxh) n))
                        (Qplus (Qmult (Qmult en (1 # 4)) (Qabs (projT1 h n)))
                               (Qplus (Qmult en' (1 # 8)) (Qmult en' (1 # 16))))).
      { apply (Qle_trans (Qabs (projT1 (b5a_comp_err_sin x Hx h Hxh) n))
                         (Qplus (projT1 (real_plus (real_mult (real_mult eps (real_const (1 # 4))) (real_abs h))
                                                   (real_mult eps' (real_const (1 # 8)))) n)
                                (projT1 (real_mult eps' (real_const (1 # 16))) n))
                         (Qplus (Qmult (Qmult en (1 # 4)) (Qabs (projT1 h n)))
                                (Qplus (Qmult en' (1 # 8)) (Qmult en' (1 # 16))))).
        { exact (HNs n HnNs). }
        { apply qeq_imp_qle.
          unfold en, en'.
          setoid_rewrite (real_plus_proj (real_mult (real_mult eps (real_const (1 # 4))) (real_abs h))
                                         (real_mult eps' (real_const (1 # 8))) n).
          setoid_rewrite (real_mult_proj (real_mult eps (real_const (1 # 4))) (real_abs h) n).
          setoid_rewrite (real_mult_proj eps (real_const (1 # 4)) n).
          rewrite (real_const_proj (1 # 4) n).
          setoid_rewrite (real_abs_proj h n).
          setoid_rewrite (real_mult_proj eps' (real_const (1 # 8)) n).
          rewrite (real_const_proj (1 # 8) n).
          setoid_rewrite (real_mult_proj eps' (real_const (1 # 16)) n).
          rewrite (real_const_proj (1 # 16) n).
          ring. } }
      (* 逐点份额界展开（cos，含 |x+h| ≤ 1 折入） *)
      assert (Hxh'n : Qle (Qabs (Qplus (projT1 x n) (projT1 h n))) 1).
      { apply (Qle_trans (Qabs (Qplus (projT1 x n) (projT1 h n)))
                         (Qabs (projT1 (real_plus x h) n))
                         1).
        { apply qeq_le. apply (Qabs_wd (Qplus (projT1 x n) (projT1 h n))
                                       (projT1 (real_plus x h) n)).
          rewrite (real_plus_proj x h n). ring. }
        { apply QleT'_to_Qle. exact (Hxh n). } }
      assert (Hrc0 : Qle (Qabs (projT1 (b5a_comp_err_cos x Hx h Hxh) n))
                         (Qplus (Qmult (Qmult en (1 # 4)) (Qabs (projT1 h n)))
                                (Qplus (Qmult en' (1 # 8)) (Qmult en' (1 # 16))))).
      { apply (Qle_trans (Qabs (projT1 (b5a_comp_err_cos x Hx h Hxh) n))
                         (Qplus (projT1 (real_plus (real_mult (real_mult eps (real_const (1 # 4))) (real_abs h))
                                                   (real_mult eps' (real_const (1 # 8)))) n)
                                (projT1 (real_mult eps' (real_const (1 # 16))) n))
                         (Qplus (Qmult (Qmult en (1 # 4)) (Qabs (projT1 h n)))
                                (Qplus (Qmult en' (1 # 8)) (Qmult en' (1 # 16))))).
        { exact (HNc n HnNc). }
        { apply qeq_imp_qle.
          unfold en, en'.
          setoid_rewrite (real_plus_proj (real_mult (real_mult eps (real_const (1 # 4))) (real_abs h))
                                         (real_mult eps' (real_const (1 # 8))) n).
          setoid_rewrite (real_mult_proj (real_mult eps (real_const (1 # 4))) (real_abs h) n).
          setoid_rewrite (real_mult_proj eps (real_const (1 # 4)) n).
          rewrite (real_const_proj (1 # 4) n).
          setoid_rewrite (real_abs_proj h n).
          setoid_rewrite (real_mult_proj eps' (real_const (1 # 8)) n).
          rewrite (real_const_proj (1 # 8) n).
          setoid_rewrite (real_mult_proj eps' (real_const (1 # 16)) n).
          rewrite (real_const_proj (1 # 16) n).
          ring. } }
      assert (Hrc : Qle (Qabs (Qmult (Qplus (projT1 x n) (projT1 h n))
                                     (projT1 (b5a_comp_err_cos x Hx h Hxh) n)))
                        (Qplus (Qmult (Qmult en (1 # 4)) (Qabs (projT1 h n)))
                               (Qplus (Qmult en' (1 # 8)) (Qmult en' (1 # 16))))).
      { apply (Qle_trans (Qabs (Qmult (Qplus (projT1 x n) (projT1 h n))
                                      (projT1 (b5a_comp_err_cos x Hx h Hxh) n)))
                         (Qmult (Qabs (Qplus (projT1 x n) (projT1 h n)))
                                (Qabs (projT1 (b5a_comp_err_cos x Hx h Hxh) n)))
                         (Qplus (Qmult (Qmult en (1 # 4)) (Qabs (projT1 h n)))
                                (Qplus (Qmult en' (1 # 8)) (Qmult en' (1 # 16))))).
        { apply qeq_le. apply (Qabs_Qmult (Qplus (projT1 x n) (projT1 h n))
                                          (projT1 (b5a_comp_err_cos x Hx h Hxh) n)). }
        { apply (Qle_trans (Qmult (Qabs (Qplus (projT1 x n) (projT1 h n)))
                                  (Qabs (projT1 (b5a_comp_err_cos x Hx h Hxh) n)))
                           (Qmult 1 (Qabs (projT1 (b5a_comp_err_cos x Hx h Hxh) n)))
                           (Qplus (Qmult (Qmult en (1 # 4)) (Qabs (projT1 h n)))
                                  (Qplus (Qmult en' (1 # 8)) (Qmult en' (1 # 16))))).
          { apply (Qmult_le_compat_r (Qabs (Qplus (projT1 x n) (projT1 h n))) 1
                                     (Qabs (projT1 (b5a_comp_err_cos x Hx h Hxh) n))).
            { exact Hxh'n. }
            { apply Qabs_nonneg. } }
          { apply (Qle_trans (Qmult 1 (Qabs (projT1 (b5a_comp_err_cos x Hx h Hxh) n)))
                             (Qabs (projT1 (b5a_comp_err_cos x Hx h Hxh) n))
                             (Qplus (Qmult (Qmult en (1 # 4)) (Qabs (projT1 h n)))
                                    (Qplus (Qmult en' (1 # 8)) (Qmult en' (1 # 16))))).
            { apply qeq_imp_qle. ring. }
            { exact Hrc0. } } } }
      (* 残差份额（b5e_res_le） *)
      assert (Hres : Qle (Qabs (projT1 (real_mult h (real_mult (cauchy_real_sin (cauchy_real_arctan x Hx))
                                                             (real_mult (b5a_atan_d x) h))) n))
                         (Qmult (Qmult (Qmult Msr kδ) en) (Qabs (projT1 h n)))).
      { apply (b5e_res_le x Hx h n Msr kδ en).
        { exact (Hd n HnNd). }
        { apply (b5dI_sA_proj_le x Hx n Msr). exact (HMsr_all n). }
        { exact Hhδn. }
        { exact Hen0. }
        { exact HMsr0. }
        { exact Hkδ0. } }
      (* Z：per-n 主界 *)
      assert (Hmain : Qle (Qabs (projT1 (b5e_E_err x Hx h Hxh) n))
                          (Qplus (Qmult en (Qabs (projT1 h n))) (Qmult (3 # 4) en'))).
      { unfold Dn.
        apply (Qle_trans (Qabs (projT1 (b5e_E_err x Hx h Hxh) n))
                         (Qabs (projT1 (b5e_E_dec x Hx h Hxh) n))
                         (Qplus (Qmult en (Qabs (projT1 h n))) (Qmult (3 # 4) en'))).
        { apply qeq_le.
          apply (Qabs_wd (projT1 (b5e_E_err x Hx h Hxh) n)
                         (projT1 (b5e_E_dec x Hx h Hxh) n)).
          exact (HNdec n HnNdec). }
        { apply (b5e_pern_main x Hx h Hxh n
                 (1 # 4) (1 # 4) (1 # 8) (1 # 8) (1 # 16) (1 # 16) Msr kδ en en').
          { exact Hrs. }
          { exact Hrc. }
          { exact Hres. }
          { exact Hen0. }
          { exact Hen'0. }
          { exact HMsr0. }
          { exact Hkδ0. }
          { exact Hcoef. }
          { exact Hadd. } } }
      (* margin：eta < (1/4)en'；Hfin：eta < (en·hn + en') − Dn *)
      assert (Hq4e : Qlt eta (Qmult (1 # 4) en')).
      { unfold eta, en'. apply (b5n_quarter_gt e1 (projT1 eps' n)).
        { apply QltT_to_Qlt. exact He1T. }
        { exact (He1lt n HnNe1). } }
      assert (Hfin : Qlt eta (Qminus (Qplus (Qmult en hn) en') Dn)).
      { apply (b5n_close Dn hn en en' eta).
        { unfold Dn. exact Hmain. }
        { unfold en'. exact Hq4e. } }
      assert (Hrepl : Qeq (Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                                  (projT1 (real_abs (b5e_E_err x Hx h Hxh)) n))
                          (Qminus (Qplus (Qmult en hn) en') Dn)).
      { unfold en, en', hn, Dn.
        setoid_rewrite (real_plus_proj (real_mult eps (real_abs h)) eps' n).
        setoid_rewrite (real_mult_proj eps (real_abs h) n).
        setoid_rewrite (real_abs_proj h n).
        setoid_rewrite (real_abs_proj (b5e_E_err x Hx h Hxh) n).
        ring. }
      apply Qlt_to_QltT.
      apply (Qlt_le_trans eta
             (Qminus (Qplus (Qmult en hn) en') Dn)
             (Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                     (projT1 (real_abs (b5e_E_err x Hx h Hxh)) n))).
      { exact Hfin. }
      { apply qeq_imp_qle. apply Qeq_sym. exact Hrepl. } } }
Defined.

(* ============================================================ *)
(* 块 item20（前缀 b5dJ_——主件 b5dJ_log_diff_dx_exp）——来源：演变/.ablation/sc2_parallel/sc2_b5a_ode/sc2_b5a_item20.v。 *)
(* ============================================================ *)

(* ============================================================ *)
(* J0 b5dJ_two_pos_exp（Defined 透明证书，δ 值侧证书）           *)
(* 根 real_two_pos_local = Qed（L44573–44579）。real_inv_pos 值  *)
(*   按证书 destruct 出 N0 ⟹ 不透明证书使 vm_compute 停滞。      *)
(* J0 = 显式见证 eps = 1/2、N = 0 的闭式证明（零根引用），       *)
(*   Defined 收尾 ⟹ projT1 (real_inv_pos (1+1) J0) n 全 n 可算   *)
(*   = Qinv 2（检验实证 = 1#2）。                                *)
(* ============================================================ *)
Lemma b5dJ_two_pos_exp : real_lt real_zero (real_plus real_one real_one).
Proof.
  unfold real_lt.
  exists (1 # 2).
  split.
  - vm_compute. constructor.
  - exists 0%nat. intros n Hn. vm_compute. constructor.
Defined.

(* ============================================================ *)
(* J1 b5dJ_log_diff_dx_exp（Defined 透明）                       *)
(* 拷贝源：213 根 b5f_log_diff_dx（ConstructiveWorld.v           *)
(*   L81720–82145，426 行，pwsh 行切片机器抽取零手抄）；          *)
(*   语句不变。                                                  *)
(* 三改（含 δ 值路径证书透明化最小改动，设计见头注释）：         *)
(*   ① Lemma 头改名 ② 收尾 Qed→Defined ③ 值侧 J0 证书 + 提取    *)
(*   桥接（lets/δ/0<δ/两提取点）。                               *)
(* ============================================================ *)
Lemma b5dJ_log_diff_dx_exp : forall (x0 : Real) (Hx0 : real_lt real_zero x0),
  forall (eps : Real), real_lt real_zero eps ->
  sigT (fun delta : Real => And (real_lt real_zero delta)
    (forall (h : Real), real_lt (real_abs h) delta ->
      forall (Hxh : real_lt real_zero (real_plus x0 h)),
      forall (eps' : Real), real_lt real_zero eps' ->
      real_le (real_abs (real_plus (real_log (real_plus x0 h) Hxh)
                 (real_opp (real_plus (real_log x0 Hx0) (real_mult (real_inv_pos x0 Hx0) h)))))
              (real_plus (real_mult eps (real_abs h)) eps'))).
Proof.
  intros x0 Hx0 eps Heps.
  set (two_inv := real_inv_pos (real_plus real_one real_one) (real_two_pos_local)).
  set (four_inv := real_mult two_inv two_inv).
  set (eight_inv := real_mult four_inv two_inv).
  set (half_x := real_mult two_inv x0).
  set (eps_x2 := real_mult eps (real_mult x0 x0)).
  set (eps4 := real_mult four_inv eps_x2).      (* eps·x²/4 *)
    (* δ 值路径透明化：值侧 half_xJ/eps4J 用 J0（b5dJ_two_pos_exp，
       Defined 透明证书）；证明侧 rtl 形 two_inv/four_inv/half_x/eps4
       原样保留——根辅助件语句内嵌 real_two_pos_local，apply 需原形；
       两侧逐点相等，桥接见下。 *)
    set (two_invJ := real_inv_pos (real_plus real_one real_one) (b5dJ_two_pos_exp)).
    set (four_invJ := real_mult two_invJ two_invJ).
    set (half_xJ := real_mult two_invJ x0).
    set (eps4J := real_mult four_invJ eps_x2).
  set (delta := real_min half_xJ eps4J).
  exists delta.
  split.
  - (* 0 < delta：min_pos（half_xJ/eps4J，J0 透明证书） *)
    unfold delta, half_xJ, eps4J, eps_x2, four_invJ, two_invJ.
    apply real_min_pos.
    + apply real_mult_positive.
      * apply (real_inv_pos_pos (real_plus real_one real_one) (b5dJ_two_pos_exp)).
      * exact Hx0.
    + apply real_mult_positive.
      * apply real_mult_positive.
        -- apply (real_inv_pos_pos (real_plus real_one real_one) (b5dJ_two_pos_exp)).
        -- apply (real_inv_pos_pos (real_plus real_one real_one) (b5dJ_two_pos_exp)).
      * apply real_mult_positive.
        -- exact Heps.
        -- apply real_mult_positive.
           ++ exact Hx0.
           ++ exact Hx0.
  - intros h Hh Hxh eps' Heps'.
    (* 份额 share := inv8·eps'（5 份共用） *)
    set (share := real_mult eight_inv eps').
    assert (Hshare : real_lt real_zero share).
    { unfold share. apply real_mult_positive.
      - unfold eight_inv, four_inv, two_inv.
        apply real_mult_positive.
        + apply real_mult_positive.
          * apply (real_inv_pos_pos (real_plus real_one real_one) (real_two_pos_local)).
          * apply (real_inv_pos_pos (real_plus real_one real_one) (real_two_pos_local)).
        + apply (real_inv_pos_pos (real_plus real_one real_one) (real_two_pos_local)).
      - exact Heps'. }
    (* t := h·inv x0 *)
    set (t := real_mult h (real_inv_pos x0 Hx0)).
    (* 桥接组：值侧（J0）与证明侧（rtl）real_eq——real_inv_proj + u 常值 2 闭式 *)
    assert (Htwo_eq : real_eq two_invJ two_inv).
    { unfold real_eq. intros eps0 Heps0.
      destruct (real_inv_proj (real_plus real_one real_one) real_two_pos_local) as [Ni HNi].
      exists Ni. intros n Hn.
      assert (Hnle : (Ni <= n)%nat) by (apply NatLe_drop; exact Hn).
      unfold two_invJ, two_inv.
      assert (Hj : projT1 (real_inv_pos (real_plus real_one real_one) b5dJ_two_pos_exp) n
                   == Qinv (projT1 (real_plus real_one real_one) n)).
      { vm_compute. reflexivity. }
      assert (Hr : projT1 (real_inv_pos (real_plus real_one real_one) real_two_pos_local) n
                   == Qinv (projT1 (real_plus real_one real_one) n)).
      { apply (HNi n). exact Hnle. }
      assert (Hd : projT1 (real_inv_pos (real_plus real_one real_one) b5dJ_two_pos_exp) n
                   - projT1 (real_inv_pos (real_plus real_one real_one) real_two_pos_local) n == 0).
      { rewrite Hj. rewrite Hr. ring. }
      assert (Habs0 : Qabs (projT1 (real_inv_pos (real_plus real_one real_one) b5dJ_two_pos_exp) n
                        - projT1 (real_inv_pos (real_plus real_one real_one) real_two_pos_local) n) == 0).
      { apply (Qeq_trans _ (Qabs 0) _).
        - apply (Qabs_wd (projT1 (real_inv_pos (real_plus real_one real_one) b5dJ_two_pos_exp) n
                          - projT1 (real_inv_pos (real_plus real_one real_one) real_two_pos_local) n) 0).
          exact Hd.
        - cbn [Qabs]. reflexivity. }
      apply (qltT_eq_compat_l 0
               (Qabs (projT1 (real_inv_pos (real_plus real_one real_one) b5dJ_two_pos_exp) n
                     - projT1 (real_inv_pos (real_plus real_one real_one) real_two_pos_local) n)) eps0).
      - apply Qeq_sym. exact Habs0.
      - exact Heps0. }
    assert (Hfour_eq : real_eq four_invJ four_inv).
    { unfold four_invJ, four_inv.
      apply (RealSetoid.real_eq_mult_compat two_invJ two_invJ two_inv two_inv Htwo_eq Htwo_eq). }
    assert (Hhalf_le : real_le half_xJ half_x).
    { unfold half_xJ, half_x.
      apply RealSetoid.real_eq_le.
      apply (RealSetoid.real_eq_mult_compat two_invJ x0 two_inv x0 Htwo_eq (real_eq_refl x0)). }
    assert (Heps4_le : real_le eps4J eps4).
    { unfold eps4J, eps4.
      apply RealSetoid.real_eq_le.
      apply (RealSetoid.real_eq_mult_compat four_invJ eps_x2 four_inv eps_x2 Hfour_eq (real_eq_refl eps_x2)). }
    (* 前提链 *)
    assert (Hh_halfJ : real_lt (real_abs h) half_xJ).
    { apply (real_min_lt_l h half_xJ eps4J). unfold delta. exact Hh. }
    assert (Hh_half : real_lt (real_abs h) half_x).
    { apply (real_lt_le_trans (real_abs h) half_xJ half_x).
      - exact Hh_halfJ.
      - exact Hhalf_le. }
    assert (Ht_half : real_lt (real_abs t) two_inv).
    { unfold t. apply (real_t_abs_lt_half x0 h Hx0). exact Hh_half. }
    assert (Ht_lower : real_lt (real_opp two_inv) t).
    { apply (real_abs_lt_lower t two_inv). exact Ht_half. }
    assert (Hhalf_t : real_lt two_inv (real_plus real_one t)).
    { apply (real_half_lt_one_plus_t t). exact Ht_lower. }
    assert (Htpos : real_lt real_zero (real_plus real_one t)).
    { apply (real_lt_trans real_zero two_inv (real_plus real_one t)).
      - apply (real_inv_pos_pos (real_plus real_one real_one) (real_two_pos_local)).
      - exact Hhalf_t. }
    assert (Hh_eps4J : real_lt (real_abs h) eps4J).
    { apply (real_min_lt_r h half_xJ eps4J). unfold delta. exact Hh. }
    assert (Hh_eps4 : real_lt (real_abs h) eps4).
    { apply (real_lt_le_trans (real_abs h) eps4J eps4).
      - exact Hh_eps4J.
      - exact Heps4_le. }
    (* X := log(1+t) − t *)
    set (X := real_plus (real_log (real_plus real_one t) Htpos) (real_opp t)).
    (* 断言 D == X *)
    assert (HDX : real_eq
      (real_plus (real_log (real_plus x0 h) Hxh)
                 (real_opp (real_plus (real_log x0 Hx0) (real_mult (real_inv_pos x0 Hx0) h))))
      X).
    {
      (* D == log(x0+h) + (opp(log x0) + opp(inv·h))：opp_plus 拆开 *)
      apply (real_eq_trans
        (real_plus (real_log (real_plus x0 h) Hxh)
                   (real_opp (real_plus (real_log x0 Hx0) (real_mult (real_inv_pos x0 Hx0) h))))
        (real_plus (real_log (real_plus x0 h) Hxh)
                   (real_plus (real_opp (real_log x0 Hx0))
                              (real_opp (real_mult (real_inv_pos x0 Hx0) h))))
        X).
      - apply (RealSetoid.real_eq_plus_compat
                 (real_log (real_plus x0 h) Hxh)
                 (real_opp (real_plus (real_log x0 Hx0) (real_mult (real_inv_pos x0 Hx0) h)))
                 (real_log (real_plus x0 h) Hxh)
                 (real_plus (real_opp (real_log x0 Hx0))
                            (real_opp (real_mult (real_inv_pos x0 Hx0) h)))).
        + apply real_eq_refl.
        + apply (real_opp_plus (real_log x0 Hx0) (real_mult (real_inv_pos x0 Hx0) h)).
      - (* (log(x0+h) + (opplog + oppinv)) == (log(x0+h) − log x0) + (−inv·h)：assoc *)
        apply (real_eq_trans
          (real_plus (real_log (real_plus x0 h) Hxh)
                     (real_plus (real_opp (real_log x0 Hx0))
                                (real_opp (real_mult (real_inv_pos x0 Hx0) h))))
          (real_plus (real_plus (real_log (real_plus x0 h) Hxh) (real_opp (real_log x0 Hx0)))
                     (real_opp (real_mult (real_inv_pos x0 Hx0) h)))
          X).
        + apply (real_plus_assoc (real_log (real_plus x0 h) Hxh)
                                 (real_opp (real_log x0 Hx0))
                                 (real_opp (real_mult (real_inv_pos x0 Hx0) h))).
        + (* (log(x0+h) − log x0) + (−inv·h) == log(1+t) − t *)
          apply (RealSetoid.real_eq_plus_compat
                   (real_plus (real_log (real_plus x0 h) Hxh) (real_opp (real_log x0 Hx0)))
                   (real_opp (real_mult (real_inv_pos x0 Hx0) h))
                   (real_log (real_plus real_one t) Htpos)
                   (real_opp t)).
          * (* log(x0+h) − log x0 == log(1+t)：real_log_plus_diff *)
            apply (real_log_plus_diff x0 h Hx0 Hxh Htpos).
          * (* −inv·h == −t：mult_comm 换形 + t 定义 *)
            apply (real_eq_trans (real_opp (real_mult (real_inv_pos x0 Hx0) h))
                                 (real_opp (real_mult h (real_inv_pos x0 Hx0)))
                                 (real_opp t)).
            -- apply (RealSetoid.real_eq_opp_compat
                       (real_mult (real_inv_pos x0 Hx0) h)
                       (real_mult h (real_inv_pos x0 Hx0))).
               apply (real_mult_comm (real_inv_pos x0 Hx0) h).
            -- apply real_eq_refl.
    }
    (* 上界：X ≤ share *)
    assert (HXup : real_le X share).
    {
      apply (real_le_trans X (real_plus (real_plus t share) (real_opp t)) share).
      - (* X ≤ (t+share) − t：le_eps + plus_le_compat *)
        unfold X.
        apply (real_le_plus_compat (real_log (real_plus real_one t) Htpos) (real_plus t share)
                                   (real_opp t) (real_opp t)).
        + exact (real_log_one_plus_le_eps t share Htpos Hshare).
        + apply real_le_refl.
      - (* (t+share) − t ≤ share：eq_le，环 *)
        apply RealSetoid.real_eq_le.
        apply (real_eq_trans (real_plus (real_plus t share) (real_opp t))
                             (real_plus t (real_plus share (real_opp t)))
                             share).
        + apply real_eq_sym. apply (real_plus_assoc t share (real_opp t)).
        + apply (real_eq_trans (real_plus t (real_plus share (real_opp t)))
                               (real_plus (real_plus t (real_opp t)) share)
                               share).
          * apply (real_eq_trans (real_plus t (real_plus share (real_opp t)))
                                 (real_plus t (real_plus (real_opp t) share))
                                 (real_plus (real_plus t (real_opp t)) share)).
            -- apply (RealSetoid.real_eq_plus_compat t (real_plus share (real_opp t))
                                                       t (real_plus (real_opp t) share)).
               ++ apply real_eq_refl.
               ++ apply (real_plus_comm share (real_opp t)).
            -- apply (real_plus_assoc t (real_opp t) share).
          * apply (real_eq_trans (real_plus (real_plus t (real_opp t)) share)
                                 (real_plus real_zero share)
                                 share).
            -- apply (RealSetoid.real_eq_plus_compat (real_plus t (real_opp t)) share real_zero share).
               ++ apply (real_plus_opp t).
               ++ apply real_eq_refl.
            -- apply (real_eq_trans (real_plus real_zero share) (real_plus share real_zero) share).
               ** apply (real_plus_comm real_zero share).
               ** apply (real_plus_zero share).
    }
    (* 下界：−X ≤ 2t² + (share+share) *)
    assert (HXdown : real_le (real_opp X)
      (real_plus (real_mult (real_mult t t) (real_plus real_one real_one))
                 (real_plus share share))).
    {
      apply (real_le_trans (real_opp X)
                           (real_plus t (real_opp (real_log (real_plus real_one t) Htpos)))
                           (real_plus (real_mult (real_mult t t) (real_plus real_one real_one)) (real_plus share share))).
      - (* −X == t − log s：eq_le，opp_plus 换形 *)
        unfold X.
        apply RealSetoid.real_eq_le.
        apply (real_eq_trans (real_opp (real_plus (real_log (real_plus real_one t) Htpos) (real_opp t)))
                             (real_plus (real_opp (real_log (real_plus real_one t) Htpos)) (real_opp (real_opp t)))
                             (real_plus t (real_opp (real_log (real_plus real_one t) Htpos)))).
        + apply (real_opp_plus (real_log (real_plus real_one t) Htpos) (real_opp t)).
        + apply (real_eq_trans (real_plus (real_opp (real_log (real_plus real_one t) Htpos)) (real_opp (real_opp t)))
                               (real_plus (real_opp (real_opp t)) (real_opp (real_log (real_plus real_one t) Htpos)))
                               (real_plus t (real_opp (real_log (real_plus real_one t) Htpos)))).
          * apply (real_plus_comm (real_opp (real_log (real_plus real_one t) Htpos)) (real_opp (real_opp t))).
          * apply (RealSetoid.real_eq_plus_compat (real_opp (real_opp t))
                                                  (real_opp (real_log (real_plus real_one t) Htpos))
                                                  t
                                                  (real_opp (real_log (real_plus real_one t) Htpos))).
            -- apply (real_opp_opp t).
            -- apply real_eq_refl.
      - (* t − log s ≤ 2t² + share + share *)
        apply (real_le_trans (real_plus t (real_opp (real_log (real_plus real_one t) Htpos)))
                             (real_plus (real_mult (real_mult t t) (real_inv_pos (real_plus real_one t) Htpos)) share)
                             (real_plus (real_mult (real_mult t t) (real_plus real_one real_one)) (real_plus share share))).
        + exact (real_t_minus_log_bound t share Htpos Hshare).
        + apply (real_le_trans (real_plus (real_mult (real_mult t t) (real_inv_pos (real_plus real_one t) Htpos)) share)
                               (real_plus (real_plus (real_mult (real_mult t t) (real_plus real_one real_one)) share) share)
                               (real_plus (real_mult (real_mult t t) (real_plus real_one real_one)) (real_plus share share))).
          * apply (real_le_plus_compat (real_mult (real_mult t t) (real_inv_pos (real_plus real_one t) Htpos))
                                       (real_plus (real_mult (real_mult t t) (real_plus real_one real_one)) share)
                                       share share).
            -- exact (real_quad_div_le_two_eps t (real_plus real_one t) share Htpos Hhalf_t Hshare).
            -- apply real_le_refl.
          * apply RealSetoid.real_eq_le.
            apply real_eq_sym. apply (real_plus_assoc (real_mult (real_mult t t) (real_plus real_one real_one)) share share).
    }
    (* abs 桥：|X| ≤ 2t² + (share + (share+share)) + share *)
    assert (Habs : real_le (real_abs X)
      (real_plus (real_plus (real_mult (real_mult t t) (real_plus real_one real_one))
                            (real_plus share (real_plus share share)))
                 share)).
    { apply (real_abs_le_quad_eps X t share (real_plus share share) share).
      - exact HXup.
      - exact HXdown.
      - exact Hshare.
      - (* 0 < share + share *)
        apply real_plus_positive; exact Hshare.
      - exact Hshare. }
    (* 22c：2t² ≤ (eps/2)|h| + share *)
    assert (Hquad : real_le
      (real_mult (real_mult (real_mult h (real_inv_pos x0 Hx0)) (real_mult h (real_inv_pos x0 Hx0)))
                 (real_plus real_one real_one))
      (real_plus (real_mult (real_mult two_inv eps) (real_abs h)) share)).
    { apply (real_quad_t_le_h_eps x0 h eps share Hx0 Hh_eps4 Heps Hshare). }
    (* 汇总 1：|D| == |X|（HDX + real_abs_eq_compat） *)
    assert (HabsD : real_le (real_abs
      (real_plus (real_log (real_plus x0 h) Hxh)
                 (real_opp (real_plus (real_log x0 Hx0) (real_mult (real_inv_pos x0 Hx0) h)))))
      (real_plus (real_plus (real_mult (real_mult t t) (real_plus real_one real_one))
                            (real_plus share (real_plus share share)))
                 share)).
    {
      apply (real_le_trans (real_abs
        (real_plus (real_log (real_plus x0 h) Hxh)
                   (real_opp (real_plus (real_log x0 Hx0) (real_mult (real_inv_pos x0 Hx0) h)))))
                           (real_abs X)
                           (real_plus (real_plus (real_mult (real_mult t t) (real_plus real_one real_one))
                                                 (real_plus share (real_plus share share)))
                                      share)).
      - (* |D| == |X| ⟹ |D| ≤ |X|：real_abs_eq_compat + eq_le *)
        apply RealSetoid.real_eq_le.
        apply (real_abs_eq_compat
          (real_plus (real_log (real_plus x0 h) Hxh)
                     (real_opp (real_plus (real_log x0 Hx0) (real_mult (real_inv_pos x0 Hx0) h))))
          X).
        exact HDX.
      - exact Habs.
    }
    (* 汇总 2：2t² + C ≤ ((eps/2)|h| + share) + C == (eps/2)|h| + (share + C) *)
    assert (Hmid : real_le
      (real_plus (real_plus (real_mult (real_mult t t) (real_plus real_one real_one))
                            (real_plus share (real_plus share share)))
                 share)
      (real_plus (real_mult (real_mult two_inv eps) (real_abs h))
                 (real_plus share (real_plus (real_plus share (real_plus share share)) share)))).
    {
      apply (real_le_trans
        (real_plus (real_plus (real_mult (real_mult t t) (real_plus real_one real_one))
                              (real_plus share (real_plus share share)))
                   share)
        (real_plus (real_mult (real_mult t t) (real_plus real_one real_one))
                   (real_plus (real_plus share (real_plus share share)) share))
        (real_plus (real_mult (real_mult two_inv eps) (real_abs h))
                   (real_plus share (real_plus (real_plus share (real_plus share share)) share)))).
      - (* (2t² + C') + share == 2t² + C（assoc 反向，C := C'+share） *)
        apply RealSetoid.real_eq_le.
        apply real_eq_sym.
        apply (real_plus_assoc (real_mult (real_mult t t) (real_plus real_one real_one))
                               (real_plus share (real_plus share share))
                               share).
      - (* 2t² + C ≤ ((eps/2)|h| + share) + C ≤ (eps/2)|h| + (share + C) *)
        apply (real_le_trans
          (real_plus (real_mult (real_mult t t) (real_plus real_one real_one))
                     (real_plus (real_plus share (real_plus share share)) share))
          (real_plus (real_plus (real_mult (real_mult two_inv eps) (real_abs h)) share)
                     (real_plus (real_plus share (real_plus share share)) share))
          (real_plus (real_mult (real_mult two_inv eps) (real_abs h))
                     (real_plus share (real_plus (real_plus share (real_plus share share)) share)))).
        + (* 2t² + C ≤ ((eps/2)|h| + share) + C：plus_le_compat（Hquad + refl） *)
          apply (real_le_plus_compat
                   (real_mult (real_mult t t) (real_plus real_one real_one))
                   (real_plus (real_mult (real_mult two_inv eps) (real_abs h)) share)
                   (real_plus (real_plus share (real_plus share share)) share)
                   (real_plus (real_plus share (real_plus share share)) share)).
          * exact Hquad.
          * apply real_le_refl.
        + (* ((eps/2)|h| + share) + C == (eps/2)|h| + (share + C)：assoc 反向 *)
          apply RealSetoid.real_eq_le.
          apply real_eq_sym.
          apply (real_plus_assoc (real_mult (real_mult two_inv eps) (real_abs h))
                                 share
                                 (real_plus (real_plus share (real_plus share share)) share)).
    }
    (* 汇总 3：最终 (eps/2)|h| + 5share ≤ eps|h| + eps'——Bishop 逐点（Or 编码无法表达通用非严格 ≤，E152-5）。
       逐点差分 = (eps_n/2)|h_n| + (3/8)eps'_n ≥ (3/8)eps'_n > (3/8)e0' > 0（见证 (3/8)·e0'） *)
    assert (Hfinal : real_le
      (real_plus (real_mult (real_mult two_inv eps) (real_abs h))
                 (real_plus share (real_plus (real_plus share (real_plus share share)) share)))
      (real_plus (real_mult eps (real_abs h)) eps')).
    {
      destruct real_two_pos_local as [e2 [He2 [N2 HN2]]].
      destruct Heps as [e0 [He0 [N0 HN0]]].
      destruct Heps' as [e0' [He0' [N0' HN0']]].
      set (eps0q := Qmult (Qmake 3 8) e0').
      assert (Heps0q : QltT 0 eps0q).
      { apply Qlt_to_QltT. unfold eps0q.
        apply (Qmult_lt_0_compat (Qmake 3 8) e0').
        - (* 0 < 3/8：0·8 < 3·1 *)
          simpl. reflexivity.
        - apply QltT_to_Qlt. exact He0'. }
      apply (RealSetoid.real_lt_le_iff_req _ _). left.
      unfold real_lt.
      exists eps0q.
      split.
      - exact Heps0q.
      - exists (Nat.max N0' (Nat.max N2 N0)).
        intros n Hn.
        apply NatLe_drop in Hn.
        assert (Hn0' : (N0' <= n)%nat) by lia.
        assert (Hn2 : (N2 <= n)%nat) by lia.
        assert (Hn0 : (N0 <= n)%nat) by lia.
        set (hn := projT1 h n).
        set (en := projT1 eps n).
        set (en' := projT1 eps' n).
        set (inv2n := projT1 two_inv n).
        set (inv8n := projT1 eight_inv n).
        (* 展开断言 *)
        assert (Hinv2 : inv2n == Qinv 2).
        { unfold inv2n, two_inv.
          cbn [real_inv_pos real_plus real_one projT1].
          assert (Hl : Nat.leb N2 n = true) by (apply Nat.leb_le; exact Hn2).
          rewrite Hl. reflexivity. }
        assert (Hinv8 : inv8n == Qinv 8).
        { unfold inv8n, eight_inv, four_inv, two_inv.
          cbn [real_inv_pos real_plus real_one projT1 real_mult].
          assert (Hl : Nat.leb N2 n = true) by (apply Nat.leb_le; exact Hn2).
          rewrite Hl. unfold Qdiv. field. }
        assert (Heps0'n : Qlt e0' en').
        { apply (Qlt_le_trans _ (en' - projT1 real_zero n) _).
          - apply QltT_to_Qlt. exact (HN0' n (NatLe_lift _ _ Hn0')).
          - apply qeq_le.
            assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
            rewrite Hz. ring. }
        assert (Heps0n : Qlt e0 en).
        { apply (Qlt_le_trans _ (en - projT1 real_zero n) _).
          - apply QltT_to_Qlt. exact (HN0 n (NatLe_lift _ _ Hn0)).
          - apply qeq_le.
            assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
            rewrite Hz. ring. }
        (* A_n、B_n 投影展开 *)
        assert (HA : projT1
          (real_plus (real_mult (real_mult two_inv eps) (real_abs h))
                     (real_plus share (real_plus (real_plus share (real_plus share share)) share))) n
          == (inv2n * en) * Qabs hn + (inv8n * en' + (inv8n * en' + (inv8n * en' + (inv8n * en' + inv8n * en'))))).
        { setoid_rewrite (real_plus_proj (real_mult (real_mult two_inv eps) (real_abs h))
                                         (real_plus share (real_plus (real_plus share (real_plus share share)) share)) n).
          setoid_rewrite (real_mult_proj (real_mult two_inv eps) (real_abs h) n).
          setoid_rewrite (real_mult_proj two_inv eps n).
          setoid_rewrite (real_abs_proj h n).
          setoid_rewrite (real_plus_proj share (real_plus (real_plus share (real_plus share share)) share) n).
          setoid_rewrite (real_plus_proj (real_plus share (real_plus share share)) share n).
          setoid_rewrite (real_plus_proj share (real_plus share share) n).
          setoid_rewrite (real_plus_proj share share n).
          unfold share.
          setoid_rewrite (real_mult_proj eight_inv eps' n).
          unfold eight_inv.
          setoid_rewrite (real_mult_proj four_inv two_inv n).
          unfold four_inv.
          setoid_rewrite (real_mult_proj two_inv two_inv n).
          unfold hn, en, en', inv2n, inv8n.
          unfold share, eight_inv, four_inv, two_inv.
          cbn [projT1 real_inv_pos real_plus real_one real_mult real_abs].
          assert (Hl : Nat.leb N2 n = true) by (apply Nat.leb_le; exact Hn2).
          rewrite Hl.
          set (aq := Qabs (projT1 h n)). unfold Qdiv. field. }
        (* 主链：eps0q < B_n − A_n *)
        apply Qlt_to_QltT.
        apply (Qlt_le_trans _ ((en / 2) * Qabs hn + (Qmake 3 8) * en') _).
        { (* eps0q < (en/2)|hn| + (3/8)en' *)
          apply (Qlt_le_trans _ ((Qmake 3 8) * en') _).
          { (* (3/8)e0' < (3/8)en'：en' > e0'，mult_lt_l *)
            unfold eps0q.
            assert (H38 : Qlt 0 (Qmake 3 8)) by (simpl; reflexivity).
            apply (proj2 (Qmult_lt_l e0' en' (Qmake 3 8) H38)).
            exact Heps0'n. }
          { (* (3/8)en' ≤ (en/2)|hn| + (3/8)en'：0 ≤ (en/2)|hn| *)
            apply (Qle_trans ((Qmake 3 8) * en')
                             ((Qmake 3 8) * en' + (en / 2) * Qabs hn)
                             ((en / 2) * Qabs hn + (Qmake 3 8) * en')).
            { apply (Qle_plus_nonneg_r ((Qmake 3 8) * en') ((en / 2) * Qabs hn)).
              apply (Qmult_le_compat_nonneg 0 (en / 2) 0 (Qabs hn)).
              { split. apply Qle_refl.
                apply (Qmult_le_compat_nonneg 0 en 0 (Qinv 2)).
                { split. apply Qle_refl. apply Qlt_le_weak. apply (Qlt_trans 0 e0 en). apply QltT_to_Qlt. exact He0. exact Heps0n. }
                { split. apply Qle_refl. apply Qlt_le_weak. simpl. reflexivity. } }
              { split. apply Qle_refl. apply Qabs_nonneg. } }
            { apply qeq_le. apply (Qplus_comm ((Qmake 3 8) * en') ((en / 2) * Qabs hn)). } }
          }
        { (* (en/2)|hn| + (3/8)en' ≤ B_n − A_n：展开 + field *)
          apply qeq_le.
          (* B_n 展开 *)
          assert (HB : projT1 (real_plus (real_mult eps (real_abs h)) eps') n == en * Qabs hn + en').
          { setoid_rewrite (real_plus_proj (real_mult eps (real_abs h)) eps' n).
            setoid_rewrite (real_mult_proj eps (real_abs h) n).
            setoid_rewrite (real_abs_proj h n).
            cbn [projT1]. unfold hn, en, en'. ring. }
          (* 主链：M == B_n − A_n *)
          apply (Qeq_trans ((en / 2) * Qabs hn + (Qmake 3 8) * en')
                           ((en * Qabs hn + en') - ((inv2n * en) * Qabs hn + (inv8n * en' + (inv8n * en' + (inv8n * en' + (inv8n * en' + inv8n * en'))))))
                           (projT1 (real_plus (real_mult eps (real_abs h)) eps') n - projT1
                             (real_plus (real_mult (real_mult two_inv eps) (real_abs h))
                                        (real_plus share (real_plus (real_plus share (real_plus share share)) share))) n)).
          - (* M == 展开形态：rewrite Hinv2/Hinv8 + field *)
            rewrite Hinv2. rewrite Hinv8.
            unfold Qdiv. field.
          - (* 展开形态 == B_n − A_n：plus_comp（HB + HA 反向） *)
            apply (Qplus_comp (en * Qabs hn + en') (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                              (Qeq_sym _ _ HB)
                              (Qopp ((inv2n * en) * Qabs hn + (inv8n * en' + (inv8n * en' + (inv8n * en' + (inv8n * en' + inv8n * en'))))))
                              (Qopp (projT1 (real_plus (real_mult (real_mult two_inv eps) (real_abs h))
                                                       (real_plus share (real_plus (real_plus share (real_plus share share)) share))) n))
                              (Qopp_comp ((inv2n * en) * Qabs hn + (inv8n * en' + (inv8n * en' + (inv8n * en' + (inv8n * en' + inv8n * en')))))
                                         (projT1 (real_plus (real_mult (real_mult two_inv eps) (real_abs h))
                                                            (real_plus share (real_plus (real_plus share (real_plus share share)) share))) n)
                                         (Qeq_sym _ _ HA))).
        }
    }
    (* 组装 *)
    apply (real_le_trans _ (real_plus (real_mult (real_mult two_inv eps) (real_abs h))
                                      (real_plus share (real_plus (real_plus share (real_plus share share)) share))) _).
    { apply (real_le_trans _ (real_plus (real_plus (real_mult (real_mult t t) (real_plus real_one real_one))
                                                   (real_plus share (real_plus share share)))
                                        share) _).
      - exact HabsD.
      - exact Hmid. }
    { exact Hfinal. }
Defined.
(* ============================================================ *)
(* J2 b5dJ_LogErr_delta_exp（Defined 透明）                      *)
(* 拷贝源：213 根 b5f_LogErr_delta（ConstructiveWorld.v          *)
(*   L82585–82641，57 行，机器抽取零手抄）；语句不变。            *)
(* 三改：① Lemma 头改名 ② 体内 destruct 源 b5f_log_diff_dx →    *)
(*   本文件 J1 b5dJ_log_diff_dx_exp（同参数调用：x0 := b5f_u x） *)
(*   ③ 收尾 Qed→Defined。                                        *)
(* ============================================================ *)
Lemma b5dJ_LogErr_delta_exp : forall (x : Real) (epsL : Real) (HepsL : real_lt real_zero epsL),
  sigT (fun delta : Real => And (real_lt real_zero delta)
    (forall (h : Real), forall (epsL' : Real), real_lt real_zero epsL' ->
      real_lt (real_abs (b5f_Du x h)) delta ->
      real_le (real_abs (b5f_LogErr x h))
              (real_plus (real_mult epsL (real_abs (b5f_Du x h))) epsL'))).
Proof.
  intros x epsL HepsL.
  destruct (b5dJ_log_diff_dx_exp (b5f_u x) (b5a_one_plus_sq_pos x) epsL HepsL) as [delta [Hd0 Hd]].
  exists delta. split.
  - exact Hd0.
  - intros h epsL' HepsL' HhΔ.
    set (logexpr := real_plus
             (real_log (real_plus (b5f_u x) (b5f_Du x h)) (b5f_u_plus_Du_pos x h))
             (real_opp (real_plus (real_log (b5f_u x) (b5a_one_plus_sq_pos x))
                        (real_mult (real_inv_pos (b5f_u x) (b5a_one_plus_sq_pos x))
                                   (b5f_Du x h))))).
    assert (Hraw : real_le (real_abs logexpr)
                   (real_plus (real_mult epsL (real_abs (b5f_Du x h))) epsL')).
    { unfold logexpr.
      exact (Hd (b5f_Du x h) HhΔ (b5f_u_plus_Du_pos x h) epsL' HepsL'). }
    (* logexpr == b5f_LogErr：仅首个 log 参数/证书不同 → real_log_wd 桥 *)
    assert (Heq : real_eq logexpr (b5f_LogErr x h)).
    { unfold logexpr, b5f_LogErr.
      apply (real_eq_trans
        (real_plus (real_log (real_plus (b5f_u x) (b5f_Du x h)) (b5f_u_plus_Du_pos x h))
                   (real_opp (real_plus (real_log (b5f_u x) (b5a_one_plus_sq_pos x))
                              (real_mult (real_inv_pos (b5f_u x) (b5a_one_plus_sq_pos x))
                                         (b5f_Du x h)))))
        (real_plus (real_log (b5f_u (real_plus x h)) (b5a_one_plus_sq_pos (real_plus x h)))
                   (real_opp (real_plus (real_log (b5f_u x) (b5a_one_plus_sq_pos x))
                              (real_mult (real_inv_pos (b5f_u x) (b5a_one_plus_sq_pos x))
                                         (b5f_Du x h)))))
        (real_plus (real_log (b5f_u (real_plus x h)) (b5a_one_plus_sq_pos (real_plus x h)))
                   (real_opp (real_plus (real_log (b5f_u x) (b5a_one_plus_sq_pos x))
                              (real_mult (b5a_atan_d x) (b5f_Du x h)))))).
      - apply (RealSetoid.real_eq_plus_compat
          (real_log (real_plus (b5f_u x) (b5f_Du x h)) (b5f_u_plus_Du_pos x h))
          (real_opp (real_plus (real_log (b5f_u x) (b5a_one_plus_sq_pos x))
                     (real_mult (real_inv_pos (b5f_u x) (b5a_one_plus_sq_pos x))
                                (b5f_Du x h))))
          (real_log (b5f_u (real_plus x h)) (b5a_one_plus_sq_pos (real_plus x h)))
          (real_opp (real_plus (real_log (b5f_u x) (b5a_one_plus_sq_pos x))
                     (real_mult (real_inv_pos (b5f_u x) (b5a_one_plus_sq_pos x))
                                (b5f_Du x h))))).
        + apply (real_log_wd (real_plus (b5f_u x) (b5f_Du x h)) (b5f_u (real_plus x h))
                   (b5f_u_plus_Du_pos x h) (b5a_one_plus_sq_pos (real_plus x h))).
          exact (b5f_u_Du_eq x h).
        + apply real_eq_refl.
      - unfold b5a_atan_d, b5f_u. apply real_eq_refl. }
    apply (real_le_trans (real_abs (b5f_LogErr x h)) (real_abs logexpr)
                         (real_plus (real_mult epsL (real_abs (b5f_Du x h))) epsL')).
    + apply RealSetoid.real_eq_le.
      apply (real_abs_eq_compat (b5f_LogErr x h) logexpr).
      apply real_eq_sym. exact Heq.
    + exact Hraw.
Defined.

(* ============================================================ *)
(* end sc2_b5a_item20.v · F1 透明链 exp/log 支链头两件 *)
(* ============================================================ *)

(* ============================================================ *)
(* 块 item7（前缀 b5d3_——主件 b5d3_exp_arch4_explicit）——来源：演变/.ablation/sc2_parallel/sc2_b5a_ode/sc2_b5a_item7.v。 *)
(* ============================================================ *)

(* ============================================================ *)
(* §0 小工具（Q 层正性证书，δB-2 闭式见证用）                   *)
(* ============================================================ *)

Lemma b5d3_Hq_half : Qlt 0 (1 # 2).
Proof. unfold Qlt. simpl. lia.
Qed.

Lemma b5d3_Hq_four : Qlt 0 (1 # 4).
Proof. unfold Qlt. simpl. lia.
Qed.

Lemma b5d3_Hq_two : Qlt 0 2.
Proof. unfold Qlt. simpl. lia.
Qed.

Lemma b5d3_Hq_four_ge : Qle 0 (1 # 4).
Proof. unfold Qle. simpl. lia.
Qed.

Lemma b5d3_Hq_half_ge : Qle 0 (1 # 2).
Proof. unfold Qle. simpl. lia.
Qed.

(* ============================================================ *)
(* §1 δB-1：b5d3_exp_arch4_explicit（C4 闭式件，Set 层 sigT）   *)
(* ============================================================ *)
(* 闭值（N0 := 11 版，满足 ≤ 55；≈54.76）：                       *)
(*   C := exp_series 11 4 + 2·(4^11/11!)                          *)
(* 尾条件：exp_tail_abs_geom2 A m n 需 ∀t≥m, 2A ≤ t+1 ——          *)
(*   A := 4、m := 11：8 ≤ t+1（t ≥ 11）由 lia 逐点验证。          *)
(* 证明同构根 exp_series_arch（L8067–8106）换显式 N0 := 11。      *)
(* ⚠️ 数值校正记录：报告建议 N0 := 7 闭值 es 7 4 + 2·(4^7/7!)     *)
(*   ≈ 58.31 > 55（报告 ≈54.8 系笔误——es 7 4 ≈ 51.81、           *)
(*   (4^7/7!)·2 ≈ 6.50）⇒ 55 分量不可用 N0 := 7；本件取 N0 := 11  *)
(*   （es 11 4 ≈ 54.55、(4^11/11!)·2 ≈ 0.210 ⇒ C ≈ 54.76 ≤ 55 ✓）。*)

Definition b5d3_exp_arch4_C : Q :=
  exp_series 11 4 + (q_pow 4 11 / q_fact 11) * (1 + 1)%Q.

(* 1 ≤ C（符号，Qed） *)
Lemma b5d3_exp_arch4_C_ge1 : QleT' 1 b5d3_exp_arch4_C.
Proof.
  apply Qle_to_QleT'.
  unfold b5d3_exp_arch4_C.
  apply (Qle_trans _ (exp_series 11 4) _).
  - setoid_replace 1 with (exp_series 0 4) by reflexivity.
    apply exp_series_mono.
    + unfold Qle. simpl. lia.
    + lia.
  - apply (Qle_plus_nonneg_r (exp_series 11 4) ((q_pow 4 11 / q_fact 11) * (1 + 1)%Q)).
    apply q_pow_fact2_nonneg. unfold Qle. simpl. lia.
Qed.

(* ∀j, es j 4 ≤ C（符号，N0 := 11 分拆；Qed） *)
Lemma b5d3_exp_arch4_C_all : forall j : nat, QleT' (exp_series j 4) b5d3_exp_arch4_C.
Proof.
  intro j.
  apply Qle_to_QleT'.
  destruct (Nat.leb j 11) eqn:E.
  - apply Nat.leb_le in E.
    apply (Qle_trans _ (exp_series 11 4) _).
    + apply exp_series_mono; [unfold Qle; simpl; lia | exact E].
    + unfold b5d3_exp_arch4_C.
      apply (Qle_plus_nonneg_r (exp_series 11 4) ((q_pow 4 11 / q_fact 11) * (1 + 1)%Q)).
      apply q_pow_fact2_nonneg. unfold Qle. simpl. lia.
  - apply Nat.leb_gt in E.
    apply (Qle_trans _ (exp_series 11 4 + (q_pow 4 11 / q_fact 11) * (1 + 1)%Q) _).
    + apply (Qle_trans _ (exp_series 11 4 + exp_tail_abs 11 j 4) _).
      * apply Qle_minus_iff.
        setoid_replace (exp_series 11 4 + exp_tail_abs 11 j 4 + - exp_series j 4)
          with (exp_tail_abs 11 j 4 - (exp_series j 4 - exp_series 11 4)) by ring.
        setoid_replace (exp_tail_abs 11 j 4 - (exp_series j 4 - exp_series 11 4))
          with (exp_tail_abs 11 j 4 + - (exp_series j 4 - exp_series 11 4)) by ring.
        apply (proj1 (Qle_minus_iff (exp_series j 4 - exp_series 11 4) (exp_tail_abs 11 j 4))).
        apply (exp_series_tail_le 4 11 j). unfold Qle. simpl. lia. lia.
      * apply (Qplus_le_compat _ _ _ _); [apply Qle_refl | apply (exp_tail_abs_geom2 4 11 j)].
        -- unfold Qle. simpl. lia.
        -- intros u Hu. unfold Qle. simpl. lia.
        -- lia.
    + unfold b5d3_exp_arch4_C. apply Qle_refl.
Qed.

(* C ≤ 55（闭值数值验证：vm_compute 直算；Qed） *)
Lemma b5d3_exp_arch4_C_le55 : QleT' b5d3_exp_arch4_C 55.
Proof.
  apply Qle_to_QleT'.
  vm_compute.
  discriminate.
Qed.

(* 主件（Defined ⇒ 见证可计算：destruct 得闭值 b5d3_exp_arch4_C） *)
Lemma b5d3_exp_arch4_explicit :
  sigT (fun C : Q => And (QleT' 1 C)
    (And (forall j : nat, QleT' (exp_series j 4) C) (QleT' C 55))).
Proof.
  exists b5d3_exp_arch4_C.
  split.
  - exact b5d3_exp_arch4_C_ge1.
  - split.
    + exact b5d3_exp_arch4_C_all.
    + exact b5d3_exp_arch4_C_le55.
Defined.

(* ---- 报告值公式 companion：C7 := es 7 4 + 2·(4^7/7!)（≈58.31，   *)
(*      无 ≤55 分量——该值下 C ≤ 55 为假）。N0 := 7 分拆。           *)

Definition b5d3_exp_arch4_C7 : Q :=
  exp_series 7 4 + (q_pow 4 7 / q_fact 7) * (1 + 1)%Q.

Lemma b5d3_exp_arch4_C7_ge1 : QleT' 1 b5d3_exp_arch4_C7.
Proof.
  apply Qle_to_QleT'.
  unfold b5d3_exp_arch4_C7.
  apply (Qle_trans _ (exp_series 7 4) _).
  - setoid_replace 1 with (exp_series 0 4) by reflexivity.
    apply exp_series_mono.
    + unfold Qle. simpl. lia.
    + lia.
  - apply (Qle_plus_nonneg_r (exp_series 7 4) ((q_pow 4 7 / q_fact 7) * (1 + 1)%Q)).
    apply q_pow_fact2_nonneg. unfold Qle. simpl. lia.
Qed.

Lemma b5d3_exp_arch4_C7_all : forall j : nat, QleT' (exp_series j 4) b5d3_exp_arch4_C7.
Proof.
  intro j.
  apply Qle_to_QleT'.
  destruct (Nat.leb j 7) eqn:E.
  - apply Nat.leb_le in E.
    apply (Qle_trans _ (exp_series 7 4) _).
    + apply exp_series_mono; [unfold Qle; simpl; lia | exact E].
    + unfold b5d3_exp_arch4_C7.
      apply (Qle_plus_nonneg_r (exp_series 7 4) ((q_pow 4 7 / q_fact 7) * (1 + 1)%Q)).
      apply q_pow_fact2_nonneg. unfold Qle. simpl. lia.
  - apply Nat.leb_gt in E.
    apply (Qle_trans _ (exp_series 7 4 + (q_pow 4 7 / q_fact 7) * (1 + 1)%Q) _).
    + apply (Qle_trans _ (exp_series 7 4 + exp_tail_abs 7 j 4) _).
      * apply Qle_minus_iff.
        setoid_replace (exp_series 7 4 + exp_tail_abs 7 j 4 + - exp_series j 4)
          with (exp_tail_abs 7 j 4 - (exp_series j 4 - exp_series 7 4)) by ring.
        setoid_replace (exp_tail_abs 7 j 4 - (exp_series j 4 - exp_series 7 4))
          with (exp_tail_abs 7 j 4 + - (exp_series j 4 - exp_series 7 4)) by ring.
        apply (proj1 (Qle_minus_iff (exp_series j 4 - exp_series 7 4) (exp_tail_abs 7 j 4))).
        apply (exp_series_tail_le 4 7 j). unfold Qle. simpl. lia. lia.
      * apply (Qplus_le_compat _ _ _ _); [apply Qle_refl | apply (exp_tail_abs_geom2 4 7 j)].
        -- unfold Qle. simpl. lia.
        -- intros u Hu. unfold Qle. simpl. lia.
        -- lia.
    + unfold b5d3_exp_arch4_C7. apply Qle_refl.
Qed.

Lemma b5d3_exp_arch4_C7_explicit :
  sigT (fun C : Q => And (QleT' 1 C) (forall j : nat, QleT' (exp_series j 4) C)).
Proof.
  exists b5d3_exp_arch4_C7.
  split.
  - exact b5d3_exp_arch4_C7_ge1.
  - exact b5d3_exp_arch4_C7_all.
Defined.

(* ============================================================ *)
(* §2 δB-2：b5d3_exp_minus_one_linear_closed（Real 层闭式副本） *)
(* ============================================================ *)
(* 根 exp_minus_one_linear（L48334–48533）逐字复制；语句换为       *)
(* 首分量 real_eq delta (real_min (real_const (1#2))              *)
(*                           (real_mult eps (real_const (1#4))))，*)
(* 两处 two_inv/four_inv 展开改写为 real_const（闭式直写）；        *)
(* real_inv_proj(Ni) 机制删除（real_const 投影 real_const_proj 直  *)
(* 算，Qinv 2 与 (1#2) 定义性相等）；N-merge 去掉 Ni 项。          *)
Lemma b5d3_exp_minus_one_linear_closed : forall (eps : Real), real_lt real_zero eps ->
  sigT (fun delta : Real =>
    And (real_eq delta (real_min (real_const (1 # 2)) (real_mult eps (real_const (1 # 4)))))
        (And (real_lt real_zero delta)
             (forall h : Real, real_lt (real_abs h) delta ->
               forall (eps' : Real), real_lt real_zero eps' ->
               real_le (real_abs (real_plus (real_plus (cauchy_real_exp h) (real_opp real_one)) (real_opp h)))
                       (real_plus (real_mult eps (real_abs h)) eps')))).
Proof.
  intros eps Heps.
  set (delta := real_min (real_const (1 # 2)) (real_mult eps (real_const (1 # 4)))).
  exists delta.
  split.
  - (* real_eq delta (real_min (real_const (1#2)) (real_mult eps (real_const (1#4)))) *)
    unfold delta. apply real_eq_refl.
  - split.
    + (* 0 < delta *)
      unfold delta.
      apply real_min_pos.
      * apply real_const_pos_f1. exact b5d3_Hq_half.
      * apply real_mult_positive.
        -- exact Heps.
        -- apply real_const_pos_f1. exact b5d3_Hq_four.
    + intros h Hh eps' Heps'.
      assert (Hh_half : real_lt (real_abs h) (real_const (1 # 2)))
        by (unfold delta in Hh; apply (real_min_lt_l h (real_const (1 # 2)) (real_mult eps (real_const (1 # 4)))); exact Hh).
      assert (Hh_eps4 : real_lt (real_abs h) (real_mult eps (real_const (1 # 4))))
        by (unfold delta in Hh; apply (real_min_lt_r h (real_const (1 # 2)) (real_mult eps (real_const (1 # 4)))); exact Hh).
      (* real_le 左分支：real_lt 构造 *)
      left.
      destruct Heps as [eps1 [Heps1 [N1 HN1]]].
      destruct Heps' as [eps1' [Heps1' [N1' HN1']]].
      destruct Hh_half as [eps2 [Heps2 [N2 HN2]]].
      destruct Hh_eps4 as [eps3 [Heps3 [N3 HN3]]].
      exists eps1'.
      split.
      * exact Heps1'.
      * exists (Nat.max (Nat.max (Nat.max N1 N1') (Nat.max N2 N3)) 2).
        intros n Hn.
        apply NatLe_drop in Hn.
        set (en := projT1 eps n). set (en' := projT1 eps' n). set (hn := projT1 h n).
        (* 逐点展开 A、B *)
        assert (HA : projT1 (real_abs (real_plus (real_plus (cauchy_real_exp h) (real_opp real_one)) (real_opp h))) n ==
                      Qabs (exp_partial n hn - 1 - hn)).
        { unfold hn.
          setoid_rewrite (real_abs_proj (real_plus (real_plus (cauchy_real_exp h) (real_opp real_one)) (real_opp h)) n).
          setoid_rewrite (real_plus_proj (real_plus (cauchy_real_exp h) (real_opp real_one)) (real_opp h) n).
          setoid_rewrite (real_plus_proj (cauchy_real_exp h) (real_opp real_one) n).
          setoid_rewrite (real_opp_proj real_one n).
          setoid_rewrite (real_opp_proj h n).
          rewrite (real_exp_proj h n).
          cbn [projT1 real_one].
          unfold Qminus. ring. }
        assert (HB : projT1 (real_plus (real_mult eps (real_abs h)) eps') n == en * Qabs hn + en').
        { unfold en, en', hn.
          setoid_rewrite (real_plus_proj (real_mult eps (real_abs h)) eps' n).
          setoid_rewrite (real_mult_proj eps (real_abs h) n).
          setoid_rewrite (real_abs_proj h n).
          cbn [projT1]. ring. }
        (* 逐点界 1：|hn| < 1/2（Hh_half 见证 + real_const (1#2) 投影） *)
        assert (Hn2 : (N2 <= n)%nat) by lia.
        assert (Hn3 : (N3 <= n)%nat) by lia.
        assert (Hn1 : (N1 <= n)%nat) by lia.
        assert (Hn1' : (N1' <= n)%nat) by lia.
        assert (HN2q : Qlt eps2 (Qminus (Qinv 2) (Qabs hn))).
        { apply (Qlt_le_trans eps2 (Qminus (projT1 (real_const (1 # 2)) n) (projT1 (real_abs h) n)) (Qminus (Qinv 2) (Qabs hn))).
          - apply QltT_to_Qlt. exact (HN2 n (NatLe_lift _ _ Hn2)).
          - apply qeq_le.
            rewrite (real_abs_proj h n).
            rewrite (real_const_proj (1 # 2) n).
            reflexivity. }
        assert (Hhn_half : Qlt (Qabs hn) (Qinv 2)).
        { apply (Qlt_le_trans (Qabs hn) (Qminus (Qinv 2) eps2) (Qinv 2)).
          - apply (q_lt_minus_shift eps2 (Qinv 2) (Qabs hn)). exact HN2q.
          - assert (Heps2q : Qle 0 eps2).
            { apply Qlt_le_weak. apply QltT_to_Qlt. exact Heps2. }
            apply (Qle_trans (Qminus (Qinv 2) eps2) (Qplus (Qminus (Qinv 2) eps2) eps2) (Qinv 2)).
            + apply (Qle_trans (Qminus (Qinv 2) eps2) (Qplus (Qminus (Qinv 2) eps2) 0) (Qplus (Qminus (Qinv 2) eps2) eps2)).
              * apply qeq_le. ring.
              * apply (Qplus_le_compat (Qminus (Qinv 2) eps2) (Qminus (Qinv 2) eps2) 0 eps2 (Qle_refl _) Heps2q).
            + apply qeq_le. ring. }
        (* 逐点界 2：|hn| < en/4（Hh_eps4 见证 + eps·real_const (1#4) 投影） *)
        assert (HN3q : Qlt eps3 (Qminus (Qmult en (Qmult (Qinv 2) (Qinv 2))) (Qabs hn))).
        { apply (Qlt_le_trans eps3 (Qminus (projT1 (real_mult eps (real_const (1 # 4))) n) (projT1 (real_abs h) n))
                                  (Qminus (Qmult en (Qmult (Qinv 2) (Qinv 2))) (Qabs hn))).
          - apply QltT_to_Qlt. exact (HN3 n (NatLe_lift _ _ Hn3)).
          - apply qeq_le.
            rewrite (real_abs_proj h n).
            unfold en.
            setoid_rewrite (real_mult_proj eps (real_const (1 # 4)) n).
            rewrite (real_const_proj (1 # 4) n).
            cbn [projT1 real_const].
            reflexivity. }
        assert (Hhn_eps4 : Qlt (Qabs hn) (Qmult en (Qmult (Qinv 2) (Qinv 2)))).
        { apply (Qlt_le_trans (Qabs hn) (Qminus (Qmult en (Qmult (Qinv 2) (Qinv 2))) eps3)
                              (Qmult en (Qmult (Qinv 2) (Qinv 2)))).
          - apply (q_lt_minus_shift eps3 (Qmult en (Qmult (Qinv 2) (Qinv 2))) (Qabs hn)). exact HN3q.
          - assert (Heps3q : Qle 0 eps3).
            { apply Qlt_le_weak. apply QltT_to_Qlt. exact Heps3. }
            apply (Qle_trans (Qminus (Qmult en (Qmult (Qinv 2) (Qinv 2))) eps3)
                             (Qplus (Qminus (Qmult en (Qmult (Qinv 2) (Qinv 2))) eps3) eps3)
                             (Qmult en (Qmult (Qinv 2) (Qinv 2)))).
            + apply (Qle_trans (Qminus (Qmult en (Qmult (Qinv 2) (Qinv 2))) eps3)
                               (Qplus (Qminus (Qmult en (Qmult (Qinv 2) (Qinv 2))) eps3) 0)
                               (Qplus (Qminus (Qmult en (Qmult (Qinv 2) (Qinv 2))) eps3) eps3)).
              * apply qeq_le. ring.
              * apply (Qplus_le_compat (Qminus (Qmult en (Qmult (Qinv 2) (Qinv 2))) eps3)
                                       (Qminus (Qmult en (Qmult (Qinv 2) (Qinv 2))) eps3) 0 eps3 (Qle_refl _) Heps3q).
            + apply qeq_le. ring. }
        (* 主链：B_n − A_n ≥ eps1' *)
        assert (Hquad : Qle (Qabs (exp_partial n hn - 1 - hn))
                            (Qmult (Qmult (Qabs hn) (Qabs hn)) (3 # 2))).
        { apply (exp_partial_linear_quad hn n).
          - lia.
          - (* 2|hn| ≤ 3：从 |hn| < 1/2 *)
            apply (Qlt_le_weak (Qmult (1 + 1)%Q (Qabs hn)) 3%Q).
            apply (Qlt_trans (Qmult (1 + 1)%Q (Qabs hn)) (Qmult (1 + 1)%Q (Qinv 2)) 3%Q).
            + setoid_rewrite (Qmult_comm (1 + 1)%Q (Qabs hn)).
              setoid_rewrite (Qmult_comm (1 + 1)%Q (Qinv 2)).
              apply (Qmult_lt_compat_r (Qabs hn) (Qinv 2) (1 + 1)%Q).
              * unfold Qlt. simpl. lia.
              * exact Hhn_half.
            + unfold Qlt. simpl. lia. }
        assert (Hq2 : Qle (Qmult (Qmult (Qabs hn) (Qabs hn)) (3 # 2))
                          (Qmult (Qmult en (Qabs hn)) (3 # 8))).
        { assert (Hhn_le : Qle (Qabs hn) (Qmult en (Qmult (Qinv 2) (Qinv 2)))).
          { apply Qlt_le_weak. exact Hhn_eps4. }
          apply (Qle_trans (Qmult (Qmult (Qabs hn) (Qabs hn)) (3 # 2))
                           (Qmult (Qmult (Qmult en (Qmult (Qinv 2) (Qinv 2))) (Qabs hn)) (3 # 2))
                           (Qmult (Qmult en (Qabs hn)) (3 # 8))).
          - (* |hn|² ≤ (en/4)·|hn|，乘 (3/2) *)
            apply (Qmult_le_compat_r (Qmult (Qabs hn) (Qabs hn))
                                     (Qmult (Qmult en (Qmult (Qinv 2) (Qinv 2))) (Qabs hn))
                                     (3 # 2)).
            + apply (Qmult_le_compat_r (Qabs hn) (Qmult en (Qmult (Qinv 2) (Qinv 2))) (Qabs hn)).
              * exact Hhn_le.
              * apply Qabs_nonneg.
            + unfold Qle. simpl. lia.
          - apply qeq_le. field. }
        assert (Hq3 : Qle (Qmult (Qmult en (Qabs hn)) (3 # 8)) (Qmult en (Qabs hn))).
        { setoid_rewrite (Qmult_comm (Qmult en (Qabs hn)) (3 # 8)).
          apply (Qle_trans (Qmult (3 # 8) (Qmult en (Qabs hn))) (Qmult 1%Q (Qmult en (Qabs hn))) (Qmult en (Qabs hn))).
          - apply (Qmult_le_compat_r (3 # 8) 1%Q (Qmult en (Qabs hn))).
            + unfold Qle. simpl. lia.
            + assert (HN1e : QltT eps1 en).
              { apply Qlt_to_QltT.
                apply (Qlt_le_trans eps1 (Qminus (projT1 eps n) (projT1 real_zero n)) en).
                - apply QltT_to_Qlt. exact (HN1 n (NatLe_lift _ _ Hn1)).
                - apply qeq_le. cbn [real_zero real_const projT1]. unfold en. ring. }
              assert (Henq : Qle 0 en).
              { apply Qlt_le_weak. apply (Qlt_trans 0 eps1 en).
                - apply QltT_to_Qlt. exact Heps1.
                - apply QltT_to_Qlt. exact HN1e. }
              apply (Qmult_le_0_compat en (Qabs hn) Henq (Qabs_nonneg hn)).
          - apply qeq_le. ring. }
        assert (Hmain : Qle (Qabs (exp_partial n hn - 1 - hn)) (Qmult en (Qabs hn))).
        { apply (Qle_trans _ (Qmult (Qmult (Qabs hn) (Qabs hn)) (3 # 2)) _).
          - exact Hquad.
          - apply (Qle_trans _ (Qmult (Qmult en (Qabs hn)) (3 # 8)) _).
            + exact Hq2.
            + exact Hq3. }
        (* eps1' < B_n − A_n：eps1' < en' ≤ B_n − A_n *)
        assert (Heps1e : QltT eps1' en').
        { apply Qlt_to_QltT.
          apply (Qlt_le_trans eps1' (Qminus (projT1 eps' n) (projT1 real_zero n)) en').
          - apply QltT_to_Qlt. exact (HN1' n (NatLe_lift _ _ Hn1')).
          - apply qeq_le. cbn [real_zero real_const projT1]. unfold en'. ring. }
        assert (Hrepl : Qeq (Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                                    (projT1 (real_abs (real_plus (real_plus (cauchy_real_exp h) (real_opp real_one)) (real_opp h))) n))
                            (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qabs (exp_partial n hn - 1 - hn)))).
        { apply (Qminus_comp (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                             (Qplus (Qmult en (Qabs hn)) en') HB
                             (projT1 (real_abs (real_plus (real_plus (cauchy_real_exp h) (real_opp real_one)) (real_opp h))) n)
                             (Qabs (exp_partial n hn - 1 - hn)) HA). }
        assert (Henle : Qle en' (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qabs (exp_partial n hn - 1 - hn)))).
        { apply (Qle_trans en' (Qplus en' (Qminus (Qmult en (Qabs hn)) (Qabs (exp_partial n hn - 1 - hn))))
                             (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qabs (exp_partial n hn - 1 - hn)))).
          - apply (Qle_trans en' (Qplus en' 0) (Qplus en' (Qminus (Qmult en (Qabs hn)) (Qabs (exp_partial n hn - 1 - hn))))).
            + apply qeq_le. ring.
            + apply (Qplus_le_compat en' en' 0 (Qminus (Qmult en (Qabs hn)) (Qabs (exp_partial n hn - 1 - hn)))
                                     (Qle_refl en')
                                     (proj1 (Qle_minus_iff (Qabs (exp_partial n hn - 1 - hn)) (Qmult en (Qabs hn))) Hmain)).
          - apply qeq_le. ring. }
        apply Qlt_to_QltT.
        apply (Qlt_le_trans eps1' en' (Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                                               (projT1 (real_abs (real_plus (real_plus (cauchy_real_exp h) (real_opp real_one)) (real_opp h))) n))).
        { apply QltT_to_Qlt. exact Heps1e. }
        { apply (Qle_trans en' (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qabs (exp_partial n hn - 1 - hn)))
                                 (Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                                         (projT1 (real_abs (real_plus (real_plus (cauchy_real_exp h) (real_opp real_one)) (real_opp h))) n))).
          - exact Henle.
          - apply qeq_le. apply Qeq_sym. exact Hrepl. }
Qed.

(* ============================================================ *)
(* §3 δB-3：b5d3_S0_pts_bound —— 前置核验结论（见设计记录 §2）   *)
(* ============================================================ *)
(* 核验（read/grep 实测）：                           *)
(*  - approx_root 根 L37483 Lemma + L37595 Qed ⇒ 不透明；         *)
(*    log_seq y Hy n = projT1 (approx_root y Hy (log_eps n) …)   *)
(*    （L37642–37643）逐点不可归约。                              *)
(*  - log_scan（L36738 Fixpoint）为二分扫描，返回区间中点/冻结点，*)
(*    非 0；扫描深度 N ← q_pow_arch（arch 黑盒）不透明。          *)
(*  - real_eq 为 Bishop 逐尾语义（L3448–3451），real_log_one 等   *)
(*    只给 eventual ⟹ ∀n 逐点闭界不可达。                        *)
(*  ⇒ 路线 A/B 均受阻；本件降级（待核）（所需引理见设计记录 §2）。  *)

(* ============================================================ *)
(* 块 item21（前缀 b5dK_——主件 b5dK_exp_part_bound_closed_r_exp）——来源：演变/.ablation/sc2_parallel/sc2_b5a_ode/sc2_b5a_item21.v。 *)
(* ============================================================ *)

(* ============================================================ *)
(* H1 b5dK_real_mult_positive_exp（Defined 透明）               *)
(* 拷贝源：根 real_mult_positive（ConstructiveWorld.v L39518，   *)
(*   体 L39520–39529 经 real_eq_lt_lt + real_mult_lt_compat 根   *)
(*   Qed 链 ⟹ 见证不透明）。语句逐字；直构显式见证：destruct 输入 *)
(*   Ha/Hb（合法——实例化后具体化）取 eps := e1·e2、N := max N1   *)
(*   N2；坐标桥 real_mult_proj + Q 层 mult 单调（Qmult_lt_compat_r*)
(*   ×2 + comm 桥）。Defined 收尾 ⟹ projT1 见证 = e1·e2 可算。   *)
(* ============================================================ *)
Lemma b5dK_real_mult_positive_exp : forall a b : Real,
  real_lt real_zero a -> real_lt real_zero b -> real_lt real_zero (real_mult a b).
Proof.
  intros a b Ha Hb.
  destruct Ha as [e1 [He1 [N1 HN1]]].
  destruct Hb as [e2 [He2 [N2 HN2]]].
  unfold real_lt.
  exists (e1 * e2)%Q.
  split.
  - (* 0 < e1·e2 *)
    apply Qlt_to_QltT.
    apply (Qmult_lt_0_compat e1 e2).
    + apply QltT_to_Qlt. exact He1.
    + apply QltT_to_Qlt. exact He2.
  - exists (Nat.max N1 N2).
    intros n Hn.
    apply NatLe_drop in Hn.
    assert (Hn1 : NatLe N1 n) by (apply NatLe_lift; lia).
    assert (Hn2 : NatLe N2 n) by (apply NatLe_lift; lia).
    apply Qlt_to_QltT.
    (* 逐点：e1 < a_n、e2 < b_n（输入见证逐点化） *)
    assert (H1n : Qlt e1 (projT1 a n)).
    { apply (Qlt_le_trans e1 (Qminus (projT1 a n) (projT1 real_zero n)) (projT1 a n)).
      - apply QltT_to_Qlt. exact (HN1 n Hn1).
      - apply qeq_le. cbn [projT1 real_zero]. ring. }
    assert (H2n : Qlt e2 (projT1 b n)).
    { apply (Qlt_le_trans e2 (Qminus (projT1 b n) (projT1 real_zero n)) (projT1 b n)).
      - apply QltT_to_Qlt. exact (HN2 n Hn2).
      - apply qeq_le. cbn [projT1 real_zero]. ring. }
    assert (Ha0 : Qlt 0 (projT1 a n)).
    { apply (Qlt_trans 0 e1 (projT1 a n)).
      - apply QltT_to_Qlt. exact He1.
      - exact H1n. }
    assert (He20 : Qlt 0 e2) by (apply QltT_to_Qlt; exact He2).
    (* e1·e2 < a_n·b_n：两段 Qmult_lt_compat_r + comm 桥 *)
    assert (Hprod : Qlt (Qmult e1 e2) (Qmult (projT1 a n) (projT1 b n))).
    { apply (Qlt_le_trans (Qmult e1 e2) (Qmult (projT1 a n) e2)
                           (Qmult (projT1 a n) (projT1 b n))).
      - apply (Qmult_lt_compat_r e1 (projT1 a n) e2 He20 H1n).
      - apply (Qle_trans (Qmult (projT1 a n) e2) (Qmult e2 (projT1 a n))
                         (Qmult (projT1 a n) (projT1 b n))).
        + apply qeq_le. ring.
        + apply (Qle_trans (Qmult e2 (projT1 a n)) (Qmult (projT1 b n) (projT1 a n))
                           (Qmult (projT1 a n) (projT1 b n))).
          * apply Qlt_le_weak.
            apply (Qmult_lt_compat_r e2 (projT1 b n) (projT1 a n) Ha0 H2n).
          * apply qeq_le. ring. }
    (* 桥：e1·e2 < (a·b)_n − 0（real_mult_proj + ring） *)
    apply (Qlt_le_trans (Qmult e1 e2) (Qmult (projT1 a n) (projT1 b n))
                        (Qminus (projT1 (real_mult a b) n) (projT1 real_zero n))).
    + exact Hprod.
    + apply qeq_le.
      assert (Hm : projT1 (real_mult a b) n == Qmult (projT1 a n) (projT1 b n))
        by (apply real_mult_proj).
      setoid_rewrite Hm.
      cbn [projT1 real_zero].
      ring.
Defined.

(* ============================================================ *)
(* H2 b5dK_real_abs_plus_one_pos_exp（Defined 透明）            *)
(* 拷贝源：根 real_abs_plus_one_pos（ConstructiveWorld.v        *)
(*   L47117，体 L47119–47147 经逐点 1+Qabs 论证；Qed ⟹ 见证      *)
(*   不透明——real_inv_pos 值按见证 destruct 出 N0 ⟹ 需透明版）。*)
(* 语句逐字；体重写为干净直构：exists (1/2)%Q + N := 0（见证     *)
(*   与根同款：e = 1/2、N0 = 0），两分支全闭式/Q 层（Qabs ≥ 0）。*)
(* Defined 收尾 ⟹ destruct 得 N0 := 0（可算）。                 *)
(* ============================================================ *)
Lemma b5dK_real_abs_plus_one_pos_exp : forall a : Real,
  real_lt real_zero (real_plus real_one (real_abs a)).
Proof.
  intro a.
  unfold real_lt.
  exists (1 / 2)%Q.
  split.
  - apply Qlt_to_QltT.
    unfold Qlt. simpl. lia.
  - exists 0%nat.
    intros n Hn.
    apply Qlt_to_QltT.
    assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
    setoid_rewrite Hz.
    assert (Hnz : projT1 (real_plus real_one (real_abs a)) n ==
                  Qplus 1 (Qabs (projT1 a n))).
    { setoid_rewrite (real_plus_proj real_one (real_abs a) n).
      setoid_rewrite (real_abs_proj a n).
      cbn [projT1]. reflexivity. }
    setoid_rewrite Hnz.
    apply (Qlt_le_trans (1 / 2) 1
                        (Qminus (Qplus 1 (Qabs (projT1 a n))) 0)).
    + unfold Qlt. simpl. lia.
    + apply (Qle_trans 1 (Qplus 1 (Qabs (projT1 a n)))
                        (Qminus (Qplus 1 (Qabs (projT1 a n))) 0)).
      * apply (Qplus_le_compat 1 1 0 (Qabs (projT1 a n))).
        -- apply Qle_refl.
        -- apply Qabs_nonneg.
      * apply qeq_le. ring.
Defined.

(* ============================================================ *)
(* H4 b5dK_real_abs_scaling_le_exp（根 real_abs_scaling_le      *)
(*   L48584–48760 拷贝，Qed——纯证明件，无值路径）              *)
(* 根件语句硬编码根 real_abs_plus_one_pos 见证（real_inv_pos 的 *)
(*   证书位）；本件 invM 证书换 H2（b5dK_real_abs_plus_one_pos_ *)
(*   exp——Defined）⟹ 根闭式件不可直接应用 ⟹ 语句同形换见证名    *)
(*   的透明拷贝（体逐字 + 见证名机械替换，零其它改动）。        *)
(* ============================================================ *)

Lemma b5dK_real_abs_scaling_le_exp : forall (a eps eps' h : Real),
  real_lt real_zero eps -> real_lt real_zero eps' ->
  real_le (real_mult (real_abs a)
            (real_plus (real_mult (real_mult eps (real_inv_pos (real_plus real_one (real_abs a)) (b5dK_real_abs_plus_one_pos_exp a))) (real_abs h))
                       (real_mult eps' (real_inv_pos (real_plus real_one (real_abs a)) (b5dK_real_abs_plus_one_pos_exp a)))))
          (real_plus (real_mult eps (real_abs h)) eps').
Proof.
  intros a eps eps' h Heps Heps'.
  unfold real_le. left.
  destruct Heps as [eps1 [Heps1 [N1 HN1]]].
  destruct Heps' as [eps1' [Heps1' [N1' HN1']]].
  destruct (real_norm_bounded a) as [M [HMpos HM]].
  destruct (real_inv_proj (real_plus real_one (real_abs a)) (b5dK_real_abs_plus_one_pos_exp a)) as [Ni HNi].
  set (M2 := Qplus M 2).
  assert (HM2pos : Qlt 0 M2).
  { unfold M2.
    apply (Qlt_le_trans 0 1 (Qplus M 2)).
    - unfold Qlt. simpl. lia.
    - apply (Qle_trans 1 (Qplus 0 1) (Qplus M 2)).
      + apply qeq_le. ring.
      + assert (H12 : Qle 1 2) by (unfold Qle; simpl; lia).
        apply (Qplus_le_compat 0 M 1 2 (Qlt_le_weak 0 M (QltT_to_Qlt _ _ HMpos)) H12). }
  exists (Qmult eps1' (Qinv M2)).
  split.
  - (* QltT 0 (eps1'·inv M2) *)
    apply Qlt_to_QltT.
    apply (Qmult_lt_0_compat eps1' (Qinv M2)).
    + apply QltT_to_Qlt. exact Heps1'.
    + apply Qinv_lt_0_compat. exact HM2pos.
  - (* 逐点：eps1'·inv M2 < (右_n − 左_n) *)
    exists (Nat.max (Nat.max N1 N1') Ni).
    intros n Hn.
    apply NatLe_drop in Hn.
    assert (Hn1 : (N1 <= n)%nat) by lia.
    assert (Hn1' : (N1' <= n)%nat) by lia.
    assert (HnNi : (Ni <= n)%nat) by lia.
    set (an := Qabs (projT1 a n)).
    set (en := projT1 eps n).
    set (e'n := projT1 eps' n).
    set (hn := projT1 h n).
    (* 左端投影展开 *)
    assert (HA : projT1 (real_mult (real_abs a)
              (real_plus (real_mult (real_mult eps (real_inv_pos (real_plus real_one (real_abs a)) (b5dK_real_abs_plus_one_pos_exp a))) (real_abs h))
                         (real_mult eps' (real_inv_pos (real_plus real_one (real_abs a)) (b5dK_real_abs_plus_one_pos_exp a))))) n
            == Qmult an (Qplus (Qmult (Qmult en (Qinv (Qplus an 1))) (Qabs hn)) (Qmult e'n (Qinv (Qplus an 1))))).
    { unfold an, en, e'n, hn.
      setoid_rewrite (real_mult_proj (real_abs a)
        (real_plus (real_mult (real_mult eps (real_inv_pos (real_plus real_one (real_abs a)) (b5dK_real_abs_plus_one_pos_exp a))) (real_abs h))
                   (real_mult eps' (real_inv_pos (real_plus real_one (real_abs a)) (b5dK_real_abs_plus_one_pos_exp a)))) n).
      setoid_rewrite (real_plus_proj
        (real_mult (real_mult eps (real_inv_pos (real_plus real_one (real_abs a)) (b5dK_real_abs_plus_one_pos_exp a))) (real_abs h))
        (real_mult eps' (real_inv_pos (real_plus real_one (real_abs a)) (b5dK_real_abs_plus_one_pos_exp a))) n).
      setoid_rewrite (real_mult_proj
        (real_mult eps (real_inv_pos (real_plus real_one (real_abs a)) (b5dK_real_abs_plus_one_pos_exp a))) (real_abs h) n).
      setoid_rewrite (real_mult_proj eps (real_inv_pos (real_plus real_one (real_abs a)) (b5dK_real_abs_plus_one_pos_exp a)) n).
      setoid_rewrite (real_mult_proj eps' (real_inv_pos (real_plus real_one (real_abs a)) (b5dK_real_abs_plus_one_pos_exp a)) n).
      setoid_rewrite (real_abs_proj h n).
      setoid_rewrite (real_abs_proj a n).
      setoid_rewrite (HNi n HnNi).
      setoid_rewrite (real_plus_proj real_one (real_abs a) n).
      setoid_rewrite (real_abs_proj a n).
      cbn [real_one real_const projT1].
      setoid_rewrite (Qplus_comm 1 (Qabs (projT1 a n))).
      ring. }
    (* 右端投影展开 *)
    assert (HB : projT1 (real_plus (real_mult eps (real_abs h)) eps') n
                 == Qplus (Qmult en (Qabs hn)) e'n).
    { unfold en, e'n, hn.
      setoid_rewrite (real_plus_proj (real_mult eps (real_abs h)) eps' n).
      setoid_rewrite (real_mult_proj eps (real_abs h) n).
      setoid_rewrite (real_abs_proj h n).
      simpl. ring. }
    (* 正性：eps 尾部 > 0 *)
    assert (HN1e : QltT eps1 en).
    { unfold en. apply Qlt_to_QltT.
      apply (Qlt_le_trans eps1 (Qminus (projT1 eps n) (projT1 real_zero n)) (projT1 eps n)).
      - apply QltT_to_Qlt. exact (HN1 n (NatLe_lift _ _ Hn1)).
      - apply qeq_le. cbn [real_zero real_const projT1]. ring. }
    assert (Hen : Qlt 0 en)
      by (apply (Qlt_trans 0 eps1 en); [apply QltT_to_Qlt; exact Heps1 | apply QltT_to_Qlt; exact HN1e]).
    assert (HN1'e : QltT eps1' e'n).
    { unfold e'n. apply Qlt_to_QltT.
      apply (Qlt_le_trans eps1' (Qminus (projT1 eps' n) (projT1 real_zero n)) (projT1 eps' n)).
      - apply QltT_to_Qlt. exact (HN1' n (NatLe_lift _ _ Hn1')).
      - apply qeq_le. cbn [real_zero real_const projT1]. ring. }
    assert (He'n : Qlt 0 e'n)
      by (apply (Qlt_trans 0 eps1' e'n); [apply QltT_to_Qlt; exact Heps1' | apply QltT_to_Qlt; exact HN1'e]).
    assert (Han1 : Qlt 0 (Qplus an 1)).
    { apply (Qlt_le_trans 0 1 (Qplus an 1)).
      - unfold Qlt. simpl. lia.
      - apply (Qle_trans 1 (Qplus 0 1) (Qplus an 1)).
        + apply qeq_le. ring.
        + apply (Qplus_le_compat 0 an 1 1 (Qabs_nonneg (projT1 a n)) (Qle_refl 1)). }
    (* inv 严格递减：an+1 ≤ M+1 < M+2 ⟹ inv M2 < inv(an+1) *)
    assert (Hm12 : Qlt (Qplus M 1) (Qplus M 2)).
    { apply (proj2 (Qlt_minus_iff (Qplus M 1) (Qplus M 2))).
      assert (Hd : Qminus (Qplus M 2) (Qplus M 1) == 1) by ring.
      rewrite Hd. unfold Qlt. simpl. lia. }
    assert (Him : Qlt (Qinv M2) (Qinv (Qplus an 1))).
    { assert (Han1nz : ~ (Qplus an 1 == 0)).
      { intro H. apply (Qlt_irrefl 0). rewrite H in Han1. exact Han1. }
      assert (HM2nz : ~ (M2 == 0)).
      { intro H. apply (Qlt_irrefl 0). rewrite H in HM2pos. exact HM2pos. }
      apply (proj2 (Qlt_minus_iff (Qinv M2) (Qinv (Qplus an 1)))).
      assert (Hdiff : Qminus (Qinv (Qplus an 1)) (Qinv M2)
                      == Qmult (Qminus M2 (Qplus an 1)) (Qinv (Qmult M2 (Qplus an 1)))).
      { field. split.
        - exact Han1nz.
        - exact HM2nz. }
      rewrite Hdiff.
      apply (Qmult_lt_0_compat (Qminus M2 (Qplus an 1)) (Qinv (Qmult M2 (Qplus an 1)))).
      - apply (proj1 (Qlt_minus_iff (Qplus an 1) M2)).
        apply (Qle_lt_trans (Qplus an 1) (Qplus M 1) M2).
        + apply (Qplus_le_compat an M 1 1 (QleT'_to_Qle _ _ (HM n)) (Qle_refl 1)).
        + unfold M2. exact Hm12.
      - apply Qinv_lt_0_compat.
        apply (Qmult_lt_0_compat M2 (Qplus an 1)); [exact HM2pos | exact Han1]. }
    (* 主链：eps1'·inv M2 < e'n·inv(an+1) ≤ (en|hn|+e'n)·inv(an+1) == 右−左 *)
    assert (Hmain : Qlt (Qmult eps1' (Qinv M2))
        (Qminus (Qplus (Qmult en (Qabs hn)) e'n)
           (Qmult an (Qplus (Qmult (Qmult en (Qinv (Qplus an 1))) (Qabs hn)) (Qmult e'n (Qinv (Qplus an 1))))))).
    { assert (Han1nz : ~ (Qplus an 1 == 0)).
      { intro H. apply (Qlt_irrefl 0). rewrite H in Han1. exact Han1. }
      assert (Hiden : Qminus (Qplus (Qmult en (Qabs hn)) e'n)
            (Qmult an (Qplus (Qmult (Qmult en (Qinv (Qplus an 1))) (Qabs hn)) (Qmult e'n (Qinv (Qplus an 1)))))
            == Qmult (Qplus (Qmult en (Qabs hn)) e'n) (Qinv (Qplus an 1))).
      { field. exact Han1nz. }
      apply (Qlt_le_trans (Qmult eps1' (Qinv M2)) (Qmult e'n (Qinv (Qplus an 1)))
             (Qminus (Qplus (Qmult en (Qabs hn)) e'n)
                (Qmult an (Qplus (Qmult (Qmult en (Qinv (Qplus an 1))) (Qabs hn)) (Qmult e'n (Qinv (Qplus an 1))))))).
      - apply (Qlt_le_trans (Qmult eps1' (Qinv M2)) (Qmult eps1' (Qinv (Qplus an 1)))
                             (Qmult e'n (Qinv (Qplus an 1)))).
        + setoid_rewrite (Qmult_comm eps1' (Qinv M2)).
          setoid_rewrite (Qmult_comm eps1' (Qinv (Qplus an 1))).
          apply (Qmult_lt_compat_r (Qinv M2) (Qinv (Qplus an 1)) eps1').
          * apply QltT_to_Qlt. exact Heps1'.
          * exact Him.
        + apply (Qmult_le_compat_r eps1' e'n (Qinv (Qplus an 1))).
          * apply Qlt_le_weak. apply QltT_to_Qlt. exact HN1'e.
          * apply Qlt_le_weak. apply Qinv_lt_0_compat. exact Han1.
      - apply (Qle_trans (Qmult e'n (Qinv (Qplus an 1)))
               (Qmult (Qplus (Qmult en (Qabs hn)) e'n) (Qinv (Qplus an 1)))
               (Qminus (Qplus (Qmult en (Qabs hn)) e'n)
                  (Qmult an (Qplus (Qmult (Qmult en (Qinv (Qplus an 1))) (Qabs hn)) (Qmult e'n (Qinv (Qplus an 1))))))).
        + apply (Qmult_le_compat_r e'n (Qplus (Qmult en (Qabs hn)) e'n) (Qinv (Qplus an 1))).
          * apply (Qle_trans e'n (Qplus e'n (Qmult en (Qabs hn))) (Qplus (Qmult en (Qabs hn)) e'n)).
            { apply (Qle_plus_nonneg_r e'n (Qmult en (Qabs hn))).
              apply (Qmult_le_compat_nonneg 0 en 0 (Qabs hn)).
              { split; [apply Qle_refl | apply Qlt_le_weak; exact Hen]. }
              { split; [apply Qle_refl | apply Qabs_nonneg]. } }
            { apply qeq_le. apply (Qplus_comm e'n (Qmult en (Qabs hn))). }
          * apply Qlt_le_weak. apply Qinv_lt_0_compat. exact Han1.
        + apply qeq_le. apply Qeq_sym. exact Hiden. }
    (* 收尾：重写投影后 exact Hmain *)
    apply Qlt_to_QltT.
    assert (Hrepl : Qeq (Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                                (projT1 (real_mult (real_abs a)
                                   (real_plus (real_mult (real_mult eps (real_inv_pos (real_plus real_one (real_abs a)) (b5dK_real_abs_plus_one_pos_exp a))) (real_abs h))
                                              (real_mult eps' (real_inv_pos (real_plus real_one (real_abs a)) (b5dK_real_abs_plus_one_pos_exp a))))) n))
                        (Qminus (Qplus (Qmult en (Qabs hn)) e'n)
                           (Qmult an (Qplus (Qmult (Qmult en (Qinv (Qplus an 1))) (Qabs hn)) (Qmult e'n (Qinv (Qplus an 1))))))).
    { apply (Qminus_comp (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                         (Qplus (Qmult en (Qabs hn)) e'n) HB
                         (projT1 (real_mult (real_abs a)
                            (real_plus (real_mult (real_mult eps (real_inv_pos (real_plus real_one (real_abs a)) (b5dK_real_abs_plus_one_pos_exp a))) (real_abs h))
                                       (real_mult eps' (real_inv_pos (real_plus real_one (real_abs a)) (b5dK_real_abs_plus_one_pos_exp a))))) n)
                         (Qmult an (Qplus (Qmult (Qmult en (Qinv (Qplus an 1))) (Qabs hn)) (Qmult e'n (Qinv (Qplus an 1))))) HA). }
    apply (Qlt_le_trans (Qmult eps1' (Qinv M2))
           (Qminus (Qplus (Qmult en (Qabs hn)) e'n)
              (Qmult an (Qplus (Qmult (Qmult en (Qinv (Qplus an 1))) (Qabs hn)) (Qmult e'n (Qinv (Qplus an 1))))))
           (Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                   (projT1 (real_mult (real_abs a)
                      (real_plus (real_mult (real_mult eps (real_inv_pos (real_plus real_one (real_abs a)) (b5dK_real_abs_plus_one_pos_exp a))) (real_abs h))
                                 (real_mult eps' (real_inv_pos (real_plus real_one (real_abs a)) (b5dK_real_abs_plus_one_pos_exp a))))) n))).
    { exact Hmain. }
    { apply qeq_le. apply Qeq_sym. exact Hrepl. }
Qed.


(* ============================================================ *)
(* H3 b5dK_exp_minus_one_linear_closed_exp（Defined 透明）      *)
(* 拷贝源：上游 sc2_b5a_item7 b5d3_exp_minus_one_linear_closed   *)
(*   （L208–400，收尾 Qed——本件透明重证件）。语句逐字（含首分量  *)
(*   real_eq delta (real_min (real_const (1#2))                 *)
(*                          (real_mult eps (real_const (1#4))))）*)
(*   体逐字复制（根 exp_minus_one_linear L48341–48533 改写版：   *)
(*   two_inv/four_inv 展开改写为 real_const 闭式 + real_inv_proj *)
(*   机制删除）；两处 (1#2)/(1#4) 正性证书（item7 文件内件         *)
(*   b5d3_Hq_half/Hq_four）内联直证；Qed→Defined。              *)
(* 值路径：exists delta，delta := real_min (real_const (1#2))   *)
(*   (real_mult eps (real_const (1#4)))——全透明 ⟹ δlin 首投影    *)
(*   可算（检验：eps := real_const (1#2) → (1#8)）。            *)
(* ============================================================ *)


Lemma b5dK_exp_minus_one_linear_closed_exp : forall (eps : Real), real_lt real_zero eps ->
  sigT (fun delta : Real =>
    And (real_eq delta (real_min (real_const (1 # 2)) (real_mult eps (real_const (1 # 4)))))
        (And (real_lt real_zero delta)
             (forall h : Real, real_lt (real_abs h) delta ->
               forall (eps' : Real), real_lt real_zero eps' ->
               real_le (real_abs (real_plus (real_plus (cauchy_real_exp h) (real_opp real_one)) (real_opp h)))
                       (real_plus (real_mult eps (real_abs h)) eps')))).
Proof.
  intros eps Heps.
  set (delta := real_min (real_const (1 # 2)) (real_mult eps (real_const (1 # 4)))).
  exists delta.
  split.
  - (* real_eq delta (real_min (real_const (1#2)) (real_mult eps (real_const (1#4)))) *)
    unfold delta. apply real_eq_refl.
  - split.
    + (* 0 < delta *)
      unfold delta.
      apply real_min_pos.
      * apply real_const_pos_f1. unfold Qlt. simpl. lia.
      * apply b5dK_real_mult_positive_exp.
        -- exact Heps.
        -- apply real_const_pos_f1. unfold Qlt. simpl. lia.
    + intros h Hh eps' Heps'.
      assert (Hh_half : real_lt (real_abs h) (real_const (1 # 2)))
        by (unfold delta in Hh; apply (real_min_lt_l h (real_const (1 # 2)) (real_mult eps (real_const (1 # 4)))); exact Hh).
      assert (Hh_eps4 : real_lt (real_abs h) (real_mult eps (real_const (1 # 4))))
        by (unfold delta in Hh; apply (real_min_lt_r h (real_const (1 # 2)) (real_mult eps (real_const (1 # 4)))); exact Hh).
      (* real_le 左分支：real_lt 构造 *)
      left.
      destruct Heps as [eps1 [Heps1 [N1 HN1]]].
      destruct Heps' as [eps1' [Heps1' [N1' HN1']]].
      destruct Hh_half as [eps2 [Heps2 [N2 HN2]]].
      destruct Hh_eps4 as [eps3 [Heps3 [N3 HN3]]].
      exists eps1'.
      split.
      * exact Heps1'.
      * exists (Nat.max (Nat.max (Nat.max N1 N1') (Nat.max N2 N3)) 2).
        intros n Hn.
        apply NatLe_drop in Hn.
        set (en := projT1 eps n). set (en' := projT1 eps' n). set (hn := projT1 h n).
        (* 逐点展开 A、B *)
        assert (HA : projT1 (real_abs (real_plus (real_plus (cauchy_real_exp h) (real_opp real_one)) (real_opp h))) n ==
                      Qabs (exp_partial n hn - 1 - hn)).
        { unfold hn.
          setoid_rewrite (real_abs_proj (real_plus (real_plus (cauchy_real_exp h) (real_opp real_one)) (real_opp h)) n).
          setoid_rewrite (real_plus_proj (real_plus (cauchy_real_exp h) (real_opp real_one)) (real_opp h) n).
          setoid_rewrite (real_plus_proj (cauchy_real_exp h) (real_opp real_one) n).
          setoid_rewrite (real_opp_proj real_one n).
          setoid_rewrite (real_opp_proj h n).
          rewrite (real_exp_proj h n).
          cbn [projT1 real_one].
          unfold Qminus. ring. }
        assert (HB : projT1 (real_plus (real_mult eps (real_abs h)) eps') n == en * Qabs hn + en').
        { unfold en, en', hn.
          setoid_rewrite (real_plus_proj (real_mult eps (real_abs h)) eps' n).
          setoid_rewrite (real_mult_proj eps (real_abs h) n).
          setoid_rewrite (real_abs_proj h n).
          cbn [projT1]. ring. }
        (* 逐点界 1：|hn| < 1/2（Hh_half 见证 + real_const (1#2) 投影） *)
        assert (Hn2 : (N2 <= n)%nat) by lia.
        assert (Hn3 : (N3 <= n)%nat) by lia.
        assert (Hn1 : (N1 <= n)%nat) by lia.
        assert (Hn1' : (N1' <= n)%nat) by lia.
        assert (HN2q : Qlt eps2 (Qminus (Qinv 2) (Qabs hn))).
        { apply (Qlt_le_trans eps2 (Qminus (projT1 (real_const (1 # 2)) n) (projT1 (real_abs h) n)) (Qminus (Qinv 2) (Qabs hn))).
          - apply QltT_to_Qlt. exact (HN2 n (NatLe_lift _ _ Hn2)).
          - apply qeq_le.
            rewrite (real_abs_proj h n).
            rewrite (real_const_proj (1 # 2) n).
            reflexivity. }
        assert (Hhn_half : Qlt (Qabs hn) (Qinv 2)).
        { apply (Qlt_le_trans (Qabs hn) (Qminus (Qinv 2) eps2) (Qinv 2)).
          - apply (q_lt_minus_shift eps2 (Qinv 2) (Qabs hn)). exact HN2q.
          - assert (Heps2q : Qle 0 eps2).
            { apply Qlt_le_weak. apply QltT_to_Qlt. exact Heps2. }
            apply (Qle_trans (Qminus (Qinv 2) eps2) (Qplus (Qminus (Qinv 2) eps2) eps2) (Qinv 2)).
            + apply (Qle_trans (Qminus (Qinv 2) eps2) (Qplus (Qminus (Qinv 2) eps2) 0) (Qplus (Qminus (Qinv 2) eps2) eps2)).
              * apply qeq_le. ring.
              * apply (Qplus_le_compat (Qminus (Qinv 2) eps2) (Qminus (Qinv 2) eps2) 0 eps2 (Qle_refl _) Heps2q).
            + apply qeq_le. ring. }
        (* 逐点界 2：|hn| < en/4（Hh_eps4 见证 + eps·real_const (1#4) 投影） *)
        assert (HN3q : Qlt eps3 (Qminus (Qmult en (Qmult (Qinv 2) (Qinv 2))) (Qabs hn))).
        { apply (Qlt_le_trans eps3 (Qminus (projT1 (real_mult eps (real_const (1 # 4))) n) (projT1 (real_abs h) n))
                                  (Qminus (Qmult en (Qmult (Qinv 2) (Qinv 2))) (Qabs hn))).
          - apply QltT_to_Qlt. exact (HN3 n (NatLe_lift _ _ Hn3)).
          - apply qeq_le.
            rewrite (real_abs_proj h n).
            unfold en.
            setoid_rewrite (real_mult_proj eps (real_const (1 # 4)) n).
            rewrite (real_const_proj (1 # 4) n).
            cbn [projT1 real_const].
            reflexivity. }
        assert (Hhn_eps4 : Qlt (Qabs hn) (Qmult en (Qmult (Qinv 2) (Qinv 2)))).
        { apply (Qlt_le_trans (Qabs hn) (Qminus (Qmult en (Qmult (Qinv 2) (Qinv 2))) eps3)
                              (Qmult en (Qmult (Qinv 2) (Qinv 2)))).
          - apply (q_lt_minus_shift eps3 (Qmult en (Qmult (Qinv 2) (Qinv 2))) (Qabs hn)). exact HN3q.
          - assert (Heps3q : Qle 0 eps3).
            { apply Qlt_le_weak. apply QltT_to_Qlt. exact Heps3. }
            apply (Qle_trans (Qminus (Qmult en (Qmult (Qinv 2) (Qinv 2))) eps3)
                             (Qplus (Qminus (Qmult en (Qmult (Qinv 2) (Qinv 2))) eps3) eps3)
                             (Qmult en (Qmult (Qinv 2) (Qinv 2)))).
            + apply (Qle_trans (Qminus (Qmult en (Qmult (Qinv 2) (Qinv 2))) eps3)
                               (Qplus (Qminus (Qmult en (Qmult (Qinv 2) (Qinv 2))) eps3) 0)
                               (Qplus (Qminus (Qmult en (Qmult (Qinv 2) (Qinv 2))) eps3) eps3)).
              * apply qeq_le. ring.
              * apply (Qplus_le_compat (Qminus (Qmult en (Qmult (Qinv 2) (Qinv 2))) eps3)
                                       (Qminus (Qmult en (Qmult (Qinv 2) (Qinv 2))) eps3) 0 eps3 (Qle_refl _) Heps3q).
            + apply qeq_le. ring. }
        (* 主链：B_n − A_n ≥ eps1' *)
        assert (Hquad : Qle (Qabs (exp_partial n hn - 1 - hn))
                            (Qmult (Qmult (Qabs hn) (Qabs hn)) (3 # 2))).
        { apply (exp_partial_linear_quad hn n).
          - lia.
          - (* 2|hn| ≤ 3：从 |hn| < 1/2 *)
            apply (Qlt_le_weak (Qmult (1 + 1)%Q (Qabs hn)) 3%Q).
            apply (Qlt_trans (Qmult (1 + 1)%Q (Qabs hn)) (Qmult (1 + 1)%Q (Qinv 2)) 3%Q).
            + setoid_rewrite (Qmult_comm (1 + 1)%Q (Qabs hn)).
              setoid_rewrite (Qmult_comm (1 + 1)%Q (Qinv 2)).
              apply (Qmult_lt_compat_r (Qabs hn) (Qinv 2) (1 + 1)%Q).
              * unfold Qlt. simpl. lia.
              * exact Hhn_half.
            + unfold Qlt. simpl. lia. }
        assert (Hq2 : Qle (Qmult (Qmult (Qabs hn) (Qabs hn)) (3 # 2))
                          (Qmult (Qmult en (Qabs hn)) (3 # 8))).
        { assert (Hhn_le : Qle (Qabs hn) (Qmult en (Qmult (Qinv 2) (Qinv 2)))).
          { apply Qlt_le_weak. exact Hhn_eps4. }
          apply (Qle_trans (Qmult (Qmult (Qabs hn) (Qabs hn)) (3 # 2))
                           (Qmult (Qmult (Qmult en (Qmult (Qinv 2) (Qinv 2))) (Qabs hn)) (3 # 2))
                           (Qmult (Qmult en (Qabs hn)) (3 # 8))).
          - (* |hn|² ≤ (en/4)·|hn|，乘 (3/2) *)
            apply (Qmult_le_compat_r (Qmult (Qabs hn) (Qabs hn))
                                     (Qmult (Qmult en (Qmult (Qinv 2) (Qinv 2))) (Qabs hn))
                                     (3 # 2)).
            + apply (Qmult_le_compat_r (Qabs hn) (Qmult en (Qmult (Qinv 2) (Qinv 2))) (Qabs hn)).
              * exact Hhn_le.
              * apply Qabs_nonneg.
            + unfold Qle. simpl. lia.
          - apply qeq_le. field. }
        assert (Hq3 : Qle (Qmult (Qmult en (Qabs hn)) (3 # 8)) (Qmult en (Qabs hn))).
        { setoid_rewrite (Qmult_comm (Qmult en (Qabs hn)) (3 # 8)).
          apply (Qle_trans (Qmult (3 # 8) (Qmult en (Qabs hn))) (Qmult 1%Q (Qmult en (Qabs hn))) (Qmult en (Qabs hn))).
          - apply (Qmult_le_compat_r (3 # 8) 1%Q (Qmult en (Qabs hn))).
            + unfold Qle. simpl. lia.
            + assert (HN1e : QltT eps1 en).
              { apply Qlt_to_QltT.
                apply (Qlt_le_trans eps1 (Qminus (projT1 eps n) (projT1 real_zero n)) en).
                - apply QltT_to_Qlt. exact (HN1 n (NatLe_lift _ _ Hn1)).
                - apply qeq_le. cbn [real_zero real_const projT1]. unfold en. ring. }
              assert (Henq : Qle 0 en).
              { apply Qlt_le_weak. apply (Qlt_trans 0 eps1 en).
                - apply QltT_to_Qlt. exact Heps1.
                - apply QltT_to_Qlt. exact HN1e. }
              apply (Qmult_le_0_compat en (Qabs hn) Henq (Qabs_nonneg hn)).
          - apply qeq_le. ring. }
        assert (Hmain : Qle (Qabs (exp_partial n hn - 1 - hn)) (Qmult en (Qabs hn))).
        { apply (Qle_trans _ (Qmult (Qmult (Qabs hn) (Qabs hn)) (3 # 2)) _).
          - exact Hquad.
          - apply (Qle_trans _ (Qmult (Qmult en (Qabs hn)) (3 # 8)) _).
            + exact Hq2.
            + exact Hq3. }
        (* eps1' < B_n − A_n：eps1' < en' ≤ B_n − A_n *)
        assert (Heps1e : QltT eps1' en').
        { apply Qlt_to_QltT.
          apply (Qlt_le_trans eps1' (Qminus (projT1 eps' n) (projT1 real_zero n)) en').
          - apply QltT_to_Qlt. exact (HN1' n (NatLe_lift _ _ Hn1')).
          - apply qeq_le. cbn [real_zero real_const projT1]. unfold en'. ring. }
        assert (Hrepl : Qeq (Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                                    (projT1 (real_abs (real_plus (real_plus (cauchy_real_exp h) (real_opp real_one)) (real_opp h))) n))
                            (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qabs (exp_partial n hn - 1 - hn)))).
        { apply (Qminus_comp (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                             (Qplus (Qmult en (Qabs hn)) en') HB
                             (projT1 (real_abs (real_plus (real_plus (cauchy_real_exp h) (real_opp real_one)) (real_opp h))) n)
                             (Qabs (exp_partial n hn - 1 - hn)) HA). }
        assert (Henle : Qle en' (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qabs (exp_partial n hn - 1 - hn)))).
        { apply (Qle_trans en' (Qplus en' (Qminus (Qmult en (Qabs hn)) (Qabs (exp_partial n hn - 1 - hn))))
                             (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qabs (exp_partial n hn - 1 - hn)))).
          - apply (Qle_trans en' (Qplus en' 0) (Qplus en' (Qminus (Qmult en (Qabs hn)) (Qabs (exp_partial n hn - 1 - hn))))).
            + apply qeq_le. ring.
            + apply (Qplus_le_compat en' en' 0 (Qminus (Qmult en (Qabs hn)) (Qabs (exp_partial n hn - 1 - hn)))
                                     (Qle_refl en')
                                     (proj1 (Qle_minus_iff (Qabs (exp_partial n hn - 1 - hn)) (Qmult en (Qabs hn))) Hmain)).
          - apply qeq_le. ring. }
        apply Qlt_to_QltT.
        apply (Qlt_le_trans eps1' en' (Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                                               (projT1 (real_abs (real_plus (real_plus (cauchy_real_exp h) (real_opp real_one)) (real_opp h))) n))).
        { apply QltT_to_Qlt. exact Heps1e. }
        { apply (Qle_trans en' (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qabs (exp_partial n hn - 1 - hn)))
                                 (Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                                         (projT1 (real_abs (real_plus (real_plus (cauchy_real_exp h) (real_opp real_one)) (real_opp h))) n))).
          - exact Henle.
          - apply qeq_le. apply Qeq_sym. exact Hrepl. }
Defined.

(* ============================================================ *)
(* 主件 ① b5dK_gdiff_pts_r_exp（Defined 透明）                  *)
(* 拷贝源：213 根 b5f_gdiff_pts_r（ConstructiveWorld.v L82826–    *)
(*   L83231，406 行切片机器抽取零手抄）；语句逐字。            *)
(* 变更项：① Lemma 头改名 ② 体内 LogErr   *)
(*   叶 b5f_LogErr_delta → 上游 item20 b5dJ_LogErr_delta_exp      *)
(*   （同参调用 x epsL HepsL）③ real_mult_positive → 本文件    *)
(*   b5dK_real_mult_positive_exp（含供入 J2 的 HepsL 构造链——  *)
(*   值路径上 J1/J2 体内 destruct 输入见证需透明）④             *)
(*   real_const_pos → 上游 item23 b5dM_real_const_pos（同语句）   *)
(*   ⑤ 第二分量内 destruct b5c_d_proj_le_one → 上游 item23       *)
(*   b5dM_b5c_d_proj_le_one ⑥ 收尾 Qed→Defined。               *)
(* 值路径：δg := min(min(δL·(1#12), eps·kL), (1#2))，δL :=      *)
(*   projT1 (b5dJ_LogErr_delta_exp x epsL HepsL)，epsL :=        *)
(*   eps·(real_const kL)，kL := k2·(1#2)——全透明链（item20 J1/  *)
(*   J2 Defined + H1/H2 透明证书）⟹ δg 首投影可算。            *)
(* ============================================================ *)
Lemma b5dK_gdiff_pts_r_exp : forall (r : Q) (Hr0 : Qle 0 r) (Hr1 : Qlt r 1)
  (x : Real) (Hxr : forall n : nat, QleT' (Qabs (projT1 x n)) r)
  (eps : Real) (Heps : real_lt real_zero eps)
  (k2 k2p : Q) (Hk2 : QltT 0 k2) (Hk2p : QltT 0 k2p),
  sigT (fun δg : Real => And (real_lt real_zero δg)
    (forall (h : Real), real_lt (real_abs h) δg ->
      forall (eps' : Real), real_lt real_zero eps' ->
      sigT (fun N : nat => forall n : nat, NatLe N n ->
        Qle (Qabs (projT1 (real_plus (b5f_v x h)
                  (real_opp (real_mult (real_mult x (b5a_atan_d x)) h))) n))
            (Qplus (Qmult (Qmult (projT1 eps n) k2) (Qabs (projT1 h n)))
                   (Qmult (Qmult 2 k2p) (projT1 eps' n)))))).
Proof.
  intros r Hr0 Hr1 x Hxr eps Heps k2 k2p Hk2 Hk2p.
  (* (1/2) Qdiv 与 (1#2) Qmake 桥（逐点 Q 层用 Qmake 免 Qinv） *)
  assert (Hhalf : (1 / 2) == (1 # 2)).
  { unfold Qdiv. cbn. reflexivity. }
  (* kL := k2·(1#2)；epsL := eps·kL（LogErr-delta 的线性份额） *)
  set (kL := Qmult k2 (1 # 2)).
  assert (HkLQ : Qlt 0 kL).
  { unfold kL. apply (Qmult_lt_0_compat k2 (1 # 2)).
    - apply QltT_to_Qlt. exact Hk2.
    - change (Qlt 0 (1 # 2)). unfold Qlt. simpl. lia. }
  assert (HkLT : QltT 0 kL) by (apply Qlt_to_QltT; exact HkLQ).
  assert (HkL0 : Qle 0 kL) by (apply Qlt_le_weak; exact HkLQ).
  set (epsL := real_mult eps (real_const kL)).
  assert (HepsL : real_lt real_zero epsL).
  { unfold epsL. apply b5dK_real_mult_positive_exp.
    - exact Heps.
    - apply b5dM_real_const_pos. exact HkLT. }
  destruct (b5dJ_LogErr_delta_exp x epsL HepsL) as [δL [HδL0 HδL]].
  (* δ 三分量组装 *)
  set (A := real_mult δL (real_const (1 # 12))).
  set (B := real_mult eps (real_const kL)).
  set (C := real_const (1 # 2)).
  set (δg := real_min (real_min A B) C).
  assert (H12T : QltT 0 (1 # 2)).
  { apply Qlt_to_QltT. change (Qlt 0 (1 # 2)). unfold Qlt. simpl. lia. }
  assert (H112T : QltT 0 (1 # 12)).
  { apply Qlt_to_QltT. change (Qlt 0 (1 # 12)). unfold Qlt. simpl. lia. }
  assert (HA0 : real_lt real_zero A).
  { unfold A. apply b5dK_real_mult_positive_exp.
    - exact HδL0.
    - apply b5dM_real_const_pos. exact H112T. }
  assert (HB0 : real_lt real_zero B).
  { unfold B. apply b5dK_real_mult_positive_exp.
    - exact Heps.
    - apply b5dM_real_const_pos. exact HkLT. }
  assert (HC0 : real_lt real_zero C).
  { unfold C. apply b5dM_real_const_pos. exact H12T. }
  assert (Hδg0 : real_lt real_zero δg).
  { unfold δg. apply real_min_pos.
    { apply real_min_pos.
      { exact HA0. }
      { exact HB0. } }
    { exact HC0. } }
  exists δg. split.
  { exact Hδg0. }
  { intros h Hhδ eps' Heps'.
    (* min-extract：|h| < A、|h| < B、|h| < C *)
    assert (HhAB : real_lt (real_abs h) (real_min A B)).
    { apply (real_min_lt_l h (real_min A B) C).
      unfold δg in Hhδ. exact Hhδ. }
    assert (HhA : real_lt (real_abs h) A).
    { apply (real_min_lt_l h A B). exact HhAB. }
    assert (HhB : real_lt (real_abs h) B).
    { apply (real_min_lt_r h A B). exact HhAB. }
    assert (HhC : real_lt (real_abs h) C).
    { apply (real_min_lt_r h (real_min A B) C).
      unfold δg in Hhδ. exact Hhδ. }
    (* 激活：|Δu| < δL（b5f_Du_act_delta） *)
    assert (Hact : real_lt (real_abs (b5f_Du x h)) δL).
    { apply (b5f_Du_act_delta r Hr0 Hr1 x Hxr h δL HδL0).
      - unfold A in HhA. exact HhA.
      - unfold C in HhC. exact HhC. }
    (* LogErr eps-delta：epsL'' := eps'·k2p *)
    set (epsL'' := real_mult eps' (real_const k2p)).
    assert (HepsL'' : real_lt real_zero epsL'').
    { unfold epsL''. apply b5dK_real_mult_positive_exp.
      - exact Heps'.
      - apply b5dM_real_const_pos. exact Hk2p. }
    assert (Hlog : real_le (real_abs (b5f_LogErr x h))
                    (real_plus (real_mult epsL (real_abs (b5f_Du x h))) epsL'')).
    { exact (HδL h epsL'' HepsL'' Hact). }
    (* b5i 桥：逐点 |LogErr_n| ≤ B_n + sh_n（sh := epsL''） *)
    destruct (b5i_abs_le_pointwise (b5f_LogErr x h)
               (real_plus (real_mult epsL (real_abs (b5f_Du x h))) epsL'')
               Hlog epsL'' HepsL'') as [Nlog HNlog].
    (* 见证分解 *)
    destruct Heps as [e0 [He0 [N0 HN0]]].
    destruct Heps' as [e0' [He0' [N0' HN0']]].
    destruct HhB as [eB [HeB [NB HNB]]].
    destruct HhC as [e1 [He1 [N1 HN1]]].
    destruct (b5dM_b5c_d_proj_le_one x) as [Nd Hd].
    set (N := Nat.max Nlog (Nat.max Nd (Nat.max N0 (Nat.max N0' (Nat.max NB N1))))).
    exists N.
    intros n Hn.
    apply NatLe_drop in Hn.
    assert (Hnlog : NatLe Nlog n) by (apply NatLe_lift; lia).
    assert (Hnd : (Nd <= n)%nat) by lia.
    assert (Hn0 : (N0 <= n)%nat) by lia.
    assert (Hn0' : (N0' <= n)%nat) by lia.
    assert (HnB : (NB <= n)%nat) by lia.
    assert (Hn1 : (N1 <= n)%nat) by lia.
    (* 逐点原子 *)
    set (hn := projT1 h n).
    set (sn := Qabs hn).
    set (en := projT1 eps n).
    set (en' := projT1 eps' n).
    set (dn := projT1 (b5a_atan_d x) n).
    set (Dn := Qabs (projT1 (b5f_Du x h) n)).
    set (wS := real_plus (b5f_v x h)
                        (real_opp (real_mult (real_mult x (b5a_atan_d x)) h))).
    set (D := real_plus (real_mult (real_const (1 / 2)) (b5f_LogErr x h))
                        (real_mult (real_const (1 / 2))
                                   (real_mult (b5a_atan_d x) (real_mult h h)))).
    (* |d_n| ≤ 1；en、en' ≥ 0（eps/eps' 见证） *)
    assert (Hd1 : Qle (Qabs dn) 1).
    { unfold dn. exact (Hd n Hnd). }
    assert (Hen0p : Qlt 0 en).
    { apply (Qlt_le_trans 0 e0 en).
      - apply QltT_to_Qlt. exact He0.
      - apply Qlt_le_weak.
        apply (Qlt_le_trans e0 (Qminus en (projT1 real_zero n)) en).
        + apply QltT_to_Qlt. exact (HN0 n (NatLe_lift _ _ Hn0)).
        + apply qeq_le.
          assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
          rewrite Hz. ring. }
    assert (Hen0 : Qle 0 en) by (apply Qlt_le_weak; exact Hen0p).
    assert (Hen'0p : Qlt 0 en').
    { apply (Qlt_le_trans 0 e0' en').
      - apply QltT_to_Qlt. exact He0'.
      - apply Qlt_le_weak.
        apply (Qlt_le_trans e0' (Qminus en' (projT1 real_zero n)) en').
        + apply QltT_to_Qlt. exact (HN0' n (NatLe_lift _ _ Hn0')).
        + apply qeq_le.
          assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
          rewrite Hz. ring. }
    assert (Hen'0 : Qle 0 en') by (apply Qlt_le_weak; exact Hen'0p).
    assert (Hk2p0 : Qle 0 k2p).
    { apply Qlt_le_weak. apply QltT_to_Qlt. exact Hk2p. }
    assert (Hk2p_en' : Qle 0 (Qmult k2p en')).
    { apply (Qmult_le_0_compat k2p en' Hk2p0 Hen'0). }
    (* |h_n| ≤ 1/2（HhC 见证逐点化） *)
    assert (Hs12 : Qle sn (1 # 2)).
    { apply (Qle_trans sn (Qminus (1 # 2) e1) (1 # 2)).
      - apply Qlt_le_weak.
        apply (q_lt_minus_shift e1 (1 # 2) sn).
        apply QltT_to_Qlt.
        apply (qltT_eq_compat_r (Qminus (1 # 2) sn)
                                (Qminus (projT1 C n) (projT1 (real_abs h) n))
                                e1).
        + unfold C. rewrite (real_const_proj (1 # 2) n).
          rewrite (real_abs_proj h n).
          unfold sn, hn. reflexivity.
        + exact (HN1 n (NatLe_lift _ _ Hn1)).
      - apply (Qle_trans (Qminus (1 # 2) e1) (Qplus (Qminus (1 # 2) e1) e1) (1 # 2)).
        + apply (Qle_plus_nonneg_r (Qminus (1 # 2) e1) e1).
          apply Qlt_le_weak. apply QltT_to_Qlt. exact He1.
        + apply qeq_imp_qle. ring. }
    (* |h_n| ≤ en·kL（HhB：|h| < eps·kL-Real 见证逐点化） *)
    assert (HsnL : Qle sn (Qmult en kL)).
    { apply (Qle_trans sn (Qminus (Qmult en kL) eB) (Qmult en kL)).
      - apply Qlt_le_weak.
        apply (q_lt_minus_shift eB (Qmult en kL) sn).
        apply QltT_to_Qlt.
        apply (qltT_eq_compat_r (Qminus (Qmult en kL) sn)
                                (Qminus (projT1 B n) (projT1 (real_abs h) n))
                                eB).
        + unfold B, en, sn, hn.
          setoid_rewrite (real_mult_proj eps (real_const kL) n).
          rewrite (real_const_proj kL n).
          rewrite (real_abs_proj h n).
          reflexivity.
        + exact (HNB n (NatLe_lift _ _ HnB)).
      - apply (Qle_trans (Qminus (Qmult en kL) eB)
                         (Qplus (Qminus (Qmult en kL) eB) eB)
                         (Qmult en kL)).
        + apply (Qle_plus_nonneg_r (Qminus (Qmult en kL) eB) eB).
          apply Qlt_le_weak. apply QltT_to_Qlt. exact HeB.
        + apply qeq_imp_qle. ring. }
    (* |Δu_n| ≤ 3·sn（b5f_Du_abs_pts + 2r+1/2 ≤ 3） *)
    assert (HD3 : Qle Dn (Qmult 3 sn)).
    { set (C0q := Qplus (Qmult 2 r) (1 # 2)).
      assert (HC0le3 : Qle C0q 3).
      { unfold C0q. nra. }
      apply (Qle_trans Dn (Qmult C0q sn) (Qmult 3 sn)).
      - unfold Dn.
        apply (b5f_Du_abs_pts r x Hxr h n).
        exact Hs12.
      - apply (Qmult_le_compat_r C0q 3 sn).
        + exact HC0le3.
        + unfold sn. apply Qabs_nonneg. }
    (* P1：|LogErr_n| ≤ en·kL·Dn + 2k2p·en'（b5i + 投影 ring） *)
    assert (P1 : Qle (Qabs (projT1 (b5f_LogErr x h) n))
                     (Qplus (Qmult (Qmult en kL) Dn)
                            (Qmult (Qmult 2 k2p) en'))).
    { apply (Qle_trans (Qabs (projT1 (b5f_LogErr x h) n))
                       (Qplus (projT1 (real_plus (real_mult epsL (real_abs (b5f_Du x h))) epsL'') n)
                              (projT1 epsL'' n))
                       (Qplus (Qmult (Qmult en kL) Dn)
                              (Qmult (Qmult 2 k2p) en'))).
      - exact (HNlog n Hnlog).
      - apply qeq_imp_qle.
        setoid_rewrite (real_plus_proj (real_mult epsL (real_abs (b5f_Du x h))) epsL'' n).
        setoid_rewrite (real_mult_proj epsL (real_abs (b5f_Du x h)) n).
        unfold epsL.
        setoid_rewrite (real_mult_proj eps (real_const kL) n).
        rewrite (real_const_proj kL n).
        setoid_rewrite (real_abs_proj (b5f_Du x h) n).
        unfold epsL''.
        setoid_rewrite (real_mult_proj eps' (real_const k2p) n).
        rewrite (real_const_proj k2p n).
        cbn [projT1].
        unfold en, en', Dn. ring. }
    (* HX：LogErr 半量逐点界（P1 × (1#2)，Δu ≤ 3sn 代入） *)
    assert (HXraw : Qle (Qmult (1 # 2) (Qabs (projT1 (b5f_LogErr x h) n)))
                        (Qplus (Qmult (1 # 2) (Qmult (Qmult en kL) Dn))
                               (Qmult (1 # 2) (Qmult (Qmult 2 k2p) en')))).
    { apply (Qle_trans (Qmult (1 # 2) (Qabs (projT1 (b5f_LogErr x h) n)))
                       (Qmult (Qabs (projT1 (b5f_LogErr x h) n)) (1 # 2))
                       (Qplus (Qmult (1 # 2) (Qmult (Qmult en kL) Dn))
                              (Qmult (1 # 2) (Qmult (Qmult 2 k2p) en')))).
      - apply qeq_imp_qle. ring.
      - { apply (Qle_trans (Qmult (Qabs (projT1 (b5f_LogErr x h) n)) (1 # 2))
                           (Qmult (Qplus (Qmult (Qmult en kL) Dn)
                                         (Qmult (Qmult 2 k2p) en')) (1 # 2))
                           (Qplus (Qmult (1 # 2) (Qmult (Qmult en kL) Dn))
                                  (Qmult (1 # 2) (Qmult (Qmult 2 k2p) en')))).
          { apply (Qmult_le_compat_r (Qabs (projT1 (b5f_LogErr x h) n))
                                     (Qplus (Qmult (Qmult en kL) Dn)
                                            (Qmult (Qmult 2 k2p) en'))
                                     (1 # 2)).
            { exact P1. }
            { change (Qle 0 (1 # 2)). unfold Qle. simpl. lia. } }
          { apply qeq_imp_qle. ring. } } }
    assert (HXstep : Qle (Qplus (Qmult (1 # 2) (Qmult (Qmult en kL) Dn))
                                (Qmult (1 # 2) (Qmult (Qmult 2 k2p) en')))
                         (Qplus (Qmult (1 # 2) (Qmult (Qmult en kL) (Qmult 3 sn)))
                                (Qmult (1 # 2) (Qmult (Qmult 2 k2p) en')))).
    { apply Qplus_le_compat.
      - { set (c := Qmult (1 # 2) (Qmult en kL)).
          assert (HenkL : Qle 0 (Qmult en kL)).
          { apply (Qmult_le_0_compat en kL Hen0 HkL0). }
          assert (Hc0 : Qle 0 c).
          { unfold c. apply (Qmult_le_0_compat (1 # 2) (Qmult en kL)).
            - change (Qle 0 (1 # 2)). unfold Qle. simpl. lia.
            - exact HenkL. }
          apply (Qle_trans (Qmult (1 # 2) (Qmult (Qmult en kL) Dn))
                           (Qmult Dn c)
                           (Qmult (1 # 2) (Qmult (Qmult en kL) (Qmult 3 sn)))).
          { unfold c. apply qeq_imp_qle. ring. }
          { apply (Qle_trans (Qmult Dn c)
                             (Qmult (Qmult 3 sn) c)
                             (Qmult (1 # 2) (Qmult (Qmult en kL) (Qmult 3 sn)))).
            { apply (Qmult_le_compat_r Dn (Qmult 3 sn) c).
              { unfold Dn. exact HD3. }
              { exact Hc0. } }
            { unfold c. apply qeq_imp_qle. ring. } } }
      - apply Qle_refl. }
    assert (HX : Qle (Qmult (1 # 2) (Qabs (projT1 (b5f_LogErr x h) n)))
                     (Qplus (Qmult (1 # 2) (Qmult (Qmult en kL) (Qmult 3 sn)))
                            (Qmult (1 # 2) (Qmult (Qmult 2 k2p) en')))).
    { apply (Qle_trans (Qmult (1 # 2) (Qabs (projT1 (b5f_LogErr x h) n)))
                       (Qplus (Qmult (1 # 2) (Qmult (Qmult en kL) Dn))
                              (Qmult (1 # 2) (Qmult (Qmult 2 k2p) en')))
                       (Qplus (Qmult (1 # 2) (Qmult (Qmult en kL) (Qmult 3 sn)))
                              (Qmult (1 # 2) (Qmult (Qmult 2 k2p) en')))).
      - exact HXraw.
      - exact HXstep. }
    (* HY：d·h² 半量逐点界（|d_n| ≤ 1 + |h_n| ≤ en·kL） *)
    assert (Hsn0 : Qle 0 sn).
    { unfold sn. apply Qabs_nonneg. }
    assert (HYp : Qle (Qmult (Qabs dn) (Qmult sn sn)) (Qmult (Qmult en kL) sn)).
    { apply (Qle_trans (Qmult (Qabs dn) (Qmult sn sn))
                       (Qmult sn sn)
                       (Qmult (Qmult en kL) sn)).
      - { apply (Qle_trans (Qmult (Qabs dn) (Qmult sn sn))
                           (Qmult 1 (Qmult sn sn))
                           (Qmult sn sn)).
          { apply (Qmult_le_compat_r (Qabs dn) 1 (Qmult sn sn)).
            { exact Hd1. }
            { apply (Qmult_le_0_compat sn sn Hsn0 Hsn0). } }
          { apply qeq_imp_qle. ring. } }
      - apply (Qmult_le_compat_r sn (Qmult en kL) sn).
        + exact HsnL.
        + exact Hsn0. }
    assert (HY : Qle (Qmult (1 # 2) (Qmult (Qabs dn) (Qmult sn sn)))
                     (Qmult (1 # 2) (Qmult (Qmult en kL) sn))).
    { apply (Qle_trans (Qmult (1 # 2) (Qmult (Qabs dn) (Qmult sn sn)))
                       (Qmult (Qmult (Qabs dn) (Qmult sn sn)) (1 # 2))
                       (Qmult (1 # 2) (Qmult (Qmult en kL) sn))).
      - apply qeq_imp_qle. ring.
      - { apply (Qle_trans (Qmult (Qmult (Qabs dn) (Qmult sn sn)) (1 # 2))
                           (Qmult (Qmult (Qmult en kL) sn) (1 # 2))
                           (Qmult (1 # 2) (Qmult (Qmult en kL) sn))).
          { apply (Qmult_le_compat_r (Qmult (Qabs dn) (Qmult sn sn))
                                     (Qmult (Qmult en kL) sn)
                                     (1 # 2)).
            { exact HYp. }
            { change (Qle 0 (1 # 2)). unfold Qle. simpl. lia. } }
          { apply qeq_imp_qle. ring. } } }
    (* 逐点恒等：wS_n == D_n == (1#2)·LogErr_n + (1#2)·d_n·h_n²（投影就地重证） *)
    assert (F0 : projT1 wS n == projT1 D n).
    { unfold wS, D, b5f_v, b5f_g, b5f_LogErr, b5f_u, b5f_Du.
      repeat (setoid_rewrite real_plus_proj || setoid_rewrite real_mult_proj ||
              setoid_rewrite real_opp_proj).
      cbn [projT1 real_const real_one real_zero].
      field. }
    assert (F1 : projT1 D n ==
             Qplus (Qmult (1 # 2) (projT1 (b5f_LogErr x h) n))
                   (Qmult (1 # 2) (Qmult (projT1 (b5a_atan_d x) n)
                                         (Qmult (projT1 h n) (projT1 h n))))).
    { unfold D.
      setoid_rewrite (real_plus_proj (real_mult (real_const (1 / 2)) (b5f_LogErr x h))
                                     (real_mult (real_const (1 / 2))
                                                (real_mult (b5a_atan_d x) (real_mult h h))) n).
      setoid_rewrite (real_mult_proj (real_const (1 / 2)) (b5f_LogErr x h) n).
      setoid_rewrite (real_mult_proj (real_const (1 / 2))
                                     (real_mult (b5a_atan_d x) (real_mult h h)) n).
      rewrite (real_const_proj (1 / 2) n).
      setoid_rewrite (real_mult_proj (b5a_atan_d x) (real_mult h h) n).
      setoid_rewrite (real_mult_proj h h n).
      cbn [projT1].
      setoid_rewrite Hhalf.
      reflexivity. }
    set (atom := Qplus (Qmult (1 # 2) (projT1 (b5f_LogErr x h) n))
                       (Qmult (1 # 2) (Qmult (projT1 (b5a_atan_d x) n)
                                             (Qmult (projT1 h n) (projT1 h n))))).
    assert (HwSabs : Qeq (Qabs (projT1 wS n)) (Qabs atom)).
    { apply (Qabs_wd (projT1 wS n) atom).
      apply (Qeq_trans (projT1 wS n) (projT1 D n) atom).
      - exact F0.
      - exact F1. }
    (* 三角拆分：|a+b| ≤ |a| + |b|，|(1#2)·x| == (1#2)·|x| *)
    assert (Hq1 : Qeq (Qabs (Qmult (1 # 2) (projT1 (b5f_LogErr x h) n)))
                      (Qmult (1 # 2) (Qabs (projT1 (b5f_LogErr x h) n)))).
    { apply (Qeq_trans (Qabs (Qmult (1 # 2) (projT1 (b5f_LogErr x h) n)))
                       (Qmult (Qabs (1 # 2)) (Qabs (projT1 (b5f_LogErr x h) n)))
                       (Qmult (1 # 2) (Qabs (projT1 (b5f_LogErr x h) n)))).
      - apply (Qabs_Qmult (1 # 2) (projT1 (b5f_LogErr x h) n)).
      - apply (Qmult_comp (Qabs (1 # 2)) (1 # 2)).
        + apply (Qabs_pos (1 # 2)). change (Qle 0 (1 # 2)). unfold Qle. simpl. lia.
        + reflexivity. }
    assert (Hq2 : Qeq (Qabs (Qmult (1 # 2) (Qmult (projT1 (b5a_atan_d x) n)
                                                (Qmult (projT1 h n) (projT1 h n)))))
                      (Qmult (1 # 2) (Qmult (Qabs (projT1 (b5a_atan_d x) n))
                                            (Qmult (Qabs (projT1 h n)) (Qabs (projT1 h n)))))).
    { apply (Qeq_trans (Qabs (Qmult (1 # 2) (Qmult (projT1 (b5a_atan_d x) n)
                                                  (Qmult (projT1 h n) (projT1 h n)))))
                       (Qmult (Qabs (1 # 2))
                              (Qabs (Qmult (projT1 (b5a_atan_d x) n)
                                           (Qmult (projT1 h n) (projT1 h n)))))
                       (Qmult (1 # 2) (Qmult (Qabs (projT1 (b5a_atan_d x) n))
                                             (Qmult (Qabs (projT1 h n)) (Qabs (projT1 h n)))))).
      - apply (Qabs_Qmult (1 # 2)
                          (Qmult (projT1 (b5a_atan_d x) n) (Qmult (projT1 h n) (projT1 h n)))).
      - apply (Qmult_comp (Qabs (1 # 2)) (1 # 2)).
        + apply (Qabs_pos (1 # 2)). change (Qle 0 (1 # 2)). unfold Qle. simpl. lia.
        + { apply (Qeq_trans (Qabs (Qmult (projT1 (b5a_atan_d x) n)
                                          (Qmult (projT1 h n) (projT1 h n))))
                             (Qmult (Qabs (projT1 (b5a_atan_d x) n))
                                    (Qabs (Qmult (projT1 h n) (projT1 h n))))
                             (Qmult (Qabs (projT1 (b5a_atan_d x) n))
                                    (Qmult (Qabs (projT1 h n)) (Qabs (projT1 h n))))).
            { apply (Qabs_Qmult (projT1 (b5a_atan_d x) n)
                                (Qmult (projT1 h n) (projT1 h n))). }
            { apply (Qmult_comp (Qabs (projT1 (b5a_atan_d x) n))
                                (Qabs (projT1 (b5a_atan_d x) n))).
              - reflexivity.
              - apply (Qabs_Qmult (projT1 h n) (projT1 h n)). } } }
    assert (Htri : Qle (Qabs atom)
                       (Qplus (Qmult (1 # 2) (Qabs (projT1 (b5f_LogErr x h) n)))
                              (Qmult (1 # 2) (Qmult (Qabs (projT1 (b5a_atan_d x) n))
                                                    (Qmult (Qabs (projT1 h n)) (Qabs (projT1 h n))))))).
    { apply (Qle_trans (Qabs atom)
                       (Qplus (Qabs (Qmult (1 # 2) (projT1 (b5f_LogErr x h) n)))
                              (Qabs (Qmult (1 # 2) (Qmult (projT1 (b5a_atan_d x) n)
                                                          (Qmult (projT1 h n) (projT1 h n))))))
                       (Qplus (Qmult (1 # 2) (Qabs (projT1 (b5f_LogErr x h) n)))
                              (Qmult (1 # 2) (Qmult (Qabs (projT1 (b5a_atan_d x) n))
                                                    (Qmult (Qabs (projT1 h n)) (Qabs (projT1 h n))))))).
      - unfold atom. apply Qabs_triangle.
      - apply qeq_imp_qle.
        apply (Qplus_comp (Qabs (Qmult (1 # 2) (projT1 (b5f_LogErr x h) n)))
                          (Qmult (1 # 2) (Qabs (projT1 (b5f_LogErr x h) n)))).
        + exact Hq1.
        + exact Hq2. }
    (* 主链：|wS_n| ≤ |atom| ≤ 预算和 ≤ en·k2·sn + 2k2p·en'（nra） *)
    apply (Qle_trans (Qabs (projT1 wS n))
                     (Qabs atom)
                     (Qplus (Qmult (Qmult (projT1 eps n) k2) (Qabs (projT1 h n)))
                            (Qmult (Qmult 2 k2p) (projT1 eps' n)))).
    { apply qeq_imp_qle. exact HwSabs. }
    { apply (Qle_trans (Qabs atom)
                       (Qplus (Qmult (1 # 2) (Qabs (projT1 (b5f_LogErr x h) n)))
                              (Qmult (1 # 2) (Qmult (Qabs (projT1 (b5a_atan_d x) n))
                                                    (Qmult (Qabs (projT1 h n)) (Qabs (projT1 h n))))))
                       (Qplus (Qmult (Qmult (projT1 eps n) k2) (Qabs (projT1 h n)))
                              (Qmult (Qmult 2 k2p) (projT1 eps' n)))).
      - exact Htri.
      - { unfold en, en', sn, hn, dn, kL in HX, HY, Hk2p_en'.
          unfold en, en', sn, hn, dn, kL.
          nra. } }
    }
Defined.

(* ============================================================ *)
(* 主件 ② b5dK_exp_part_bound_closed_r_exp（Defined 透明）      *)
(* 拷贝源：213 根 b5a_S_exp_part_bound_closed_r（Constructive-  *)
(*   World.v L84306–84653，348 行切片机器抽取零手抄；⚠️ L83581  *)
(*   为注释草案语句，真定义 L84306 起）；语句逐字。            *)
(* 变更项：① Lemma 头改名 ② LogErr 叶                          *)
(*   b5f_LogErr_delta → 上游 item20 b5dJ_LogErr_delta_exp（同参  *)
(*   调用 x (real_const b5j_kL) HkLpos）③ δlin 源               *)
(*   exp_minus_one_linear → 本文件 H3 b5dK_exp_minus_one_linear *)
(*   _closed_exp（destruct 多一重 Hδeq 分量——H3 语句含 real_eq  *)
(*   首分量）④ invM 证书 real_abs_plus_one_pos → 本文件 H2      *)
(*   b5dK_real_abs_plus_one_pos_exp（real_inv_pos 值按见证      *)
(*   destruct 出 N0——值路径必换）⑤ real_mult_positive → H1    *)
(*   ⑥ real_const_pos → 上游 item23 b5dM_real_const_pos ⑦ 末闭式  *)
(*   real_abs_scaling_le → 本文件 H4 b5dK_real_abs_scaling_le_exp *)
(*   （根件语句硬编码根 real_abs_plus_one_pos 见证名——invM 换 H2 *)
(*   后不可直接应用，同形换见证名拷贝）⑧ 收尾 Qed→Defined。     *)
(* 值路径：delta := min(min(δlin·(1#4), δL·(1#12)), (1#2))，    *)
(*   δlin := projT1 (H3 eps0 Heps0)（闭式 min((1#2), eps0·      *)
(*   (1#4))），eps0 := eps·(Qinv (b5j_Kvq r))·invM，invM :=      *)
(*   real_inv_pos (1+|Sx|) (H2 Sx)，Sx := b5a_S x——全透明链     *)
(*   （H3/H2 Defined；b5a_S/cauchy_real_exp 透明；exp_partial 0 *)
(*   基底 1%Q 免 log_seq/approx_root 求值）⟹ delta 首投影可算。*)
(* ============================================================ *)
Lemma b5dK_exp_part_bound_closed_r_exp :
  forall (r : Q) (Hr0 : Qle 0 r) (Hr1 : Qlt r 1),
  forall (x : Real) (Hxr : forall n : nat, QleT' (Qabs (projT1 x n)) r),
  forall (eps : Real), real_lt real_zero eps ->
  sigT (fun delta : Real => And (real_lt real_zero delta)
    (forall (h : Real), real_lt (real_abs h) delta ->
      forall (eps' : Real), real_lt real_zero eps' ->
      real_le (real_abs (real_mult (b5a_S x)
                 (real_plus (cauchy_real_exp (b5f_v x h))
                            (real_opp (real_plus real_one (b5f_v x h))))))
              (real_plus (real_mult eps (real_abs h)) eps'))).
Proof.
  intros r Hr0 Hr1 x Hxr eps Heps.
  set (Sx := b5a_S x).
  set (invM := real_inv_pos (real_plus real_one (real_abs Sx)) (b5dK_real_abs_plus_one_pos_exp Sx)).
  set (eps0 := real_mult (real_mult eps (real_const (Qinv (b5j_Kvq r)))) invM).
  (* 正性件 *)
  assert (HKqinvT : QltT 0 (Qinv (b5j_Kvq r))).
  { apply Qlt_to_QltT. apply Qinv_lt_0_compat. exact (b5j_Kvq_pos r Hr0). }
  assert (HinvM0 : real_lt real_zero invM).
  { unfold invM. apply (real_inv_pos_pos (real_plus real_one (real_abs Sx)) (b5dK_real_abs_plus_one_pos_exp Sx)). }
  assert (Heps0 : real_lt real_zero eps0).
  { unfold eps0. apply b5dK_real_mult_positive_exp.
    - apply b5dK_real_mult_positive_exp.
      + exact Heps.
      + apply b5dM_real_const_pos. exact HKqinvT.
    - exact HinvM0. }
  assert (Heps0le : real_le real_zero eps0).
  { apply (RealSetoid.real_lt_le_iff_req real_zero eps0). left. exact Heps0. }
  assert (HkLpos : real_lt real_zero (real_const b5j_kL)).
  { apply b5dM_real_const_pos. exact b5j_kL_posT. }
  destruct (b5dJ_LogErr_delta_exp x (real_const b5j_kL) HkLpos) as [δL [HδL0 HδL]].
  destruct (b5dK_exp_minus_one_linear_closed_exp eps0 Heps0) as [δlin [Hδeq [Hδlin0 Hδlin]]].
  set (A := real_mult δlin (real_const (1 # 4))).
  set (B := real_mult δL (real_const (1 # 12))).
  set (C := real_const (1 # 2)).
  set (delta := real_min (real_min A B) C).
  assert (H14T : QltT 0 (1 # 4)).
  { apply Qlt_to_QltT. change (Qlt 0 (1 # 4)). unfold Qlt. simpl. lia. }
  assert (H112T : QltT 0 (1 # 12)).
  { apply Qlt_to_QltT. change (Qlt 0 (1 # 12)). unfold Qlt. simpl. lia. }
  assert (H12T : QltT 0 (1 # 2)).
  { apply Qlt_to_QltT. change (Qlt 0 (1 # 2)). unfold Qlt. simpl. lia. }
  assert (HA0 : real_lt real_zero A).
  { unfold A. apply b5dK_real_mult_positive_exp.
    - exact Hδlin0.
    - apply b5dM_real_const_pos. exact H14T. }
  assert (HB0 : real_lt real_zero B).
  { unfold B. apply b5dK_real_mult_positive_exp.
    - exact HδL0.
    - apply b5dM_real_const_pos. exact H112T. }
  assert (HC0 : real_lt real_zero C).
  { unfold C. apply b5dM_real_const_pos. exact H12T. }
  assert (Hdelta0 : real_lt real_zero delta).
  { unfold delta. apply real_min_pos.
    - apply real_min_pos.
      + exact HA0.
      + exact HB0.
    - exact HC0. }
  exists delta.
  split.
  - exact Hdelta0.
  - intros h Hhδ eps' Heps'.
    assert (HhAB : real_lt (real_abs h) (real_min A B)).
    { apply (real_min_lt_l h (real_min A B) C). unfold delta in Hhδ. exact Hhδ. }
    assert (HhA : real_lt (real_abs h) A).
    { apply (real_min_lt_l h A B). exact HhAB. }
    assert (HhB : real_lt (real_abs h) B).
    { apply (real_min_lt_r h A B). exact HhAB. }
    assert (HhC : real_lt (real_abs h) C).
    { apply (real_min_lt_r h (real_min A B) C). unfold delta in Hhδ. exact Hhδ. }
    assert (HactDu : real_lt (real_abs (b5f_Du x h)) δL).
    { apply (b5f_Du_act_delta r Hr0 Hr1 x Hxr h δL HδL0).
      - unfold B in HhB. exact HhB.
      - unfold C in HhC. exact HhC. }
    assert (HlogS : forall (epsL' : Real), real_lt real_zero epsL' ->
        real_le (real_abs (b5f_LogErr x h))
                (real_plus (real_mult (real_const b5j_kL) (real_abs (b5f_Du x h))) epsL')).
    { intros epsL' HepsL'. exact (HδL h epsL' HepsL' HactDu). }
    assert (Hvlt : real_lt (real_abs (b5f_v x h)) δlin).
    { apply (b5j_v_act_lt r Hr0 Hr1 x Hxr h δlin Hδlin0 HlogS).
      - unfold A in HhA. exact HhA.
      - unfold C in HhC. exact HhC. }
    (* eps0' := (3#4)·(eps'·invM)；shV := invE·((1#4)·Kvq-const)·eps' *)
    set (eps0' := real_mult (real_const (3 # 4)) (real_mult eps' invM)).
    set (invE := real_inv_pos eps Heps).
    set (shV := real_mult (real_mult invE (real_const (Qmult (1 # 4) (b5j_Kvq r)))) eps').
    assert (H34T : QltT 0 (3 # 4)).
    { apply Qlt_to_QltT. change (Qlt 0 (3 # 4)). unfold Qlt. simpl. lia. }
    assert (H14KvT : QltT 0 (Qmult (1 # 4) (b5j_Kvq r))).
    { apply Qlt_to_QltT.
      apply (Qmult_lt_0_compat (1 # 4) (b5j_Kvq r)).
      - change (Qlt 0 (1 # 4)). unfold Qlt. simpl. lia.
      - exact (b5j_Kvq_pos r Hr0). }
    assert (HinvE0 : real_lt real_zero invE).
    { unfold invE. apply (real_inv_pos_pos eps Heps). }
    assert (Heps0' : real_lt real_zero eps0').
    { unfold eps0'. apply b5dK_real_mult_positive_exp.
      - apply b5dM_real_const_pos. exact H34T.
      - apply b5dK_real_mult_positive_exp.
        + exact Heps'.
        + exact HinvM0. }
    assert (HshV : real_lt real_zero shV).
    { unfold shV. apply b5dK_real_mult_positive_exp.
      - apply b5dK_real_mult_positive_exp.
        + exact HinvE0.
        + apply b5dM_real_const_pos. exact H14KvT.
      - exact Heps'. }
    (* 斜率实例：|v| ≤ Kvqc·|h| + shV *)
    assert (Hvslope : real_le (real_abs (b5f_v x h))
                              (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV)).
    { apply (b5j_v_abs_bd r Hr0 Hr1 x Hxr h shV HshV HlogS).
      unfold C in HhC. exact HhC. }
    (* |LinE(v)| ≤ eps0·|v| + eps0'（exp 线性化实例 @ b5f_v x h） *)
    assert (Hlin : real_le
        (real_abs (real_plus (cauchy_real_exp (b5f_v x h))
                             (real_opp (real_plus real_one (b5f_v x h)))))
        (real_plus (real_mult eps0 (real_abs (b5f_v x h))) eps0')).
    { apply (real_le_trans
               (real_abs (real_plus (cauchy_real_exp (b5f_v x h))
                                    (real_opp (real_plus real_one (b5f_v x h)))))
               (real_abs (real_plus (real_plus (cauchy_real_exp (b5f_v x h)) (real_opp real_one))
                                    (real_opp (b5f_v x h))))
               (real_plus (real_mult eps0 (real_abs (b5f_v x h))) eps0')).
      - apply RealSetoid.real_eq_le.
        apply (real_abs_eq_compat
                 (real_plus (cauchy_real_exp (b5f_v x h))
                            (real_opp (real_plus real_one (b5f_v x h))))
                 (real_plus (real_plus (cauchy_real_exp (b5f_v x h)) (real_opp real_one))
                            (real_opp (b5f_v x h)))).
        apply (b5j_lin_shape_eq (b5f_v x h)).
      - apply (Hδlin (b5f_v x h) Hvlt eps0' Heps0'). }
    (* eps0·|v| ≤ eps0·(Kvqc·|h| + shV)（real_le_mult_compat_weak + comm 桥） *)
    assert (Hmulv : real_le (real_mult eps0 (real_abs (b5f_v x h)))
                            (real_mult eps0
                               (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV))).
    { apply (real_le_trans (real_mult eps0 (real_abs (b5f_v x h)))
                           (real_mult (real_abs (b5f_v x h)) eps0)
                           (real_mult eps0
                              (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV))).
      - apply RealSetoid.real_eq_le.
        apply (real_mult_comm eps0 (real_abs (b5f_v x h))).
      - apply (real_le_trans (real_mult (real_abs (b5f_v x h)) eps0)
                             (real_mult (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV) eps0)
                             (real_mult eps0
                                (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV))).
        + apply (real_le_mult_compat_weak (real_abs (b5f_v x h))
                                          (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV)
                                          eps0).
          * exact Heps0le.
          * exact Hvslope.
        + apply RealSetoid.real_eq_le.
          apply (real_mult_comm (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV) eps0). }
    (* |LinE| ≤ eps0·(Kvqc·|h|+shV) + eps0' *)
    assert (Hlin2 : real_le
        (real_abs (real_plus (cauchy_real_exp (b5f_v x h))
                             (real_opp (real_plus real_one (b5f_v x h)))))
        (real_plus (real_mult eps0
                     (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV))
                   eps0')).
    { apply (real_le_trans
               (real_abs (real_plus (cauchy_real_exp (b5f_v x h))
                                    (real_opp (real_plus real_one (b5f_v x h)))))
               (real_plus (real_mult eps0 (real_abs (b5f_v x h))) eps0')
               (real_plus (real_mult eps0
                            (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV))
                          eps0')).
      - exact Hlin.
      - apply (real_le_plus_compat
                 (real_mult eps0 (real_abs (b5f_v x h)))
                 (real_mult eps0 (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV))
                 eps0' eps0').
        + exact Hmulv.
        + apply real_le_refl. }
    (* |Sx·LinE| == |Sx|·|LinE| ≤ |Sx|·(eps0·(Kvqc·|h|+shV) + eps0') *)
    assert (Hmid1 : real_le
        (real_mult (real_abs Sx)
           (real_abs (real_plus (cauchy_real_exp (b5f_v x h))
                                (real_opp (real_plus real_one (b5f_v x h))))))
        (real_mult (real_abs Sx)
           (real_plus (real_mult eps0
                        (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV))
                      eps0'))).
    { apply (real_le_trans
               (real_mult (real_abs Sx)
                  (real_abs (real_plus (cauchy_real_exp (b5f_v x h))
                                       (real_opp (real_plus real_one (b5f_v x h))))))
               (real_mult (real_abs (real_plus (cauchy_real_exp (b5f_v x h))
                                               (real_opp (real_plus real_one (b5f_v x h)))))
                          (real_abs Sx))
               (real_mult (real_abs Sx)
                  (real_plus (real_mult eps0
                               (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV))
                             eps0'))).
      - apply RealSetoid.real_eq_le.
        apply (real_mult_comm (real_abs Sx)
               (real_abs (real_plus (cauchy_real_exp (b5f_v x h))
                                    (real_opp (real_plus real_one (b5f_v x h)))))).
      - apply (real_le_trans
                 (real_mult (real_abs (real_plus (cauchy_real_exp (b5f_v x h))
                                                 (real_opp (real_plus real_one (b5f_v x h)))))
                            (real_abs Sx))
                 (real_mult (real_plus (real_mult eps0
                              (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV))
                            eps0')
                            (real_abs Sx))
                 (real_mult (real_abs Sx)
                    (real_plus (real_mult eps0
                                 (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV))
                               eps0'))).
        + apply (real_le_mult_compat_weak
                   (real_abs (real_plus (cauchy_real_exp (b5f_v x h))
                                        (real_opp (real_plus real_one (b5f_v x h)))))
                   (real_plus (real_mult eps0
                                (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV))
                              eps0')
                   (real_abs Sx)).
          * apply (RealSetoid.real_lt_le_iff_req real_zero (real_abs Sx)).
            left. unfold Sx. exact (b5j_Sx_abs_pos x).
          * exact Hlin2.
        + apply RealSetoid.real_eq_le.
          apply (real_mult_comm
                   (real_plus (real_mult eps0
                                (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV))
                              eps0')
                   (real_abs Sx)). }
    (* 重塑：|Sx|·(eps0·(Kvqc·|h|+shV) + eps0') == |Sx|·((eps·invM)·|h| + eps'·invM) *)
    assert (Hreshape : real_eq
        (real_mult (real_abs Sx)
           (real_plus (real_mult eps0
                        (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV))
                      eps0'))
        (real_mult (real_abs Sx)
           (real_plus (real_mult (real_mult eps invM) (real_abs h))
                      (real_mult eps' invM)))).
    { apply (RealSetoid.real_eq_mult_compat
               (real_abs Sx)
               (real_plus (real_mult eps0
                            (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV))
                          eps0')
               (real_abs Sx)
               (real_plus (real_mult (real_mult eps invM) (real_abs h))
                          (real_mult eps' invM))).
      - apply real_eq_refl.
      - (* 内层重塑：eps0·(Kvqc·|h|+shV) + eps0' == (eps·invM)·|h| + eps'·invM *)
        apply (real_eq_trans
                 (real_plus (real_mult eps0
                              (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV))
                            eps0')
                 (real_plus (real_plus (real_mult eps0 (real_mult (real_const (b5j_Kvq r)) (real_abs h)))
                                       (real_mult eps0 shV))
                            eps0')
                 (real_plus (real_mult (real_mult eps invM) (real_abs h))
                            (real_mult eps' invM))).
        + (* distr：eps0·(A+B) == eps0·A + eps0·B *)
          apply (RealSetoid.real_eq_plus_compat
                   (real_mult eps0
                      (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV))
                   eps0'
                   (real_plus (real_mult eps0 (real_mult (real_const (b5j_Kvq r)) (real_abs h)))
                              (real_mult eps0 shV))
                   eps0').
          * apply (b5j_mult_plus_distr_eq eps0
                     (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV).
          * apply real_eq_refl.
        + (* 重组到 T：assoc + E1 + E2 + eps0'-def + 常数和 *)
          apply (real_eq_trans
                   (real_plus (real_plus (real_mult eps0 (real_mult (real_const (b5j_Kvq r)) (real_abs h)))
                                         (real_mult eps0 shV))
                              eps0')
                   (real_plus (real_mult eps0 (real_mult (real_const (b5j_Kvq r)) (real_abs h)))
                              (real_plus (real_mult eps0 shV) eps0'))
                   (real_plus (real_mult (real_mult eps invM) (real_abs h))
                              (real_mult eps' invM))).
          * apply real_eq_sym.
            apply (real_plus_assoc
                     (real_mult eps0 (real_mult (real_const (b5j_Kvq r)) (real_abs h)))
                     (real_mult eps0 shV) eps0').
          * apply (RealSetoid.real_eq_plus_compat
                     (real_mult eps0 (real_mult (real_const (b5j_Kvq r)) (real_abs h)))
                     (real_plus (real_mult eps0 shV) eps0')
                     (real_mult (real_mult eps invM) (real_abs h))
                     (real_mult eps' invM)).
            -- (* eps0·(Kvqc·|h|) == (eps·invM)·|h|：assoc + E1 *)
               apply (real_eq_trans
                        (real_mult eps0 (real_mult (real_const (b5j_Kvq r)) (real_abs h)))
                        (real_mult (real_mult eps0 (real_const (b5j_Kvq r))) (real_abs h))
                        (real_mult (real_mult eps invM) (real_abs h))).
               ++ apply (real_mult_assoc eps0 (real_const (b5j_Kvq r)) (real_abs h)).
               ++ apply (RealSetoid.real_eq_mult_compat
                           (real_mult eps0 (real_const (b5j_Kvq r)))
                           (real_abs h)
                           (real_mult eps invM)
                           (real_abs h)).
                  ** unfold eps0. apply (b5j_eps0_kvq_req r Hr0 eps invM).
                  ** apply real_eq_refl.
            -- (* eps0·shV + eps0' == eps'·invM：E2 + 常数和 *)
               apply (real_eq_trans
                        (real_plus (real_mult eps0 shV) eps0')
                        (real_plus (real_mult (real_const (1 # 4)) (real_mult eps' invM))
                                   (real_mult (real_const (3 # 4)) (real_mult eps' invM)))
                        (real_mult eps' invM)).
               ++ apply (RealSetoid.real_eq_plus_compat
                           (real_mult eps0 shV)
                           eps0'
                           (real_mult (real_const (1 # 4)) (real_mult eps' invM))
                           (real_mult (real_const (3 # 4)) (real_mult eps' invM))).
                  ** unfold shV, invE.
                     apply (b5j_eps0_shv_req r Hr0 eps eps' invM Heps).
                  ** unfold eps0'.
                     apply real_eq_refl.
               ++ apply (b5j_fourth_threefourth_sum (real_mult eps' invM)). }
    apply (real_le_trans
             (real_abs (real_mult (b5a_S x)
                        (real_plus (cauchy_real_exp (b5f_v x h))
                                   (real_opp (real_plus real_one (b5f_v x h))))))
             (real_mult (real_abs Sx)
                (real_abs (real_plus (cauchy_real_exp (b5f_v x h))
                                     (real_opp (real_plus real_one (b5f_v x h))))))
             (real_plus (real_mult eps (real_abs h)) eps')).
    { apply RealSetoid.real_eq_le.
      apply (real_abs_mult_req (b5a_S x)
             (real_plus (cauchy_real_exp (b5f_v x h))
                        (real_opp (real_plus real_one (b5f_v x h))))). }
    { apply (real_le_trans
               (real_mult (real_abs Sx)
                  (real_abs (real_plus (cauchy_real_exp (b5f_v x h))
                                       (real_opp (real_plus real_one (b5f_v x h))))))
               (real_mult (real_abs Sx)
                  (real_plus (real_mult eps0
                               (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV))
                             eps0'))
               (real_plus (real_mult eps (real_abs h)) eps')).
      { exact Hmid1. }
      { apply (real_le_trans
                 (real_mult (real_abs Sx)
                    (real_plus (real_mult eps0
                                 (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV))
                               eps0'))
                 (real_mult (real_abs Sx)
                    (real_plus (real_mult (real_mult eps invM) (real_abs h))
                               (real_mult eps' invM)))
                 (real_plus (real_mult eps (real_abs h)) eps')).
        { apply RealSetoid.real_eq_le. exact Hreshape. }
        { apply (b5dK_real_abs_scaling_le_exp (b5a_S x) eps eps' h Heps Heps'). }
    }
    }
Defined.

(* ============================================================ *)
(* end sc2_b5a_item21.v · F1-δD2 item21 gdiff+exp-part 透明 Defined 拷贝 *)
(* ============================================================ *)

(* ============================================================ *)
(* 块 item6（前缀 b5d2_——主件 b5d2_sin_partial_abs_le1）——来源：演变/.ablation/sc2_parallel/sc2_b5a_ode/sc2_b5a_item6.v。 *)
(* ============================================================ *)

(* ============================================================ *)
(* §0 件清单（语句以规范 §2 表 + 审查报告 §3 为准；            *)
(*    编译通过即定稿）                                          *)
(*   M1  b5d2_ap_abs_le1 : forall (a : Q) (n : nat),            *)
(*        QleT' (Qabs a) 1 ->                                   *)
(*        Qle (Qabs (arctan_partial n a)) 1.                    *)
(*   M2  b5d2_sin_partial_abs_le1 : forall (n : nat) (q : Q),    *)
(*        QleT' (Qabs q) 1 ->                                   *)
(*        Qle (Qabs (sin_partial n q)) 1.                       *)
(*   M3  b5d2_cos_partial_abs_le1 : forall (n : nat) (q : Q),    *)
(*        QleT' (Qabs q) 1 ->                                   *)
(*        Qle (Qabs (cos_partial n q)) 1.                       *)
(*   M4  b5d2_sinA_abs_le1 : forall (x : Real)                  *)
(*          (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)  *)
(*          (n : nat),                                          *)
(*        Qle (Qabs (sin_partial n (arctan_partial n            *)
(*                                   (projT1 x n)))) 1.         *)
(*       b5d2_cosA_abs_le1 : 同上（cos_partial 替换）。          *)
(*   M5  b5d2_x0_sinA_le1 : forall n : nat,                     *)
(*        Qle (Qabs (sin_partial n (arctan_partial n            *)
(*                                   (projT1 (real_const 0) n)))) 1. *)
(*       b5d2_x0_cosA_le1 : 同上（cos_partial 替换）。           *)
(* ============================================================ *)

(* ============================================================ *)
(* §1 M1 b5d2_ap_abs_le1（arctan_partial 双向 |·| ≤ 1）         *)
(* 路线：x ∈ [0,1] 上交替级数夹逼 0 ≤ S_n(x) ≤ x（子列单调       *)
(*   偶 ↓ / 奇 ↑ + 奇在偶下 mix；建材 = 根 atan 族 atan_mag/     *)
(*   atan_mag_decr/atan_mag_nonneg + 符号恒等（本文件自建）），   *)
(*   负半轴经奇性 arctan_partial n (−x) == −arctan_partial n x。 *)
(* ============================================================ *)

(* ---- 值：arctan_term 0 x == x、arctan_partial 0 x == x ---- *)
Lemma b5d2_at_term0 : forall x : Q, arctan_term 0 x == x.
Proof.
  intro x.
  unfold arctan_term.
  replace (2 * 0 + 1)%nat with 1%nat by lia.
  unfold Qdiv. cbn [q_pow].
  change (Qinv (Z.of_nat 1 # 1)) with 1.
  simpl. ring.
Qed.

Lemma b5d2_ap0_x : forall x : Q, arctan_partial 0 x == x.
Proof.
  intro x.
  change (arctan_term 0 x == x).
  apply b5d2_at_term0.
Qed.

(* ---- 奇性（atan_term / arctan_partial） ---- *)
Lemma b5d2_at_term_neg : forall (k : nat) (x : Q), arctan_term k (- x) == - arctan_term k x.
Proof.
  intros k x.
  unfold arctan_term, Qdiv.
  replace (2 * k + 1)%nat with (Datatypes.S (2 * k))%nat by lia.
  rewrite (q_pow_neg_odd x k).
  ring.
Qed.

Lemma b5d2_ap_neg : forall (n : nat) (x : Q), arctan_partial n (- x) == - arctan_partial n x.
Proof.
  intros n x.
  induction n as [| n IH]; simpl.
  - apply b5d2_at_term_neg.
  - rewrite IH. rewrite (b5d2_at_term_neg (Datatypes.S n) x). ring.
Qed.

(* ---- 符号恒等（x ≥ 0）：奇指标项 == −c、偶指标项 == c ---- *)
Lemma b5d2_at_term_odd_neg : forall (m : nat) (x : Q), Qle 0 x ->
  arctan_term (Datatypes.S (2 * m)) x == - atan_mag (Datatypes.S (2 * m)) x.
Proof.
  intros m x Hx0.
  unfold arctan_term, atan_mag, Qdiv.
  rewrite (sc_qpow_odd_neg_m m).
  assert (Hp : q_pow x (2 * Datatypes.S (2 * m) + 1) ==
                q_pow (Qabs x) (2 * Datatypes.S (2 * m) + 1)).
  { apply (q_pow_wd x (Qabs x) (2 * Datatypes.S (2 * m) + 1)).
    apply Qeq_sym. apply Qabs_pos. exact Hx0. }
  rewrite Hp. ring.
Qed.

Lemma b5d2_at_term_even_pos : forall (m : nat) (x : Q), Qle 0 x ->
  arctan_term (Datatypes.S (Datatypes.S (2 * m))) x == atan_mag (Datatypes.S (Datatypes.S (2 * m))) x.
Proof.
  intros m x Hx0.
  unfold arctan_term, atan_mag, Qdiv.
  rewrite (sc_qpow_even_pos_m m).
  assert (Hp : q_pow x (2 * Datatypes.S (Datatypes.S (2 * m)) + 1) ==
                q_pow (Qabs x) (2 * Datatypes.S (Datatypes.S (2 * m)) + 1)).
  { apply (q_pow_wd x (Qabs x) (2 * Datatypes.S (Datatypes.S (2 * m)) + 1)).
    apply Qeq_sym. apply Qabs_pos. exact Hx0. }
  rewrite Hp. ring.
Qed.

(* ---- x ≥ 0 时 c_0 == x（atan_mag 0 x == x） ---- *)
Lemma b5d2_mag0_x : forall x : Q, Qle 0 x -> atan_mag 0 x == x.
Proof.
  intros x Hx0.
  unfold atan_mag.
  replace (2 * 0 + 1)%nat with 1%nat by lia.
  cbn [q_pow].
  unfold Qdiv.
  change (Qinv (Z.of_nat 1 # 1)) with 1.
  rewrite (Qabs_pos x Hx0).
  simpl. ring.
Qed.

(* ---- x ∈ [0,1] ⟹ QleT' (Qabs x) 1（内部推导辅助） ---- *)
Lemma b5d2_xle1T : forall x : Q, Qle 0 x -> Qle x 1 -> QleT' (Qabs x) 1.
Proof.
  intros x Hx0 Hx1.
  apply Qle_to_QleT'.
  apply (Qle_trans (Qabs x) x 1).
  - apply qeq_imp_qle. apply Qabs_pos. exact Hx0.
  - exact Hx1.
Qed.

(* ---- 子列单调：偶 ↓（S_{2m+2} ≤ S_{2m}） ---- *)
Lemma b5d2_ap_even_dec : forall (m : nat) (x : Q), Qle 0 x -> Qle x 1 ->
  Qle (arctan_partial (2 * Datatypes.S m) x) (arctan_partial (2 * m) x).
Proof.
  intros m x Hx0 Hx1.
  replace (2 * Datatypes.S m)%nat with (Datatypes.S (Datatypes.S (2 * m))) by lia.
  rewrite (arctan_partial_step2 (2 * m) x).
  rewrite (b5d2_at_term_odd_neg m x Hx0).
  rewrite (b5d2_at_term_even_pos m x Hx0).
  apply (proj2 (Qle_minus_iff
    (arctan_partial (2 * m) x + (- atan_mag (Datatypes.S (2 * m)) x) + atan_mag (Datatypes.S (Datatypes.S (2 * m))) x)
    (arctan_partial (2 * m) x))).
  assert (Heq : arctan_partial (2 * m) x -
    (arctan_partial (2 * m) x + (- atan_mag (Datatypes.S (2 * m)) x) + atan_mag (Datatypes.S (Datatypes.S (2 * m))) x) ==
    atan_mag (Datatypes.S (2 * m)) x - atan_mag (Datatypes.S (Datatypes.S (2 * m))) x) by ring.
  rewrite Heq.
  apply (proj1 (Qle_minus_iff (atan_mag (Datatypes.S (Datatypes.S (2 * m))) x)
                              (atan_mag (Datatypes.S (2 * m)) x))).
  apply (atan_mag_decr (Datatypes.S (2 * m)) x).
  apply b5d2_xle1T. exact Hx0. exact Hx1.
Qed.

(* ---- 子列单调：奇 ↑（S_{2m+1} ≤ S_{2m+3}） ---- *)
Lemma b5d2_ap_odd_inc : forall (m : nat) (x : Q), Qle 0 x -> Qle x 1 ->
  Qle (arctan_partial (Datatypes.S (2 * m)) x)
      (arctan_partial (Datatypes.S (Datatypes.S (Datatypes.S (2 * m)))) x).
Proof.
  intros m x Hx0 Hx1.
  rewrite (arctan_partial_step2 (Datatypes.S (2 * m)) x).
  rewrite (b5d2_at_term_even_pos m x Hx0).
  replace (Datatypes.S (Datatypes.S (Datatypes.S (2 * m))))%nat with (Datatypes.S (2 * Datatypes.S m))%nat by lia.
  rewrite (b5d2_at_term_odd_neg (Datatypes.S m) x Hx0).
  assert (Heq : arctan_partial (Datatypes.S (2 * m)) x + atan_mag (Datatypes.S (Datatypes.S (2 * m))) x +
                (- atan_mag (Datatypes.S (2 * Datatypes.S m)) x) ==
                arctan_partial (Datatypes.S (2 * m)) x +
                (atan_mag (Datatypes.S (Datatypes.S (2 * m))) x - atan_mag (Datatypes.S (2 * Datatypes.S m)) x)) by ring.
  rewrite Heq.
  apply Qle_plus_nonneg_r.
  replace (Datatypes.S (2 * Datatypes.S m))%nat with (Datatypes.S (Datatypes.S (Datatypes.S (2 * m))))%nat by lia.
  apply (proj1 (Qle_minus_iff (atan_mag (Datatypes.S (Datatypes.S (Datatypes.S (2 * m)))) x)
                              (atan_mag (Datatypes.S (Datatypes.S (2 * m))) x))).
  apply (atan_mag_decr (Datatypes.S (Datatypes.S (2 * m))) x).
  apply b5d2_xle1T. exact Hx0. exact Hx1.
Qed.

(* ---- 混合：奇在偶下（S_{2m+1} ≤ S_{2m}） ---- *)
Lemma b5d2_ap_mix_le : forall (m : nat) (x : Q), Qle 0 x ->
  Qle (arctan_partial (Datatypes.S (2 * m)) x) (arctan_partial (2 * m) x).
Proof.
  intros m x Hx0.
  assert (Hstep : arctan_partial (Datatypes.S (2 * m)) x ==
                  arctan_partial (2 * m) x + arctan_term (Datatypes.S (2 * m)) x).
  { reflexivity. }
  rewrite Hstep.
  rewrite (b5d2_at_term_odd_neg m x Hx0).
  apply (proj2 (Qle_minus_iff
      (arctan_partial (2 * m) x + (- atan_mag (Datatypes.S (2 * m)) x))
      (arctan_partial (2 * m) x))).
  assert (Heq : arctan_partial (2 * m) x -
      (arctan_partial (2 * m) x + (- atan_mag (Datatypes.S (2 * m)) x)) ==
      atan_mag (Datatypes.S (2 * m)) x) by ring.
  rewrite Heq.
  apply atan_mag_nonneg.
Qed.

(* ---- 混合：偶在奇上（S_{2m+1} ≤ S_{2m+2}） ---- *)
Lemma b5d2_ap_mix_ge : forall (m : nat) (x : Q), Qle 0 x ->
  Qle (arctan_partial (Datatypes.S (2 * m)) x)
      (arctan_partial (Datatypes.S (Datatypes.S (2 * m))) x).
Proof.
  intros m x Hx0.
  assert (Hstep : arctan_partial (Datatypes.S (Datatypes.S (2 * m))) x ==
                  arctan_partial (Datatypes.S (2 * m)) x + arctan_term (Datatypes.S (Datatypes.S (2 * m))) x).
  { simpl. ring. }
  rewrite Hstep.
  rewrite (b5d2_at_term_even_pos m x Hx0).
  apply Qle_plus_nonneg_r.
  apply atan_mag_nonneg.
Qed.

(* ---- S_1 ≥ 0（0 ≤ x − c_1，c_1 = atan_mag 1 x ≤ c_0 = x） ---- *)
Lemma b5d2_ap_S1_pos : forall (x : Q), Qle 0 x -> Qle x 1 -> Qle 0 (arctan_partial 1 x).
Proof.
  intros x Hx0 Hx1.
  assert (Hv : arctan_partial 1 x == atan_mag 0 x - atan_mag 1 x).
  { change (arctan_term 0 x + arctan_term 1 x == atan_mag 0 x - atan_mag 1 x).
    rewrite (b5d2_at_term0 x).
    rewrite (b5d2_mag0_x x Hx0).
    replace (1)%nat with (Datatypes.S (2 * 0))%nat by lia.
    rewrite (b5d2_at_term_odd_neg 0 x Hx0).
    ring. }
  rewrite Hv.
  apply (proj1 (Qle_minus_iff (atan_mag 1 x) (atan_mag 0 x))).
  apply (atan_mag_decr 0 x).
  apply b5d2_xle1T. exact Hx0. exact Hx1.
Qed.

(* ---- 奇子列 ≥ 0 ---- *)
Lemma b5d2_ap_odd_pos : forall (m : nat) (x : Q), Qle 0 x -> Qle x 1 ->
  Qle 0 (arctan_partial (Datatypes.S (2 * m)) x).
Proof.
  intros m x Hx0 Hx1.
  induction m as [| m' IH].
  - replace (Datatypes.S (2 * 0))%nat with 1%nat by lia.
    apply b5d2_ap_S1_pos. exact Hx0. exact Hx1.
  - replace (Datatypes.S (2 * Datatypes.S m'))%nat with (Datatypes.S (Datatypes.S (Datatypes.S (2 * m'))))%nat by lia.
    apply (Qle_trans 0 (arctan_partial (Datatypes.S (2 * m')) x)
                       (arctan_partial (Datatypes.S (Datatypes.S (Datatypes.S (2 * m')))) x)).
    + exact IH.
    + apply b5d2_ap_odd_inc. exact Hx0. exact Hx1.
Qed.

(* ---- 偶子列 ≥ 0 ---- *)
Lemma b5d2_ap_even_pos : forall (m : nat) (x : Q), Qle 0 x -> Qle x 1 ->
  Qle 0 (arctan_partial (2 * m) x).
Proof.
  intros m x Hx0 Hx1.
  destruct m as [| m'].
  - replace (2 * 0)%nat with 0%nat by lia.
    rewrite (b5d2_ap0_x x).
    exact Hx0.
  - apply (Qle_trans 0 (arctan_partial (Datatypes.S (2 * m')) x)
                       (arctan_partial (2 * Datatypes.S m') x)).
    + apply b5d2_ap_odd_pos. exact Hx0. exact Hx1.
    + replace (2 * Datatypes.S m')%nat with (Datatypes.S (Datatypes.S (2 * m')))%nat by lia.
      apply b5d2_ap_mix_ge. exact Hx0.
Qed.

(* ---- 偶子列 ≤ x（S_{2m} ≤ S_0 == x） ---- *)
Lemma b5d2_ap_even_ub : forall (m : nat) (x : Q), Qle 0 x -> Qle x 1 ->
  Qle (arctan_partial (2 * m) x) x.
Proof.
  intros m x Hx0 Hx1.
  induction m as [| m' IH].
  - replace (2 * 0)%nat with 0%nat by lia.
    apply qeq_imp_qle. apply b5d2_ap0_x.
  - apply (Qle_trans _ (arctan_partial (2 * m') x) _).
    + apply b5d2_ap_even_dec. exact Hx0. exact Hx1.
    + exact IH.
Qed.

(* ---- 夹逼：x ∈ [0,1] ⟹ 0 ≤ S_n(x) ∧ S_n(x) ≤ x ---- *)
Lemma b5d2_ap_sandwich : forall (x : Q) (n : nat), Qle 0 x -> Qle x 1 ->
  And (QleT' 0 (arctan_partial n x)) (QleT' (arctan_partial n x) x).
Proof.
  intros x n Hx0 Hx1.
  destruct (sc_nat_split n) as [m Hm | m Hm].
  - rewrite Hm. split.
    + apply Qle_to_QleT'. apply b5d2_ap_even_pos. exact Hx0. exact Hx1.
    + apply Qle_to_QleT'. apply b5d2_ap_even_ub. exact Hx0. exact Hx1.
  - rewrite Hm. split.
    + apply Qle_to_QleT'. apply b5d2_ap_odd_pos. exact Hx0. exact Hx1.
    + apply Qle_to_QleT'. apply (Qle_trans _ (arctan_partial (2 * m) x) _).
      * apply b5d2_ap_mix_le. exact Hx0.
      * apply b5d2_ap_even_ub. exact Hx0. exact Hx1.
Qed.

(* ---- 非负支：x ∈ [0,1] ⟹ |S_n(x)| ≤ 1 ---- *)
Lemma b5d2_ap_abs_le1_nonneg : forall (x : Q) (n : nat), Qle 0 x -> Qle x 1 ->
  Qle (Qabs (arctan_partial n x)) 1.
Proof.
  intros x n Hx0 Hx1.
  destruct (b5d2_ap_sandwich x n Hx0 Hx1) as [Hs0 Hsx].
  apply (Qle_trans _ (arctan_partial n x) _).
  - apply qeq_imp_qle. apply Qabs_pos. exact (QleT'_to_Qle _ _ Hs0).
  - apply (Qle_trans _ x _). exact (QleT'_to_Qle _ _ Hsx). exact Hx1.
Qed.

(* ============================================================ *)
(* M1：∀a n, |a| ≤ 1 → |arctan_partial n a| ≤ 1                 *)
(* ============================================================ *)
Lemma b5d2_ap_abs_le1 : forall (a : Q) (n : nat), QleT' (Qabs a) 1 ->
  Qle (Qabs (arctan_partial n a)) 1.
Proof.
  intros a n Ha.
  assert (Hqle : Qle (Qabs a) 1) by (apply QleT'_to_Qle; exact Ha).
  destruct (Qcompare a 0) eqn:E.
  - (* a == 0：走非负支 *)
    assert (Ha0 : a == 0) by (apply (proj2 (Qeq_alt a 0)); exact E).
    assert (H0a : Qle 0 a) by (apply qeq_imp_qle; apply Qeq_sym; exact Ha0).
    assert (Ha1 : Qle a 1) by (apply (Qle_trans a 0 1); [apply qeq_imp_qle; exact Ha0 | exact Qle_0_1]).
    exact (b5d2_ap_abs_le1_nonneg a n H0a Ha1).
  - (* a < 0：奇性 → 非负支（x := −a） *)
    assert (Halt : Qlt a 0) by (apply (proj2 (Qlt_alt a 0)); exact E).
    assert (Hal0 : Qle a 0) by (apply Qlt_le_weak; exact Halt).
    assert (H0na : Qle 0 (- a)).
    { apply (Qle_trans 0 (Qabs a) (- a)).
      - apply Qabs_nonneg.
      - apply qeq_imp_qle. exact (Qabs_neg a Hal0). }
    assert (Hna1 : Qle (- a) 1).
    { apply (Qle_trans (- a) (Qabs a) 1).
      - apply qeq_imp_qle. apply Qeq_sym. exact (Qabs_neg a Hal0).
      - exact Hqle. }
    assert (Hodd : arctan_partial n a == - arctan_partial n (- a)).
    { apply (Qeq_trans _ (arctan_partial n (- (- a))) _).
      - apply (b5c_arctan_partial_wd n a (- (- a))).
        apply Qeq_sym. apply Qopp_involutive.
      - exact (b5d2_ap_neg n (- a)). }
    assert (Habs : Qabs (arctan_partial n a) == Qabs (arctan_partial n (- a))).
    { apply (Qeq_trans _ (Qabs (- arctan_partial n (- a))) _).
      - apply (Qabs_wd (arctan_partial n a) (- arctan_partial n (- a))).
        exact Hodd.
      - apply Qabs_opp. }
    apply (Qle_trans _ (Qabs (arctan_partial n (- a))) _).
    + apply qeq_imp_qle. exact Habs.
    + exact (b5d2_ap_abs_le1_nonneg (- a) n H0na Hna1).
  - (* 0 < a *)
    assert (Hgt : Qlt 0 a) by (apply (proj2 (Qgt_alt a 0)); exact E).
    assert (H0a : Qle 0 a) by (apply Qlt_le_weak; exact Hgt).
    assert (Ha1 : Qle a 1).
    { apply (Qle_trans a (Qabs a) 1).
      - apply qeq_imp_qle. apply Qeq_sym. apply Qabs_pos. exact H0a.
      - exact Hqle. }
    exact (b5d2_ap_abs_le1_nonneg a n H0a Ha1).
Qed.

(* ============================================================ *)
(* §2 M2 b5d2_sin_partial_abs_le1（|sin_partial n q| ≤ 1，|q|≤1）*)
(* 路线：q ∈ [0,1] 支用 sc_sin_partial_upper_x（上）+              *)
(*   sc_sin_partial_lower_c1（q − q³/6 ≤ sin ⟹ 0 ≤ sin）；        *)
(*   q ≤ 0 支经 sc_sin_partial_neg 奇性归约到 −q ≥ 0。            *)
(* ============================================================ *)

(* ---- 算术：q³ ≤ 6q（0 ≤ q ≤ 1） ---- *)
Lemma b5d2_qpow3_le_6x : forall x : Q, Qle 0 x -> Qle x 1 -> Qle (q_pow x 3) (x * 6).
Proof.
  intros x Hx0 Hx1.
  assert (Hc : q_pow x 3 == x * (x * x)) by (cbn [q_pow]; ring).
  rewrite Hc.
  apply (sc_qmult_le_l (x * x) 6 x).
  - apply (Qle_trans (x * x) 1 6).
    + apply atan_sq_le_one. apply b5d2_xle1T. exact Hx0. exact Hx1.
    + unfold Qle; simpl; lia.
  - exact Hx0.
Qed.

(* ---- 算术：c1 = q³/6 ≤ q（0 ≤ q ≤ 1）⟹ 0 ≤ q − c1 ---- *)
Lemma b5d2_sin_alt1_le_x : forall x : Q, Qle 0 x -> Qle x 1 -> Qle (sc_sin_alt 1 x) x.
Proof.
  intros x Hx0 Hx1.
  rewrite (sc_sin_alt1_cube x).
  assert (Hc : q_pow x 3 == x * (x * x)) by (cbn [q_pow]; ring).
  rewrite Hc.
  unfold Qdiv.
  assert (H6 : Qlt 0 6) by (unfold Qlt; simpl; lia).
  assert (Hinv0 : Qle 0 (Qinv 6)) by (apply Qlt_le_weak; apply Qinv_lt_0_compat; exact H6).
  assert (Hxx6 : Qle (x * x) 6).
  { apply (Qle_trans (x * x) 1 6).
    - apply atan_sq_le_one. apply b5d2_xle1T. exact Hx0. exact Hx1.
    - unfold Qle; simpl; lia. }
  assert (Hx6 : Qle (x * (x * x)) (x * 6)).
  { apply (sc_qmult_le_l (x * x) 6 x). exact Hxx6. exact Hx0. }
  apply (Qle_trans _ ((x * 6) * Qinv 6) _).
  - apply (Qmult_le_compat_r (x * (x * x)) (x * 6) (Qinv 6)).
    + exact Hx6.
    + exact Hinv0.
  - apply qeq_le. field.
Qed.

(* ---- 非负支：q ∈ [0,1] ⟹ |sin_partial n q| ≤ 1 ---- *)
Lemma b5d2_sin_abs_le1_nonneg : forall (n : nat) (q : Q), Qle 0 q -> Qle q 1 ->
  Qle (Qabs (sin_partial n q)) 1.
Proof.
  intros n q Hq0 Hq1.
  assert (Hs_le_q : Qle (sin_partial n q) q).
  { apply sc_sin_partial_upper_x. exact Hq0. exact Hq1. }
  assert (Hs_ge_c : Qle (q - sc_sin_alt 1 q) (sin_partial n q)).
  { apply sc_sin_partial_lower_c1. exact Hq0. exact Hq1. }
  assert (Hc_le_q : Qle (sc_sin_alt 1 q) q) by (apply b5d2_sin_alt1_le_x; [exact Hq0 | exact Hq1]).
  assert (Hs0 : Qle 0 (sin_partial n q)).
  { apply (Qle_trans _ (q - sc_sin_alt 1 q) _).
    - apply (proj1 (Qle_minus_iff (sc_sin_alt 1 q) q)). exact Hc_le_q.
    - exact Hs_ge_c. }
  apply (Qle_trans _ (sin_partial n q) _).
  - apply qeq_imp_qle. apply Qabs_pos. exact Hs0.
  - apply (Qle_trans _ q _). exact Hs_le_q. exact Hq1.
Qed.

(* ============================================================ *)
(* M2：∀n q, |q| ≤ 1 → |sin_partial n q| ≤ 1                    *)
(* ============================================================ *)
Lemma b5d2_sin_partial_abs_le1 : forall (n : nat) (q : Q), QleT' (Qabs q) 1 ->
  Qle (Qabs (sin_partial n q)) 1.
Proof.
  intros n q Hq.
  assert (Hqle : Qle (Qabs q) 1) by (apply QleT'_to_Qle; exact Hq).
  destruct (Qcompare q 0) eqn:E.
  - (* q == 0：走非负支 *)
    assert (Hq0 : q == 0) by (apply (proj2 (Qeq_alt q 0)); exact E).
    assert (H0q : Qle 0 q) by (apply qeq_imp_qle; apply Qeq_sym; exact Hq0).
    assert (Hq1 : Qle q 1) by (apply (Qle_trans q 0 1); [apply qeq_imp_qle; exact Hq0 | exact Qle_0_1]).
    exact (b5d2_sin_abs_le1_nonneg n q H0q Hq1).
  - (* q < 0：奇性 → 非负支（x := −q） *)
    assert (Hqlt : Qlt q 0) by (apply (proj2 (Qlt_alt q 0)); exact E).
    assert (Hq0' : Qle q 0) by (apply Qlt_le_weak; exact Hqlt).
    assert (H0nq : Qle 0 (- q)).
    { apply (Qle_trans 0 (Qabs q) (- q)).
      - apply Qabs_nonneg.
      - apply qeq_imp_qle. exact (Qabs_neg q Hq0'). }
    assert (Hnq1 : Qle (- q) 1).
    { apply (Qle_trans (- q) (Qabs q) 1).
      - apply qeq_imp_qle. apply Qeq_sym. exact (Qabs_neg q Hq0').
      - exact Hqle. }
    assert (Hs : sin_partial n q == - sin_partial n (- q)).
    { apply (Qeq_trans _ (sin_partial n (- (- q))) _).
      - apply (sc_sin_partial_wd n q (- (- q))). apply Qeq_sym. apply Qopp_involutive.
      - exact (sc_sin_partial_neg n (- q)). }
    assert (Habs : Qabs (sin_partial n q) == Qabs (sin_partial n (- q))).
    { apply (Qeq_trans _ (Qabs (- sin_partial n (- q))) _).
      - apply (Qabs_wd (sin_partial n q) (- sin_partial n (- q))). exact Hs.
      - apply Qabs_opp. }
    apply (Qle_trans _ (Qabs (sin_partial n (- q))) _).
    + apply qeq_imp_qle. exact Habs.
    + exact (b5d2_sin_abs_le1_nonneg n (- q) H0nq Hnq1).
  - (* 0 < q *)
    assert (Hgt : Qlt 0 q) by (apply (proj2 (Qgt_alt q 0)); exact E).
    assert (H0q : Qle 0 q) by (apply Qlt_le_weak; exact Hgt).
    assert (Hq1 : Qle q 1).
    { apply (Qle_trans q (Qabs q) 1).
      - apply qeq_imp_qle. apply Qeq_sym. apply Qabs_pos. exact H0q.
      - exact Hqle. }
    exact (b5d2_sin_abs_le1_nonneg n q H0q Hq1).
Qed.

(* ============================================================ *)
(* §3 M3 b5d2_cos_partial_abs_le1（|cos_partial n q| ≤ 1，|q|≤1）*)
(* 路线：q ∈ [0,1] 支用 sc_cos_partial_upper_one（上）+          *)
(*   sc_cos_partial_lower_c1（1 − q²/2 ≤ cos ⟹ 0 ≤ cos）；       *)
(*   q ≤ 0 支经偶性 sc_cos_partial_neg。                         *)
(* ============================================================ *)

(* ---- 算术：c1' = q²/2 ≤ 1（0 ≤ q ≤ 1）⟹ 0 ≤ 1 − c1' ---- *)
Lemma b5d2_cos_alt1_le_one : forall x : Q, Qle 0 x -> Qle x 1 -> Qle (sc_cos_alt 1 x) 1.
Proof.
  intros x Hx0 Hx1.
  rewrite (sc_cos_alt1_half x).
  assert (Hc : q_pow x 2 == x * x) by (cbn [q_pow]; ring).
  rewrite Hc.
  unfold Qdiv.
  assert (H2 : Qlt 0 2) by (unfold Qlt; simpl; lia).
  assert (Hinv0 : Qle 0 (Qinv 2)) by (apply Qlt_le_weak; apply Qinv_lt_0_compat; exact H2).
  apply (Qle_trans _ (2 * Qinv 2) _).
  - apply (Qmult_le_compat_r (x * x) 2 (Qinv 2)).
    + apply (Qle_trans (x * x) 1 2).
      * apply atan_sq_le_one. apply b5d2_xle1T. exact Hx0. exact Hx1.
      * unfold Qle; simpl; lia.
    + exact Hinv0.
  - apply qeq_le. rewrite (Qmult_inv_r 2 (q_neq_of_lt 2 H2)). ring.
Qed.

(* ---- 非负支：q ∈ [0,1] ⟹ |cos_partial n q| ≤ 1 ---- *)
Lemma b5d2_cos_abs_le1_nonneg : forall (n : nat) (q : Q), Qle 0 q -> Qle q 1 ->
  Qle (Qabs (cos_partial n q)) 1.
Proof.
  intros n q Hq0 Hq1.
  assert (Hs_le1 : Qle (cos_partial n q) 1).
  { apply sc_cos_partial_upper_one. exact Hq0. exact Hq1. }
  assert (Hs_ge_c : Qle (1 - sc_cos_alt 1 q) (cos_partial n q)).
  { apply sc_cos_partial_lower_c1. exact Hq0. exact Hq1. }
  assert (Hc_le1 : Qle (sc_cos_alt 1 q) 1) by (apply b5d2_cos_alt1_le_one; [exact Hq0 | exact Hq1]).
  assert (Hs0 : Qle 0 (cos_partial n q)).
  { apply (Qle_trans _ (1 - sc_cos_alt 1 q) _).
    - apply (proj1 (Qle_minus_iff (sc_cos_alt 1 q) 1)). exact Hc_le1.
    - exact Hs_ge_c. }
  apply (Qle_trans _ (cos_partial n q) _).
  - apply qeq_imp_qle. apply Qabs_pos. exact Hs0.
  - exact Hs_le1.
Qed.

(* ============================================================ *)
(* M3：∀n q, |q| ≤ 1 → |cos_partial n q| ≤ 1                    *)
(* ============================================================ *)
Lemma b5d2_cos_partial_abs_le1 : forall (n : nat) (q : Q), QleT' (Qabs q) 1 ->
  Qle (Qabs (cos_partial n q)) 1.
Proof.
  intros n q Hq.
  assert (Hqle : Qle (Qabs q) 1) by (apply QleT'_to_Qle; exact Hq).
  destruct (Qcompare q 0) eqn:E.
  - (* q == 0：走非负支 *)
    assert (Hq0 : q == 0) by (apply (proj2 (Qeq_alt q 0)); exact E).
    assert (H0q : Qle 0 q) by (apply qeq_imp_qle; apply Qeq_sym; exact Hq0).
    assert (Hq1 : Qle q 1) by (apply (Qle_trans q 0 1); [apply qeq_imp_qle; exact Hq0 | exact Qle_0_1]).
    exact (b5d2_cos_abs_le1_nonneg n q H0q Hq1).
  - (* q < 0：偶性 → 非负支（x := −q） *)
    assert (Hqlt : Qlt q 0) by (apply (proj2 (Qlt_alt q 0)); exact E).
    assert (Hq0' : Qle q 0) by (apply Qlt_le_weak; exact Hqlt).
    assert (H0nq : Qle 0 (- q)).
    { apply (Qle_trans 0 (Qabs q) (- q)).
      - apply Qabs_nonneg.
      - apply qeq_imp_qle. exact (Qabs_neg q Hq0'). }
    assert (Hnq1 : Qle (- q) 1).
    { apply (Qle_trans (- q) (Qabs q) 1).
      - apply qeq_imp_qle. apply Qeq_sym. exact (Qabs_neg q Hq0').
      - exact Hqle. }
    assert (Hev : cos_partial n q == cos_partial n (- q)).
    { apply Qeq_sym. exact (sc_cos_partial_neg n q). }
    assert (Habs : Qabs (cos_partial n q) == Qabs (cos_partial n (- q))).
    { apply (Qabs_wd (cos_partial n q) (cos_partial n (- q))). exact Hev. }
    apply (Qle_trans _ (Qabs (cos_partial n (- q))) _).
    + apply qeq_imp_qle. exact Habs.
    + exact (b5d2_cos_abs_le1_nonneg n (- q) H0nq Hnq1).
  - (* 0 < q *)
    assert (Hgt : Qlt 0 q) by (apply (proj2 (Qgt_alt q 0)); exact E).
    assert (H0q : Qle 0 q) by (apply Qlt_le_weak; exact Hgt).
    assert (Hq1 : Qle q 1).
    { apply (Qle_trans q (Qabs q) 1).
      - apply qeq_imp_qle. apply Qeq_sym. apply Qabs_pos. exact H0q.
      - exact Hqle. }
    exact (b5d2_cos_abs_le1_nonneg n q H0q Hq1).
Qed.

(* ============================================================ *)
(* §4 M4：组合 glue（M1 + M2/M3）                               *)
(*   |sin/cos_partial n (arctan_partial n x_n)| ≤ 1（|x_n|≤1）  *)
(* ============================================================ *)
Lemma b5d2_sinA_abs_le1 : forall (x : Real)
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1) (n : nat),
  Qle (Qabs (sin_partial n (arctan_partial n (projT1 x n)))) 1.
Proof.
  intros x Hx n.
  apply (b5d2_sin_partial_abs_le1 n (arctan_partial n (projT1 x n))).
  apply Qle_to_QleT'.
  apply (b5d2_ap_abs_le1 (projT1 x n) n).
  exact (Hx n).
Qed.

Lemma b5d2_cosA_abs_le1 : forall (x : Real)
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1) (n : nat),
  Qle (Qabs (cos_partial n (arctan_partial n (projT1 x n)))) 1.
Proof.
  intros x Hx n.
  apply (b5d2_cos_partial_abs_le1 n (arctan_partial n (projT1 x n))).
  apply Qle_to_QleT'.
  apply (b5d2_ap_abs_le1 (projT1 x n) n).
  exact (Hx n).
Qed.

(* ============================================================ *)
(* §5 M5：x := real_const 0 实例（值件 + Qabs 桥）              *)
(* ============================================================ *)
Lemma b5d2_x0_sinA_le1 : forall n : nat,
  Qle (Qabs (sin_partial n (arctan_partial n (projT1 (real_const 0) n)))) 1.
Proof.
  intro n.
  assert (Hz : projT1 (real_const 0) n == 0) by reflexivity.
  assert (Hap0 : arctan_partial n (projT1 (real_const 0) n) == 0).
  { apply (Qeq_trans _ (arctan_partial n 0) _).
    - apply (b5c_arctan_partial_wd n (projT1 (real_const 0) n) 0). exact Hz.
    - apply b5c_arctan_partial_zero. }
  assert (Hs0 : sin_partial n (arctan_partial n (projT1 (real_const 0) n)) == 0).
  { apply (Qeq_trans _ (sin_partial n 0) _).
    - apply (sc_sin_partial_wd n (arctan_partial n (projT1 (real_const 0) n)) 0). exact Hap0.
    - apply sc_sin_partial_zero. }
  apply (Qle_trans (Qabs (sin_partial n (arctan_partial n (projT1 (real_const 0) n)))) (Qabs 0) 1).
  - apply qeq_imp_qle.
    apply (Qabs_wd (sin_partial n (arctan_partial n (projT1 (real_const 0) n))) 0).
    exact Hs0.
  - apply (Qle_trans (Qabs 0) 0 1).
    + apply qeq_imp_qle. change (Qabs 0 == 0). cbn. reflexivity.
    + exact Qle_0_1.
Qed.

Lemma b5d2_x0_cosA_le1 : forall n : nat,
  Qle (Qabs (cos_partial n (arctan_partial n (projT1 (real_const 0) n)))) 1.
Proof.
  intro n.
  assert (Hz : projT1 (real_const 0) n == 0) by reflexivity.
  assert (Hap0 : arctan_partial n (projT1 (real_const 0) n) == 0).
  { apply (Qeq_trans _ (arctan_partial n 0) _).
    - apply (b5c_arctan_partial_wd n (projT1 (real_const 0) n) 0). exact Hz.
    - apply b5c_arctan_partial_zero. }
  assert (Hc1 : cos_partial n (arctan_partial n (projT1 (real_const 0) n)) == 1).
  { apply (Qeq_trans _ (cos_partial n 0) _).
    - apply (sc_cos_partial_wd n (arctan_partial n (projT1 (real_const 0) n)) 0). exact Hap0.
    - apply sc_cos_partial_one. }
  apply (Qle_trans (Qabs (cos_partial n (arctan_partial n (projT1 (real_const 0) n)))) (Qabs 1) 1).
  - apply qeq_imp_qle.
    apply (Qabs_wd (cos_partial n (arctan_partial n (projT1 (real_const 0) n))) 1).
    exact Hc1.
  - apply qeq_imp_qle. apply (Qabs_pos 1 Qle_0_1).
Qed.

(* ============================================================ *)
(* 块 item8（前缀 b5d4_——主件 b5d4_S0_lb_half）——来源：演变/.ablation/sc2_parallel/sc2_b5a_ode/sc2_b5a_item8.v。 *)
(* ============================================================ *)

(* ============================================================ *)
(* §0 证书与桥引理（b5d4_ 独占；全部真 Qed）                    *)
(* ============================================================ *)

(* eps 正性证书（real_eq 实例化 eps := 1/2 / 1 用） *)
Lemma b5d4_Hq12T : QltT 0 (1 # 2).
Proof. apply Qlt_to_QltT. unfold Qlt. simpl. lia. Qed.

Lemma b5d4_Hq1T : QltT 0 1.
Proof. apply Qlt_to_QltT. unfold Qlt. simpl. lia. Qed.

(* Qlt 0 (1#2) / Qlt 0 1（Q 层正性，q_abs_gt_neg 系引理用） *)
Lemma b5d4_Hq12 : Qlt 0 (1 # 2).
Proof. unfold Qlt. simpl. lia. Qed.

Lemma b5d4_Hq1 : Qlt 0 1.
Proof. unfold Qlt. simpl. lia. Qed.

(* real_const 0 == real_zero 桥（逐点零差；仿 item4 b5n2_zero_eq_const0
   思路自写，勿 Require item4） *)
Lemma b5d4_const0_eq_zero : real_eq (real_const 0) real_zero.
Proof.
  apply real_eq_of_zero_diff.
  intro n.
  rewrite (real_const_proj 0 n).
  cbn [projT1 real_zero].
  reflexivity.
Qed.

(* b5a_S 的 real_eq 外延兼容（自建，仿 item3b b5m_S_wd 思路；
   零上游依赖）：u ≈ v ⟹ S u ≈ S v *)
Lemma b5d4_S_wd : forall (u v : Real), real_eq u v -> real_eq (b5a_S u) (b5a_S v).
Proof.
  intros u v Huv.
  unfold b5a_S.
  apply cauchy_real_exp_wd.
  apply (RealSetoid.real_eq_mult_compat
           (real_const (1 / 2))
           (real_log (real_plus real_one (real_mult u u)) (b5a_one_plus_sq_pos u))
           (real_const (1 / 2))
           (real_log (real_plus real_one (real_mult v v)) (b5a_one_plus_sq_pos v))).
  - apply real_eq_refl.
  - apply (real_log_wd (real_plus real_one (real_mult u u)) (real_plus real_one (real_mult v v))
                       (b5a_one_plus_sq_pos u) (b5a_one_plus_sq_pos v)).
    apply (RealSetoid.real_eq_plus_compat real_one (real_mult u u) real_one (real_mult v v)).
    + apply real_eq_refl.
    + apply (RealSetoid.real_eq_mult_compat u u v v); exact Huv.
Qed.

(* Q 层：|x − p| < 1/2 ∧ p == 1 ⟹ 1/2 < x（件 B1 尾界内核） *)
Lemma b5d4_q_lb_half : forall (x p : Q), p == 1 -> Qlt (Qabs (x - p)) (1 # 2) -> Qlt (1 # 2) x.
Proof.
  intros x p Hp H.
  setoid_rewrite Hp in H.   (* p → 1（Qminus_comp/Qabs_wd/Qlt_compat 齐备） *)
  apply (proj2 (Qlt_minus_iff (1 # 2) x)).
  setoid_replace (x - (1 # 2)) with ((x - 1) - - (1 # 2)) by ring.
  apply (proj1 (Qlt_minus_iff (- (1 # 2)) (x - 1))).
  apply (q_abs_gt_neg (x - 1) (1 # 2) b5d4_Hq12). exact H.
Qed.

(* Q 层：|x − p| < 1 ∧ p == 1 ⟹ |x| ≤ 2（件 B2 尾界内核） *)
Lemma b5d4_q_ub_two : forall (x p : Q), p == 1 -> Qlt (Qabs (x - p)) 1 -> Qle (Qabs x) 2.
Proof.
  intros x p Hp H.
  setoid_rewrite Hp in H.   (* Qlt (Qabs (x - 1)) 1 *)
  assert (Hlow : Qlt 0 x).
  { apply (proj2 (Qlt_minus_iff 0 x)).
    setoid_replace (x - 0) with ((x - 1) - - 1) by ring.
    apply (proj1 (Qlt_minus_iff (- 1) (x - 1))).
    apply (q_abs_gt_neg (x - 1) 1 b5d4_Hq1). exact H. }
  assert (Hup : Qlt x 2).
  { apply (proj2 (Qlt_minus_iff x 2)).
    setoid_replace (2 - x) with (- (x - 1) - - 1) by ring.
    apply (proj1 (Qlt_minus_iff (- 1) (- (x - 1)))).
    apply (q_abs_gt_neg (- (x - 1)) 1 b5d4_Hq1).
    rewrite (Qabs_opp (x - 1)). exact H. }
  apply (Qle_trans (Qabs x) x 2).
  - apply qeq_imp_qle. apply (Qabs_pos x). apply Qlt_le_weak. exact Hlow.
  - apply Qlt_le_weak. exact Hup.
Qed.

(* ============================================================ *)
(* 件 A：S(0) == 1（S-族 real_eq 锚，库内缺失，关键新数学件）    *)
(*   b5d4_S_const0_eq_one : real_eq (b5a_S (real_const 0))       *)
(*                            real_one                           *)
(* 链：1 + 0·0 == 1 ⟹ real_log_wd ⟹ real_log_one（log 1 == 0）    *)
(*   ⟹ (1/2)·log(1 + 0·0) == (1/2)·0 == 0 ⟹ cauchy_real_exp_wd   *)
(*   ⟹ cauchy_real_exp_zero（e^0 == 1）。纯 Real 层 real_eq 代数， *)
(*   零 log_seq 逐点（审查 §5.2 形态上限）。                      *)
(* ============================================================ *)
Lemma b5d4_S_const0_eq_one : real_eq (b5a_S (real_const 0)) real_one.
Proof.
  (* 0·0 == real_zero（经 real_const 0 == real_zero 桥 + mult_zero） *)
  assert (H00 : real_eq (real_mult (real_const 0) (real_const 0)) real_zero).
  { apply (real_eq_trans _ (real_mult real_zero real_zero) _).
    - apply (RealSetoid.real_eq_mult_compat (real_const 0) (real_const 0) real_zero real_zero);
        exact b5d4_const0_eq_zero.
    - exact (real_mult_zero real_zero). }
  (* 1 + 0·0 == 1 *)
  assert (Hone : real_eq (real_plus real_one (real_mult (real_const 0) (real_const 0))) real_one).
  { apply (real_eq_trans _ (real_plus real_one real_zero) _).
    - apply (RealSetoid.real_eq_plus_compat real_one (real_mult (real_const 0) (real_const 0))
                                            real_one real_zero);
        [ apply real_eq_refl | exact H00 ].
    - exact (real_plus_zero real_one). }
  (* log(1 + 0·0) == log 1（real_log_wd，正性证书两侧齐备） *)
  assert (Hlog1 : real_eq
      (real_log (real_plus real_one (real_mult (real_const 0) (real_const 0)))
                (b5a_one_plus_sq_pos (real_const 0)))
      (real_log real_one real_lt_zero_one)).
  { apply (real_log_wd (real_plus real_one (real_mult (real_const 0) (real_const 0))) real_one
                       (b5a_one_plus_sq_pos (real_const 0)) real_lt_zero_one). exact Hone. }
  (* log(1 + 0·0) == real_zero（real_log_one 锚） *)
  assert (Hlogz : real_eq
      (real_log (real_plus real_one (real_mult (real_const 0) (real_const 0)))
                (b5a_one_plus_sq_pos (real_const 0)))
      real_zero).
  { apply (real_eq_trans _ (real_log real_one real_lt_zero_one) _).
    - exact Hlog1.
    - exact (real_log_one real_lt_zero_one). }
  (* (1/2)·log(1 + 0·0) == (1/2)·0 == 0 *)
  assert (Hmulz : real_eq
      (real_mult (real_const (1 / 2))
                 (real_log (real_plus real_one (real_mult (real_const 0) (real_const 0)))
                           (b5a_one_plus_sq_pos (real_const 0))))
      real_zero).
  { apply (real_eq_trans _ (real_mult (real_const (1 / 2)) real_zero) _).
    - apply (RealSetoid.real_eq_mult_compat (real_const (1 / 2))
             (real_log (real_plus real_one (real_mult (real_const 0) (real_const 0)))
                       (b5a_one_plus_sq_pos (real_const 0)))
             (real_const (1 / 2)) real_zero);
        [ apply real_eq_refl | exact Hlogz ].
    - exact (real_mult_zero (real_const (1 / 2))). }
  (* exp∘mult == exp 0 == 1 *)
  unfold b5a_S.
  apply (real_eq_trans _ (cauchy_real_exp real_zero) _).
  - apply cauchy_real_exp_wd. exact Hmulz.
  - exact cauchy_real_exp_zero.
Qed.

(* ============================================================ *)
(* 件 A'：S(real_zero) == 1（real_zero 变体，服务 clamp01 端点   *)
(*   锚；经件 A + b5d4_S_wd + real_const 0 == real_zero 桥）      *)
(*   b5d4_S_zero_eq_one : real_eq (b5a_S real_zero) real_one      *)
(* ============================================================ *)
Lemma b5d4_S_zero_eq_one : real_eq (b5a_S real_zero) real_one.
Proof.
  apply (real_eq_trans _ (b5a_S (real_const 0)) _).
  - apply real_eq_sym.
    apply (b5d4_S_wd (real_const 0) real_zero). exact b5d4_const0_eq_zero.
  - exact b5d4_S_const0_eq_one.
Qed.

(* ============================================================ *)
(* 件 B1：端点显式下界（有理值直写，禁 sigT c 包装后 Qed）       *)
(*   b5d4_S0_lb_half : sigT (fun N => forall n, (N<=n)%nat ->    *)
(*     Qle (1#2) (projT1 (b5a_S (real_const 0)) n))              *)
(* 依赖：件 A 的 eps := 1/2 实例 + b5d4_q_lb_half（Q 层证毕）。   *)
(* ============================================================ *)
Lemma b5d4_S0_lb_half : sigT (fun N : nat => forall n : nat, (N <= n)%nat ->
  Qle (1 # 2) (projT1 (b5a_S (real_const 0)) n)).
Proof.
  destruct (b5d4_S_const0_eq_one (1 # 2) b5d4_Hq12T) as [N HN].
  exists N.
  intros n Hn.
  apply Qlt_le_weak.
  apply (b5d4_q_lb_half (projT1 (b5a_S (real_const 0)) n) (projT1 real_one n)).
  - cbn [projT1 real_one]. reflexivity.
  - apply QltT_to_Qlt. exact (HN n (NatLe_lift _ _ Hn)).
Qed.

(* ============================================================ *)
(* 件 B2：端点显式上界（尾，M0 := 2；有理值直写）               *)
(*   b5d4_S0_ub_two : sigT (fun N => forall n, (N<=n)%nat ->     *)
(*     Qle (Qabs (projT1 (b5a_S (real_const 0)) n)) 2)           *)
(* 依赖：件 A 的 eps := 1 实例 + b5d4_q_ub_two（Q 层证毕）。      *)
(* ============================================================ *)
Lemma b5d4_S0_ub_two : sigT (fun N : nat => forall n : nat, (N <= n)%nat ->
  Qle (Qabs (projT1 (b5a_S (real_const 0)) n)) 2).
Proof.
  destruct (b5d4_S_const0_eq_one 1 b5d4_Hq1T) as [N HN].
  exists N.
  intros n Hn.
  apply (b5d4_q_ub_two (projT1 (b5a_S (real_const 0)) n) (projT1 real_one n)).
  - cbn [projT1 real_one]. reflexivity.
  - apply QltT_to_Qlt. exact (HN n (NatLe_lift _ _ Hn)).
Qed.

(* ============================================================ *)
(* 块 item11（前缀 b5d7_——主件 b5d7_J_deriv_zero_exp）——来源：演变/.ablation/sc2_parallel/sc2_b5a_ode/sc2_b5a_item11.v。 *)
(* ============================================================ *)

(* ============================================================ *)
(* §0 主件 b5d7_J_deriv_zero_exp（C5 显式参数化定稿语句）        *)
(*   语句 = δC-审查 §1.5 + δB-审查-ScA下界 §4.1 草案全文；       *)
(*   Hxh 形同原 b5a_J_deriv_zero（源 L373–383）。前提为未命名     *)
(*   箭头（intros 处命名 HNA/HMall/HMs_all/HMc_all）。           *)
(* ============================================================ *)
Lemma b5d7_J_deriv_zero_exp :
  forall (r : Q) (Hr0 : Qle 0 r) (Hr1 : Qlt r 1),
  forall (cA M Ms Mc : Q)
         (HcA : Qlt 0 cA) (HM : Qlt 0 M)
         (HMs : QltT 0 Ms) (HMc : QltT 0 Mc),
  forall (x : Real) (Hxr : forall n : nat, QleT' (Qabs (projT1 x n)) r),
  forall (NA : nat),
  (forall n : nat, (NA <= n)%nat -> Qle cA (projT1 (b5a_S x) n)) ->
  (forall n : nat, Qle (Qabs (projT1 (b5a_S x) n)) M) ->
  (forall n : nat,
     Qle (Qabs (sin_partial n (arctan_partial n (projT1 x n)))) Ms) ->
  (forall n : nat,
     Qle (Qabs (cos_partial n (arctan_partial n (projT1 x n)))) Mc) ->
  forall (eps : Real), real_lt real_zero eps ->
  sigT (fun delta : Real => And (real_lt real_zero delta)
    (forall (h : Real), real_lt (real_abs h) delta ->
      forall (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1),
      forall (eps' : Real), real_lt real_zero eps' ->
      real_le (real_abs (real_plus (b5c_J (real_plus x h) Hxh)
                 (real_opp (b5c_J x (b3rr_dom_r1 x r Hxr Hr1)))))
              (real_plus (real_mult eps (real_abs h)) eps'))).
Proof.
  intros r Hr0 Hr1 cA M Ms Mc HcA HM HMs HMc x Hxr NA HNA HMall HMs_all HMc_all eps Heps.
  set (Hx := b3rr_dom_r1 x r Hxr Hr1).
  (* ---- 固定数据 ---- *)
  (* cA：S(x) 逐点正下界——语句显式 Q 参数 cA/HcA + NA 尾界前提 HNA； *)
  (* δ-C C5：4 处黑盒 destruct（源 L389/396/399/400）→ intros 参数束 *)
  set (cB := Qmult cA (1 # 2)).
  assert (HcB : Qlt 0 cB).
  { unfold cB. apply (Qmult_lt_0_compat cA (1 # 2)).
    - exact HcA.
    - change (Qlt 0 (1 # 2)). unfold Qlt. simpl. lia. }
  (* M/Ms/Mc：语句显式 Q 参数；全 n 前提 HMall/HMs_all/HMc_all 直接应用 *)
  assert (HM0 : Qle 0 M). { apply Qlt_le_weak. exact HM. }
  (* Ms/Mc：sinA/cosA 逐点界 ⟹ ME := Ms + r·Mc（|E(x)_n| ≤ ME）     *)
  assert (HMs0 : Qle 0 Ms). { apply Qlt_le_weak. apply QltT_to_Qlt. exact HMs. }
  assert (HMc0 : Qle 0 Mc). { apply Qlt_le_weak. apply QltT_to_Qlt. exact HMc. }
  assert (Hr0' : Qle 0 r). { exact Hr0. }
  set (ME := Qplus Ms (Qmult r Mc)).
  assert (HME0 : Qle 0 ME).
  { unfold ME. nra. }
  (* 逆常数与份额（全部只依赖 x 数据；QltT 0 用于 real_const_pos） *)
  set (QicA := Qinv cA).
  set (QicB := Qinv cB).
  set (kE := Qmult cB (1 # 8)).
  set (kEp := Qmult cB (1 # 16)).
  set (kapE := Qmult cB (1 # 16)).
  set (invM1 := Qinv (Qplus ME 1)).
  set (kS := Qmult (Qmult (Qmult cA cB) (1 # 8)) invM1).
  set (kSp := Qmult (Qmult (Qmult cA cB) (1 # 16)) invM1).
  set (kapS := Qmult (Qmult (Qmult cA cB) (1 # 16)) invM1).
  set (K1 := Qplus (Qmult r M) 1).
  set (tau := Qmult cA (Qinv (Qmult 8 K1))).
  set (mu := Qmult cA (1 # 16)).
  set (kapS2 := Qmult cA (1 # 16)).
  (* 正性事实 *)
  assert (HkET : QltT 0 kE).
  { unfold kE. apply Qlt_to_QltT. apply (Qmult_lt_0_compat cB (1 # 8)).
    - exact HcB.
    - change (Qlt 0 (1 # 8)). unfold Qlt. simpl. lia. }
  assert (HkEpT : QltT 0 kEp).
  { unfold kEp. apply Qlt_to_QltT. apply (Qmult_lt_0_compat cB (1 # 16)).
    - exact HcB.
    - change (Qlt 0 (1 # 16)). unfold Qlt. simpl. lia. }
  assert (HkapET : QltT 0 kapE).
  { unfold kapE. apply Qlt_to_QltT. apply (Qmult_lt_0_compat cB (1 # 16)).
    - exact HcB.
    - change (Qlt 0 (1 # 16)). unfold Qlt. simpl. lia. }
  assert (HME1 : Qlt 0 (Qplus ME 1)).
  { nra. }
  assert (HME1ne : ~ Qplus ME 1 == 0).
  { apply q_neq_of_lt. exact HME1. }
  assert (Hinv1T : QltT 0 invM1).
  { unfold invM1. apply Qlt_to_QltT. apply Qinv_lt_0_compat. exact HME1. }
  assert (HcAcB0 : Qlt 0 (Qmult (Qmult cA cB) (1 # 8))).
  { apply (Qmult_lt_0_compat (Qmult cA cB) (1 # 8)).
    - apply (Qmult_lt_0_compat cA cB). { exact HcA. } { exact HcB. }
    - change (Qlt 0 (1 # 8)). unfold Qlt. simpl. lia. }
  assert (HcAcB0b : Qlt 0 (Qmult (Qmult cA cB) (1 # 16))).
  { apply (Qmult_lt_0_compat (Qmult cA cB) (1 # 16)).
    - apply (Qmult_lt_0_compat cA cB). { exact HcA. } { exact HcB. }
    - change (Qlt 0 (1 # 16)). unfold Qlt. simpl. lia. }
  assert (HkST : QltT 0 kS).
  { unfold kS. apply Qlt_to_QltT.
    apply (Qmult_lt_0_compat (Qmult (Qmult cA cB) (1 # 8)) invM1).
    - exact HcAcB0.
    - apply QltT_to_Qlt. exact Hinv1T. }
  assert (HkSpT : QltT 0 kSp).
  { unfold kSp. apply Qlt_to_QltT.
    apply (Qmult_lt_0_compat (Qmult (Qmult cA cB) (1 # 16)) invM1).
    - exact HcAcB0b.
    - apply QltT_to_Qlt. exact Hinv1T. }
  assert (HkapST : QltT 0 kapS).
  { unfold kapS. apply Qlt_to_QltT.
    apply (Qmult_lt_0_compat (Qmult (Qmult cA cB) (1 # 16)) invM1).
    - exact HcAcB0b.
    - apply QltT_to_Qlt. exact Hinv1T. }
  assert (HK1 : Qlt 0 K1).
  { unfold K1. nra. }
  assert (HtauT : QltT 0 tau).
  { unfold tau. apply Qlt_to_QltT.
    apply (Qmult_lt_0_compat cA (Qinv (Qmult 8 K1))).
    - exact HcA.
    - apply Qinv_lt_0_compat. nra. }
  assert (HmuT : QltT 0 mu).
  { unfold mu. apply Qlt_to_QltT. apply (Qmult_lt_0_compat cA (1 # 16)).
    - exact HcA.
    - change (Qlt 0 (1 # 16)). unfold Qlt. simpl. lia. }
  assert (HkapS2T : QltT 0 kapS2).
  { unfold kapS2. apply Qlt_to_QltT. apply (Qmult_lt_0_compat cA (1 # 16)).
    - exact HcA.
    - change (Qlt 0 (1 # 16)). unfold Qlt. simpl. lia. }
  assert (H1T : QltT 0 1) by (apply Qlt_to_QltT; change (Qlt 0 1); unfold Qlt; simpl; lia).
  assert (HcA0 : Qle 0 cA). { apply Qlt_le_weak. exact HcA. }
  assert (HcB0 : Qle 0 cB). { apply Qlt_le_weak. exact HcB. }
  assert (HcAne : ~ cA == 0). { apply q_neq_of_lt. exact HcA. }
  assert (HcBne : ~ cB == 0). { apply q_neq_of_lt. exact HcB. }
  assert (H8K1ne : ~ Qmult 8 K1 == 0).
  { apply q_neq_of_lt. nra. }
  assert (HK1ne : ~ K1 == 0).
  { apply q_neq_of_lt. exact HK1. }
  (* ---- 系数预算事实（Q 层固定，供逐点吸收） ---- *)
  (* Hc1：QicB·kE == 1/8；Hc2：QicB·(kEp+kapE) == 1/8 *)
  assert (Hc1 : Qle (Qmult QicB kE) (1 # 8)).
  { apply qeq_imp_qle.
    unfold QicB, kE.
    field. exact HcBne. }
  assert (Hc1' : Qle (Qmult QicB (Qplus kEp kapE)) (1 # 8)).
  { apply qeq_imp_qle.
    unfold QicB, kEp, kapE.
    field. exact HcBne. }
  (* Hc2/Hc2'：ME·QicA·QicB·kS ≤ 1/8、ME·QicA·QicB·(kSp+kapS) ≤ 1/8 *)
  set (Mterm := Qmult ME (Qmult QicA QicB)).
  assert (Hc2 : Qle (Qmult Mterm kS) (1 # 8)).
  { apply (Qle_trans (Qmult Mterm kS)
                     (Qmult (Qmult ME (1 # 8)) (Qinv (Qplus ME 1)))
                     (1 # 8)).
    - apply qeq_imp_qle.
      unfold Mterm, QicA, QicB, kS, invM1.
      field. all: repeat split; assumption.
    - apply (Qle_trans (Qmult (Qmult ME (1 # 8)) (Qinv (Qplus ME 1)))
                       (Qinv 8)
                       (1 # 8)).
      + apply (b5n_xinv_le (Qmult ME (1 # 8)) (Qplus ME 1) 8).
        * exact HME1.
        * change (Qlt 0 8). unfold Qlt. simpl. lia.
        * nra.
      + apply qeq_imp_qle. unfold Qinv. reflexivity. }
  assert (Hc2' : Qle (Qmult Mterm (Qplus kSp kapS)) (1 # 8)).
  { apply (Qle_trans (Qmult Mterm (Qplus kSp kapS))
                     (Qmult (Qmult ME (1 # 8)) (Qinv (Qplus ME 1)))
                     (1 # 8)).
    - apply qeq_imp_qle.
      unfold Mterm, QicA, QicB, kSp, kapS, invM1.
      field. all: repeat split; assumption.
    - apply (Qle_trans (Qmult (Qmult ME (1 # 8)) (Qinv (Qplus ME 1)))
                       (Qinv 8)
                       (1 # 8)).
      + apply (b5n_xinv_le (Qmult ME (1 # 8)) (Qplus ME 1) 8).
        * exact HME1.
        * change (Qlt 0 8). unfold Qlt. simpl. lia.
        * nra.
      + apply qeq_imp_qle. unfold Qinv. reflexivity. }
  (* 下界不等式：(K1·τ) + μ + kapS2 ≤ cA − cB（== cA/2，LHS == cA/4） *)
  assert (Htau_eq : Qle (Qmult K1 tau) (Qmult cA (1 # 8))).
  { apply qeq_imp_qle.
    unfold tau.
    field. all: repeat split; assumption. }
  assert (Hlb_ineq : Qle (Qplus (Qmult K1 tau) (Qplus mu kapS2)) (Qminus cA cB)).
  { apply (Qle_trans (Qplus (Qmult K1 tau) (Qplus mu kapS2))
                     (Qplus (Qmult cA (1 # 8)) (Qmult cA (1 # 8)))
                     (Qminus cA cB)).
    - apply Qplus_le_compat.
      + apply (Qle_trans (Qmult K1 tau) (Qmult cA (1 # 8)) (Qmult cA (1 # 8))).
        * exact Htau_eq.
        * apply Qle_refl.
      + apply (Qle_trans (Qplus mu kapS2) (Qmult cA (1 # 8)) (Qmult cA (1 # 8))).
        * apply qeq_imp_qle. unfold mu, kapS2. ring.
        * apply Qle_refl.
    - unfold cB. nra. }
  (* ---- eps 见证与份额 ---- *)
  destruct (b5n_eps_proj_lt eps Heps) as [e0 [He0T [Ne0 He0lt]]].
  assert (H2T : QltT 0 (1 # 2)) by (apply Qlt_to_QltT; change (Qlt 0 (1 # 2)); unfold Qlt; simpl; lia).
  assert (H4T : QltT 0 (1 # 4)) by (apply Qlt_to_QltT; change (Qlt 0 (1 # 4)); unfold Qlt; simpl; lia).
  assert (H8T : QltT 0 (1 # 8)) by (apply Qlt_to_QltT; change (Qlt 0 (1 # 8)); unfold Qlt; simpl; lia).
  assert (H16T : QltT 0 (1 # 16)) by (apply Qlt_to_QltT; change (Qlt 0 (1 # 16)); unfold Qlt; simpl; lia).
  (* eps 份额（Real）：epsE / epsS（E-diff 与 S-diff 主实例的斜率份额） *)
  set (epsE := real_mult eps (real_const kE)).
  assert (HepsE : real_lt real_zero epsE).
  { unfold epsE. apply real_mult_positive. { exact Heps. } { apply real_const_pos. exact HkET. } }
  set (epsS := real_mult eps (real_const kS)).
  assert (HepsS : real_lt real_zero epsS).
  { unfold epsS. apply real_mult_positive. { exact Heps. } { apply real_const_pos. exact HkST. } }
  (* 闭式实例化：δE（E-diff）、δS1/δS2（S-diff 主/常份额） *)
  destruct (b5a_E_diff_closed_r r Hr0 Hr1 x Hxr epsE HepsE) as [δE [HδE0 HδE]].
  destruct (b5a_S_diff_closed_r r Hr0 Hr1 x Hxr epsS HepsS) as [δS1 [HδS10 HδS1]].
  destruct (b5a_S_diff_closed_r r Hr0 Hr1 x Hxr (real_const 1) (real_const_pos 1 H1T))
    as [δS2 [HδS20 HδS2]].
  (* δ := min(min(min(δE, δS1), δS2), real_const τ) *)
  set (delta := real_min (real_min (real_min δE δS1) δS2) (real_const tau)).
  assert (Hdpos : real_lt real_zero delta).
  { unfold delta.
    apply real_min_pos.
    { apply real_min_pos.
      { apply real_min_pos. { exact HδE0. } { exact HδS10. } }
      { exact HδS20. } }
    { apply real_const_pos. exact HtauT. } }
  exists delta.
  split.
  { exact Hdpos. }
  { intros h Hh Hxh eps' Heps'.
    (* 提取 |h| < 分量 *)
    assert (Hh1 : real_lt (real_abs h) (real_min (real_min δE δS1) δS2)).
    { apply (real_min_lt_l h (real_min (real_min δE δS1) δS2) (real_const tau)).
      unfold delta in Hh. exact Hh. }
    assert (Hhτ : real_lt (real_abs h) (real_const tau)).
    { apply (real_min_lt_r h (real_min (real_min δE δS1) δS2) (real_const tau)).
      unfold delta in Hh. exact Hh. }
    assert (Hh2 : real_lt (real_abs h) (real_min δE δS1)).
    { apply (real_min_lt_l h (real_min δE δS1) δS2). exact Hh1. }
    assert (HhS2 : real_lt (real_abs h) δS2).
    { apply (real_min_lt_r h (real_min δE δS1) δS2). exact Hh1. }
    assert (HhE : real_lt (real_abs h) δE).
    { apply (real_min_lt_l h δE δS1). exact Hh2. }
    assert (HhS1 : real_lt (real_abs h) δS1).
    { apply (real_min_lt_r h δE δS1). exact Hh2. }
    destruct (b5n_eps_proj_lt eps' Heps') as [e1 [He1T [Ne1 He1lt]]].
    set (eta := Qmult (1 # 8) e1).
    assert (HetaT : QltT 0 eta).
    { unfold eta. apply Qlt_to_QltT.
      apply (Qmult_lt_0_compat (1 # 8) e1).
      - change (Qlt 0 (1 # 8)). unfold Qlt. simpl. lia.
      - apply QltT_to_Qlt. exact He1T. }
    (* eps' 份额（Real）：E-diff epsE'/margin shE、S-diff epsS'/margin shS *)
    set (epsE' := real_mult eps' (real_const kEp)).
    assert (HepsE' : real_lt real_zero epsE').
    { unfold epsE'. apply real_mult_positive. { exact Heps'. } { apply real_const_pos. exact HkEpT. } }
    set (shE := real_mult eps' (real_const kapE)).
    assert (HshE : real_lt real_zero shE).
    { unfold shE. apply real_mult_positive. { exact Heps'. } { apply real_const_pos. exact HkapET. } }
    set (epsS' := real_mult eps' (real_const kSp)).
    assert (HepsS' : real_lt real_zero epsS').
    { unfold epsS'. apply real_mult_positive. { exact Heps'. } { apply real_const_pos. exact HkSpT. } }
    set (shS := real_mult eps' (real_const kapS)).
    assert (HshS : real_lt real_zero shS).
    { unfold shS. apply real_mult_positive. { exact Heps'. } { apply real_const_pos. exact HkapST. } }
    (* 下界实例的常份额（Real，不依赖 eps'） *)
    assert (Hcμ : real_lt real_zero (real_const mu)).
    { apply real_const_pos. exact HmuT. }
    assert (HcκS2 : real_lt real_zero (real_const kapS2)).
    { apply real_const_pos. exact HkapS2T. }
    (* 逐点转换（real_le → per-n，margin 松弛） *)
    set (BE := real_plus (real_mult epsE (real_abs h)) epsE').
    destruct (b5i_abs_le_pointwise (b5e_E_err x Hx h Hxh) BE
               (HδE h HhE Hxh epsE' HepsE') shE HshE) as [NE HNE].
    set (BS1 := real_plus (real_mult epsS (real_abs h)) epsS').
    destruct (b5i_abs_le_pointwise (b5m_rS x h) BS1
               (HδS1 h HhS1 epsS' HepsS') shS HshS) as [NS HNS].
    set (BS2 := real_plus (real_mult (real_const 1) (real_abs h)) (real_const mu)).
    destruct (b5i_abs_le_pointwise (b5m_rS x h) BS2
               (HδS2 h HhS2 (real_const mu) Hcμ) (real_const kapS2) HcκS2) as [NS2 HNS2].
    (* |h_n| ≤ tau（b5i_h_le_const）、|d_n| ≤ 1 尾、逐点恒等 N *)
    destruct (b5i_h_le_const h tau Hhτ HtauT) as [Nτ HNτ].
    destruct (b5c_d_proj_le_one x) as [Nd Hd].
    destruct (b5m_J_dec_proj x h Hx Hxh) as [Ndec HNdec].
    (* 逐点预算（对 eps/eps' 见证） *)
    assert (Hen'g : forall n : nat, NatLe Ne1 n -> Qle 0 (projT1 eps' n)).
    { intros n Hn.
      apply (Qle_trans 0 e1 (projT1 eps' n)).
      { apply Qlt_le_weak. apply QltT_to_Qlt. exact He1T. }
      { apply Qlt_le_weak. exact (He1lt n Hn). } }
    set (Nmax := Nat.max (Nat.max Ne0 Ne1)
                 (Nat.max (Nat.max Ndec Nτ)
                  (Nat.max (Nat.max NE (Nat.max NS NS2)) (Nat.max NA Nd)))).
    (* 主装配：real_le → real_lt（左支），见证 eta *)
    left.
    exists eta.
    split.
    { exact HetaT. }
    { exists Nmax.
      intros n Hn.
      apply NatLe_drop in Hn.
      set (en := projT1 eps n).
      set (en' := projT1 eps' n).
      set (hn := Qabs (projT1 h n)).
      set (Dn := Qabs (projT1 (b5m_J_err x Hx h Hxh) n)).
      set (Sn := projT1 (b5a_S x) n).
      set (Shn := projT1 (b5a_S (real_plus x h)) n).
      set (dn := projT1 (b5a_atan_d x) n).
      set (rEn := projT1 (b5e_E_err x Hx h Hxh) n).
      set (rSn := projT1 (b5m_rS x h) n).
      set (Exn := projT1 (b5a_E x Hx) n).
      (* 尾指标 *)
      assert (HnNe0 : NatLe Ne0 n) by (apply NatLe_lift; lia).
      assert (HnNe1 : NatLe Ne1 n) by (apply NatLe_lift; lia).
      assert (HnNE : NatLe NE n) by (apply NatLe_lift; lia).
      assert (HnNS : NatLe NS n) by (apply NatLe_lift; lia).
      assert (HnNS2 : NatLe NS2 n) by (apply NatLe_lift; lia).
      assert (HnNτ : NatLe Nτ n) by (apply NatLe_lift; lia).
      assert (HnNd : (Nd <= n)%nat) by lia.
      assert (HnNdec : (Ndec <= n)%nat) by lia.
      assert (HnNA : (NA <= n)%nat) by lia.
      (* 非负 *)
      assert (Hen0 : Qle 0 en).
      { unfold en. apply (Qle_trans 0 e0 (projT1 eps n)).
        - apply Qlt_le_weak. apply QltT_to_Qlt. exact He0T.
        - apply Qlt_le_weak. exact (He0lt n HnNe0). }
      assert (Hen'0 : Qle 0 en').
      { unfold en'. exact (Hen'g n HnNe1). }
      assert (Hhn0 : Qle 0 hn). { unfold hn. apply Qabs_nonneg. }
      (* |h_n| ≤ tau、|d_n| ≤ 1、Sn ≥ cA *)
      assert (Hhτn : Qle (Qabs (projT1 h n)) tau).
      { unfold tau in *. exact (HNτ n HnNτ). }
      assert (Hdn1 : Qle (Qabs dn) 1).
      { unfold dn. exact (Hd n HnNd). }
      assert (HSnA : Qle cA Sn).
      { unfold Sn. exact (HNA n HnNA). }
      (* |rE_n| ≤ kE·en·hn + (kEp+kapE)·en'（E-diff 逐点化） *)
      assert (HrE : Qle (Qabs rEn)
                        (Qplus (Qmult (Qmult en kE) (Qabs (projT1 h n)))
                               (Qplus (Qmult en' kEp) (Qmult en' kapE)))).
      { apply (Qle_trans (Qabs rEn)
                         (Qplus (projT1 BE n) (projT1 shE n))
                         (Qplus (Qmult (Qmult en kE) (Qabs (projT1 h n)))
                                (Qplus (Qmult en' kEp) (Qmult en' kapE)))).
        - unfold rEn. exact (HNE n HnNE).
        - apply qeq_imp_qle.
          unfold BE, shE, en, en'.
          setoid_rewrite (real_plus_proj (real_mult epsE (real_abs h)) epsE' n).
          setoid_rewrite (real_mult_proj epsE (real_abs h) n).
          unfold epsE, epsE'.
          setoid_rewrite (real_mult_proj eps (real_const kE) n).
          rewrite (real_const_proj kE n).
          setoid_rewrite (real_abs_proj h n).
          setoid_rewrite (real_mult_proj eps' (real_const kEp) n).
          rewrite (real_const_proj kEp n).
          setoid_rewrite (real_mult_proj eps' (real_const kapE) n).
          rewrite (real_const_proj kapE n).
          ring. }
      (* |rS_n| ≤ kS·en·hn + (kSp+kapS)·en'（S-diff 主实例逐点化） *)
      assert (HrS : Qle (Qabs rSn)
                        (Qplus (Qmult (Qmult en kS) (Qabs (projT1 h n)))
                               (Qplus (Qmult en' kSp) (Qmult en' kapS)))).
      { apply (Qle_trans (Qabs rSn)
                         (Qplus (projT1 BS1 n) (projT1 shS n))
                         (Qplus (Qmult (Qmult en kS) (Qabs (projT1 h n)))
                                (Qplus (Qmult en' kSp) (Qmult en' kapS)))).
        - unfold rSn. exact (HNS n HnNS).
        - apply qeq_imp_qle.
          unfold BS1, shS, en, en'.
          setoid_rewrite (real_plus_proj (real_mult epsS (real_abs h)) epsS' n).
          setoid_rewrite (real_mult_proj epsS (real_abs h) n).
          unfold epsS, epsS'.
          setoid_rewrite (real_mult_proj eps (real_const kS) n).
          rewrite (real_const_proj kS n).
          setoid_rewrite (real_abs_proj h n).
          setoid_rewrite (real_mult_proj eps' (real_const kSp) n).
          rewrite (real_const_proj kSp n).
          setoid_rewrite (real_mult_proj eps' (real_const kapS) n).
          rewrite (real_const_proj kapS n).
          ring. }
      (* |rS_n| ≤ 1·hn + mu + kapS2（S-diff 常份额实例逐点化，下界用） *)
      assert (HrS2 : Qle (Qabs rSn)
                         (Qplus (Qabs (projT1 h n)) (Qplus mu kapS2))).
      { apply (Qle_trans (Qabs rSn)
                         (Qplus (projT1 BS2 n) (projT1 (real_const kapS2) n))
                         (Qplus (Qabs (projT1 h n)) (Qplus mu kapS2))).
        - unfold rSn. exact (HNS2 n HnNS2).
        - apply qeq_imp_qle.
          unfold BS2.
          setoid_rewrite (real_plus_proj (real_mult (real_const 1) (real_abs h))
                                         (real_const mu) n).
          setoid_rewrite (real_mult_proj (real_const 1) (real_abs h) n).
          rewrite (real_const_proj 1 n).
          setoid_rewrite (real_abs_proj h n).
          rewrite (real_const_proj mu n).
          rewrite (real_const_proj kapS2 n).
          ring. }
      (* |Ex_n| ≤ ME（sinA/cosA 逐点界 + |x_n| ≤ r；Exn == sAn − xn·cAn） *)
      assert (HEx : Qle (Qabs Exn) ME).
      { unfold Exn, b5a_E.
        rewrite (real_plus_proj (cauchy_real_sin (cauchy_real_arctan x Hx))
                                (real_opp (real_mult x (cauchy_real_cos (cauchy_real_arctan x Hx)))) n).
        rewrite (real_opp_proj (real_mult x (cauchy_real_cos (cauchy_real_arctan x Hx))) n).
        rewrite (real_mult_proj x (cauchy_real_cos (cauchy_real_arctan x Hx)) n).
        apply (Qle_trans
                 (Qabs (Qplus (projT1 (cauchy_real_sin (cauchy_real_arctan x Hx)) n)
                              (Qopp (Qmult (projT1 x n)
                                           (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n)))))
                 (Qplus (Qabs (projT1 (cauchy_real_sin (cauchy_real_arctan x Hx)) n))
                        (Qabs (Qmult (projT1 x n)
                                     (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n))))
                 ME).
        - apply (Qle_trans
                   (Qabs (Qplus (projT1 (cauchy_real_sin (cauchy_real_arctan x Hx)) n)
                                (Qopp (Qmult (projT1 x n)
                                             (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n)))))
                   (Qplus (Qabs (projT1 (cauchy_real_sin (cauchy_real_arctan x Hx)) n))
                          (Qabs (Qopp (Qmult (projT1 x n)
                                             (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n)))))
                   (Qplus (Qabs (projT1 (cauchy_real_sin (cauchy_real_arctan x Hx)) n))
                          (Qabs (Qmult (projT1 x n)
                                       (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n))))).
          + apply Qabs_triangle.
          + apply Qplus_le_compat.
            * apply Qle_refl.
            * apply qeq_imp_qle.
              apply (Qabs_opp (Qmult (projT1 x n)
                                     (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n))).
        - (* |sA| + |x·cA| ≤ Ms + r·Mc ≤ ME *)
          apply (Qle_trans
                   (Qplus (Qabs (projT1 (cauchy_real_sin (cauchy_real_arctan x Hx)) n))
                          (Qabs (Qmult (projT1 x n)
                                       (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n))))
                   (Qplus Ms (Qmult r Mc))
                   ME).
          + apply Qplus_le_compat.
            * apply (Qle_trans (Qabs (projT1 (cauchy_real_sin (cauchy_real_arctan x Hx)) n))
                               (Qabs (sin_partial n (arctan_partial n (projT1 x n))))
                               Ms).
              { apply qeq_imp_qle. apply Qabs_wd. apply Qeq_sym.
                setoid_rewrite (real_sin_proj (cauchy_real_arctan x Hx) n).
                setoid_rewrite (arctan_real_proj x Hx n).
                reflexivity. }
              { exact (HMs_all n). }
            * apply (Qle_trans (Qabs (Qmult (projT1 x n)
                                            (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n)))
                               (Qmult r (Qabs (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n)))
                               (Qmult r Mc)).
              { apply (Qle_trans (Qabs (Qmult (projT1 x n)
                                              (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n)))
                                 (Qmult (Qabs (projT1 x n))
                                        (Qabs (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n)))
                                 (Qmult r (Qabs (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n)))).
                - apply qeq_imp_qle.
                  apply (Qabs_Qmult (projT1 x n)
                                    (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n)).
                - apply (Qmult_le_compat_r (Qabs (projT1 x n)) r
                                           (Qabs (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n))).
                  + apply QleT'_to_Qle. exact (Hxr n).
                  + apply Qabs_nonneg. }
              { apply (sc_qmult_le_l (Qabs (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n))
                                     Mc r).
                - apply (Qle_trans (Qabs (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n))
                                   (Qabs (cos_partial n (arctan_partial n (projT1 x n))))
                                   Mc).
                  + apply qeq_imp_qle. apply Qabs_wd. apply Qeq_sym.
                    setoid_rewrite (real_cos_proj (cauchy_real_arctan x Hx) n).
                    setoid_rewrite (arctan_real_proj x Hx n).
                    reflexivity.
                  + exact (HMc_all n).
                - exact Hr0'. }
          + unfold ME. nra. }
      (* 商分母证书：|Qinv(Sn)| ≤ QicA *)
      assert (HQA : Qle (Qabs (Qinv Sn)) QicA).
      { unfold Sn, QicA. apply (b5m_inv_le Sn cA HcA HSnA). }
      (* Sxh ≥ cB：|ΔS| 界（r·M·hn + |rS|）→ K1·tau + mu + kapS2 ≤ cA − cB *)
      assert (Hdel0 : Qle (Qabs (Qminus Shn Sn))
                          (Qplus (Qmult (Qmult r M) (Qabs (projT1 h n)))
                                 (Qplus (Qabs (projT1 h n)) (Qplus mu kapS2)))).
      { (* Shn − Sn == (x·S·d·h)_n + rS_n *)
        apply (Qle_trans (Qabs (Qminus Shn Sn))
                         (Qplus (Qabs (Qmult (Qmult (projT1 x n) Sn) (Qmult dn (projT1 h n))))
                                (Qabs rSn))
                         (Qplus (Qmult (Qmult r M) (Qabs (projT1 h n)))
                                (Qplus (Qabs (projT1 h n)) (Qplus mu kapS2)))).
        - (* triangle：|Shn − Sn| == |P + rS| ≤ |P| + |rS| *)
          apply (Qle_trans (Qabs (Qminus Shn Sn))
                           (Qabs (Qplus (Qmult (Qmult (projT1 x n) Sn) (Qmult dn (projT1 h n))) rSn))
                           (Qplus (Qabs (Qmult (Qmult (projT1 x n) Sn) (Qmult dn (projT1 h n))))
                                  (Qabs rSn))).
          + apply qeq_imp_qle.
            apply (Qabs_wd (Qminus Shn Sn)
                           (Qplus (Qmult (Qmult (projT1 x n) Sn) (Qmult dn (projT1 h n))) rSn)).
            unfold Shn, Sn, dn, rSn.
            unfold b5m_rS.
            rewrite (real_plus_proj (b5a_S (real_plus x h))
                                    (real_opp (real_plus (b5a_S x)
                                               (real_mult (real_mult x (b5a_S x))
                                                          (real_mult (b5a_atan_d x) h)))) n).
            rewrite (real_opp_proj (real_plus (b5a_S x)
                                    (real_mult (real_mult x (b5a_S x))
                                               (real_mult (b5a_atan_d x) h))) n).
            rewrite (real_plus_proj (b5a_S x)
                                    (real_mult (real_mult x (b5a_S x))
                                               (real_mult (b5a_atan_d x) h)) n).
            rewrite (real_mult_proj (real_mult x (b5a_S x))
                                    (real_mult (b5a_atan_d x) h) n).
            rewrite (real_mult_proj x (b5a_S x) n).
            rewrite (real_mult_proj (b5a_atan_d x) h n).
            cbn [projT1 real_zero].
            ring.
          + apply Qabs_triangle.
        - (* |P| ≤ r·M·1·hn、|rS_n| ≤ hn + mu + kapS2（HrS2） *)
          apply Qplus_le_compat.
          + (* |(x·S·d·h)_n| ≤ r·M·1·hn *)
            apply (Qle_trans (Qabs (Qmult (Qmult (projT1 x n) Sn) (Qmult dn (projT1 h n))))
                             (Qmult (Qmult (Qabs (projT1 x n)) (Qabs Sn)) (Qmult (Qabs dn) (Qabs (projT1 h n))))
                             (Qmult (Qmult r M) (Qabs (projT1 h n)))).
            * apply qeq_imp_qle.
              apply (Qeq_trans (Qabs (Qmult (Qmult (projT1 x n) Sn) (Qmult dn (projT1 h n))))
                               (Qmult (Qabs (Qmult (projT1 x n) Sn)) (Qabs (Qmult dn (projT1 h n))))
                               (Qmult (Qmult (Qabs (projT1 x n)) (Qabs Sn)) (Qmult (Qabs dn) (Qabs (projT1 h n))))).
              { apply (Qabs_Qmult (Qmult (projT1 x n) Sn) (Qmult dn (projT1 h n))). }
              { apply Qmult_comp.
                - apply (Qabs_Qmult (projT1 x n) Sn).
                - apply (Qabs_Qmult dn (projT1 h n)). }
            * (* (|xn|·|Sn|)·(|dn|·|hn|) ≤ (r·M)·(1·hn) *)
              apply (Qle_trans (Qmult (Qmult (Qabs (projT1 x n)) (Qabs Sn)) (Qmult (Qabs dn) (Qabs (projT1 h n))))
                               (Qmult (Qmult r M) (Qmult 1 (Qabs (projT1 h n))))
                               (Qmult (Qmult r M) (Qabs (projT1 h n)))).
              { apply (Qle_trans (Qmult (Qmult (Qabs (projT1 x n)) (Qabs Sn)) (Qmult (Qabs dn) (Qabs (projT1 h n))))
                                 (Qmult (Qmult r M) (Qmult (Qabs dn) (Qabs (projT1 h n))))
                                 (Qmult (Qmult r M) (Qmult 1 (Qabs (projT1 h n))))).
                - apply (Qmult_le_compat_r (Qmult (Qabs (projT1 x n)) (Qabs Sn)) (Qmult r M)
                                           (Qmult (Qabs dn) (Qabs (projT1 h n)))).
                  + apply (Qle_trans (Qmult (Qabs (projT1 x n)) (Qabs Sn))
                                     (Qmult r (Qabs Sn))
                                     (Qmult r M)).
                    * apply (Qmult_le_compat_r (Qabs (projT1 x n)) r (Qabs Sn)).
                      { apply QleT'_to_Qle. exact (Hxr n). }
                      { apply Qabs_nonneg. }
                    * apply (sc_qmult_le_l (Qabs Sn) M r).
                      { unfold Sn. exact (HMall n). }
                      { exact Hr0'. }
                  + apply Qmult_le_0_compat.
                    * apply Qabs_nonneg.
                    * apply Qabs_nonneg.
                - apply (sc_qmult_le_l (Qmult (Qabs dn) (Qabs (projT1 h n)))
                                       (Qmult 1 (Qabs (projT1 h n)))
                                       (Qmult r M)).
                  + apply (Qmult_le_compat_r (Qabs dn) 1 (Qabs (projT1 h n))).
                    * exact Hdn1.
                    * apply Qabs_nonneg.
                  + apply Qmult_le_0_compat.
                    * exact Hr0'.
                    * exact HM0. }
              { apply qeq_imp_qle. ring. }
          + (* |rS_n| ≤ hn + mu + kapS2 *)
            apply (Qle_trans (Qabs rSn)
                             (Qplus (Qabs (projT1 h n)) (Qplus mu kapS2))
                             (Qplus (Qabs (projT1 h n)) (Qplus mu kapS2))).
            * exact HrS2.
            * apply Qle_refl. }
      (* |ΔS| ≤ K1·tau + mu + kapS2（hn ≤ tau） *)
      assert (Hdel : Qle (Qabs (Qminus Shn Sn))
                         (Qplus (Qmult K1 tau) (Qplus mu kapS2))).
      { apply (Qle_trans (Qabs (Qminus Shn Sn))
                         (Qplus (Qmult (Qmult r M) tau) (Qplus tau (Qplus mu kapS2)))
                         (Qplus (Qmult K1 tau) (Qplus mu kapS2))).
        - apply (Qle_trans (Qabs (Qminus Shn Sn))
                           (Qplus (Qmult (Qmult r M) (Qabs (projT1 h n)))
                                  (Qplus (Qabs (projT1 h n)) (Qplus mu kapS2)))
                           (Qplus (Qmult (Qmult r M) tau) (Qplus tau (Qplus mu kapS2)))).
          + exact Hdel0.
          + apply Qplus_le_compat.
            * apply (sc_qmult_le_l (Qabs (projT1 h n)) tau (Qmult r M)).
              { exact Hhτn. }
              { apply Qmult_le_0_compat. { exact Hr0'. } { exact HM0. } }
            * apply Qplus_le_compat.
              { exact Hhτn. }
              { apply Qle_refl. }
        - apply qeq_imp_qle. unfold K1. ring. }
      (* Shn ≥ cB（Sn ≥ cA、|ΔS| ≤ B0、B0 ≤ cA − cB） *)
      assert (HShnB : Qle cB Shn).
      { (* Sn ≤ Shn + |Δ| 且 |Δ| ≤ B0（Hdel）⟹ Sn ≤ Shn + B0 *)
        assert (HS2 : Qle Sn (Qplus Shn (Qplus (Qmult K1 tau) (Qplus mu kapS2)))).
        { apply (Qle_trans Sn (Qplus Shn (Qabs (Qminus Shn Sn)))
                              (Qplus Shn (Qplus (Qmult K1 tau) (Qplus mu kapS2)))).
          - apply (Qle_trans Sn (Qplus Shn (Qminus Sn Shn))
                                (Qplus Shn (Qabs (Qminus Shn Sn)))).
            + apply qeq_imp_qle. ring.
            + apply Qplus_le_compat.
              * apply Qle_refl.
              * apply (Qle_trans (Qminus Sn Shn) (Qabs (Qminus Sn Shn))
                                 (Qabs (Qminus Shn Sn))).
                { apply Qle_Qabs. }
                { apply qeq_imp_qle.
                  apply (Qeq_trans (Qabs (Qminus Sn Shn))
                                   (Qabs (Qopp (Qminus Shn Sn)))
                                   (Qabs (Qminus Shn Sn))).
                  - apply Qabs_wd. ring.
                  - apply (Qabs_opp (Qminus Shn Sn)). }
          - apply Qplus_le_compat.
            + apply Qle_refl.
            + exact Hdel. }
        (* cB ≤ cA − B0（Hlb_ineq）、cA ≤ Sn（HSnA）、Sn ≤ Shn + B0 ⟹ cB ≤ Shn *)
        nra. }
      (* 商分母证书：|Qinv(Shn)| ≤ QicB *)
      assert (HQB : Qle (Qabs (Qinv Shn)) QicB).
      { unfold Shn, QicB. apply (b5m_inv_le Shn cB HcB HShnB). }
      (* b5m_J_abs_tri 主步 *)
      set (RE := Qplus (Qmult (Qmult en kE) (Qabs (projT1 h n)))
                       (Qplus (Qmult en' kEp) (Qmult en' kapE))).
      set (RS := Qplus (Qmult (Qmult en kS) (Qabs (projT1 h n)))
                       (Qplus (Qmult en' kSp) (Qmult en' kapS))).
      assert (Hmain0 : Qle Dn (Qplus (Qmult QicB RE) (Qmult Mterm RS))).
      { unfold Dn.
        apply (b5m_J_abs_tri x h Hx Hxh n QicA QicB ME RE RS).
        - exact HQA.
        - exact HQB.
        - unfold Exn. exact HEx.
        - unfold rEn. exact HrE.
        - unfold rSn. exact HrS.
        - unfold QicA. apply Qlt_le_weak. apply Qinv_lt_0_compat. exact HcA.
        - unfold QicB. apply Qlt_le_weak. apply Qinv_lt_0_compat. exact HcB.
        - exact (HNdec n HnNdec). }
      (* 系数吸收：QicB·RE ≤ (1/8)·en·hn + (1/8)·en'；Mterm·RS ≤ 同形 *)
      assert (HT1 : Qle (Qmult QicB (Qmult (Qmult en kE) (Qabs (projT1 h n))))
                        (Qmult (1 # 8) (Qmult en hn))).
      { apply (Qle_trans (Qmult QicB (Qmult (Qmult en kE) (Qabs (projT1 h n))))
                         (Qmult (Qmult QicB kE) (Qmult en hn))
                         (Qmult (1 # 8) (Qmult en hn))).
        - apply qeq_imp_qle. unfold hn. ring.
        - apply (Qmult_le_compat_r (Qmult QicB kE) (1 # 8) (Qmult en hn)).
          + exact Hc1.
          + apply Qmult_le_0_compat.
            * exact Hen0.
            * exact Hhn0. }
      assert (HT2 : Qle (Qmult QicB (Qplus (Qmult en' kEp) (Qmult en' kapE)))
                        (Qmult (1 # 8) en')).
      { apply (Qle_trans (Qmult QicB (Qplus (Qmult en' kEp) (Qmult en' kapE)))
                         (Qmult (Qmult QicB (Qplus kEp kapE)) en')
                         (Qmult (1 # 8) en')).
        - apply qeq_imp_qle. ring.
        - apply (Qmult_le_compat_r (Qmult QicB (Qplus kEp kapE)) (1 # 8) en').
          + exact Hc1'.
          + exact Hen'0. }
      assert (HT3 : Qle (Qmult Mterm (Qmult (Qmult en kS) (Qabs (projT1 h n))))
                        (Qmult (1 # 8) (Qmult en hn))).
      { apply (Qle_trans (Qmult Mterm (Qmult (Qmult en kS) (Qabs (projT1 h n))))
                         (Qmult (Qmult Mterm kS) (Qmult en hn))
                         (Qmult (1 # 8) (Qmult en hn))).
        - apply qeq_imp_qle. unfold hn. ring.
        - apply (Qmult_le_compat_r (Qmult Mterm kS) (1 # 8) (Qmult en hn)).
          + exact Hc2.
          + apply Qmult_le_0_compat.
            * exact Hen0.
            * exact Hhn0. }
      assert (HT4 : Qle (Qmult Mterm (Qplus (Qmult en' kSp) (Qmult en' kapS)))
                        (Qmult (1 # 8) en')).
      { apply (Qle_trans (Qmult Mterm (Qplus (Qmult en' kSp) (Qmult en' kapS)))
                         (Qmult (Qmult Mterm (Qplus kSp kapS)) en')
                         (Qmult (1 # 8) en')).
        - apply qeq_imp_qle. ring.
        - apply (Qmult_le_compat_r (Qmult Mterm (Qplus kSp kapS)) (1 # 8) en').
          + exact Hc2'.
          + exact Hen'0. }
      (* 组装逐点主界：|Dn| ≤ en·hn + (3/4)·en' *)
      assert (Hmain : Qle Dn (Qplus (Qmult en hn) (Qmult (3 # 4) en'))).
      { apply (Qle_trans Dn
                         (Qplus (Qmult QicB RE) (Qmult Mterm RS))
                         (Qplus (Qmult en hn) (Qmult (3 # 4) en'))).
        - exact Hmain0.
        - (* 展开并吸收：QicB·RE + Mterm·RS ≤ (1/8)(en hn)+(1/8)en' 各两份 *)
          apply (Qle_trans (Qplus (Qmult QicB RE) (Qmult Mterm RS))
                           (Qplus (Qplus (Qmult QicB (Qmult (Qmult en kE) (Qabs (projT1 h n))))
                                         (Qmult QicB (Qplus (Qmult en' kEp) (Qmult en' kapE))))
                                  (Qplus (Qmult Mterm (Qmult (Qmult en kS) (Qabs (projT1 h n))))
                                         (Qmult Mterm (Qplus (Qmult en' kSp) (Qmult en' kapS)))))
                           (Qplus (Qmult en hn) (Qmult (3 # 4) en'))).
          + apply qeq_imp_qle. unfold RE, RS, hn. ring.
          + apply (Qle_trans
                     (Qplus (Qplus (Qmult QicB (Qmult (Qmult en kE) (Qabs (projT1 h n))))
                                   (Qmult QicB (Qplus (Qmult en' kEp) (Qmult en' kapE))))
                            (Qplus (Qmult Mterm (Qmult (Qmult en kS) (Qabs (projT1 h n))))
                                   (Qmult Mterm (Qplus (Qmult en' kSp) (Qmult en' kapS)))))
                     (Qplus (Qplus (Qmult (1 # 8) (Qmult en hn)) (Qmult (1 # 8) en'))
                            (Qplus (Qmult (1 # 8) (Qmult en hn)) (Qmult (1 # 8) en')))
                     (Qplus (Qmult en hn) (Qmult (3 # 4) en'))).
            * apply Qplus_le_compat.
              { apply Qplus_le_compat. { exact HT1. } { exact HT2. } }
              { apply Qplus_le_compat. { exact HT3. } { exact HT4. } }
            * nra. }
      (* margin：eta < (1/4)·en'；Hfin：eta < (en·hn + en') − Dn *)
      assert (Hq4e : Qlt eta (Qmult (1 # 4) en')).
      { unfold eta, en'. apply (b5n_quarter_gt e1 (projT1 eps' n)).
        - apply QltT_to_Qlt. exact He1T.
        - exact (He1lt n HnNe1). }
      assert (Hfin : Qlt eta (Qminus (Qplus (Qmult en hn) en') Dn)).
      { apply (b5n_close Dn hn en en' eta).
        - unfold Dn. exact Hmain.
        - unfold en'. exact Hq4e. }
      apply Qlt_to_QltT.
      apply (Qlt_le_trans eta
             (Qminus (Qplus (Qmult en hn) en') Dn)
             (Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                     (projT1 (real_abs (b5m_J_err x Hx h Hxh)) n))).
      - exact Hfin.
      - apply qeq_imp_qle. apply Qeq_sym.
        setoid_rewrite (real_plus_proj (real_mult eps (real_abs h)) eps' n).
        setoid_rewrite (real_mult_proj eps (real_abs h) n).
        setoid_rewrite (real_abs_proj h n).
        setoid_rewrite (real_abs_proj (b5m_J_err x Hx h Hxh) n).
        unfold en, en', hn, Dn.
        ring. } }
Qed.

(* ============================================================ *)
(* 块 item12（前缀 b5d8_——主件 b5d8_J_deriv_zero_tail_exp）——来源：演变/.ablation/sc2_parallel/sc2_b5a_ode/sc2_b5a_item12.v。 *)
(* ============================================================ *)

(* ============================================================ *)
(* §0 主件 b5d8_J_deriv_zero_tail_exp（C6 显式参数化定稿语句）   *)
(*   语句 = δC-审查 §1.6 + δB-审查-ScA下界 §4.2 草案：同束参数   *)
(*   （cA/M/Ms/Mc + HcA/HM/HMs/HMc）加于量词头部；N0/Hxr 尾证书  *)
(*   与 Hx1 全 n ≤1 原样；误差 J(x+h)−J(x) 同 item11 C5 形态但   *)
(*   基点证书 = Hx1（照源件 L1365–1377）。界前提载体 = x̂ :=      *)
(*   b5m_tailtrunc x N0（C5 expl 调用点——见文件头改造 2 与进度   *)
(*   §3 的形态核实）。前提为未命名箭头（intros 处命名             *)
(*   HNA/HMall/HMs_all/HMc_all；HNA 用 (NA<=n)%nat 形——item11    *)
(*   §4 形态决策：NatLe 与 (<=)%nat 不可转换）。                  *)
(* ============================================================ *)
Lemma b5d8_J_deriv_zero_tail_exp :
  forall (r : Q) (Hr0 : Qle 0 r) (Hr1 : Qlt r 1),
  forall (cA M Ms Mc : Q)
         (HcA : Qlt 0 cA) (HM : Qlt 0 M)
         (HMs : QltT 0 Ms) (HMc : QltT 0 Mc),
  forall (x : Real) (N0 : nat)
    (Hxr : forall n : nat, NatLe N0 n -> QleT' (Qabs (projT1 x n)) r),
  forall (Hx1 : forall n : nat, QleT' (Qabs (projT1 x n)) 1),
  forall (NA : nat),
  (forall n : nat, (NA <= n)%nat -> Qle cA (projT1 (b5a_S (b5m_tailtrunc x N0)) n)) ->
  (forall n : nat, Qle (Qabs (projT1 (b5a_S (b5m_tailtrunc x N0)) n)) M) ->
  (forall n : nat,
     Qle (Qabs (sin_partial n (arctan_partial n (projT1 (b5m_tailtrunc x N0) n)))) Ms) ->
  (forall n : nat,
     Qle (Qabs (cos_partial n (arctan_partial n (projT1 (b5m_tailtrunc x N0) n)))) Mc) ->
  forall (eps : Real), real_lt real_zero eps ->
  sigT (fun delta : Real => And (real_lt real_zero delta)
    (forall (h : Real), real_lt (real_abs h) delta ->
      forall (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1),
      forall (eps' : Real), real_lt real_zero eps' ->
      real_le (real_abs (real_plus (b5c_J (real_plus x h) Hxh)
                 (real_opp (b5c_J x Hx1))))
              (real_plus (real_mult eps (real_abs h)) eps'))).
Proof.
  intros r Hr0 Hr1 cA M Ms Mc HcA HM HMs HMc x N0 Hxr Hx1 NA HNA HMall HMs_all HMc_all eps Heps.
  (* 截断基点的全 n r 证书 *)
  assert (Hx̂r : forall n : nat,
            QleT' (Qabs (projT1 (b5m_tailtrunc x N0) n)) r).
  { apply (b5m_tailtrunc_r r Hr0 N0 x). exact Hxr. }
  (* 黑盒：b5a_J_deriv_zero @ (trunc x N0, Hx̂r) *)
  (* δ-C C6：黑盒调用点改调 C5 显式主件 b5d7_J_deriv_zero_exp @ *)
  (*   (trunc x N0, 显式参数束)；δ := δ_exp @ (x̂, 束) 透传        *)
  destruct (b5d7_J_deriv_zero_exp r Hr0 Hr1 cA M Ms Mc HcA HM HMs HMc (b5m_tailtrunc x N0) Hx̂r NA HNA HMall HMs_all HMc_all eps Heps)
    as [delta [Hd0 Hd]].
  exists delta.
  split.
  { exact Hd0. }
  { intros h Hh Hxh eps' Heps'.
    (* ĥ := trunc h N0 满足 |ĥ| < delta（ĥ == h ⟹ |ĥ| == |h|） *)
    assert (Hĥlt : real_lt (real_abs (b5m_tailtrunc h N0)) delta).
    { apply (RealSetoid.real_lt_compat (real_abs h)
                                       (real_abs (b5m_tailtrunc h N0))
                                       delta delta).
      - apply real_eq_sym.
        apply (real_abs_eq_compat (b5m_tailtrunc h N0) h).
        exact (b5m_tailtrunc_eq h N0).
      - apply real_eq_refl.
      - exact Hh. }
    (* cw_unit (trunc x N0 + trunc h N0)：由 Hxh 逐点析出 *)
    assert (Hxĥ : forall n : nat,
              QleT' (Qabs (projT1 (real_plus (b5m_tailtrunc x N0)
                                             (b5m_tailtrunc h N0)) n)) 1).
    { exact (b5m_plus_tailtrunc_unit x h N0 Hxh). }
    (* 黑盒模量在截断基点 *)
    assert (Hmod : real_le
      (real_abs (real_plus
        (b5c_J (real_plus (b5m_tailtrunc x N0) (b5m_tailtrunc h N0)) Hxĥ)
        (real_opp (b5c_J (b5m_tailtrunc x N0)
                         (b3rr_dom_r1 (b5m_tailtrunc x N0) r Hx̂r Hr1)))))
      (real_plus (real_mult eps (real_abs (b5m_tailtrunc h N0))) eps')).
    { exact (Hd (b5m_tailtrunc h N0) Hĥlt Hxĥ eps' Heps'). }
    (* real_eq 桥：x̂ == x、ĥ == h、x̂+ĥ == x+h *)
    assert (Hxeq : real_eq (b5m_tailtrunc x N0) x).
    { exact (b5m_tailtrunc_eq x N0). }
    assert (Hheq : real_eq (b5m_tailtrunc h N0) h).
    { exact (b5m_tailtrunc_eq h N0). }
    assert (Hpeq : real_eq (real_plus (b5m_tailtrunc x N0) (b5m_tailtrunc h N0))
                           (real_plus x h)).
    { apply (RealSetoid.real_eq_plus_compat
               (b5m_tailtrunc x N0) (b5m_tailtrunc h N0) x h).
      - exact Hxeq.
      - exact Hheq. }
    (* J 值外延传输 *)
    assert (Hj1 : real_eq (b5c_J (real_plus x h) Hxh)
                          (b5c_J (real_plus (b5m_tailtrunc x N0) (b5m_tailtrunc h N0)) Hxĥ)).
    { apply (b5m_J_wd (real_plus x h)
                      (real_plus (b5m_tailtrunc x N0) (b5m_tailtrunc h N0))
                      Hxh Hxĥ).
      apply real_eq_sym. exact Hpeq. }
    assert (Hj2 : real_eq (b5c_J x Hx1)
                          (b5c_J (b5m_tailtrunc x N0)
                                 (b3rr_dom_r1 (b5m_tailtrunc x N0) r Hx̂r Hr1))).
    { apply (b5m_J_wd x (b5m_tailtrunc x N0) Hx1
                      (b3rr_dom_r1 (b5m_tailtrunc x N0) r Hx̂r Hr1)).
      apply real_eq_sym. exact Hxeq. }
    (* 差 |J(x+h) − J(x)| == |J(x̂+ĥ) − J(x̂)|（abs/plus/opp compat） *)
    assert (HA : real_eq
      (real_abs (real_plus (b5c_J (real_plus x h) Hxh) (real_opp (b5c_J x Hx1))))
      (real_abs (real_plus
        (b5c_J (real_plus (b5m_tailtrunc x N0) (b5m_tailtrunc h N0)) Hxĥ)
        (real_opp (b5c_J (b5m_tailtrunc x N0)
                         (b3rr_dom_r1 (b5m_tailtrunc x N0) r Hx̂r Hr1)))))).
    { apply (RealSetoid.real_eq_abs_compat
        (real_plus (b5c_J (real_plus x h) Hxh) (real_opp (b5c_J x Hx1)))
        (real_plus (b5c_J (real_plus (b5m_tailtrunc x N0) (b5m_tailtrunc h N0)) Hxĥ)
                   (real_opp (b5c_J (b5m_tailtrunc x N0)
                                    (b3rr_dom_r1 (b5m_tailtrunc x N0) r Hx̂r Hr1))))).
      apply (RealSetoid.real_eq_plus_compat
        (b5c_J (real_plus x h) Hxh)
        (real_opp (b5c_J x Hx1))
        (b5c_J (real_plus (b5m_tailtrunc x N0) (b5m_tailtrunc h N0)) Hxĥ)
        (real_opp (b5c_J (b5m_tailtrunc x N0)
                         (b3rr_dom_r1 (b5m_tailtrunc x N0) r Hx̂r Hr1)))).
      - exact Hj1.
      - apply (RealSetoid.real_eq_opp_compat
                 (b5c_J x Hx1)
                 (b5c_J (b5m_tailtrunc x N0)
                        (b3rr_dom_r1 (b5m_tailtrunc x N0) r Hx̂r Hr1))).
        exact Hj2. }
    (* 界 eps|ĥ| + eps' == eps|h| + eps'（|ĥ| == |h|） *)
    assert (HB : real_eq
      (real_plus (real_mult eps (real_abs (b5m_tailtrunc h N0))) eps')
      (real_plus (real_mult eps (real_abs h)) eps')).
    { apply (RealSetoid.real_eq_plus_compat
        (real_mult eps (real_abs (b5m_tailtrunc h N0))) eps'
        (real_mult eps (real_abs h)) eps').
      - apply (RealSetoid.real_eq_mult_compat
          eps (real_abs (b5m_tailtrunc h N0)) eps (real_abs h)).
        + apply real_eq_refl.
        + apply (real_abs_eq_compat (b5m_tailtrunc h N0) h).
          exact (b5m_tailtrunc_eq h N0).
      - apply real_eq_refl. }
    (* 模量回传：real_le_compat 把 (x̂,ĥ) 模量传回 (x,h) *)
    apply (RealSetoid.real_le_compat
      (real_abs (real_plus
        (b5c_J (real_plus (b5m_tailtrunc x N0) (b5m_tailtrunc h N0)) Hxĥ)
        (real_opp (b5c_J (b5m_tailtrunc x N0)
                         (b3rr_dom_r1 (b5m_tailtrunc x N0) r Hx̂r Hr1)))))
      (real_abs (real_plus (b5c_J (real_plus x h) Hxh) (real_opp (b5c_J x Hx1))))
      (real_plus (real_mult eps (real_abs (b5m_tailtrunc h N0))) eps')
      (real_plus (real_mult eps (real_abs h)) eps')).
    - apply real_eq_sym. exact HA.
    - exact HB.
    - exact Hmod. }
Qed.

(* ============================================================ *)
(* 块 item15（前缀 b5dE_——主件 b5dE_S_ub_tail_q）——来源：演变/.ablation/sc2_parallel/sc2_b5a_ode/sc2_b5a_item15.v。 *)
(* ============================================================ *)

(* ============================================================ *)
(* §0 Q 层小件（b5dE_ 独占；全部真 Qed；nra/vm_compute 证毕）    *)
(* ============================================================ *)

(* Qlt 0 (1/2)（Qdiv 写法；vm_compute 闭值判定） *)
Lemma b5dE_half_pos_div : Qlt 0 (1 / 2).
Proof. vm_compute. reflexivity. Qed.

(* Qlt (1/2) 1 *)
Lemma b5dE_half_lt_one_div : Qlt (1 / 2) 1.
Proof. vm_compute. reflexivity. Qed.

(* Qlt 0 1 *)
Lemma b5dE_zero_lt_one : Qlt 0 1.
Proof. vm_compute. reflexivity. Qed.

(* Qle 0 1 *)
Lemma b5dE_zero_le_one : Qle 0 1.
Proof.
  (* ToyR 替换：Z 层直构（消 Qlt_le_weak→b5dE_zero_lt_one 两跳转发）：
     Qle 展开 = 交叉积 Z.le，字面归约后线性判定闭合 *)
  unfold Qle.
  simpl.
  lia.
Qed.

(* 0 < q、q < 1 ⟹ e0 := (1 − q²)·(1/2) > 0（nra 非线性证毕） *)
Lemma b5dE_e0_pos : forall (q : Q), Qlt 0 q -> Qlt q 1 ->
  Qlt 0 ((1 - q * q) * (1 # 2)).
Proof. intros q Hq0 Hq1. nra. Qed.

(* 0 < q、q < 1 ⟹ q² + e0 < 1（e0 := (1 − q²)·(1/2)；严格 gap） *)
Lemma b5dE_e0_sum_lt_one : forall (q : Q), Qlt 0 q -> Qlt q 1 ->
  Qlt (q * q + (1 - q * q) * (1 # 2)) 1.
Proof. intros q Hq0 Hq1. nra. Qed.

(* Q 层内核：1 ≤ x ∧ x < 2 ⟹ |x| ≤ 2（主件尾步） *)
Lemma b5dE_q_abs_le_of_bounds : forall (x : Q),
  Qle 1 x -> Qlt x 2 -> Qle (Qabs x) 2.
Proof.
  intros x Hlb Hup.
  apply (Qle_trans (Qabs x) x 2).
  - apply qeq_imp_qle. apply (Qabs_pos x).
    apply (Qle_trans 0 1 x b5dE_zero_le_one Hlb).
  - apply Qlt_le_weak. exact Hup.
Qed.

(* ============================================================ *)
(* §1 Real 层证书小件（b5dE_ 独占；全部真 Qed）                 *)
(* ============================================================ *)

(* real_const 1 == real_one 桥（real_lt 与 real_one 域互通） *)
Lemma b5dE_const1_eq_one : real_eq (real_const 1) real_one.
Proof.
  apply real_eq_of_zero_diff.
  intro n.
  rewrite (real_const_proj 1 n).
  cbn [projT1 real_one].
  ring.
Qed.

(* q > 0 ⟹ 0 < real_const q（real_const_pos L36290 实例） *)
Lemma b5dE_q_pos : forall (q : Q) (Hq0 : Qlt 0 q),
  real_lt real_zero (real_const q).
Proof.
  intros q Hq0.
  apply real_const_pos.
  apply Qlt_to_QltT.
  exact Hq0.
Qed.

(* 0 < real_const (1/2)（real_const_pos 实例，Qdiv 写法） *)
Lemma b5dE_half_pos_real : real_lt real_zero (real_const (1 / 2)).
Proof.
  apply real_const_pos.
  apply Qlt_to_QltT.
  exact b5dE_half_pos_div.
Qed.

(* ============================================================ *)
(* §2 Real 层界链（b5dE_ 独占；全部真 Qed）                     *)
(*   链：log(1+q·q) < real_const 1 → ×(1/2) → exp 单调 →        *)
(*        S(q) < exp(1/2) ≤ 2（inv(1/2) == 2 桥）                *)
(* ============================================================ *)

(* ============================================================ *)
(* 件 b5dE_log_ub_one：0 < q < 1 ⟹ log(1 + q²) < real_const 1   *)
(*   链：t := real_const q · real_const q == real_const (q·q)     *)
(*     （real_eq_of_zero_diff 逐点）⟹ log(1+t) ≤ t + real_const   *)
(*     e0（real_log_one_plus_le_eps L44229，e0 := (1−q²)(1/2)）   *)
(*     ≤ real_const (q²+e0)（le_trans + plus_compat + const 桥）  *)
(*     < real_const 1（real_const_lt L37095；q²+e0 < 1 严格分离） *)
(*     ⟹ 经 real_le_lt_trans L6212 证毕。零 log 闭式值依赖。       *)
(* ============================================================ *)
Lemma b5dE_log_ub_one : forall (q : Q) (Hq0 : Qlt 0 q) (Hq1 : Qlt q 1),
  real_lt (real_log (real_plus real_one (real_mult (real_const q) (real_const q)))
                    (b5a_one_plus_sq_pos (real_const q)))
          (real_const 1).
Proof.
  intros q Hq0 Hq1.
  set (t := real_mult (real_const q) (real_const q)).
  set (e0 := (1 - q * q) * (1 # 2)).
  (* t == real_const (q·q)（逐点投影 + cbn + ring） *)
  assert (Hteq : real_eq t (real_const (q * q))).
  { apply real_eq_of_zero_diff. intro n.
    unfold t.
    setoid_rewrite (real_mult_proj (real_const q) (real_const q) n).
    cbn [projT1 real_const].
    ring. }
  (* e0 > 0、q² + e0 < 1（Q 层 nra，分离证书） *)
  assert (He0 : Qlt 0 e0).
  { unfold e0. exact (b5dE_e0_pos q Hq0 Hq1). }
  assert (He1 : Qlt (q * q + e0) 1).
  { unfold e0. exact (b5dE_e0_sum_lt_one q Hq0 Hq1). }
  (* eps0 := real_const e0 > 0 *)
  assert (Heps0 : real_lt real_zero (real_const e0)).
  { apply real_const_pos. apply Qlt_to_QltT. exact He0. }
  (* log(1+t) ≤ t + eps0 *)
  assert (Hlog1 : real_le (real_log (real_plus real_one t) (b5a_one_plus_sq_pos (real_const q)))
                          (real_plus t (real_const e0))).
  { apply (real_log_one_plus_le_eps t (real_const e0) (b5a_one_plus_sq_pos (real_const q)) Heps0). }
  (* t ≤ real_const (q·q)（real_eq → real_le） *)
  assert (Hle_t : real_le t (real_const (q * q))).
  { apply RealSetoid.real_eq_le. exact Hteq. }
  (* t + eps0 ≤ real_const(q·q) + eps0 *)
  assert (Hle_sum : real_le (real_plus t (real_const e0))
                            (real_plus (real_const (q * q)) (real_const e0))).
  { apply (real_le_plus_compat t (real_const (q * q)) (real_const e0) (real_const e0) Hle_t).
    apply real_le_refl. }
  (* real_const(q·q) + real_const e0 == real_const (q·q + e0) *)
  assert (Hsum_eq : real_eq (real_plus (real_const (q * q)) (real_const e0))
                            (real_const (q * q + e0))).
  { apply real_eq_of_zero_diff. intro n.
    setoid_rewrite (real_plus_proj (real_const (q * q)) (real_const e0) n).
    cbn [projT1 real_const].
    ring. }
  (* t + eps0 ≤ real_const (q·q + e0) *)
  assert (Hle_sum2 : real_le (real_plus t (real_const e0)) (real_const (q * q + e0))).
  { apply (real_le_trans (real_plus t (real_const e0))
                         (real_plus (real_const (q * q)) (real_const e0))
                         (real_const (q * q + e0)) Hle_sum).
    apply RealSetoid.real_eq_le. exact Hsum_eq. }
  (* log(1+t) ≤ real_const (q·q + e0) *)
  assert (Hlog2 : real_le (real_log (real_plus real_one t) (b5a_one_plus_sq_pos (real_const q)))
                          (real_const (q * q + e0))).
  { apply (real_le_trans (real_log (real_plus real_one t) (b5a_one_plus_sq_pos (real_const q)))
                         (real_plus t (real_const e0))
                         (real_const (q * q + e0)) Hlog1 Hle_sum2). }
  (* real_const (q·q + e0) < real_const 1（Q 分离） *)
  assert (Hc_lt : real_lt (real_const (q * q + e0)) (real_const 1)).
  { apply real_const_lt. exact He1. }
  apply (real_le_lt_trans (real_log (real_plus real_one t) (b5a_one_plus_sq_pos (real_const q)))
                          (real_const (q * q + e0))
                          (real_const 1) Hlog2 Hc_lt).
Qed.

(* ============================================================ *)
(* 件 b5dE_S_lt_exp_half：0 < q < 1 ⟹ S(q) < exp(real_const(1/2)) *)
(*   链：log 上界件 ×(1/2)（real_lt_mult_compat L39389，正乘数）  *)
(*     ⟹ (1/2)·log(1+q²) < real_const(1/2)（(1/2)·1 == 1/2 桥）  *)
(*     ⟹ exp 严格单调（cauchy_real_exp_mono L35227）。            *)
(* ============================================================ *)
Lemma b5dE_S_lt_exp_half : forall (q : Q) (Hq0 : Qlt 0 q) (Hq1 : Qlt q 1),
  real_lt (b5a_S (real_const q)) (cauchy_real_exp (real_const (1 / 2))).
Proof.
  intros q Hq0 Hq1.
  assert (Hlogb : real_lt (real_log (real_plus real_one (real_mult (real_const q) (real_const q)))
                                    (b5a_one_plus_sq_pos (real_const q)))
                          (real_const 1)).
  { exact (b5dE_log_ub_one q Hq0 Hq1). }
  (* (1/2)·log(1+q²) < (1/2)·real_const 1 == real_const (1/2) *)
  assert (Hsmall : real_lt (real_mult (real_const (1 / 2))
                                      (real_log (real_plus real_one (real_mult (real_const q) (real_const q)))
                                                (b5a_one_plus_sq_pos (real_const q))))
                           (real_const (1 / 2))).
  { apply (real_lt_eq_lt (real_mult (real_const (1 / 2))
                                    (real_log (real_plus real_one (real_mult (real_const q) (real_const q)))
                                              (b5a_one_plus_sq_pos (real_const q))))
                         (real_mult (real_const (1 / 2)) (real_const 1))
                         (real_const (1 / 2))).
    - apply (real_lt_mult_compat (real_log (real_plus real_one (real_mult (real_const q) (real_const q)))
                                           (b5a_one_plus_sq_pos (real_const q)))
                                 (real_const 1) (real_const (1 / 2)) b5dE_half_pos_real Hlogb).
    - (* (1/2)·real_const 1 == real_const (1/2)（逐点 cbn + ring） *)
      apply real_eq_of_zero_diff. intro n.
      setoid_rewrite (real_mult_proj (real_const (1 / 2)) (real_const 1) n).
      cbn [projT1 real_const].
      ring. }
  (* exp 严格单调（b5a_S 定义性展开匹配） *)
  apply (cauchy_real_exp_mono (real_mult (real_const (1 / 2))
                                (real_log (real_plus real_one (real_mult (real_const q) (real_const q)))
                                          (b5a_one_plus_sq_pos (real_const q))))
                              (real_const (1 / 2)) Hsmall).
Qed.

(* ============================================================ *)
(* 件 b5dE_exp_half_le_two：exp(real_const (1/2)) ≤ real_const 2 *)
(*   链：real_exp_le_inv_one_minus L53549 @ x := real_const(1/2)  *)
(*     （0 < ½ < 1 证书）⟹ exp(½) ≤ inv(1−½)；1−½ == ½（逐点     *)
(*     field）⟹ real_inv_pos_ext L39276 换形；inv(½) == 2         *)
(*     （real_inv_unique L36016：½·inv(½) == 1 == ½·2）⟹ 证毕。   *)
(* ============================================================ *)
Lemma b5dE_exp_half_le_two : real_le (cauchy_real_exp (real_const (1 / 2))) (real_const 2).
Proof.
  (* real_const (1/2) < real_one（域证书，经 real_const 1 桥） *)
  assert (Hhalflt1 : real_lt (real_const (1 / 2)) real_one).
  { apply (real_lt_eq_lt (real_const (1 / 2)) (real_const 1) real_one).
    - apply real_const_lt. exact b5dE_half_lt_one_div.
    - exact b5dE_const1_eq_one. }
  (* exp(1/2) ≤ inv(1 − 1/2)（real_exp_le_inv_one_minus） *)
  pose proof (real_exp_le_inv_one_minus (real_const (1 / 2)) b5dE_half_pos_real Hhalflt1) as He1.
  set (W := real_lt_opp_plus (real_const (1 / 2)) real_one Hhalflt1).
  (* 1 − 1/2 == 1/2（逐点投影 + cbn + field） *)
  assert (Hb : real_eq (real_plus real_one (real_opp (real_const (1 / 2)))) (real_const (1 / 2))).
  { apply real_eq_of_zero_diff. intro n.
    setoid_rewrite (real_plus_proj real_one (real_opp (real_const (1 / 2))) n).
    setoid_rewrite (real_opp_proj (real_const (1 / 2)) n).
    cbn [projT1 real_const real_one].
    field. }
  (* inv(1 − 1/2) == inv(1/2)（real_inv_pos_ext） *)
  pose proof (real_inv_pos_ext (real_plus real_one (real_opp (real_const (1 / 2))))
                               (real_const (1 / 2)) W b5dE_half_pos_real Hb) as Hinvext.
  (* inv(1/2) == real_const 2（real_inv_unique：½·inv(½) == 1 == ½·2） *)
  assert (Htwo : real_eq (real_inv_pos (real_const (1 / 2)) b5dE_half_pos_real) (real_const 2)).
  { apply (real_inv_unique (real_const (1 / 2))
                           (real_inv_pos (real_const (1 / 2)) b5dE_half_pos_real)
                           (real_const 2)).
    - exact (real_inv_pos_correct (real_const (1 / 2)) b5dE_half_pos_real).
    - (* (1/2)·2 == 1（逐点投影 + cbn + field） *)
      apply real_eq_of_zero_diff. intro n.
      setoid_rewrite (real_mult_proj (real_const (1 / 2)) (real_const 2) n).
      cbn [projT1 real_const real_one].
      field. }
  (* 组装：exp(1/2) ≤ inv(1−1/2) ≤ inv(1/2) ≤ real_const 2 *)
  apply (real_le_trans (cauchy_real_exp (real_const (1 / 2)))
                       (real_inv_pos (real_plus real_one (real_opp (real_const (1 / 2)))) W)
                       (real_const 2)).
  - exact He1.
  - apply (real_le_trans (real_inv_pos (real_plus real_one (real_opp (real_const (1 / 2)))) W)
                         (real_inv_pos (real_const (1 / 2)) b5dE_half_pos_real)
                         (real_const 2)).
    + apply RealSetoid.real_eq_le. exact Hinvext.
    + apply RealSetoid.real_eq_le. exact Htwo.
Qed.

(* ============================================================ *)
(* §3 主件：S 有理点上界尾证书（M0 := 2 直写）                  *)
(*   主件 b5dE_S_ub_tail_q : forall (q : Q) (Hq0 : Qlt 0 q)      *)
(*      (Hq1 : Qlt q 1), sigT (fun N : nat => forall n : nat,    *)
(*      (N <= n)%nat ->                                          *)
(*      Qle (Qabs (projT1 (b5a_S (real_const q)) n)) 2)          *)
(*   组装：下界侧 b5a_S_ge_one L84807（0 < q ⟹ 尾 Qle 1 S_n）    *)
(*     + 上界侧 b5dE_S_lt_exp_half ∘ b5dE_exp_half_le_two ⟹       *)
(*       real_lt_le_trans L6205：S(q) < real_const 2（严格 gap）  *)
(*     ⟹ real_lt_pt_lt L37117 逐点化（(N ≤ n)%nat 形）⟹           *)
(*     Q 层内核 b5dE_q_abs_le_of_bounds 逐 n 应用（max-N 合并）。  *)
(*   服务 F1/网格：B′ 网格点 t_k := k·q/M ∈ (0,1) 有理 ⟹          *)
(*     q := t_k 实例自动满足 0<q<1；q := 0 端点由 item8 B2        *)
(*     b5d4_S0_ub_two（L226，尾 ≤ 2）覆盖，本件不做端点。         *)
(* ============================================================ *)
Lemma b5dE_S_ub_tail_q : forall (q : Q) (Hq0 : Qlt 0 q) (Hq1 : Qlt q 1),
  sigT (fun N : nat => forall n : nat, (N <= n)%nat ->
    Qle (Qabs (projT1 (b5a_S (real_const q)) n)) 2).
Proof.
  intros q Hq0 Hq1.
  (* 下界侧：0 < q ⟹ 尾 Qle 1 (S(q))（b5a_S_ge_one L84807） *)
  destruct (b5a_S_ge_one (real_const q) (b5dE_q_pos q Hq0)) as [N1 H1].
  (* 上界侧：S(q) < exp(1/2) ≤ 2 ⟹ S(q) < real_const 2（严格） *)
  assert (Hstrict : real_lt (b5a_S (real_const q)) (real_const 2)).
  { apply (real_lt_le_trans (b5a_S (real_const q))
                            (cauchy_real_exp (real_const (1 / 2)))
                            (real_const 2)).
    - exact (b5dE_S_lt_exp_half q Hq0 Hq1).
    - exact b5dE_exp_half_le_two. }
  (* 逐点化：(N2 ≤ n)%nat ⟹ S_n < (real_const 2)_n（real_lt_pt_lt） *)
  destruct (real_lt_pt_lt (b5a_S (real_const q)) (real_const 2) Hstrict) as [N2 H2].
  exists (Nat.max N1 N2).
  intros n Hn.
  apply (b5dE_q_abs_le_of_bounds (projT1 (b5a_S (real_const q)) n)).
  - apply (H1 n). apply NatLe_lift. lia.
  - assert (Hup : Qlt (projT1 (b5a_S (real_const q)) n) (projT1 (real_const 2) n)).
    { apply (H2 n). lia. }
    setoid_rewrite (real_const_proj 2 n) in Hup.
    exact Hup.
Qed.

(* ============================================================ *)
(* 块 item16（前缀 b5dF_——主件 b5dF_E_one_zero_of_rational）——来源：演变/.ablation/sc2_parallel/sc2_b5a_ode/sc2_b5a_item16.v。 *)
(* ============================================================ *)

(* ============================================================ *)
(* 段 A §1：Q glue —— xg := 1−g 的开区间 Q 证书                  *)
(*   复刻内 g = Qmin (1/2) a 满足 0 < g（Hg0）且 g ≤ 1/2          *)
(*   （Hg_le_half）⟹ 需 Qlt 0 (1−g)（g ≤ 1/2 侧）与               *)
(*   Qlt (1−g) 1（0 < g 侧）。根只有实层版 b5b_ep_xg_pos/lt_one   *)
(*   （L78030/L78041），Q 层版根内无同名 ⟹ 本文件自建（同构根证   *)
(*   法）。                                                     *)
(* ============================================================ *)

(* Q 层：g ≤ 1/2 ⟹ 0 < 1 − g（同构根 b5b_ep_xg_pos L78030 的 Q 层版；
   b5b_endpoint 体上下文 Hg_le_half : Qle g (1/2) 直接供给）。
   语义核实（规范 ⚠️）：1−g > 0 需 g < 1，非仅 0 < g——端点体给
   的是 g ≤ 1/2（g := Qmin (1/2) a），故本件取 Qle g (1/2) 为假设。 *)
Lemma b5dF_q_1mg_pos : forall (g : Q), Qle g (1 / 2) -> Qlt 0 (1 - g).
Proof.
  intros g Hg12.
  apply (Qlt_le_trans 0 (1 / 2) (1 - g)).
  - exact b5b_ep_half_pos.
  - apply (b5b_ep_half_le_1mg g). exact Hg12.
Qed.

(* Q 层：0 < g ⟹ 1 − g < 1（同构根 b5b_ep_xg_lt_one L78041 的 Q 层版；
   b5b_endpoint 体上下文 Hg0 : Qlt 0 g 直接供给） *)
Lemma b5dF_q_1mg_lt1 : forall (g : Q), Qlt 0 g -> Qlt (1 - g) 1.
Proof.
  intros g Hg0.
  apply (proj2 (Qlt_minus_iff (1 - g) 1)).
  assert (Heq : (1 - (1 - g)) == g) by ring.
  rewrite Heq. exact Hg0.
Qed.

(* ============================================================ *)
(* 段 A §2：xg := real_const (1−g) 域证书族（0<g≤1/2 束）        *)
(* ============================================================ *)

(* xg := real_const (1−g) 的 cw_unit 域证书（0<g ∧ g≤1/2 束 ⟹
   b5b_unit_const L73651 的 0≤g、g≤1 前提；主件内 Hxg 即用本件） *)
Lemma b5dF_xg_unit : forall (g : Q), Qlt 0 g -> Qle g (1 / 2) ->
  cw_unit (real_const (1 - g)).
Proof.
  intros g Hg0 Hg12.
  apply (b5b_unit_const g).
  - apply (Qlt_le_weak 0 g). exact Hg0.
  - apply (Qle_trans _ (1 / 2) _); [ exact Hg12 | exact b5b_ep_half_le_one ].
Qed.

(* xg 实层下开：real_lt 0 xg（同构根 b5b_ep_xg_pos L78030；束形合并。
   注：主件 b5dF_E_one_zero_of_rational 内不需要本件（有理点件取用
   Q 证书 b5dF_q_1mg_*，非实层开区间序）——保留为本族完整域证书，
   供后续 E_rational_zero 侧/实层组装取用。 *)
Lemma b5dF_xg_pos : forall (g : Q), Qlt 0 g -> Qle g (1 / 2) ->
  real_lt real_zero (real_const (1 - g)).
Proof.
  intros g Hg0 Hg12.
  exact (b5b_ep_xg_pos g Hg12).
Qed.

(* xg 实层上开：real_lt xg (real_const 1)（同构根 b5b_ep_xg_lt_one
   L78041；束形合并；取用情况同 b5dF_xg_pos 注） *)
Lemma b5dF_xg_lt1 : forall (g : Q), Qlt 0 g -> Qle g (1 / 2) ->
  real_lt (real_const (1 - g)) (real_const 1).
Proof.
  intros g Hg0 Hg12.
  exact (b5b_ep_xg_lt_one g Hg0).
Qed.

(* ============================================================ *)
(* 段 A §3：有理点件 → real_eq (real_E xg Hxg) real_zero 的 glue  *)
(* ============================================================ *)

(* 有理点件 → xg 零点 glue：把「∀q 有理 E(q)==0 件」实例化于
   q := 1−g（g 由 b5b_endpoint 式的 q_arch_inv 选取，有理），得到
   real_eq (real_E (real_const (1 - g)) Hunit) real_zero。
   输入 = 主件复刻上下文现成物：Hunit（cw_unit 证书，b5dF_xg_unit/
   b5b_unit_const 给）+ Q 开区间证书 Hg0q/Hg1q（b5dF_q_1mg_* 给）。
   与根 b5b_endpoint L78098 的 Section 假设取用点同构：彼处
   b5a_E_zero_on_unit xg Hxg Hxg0 Hxg1（∀x 实例化），此处
   Hrat (1−g) Hg0q Hg1q Hunit（有理点件实例化）。 *)
Lemma b5dF_rational_at_xg : forall (g : Q) (Hunit : cw_unit (real_const (1 - g))),
  Qlt 0 (1 - g) -> Qlt (1 - g) 1 ->
  (forall (q : Q), Qlt 0 q -> Qlt q 1 ->
    forall (Hq : cw_unit (real_const q)),
    real_eq (real_E (real_const q) Hq) real_zero) ->
  real_eq (real_E (real_const (1 - g)) Hunit) real_zero.
Proof.
  intros g Hunit Hg0q Hg1q Hrat.
  exact (Hrat (1 - g) Hg0q Hg1q Hunit).
Qed.

(* ============================================================ *)
(* 段 A §4：前提式主件 b5dF_E_one_zero_of_rational               *)
(* ============================================================ *)

(* ============================================================ *)
(* 前提式主件：E(1)==0（复刻根 b5b_endpoint L78062–78177）        *)
(* 与根差异（仅 3 处）：                                        *)
(*   (a) Section 假设 b5a_E_zero_on_unit → forall 前提 Hrat（「有  *)
(*       理点 E(q)==0 件」，δ-D2 产出，未闭；本件 = 前提式 Lemma， *)
(*       真 Qed，禁公理面/承认件）；                            *)
(*   (b) L78092 Hxg 证书 → b5dF_xg_unit（0<g ∧ g≤1/2 束）；       *)
(*   (c) L78093–78099 取用点 → 删实层 Hxg0/Hxg1（有理件只取用 Q   *)
(*       证书），Hz0 := b5dF_rational_at_xg g Hxg（q_1mg 证书 +   *)
(*       Hrat）。                                                *)
(* 体其余（① |E1−Eg| ② |Eg−0| 三角不等式）逐字照抄。               *)
(* ============================================================ *)
Lemma b5dF_E_one_zero_of_rational :
  (forall (q : Q), Qlt 0 q -> Qlt q 1 ->
    forall (Hq : cw_unit (real_const q)),
    real_eq (real_E (real_const q) Hq) real_zero) ->
  real_eq real_E_one real_zero.
Proof.
  intros Hrat.
  intros epsQ HepsQT.
  assert (HepsQ : Qlt 0 epsQ) by (apply QltT_to_Qlt; exact HepsQT).
  assert (HhalfQ : Qlt 0 (epsQ / 2)) by (apply QltT_to_Qlt; apply q_half_pos; exact HepsQT).
  assert (HhalfT : QltT 0 (epsQ / 2)) by (apply Qlt_to_QltT; exact HhalfQ).
  (* b5b_E_close_q (epsQ/2)：∃N0 g0>0：n≥N0、0<g≤g0 ⟹ |E_n(1−g)−E_n(1)| < epsQ/2 *)
  destruct (b5b_E_close_q (epsQ / 2) HhalfQ) as [N0 [g0 [Hg0pos Hclose]]].
  (* q_arch_inv g0 取 K：a := 1/(K+2) < g0；g := Qmin (1/2) a *)
  destruct (q_arch_inv g0 (QltT_to_Qlt 0 g0 Hg0pos)) as [K HK].
  set (a := 1 / (Z.of_nat (K + 2) # 1)).
  set (g := Qmin (1 / 2) a).
  assert (Ha0 : Qlt 0 a).
  { unfold a. exact (q_arch_inv_pos K). }
  assert (Hg0 : Qlt 0 g).
  { unfold g. apply (b5b_ecl_min_pos (1 / 2) a); [exact b5b_ep_half_pos | exact Ha0]. }
  assert (Hg0le : Qle 0 g) by (apply (Qlt_le_weak 0 g); exact Hg0).
  assert (Hg_le_half : Qle g (1 / 2)).
  { unfold g. exact (Q.le_min_l (1 / 2) a). }
  assert (Hg_le_a : Qle g a).
  { unfold g. exact (Q.le_min_r (1 / 2) a). }
  assert (Ha_g0 : Qle a g0).
  { apply (Qlt_le_weak a g0). unfold a. exact HK. }
  assert (Hg_g0 : Qle g g0).
  { apply (Qle_trans _ a _); [exact Hg_le_a | exact Ha_g0]. }
  assert (Hg1 : Qle g 1).
  { apply (Qle_trans _ (1 / 2) _); [exact Hg_le_half | exact b5b_ep_half_le_one]. }
  (* xg := real_const (1−g)；域证书 Hxg（本文件 b5dF_xg_unit，
     g 上下文给 0<g（Hg0）与 g≤1/2（Hg_le_half）） *)
  set (xg := real_const (1 - g)).
  assert (Hxg : cw_unit xg).
  { unfold xg. apply (b5dF_xg_unit g Hg0 Hg_le_half). }
  (* 假设取用点（复刻根 L78098）：Hz0 := real_eq (real_E xg Hxg) real_zero；
     根彼处 = b5a_E_zero_on_unit xg Hxg Hxg0 Hxg1（∀x 全称实例化，
     需实层开区间序 Hxg0/Hxg1）；本处 = 有理点件 @ q := 1−g 实例化
     （b5dF_rational_at_xg），Q 开区间证书 = b5dF_q_1mg_pos/lt1，
     Hxg 即 Hunit——实层序不再需要 ⟹ 删 Hxg0/Hxg1 assert *)
  assert (Hz0 : real_eq (real_E xg Hxg) real_zero).
  { unfold xg.
    exact (b5dF_rational_at_xg g Hxg
             (b5dF_q_1mg_pos g Hg_le_half)
             (b5dF_q_1mg_lt1 g Hg0) Hrat). }
  destruct (Hz0 (epsQ / 2) HhalfT) as [Nz HNz].
  (* 模：N := max(N0, Nz) *)
  exists (Nat.max N0 Nz).
  intros n Hn.
  apply NatLe_drop in Hn.
  assert (HnN0 : (N0 <= n)%nat) by lia.
  assert (HnNz : (Nz <= n)%nat) by lia.
  (* ① |E1_n − Eg_n| < epsQ/2：b5b_En_proj 桥 + b5b_E_close_q *)
  assert (Hq1eq : (projT1 real_E_one n - projT1 (real_E xg Hxg) n) ==
                  (b5b_En n 1 - b5b_En n (1 - g))).
  { unfold real_E_one.
    rewrite (b5b_En_proj (real_const 1) atan1_pt_bound n).
    rewrite (b5b_En_proj xg Hxg n).
    unfold xg.
    (* projT1 (real_const c) k 与 c 定义性相等（real_const_proj 由
       reflexivity 证明），此处不可在 b5b_En 参数内 setoid 重写
       （b5b_En 无 Qeq Proper 实例），靠 kernel 转换 reflexivity 收。 *)
    reflexivity. }
  assert (Hq1abs : Qabs (projT1 real_E_one n - projT1 (real_E xg Hxg) n) ==
                   Qabs (b5b_En n (1 - g) - b5b_En n 1)).
  { apply (Qeq_trans _ (Qabs (b5b_En n 1 - b5b_En n (1 - g))) _).
    - apply (Qabs_wd (projT1 real_E_one n - projT1 (real_E xg Hxg) n)
                     (b5b_En n 1 - b5b_En n (1 - g))).
      exact Hq1eq.
    - apply (q_abs_minus_sym (b5b_En n 1) (b5b_En n (1 - g))). }
  assert (Hterm1T : QltT (Qabs (projT1 real_E_one n - projT1 (real_E xg Hxg) n))
                         (epsQ / 2)).
  { apply (qltT_eq_compat_l (Qabs (b5b_En n (1 - g) - b5b_En n 1))
                            (Qabs (projT1 real_E_one n - projT1 (real_E xg Hxg) n))
                            (epsQ / 2)).
    - apply Qeq_sym. exact Hq1abs.
    - apply Qlt_to_QltT.
      exact (Hclose n g (NatLe_lift _ _ HnN0) Hg0 Hg_g0). }
  assert (Hterm1 : Qlt (Qabs (projT1 real_E_one n - projT1 (real_E xg Hxg) n))
                       (epsQ / 2))
    by (apply QltT_to_Qlt; exact Hterm1T).
  (* ② |Eg_n − 0_n| < epsQ/2：Hz0（real_eq (E xg) 0）逐点 *)
  assert (Hterm2T : QltT (Qabs (projT1 (real_E xg Hxg) n - projT1 real_zero n))
                         (epsQ / 2)).
  { exact (HNz n (NatLe_lift _ _ HnNz)). }
  assert (Hterm2 : Qlt (Qabs (projT1 (real_E xg Hxg) n - projT1 real_zero n))
                       (epsQ / 2))
    by (apply QltT_to_Qlt; exact Hterm2T).
  (* 三角：|E1_n − 0_n| ≤ |E1_n − Eg_n| + |Eg_n − 0_n| *)
  assert (Htri : Qle (Qabs (projT1 real_E_one n - projT1 real_zero n))
                     (Qplus (Qabs (projT1 real_E_one n - projT1 (real_E xg Hxg) n))
                            (Qabs (projT1 (real_E xg Hxg) n - projT1 real_zero n)))).
  { apply (Qle_trans _
             (Qabs ((projT1 real_E_one n - projT1 (real_E xg Hxg) n) +
                    (projT1 (real_E xg Hxg) n - projT1 real_zero n))) _).
    - apply qeq_le.
      apply (Qabs_wd (projT1 real_E_one n - projT1 real_zero n)
                     ((projT1 real_E_one n - projT1 (real_E xg Hxg) n) +
                      (projT1 (real_E xg Hxg) n - projT1 real_zero n))).
      ring.
    - apply Qabs_triangle. }
  (* 两项和 < epsQ/2 + epsQ/2 == epsQ *)
  assert (Hsum : Qlt (Qplus (Qabs (projT1 real_E_one n - projT1 (real_E xg Hxg) n))
                            (Qabs (projT1 (real_E xg Hxg) n - projT1 real_zero n)))
                     (Qplus (epsQ / 2) (epsQ / 2))).
  { apply (Qplus_lt_compat (Qabs (projT1 real_E_one n - projT1 (real_E xg Hxg) n))
                           (epsQ / 2)
                           (Qabs (projT1 (real_E xg Hxg) n - projT1 real_zero n))
                           (epsQ / 2)).
    - exact Hterm1.
    - exact Hterm2. }
  apply Qlt_to_QltT.
  apply (Qle_lt_trans (Qabs (projT1 real_E_one n - projT1 real_zero n))
                      (Qplus (Qabs (projT1 real_E_one n - projT1 (real_E xg Hxg) n))
                             (Qabs (projT1 (real_E xg Hxg) n - projT1 real_zero n)))
                      epsQ).
  - exact Htri.
  - apply (Qlt_le_trans (Qplus (Qabs (projT1 real_E_one n - projT1 (real_E xg Hxg) n))
                               (Qabs (projT1 (real_E xg Hxg) n - projT1 real_zero n)))
                        (Qplus (epsQ / 2) (epsQ / 2)) epsQ).
    + exact Hsum.
    + apply qeq_le. exact (b5b_ep_half_sum epsQ).
Qed.

(* ============================================================ *)
(* 段 B：E_rational_zero 网格望远镜依赖清单（零代码，注释登记）  *)
(* ============================================================ *)

(* ============================================================ *)
(* 段 B（零代码，注释登记）：E_rational_zero（δ-D2 主件）网格     *)
(*   望远镜依赖清单——供后续规范引用。                          *)
(* 目标语句契约（= 本文件 §A4 前提；δ-D 设计 §2.1 逐字）：        *)
(*   b5?_E_rational_zero : forall (q : Q), Qlt 0 q -> Qlt q 1 ->   *)
(*     forall (Hq : cw_unit (real_const q)),                       *)
(*     real_eq (real_E (real_const q) Hq) real_zero                *)
(* 证明链（依设计 §2(iii)）：                                       *)
(*   E(q)==0 ⟸ b5p2_E_zero_of_J_zero（根 L86865）@ (real_const q)  *)
(*     Hq + real_E/b5a_E 同体桥（L72948/L73975，自建 ~8–12 行，    *)
(*     仿 item4r2 B1 先例）                                       *)
(*   ⟸ J(q)==0 ⟸ J(0)==0（b5c_J_zero_at_zero L74734 @              *)
(*     b5c_unit_zero L74360（Definition，real_const 0 域证书），    *)
(*     已闭）+ 网格望远镜 t_k := Qmult q (k/M)，M≥1，k=0..M：      *)
(*     每步 |J(t_{k+1})−J(t_k)| ≤ b_k（b_k := eps0Q·(q/M)+eps0'Q   *)
(*     闭式），Σ_k b_k == eps0Q·q + M·eps0'Q == epsQ 预算证毕。    *)
(* ------------------------------------------------------------ *)
(* ① 网格 nsum/三角骨架（根 b4 族，实测行号）：                   *)
(*    b4_nsum_const L72499 / b4_nsum_le L72527 / b4_nsum_tri       *)
(*    L72541 / b4_nsum_telescope L72615（L72615 起区 = 望远镜     *)
(*    nsum 骨架）；链式模板 b4_chain_lipschitz L73016 /            *)
(*    b4_arch_step L72844 / b4_chain_bound_eps0 L76930 /           *)
(*    b4_deriv_zero_eq_endpoints L77111 /                          *)
(*    b4_const_on_interval_pair L77173。                          *)
(* ② 桥接引理（item4r2 B1–B4 同款；item4r2 .vo 基于 212 根不可        *)
(*    Require——等价件根内自建，禁 Require item4r2）：             *)
(*    b5c_const_unit L74348（0≤q≤1 ⟹ cw_unit (real_const q)，     *)
(*    网格点域证书）/ b5p2_E_zero_of_J_zero L86865 /              *)
(*    b5p2_E_eq_J_S L86834 / b5c_J_zero_at_zero L74734 /           *)
(*    b5c_unit_zero L74360 / real_E↔b5a_E 同体桥（自建）。         *)
(* ③ 每步模量源 = C5 expl 尾-M 变体：item11（上游）                *)
(*    b5d7_J_deriv_zero_exp（δ-C C5，参数束 cA/M/Ms/Mc + 全 n 界   *)
(*    前提 HMall）；尾-M 改法 = HMall → (NM : nat) + ∀n≥NM，      *)
(*    Nmax 并入 NM（item11 L334–336 区改 3–5 行；δC 审查 §1.4/    *)
(*    1.5 同判；C6 = item12 b5d8_J_deriv_zero_tail_exp 可作改法   *)
(*    参照）。⚠️ 载体实测（item12 记录）：C5/C6 界前提的载体  *)
(*    = x̂ := b5m_tailtrunc x N0 而非 x ⟹ 逐点消解须按      *)
(*    trunc 载体设计。                                            *)
(* ④ 实例证书族（上游全 δ 系可 Require）：                       *)
(*    item6 M4a/M4b：b5d2_sinA_abs_le1 / b5d2_cosA_abs_le1        *)
(*    （Ms := Mc := 1 全 n 证书）；item8 B1：b5d4_S0_lb_half       *)
(*    （cA := 1/2）+ 件 A：b5d4_S_const0_eq_one（S(0)==1）；       *)
(*    item5：b5d1_b3rr_atan_deriv_lin（L0 透明底，Defined）。     *)
(* ⑤ S 上界（新数学件，δ-D 设计 §2.5 路线 (b)）：逐点全 n 界不可  *)
(*    证（log_seq/approx_root 逐点墙，δB-3 降级实证 item7 §2）⟹   *)
(*    尾形 M 前提 + 尾证书 b5?_S_ub_tail_q（M_S0 := 2 或 4）：     *)
(*    S(0)==1 → S-diff@x:=0 透明件 → eps:=1/2、eps':=1/4 松弛 →   *)
(*    ≤ 2/4 证毕；τ0 := cA·Qinv(8·(M_S0·r+1)) 闭式照常。          *)
(* ⑥ 透明 δ 链硬前置（δ-D 设计 §2.3/§2.4）：保守态 C1–C6        *)
(*    输出 δ 含不透明叶（δE/δS1/δS2 = 根 Qed sigT 见证，递归     *)
(*    vdh→atan_deriv→b3rr，仅知 >0 无下界 ⟹ 有理步 |h| < δ 无从   *)
(*    构造）⟹ 逐层 Qed→Defined 透明化 + 逐叶下界证书（自底向上    *)
(*    b3rr→atan_deriv→vdh→sin/cos-atan→exp/g→E→S→J，~2,500 行；   *)
(*    item14（b5dD_，C8 透明基座）与 item15（b5dE_，S 上界尾证书  *)
(*    = ⑤）为 δ-D 并行批的前置文件）。                            *)
(* ⑦ 预算/arch（Q 层现成）：q_arch_inv L4733 / q_arch_inv_pos     *)
(*    L4790——M := K+2 := q_arch_inv (δ0/q)，照 b5b_endpoint       *)
(*    L78071 模式；eps0Q := epsQ/(2q)（q>0 可除）、                *)
(*    eps0'Q := epsQ/(2M)；δ0 := min(各显式分量) 全为 q/eps0Q 的   *)
(*    有理闭式。                                                  *)
(* 实例化：b5?_E_rational_zero 供入本文件                        *)
(*   b5dF_E_one_zero_of_rational ⟹ real_eq real_E_one real_zero    *)
(*   ⟹ b5b_hsc_main（L72994）⟹ a3_closure_f1（L67997）⟹           *)
(*   real_eq real_pi_geom cauchy_real_pi_leibniz（F1 主定理）。    *)
(* ============================================================ *)

(* ============================================================ *)
(* 块 item18（前缀 b5dH_——主件 b5dH_E_zero_of_J_zero）——来源：演变/.ablation/sc2_parallel/sc2_b5a_ode/sc2_b5a_item18.v。 *)
(* ============================================================ *)

(* ============================================================ *)
(* 件清单（随实现进度更新；主件最后攻坚）：                     *)
(*   段 A 桥与归约（非墙，先行）：                              *)
(*     b5dH_E_eq_b5aE   : real_E ↔ b5a_E 同体桥（reflexivity）  *)
(*     b5dH_J_zero0     : J(real_const 0)==0 @ b5c_unit_zero    *)
(*     b5dH_E_zero_of_J : ∀q Hq, J(q)==0 ⟹ E(q)==0（主件归约核） *)
(*   段 B 网格点域证书族（t_k := q·(k/M) ∈ (0,1) 有理）：        *)
(*     cw_unit/开区间/S 尾界实例化（item15 @ t_k、item8 @ 0）    *)
(*   段 C 望远镜与预算（b4_nsum 骨架 + b_k 闭式）                *)
(*   段 D 主件 b5dH_E_rational_zero（前置墙件就绪后组装）          *)
(* ============================================================ *)

(* ============================================================ *)
(* 段 A §1：real_E ↔ b5a_E 同体桥（非墙件，先行闭合）            *)
(*   根 L72948 real_E 与 L73975 b5a_E 定义体逐字相同             *)
(*   （real_plus (cauchy_real_sin (cauchy_real_arctan x Hx))     *)
(*     (real_opp (real_mult x (cauchy_real_cos (cauchy_real_arctan *)
(*     x Hx))))）⟹ 对任意同一 x/Hx 的 real_eq 由 unfold + refl 收。*)
(* ============================================================ *)

(* real_E ↔ b5a_E 同体桥：real_E x Hx == b5a_E x Hx（∀x Hx）    *)
Lemma b5dH_E_eq_b5aE : forall (x : Real) (Hx : cw_unit x),
  real_eq (real_E x Hx) (b5a_E x Hx).
Proof.
  intros x Hx.
  unfold real_E, b5a_E.
  apply real_eq_refl.
Qed.

(* ============================================================ *)
(* 段 A §2：J(real_const 0) == 0（b5c_J_zero_at_zero L74734 @   *)
(*   b5c_unit_zero L74360，上游已证件直接应用）                    *)
(* ============================================================ *)

(* J(0) == 0：b5c_J_zero_at_zero 的 H0 := b5c_unit_zero（类型   *)
(*   forall n, QleT' (Qabs (projT1 (real_const 0) n)) 1 逐字吻合）*)
Lemma b5dH_J_zero0 : real_eq (b5c_J (real_const 0) b5c_unit_zero) real_zero.
Proof.
  exact (b5c_J_zero_at_zero b5c_unit_zero).
Qed.

(* ============================================================ *)
(* 段 A §3：E(q)==0 ⟸ J(q)==0 归约核（b5p2_E_zero_of_J_zero     *)
(*   L86865 @ (real_const q) Hq + §1 桥）——主件的最终两步，  *)
(*   不依赖墙件，先行闭合。                                     *)
(* ============================================================ *)

(* E(x) == 0 ⟸ J(x) == 0（任意 x，含主件实例 x := real_const q）*)
Lemma b5dH_E_zero_of_J_zero : forall (x : Real) (Hx : cw_unit x),
  real_eq (b5c_J x Hx) real_zero -> real_eq (real_E x Hx) real_zero.
Proof.
  intros x Hx HJ0.
  apply (real_eq_trans _ (b5a_E x Hx) _).
  - exact (b5dH_E_eq_b5aE x Hx).
  - exact (b5p2_E_zero_of_J_zero x Hx HJ0).
Qed.

(* ============================================================ *)
(* 段 A §4：网格点域证书（t_k := q·(k/M) ∈ [0,1] 有理 → cw_unit；*)
(*   0≤x≤1 的 cw_unit (real_const x) = 根 b5c_const_unit L74348  *)
(*   直接应用，无需新件；此处补 0<x<1 ⟹ Qle 0 x 与 Qle x 1 的 Q 层  *)
(*   辅助小件（同构 b5dF_q_1mg_* 模式，Q 层纯代数））            *)
(* ============================================================ *)

(* 0 < x < 1 ⟹ 0 ≤ x（Qlt_le_weak 直收） *)
Lemma b5dH_q_pos_le : forall (x : Q), Qlt 0 x -> Qle 0 x.
Proof.
  intros x Hx. apply (Qlt_le_weak 0 x). exact Hx.
Qed.

(* 0 < x < 1 ⟹ x ≤ 1（Qlt_le_weak 直收） *)
Lemma b5dH_q_lt1_le : forall (x : Q), Qlt x 1 -> Qle x 1.
Proof.
  intros x Hx. apply (Qlt_le_weak x 1). exact Hx.
Qed.

(* ============================================================ *)
(* 段 A §5：real_const 参数 glue（望远镜参数桥，望远镜组装用）   *)
(* ============================================================ *)

(* Qeq ⟹ real_eq (real_const a) (real_const b)（逐点 ==，N := 0） *)
Lemma b5dH_real_const_qeq : forall (a b : Q), a == b ->
  real_eq (real_const a) (real_const b).
Proof.
  intros a b Hab.
  apply real_eq_of_zero_diff.
  intro n.
  cbn [projT1 real_const].
  rewrite Hab.
  ring.
Qed.

(* real_plus (real_const a) (real_const b) == real_const (a + b)（逐点） *)
Lemma b5dH_plus_const_eq : forall (a b : Q),
  real_eq (real_plus (real_const a) (real_const b)) (real_const (a + b)).
Proof.
  intros a b.
  apply real_eq_of_zero_diff.
  intro n.
  rewrite (real_plus_proj (real_const a) (real_const b) n).
  cbn [projT1 real_const].
  ring.
Qed.

(* ============================================================ *)
(* 段 D：主件（契约语句见文件头注释；证体待墙件裁决后落地）     *)
(*   主件语句（与 item16 §A4 前提逐字，不得改动）：              *)
(*   forall (q : Q), Qlt 0 q -> Qlt q 1 ->                       *)
(*     forall (Hq : cw_unit (real_const q)),                     *)
(*     real_eq (real_E (real_const q) Hq) real_zero              *)
(*   组装骨架（段 A 已闭，前置件就绪后按序组装）：                 *)
(*   (1) b5dH_E_zero_of_J_zero (real_const q) Hq                 *)
(*       (b5dH_J_q_zero q ...)  其中 J(q)==0 由网格望远镜给出；  *)
(*   (2) J(q)==J(0)：t_k 网格逐点模量实例（墙件：透明 J 模量）    *)
(*       每步 real_le |J(t_{k+1})−J(t_k)| (eps0Q·(q/M)+eps0'Q)， *)
(*       b4_nsum_telescope/le/tri 累加（L72615/72527/72541）。    *)
(*   当前正文：7 Lemma = 7 Qed 全真闭合（段 A 桥与归约），主件待  *)
(*   墙件裁决后落地（设计记录 §3）。                             *)
(* ============================================================ *)

(* ============================================================ *)
(* end sc2_b5a_item18.v · δ-D2 E_rational_zero · M1 骨架          *)
(* ============================================================ *)

(* ============================================================ *)
(* 块 item22（前缀 b5dL_——主件 b5dL_E_rational_zero_premise）——来源：演变/.ablation/sc2_parallel/sc2_b5a_ode/sc2_b5a_item22.v。 *)
(* ============================================================ *)

(* ============================================================ *)
(* 件清单（随实现进度更新；实现顺序 = 段 A→B→C→D→E）：          *)
(*   段 A Definitions：                                         *)
(*     b5dL_tkq   : t_k := q·(Z.of_nat k # 1)/(Z.of_nat M # 1)  *)
(*     b5dL_qdiv  : 步长 q/M                                     *)
(*     b5dL_Qnsum : Q 层 Σ_{k<N}（同构 b4_nsum 左折）            *)
(*   段 A 网格点域证书族（Q 层 13 件 + cw_unit 证书）：           *)
(*     0 ≤ t_k / t_k ≤ q(k≤M) / t_k < 1(q<1) / t_k > 0(k≥1) /   *)
(*     t_0 == 0 / t_M == q / t_{S k} == t_k + q/M /              *)
(*     b5dL_tkC（cw_unit (real_const t_k)，b5c_const_unit 直接应用） *)
(*   段 A 附加 Real glue（δ 链实例化 Hstep 桥 C5 输出必需）：     *)
(*     b5dL_abs_const / b5dL_mult_const / b5dL_J_tk_succ_bridge  *)
(*   段 B 望远镜前提式（核心骨架，δ 无关）：                     *)
(*     b5dL_Qnsum_const / b5dL_nsum_real /                       *)
(*     b5dL_telescope_premise（纯 f/g 形，结论含三角松量 e）      *)
(*   段 C J 网格望远镜（证书参数化；自建归纳 Aux(n)）：           *)
(*     b5dL_J_grid_premise（∀Hk Hk1 每步前提 + 端点证书量化）     *)
(*   段 D eps 预算 Q 层算术：                                    *)
(*     b5dL_bk / b5dL_epsQ1 / b5dL_epsQ1_pos /                   *)
(*     b5dL_budget_closure（Σbk + Σe == epsQ）                   *)
(*   段 E 前提式（δ 链就绪后只剩实例化）：                    *)
(*     b5dL_J_zero_on_grid_premise（|J(q)−J(0)| ≤ real_const     *)
(*       epsQ，经 b5dH_J_zero0 桥 J(0) 侧）                      *)
(*     b5dL_E_rational_zero_premise（主件形前提式：Hmod =         *)
(*       ∀epsQ sigT M 每步前提 → real_eq (real_E (real_const q)   *)
(*       Hq) real_zero；证法 = b5dH_E_zero_of_J_zero +            *)
(*       b4_abs_le_forall_eps_eq + real_eps_witness 取 Q 下界）   *)
(*   段 F（注释）：证明链说明 / 待补部分（等 δ 链）             *)
(* ============================================================ *)

(* ============================================================ *)
(* 段 A §1：Definitions（t_k 网格 / 步长 / Q 层和）               *)
(*   设计（设计记录 §3.1）：t_kQ := q·(Z.of_nat k # 1)/(M#1)     *)
(* ============================================================ *)

(* t_k := q·(k/M)（k 的 #1 提升；M > 0 时才是有意义网格） *)
Definition b5dL_tkq (q : Q) (M : nat) (k : nat) : Q :=
  (q * (Z.of_nat k # 1)) / (Z.of_nat M # 1).

(* 步长 η := q/M（步进恒等 t_{k+1} == t_k + η 的 Q 层项） *)
Definition b5dL_qdiv (q : Q) (M : nat) : Q :=
  q / (Z.of_nat M # 1).

(* Q 层 Σ_{k<N}（同构根 b4_nsum 左折；b4_nsum 是 Real 层） *)
Fixpoint b5dL_Qnsum (b : nat -> Q) (N : nat) : Q :=
  match N with
  | 0%nat => 0
  | Datatypes.S m => b5dL_Qnsum b m + b m
  end.

(* ============================================================ *)
(* 段 A §2：nat 提升 Q 小件（模式 = 检验定稿：                   *)
(*   unfold Qlt/Qeq; simpl; lia）                                *)
(* ============================================================ *)

(* (S m)#1 > 0（无前提；0 < M 的 destruct 落点件） *)
Lemma b5dL_lift_pos2 : forall (m : nat), Qlt 0 (Z.of_nat (Datatypes.S m) # 1).
Proof.
  intro m.
  unfold Qlt. simpl. lia.
Qed.

(* 1 ≤ n ⟹ n#1 > 0（tkq_pos 用） *)
Lemma b5dL_lift_pos : forall (n : nat), (1 <= n)%nat -> Qlt 0 (Z.of_nat n # 1).
Proof.
  intros n Hn.
  destruct n as [| m]; [lia | exact (b5dL_lift_pos2 m)].
Qed.

(* (S k)#1 == k#1 + 1（Qnsum_const 归纳步 / tkq_succ 分子） *)
Lemma b5dL_lift_succ_q : forall (k : nat),
  Qeq (Z.of_nat (Datatypes.S k) # 1) ((Z.of_nat k # 1) + 1).
Proof.
  intro k.
  unfold Qeq. simpl. lia.
Qed.

(* 0 < M ⟹ M#1 ≠ 0（field 除零条件件） *)
Lemma b5dL_lift_nz : forall (M : nat), (0 < M)%nat -> ~ (Z.of_nat M # 1 == 0).
Proof.
  intros M HM Hz.
  unfold Qeq in Hz. simpl in Hz.
  lia.
Qed.

(* (k#1) ≥ 0 全 k（tkq 非负的分子因子） *)
Lemma b5dL_nat_nonneg : forall (k : nat), Qle 0 (Z.of_nat k # 1).
Proof.
  intro k.
  destruct k as [| m].
  - cbn. apply Qle_refl.
  - apply (Qlt_le_weak 0 (Z.of_nat (Datatypes.S m) # 1)).
    exact (b5dL_lift_pos2 m).
Qed.

(* k ≤ M ⟹ (k#1) ≤ (M#1)（Qle 展开到 Z 层，lia 归一化） *)
Lemma b5dL_nat_le_qle : forall (k M : nat), (k <= M)%nat ->
  Qle (Z.of_nat k # 1) (Z.of_nat M # 1).
Proof.
  intros k M Hkm.
  unfold Qle. simpl. lia.
Qed.

(* Qlt 0 x ⟹ x ≠ 0（field 条件件；Qeq-rewrite 于 Qlt 可用） *)
Lemma b5dL_q_lt0_nz : forall (x : Q), Qlt 0 x -> ~ x == 0.
Proof.
  intros x Hx Heq.
  rewrite Heq in Hx.
  apply (Qlt_irrefl 0). exact Hx.
Qed.

(* ============================================================ *)
(* 段 A §3：网格点域证书族（t_k ∈ [0,1]/开区间/步进恒等）         *)
(* ============================================================ *)

(* 0 ≤ q ⟹ 0 ≤ t_k（q·k#1 ≥ 0 且 M#1 > 0 ⟹ 商 ≥ 0） *)
Lemma b5dL_tkq_nonneg : forall (q : Q) (M k : nat),
  Qle 0 q -> (0 < M)%nat -> Qle 0 (b5dL_tkq q M k).
Proof.
  intros q M k Hq0 HM.
  unfold b5dL_tkq.
  unfold Qdiv.
  apply Qmult_le_0_compat.
  - apply Qmult_le_0_compat.
    + exact Hq0.
    + exact (b5dL_nat_nonneg k).
  - apply Qinv_le_0_compat.
    apply (Qlt_le_weak 0 (Z.of_nat M # 1)).
    destruct M as [| m]; [exfalso; lia | exact (b5dL_lift_pos2 m)].
Qed.

(* k ≤ M ⟹ t_k ≤ q（Qle_shift_div_r + 交换桥） *)
Lemma b5dL_tkq_le_q : forall (q : Q) (M k : nat),
  Qle 0 q -> (0 < M)%nat -> (k <= M)%nat ->
  Qle (b5dL_tkq q M k) q.
Proof.
  intros q M k Hq0 HM Hk.
  unfold b5dL_tkq.
  apply (Qle_shift_div_r (q * (Z.of_nat k # 1)) (Z.of_nat M # 1) q).
  - destruct M as [| m]; [exfalso; lia | exact (b5dL_lift_pos2 m)].
  - (* q·(k#1) ≤ q·(M#1)：经 k#1·q ≤ M#1·q + Qmult_comm 桥 *)
    apply (Qle_trans _ (Qmult (Z.of_nat k # 1) q) _).
    + apply qeq_le. exact (Qmult_comm q (Z.of_nat k # 1)).
    + apply (Qle_trans _ (Qmult (Z.of_nat M # 1) q) _).
      * exact (Qmult_le_compat_r (Z.of_nat k # 1) (Z.of_nat M # 1) q
                 (b5dL_nat_le_qle k M Hk) Hq0).
      * apply qeq_le. exact (Qmult_comm (Z.of_nat M # 1) q).
Qed.

(* k ≤ M ⟹ t_k ≤ 1（t_k ≤ q ≤ 1；b5c_const_unit 前提） *)
Lemma b5dL_tkq_le1 : forall (q : Q) (M k : nat),
  Qle 0 q -> Qle q 1 -> (0 < M)%nat -> (k <= M)%nat ->
  Qle (b5dL_tkq q M k) 1.
Proof.
  intros q M k Hq0 Hq1 HM Hk.
  apply (Qle_trans (b5dL_tkq q M k) q 1).
  - exact (b5dL_tkq_le_q q M k Hq0 HM Hk).
  - exact Hq1.
Qed.

(* k ≤ M ∧ q<1 ⟹ t_k < 1（开区间上证书；S 尾界实例化等用） *)
Lemma b5dL_tkq_lt1 : forall (q : Q) (M k : nat),
  Qle 0 q -> (0 < M)%nat -> (k <= M)%nat -> Qlt q 1 -> Qlt (b5dL_tkq q M k) 1.
Proof.
  intros q M k Hq0 HM Hk Hq1.
  apply (Qle_lt_trans (b5dL_tkq q M k) q 1).
  - exact (b5dL_tkq_le_q q M k Hq0 HM Hk).
  - exact Hq1.
Qed.

(* 0<q ∧ k≥1 ⟹ 0 < t_k（右端点证书；J 模量 δ 链实例化域） *)
Lemma b5dL_tkq_pos : forall (q : Q) (M k : nat),
  Qlt 0 q -> (0 < M)%nat -> (0 < k)%nat -> Qlt 0 (b5dL_tkq q M k).
Proof.
  intros q M k Hq0 HM Hk0.
  unfold b5dL_tkq.
  unfold Qdiv.
  apply (Qmult_lt_0_compat (q * (Z.of_nat k # 1)) (Qinv (Z.of_nat M # 1))).
  - apply (Qmult_lt_0_compat q (Z.of_nat k # 1)).
    + exact Hq0.
    + exact (b5dL_lift_pos k Hk0).
  - apply Qinv_lt_0_compat.
    destruct M as [| m]; [exfalso; lia | exact (b5dL_lift_pos2 m)].
Qed.

(* t_0 == 0（分子归零两步：q·0 == 0，0/(M#1) == 0） *)
Lemma b5dL_tkq_0 : forall (q : Q) (M : nat), Qeq (b5dL_tkq q M 0) 0.
Proof.
  intros q M.
  unfold b5dL_tkq.
  change (Z.of_nat 0) with 0%Z.
  rewrite (Qmult_0_r q).
  unfold Qdiv.
  rewrite (Qmult_0_l (Qinv (Z.of_nat M # 1))).
  reflexivity.
Qed.

(* t_M == q（field；M#1 ≠ 0 由 0 < M） *)
Lemma b5dL_tkq_M : forall (q : Q) (M : nat), (0 < M)%nat ->
  Qeq (b5dL_tkq q M M) q.
Proof.
  intros q M HM.
  unfold b5dL_tkq.
  field.
  intro Hz.
  unfold Qeq in Hz. simpl in Hz.
  lia.
Qed.

(* 步进恒等：t_{S k} == t_k + q/M（field + lift_succ_q 分子重写） *)
Lemma b5dL_tkq_succ : forall (q : Q) (M k : nat), (0 < M)%nat ->
  Qeq (b5dL_tkq q M (Datatypes.S k))
      (b5dL_tkq q M k + b5dL_qdiv q M).
Proof.
  intros q M k HM.
  unfold b5dL_tkq, b5dL_qdiv.
  rewrite (b5dL_lift_succ_q k).
  field.
  intro Hz.
  unfold Qeq in Hz. simpl in Hz.
  lia.
Qed.

(* 网格点域证书：0<q ∧ q<1 ∧ k≤M ⟹ cw_unit (real_const t_k)（经 b5c_const_unit） *)
Lemma b5dL_tkC : forall (q : Q) (Hq0 : Qlt 0 q) (Hq1 : Qlt q 1)
  (M : nat) (k : nat), (0 < M)%nat -> (k <= M)%nat ->
  cw_unit (real_const (b5dL_tkq q M k)).
Proof.
  intros q Hq0 Hq1 M k HM Hk.
  unfold cw_unit.
  apply (b5c_const_unit (b5dL_tkq q M k)).
  - exact (b5dL_tkq_nonneg q M k (b5dH_q_pos_le q Hq0) HM).
  - apply (Qle_trans (b5dL_tkq q M k) 1 1).
    + exact (b5dL_tkq_le1 q M k (b5dH_q_pos_le q Hq0) (b5dH_q_lt1_le q Hq1) HM Hk).
    + apply Qle_refl.
Qed.

(* ============================================================ *)
(* 段 A §4：Qnsum 恒等（Q 层 + Real 桥）                        *)
(* ============================================================ *)

(* Σ_{k<N} c == (N#1)·c（Q 层；归纳 + lift_succ_q + ring） *)
Lemma b5dL_Qnsum_const : forall (c : Q) (M : nat),
  Qeq (b5dL_Qnsum (fun _ : nat => c) M) (Qmult (Z.of_nat M # 1) c).
Proof.
  intros c M.
  induction M as [| M IH]; simpl.
  - ring.
  - rewrite IH.
    rewrite (b5dL_lift_succ_q M).
    ring.
Qed.

(* Real 桥：b4_nsum (real_const ∘ b) == real_const (Qnsum b)（归纳 + b5dH_plus_const_eq） *)
Lemma b5dL_nsum_real : forall (b : nat -> Q) (M : nat),
  real_eq (b4_nsum (fun k => real_const (b k)) M)
          (real_const (b5dL_Qnsum b M)).
Proof.
  intros b M.
  induction M as [| M IH]; simpl.
  - apply real_eq_of_zero_diff. intro n.
    rewrite (real_const_proj 0 n).
    cbn [projT1 real_zero].
    reflexivity.
  - apply (real_eq_trans _ (real_plus (real_const (b5dL_Qnsum b M))
                                      (real_const (b M))) _).
    + apply (RealSetoid.real_eq_plus_compat
               (b4_nsum (fun k : nat => real_const (b k)) M)
               (real_const (b M))
               (real_const (b5dL_Qnsum b M)) (real_const (b M))).
      * exact IH.
      * apply real_eq_refl.
    + exact (b5dH_plus_const_eq (b5dL_Qnsum b M) (b M)).
Qed.

(* ============================================================ *)
(* 段 A §5：Real glue（δ 链实例化 Hstep 时把 C5 输出的            *)
(*   eps·|h| + eps' 桥成 real_const (b k) 必需；δ 无关先闭）      *)
(* ============================================================ *)

(* |real_const a| == real_const (Qabs a)（逐点 Qabs_wd 于常量坐标） *)
Lemma b5dL_abs_const : forall (a : Q),
  real_eq (real_abs (real_const a)) (real_const (Qabs a)).
Proof.
  intro a.
  apply real_eq_of_zero_diff.
  intro n.
  rewrite (real_abs_proj (real_const a) n).
  rewrite (real_const_proj a n).
  rewrite (real_const_proj (Qabs a) n).
  ring.
Qed.

(* real_const a · real_const b == real_const (a·b)（逐点 ring） *)
Lemma b5dL_mult_const : forall (a b : Q),
  real_eq (real_mult (real_const a) (real_const b)) (real_const (a * b)).
Proof.
  intros a b.
  apply real_eq_of_zero_diff.
  intro n.
  rewrite (real_mult_proj (real_const a) (real_const b) n).
  rewrite (real_const_proj a n).
  rewrite (real_const_proj b n).
  rewrite (real_const_proj (a * b) n).
  ring.
Qed.

(* ============================================================ *)
(* 段 B：望远镜前提式（核心骨架——纯 f/g 形；结论含三角松量 e）    *)
(*   设计（设计记录 §3.3/§3.4）：real_le := Or(lt,eq) 下           *)
(*   |ΣΔ| ≤ Σ|Δ| 无松量不可证 ⟹ 用 b4_nsum_tri（e k > 0 松量）   *)
(*   结论 = real_const (Qnsum b M + Qnsum e M)。                  *)
(* ============================================================ *)

(* |Σ_{k<N} Δk| ≤ Σ|Δk| + Σe：直接应用 b4_nsum_tri（e 正性前提） *)
(* 注：b4_nsum_tri 的 e 前提是 real_lt real_zero (e k)——由 Qlt 0 (e k) 经
   Qlt_to_QltT + real_const_pos 供给 *)

(* 纯 f/g 望远镜前提式：每步 |f(g_{k+1})−f(g_k)| ≤ real_const (b k)
   ⟹ |f(g_M)−f(g_0)| ≤ real_const (Qnsum b M + Qnsum e M)
   证法 = b4_chain_lipschitz 样板：telescope + tri + nsum_le + nsum_real 证毕 *)
Lemma b5dL_telescope_premise : forall (f : Real -> Real) (g : nat -> Real)
  (b e : nat -> Q) (M : nat),
  (forall k : nat, (k < M)%nat -> Qlt 0 (e k)) ->
  (forall k : nat, (k < M)%nat ->
     real_le (real_abs (real_plus (f (g (Datatypes.S k))) (real_opp (f (g k)))))
             (real_const (b k))) ->
  real_le (real_abs (real_plus (f (g M)) (real_opp (f (g 0%nat)))))
          (real_const (Qplus (b5dL_Qnsum b M) (b5dL_Qnsum e M))).
Proof.
  intros f g b e M He Hstep.
  (* 和项与松量序列 *)
  set (d := fun k : nat => real_plus (f (g (Datatypes.S k))) (real_opp (f (g k)))).
  set (ek := fun k : nat => real_const (e k)).
  (* 1) 望远镜：Σ d == f(g M) − f(g 0)（real_eq；直接应用 b4_nsum_telescope） *)
  assert (Htel : real_eq (b4_nsum d M)
                         (real_plus (f (g M)) (real_opp (f (g 0%nat))))).
  { unfold d. apply (b4_nsum_telescope f g M). }
  (* 2) |Σd| ≤ Σ|d| + Σek（b4_nsum_tri；e k > 0 逐点） *)
  assert (Htri : real_le (real_abs (b4_nsum d M))
                         (real_plus (b4_nsum (fun k => real_abs (d k)) M)
                                    (b4_nsum ek M))).
  { apply (b4_nsum_tri d ek M).
    intros k Hk. unfold ek.
    apply real_const_pos. apply Qlt_to_QltT. exact (He k Hk). }
  (* 3) Σ|d| ≤ Σ real_const(b k)（b4_nsum_le；直接应用 Hstep） *)
  assert (Hle1 : real_le (b4_nsum (fun k => real_abs (d k)) M)
                         (b4_nsum (fun k => real_const (b k)) M)).
  { apply b4_nsum_le.
    intros k Hk. unfold d. exact (Hstep k Hk). }
  (* 4) Σreal_const(b) == real_const (Qnsum b M)；Σek == real_const (Qnsum e M) *)
  (* 5) 组装：|端点| == |Σd| ≤ (Σ|d| + Σek) ≤ (Σb-real + Σe-real) == real_const(Qnsum b M + Qnsum e M) *)
  apply (real_le_trans
           (real_abs (real_plus (f (g M)) (real_opp (f (g 0%nat)))))
           (real_plus (b4_nsum (fun k => real_abs (d k)) M) (b4_nsum ek M))
           (real_const (Qplus (b5dL_Qnsum b M) (b5dL_Qnsum e M)))).
  - (* |端点| == |Σd|（Htel + abs compat）且 |Σd| ≤ Σ|d| + Σek（Htri） *)
    apply (RealSetoid.real_le_id_l
             (real_abs (real_plus (f (g M)) (real_opp (f (g 0%nat)))))
             (real_abs (b4_nsum d M))
             (real_plus (b4_nsum (fun k => real_abs (d k)) M) (b4_nsum ek M))).
    + apply real_abs_eq_compat. apply real_eq_sym. exact Htel.
    + exact Htri.
  - apply (real_le_trans
             (real_plus (b4_nsum (fun k => real_abs (d k)) M) (b4_nsum ek M))
             (real_plus (b4_nsum (fun k => real_const (b k)) M) (b4_nsum ek M))
             (real_const (Qplus (b5dL_Qnsum b M) (b5dL_Qnsum e M)))).
    + apply (real_le_plus_compat
               (b4_nsum (fun k => real_abs (d k)) M)
               (b4_nsum (fun k => real_const (b k)) M)
               (b4_nsum ek M) (b4_nsum ek M)).
      * exact Hle1.
      * apply real_le_refl.
    + apply (RealSetoid.real_eq_le
               (real_plus (b4_nsum (fun k : nat => real_const (b k)) M)
                          (b4_nsum ek M))
               (real_const (Qplus (b5dL_Qnsum b M) (b5dL_Qnsum e M)))).
      apply (real_eq_trans
               (real_plus (b4_nsum (fun k : nat => real_const (b k)) M)
                          (b4_nsum ek M))
               (real_plus (real_const (b5dL_Qnsum b M))
                          (real_const (b5dL_Qnsum e M)))
               (real_const (Qplus (b5dL_Qnsum b M) (b5dL_Qnsum e M)))).
      * apply (RealSetoid.real_eq_plus_compat
                 (b4_nsum (fun k : nat => real_const (b k)) M)
                 (b4_nsum ek M)
                 (real_const (b5dL_Qnsum b M)) (real_const (b5dL_Qnsum e M))).
        -- exact (b5dL_nsum_real b M).
        -- unfold ek. exact (b5dL_nsum_real e M).
      * exact (b5dH_plus_const_eq (b5dL_Qnsum b M) (b5dL_Qnsum e M)).
Qed.

(* ============================================================ *)
(* 段 D：eps 预算 Q 层算术（b_k := eps0Q·(q/M) + eps0'Q）         *)
(*   设计（设计记录 §3.5，既定）：eps0Q := epsQ/(2q)、       *)
(*   eps0'Q := epsQ/(4M)；三角松量 e_k := eps0'Q 并入后总闭式     *)
(*   eps0Q·q + 2M·eps0'Q == epsQ（紧，零浪费）                    *)
(* ============================================================ *)

(* 每步预算 b_k（k 无关；δ 链实例化 Hstep 的 RHS = real_const (b k)） *)
Definition b5dL_bk (q : Q) (M : nat) (epsQ : Q) (_ : nat) : Q :=
  (epsQ / (2 * q)) * (b5dL_qdiv q M) + (epsQ / (4 * (Z.of_nat M # 1))).

(* 三角松量 e_k := eps0'Q（与 bk 第二项同值；b4_nsum_tri 的 e） *)
Definition b5dL_epsQ1 (M : nat) (epsQ : Q) : Q :=
  epsQ / (4 * (Z.of_nat M # 1)).

(* 2·q > 0（q > 0；field 条件件） *)
Lemma b5dL_two_q_pos : forall (q : Q), Qlt 0 q -> Qlt 0 (2 * q).
Proof.
  intros q Hq0.
  apply (Qmult_lt_0_compat 2 q).
  - unfold Qlt. simpl. lia.
  - exact Hq0.
Qed.

(* 4·(M#1) > 0（0 < M；field 条件件） *)
Lemma b5dL_four_M_pos : forall (M : nat), (0 < M)%nat -> Qlt 0 (4 * (Z.of_nat M # 1)).
Proof.
  intros M HM.
  destruct M as [| m]; [exfalso; lia | idtac].
  apply (Qmult_lt_0_compat 4 (Z.of_nat (Datatypes.S m) # 1)).
  - unfold Qlt. simpl. lia.
  - exact (b5dL_lift_pos2 m).
Qed.

(* 0 < epsQ/(4·(M#1))（epsQ > 0 ∧ 0 < M；b4_nsum_tri 的 e 正性前提） *)
Lemma b5dL_epsQ1_pos : forall (epsQ : Q) (M : nat),
  Qlt 0 epsQ -> (0 < M)%nat -> Qlt 0 (b5dL_epsQ1 M epsQ).
Proof.
  intros epsQ M Heps HM.
  unfold b5dL_epsQ1.
  destruct M as [| m]; [exfalso; lia | idtac].
  apply (Qmult_lt_0_compat epsQ (Qinv (4 * (Z.of_nat (Datatypes.S m) # 1)))).
  - exact Heps.
  - apply Qinv_lt_0_compat.
    apply (Qmult_lt_0_compat 4 (Z.of_nat (Datatypes.S m) # 1)).
    + unfold Qlt. simpl. lia.
    + exact (b5dL_lift_pos2 m).
Qed.

(* 预算闭式：Qnsum(bk) + Qnsum(epsQ1 常值) == epsQ
   证法：Qnsum_const 重写 ×2 + unfold bk + field（除零条件为合取形
   ~ x == 0，逐个 nz 件 + repeat split 收） *)
Lemma b5dL_budget_closure : forall (q : Q) (M : nat) (epsQ : Q),
  Qlt 0 q -> (0 < M)%nat -> Qlt 0 epsQ ->
  Qeq (Qplus (b5dL_Qnsum (b5dL_bk q M epsQ) M)
             (b5dL_Qnsum (fun _ : nat => b5dL_epsQ1 M epsQ) M))
      epsQ.
Proof.
  intros q M epsQ Hq0 HM Heps.
  rewrite (b5dL_Qnsum_const (b5dL_bk q M epsQ 0) M).
  rewrite (b5dL_Qnsum_const (b5dL_epsQ1 M epsQ) M).
  unfold b5dL_bk, b5dL_qdiv, b5dL_epsQ1.
  field.
  all: try (unfold Qeq in *; simpl in *; lia).
  all: repeat split.
  all: try (intro Hz;
    first [ apply (b5dL_q_lt0_nz q Hq0); exact Hz
          | apply (b5dL_q_lt0_nz (2 * q) (b5dL_two_q_pos q Hq0)); exact Hz
          | destruct M as [| m]; [exfalso; lia | apply (b5dL_q_lt0_nz (Z.of_nat (Datatypes.S m) # 1) (b5dL_lift_pos2 m)); exact Hz]
          | apply (b5dL_q_lt0_nz (4 * (Z.of_nat M # 1)) (b5dL_four_M_pos M HM)); exact Hz ]).
Qed.

(* ============================================================ *)
(* 段 C：J 网格望远镜前提式（证书参数化）                         *)
(*   设计（设计记录 §3.4）：J 的域证书是 Set 层数据且 k > M 时      *)
(*   cw_unit (real_const (tkq q M k)) 无居留 ⟹ b4_nsum_telescope  *)
(*   的 f/g 形式不可直套 ⟹ 自建归纳 Aux(n)（≤ M 前缀和）：          *)
(*   每步三角用 real_abs_triangle_le_eps（e n 松量），中证书现场   *)
(*   取 b5dL_tkC；Hstep 前提对证书全称化（与 C5 输出兼容）。       *)
(* ============================================================ *)

Lemma b5dL_J_grid_premise : forall (q : Q) (Hq0 : Qlt 0 q) (Hq1 : Qlt q 1)
  (M : nat) (b e : nat -> Q),
  (forall k : nat, (k < M)%nat -> Qlt 0 (e k)) ->
  (forall k : nat, (k < M)%nat ->
     forall (Hk : cw_unit (real_const (b5dL_tkq q M k)))
            (Hk1 : cw_unit (real_const (b5dL_tkq q M (Datatypes.S k)))),
     real_le (real_abs (real_plus (b5c_J (real_const (b5dL_tkq q M (Datatypes.S k))) Hk1)
                                  (real_opp (b5c_J (real_const (b5dL_tkq q M k)) Hk))))
             (real_const (b k))) ->
  forall (C0 : cw_unit (real_const (b5dL_tkq q M 0)))
         (CM : cw_unit (real_const (b5dL_tkq q M M))),
  real_le (real_abs (real_plus (b5c_J (real_const (b5dL_tkq q M M)) CM)
                               (real_opp (b5c_J (real_const (b5dL_tkq q M 0)) C0))))
          (real_const (Qplus (b5dL_Qnsum b M) (b5dL_Qnsum e M))).
Proof.
  intros q Hq0 Hq1 M b e He Hstep C0 CM.
  (* Aux：≤ M 前缀和 |J(t_n)Cn − J(t_0)C0| ≤ real_const (Qnsum b n + Qnsum e n) *)
  assert (Aux : forall (n : nat), (n <= M)%nat ->
            forall (Cn : cw_unit (real_const (b5dL_tkq q M n)))
                   (C0' : cw_unit (real_const (b5dL_tkq q M 0))),
            real_le (real_abs (real_plus (b5c_J (real_const (b5dL_tkq q M n)) Cn)
                                         (real_opp (b5c_J (real_const (b5dL_tkq q M 0)) C0'))))
                    (real_const (Qplus (b5dL_Qnsum b n) (b5dL_Qnsum e n)))).
  { induction n as [| n IH]; intros Hn Cn C0'.
    - (* 基 n = 0：|J0 − J0| == 0 ≤ real_const (Qnsum b 0 + Qnsum e 0) *)
      assert (Hjw : real_eq (b5c_J (real_const (b5dL_tkq q M 0)) Cn)
                            (b5c_J (real_const (b5dL_tkq q M 0)) C0')).
      { apply (b5p2_J_wd (real_const (b5dL_tkq q M 0))
                         (real_const (b5dL_tkq q M 0)) Cn C0').
        apply real_eq_refl. }
      apply (real_le_trans
               (real_abs (real_plus (b5c_J (real_const (b5dL_tkq q M 0)) Cn)
                                    (real_opp (b5c_J (real_const (b5dL_tkq q M 0)) C0'))))
               real_zero
               (real_const (Qplus (b5dL_Qnsum b 0) (b5dL_Qnsum e 0)))).
      + apply (RealSetoid.real_eq_le _ _).
        apply (real_eq_trans _ (real_abs (real_plus (b5c_J (real_const (b5dL_tkq q M 0)) Cn)
                                                    (real_opp (b5c_J (real_const (b5dL_tkq q M 0)) Cn)))) _).
        * apply real_abs_eq_compat.
          apply (RealSetoid.real_eq_plus_compat
                   (b5c_J (real_const (b5dL_tkq q M 0)) Cn)
                   (real_opp (b5c_J (real_const (b5dL_tkq q M 0)) C0'))
                   (b5c_J (real_const (b5dL_tkq q M 0)) Cn)
                   (real_opp (b5c_J (real_const (b5dL_tkq q M 0)) Cn))).
          -- apply real_eq_refl.
          -- apply (RealSetoid.real_eq_opp_compat
                     (b5c_J (real_const (b5dL_tkq q M 0)) C0')
                     (b5c_J (real_const (b5dL_tkq q M 0)) Cn)).
             apply real_eq_sym. exact Hjw.
        * apply (real_eq_trans _ (real_abs real_zero) _).
          -- apply real_abs_eq_compat. exact (real_plus_opp (b5c_J (real_const (b5dL_tkq q M 0)) Cn)).
          -- apply real_abs_zero_req.
      + apply (RealSetoid.real_eq_le _ _).
        apply real_eq_sym.
        apply real_eq_of_zero_diff.
        intro n0.
        rewrite (real_const_proj (Qplus (b5dL_Qnsum b 0) (b5dL_Qnsum e 0)) n0).
        cbn [b5dL_Qnsum projT1 real_zero].
        ring.
    - (* 步 n → S n：三角 + Hstep + IH *)
      assert (Hn' : (n <= M)%nat) by lia.
      assert (Hnlt : (n < M)%nat) by lia.
      assert (HM' : (0 < M)%nat) by lia.
      assert (Hmid : cw_unit (real_const (b5dL_tkq q M n))).
      { exact (b5dL_tkC q Hq0 Hq1 M n HM' Hn'). }
      (* 每步界（证书现场：中证书 = canonical） *)
      assert (Hstep_n : real_le
               (real_abs (real_plus (b5c_J (real_const (b5dL_tkq q M (Datatypes.S n))) Cn)
                                    (real_opp (b5c_J (real_const (b5dL_tkq q M n)) Hmid))))
               (real_const (b n))).
      { exact (Hstep n Hnlt Hmid Cn). }
      assert (Hih_n : real_le
               (real_abs (real_plus (b5c_J (real_const (b5dL_tkq q M n)) Hmid)
                                    (real_opp (b5c_J (real_const (b5dL_tkq q M 0)) C0'))))
               (real_const (Qplus (b5dL_Qnsum b n) (b5dL_Qnsum e n)))).
      { exact (IH Hn' Hmid C0'). }
      (* 三角（e n 松量）：|A−C0| ≤ (|A−B| + |B−C0|) + e n *)
      assert (Htri : real_le
               (real_abs (real_plus
                  (real_plus (b5c_J (real_const (b5dL_tkq q M (Datatypes.S n))) Cn)
                             (real_opp (b5c_J (real_const (b5dL_tkq q M n)) Hmid)))
                  (real_plus (b5c_J (real_const (b5dL_tkq q M n)) Hmid)
                             (real_opp (b5c_J (real_const (b5dL_tkq q M 0)) C0')))))
               (real_plus
                  (real_plus
                     (real_abs (real_plus (b5c_J (real_const (b5dL_tkq q M (Datatypes.S n))) Cn)
                                          (real_opp (b5c_J (real_const (b5dL_tkq q M n)) Hmid))))
                     (real_abs (real_plus (b5c_J (real_const (b5dL_tkq q M n)) Hmid)
                                          (real_opp (b5c_J (real_const (b5dL_tkq q M 0)) C0')))))
                  (real_const (e n)))).
      { apply (real_abs_triangle_le_eps
                 (real_plus (b5c_J (real_const (b5dL_tkq q M (Datatypes.S n))) Cn)
                            (real_opp (b5c_J (real_const (b5dL_tkq q M n)) Hmid)))
                 (real_plus (b5c_J (real_const (b5dL_tkq q M n)) Hmid)
                            (real_opp (b5c_J (real_const (b5dL_tkq q M 0)) C0')))
                 (real_const (e n))).
        apply real_const_pos. apply Qlt_to_QltT. exact (He n Hnlt). }
      (* 中间环代：((A−B) + (B−C0)) == (A−C0) *)
      assert (Hring : real_eq
               (real_plus (real_plus (b5c_J (real_const (b5dL_tkq q M (Datatypes.S n))) Cn)
                                     (real_opp (b5c_J (real_const (b5dL_tkq q M n)) Hmid)))
                          (real_plus (b5c_J (real_const (b5dL_tkq q M n)) Hmid)
                                     (real_opp (b5c_J (real_const (b5dL_tkq q M 0)) C0'))))
               (real_plus (b5c_J (real_const (b5dL_tkq q M (Datatypes.S n))) Cn)
                          (real_opp (b5c_J (real_const (b5dL_tkq q M 0)) C0')))).
      { apply real_eq_of_zero_diff. intro n0.
        rewrite (real_plus_proj
                   (real_plus (b5c_J (real_const (b5dL_tkq q M (Datatypes.S n))) Cn)
                              (real_opp (b5c_J (real_const (b5dL_tkq q M n)) Hmid)))
                   (real_plus (b5c_J (real_const (b5dL_tkq q M n)) Hmid)
                              (real_opp (b5c_J (real_const (b5dL_tkq q M 0)) C0'))) n0).
        rewrite (real_plus_proj (b5c_J (real_const (b5dL_tkq q M (Datatypes.S n))) Cn)
                                (real_opp (b5c_J (real_const (b5dL_tkq q M n)) Hmid)) n0).
        rewrite (real_opp_proj (b5c_J (real_const (b5dL_tkq q M n)) Hmid) n0).
        rewrite (real_plus_proj (b5c_J (real_const (b5dL_tkq q M n)) Hmid)
                                (real_opp (b5c_J (real_const (b5dL_tkq q M 0)) C0')) n0).
        rewrite (real_opp_proj (b5c_J (real_const (b5dL_tkq q M 0)) C0') n0).
        rewrite (real_plus_proj (b5c_J (real_const (b5dL_tkq q M (Datatypes.S n))) Cn)
                                (real_opp (b5c_J (real_const (b5dL_tkq q M 0)) C0')) n0).
        rewrite (real_opp_proj (b5c_J (real_const (b5dL_tkq q M 0)) C0') n0).
        ring. }
      (* |A−C0| ≤ (|A−B| + |B−C0|) + e n（经 |(A−B)+(B−C0)| 换序） *)
      assert (Hmain : real_le
               (real_abs (real_plus (b5c_J (real_const (b5dL_tkq q M (Datatypes.S n))) Cn)
                                    (real_opp (b5c_J (real_const (b5dL_tkq q M 0)) C0'))))
               (real_plus (real_plus
                             (real_abs (real_plus (b5c_J (real_const (b5dL_tkq q M (Datatypes.S n))) Cn)
                                                  (real_opp (b5c_J (real_const (b5dL_tkq q M n)) Hmid))))
                             (real_abs (real_plus (b5c_J (real_const (b5dL_tkq q M n)) Hmid)
                                                  (real_opp (b5c_J (real_const (b5dL_tkq q M 0)) C0')))))
                          (real_const (e n)))).
      { apply (RealSetoid.real_le_id_l
                 (real_abs (real_plus (b5c_J (real_const (b5dL_tkq q M (Datatypes.S n))) Cn)
                                      (real_opp (b5c_J (real_const (b5dL_tkq q M 0)) C0'))))
                 (real_abs (real_plus
                    (real_plus (b5c_J (real_const (b5dL_tkq q M (Datatypes.S n))) Cn)
                               (real_opp (b5c_J (real_const (b5dL_tkq q M n)) Hmid)))
                    (real_plus (b5c_J (real_const (b5dL_tkq q M n)) Hmid)
                               (real_opp (b5c_J (real_const (b5dL_tkq q M 0)) C0')))))
                 (real_plus (real_plus
                               (real_abs (real_plus (b5c_J (real_const (b5dL_tkq q M (Datatypes.S n))) Cn)
                                                    (real_opp (b5c_J (real_const (b5dL_tkq q M n)) Hmid))))
                               (real_abs (real_plus (b5c_J (real_const (b5dL_tkq q M n)) Hmid)
                                                    (real_opp (b5c_J (real_const (b5dL_tkq q M 0)) C0')))))
                            (real_const (e n)))).
        - apply real_abs_eq_compat. apply real_eq_sym. exact Hring.
        - exact Htri. }
      (* (|A−B| + |B−C0|) + e n ≤ (real_const (b n) + real_const (Qnsum b n + Qnsum e n)) + real_const (e n) *)
      assert (Hrhs : real_le
               (real_plus (real_plus
                             (real_abs (real_plus (b5c_J (real_const (b5dL_tkq q M (Datatypes.S n))) Cn)
                                                  (real_opp (b5c_J (real_const (b5dL_tkq q M n)) Hmid))))
                             (real_abs (real_plus (b5c_J (real_const (b5dL_tkq q M n)) Hmid)
                                                  (real_opp (b5c_J (real_const (b5dL_tkq q M 0)) C0')))))
                          (real_const (e n)))
               (real_plus (real_plus (real_const (b n))
                                     (real_const (Qplus (b5dL_Qnsum b n) (b5dL_Qnsum e n))))
                          (real_const (e n)))).
      { apply (real_le_plus_compat
                 (real_plus (real_abs (real_plus (b5c_J (real_const (b5dL_tkq q M (Datatypes.S n))) Cn)
                                                 (real_opp (b5c_J (real_const (b5dL_tkq q M n)) Hmid))))
                            (real_abs (real_plus (b5c_J (real_const (b5dL_tkq q M n)) Hmid)
                                                 (real_opp (b5c_J (real_const (b5dL_tkq q M 0)) C0')))))
                 (real_plus (real_const (b n)) (real_const (Qplus (b5dL_Qnsum b n) (b5dL_Qnsum e n))))
                 (real_const (e n)) (real_const (e n))).
        - apply (real_le_plus_compat
                   (real_abs (real_plus (b5c_J (real_const (b5dL_tkq q M (Datatypes.S n))) Cn)
                                        (real_opp (b5c_J (real_const (b5dL_tkq q M n)) Hmid))))
                   (real_const (b n))
                   (real_abs (real_plus (b5c_J (real_const (b5dL_tkq q M n)) Hmid)
                                        (real_opp (b5c_J (real_const (b5dL_tkq q M 0)) C0'))))
                   (real_const (Qplus (b5dL_Qnsum b n) (b5dL_Qnsum e n)))).
          + exact Hstep_n.
          + exact Hih_n.
        - apply real_le_refl. }
      (* 结论：|A−C0| ≤ ... == real_const (Qnsum b (S n) + Qnsum e (S n)) *)
      apply (real_le_trans
               (real_abs (real_plus (b5c_J (real_const (b5dL_tkq q M (Datatypes.S n))) Cn)
                                    (real_opp (b5c_J (real_const (b5dL_tkq q M 0)) C0'))))
               (real_plus (real_plus (real_const (b n))
                                     (real_const (Qplus (b5dL_Qnsum b n) (b5dL_Qnsum e n))))
                          (real_const (e n)))
               (real_const (Qplus (b5dL_Qnsum b (Datatypes.S n)) (b5dL_Qnsum e (Datatypes.S n))))).
      + apply (real_le_trans
                 (real_abs (real_plus (b5c_J (real_const (b5dL_tkq q M (Datatypes.S n))) Cn)
                                      (real_opp (b5c_J (real_const (b5dL_tkq q M 0)) C0'))))
                 (real_plus (real_plus
                               (real_abs (real_plus (b5c_J (real_const (b5dL_tkq q M (Datatypes.S n))) Cn)
                                                    (real_opp (b5c_J (real_const (b5dL_tkq q M n)) Hmid))))
                               (real_abs (real_plus (b5c_J (real_const (b5dL_tkq q M n)) Hmid)
                                                    (real_opp (b5c_J (real_const (b5dL_tkq q M 0)) C0')))))
                            (real_const (e n)))
                 (real_plus (real_plus (real_const (b n))
                                       (real_const (Qplus (b5dL_Qnsum b n) (b5dL_Qnsum e n))))
                            (real_const (e n)))).
        * exact Hmain.
        * exact Hrhs.
      + apply (RealSetoid.real_eq_le
                 (real_plus (real_plus (real_const (b n))
                                       (real_const (Qplus (b5dL_Qnsum b n) (b5dL_Qnsum e n))))
                            (real_const (e n)))
                 (real_const (Qplus (b5dL_Qnsum b (Datatypes.S n)) (b5dL_Qnsum e (Datatypes.S n))))).
        apply real_eq_of_zero_diff.
        intro n0.
        rewrite (real_plus_proj
                   (real_plus (real_const (b n)) (real_const (Qplus (b5dL_Qnsum b n) (b5dL_Qnsum e n))))
                   (real_const (e n)) n0).
        rewrite (real_plus_proj (real_const (b n))
                                (real_const (Qplus (b5dL_Qnsum b n) (b5dL_Qnsum e n))) n0).
        rewrite (real_const_proj (b n) n0).
        rewrite (real_const_proj (Qplus (b5dL_Qnsum b n) (b5dL_Qnsum e n)) n0).
        rewrite (real_const_proj (e n) n0).
        rewrite (real_const_proj (Qplus (b5dL_Qnsum b (Datatypes.S n)) (b5dL_Qnsum e (Datatypes.S n))) n0).
        cbn [b5dL_Qnsum projT1 real_zero].
        ring. }
  (* 终：n := M *)
  exact (Aux M (Nat.le_refl M) CM C0).
Qed.

(* ============================================================ *)
(* 段 E：前提式（δ 链就绪后只剩实例化 Hstep）                 *)
(* ============================================================ *)

(* ∀Real e > 0 取 Q 下界：∃c > 0 有理：real_le (real_const c) e
   证法：destruct e 的正性见证（e_n > eps0 尾部）⟹ c := eps0/2 严格低于 e
   （lt 分支见证 eps0/2；qltT_eq_compat_l/r 作坐标重写） *)
Lemma b5dL_eps_real_lower : forall (e : Real), real_lt real_zero e ->
  sigT (fun c : Q => And (QltT 0 c) (real_le (real_const c) e)).
Proof.
  intros e He.
  destruct He as [eps0 [Heps0 [N0 HN0]]].
  exists (eps0 / 2)%Q.
  split.
  - apply (q_half_pos eps0). exact Heps0.
  - apply (RealSetoid.real_lt_le_iff_req (real_const (eps0 / 2)) e). left.
    unfold real_lt.
    exists (eps0 / 2)%Q.
    split.
    + apply (q_half_pos eps0). exact Heps0.
    + exists N0.
      intros n Hn.
      (* 坐标重写：projT1 (real_const (eps0/2)) n == eps0/2 *)
      apply (qltT_eq_compat_r (projT1 e n - projT1 (real_const (eps0 / 2)) n)
                              (projT1 e n - (eps0 / 2))
                              (eps0 / 2)).
      * apply Qplus_comp; [ apply Qeq_refl | ].
        apply (Qopp_comp _ _ (real_const_proj (eps0 / 2) n)).
      * apply Qlt_to_QltT.
        (* 目标：eps0/2 < e_n − eps0/2 ⟺ eps0 < e_n（HN0 直供） *)
        apply (proj2 (Qlt_minus_iff (eps0 / 2) (projT1 e n - (eps0 / 2)))).
        assert (Heq2 : Qeq ((projT1 e n - (eps0 / 2)) - (eps0 / 2))
                          (projT1 e n - eps0)).
        { field.
          all: try (unfold Qeq in *; simpl in *; lia).
          all: try (repeat split).
          all: try (intro Hz; unfold Qeq in Hz; simpl in Hz; lia). }
        rewrite Heq2.
        apply (proj1 (Qlt_minus_iff eps0 (projT1 e n))).
        apply QltT_to_Qlt.
        apply (qltT_eq_compat_r (projT1 e n)
                                (projT1 e n - projT1 real_zero n) eps0).
        -- apply Qeq_sym.
           assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
           rewrite Hz. ring.
        -- exact (HN0 n Hn).
Qed.

(* 网格预算结论：每步前提（bk 预算）⟹ |J(q)Hq − J(0)bz| ≤ real_const epsQ
   证法：J_grid @ (b := bk, e := epsQ1 常值) + tkq_M/tkq_0 端点桥 + budget_closure *)
Lemma b5dL_J_zero_on_grid_premise : forall (q : Q) (Hq0 : Qlt 0 q) (Hq1 : Qlt q 1)
  (M : nat) (HMpos : (0 < M)%nat) (epsQ : Q) (Heps : Qlt 0 epsQ),
  (forall k : nat, (k < M)%nat ->
     forall (Hk : cw_unit (real_const (b5dL_tkq q M k)))
            (Hk1 : cw_unit (real_const (b5dL_tkq q M (Datatypes.S k)))),
     real_le (real_abs (real_plus (b5c_J (real_const (b5dL_tkq q M (Datatypes.S k))) Hk1)
                                  (real_opp (b5c_J (real_const (b5dL_tkq q M k)) Hk))))
             (real_const (b5dL_bk q M epsQ k))) ->
  forall (Hq : cw_unit (real_const q)),
  real_le (real_abs (real_plus (b5c_J (real_const q) Hq)
                               (real_opp (b5c_J (real_const 0) b5c_unit_zero))))
          (real_const epsQ).
Proof.
  intros q Hq0 Hq1 M HMpos epsQ Heps Hstep Hq.
  pose (C0 := b5dL_tkC q Hq0 Hq1 M 0 HMpos (Nat.le_0_l M)).
  pose (CM := b5dL_tkC q Hq0 Hq1 M M HMpos (Nat.le_refl M)).
  (* J 网格望远镜实例：b := bk，e := epsQ1 常值 *)
  assert (Hgrid : real_le
             (real_abs (real_plus (b5c_J (real_const (b5dL_tkq q M M)) CM)
                                  (real_opp (b5c_J (real_const (b5dL_tkq q M 0)) C0))))
             (real_const (Qplus (b5dL_Qnsum (b5dL_bk q M epsQ) M)
                                (b5dL_Qnsum (fun _ : nat => b5dL_epsQ1 M epsQ) M)))).
  { apply (b5dL_J_grid_premise q Hq0 Hq1 M
             (b5dL_bk q M epsQ) (fun _ : nat => b5dL_epsQ1 M epsQ)).
    - intros k Hk. exact (b5dL_epsQ1_pos epsQ M Heps HMpos).
    - intros k Hk. exact (Hstep k Hk). }
  (* 预算闭式：Qnsum(bk) + Qnsum(epsQ1) == epsQ *)
  assert (Hsum : Qeq (Qplus (b5dL_Qnsum (b5dL_bk q M epsQ) M)
                            (b5dL_Qnsum (fun _ : nat => b5dL_epsQ1 M epsQ) M)) epsQ).
  { exact (b5dL_budget_closure q M epsQ Hq0 HMpos Heps). }
  (* 端点桥：t_M == q、t_0 == 0（real_const_qeq + J_wd） *)
  assert (HbrM : real_eq (b5c_J (real_const (b5dL_tkq q M M)) CM)
                         (b5c_J (real_const q) Hq)).
  { apply (b5p2_J_wd (real_const (b5dL_tkq q M M)) (real_const q) CM Hq).
    apply (b5dH_real_const_qeq (b5dL_tkq q M M) q).
    exact (b5dL_tkq_M q M HMpos). }
  assert (Hbr0 : real_eq (b5c_J (real_const (b5dL_tkq q M 0)) C0)
                         (b5c_J (real_const 0) b5c_unit_zero)).
  { apply (b5p2_J_wd (real_const (b5dL_tkq q M 0)) (real_const 0) C0 b5c_unit_zero).
    apply (b5dH_real_const_qeq (b5dL_tkq q M 0) 0).
    exact (b5dL_tkq_0 q M). }
  (* |J(q)Hq − J(0)bz| == |J(t_M)CM − J(t_0)C0|（abs compat 桥） *)
  assert (Habs : real_eq
             (real_abs (real_plus (b5c_J (real_const q) Hq)
                                  (real_opp (b5c_J (real_const 0) b5c_unit_zero))))
             (real_abs (real_plus (b5c_J (real_const (b5dL_tkq q M M)) CM)
                                  (real_opp (b5c_J (real_const (b5dL_tkq q M 0)) C0))))).
  { apply real_abs_eq_compat.
    apply (RealSetoid.real_eq_plus_compat
             (b5c_J (real_const q) Hq)
             (real_opp (b5c_J (real_const 0) b5c_unit_zero))
             (b5c_J (real_const (b5dL_tkq q M M)) CM)
             (real_opp (b5c_J (real_const (b5dL_tkq q M 0)) C0))).
    - apply real_eq_sym. exact HbrM.
    - apply (RealSetoid.real_eq_opp_compat
               (b5c_J (real_const 0) b5c_unit_zero)
               (b5c_J (real_const (b5dL_tkq q M 0)) C0)).
      apply real_eq_sym. exact Hbr0. }
  (* 组装：|J(q)−J(0)| ≤ |J(t_M)−J(t_0)| ≤ real_const (Qnsum+Qnsum) == real_const epsQ *)
  apply (real_le_trans
           (real_abs (real_plus (b5c_J (real_const q) Hq)
                                (real_opp (b5c_J (real_const 0) b5c_unit_zero))))
           (real_abs (real_plus (b5c_J (real_const (b5dL_tkq q M M)) CM)
                                (real_opp (b5c_J (real_const (b5dL_tkq q M 0)) C0))))
           (real_const epsQ)).
  - apply (RealSetoid.real_eq_le
             (real_abs (real_plus (b5c_J (real_const q) Hq)
                                  (real_opp (b5c_J (real_const 0) b5c_unit_zero))))
             (real_abs (real_plus (b5c_J (real_const (b5dL_tkq q M M)) CM)
                                  (real_opp (b5c_J (real_const (b5dL_tkq q M 0)) C0))))).
    exact Habs.
  - apply (RealSetoid.real_le_id_r
             (real_abs (real_plus (b5c_J (real_const (b5dL_tkq q M M)) CM)
                                  (real_opp (b5c_J (real_const (b5dL_tkq q M 0)) C0))))
             (real_const (Qplus (b5dL_Qnsum (b5dL_bk q M epsQ) M)
                                (b5dL_Qnsum (fun _ : nat => b5dL_epsQ1 M epsQ) M)))
             (real_const epsQ)).
    + apply (b5dH_real_const_qeq
               (Qplus (b5dL_Qnsum (b5dL_bk q M epsQ) M)
                      (b5dL_Qnsum (fun _ : nat => b5dL_epsQ1 M epsQ) M)) epsQ).
      exact Hsum.
    + exact Hgrid.
Qed.

(* 主件形前提式：Hmod（∀epsQ > 0，∃M ≥ 1 网格每步前提）⟹ E(q) == 0
   证法：b5dH_E_zero_of_J_zero + b4_abs_le_forall_eps_eq（∀Real e 取 Q 下界 c
   = b5dL_eps_real_lower）+ J_zero_on_grid @ (epsQ := c, M) + J(0)==0 桥（b5dH_J_zero0） *)
Lemma b5dL_E_rational_zero_premise : forall (q : Q) (Hq0 : Qlt 0 q) (Hq1 : Qlt q 1),
  (forall (epsQ : Q), Qlt 0 epsQ ->
     sigT (fun M : nat => And (NatLe 1 M)
       (forall (k : nat), (k < M)%nat ->
          forall (Hk : cw_unit (real_const (b5dL_tkq q M k)))
                 (Hk1 : cw_unit (real_const (b5dL_tkq q M (Datatypes.S k)))),
          real_le (real_abs (real_plus (b5c_J (real_const (b5dL_tkq q M (Datatypes.S k))) Hk1)
                                       (real_opp (b5c_J (real_const (b5dL_tkq q M k)) Hk))))
                  (real_const (b5dL_bk q M epsQ k))))) ->
  forall (Hq : cw_unit (real_const q)),
  real_eq (real_E (real_const q) Hq) real_zero.
Proof.
  intros q Hq0 Hq1 Hmod Hq.
  apply (b5dH_E_zero_of_J_zero (real_const q) Hq).
  apply (b4_abs_le_forall_eps_eq (b5c_J (real_const q) Hq) real_zero).
  intros e He.
  (* Q 下界：∃c > 0：real_le (real_const c) e *)
  destruct (b5dL_eps_real_lower e He) as [c [Hc0 Hcle]].
  destruct (Hmod c (QltT_to_Qlt _ _ Hc0)) as [M [HMpos Hstep]].
  (* |J(q)Hq − J(0)bz| ≤ real_const c（网格实例） *)
  assert (Hle_c : real_le
             (real_abs (real_plus (b5c_J (real_const q) Hq)
                                  (real_opp (b5c_J (real_const 0) b5c_unit_zero))))
             (real_const c)).
  { exact (b5dL_J_zero_on_grid_premise q Hq0 Hq1 M (NatLe_drop 1 M HMpos) c (QltT_to_Qlt _ _ Hc0) Hstep Hq). }
  (* J(0) == 0 桥：|J(q) − 0| == |J(q) − J(0)bz| *)
  assert (Hj0 : real_eq (b5c_J (real_const 0) b5c_unit_zero) real_zero)
    by exact b5dH_J_zero0.
  assert (Habs0 : real_eq
             (real_abs (real_plus (b5c_J (real_const q) Hq) (real_opp real_zero)))
             (real_abs (real_plus (b5c_J (real_const q) Hq)
                                  (real_opp (b5c_J (real_const 0) b5c_unit_zero))))).
  { apply real_abs_eq_compat.
    apply (RealSetoid.real_eq_plus_compat
             (b5c_J (real_const q) Hq) (real_opp real_zero)
             (b5c_J (real_const q) Hq)
             (real_opp (b5c_J (real_const 0) b5c_unit_zero))).
    - apply real_eq_refl.
    - apply (RealSetoid.real_eq_opp_compat real_zero
                                           (b5c_J (real_const 0) b5c_unit_zero)).
      apply real_eq_sym. exact Hj0. }
  apply (real_le_trans
           (real_abs (real_plus (b5c_J (real_const q) Hq) (real_opp real_zero)))
           (real_const c) e).
  - apply (RealSetoid.real_le_id_l
             (real_abs (real_plus (b5c_J (real_const q) Hq) (real_opp real_zero)))
             (real_abs (real_plus (b5c_J (real_const q) Hq)
                                  (real_opp (b5c_J (real_const 0) b5c_unit_zero))))
             (real_const c)).
    + exact Habs0.
    + exact Hle_c.
  - exact Hcle.
Qed.

(* ============================================================ *)
(* end sc2_b5a_item22.v · δ-D2e 前提式望远镜骨架 · 段 A/B/C/D/E   *)
(* ============================================================ *)

(* ============================================================ *)
(* 块 item26（前缀 b5dP_——主件 b5dP_S_diff_closed_r_M_exp_tail）——来源：演变/.ablation/sc2_parallel/sc2_b5a_ode/sc2_b5a_item26.v。 *)
(* ============================================================ *)

(* ============================================================ *)
(* 段 A：主件 b5dP_S_diff_closed_r_M_exp_tail（S-diff 尾形件， *)
(*   Defined 预置）                                             *)
(*   拷贝源 = sc2_b5a_item24.v 主件区 L87–370（机器抽取，零     *)
(*   手抄；其自身 = item10 C4 的 M 参数化 Defined 拷贝——        *)
(*   item24 改动 S1–S5 已做：改名/eps 见证下移（spine-clean）/  *)
(*   exp 部 g 部叶换源 b5dK_（item21）/Qed→Defined）。           *)
(*   改动 A1–A5（尾形化增量，设计 §2.3 表）：语句 HMall 行 →    *)
(*   (NM : nat) + 尾形 HMall；intros 扩名；Nmax 并入 NM；取用点  *)
(*   守卫 + per-n 断言；收尾 Defined（源已 Defined）。体内其余   *)
(*   根引用（b5l_/b5n_/b5i_/b5f_/sc_/real_ 系）零改——全在     *)
(*   证明位，不进 δ 值；δ := real_min δexp δg 照拷。语句类型   *)
(*   除 A2 改动行 = item10 C4 逐字（下游 item27 接口契约）。     *)
(* ============================================================ *)
Lemma b5dP_S_diff_closed_r_M_exp_tail :
  forall (r : Q) (Hr0 : Qle 0 r) (Hr1 : Qlt r 1),
  forall (x : Real) (Hxr : forall n : nat, QleT' (Qabs (projT1 x n)) r),
  forall (M : Q) (HMpos : Qlt 0 M)
    (NM : nat)
    (HMall : forall n : nat, (NM <= n)%nat -> Qle (Qabs (projT1 (b5a_S x) n)) M),
  forall (eps : Real), real_lt real_zero eps ->
  sigT (fun delta : Real => And (real_lt real_zero delta)
    (forall (h : Real), real_lt (real_abs h) delta ->
      forall (eps' : Real), real_lt real_zero eps' ->
      real_le (real_abs (real_plus (b5a_S (real_plus x h))
                 (real_opp (real_plus (b5a_S x)
                            (real_mult (real_mult x (b5a_S x)) (real_mult (b5a_atan_d x) h))))))
              (real_plus (real_mult eps (real_abs h)) eps'))).
Proof.
  intros r Hr0 Hr1 x Hxr M HMpos NM HMall eps Heps.
  (* M：|S(x)_n| ≤ M（0 < M） *)
  assert (HM0 : Qle 0 M). { apply Qlt_le_weak. exact HMpos. }
  (* k2 := k2p := Qinv(8(1+M))：QltT 0、M·k ≤ (1#8) *)
  set (k2 := Qinv (Qmult 8 (Qplus M 1))).
  set (k2p := Qinv (Qmult 8 (Qplus M 1))).
  assert (Hk2T : QltT 0 k2). { unfold k2. apply b5l_k_posT. exact HM0. }
  assert (Hk2pT : QltT 0 k2p). { unfold k2p. apply b5l_k_posT. exact HM0. }
  assert (HMk2 : Qle (Qmult M k2) (1 # 8)). { unfold k2. apply b5l_Mk_le. exact HM0. }
  assert (HMk2p : Qle (Qmult M k2p) (1 # 8)). { unfold k2p. apply b5l_Mk_le. exact HM0. }
  (* 系数吸收事实：coefS1 := (M·k2)·(1#4) ≤ (1#32)；coefG1 := M·2k2p·(1#8) ≤ (1#32) *)
  assert (HcoefS1 : Qle (Qmult (Qmult M k2) (1 # 4)) (1 # 32)).
  { apply (Qle_trans (Qmult (Qmult M k2) (1 # 4)) (Qmult (1 # 8) (1 # 4)) (1 # 32)).
    - apply (Qmult_le_compat_r (Qmult M k2) (1 # 8) (1 # 4)).
      + exact HMk2.
      + change (Qle 0 (1 # 4)). unfold Qle. simpl. lia.
    - apply qeq_imp_qle. ring. }
  assert (HcoefG1 : Qle (Qmult (Qmult M (Qmult 2 k2p)) (1 # 8)) (1 # 32)).
  { apply (Qle_trans (Qmult (Qmult M (Qmult 2 k2p)) (1 # 8))
                     (Qmult (Qmult M k2p) (1 # 4))
                     (1 # 32)).
    - apply qeq_imp_qle. ring.
    - apply (Qle_trans (Qmult (Qmult M k2p) (1 # 4))
                       (Qmult (1 # 8) (1 # 4))
                       (1 # 32)).
      + apply (Qmult_le_compat_r (Qmult M k2p) (1 # 8) (1 # 4)).
        * exact HMk2p.
        * change (Qle 0 (1 # 4)). unfold Qle. simpl. lia.
      + apply qeq_imp_qle. ring. }
  (* eps 见证与 Q 常数正性 *)
  assert (H2T : QltT 0 (1 # 2)) by (apply Qlt_to_QltT; change (Qlt 0 (1 # 2)); unfold Qlt; simpl; lia).
  assert (H4T : QltT 0 (1 # 4)) by (apply Qlt_to_QltT; change (Qlt 0 (1 # 4)); unfold Qlt; simpl; lia).
  assert (H8T : QltT 0 (1 # 8)) by (apply Qlt_to_QltT; change (Qlt 0 (1 # 8)); unfold Qlt; simpl; lia).
  assert (H16T : QltT 0 (1 # 16)) by (apply Qlt_to_QltT; change (Qlt 0 (1 # 16)); unfold Qlt; simpl; lia).
  assert (H32T : QltT 0 (1 # 32)) by (apply Qlt_to_QltT; change (Qlt 0 (1 # 32)); unfold Qlt; simpl; lia).
  (* eps 份额（Real） *)
  set (eps1 := real_mult eps (real_const (1 # 2))).
  assert (Heps1 : real_lt real_zero eps1).
  { unfold eps1. apply real_mult_positive. { exact Heps. } { apply real_const_pos. exact H2T. } }
  set (eps2 := real_mult eps (real_const (1 # 4))).
  assert (Heps2 : real_lt real_zero eps2).
  { unfold eps2. apply real_mult_positive. { exact Heps. } { apply real_const_pos. exact H4T. } }
  (* exp 部 δexp（item3e 主件）与 g 部 δg（b5f_gdiff_pts_r） *)
  destruct (b5dK_exp_part_bound_closed_r_exp r Hr0 Hr1 x Hxr eps1 Heps1) as [δexp [Hδe0 Hδe]].
  destruct (b5dK_gdiff_pts_r_exp r Hr0 Hr1 x Hxr eps2 Heps2 k2 k2p Hk2T Hk2pT) as [δg [Hδg0 Hδg]].
  (* δ := min δexp δg *)
  set (delta := real_min δexp δg).
  assert (Hd0 : real_lt real_zero delta).
  { unfold delta. apply real_min_pos. { exact Hδe0. } { exact Hδg0. } }
  exists delta. split. { exact Hd0. }
  { intros h Hh eps' Heps'.
  destruct (b5n_eps_proj_lt eps Heps) as [e0 [He0T [Ne0 He0lt]]].
    assert (HhE : real_lt (real_abs h) δexp).
    { apply (real_min_lt_l h δexp δg). unfold delta in Hh. exact Hh. }
    assert (HhG : real_lt (real_abs h) δg).
    { apply (real_min_lt_r h δexp δg). unfold delta in Hh. exact Hh. }
    destruct (b5n_eps_proj_lt eps' Heps') as [e1 [He1T [Ne1 He1lt]]].
    set (eta := Qmult (1 # 8) e1).
    assert (HetaT : QltT 0 eta).
    { unfold eta. apply Qlt_to_QltT. apply (Qmult_lt_0_compat (1 # 8) e1).
      - change (Qlt 0 (1 # 8)). unfold Qlt. simpl. lia.
      - apply QltT_to_Qlt. exact He1T. }
    (* 份额：exp 内层 eps1'、margin shE、g 内层 eps2'、slack m0 *)
    set (eps1' := real_mult eps' (real_const (1 # 4))).
    assert (Heps1' : real_lt real_zero eps1').
    { unfold eps1'. apply real_mult_positive. { exact Heps'. } { apply real_const_pos. exact H4T. } }
    set (shE := real_mult eps' (real_const (1 # 16))).
    assert (HshE : real_lt real_zero shE).
    { unfold shE. apply real_mult_positive. { exact Heps'. } { apply real_const_pos. exact H16T. } }
    set (eps2' := real_mult eps' (real_const (1 # 8))).
    assert (Heps2' : real_lt real_zero eps2').
    { unfold eps2'. apply real_mult_positive. { exact Heps'. } { apply real_const_pos. exact H8T. } }
    set (m0 := Qmult (1 # 32) e1).
    assert (Hm0T : QltT 0 m0).
    { unfold m0. apply Qlt_to_QltT. apply (Qmult_lt_0_compat (1 # 32) e1).
      - change (Qlt 0 (1 # 32)). unfold Qlt. simpl. lia.
      - apply QltT_to_Qlt. exact He1T. }
    (* 误差对象（与 b5f_S_err_decomp 语句逐字一致） *)
    set (err := real_plus (b5a_S (real_plus x h))
                 (real_opp (real_plus (b5a_S x)
                            (real_mult (real_mult x (b5a_S x)) (real_mult (b5a_atan_d x) h))))).
    set (Eobj := real_mult (b5a_S x)
                  (real_plus (cauchy_real_exp (b5f_v x h))
                             (real_opp (real_plus real_one (b5f_v x h))))).
    set (wS := real_plus (b5f_v x h)
                         (real_opp (real_mult (real_mult x (b5a_atan_d x)) h))).
    set (Gob := real_mult (b5a_S x) wS).
    (* exp 部 real-le 实例化（item3e 主件内层 eps' 份额） *)
    set (Bexp := real_plus (real_mult eps1 (real_abs h)) eps1').
    assert (Hexp_le : real_le (real_abs Eobj) Bexp).
    { unfold Eobj, Bexp. exact (Hδe h HhE eps1' Heps1'). }
    destruct (b5i_abs_le_pointwise Eobj Bexp Hexp_le shE HshE) as [NE HNE].
    (* g 部逐点（gdiff 内层 eps' 份额） *)
    destruct (Hδg h HhG eps2' Heps2') as [Ng HNg].
    (* 分解 slack：real_eq err (Eobj + Gob) *)
    destruct (b5l_eq_abs_tri err Eobj Gob m0 (b5f_S_err_decomp x h) Hm0T) as [Ntri Htri].
    (* real_le 左支 real_lt，见证 eta *)
    left.
    exists eta.
    split.
    { exact HetaT. }
    { set (Nmax := Nat.max NM (Nat.max Ne0 (Nat.max Ne1 (Nat.max NE (Nat.max Ng Ntri))))).
      exists Nmax.
      intros n Hn.
      apply NatLe_drop in Hn.
      set (en := projT1 eps n).
      set (en' := projT1 eps' n).
      set (hn := Qabs (projT1 h n)).
      set (Dn := Qabs (projT1 err n)).
      assert (HnNe0 : NatLe Ne0 n) by (apply NatLe_lift; lia).
      assert (HnNe1 : NatLe Ne1 n) by (apply NatLe_lift; lia).
      assert (HnNE : NatLe NE n) by (apply NatLe_lift; lia).
      assert (HnNg : NatLe Ng n) by (apply NatLe_lift; lia).
      assert (HnNtri : NatLe Ntri n) by (apply NatLe_lift; lia).
      assert (HnNM : (NM <= n)%nat) by lia.
      (* 非负事实 *)
      assert (Hen0 : Qle 0 en).
      { unfold en. apply (Qle_trans 0 e0 (projT1 eps n)).
        - apply Qlt_le_weak. apply QltT_to_Qlt. exact He0T.
        - apply Qlt_le_weak. exact (He0lt n HnNe0). }
      assert (Hen'0 : Qle 0 en').
      { unfold en'. apply (Qle_trans 0 e1 (projT1 eps' n)).
        - apply Qlt_le_weak. apply QltT_to_Qlt. exact He1T.
        - apply Qlt_le_weak. exact (He1lt n HnNe1). }
      assert (Hhn0 : Qle 0 hn). { unfold hn. apply Qabs_nonneg. }
      assert (Hm0le : Qle m0 (Qmult (1 # 32) en')).
      { unfold m0, en'. apply (sc_qmult_le_l e1 (projT1 eps' n) (1 # 32)).
        - apply Qlt_le_weak. exact (He1lt n HnNe1).
        - change (Qle 0 (1 # 32)). unfold Qle. simpl. lia. }
      (* exp 部逐点界：|Eobj_n| ≤ Eexpn *)
      set (Eexpn := Qplus (Qmult (Qmult en (1 # 2)) hn)
                          (Qplus (Qmult en' (1 # 4)) (Qmult en' (1 # 16)))).
      assert (HexpB : Qle (Qabs (projT1 Eobj n)) Eexpn).
      { apply (Qle_trans (Qabs (projT1 Eobj n))
                         (Qplus (projT1 Bexp n) (projT1 shE n))
                         Eexpn).
        - exact (HNE n HnNE).
        - apply qeq_imp_qle.
          assert (Hp1 : projT1 eps1 n == Qmult (projT1 eps n) (1 # 2)).
          { unfold eps1. setoid_rewrite (real_mult_proj eps (real_const (1 # 2)) n).
            rewrite (real_const_proj (1 # 2) n). reflexivity. }
          assert (Hp1' : projT1 eps1' n == Qmult (projT1 eps' n) (1 # 4)).
          { unfold eps1'. setoid_rewrite (real_mult_proj eps' (real_const (1 # 4)) n).
            rewrite (real_const_proj (1 # 4) n). reflexivity. }
          assert (Hpsh : projT1 shE n == Qmult (projT1 eps' n) (1 # 16)).
          { unfold shE. setoid_rewrite (real_mult_proj eps' (real_const (1 # 16)) n).
            rewrite (real_const_proj (1 # 16) n). reflexivity. }
          assert (Hqh : projT1 (real_abs h) n == Qabs (projT1 h n)).
          { apply real_abs_proj. }
          unfold Eexpn, Bexp, en, en', hn.
          setoid_rewrite (real_plus_proj (real_mult eps1 (real_abs h)) eps1' n).
          setoid_rewrite (real_mult_proj eps1 (real_abs h) n).
          setoid_rewrite Hp1.
          setoid_rewrite Hqh.
          setoid_rewrite Hp1'.
          setoid_rewrite Hpsh.
          ring. }
      (* g 部逐点界：|Gob_n| ≤ (1#32)·(en·hn) + (1#32)·en' *)
      assert (HgB : Qle (Qabs (projT1 Gob n))
                        (Qplus (Qmult (1 # 32) (Qmult en hn)) (Qmult (1 # 32) en'))).
      { (* |Gob_n| ≤ M·|wS_n|（|S_n| ≤ M） *)
        assert (H1 : Qle (Qabs (projT1 Gob n)) (Qmult M (Qabs (projT1 wS n)))).
        { unfold Gob, wS. apply (b5l_Sx_mult_abs_le x wS M n). exact (HMall n HnNM). }
        (* |wS_n| ≤ en·(1#4)·k2·hn + 2k2p·(1#8)·en'（gdiff 逐点 + 投影） *)
        assert (H2 : Qle (Qabs (projT1 wS n))
                         (Qplus (Qmult (Qmult (Qmult en (1 # 4)) k2) hn)
                                (Qmult (Qmult (Qmult 2 k2p) (1 # 8)) en'))).
        { apply (Qle_trans (Qabs (projT1 wS n))
                           (Qplus (Qmult (Qmult (projT1 eps2 n) k2) (Qabs (projT1 h n)))
                                  (Qmult (Qmult 2 k2p) (projT1 eps2' n)))
                           (Qplus (Qmult (Qmult (Qmult en (1 # 4)) k2) hn)
                                  (Qmult (Qmult (Qmult 2 k2p) (1 # 8)) en'))).
          - exact (HNg n HnNg).
          - apply qeq_imp_qle.
            unfold eps2, eps2', en, en', hn.
            setoid_rewrite (real_mult_proj eps (real_const (1 # 4)) n).
            rewrite (real_const_proj (1 # 4) n).
            setoid_rewrite (real_mult_proj eps' (real_const (1 # 8)) n).
            rewrite (real_const_proj (1 # 8) n).
            ring. }
        (* M·|wS_n| ≤ M·(A1+A2) = M·A1 + M·A2 *)
        assert (H3 : Qle (Qmult M (Qabs (projT1 wS n)))
                         (Qplus (Qmult M (Qmult (Qmult (Qmult en (1 # 4)) k2) hn))
                                (Qmult M (Qmult (Qmult (Qmult 2 k2p) (1 # 8)) en')))).
        { apply (Qle_trans (Qmult M (Qabs (projT1 wS n)))
                           (Qmult M (Qplus (Qmult (Qmult (Qmult en (1 # 4)) k2) hn)
                                           (Qmult (Qmult (Qmult 2 k2p) (1 # 8)) en')))
                           (Qplus (Qmult M (Qmult (Qmult (Qmult en (1 # 4)) k2) hn))
                                  (Qmult M (Qmult (Qmult (Qmult 2 k2p) (1 # 8)) en')))).
          - apply (sc_qmult_le_l (Qabs (projT1 wS n))
                                 (Qplus (Qmult (Qmult (Qmult en (1 # 4)) k2) hn)
                                        (Qmult (Qmult (Qmult 2 k2p) (1 # 8)) en'))
                                 M).
            + exact H2.
            + exact HM0.
          - apply qeq_imp_qle. ring. }
        (* M·A1 ≤ (1#32)·(en·hn)（coefS1 吸收） *)
        assert (H4 : Qle (Qmult M (Qmult (Qmult (Qmult en (1 # 4)) k2) hn))
                         (Qmult (1 # 32) (Qmult en hn))).
        { apply (Qle_trans (Qmult M (Qmult (Qmult (Qmult en (1 # 4)) k2) hn))
                           (Qmult (Qmult (Qmult M k2) (1 # 4)) (Qmult en hn))
                           (Qmult (1 # 32) (Qmult en hn))).
          - apply qeq_imp_qle. ring.
          - apply (Qmult_le_compat_r (Qmult (Qmult M k2) (1 # 4)) (1 # 32) (Qmult en hn)).
            + exact HcoefS1.
            + apply (Qmult_le_0_compat en hn Hen0 Hhn0). }
        (* M·A2 ≤ (1#32)·en'（coefG1 吸收） *)
        assert (H5 : Qle (Qmult M (Qmult (Qmult (Qmult 2 k2p) (1 # 8)) en'))
                         (Qmult (1 # 32) en')).
        { apply (Qle_trans (Qmult M (Qmult (Qmult (Qmult 2 k2p) (1 # 8)) en'))
                           (Qmult (Qmult (Qmult M (Qmult 2 k2p)) (1 # 8)) en')
                           (Qmult (1 # 32) en')).
          - apply qeq_imp_qle. ring.
          - apply (Qmult_le_compat_r (Qmult (Qmult M (Qmult 2 k2p)) (1 # 8)) (1 # 32) en').
            + exact HcoefG1.
            + exact Hen'0. }
        (* 组装 *)
        apply (Qle_trans (Qabs (projT1 Gob n))
                         (Qmult M (Qabs (projT1 wS n)))
                         (Qplus (Qmult (1 # 32) (Qmult en hn)) (Qmult (1 # 32) en'))).
        - exact H1.
        - apply (Qle_trans (Qmult M (Qabs (projT1 wS n)))
                           (Qplus (Qmult M (Qmult (Qmult (Qmult en (1 # 4)) k2) hn))
                                  (Qmult M (Qmult (Qmult (Qmult 2 k2p) (1 # 8)) en')))
                           (Qplus (Qmult (1 # 32) (Qmult en hn)) (Qmult (1 # 32) en'))).
          + exact H3.
          + apply Qplus_le_compat. { exact H4. } { exact H5. } }
      (* 分解：|err_n| ≤ |Eobj_n| + (|Gob_n| + m0) *)
      assert (HtriB : Qle Dn (Qplus (Qabs (projT1 Eobj n)) (Qplus (Qabs (projT1 Gob n)) m0))).
      { unfold Dn. exact (Htri n HnNtri). }
      (* 汇总 → 吸收 → 线性 nra 证毕 *)
      assert (Hmain : Qle Dn (Qplus (Qmult en hn) (Qmult (3 # 4) en'))).
      { apply (Qle_trans Dn
                         (Qplus Eexpn (Qplus (Qplus (Qmult (1 # 32) (Qmult en hn))
                                                    (Qmult (1 # 32) en'))
                                             m0))
                         (Qplus (Qmult en hn) (Qmult (3 # 4) en'))).
        - apply (Qle_trans Dn
                           (Qplus (Qabs (projT1 Eobj n)) (Qplus (Qabs (projT1 Gob n)) m0))
                           (Qplus Eexpn (Qplus (Qplus (Qmult (1 # 32) (Qmult en hn))
                                                      (Qmult (1 # 32) en'))
                                               m0))).
          + exact HtriB.
          + apply Qplus_le_compat.
            * exact HexpB.
            * apply Qplus_le_compat. { exact HgB. } { apply Qle_refl. }
        - unfold Eexpn.
          nra. }
      (* margin：eta < (1#4)·en'；经 b5n_close *)
      assert (Hq4e : Qlt eta (Qmult (1 # 4) en')).
      { unfold eta, en'. apply (b5n_quarter_gt e1 (projT1 eps' n)).
        - apply QltT_to_Qlt. exact He1T.
        - exact (He1lt n HnNe1). }
      assert (Hfin : Qlt eta (Qminus (Qplus (Qmult en hn) en') Dn)).
      { apply (b5n_close Dn hn en en' eta).
        - unfold Dn. exact Hmain.
        - unfold en'. exact Hq4e. }
      apply Qlt_to_QltT.
      apply (Qlt_le_trans eta
             (Qminus (Qplus (Qmult en hn) en') Dn)
             (Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                     (projT1 (real_abs err) n))).
      - exact Hfin.
      - apply qeq_imp_qle. apply Qeq_sym.
        setoid_rewrite (real_plus_proj (real_mult eps (real_abs h)) eps' n).
        setoid_rewrite (real_mult_proj eps (real_abs h) n).
        setoid_rewrite (real_abs_proj h n).
        setoid_rewrite (real_abs_proj err n).
        unfold en, en', hn, Dn.
        ring. } }
Defined.
(* ============================================================ *)
(* 段 B：主件 b5dP_J_deriv_zero_exp_tail（J-mod 尾形件，        *)
(*   Defined 预置）                                             *)
(*   拷贝源 = sc2_b5a_item25.v 主件区 L87–794（机器抽取，零     *)
(*   手抄；其自身 = item11 C5 机拷 + item25 改动 S1–S8——已含   *)
(*   E-diff 叶换源 b5dI_（item19，C4 束 = item7                  *)
(*   b5d3_exp_arch4_C 族直供）/S-diff 叶换源 b5dN_（item24）/   *)
(*   见证换源 b5dM_（item23）/eps 见证下移（spine-clean）/      *)
(*   Qed→Defined；本件在其终态文本之上做尾形增量改动）。         *)
(*   改动 B1–B6（设计 §2.2 表尾形部分）：语句 HMall 前提行尾形  *)
(*   化 + (NA NM : nat)；intros 扩名；S-diff 叶引用 ×2 改指本    *)
(*   文件段 A 件名 + 束实参插 NM；Nmax 并入 NM；取用点守卫 +     *)
(*   per-n 断言；收尾 Defined（源已 Defined）。E-diff 叶         *)
(*   （b5dI_）与其余 S1–S8 产物不动；HNA 原尾形前提保留。        *)
(*   语句类型除 B2/B3 改动行 = item11 C5 逐字（下游 item27       *)
(*   接口契约）。                                               *)
(* ============================================================ *)
Lemma b5dP_J_deriv_zero_exp_tail :
  forall (r : Q) (Hr0 : Qle 0 r) (Hr1 : Qlt r 1),
  forall (cA M Ms Mc : Q)
         (HcA : Qlt 0 cA) (HM : Qlt 0 M)
         (HMs : QltT 0 Ms) (HMc : QltT 0 Mc),
  forall (x : Real) (Hxr : forall n : nat, QleT' (Qabs (projT1 x n)) r),
  forall (NA NM : nat),
  (forall n : nat, (NA <= n)%nat -> Qle cA (projT1 (b5a_S x) n)) ->
  (forall n : nat, (NM <= n)%nat -> Qle (Qabs (projT1 (b5a_S x) n)) M) ->
  (forall n : nat,
     Qle (Qabs (sin_partial n (arctan_partial n (projT1 x n)))) Ms) ->
  (forall n : nat,
     Qle (Qabs (cos_partial n (arctan_partial n (projT1 x n)))) Mc) ->
  forall (eps : Real), real_lt real_zero eps ->
  sigT (fun delta : Real => And (real_lt real_zero delta)
    (forall (h : Real), real_lt (real_abs h) delta ->
      forall (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1),
      forall (eps' : Real), real_lt real_zero eps' ->
      real_le (real_abs (real_plus (b5c_J (real_plus x h) Hxh)
                 (real_opp (b5c_J x (b3rr_dom_r1 x r Hxr Hr1)))))
              (real_plus (real_mult eps (real_abs h)) eps'))).
Proof.
  intros r Hr0 Hr1 cA M Ms Mc HcA HM HMs HMc x Hxr NA NM HNA HMall HMs_all HMc_all eps Heps.
  set (Hx := b3rr_dom_r1 x r Hxr Hr1).
  (* ---- 固定数据 ---- *)
  (* cA：S(x) 逐点正下界——语句显式 Q 参数 cA/HcA + NA 尾界前提 HNA； *)
  (* δ-C C5：4 处黑盒 destruct（源 L389/396/399/400）→ intros 参数束 *)
  set (cB := Qmult cA (1 # 2)).
  assert (HcB : Qlt 0 cB).
  { unfold cB. apply (Qmult_lt_0_compat cA (1 # 2)).
    - exact HcA.
    - change (Qlt 0 (1 # 2)). unfold Qlt. simpl. lia. }
  (* M/Ms/Mc：语句显式 Q 参数；全 n 前提 HMall/HMs_all/HMc_all 直接应用 *)
  assert (HM0 : Qle 0 M). { apply Qlt_le_weak. exact HM. }
  (* Ms/Mc：sinA/cosA 逐点界 ⟹ ME := Ms + r·Mc（|E(x)_n| ≤ ME）     *)
  assert (HMs0 : Qle 0 Ms). { apply Qlt_le_weak. apply QltT_to_Qlt. exact HMs. }
  assert (HMc0 : Qle 0 Mc). { apply Qlt_le_weak. apply QltT_to_Qlt. exact HMc. }
  (* E/S-diff 换源证书（item25 改动 S3：b5dI_E_diff_closed_r_exp 束参数——
     QltT_to_Qlt 证明侧应用；C4 闭值 = item7 b5d3_exp_arch4_C） *)
  assert (HMsQ : Qlt 0 Ms). { apply QltT_to_Qlt. exact HMs. }
  assert (HMcQ : Qlt 0 Mc). { apply QltT_to_Qlt. exact HMc. }
  assert (HC40C : Qle 0 b5d3_exp_arch4_C).
  { apply (Qle_trans _ 1 _). { exact Qle_0_1. } { apply QleT'_to_Qle. exact b5d3_exp_arch4_C_ge1. } }
  assert (Hr0' : Qle 0 r). { exact Hr0. }
  set (ME := Qplus Ms (Qmult r Mc)).
  assert (HME0 : Qle 0 ME).
  { unfold ME. nra. }
  (* 逆常数与份额（全部只依赖 x 数据；QltT 0 用于 real_const_pos） *)
  set (QicA := Qinv cA).
  set (QicB := Qinv cB).
  set (kE := Qmult cB (1 # 8)).
  set (kEp := Qmult cB (1 # 16)).
  set (kapE := Qmult cB (1 # 16)).
  set (invM1 := Qinv (Qplus ME 1)).
  set (kS := Qmult (Qmult (Qmult cA cB) (1 # 8)) invM1).
  set (kSp := Qmult (Qmult (Qmult cA cB) (1 # 16)) invM1).
  set (kapS := Qmult (Qmult (Qmult cA cB) (1 # 16)) invM1).
  set (K1 := Qplus (Qmult r M) 1).
  set (tau := Qmult cA (Qinv (Qmult 8 K1))).
  set (mu := Qmult cA (1 # 16)).
  set (kapS2 := Qmult cA (1 # 16)).
  (* 正性事实 *)
  assert (HkET : QltT 0 kE).
  { unfold kE. apply Qlt_to_QltT. apply (Qmult_lt_0_compat cB (1 # 8)).
    - exact HcB.
    - change (Qlt 0 (1 # 8)). unfold Qlt. simpl. lia. }
  assert (HkEpT : QltT 0 kEp).
  { unfold kEp. apply Qlt_to_QltT. apply (Qmult_lt_0_compat cB (1 # 16)).
    - exact HcB.
    - change (Qlt 0 (1 # 16)). unfold Qlt. simpl. lia. }
  assert (HkapET : QltT 0 kapE).
  { unfold kapE. apply Qlt_to_QltT. apply (Qmult_lt_0_compat cB (1 # 16)).
    - exact HcB.
    - change (Qlt 0 (1 # 16)). unfold Qlt. simpl. lia. }
  assert (HME1 : Qlt 0 (Qplus ME 1)).
  { nra. }
  assert (HME1ne : ~ Qplus ME 1 == 0).
  { apply q_neq_of_lt. exact HME1. }
  assert (Hinv1T : QltT 0 invM1).
  { unfold invM1. apply Qlt_to_QltT. apply Qinv_lt_0_compat. exact HME1. }
  assert (HcAcB0 : Qlt 0 (Qmult (Qmult cA cB) (1 # 8))).
  { apply (Qmult_lt_0_compat (Qmult cA cB) (1 # 8)).
    - apply (Qmult_lt_0_compat cA cB). { exact HcA. } { exact HcB. }
    - change (Qlt 0 (1 # 8)). unfold Qlt. simpl. lia. }
  assert (HcAcB0b : Qlt 0 (Qmult (Qmult cA cB) (1 # 16))).
  { apply (Qmult_lt_0_compat (Qmult cA cB) (1 # 16)).
    - apply (Qmult_lt_0_compat cA cB). { exact HcA. } { exact HcB. }
    - change (Qlt 0 (1 # 16)). unfold Qlt. simpl. lia. }
  assert (HkST : QltT 0 kS).
  { unfold kS. apply Qlt_to_QltT.
    apply (Qmult_lt_0_compat (Qmult (Qmult cA cB) (1 # 8)) invM1).
    - exact HcAcB0.
    - apply QltT_to_Qlt. exact Hinv1T. }
  assert (HkSpT : QltT 0 kSp).
  { unfold kSp. apply Qlt_to_QltT.
    apply (Qmult_lt_0_compat (Qmult (Qmult cA cB) (1 # 16)) invM1).
    - exact HcAcB0b.
    - apply QltT_to_Qlt. exact Hinv1T. }
  assert (HkapST : QltT 0 kapS).
  { unfold kapS. apply Qlt_to_QltT.
    apply (Qmult_lt_0_compat (Qmult (Qmult cA cB) (1 # 16)) invM1).
    - exact HcAcB0b.
    - apply QltT_to_Qlt. exact Hinv1T. }
  assert (HK1 : Qlt 0 K1).
  { unfold K1. nra. }
  assert (HtauT : QltT 0 tau).
  { unfold tau. apply Qlt_to_QltT.
    apply (Qmult_lt_0_compat cA (Qinv (Qmult 8 K1))).
    - exact HcA.
    - apply Qinv_lt_0_compat. nra. }
  assert (HmuT : QltT 0 mu).
  { unfold mu. apply Qlt_to_QltT. apply (Qmult_lt_0_compat cA (1 # 16)).
    - exact HcA.
    - change (Qlt 0 (1 # 16)). unfold Qlt. simpl. lia. }
  assert (HkapS2T : QltT 0 kapS2).
  { unfold kapS2. apply Qlt_to_QltT. apply (Qmult_lt_0_compat cA (1 # 16)).
    - exact HcA.
    - change (Qlt 0 (1 # 16)). unfold Qlt. simpl. lia. }
  assert (H1T : QltT 0 1) by (apply Qlt_to_QltT; change (Qlt 0 1); unfold Qlt; simpl; lia).
  assert (HcA0 : Qle 0 cA). { apply Qlt_le_weak. exact HcA. }
  assert (HcB0 : Qle 0 cB). { apply Qlt_le_weak. exact HcB. }
  assert (HcAne : ~ cA == 0). { apply q_neq_of_lt. exact HcA. }
  assert (HcBne : ~ cB == 0). { apply q_neq_of_lt. exact HcB. }
  assert (H8K1ne : ~ Qmult 8 K1 == 0).
  { apply q_neq_of_lt. nra. }
  assert (HK1ne : ~ K1 == 0).
  { apply q_neq_of_lt. exact HK1. }
  (* ---- 系数预算事实（Q 层固定，供逐点吸收） ---- *)
  (* Hc1：QicB·kE == 1/8；Hc2：QicB·(kEp+kapE) == 1/8 *)
  assert (Hc1 : Qle (Qmult QicB kE) (1 # 8)).
  { apply qeq_imp_qle.
    unfold QicB, kE.
    field. exact HcBne. }
  assert (Hc1' : Qle (Qmult QicB (Qplus kEp kapE)) (1 # 8)).
  { apply qeq_imp_qle.
    unfold QicB, kEp, kapE.
    field. exact HcBne. }
  (* Hc2/Hc2'：ME·QicA·QicB·kS ≤ 1/8、ME·QicA·QicB·(kSp+kapS) ≤ 1/8 *)
  set (Mterm := Qmult ME (Qmult QicA QicB)).
  assert (Hc2 : Qle (Qmult Mterm kS) (1 # 8)).
  { apply (Qle_trans (Qmult Mterm kS)
                     (Qmult (Qmult ME (1 # 8)) (Qinv (Qplus ME 1)))
                     (1 # 8)).
    - apply qeq_imp_qle.
      unfold Mterm, QicA, QicB, kS, invM1.
      field. all: repeat split; assumption.
    - apply (Qle_trans (Qmult (Qmult ME (1 # 8)) (Qinv (Qplus ME 1)))
                       (Qinv 8)
                       (1 # 8)).
      + apply (b5n_xinv_le (Qmult ME (1 # 8)) (Qplus ME 1) 8).
        * exact HME1.
        * change (Qlt 0 8). unfold Qlt. simpl. lia.
        * nra.
      + apply qeq_imp_qle. unfold Qinv. reflexivity. }
  assert (Hc2' : Qle (Qmult Mterm (Qplus kSp kapS)) (1 # 8)).
  { apply (Qle_trans (Qmult Mterm (Qplus kSp kapS))
                     (Qmult (Qmult ME (1 # 8)) (Qinv (Qplus ME 1)))
                     (1 # 8)).
    - apply qeq_imp_qle.
      unfold Mterm, QicA, QicB, kSp, kapS, invM1.
      field. all: repeat split; assumption.
    - apply (Qle_trans (Qmult (Qmult ME (1 # 8)) (Qinv (Qplus ME 1)))
                       (Qinv 8)
                       (1 # 8)).
      + apply (b5n_xinv_le (Qmult ME (1 # 8)) (Qplus ME 1) 8).
        * exact HME1.
        * change (Qlt 0 8). unfold Qlt. simpl. lia.
        * nra.
      + apply qeq_imp_qle. unfold Qinv. reflexivity. }
  (* 下界不等式：(K1·τ) + μ + kapS2 ≤ cA − cB（== cA/2，LHS == cA/4） *)
  assert (Htau_eq : Qle (Qmult K1 tau) (Qmult cA (1 # 8))).
  { apply qeq_imp_qle.
    unfold tau.
    field. all: repeat split; assumption. }
  assert (Hlb_ineq : Qle (Qplus (Qmult K1 tau) (Qplus mu kapS2)) (Qminus cA cB)).
  { apply (Qle_trans (Qplus (Qmult K1 tau) (Qplus mu kapS2))
                     (Qplus (Qmult cA (1 # 8)) (Qmult cA (1 # 8)))
                     (Qminus cA cB)).
    - apply Qplus_le_compat.
      + apply (Qle_trans (Qmult K1 tau) (Qmult cA (1 # 8)) (Qmult cA (1 # 8))).
        * exact Htau_eq.
        * apply Qle_refl.
      + apply (Qle_trans (Qplus mu kapS2) (Qmult cA (1 # 8)) (Qmult cA (1 # 8))).
        * apply qeq_imp_qle. unfold mu, kapS2. ring.
        * apply Qle_refl.
    - unfold cB. nra. }
  (* ---- eps 见证与份额 ---- *)
  assert (H2T : QltT 0 (1 # 2)) by (apply Qlt_to_QltT; change (Qlt 0 (1 # 2)); unfold Qlt; simpl; lia).
  assert (H4T : QltT 0 (1 # 4)) by (apply Qlt_to_QltT; change (Qlt 0 (1 # 4)); unfold Qlt; simpl; lia).
  assert (H8T : QltT 0 (1 # 8)) by (apply Qlt_to_QltT; change (Qlt 0 (1 # 8)); unfold Qlt; simpl; lia).
  assert (H16T : QltT 0 (1 # 16)) by (apply Qlt_to_QltT; change (Qlt 0 (1 # 16)); unfold Qlt; simpl; lia).
  (* eps 份额（Real）：epsE / epsS（E-diff 与 S-diff 主实例的斜率份额） *)
  set (epsE := real_mult eps (real_const kE)).
  assert (HepsE : real_lt real_zero epsE).
  { unfold epsE. apply b5dI_real_mult_positive_exp. { exact Heps. } { apply b5dM_real_const_pos. exact HkET. } }
  set (epsS := real_mult eps (real_const kS)).
  assert (HepsS : real_lt real_zero epsS).
  { unfold epsS. apply b5dI_real_mult_positive_exp. { exact Heps. } { apply b5dM_real_const_pos. exact HkST. } }
  (* 闭式实例化：δE（E-diff）、δS1/δS2（S-diff 主/常份额） *)
  destruct (b5dI_E_diff_closed_r_exp r Hr0 Hr1 x Hxr
             Ms Mc b5d3_exp_arch4_C HMsQ HMcQ HC40C
             b5d3_exp_arch4_C_ge1 b5d3_exp_arch4_C_all
             HMs_all HMc_all epsE HepsE) as [δE [HδE0 HδE]].
  destruct (b5dP_S_diff_closed_r_M_exp_tail r Hr0 Hr1 x Hxr M HM NM HMall epsS HepsS) as [δS1 [HδS10 HδS1]].
  destruct (b5dP_S_diff_closed_r_M_exp_tail r Hr0 Hr1 x Hxr M HM NM HMall (real_const 1) (b5dM_real_const_pos 1 H1T))
    as [δS2 [HδS20 HδS2]].
  (* δ := min(min(min(δE, δS1), δS2), real_const τ) *)
  set (delta := real_min (real_min (real_min δE δS1) δS2) (real_const tau)).
  assert (Hdpos : real_lt real_zero delta).
  { unfold delta.
    apply real_min_pos.
    { apply real_min_pos.
      { apply real_min_pos. { exact HδE0. } { exact HδS10. } }
      { exact HδS20. } }
    { apply real_const_pos. exact HtauT. } }
  exists delta.
  split.
  { exact Hdpos. }
  { intros h Hh Hxh eps' Heps'.
    (* eps 见证分解（item25 改动 S4：自 item11 L244 下移——spine-clean：
       e0/He0T/Ne0/He0lt 不进 δ 值；换源 b5dM_b5n_eps_proj_lt） *)
    destruct (b5dM_b5n_eps_proj_lt eps Heps) as [e0 [He0T [Ne0 He0lt]]].
    (* 提取 |h| < 分量 *)
    assert (Hh1 : real_lt (real_abs h) (real_min (real_min δE δS1) δS2)).
    { apply (real_min_lt_l h (real_min (real_min δE δS1) δS2) (real_const tau)).
      unfold delta in Hh. exact Hh. }
    assert (Hhτ : real_lt (real_abs h) (real_const tau)).
    { apply (real_min_lt_r h (real_min (real_min δE δS1) δS2) (real_const tau)).
      unfold delta in Hh. exact Hh. }
    assert (Hh2 : real_lt (real_abs h) (real_min δE δS1)).
    { apply (real_min_lt_l h (real_min δE δS1) δS2). exact Hh1. }
    assert (HhS2 : real_lt (real_abs h) δS2).
    { apply (real_min_lt_r h (real_min δE δS1) δS2). exact Hh1. }
    assert (HhE : real_lt (real_abs h) δE).
    { apply (real_min_lt_l h δE δS1). exact Hh2. }
    assert (HhS1 : real_lt (real_abs h) δS1).
    { apply (real_min_lt_r h δE δS1). exact Hh2. }
    destruct (b5dM_b5n_eps_proj_lt eps' Heps') as [e1 [He1T [Ne1 He1lt]]].
    set (eta := Qmult (1 # 8) e1).
    assert (HetaT : QltT 0 eta).
    { unfold eta. apply Qlt_to_QltT.
      apply (Qmult_lt_0_compat (1 # 8) e1).
      - change (Qlt 0 (1 # 8)). unfold Qlt. simpl. lia.
      - apply QltT_to_Qlt. exact He1T. }
    (* eps' 份额（Real）：E-diff epsE'/margin shE、S-diff epsS'/margin shS *)
    set (epsE' := real_mult eps' (real_const kEp)).
    assert (HepsE' : real_lt real_zero epsE').
    { unfold epsE'. apply real_mult_positive. { exact Heps'. } { apply real_const_pos. exact HkEpT. } }
    set (shE := real_mult eps' (real_const kapE)).
    assert (HshE : real_lt real_zero shE).
    { unfold shE. apply real_mult_positive. { exact Heps'. } { apply real_const_pos. exact HkapET. } }
    set (epsS' := real_mult eps' (real_const kSp)).
    assert (HepsS' : real_lt real_zero epsS').
    { unfold epsS'. apply real_mult_positive. { exact Heps'. } { apply real_const_pos. exact HkSpT. } }
    set (shS := real_mult eps' (real_const kapS)).
    assert (HshS : real_lt real_zero shS).
    { unfold shS. apply real_mult_positive. { exact Heps'. } { apply real_const_pos. exact HkapST. } }
    (* 下界实例的常份额（Real，不依赖 eps'） *)
    assert (Hcμ : real_lt real_zero (real_const mu)).
    { apply real_const_pos. exact HmuT. }
    assert (HcκS2 : real_lt real_zero (real_const kapS2)).
    { apply real_const_pos. exact HkapS2T. }
    (* 逐点转换（real_le → per-n，margin 松弛） *)
    set (BE := real_plus (real_mult epsE (real_abs h)) epsE').
    destruct (b5i_abs_le_pointwise (b5e_E_err x Hx h Hxh) BE
               (HδE h HhE Hxh epsE' HepsE') shE HshE) as [NE HNE].
    set (BS1 := real_plus (real_mult epsS (real_abs h)) epsS').
    destruct (b5i_abs_le_pointwise (b5m_rS x h) BS1
               (HδS1 h HhS1 epsS' HepsS') shS HshS) as [NS HNS].
    set (BS2 := real_plus (real_mult (real_const 1) (real_abs h)) (real_const mu)).
    destruct (b5i_abs_le_pointwise (b5m_rS x h) BS2
               (HδS2 h HhS2 (real_const mu) Hcμ) (real_const kapS2) HcκS2) as [NS2 HNS2].
    (* |h_n| ≤ tau（b5i_h_le_const）、|d_n| ≤ 1 尾、逐点恒等 N *)
    destruct (b5i_h_le_const h tau Hhτ HtauT) as [Nτ HNτ].
    destruct (b5dM_b5c_d_proj_le_one x) as [Nd Hd].
    destruct (b5m_J_dec_proj x h Hx Hxh) as [Ndec HNdec].
    (* 逐点预算（对 eps/eps' 见证） *)
    assert (Hen'g : forall n : nat, NatLe Ne1 n -> Qle 0 (projT1 eps' n)).
    { intros n Hn.
      apply (Qle_trans 0 e1 (projT1 eps' n)).
      { apply Qlt_le_weak. apply QltT_to_Qlt. exact He1T. }
      { apply Qlt_le_weak. exact (He1lt n Hn). } }
    set (Nmax := Nat.max NM (Nat.max (Nat.max Ne0 Ne1)
                 (Nat.max (Nat.max Ndec Nτ)
                  (Nat.max (Nat.max NE (Nat.max NS NS2)) (Nat.max NA Nd))))).
    (* 主装配：real_le → real_lt（左支），见证 eta *)
    left.
    exists eta.
    split.
    { exact HetaT. }
    { exists Nmax.
      intros n Hn.
      apply NatLe_drop in Hn.
      set (en := projT1 eps n).
      set (en' := projT1 eps' n).
      set (hn := Qabs (projT1 h n)).
      set (Dn := Qabs (projT1 (b5m_J_err x Hx h Hxh) n)).
      set (Sn := projT1 (b5a_S x) n).
      set (Shn := projT1 (b5a_S (real_plus x h)) n).
      set (dn := projT1 (b5a_atan_d x) n).
      set (rEn := projT1 (b5e_E_err x Hx h Hxh) n).
      set (rSn := projT1 (b5m_rS x h) n).
      set (Exn := projT1 (b5a_E x Hx) n).
      (* 尾指标 *)
      assert (HnNe0 : NatLe Ne0 n) by (apply NatLe_lift; lia).
      assert (HnNe1 : NatLe Ne1 n) by (apply NatLe_lift; lia).
      assert (HnNE : NatLe NE n) by (apply NatLe_lift; lia).
      assert (HnNS : NatLe NS n) by (apply NatLe_lift; lia).
      assert (HnNS2 : NatLe NS2 n) by (apply NatLe_lift; lia).
      assert (HnNτ : NatLe Nτ n) by (apply NatLe_lift; lia).
      assert (HnNd : (Nd <= n)%nat) by lia.
      assert (HnNdec : (Ndec <= n)%nat) by lia.
      assert (HnNA : (NA <= n)%nat) by lia.
      assert (HnNM : (NM <= n)%nat) by lia.
      (* 非负 *)
      assert (Hen0 : Qle 0 en).
      { unfold en. apply (Qle_trans 0 e0 (projT1 eps n)).
        - apply Qlt_le_weak. apply QltT_to_Qlt. exact He0T.
        - apply Qlt_le_weak. exact (He0lt n HnNe0). }
      assert (Hen'0 : Qle 0 en').
      { unfold en'. exact (Hen'g n HnNe1). }
      assert (Hhn0 : Qle 0 hn). { unfold hn. apply Qabs_nonneg. }
      (* |h_n| ≤ tau、|d_n| ≤ 1、Sn ≥ cA *)
      assert (Hhτn : Qle (Qabs (projT1 h n)) tau).
      { unfold tau in *. exact (HNτ n HnNτ). }
      assert (Hdn1 : Qle (Qabs dn) 1).
      { unfold dn. exact (Hd n HnNd). }
      assert (HSnA : Qle cA Sn).
      { unfold Sn. exact (HNA n HnNA). }
      (* |rE_n| ≤ kE·en·hn + (kEp+kapE)·en'（E-diff 逐点化） *)
      assert (HrE : Qle (Qabs rEn)
                        (Qplus (Qmult (Qmult en kE) (Qabs (projT1 h n)))
                               (Qplus (Qmult en' kEp) (Qmult en' kapE)))).
      { apply (Qle_trans (Qabs rEn)
                         (Qplus (projT1 BE n) (projT1 shE n))
                         (Qplus (Qmult (Qmult en kE) (Qabs (projT1 h n)))
                                (Qplus (Qmult en' kEp) (Qmult en' kapE)))).
        - unfold rEn. exact (HNE n HnNE).
        - apply qeq_imp_qle.
          unfold BE, shE, en, en'.
          setoid_rewrite (real_plus_proj (real_mult epsE (real_abs h)) epsE' n).
          setoid_rewrite (real_mult_proj epsE (real_abs h) n).
          unfold epsE, epsE'.
          setoid_rewrite (real_mult_proj eps (real_const kE) n).
          rewrite (real_const_proj kE n).
          setoid_rewrite (real_abs_proj h n).
          setoid_rewrite (real_mult_proj eps' (real_const kEp) n).
          rewrite (real_const_proj kEp n).
          setoid_rewrite (real_mult_proj eps' (real_const kapE) n).
          rewrite (real_const_proj kapE n).
          ring. }
      (* |rS_n| ≤ kS·en·hn + (kSp+kapS)·en'（S-diff 主实例逐点化） *)
      assert (HrS : Qle (Qabs rSn)
                        (Qplus (Qmult (Qmult en kS) (Qabs (projT1 h n)))
                               (Qplus (Qmult en' kSp) (Qmult en' kapS)))).
      { apply (Qle_trans (Qabs rSn)
                         (Qplus (projT1 BS1 n) (projT1 shS n))
                         (Qplus (Qmult (Qmult en kS) (Qabs (projT1 h n)))
                                (Qplus (Qmult en' kSp) (Qmult en' kapS)))).
        - unfold rSn. exact (HNS n HnNS).
        - apply qeq_imp_qle.
          unfold BS1, shS, en, en'.
          setoid_rewrite (real_plus_proj (real_mult epsS (real_abs h)) epsS' n).
          setoid_rewrite (real_mult_proj epsS (real_abs h) n).
          unfold epsS, epsS'.
          setoid_rewrite (real_mult_proj eps (real_const kS) n).
          rewrite (real_const_proj kS n).
          setoid_rewrite (real_abs_proj h n).
          setoid_rewrite (real_mult_proj eps' (real_const kSp) n).
          rewrite (real_const_proj kSp n).
          setoid_rewrite (real_mult_proj eps' (real_const kapS) n).
          rewrite (real_const_proj kapS n).
          ring. }
      (* |rS_n| ≤ 1·hn + mu + kapS2（S-diff 常份额实例逐点化，下界用） *)
      assert (HrS2 : Qle (Qabs rSn)
                         (Qplus (Qabs (projT1 h n)) (Qplus mu kapS2))).
      { apply (Qle_trans (Qabs rSn)
                         (Qplus (projT1 BS2 n) (projT1 (real_const kapS2) n))
                         (Qplus (Qabs (projT1 h n)) (Qplus mu kapS2))).
        - unfold rSn. exact (HNS2 n HnNS2).
        - apply qeq_imp_qle.
          unfold BS2.
          setoid_rewrite (real_plus_proj (real_mult (real_const 1) (real_abs h))
                                         (real_const mu) n).
          setoid_rewrite (real_mult_proj (real_const 1) (real_abs h) n).
          rewrite (real_const_proj 1 n).
          setoid_rewrite (real_abs_proj h n).
          rewrite (real_const_proj mu n).
          rewrite (real_const_proj kapS2 n).
          ring. }
      (* |Ex_n| ≤ ME（sinA/cosA 逐点界 + |x_n| ≤ r；Exn == sAn − xn·cAn） *)
      assert (HEx : Qle (Qabs Exn) ME).
      { unfold Exn, b5a_E.
        rewrite (real_plus_proj (cauchy_real_sin (cauchy_real_arctan x Hx))
                                (real_opp (real_mult x (cauchy_real_cos (cauchy_real_arctan x Hx)))) n).
        rewrite (real_opp_proj (real_mult x (cauchy_real_cos (cauchy_real_arctan x Hx))) n).
        rewrite (real_mult_proj x (cauchy_real_cos (cauchy_real_arctan x Hx)) n).
        apply (Qle_trans
                 (Qabs (Qplus (projT1 (cauchy_real_sin (cauchy_real_arctan x Hx)) n)
                              (Qopp (Qmult (projT1 x n)
                                           (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n)))))
                 (Qplus (Qabs (projT1 (cauchy_real_sin (cauchy_real_arctan x Hx)) n))
                        (Qabs (Qmult (projT1 x n)
                                     (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n))))
                 ME).
        - apply (Qle_trans
                   (Qabs (Qplus (projT1 (cauchy_real_sin (cauchy_real_arctan x Hx)) n)
                                (Qopp (Qmult (projT1 x n)
                                             (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n)))))
                   (Qplus (Qabs (projT1 (cauchy_real_sin (cauchy_real_arctan x Hx)) n))
                          (Qabs (Qopp (Qmult (projT1 x n)
                                             (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n)))))
                   (Qplus (Qabs (projT1 (cauchy_real_sin (cauchy_real_arctan x Hx)) n))
                          (Qabs (Qmult (projT1 x n)
                                       (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n))))).
          + apply Qabs_triangle.
          + apply Qplus_le_compat.
            * apply Qle_refl.
            * apply qeq_imp_qle.
              apply (Qabs_opp (Qmult (projT1 x n)
                                     (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n))).
        - (* |sA| + |x·cA| ≤ Ms + r·Mc ≤ ME *)
          apply (Qle_trans
                   (Qplus (Qabs (projT1 (cauchy_real_sin (cauchy_real_arctan x Hx)) n))
                          (Qabs (Qmult (projT1 x n)
                                       (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n))))
                   (Qplus Ms (Qmult r Mc))
                   ME).
          + apply Qplus_le_compat.
            * apply (Qle_trans (Qabs (projT1 (cauchy_real_sin (cauchy_real_arctan x Hx)) n))
                               (Qabs (sin_partial n (arctan_partial n (projT1 x n))))
                               Ms).
              { apply qeq_imp_qle. apply Qabs_wd. apply Qeq_sym.
                setoid_rewrite (real_sin_proj (cauchy_real_arctan x Hx) n).
                setoid_rewrite (arctan_real_proj x Hx n).
                reflexivity. }
              { exact (HMs_all n). }
            * apply (Qle_trans (Qabs (Qmult (projT1 x n)
                                            (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n)))
                               (Qmult r (Qabs (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n)))
                               (Qmult r Mc)).
              { apply (Qle_trans (Qabs (Qmult (projT1 x n)
                                              (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n)))
                                 (Qmult (Qabs (projT1 x n))
                                        (Qabs (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n)))
                                 (Qmult r (Qabs (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n)))).
                - apply qeq_imp_qle.
                  apply (Qabs_Qmult (projT1 x n)
                                    (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n)).
                - apply (Qmult_le_compat_r (Qabs (projT1 x n)) r
                                           (Qabs (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n))).
                  + apply QleT'_to_Qle. exact (Hxr n).
                  + apply Qabs_nonneg. }
              { apply (sc_qmult_le_l (Qabs (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n))
                                     Mc r).
                - apply (Qle_trans (Qabs (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n))
                                   (Qabs (cos_partial n (arctan_partial n (projT1 x n))))
                                   Mc).
                  + apply qeq_imp_qle. apply Qabs_wd. apply Qeq_sym.
                    setoid_rewrite (real_cos_proj (cauchy_real_arctan x Hx) n).
                    setoid_rewrite (arctan_real_proj x Hx n).
                    reflexivity.
                  + exact (HMc_all n).
                - exact Hr0'. }
          + unfold ME. nra. }
      (* 商分母证书：|Qinv(Sn)| ≤ QicA *)
      assert (HQA : Qle (Qabs (Qinv Sn)) QicA).
      { unfold Sn, QicA. apply (b5m_inv_le Sn cA HcA HSnA). }
      (* Sxh ≥ cB：|ΔS| 界（r·M·hn + |rS|）→ K1·tau + mu + kapS2 ≤ cA − cB *)
      assert (Hdel0 : Qle (Qabs (Qminus Shn Sn))
                          (Qplus (Qmult (Qmult r M) (Qabs (projT1 h n)))
                                 (Qplus (Qabs (projT1 h n)) (Qplus mu kapS2)))).
      { (* Shn − Sn == (x·S·d·h)_n + rS_n *)
        apply (Qle_trans (Qabs (Qminus Shn Sn))
                         (Qplus (Qabs (Qmult (Qmult (projT1 x n) Sn) (Qmult dn (projT1 h n))))
                                (Qabs rSn))
                         (Qplus (Qmult (Qmult r M) (Qabs (projT1 h n)))
                                (Qplus (Qabs (projT1 h n)) (Qplus mu kapS2)))).
        - (* triangle：|Shn − Sn| == |P + rS| ≤ |P| + |rS| *)
          apply (Qle_trans (Qabs (Qminus Shn Sn))
                           (Qabs (Qplus (Qmult (Qmult (projT1 x n) Sn) (Qmult dn (projT1 h n))) rSn))
                           (Qplus (Qabs (Qmult (Qmult (projT1 x n) Sn) (Qmult dn (projT1 h n))))
                                  (Qabs rSn))).
          + apply qeq_imp_qle.
            apply (Qabs_wd (Qminus Shn Sn)
                           (Qplus (Qmult (Qmult (projT1 x n) Sn) (Qmult dn (projT1 h n))) rSn)).
            unfold Shn, Sn, dn, rSn.
            unfold b5m_rS.
            rewrite (real_plus_proj (b5a_S (real_plus x h))
                                    (real_opp (real_plus (b5a_S x)
                                               (real_mult (real_mult x (b5a_S x))
                                                          (real_mult (b5a_atan_d x) h)))) n).
            rewrite (real_opp_proj (real_plus (b5a_S x)
                                    (real_mult (real_mult x (b5a_S x))
                                               (real_mult (b5a_atan_d x) h))) n).
            rewrite (real_plus_proj (b5a_S x)
                                    (real_mult (real_mult x (b5a_S x))
                                               (real_mult (b5a_atan_d x) h)) n).
            rewrite (real_mult_proj (real_mult x (b5a_S x))
                                    (real_mult (b5a_atan_d x) h) n).
            rewrite (real_mult_proj x (b5a_S x) n).
            rewrite (real_mult_proj (b5a_atan_d x) h n).
            cbn [projT1 real_zero].
            ring.
          + apply Qabs_triangle.
        - (* |P| ≤ r·M·1·hn、|rS_n| ≤ hn + mu + kapS2（HrS2） *)
          apply Qplus_le_compat.
          + (* |(x·S·d·h)_n| ≤ r·M·1·hn *)
            apply (Qle_trans (Qabs (Qmult (Qmult (projT1 x n) Sn) (Qmult dn (projT1 h n))))
                             (Qmult (Qmult (Qabs (projT1 x n)) (Qabs Sn)) (Qmult (Qabs dn) (Qabs (projT1 h n))))
                             (Qmult (Qmult r M) (Qabs (projT1 h n)))).
            * apply qeq_imp_qle.
              apply (Qeq_trans (Qabs (Qmult (Qmult (projT1 x n) Sn) (Qmult dn (projT1 h n))))
                               (Qmult (Qabs (Qmult (projT1 x n) Sn)) (Qabs (Qmult dn (projT1 h n))))
                               (Qmult (Qmult (Qabs (projT1 x n)) (Qabs Sn)) (Qmult (Qabs dn) (Qabs (projT1 h n))))).
              { apply (Qabs_Qmult (Qmult (projT1 x n) Sn) (Qmult dn (projT1 h n))). }
              { apply Qmult_comp.
                - apply (Qabs_Qmult (projT1 x n) Sn).
                - apply (Qabs_Qmult dn (projT1 h n)). }
            * (* (|xn|·|Sn|)·(|dn|·|hn|) ≤ (r·M)·(1·hn) *)
              apply (Qle_trans (Qmult (Qmult (Qabs (projT1 x n)) (Qabs Sn)) (Qmult (Qabs dn) (Qabs (projT1 h n))))
                               (Qmult (Qmult r M) (Qmult 1 (Qabs (projT1 h n))))
                               (Qmult (Qmult r M) (Qabs (projT1 h n)))).
              { apply (Qle_trans (Qmult (Qmult (Qabs (projT1 x n)) (Qabs Sn)) (Qmult (Qabs dn) (Qabs (projT1 h n))))
                                 (Qmult (Qmult r M) (Qmult (Qabs dn) (Qabs (projT1 h n))))
                                 (Qmult (Qmult r M) (Qmult 1 (Qabs (projT1 h n))))).
                - apply (Qmult_le_compat_r (Qmult (Qabs (projT1 x n)) (Qabs Sn)) (Qmult r M)
                                           (Qmult (Qabs dn) (Qabs (projT1 h n)))).
                  + apply (Qle_trans (Qmult (Qabs (projT1 x n)) (Qabs Sn))
                                     (Qmult r (Qabs Sn))
                                     (Qmult r M)).
                    * apply (Qmult_le_compat_r (Qabs (projT1 x n)) r (Qabs Sn)).
                      { apply QleT'_to_Qle. exact (Hxr n). }
                      { apply Qabs_nonneg. }
                    * apply (sc_qmult_le_l (Qabs Sn) M r).
                      { unfold Sn. exact (HMall n HnNM). }
                      { exact Hr0'. }
                  + apply Qmult_le_0_compat.
                    * apply Qabs_nonneg.
                    * apply Qabs_nonneg.
                - apply (sc_qmult_le_l (Qmult (Qabs dn) (Qabs (projT1 h n)))
                                       (Qmult 1 (Qabs (projT1 h n)))
                                       (Qmult r M)).
                  + apply (Qmult_le_compat_r (Qabs dn) 1 (Qabs (projT1 h n))).
                    * exact Hdn1.
                    * apply Qabs_nonneg.
                  + apply Qmult_le_0_compat.
                    * exact Hr0'.
                    * exact HM0. }
              { apply qeq_imp_qle. ring. }
          + (* |rS_n| ≤ hn + mu + kapS2 *)
            apply (Qle_trans (Qabs rSn)
                             (Qplus (Qabs (projT1 h n)) (Qplus mu kapS2))
                             (Qplus (Qabs (projT1 h n)) (Qplus mu kapS2))).
            * exact HrS2.
            * apply Qle_refl. }
      (* |ΔS| ≤ K1·tau + mu + kapS2（hn ≤ tau） *)
      assert (Hdel : Qle (Qabs (Qminus Shn Sn))
                         (Qplus (Qmult K1 tau) (Qplus mu kapS2))).
      { apply (Qle_trans (Qabs (Qminus Shn Sn))
                         (Qplus (Qmult (Qmult r M) tau) (Qplus tau (Qplus mu kapS2)))
                         (Qplus (Qmult K1 tau) (Qplus mu kapS2))).
        - apply (Qle_trans (Qabs (Qminus Shn Sn))
                           (Qplus (Qmult (Qmult r M) (Qabs (projT1 h n)))
                                  (Qplus (Qabs (projT1 h n)) (Qplus mu kapS2)))
                           (Qplus (Qmult (Qmult r M) tau) (Qplus tau (Qplus mu kapS2)))).
          + exact Hdel0.
          + apply Qplus_le_compat.
            * apply (sc_qmult_le_l (Qabs (projT1 h n)) tau (Qmult r M)).
              { exact Hhτn. }
              { apply Qmult_le_0_compat. { exact Hr0'. } { exact HM0. } }
            * apply Qplus_le_compat.
              { exact Hhτn. }
              { apply Qle_refl. }
        - apply qeq_imp_qle. unfold K1. ring. }
      (* Shn ≥ cB（Sn ≥ cA、|ΔS| ≤ B0、B0 ≤ cA − cB） *)
      assert (HShnB : Qle cB Shn).
      { (* Sn ≤ Shn + |Δ| 且 |Δ| ≤ B0（Hdel）⟹ Sn ≤ Shn + B0 *)
        assert (HS2 : Qle Sn (Qplus Shn (Qplus (Qmult K1 tau) (Qplus mu kapS2)))).
        { apply (Qle_trans Sn (Qplus Shn (Qabs (Qminus Shn Sn)))
                              (Qplus Shn (Qplus (Qmult K1 tau) (Qplus mu kapS2)))).
          - apply (Qle_trans Sn (Qplus Shn (Qminus Sn Shn))
                                (Qplus Shn (Qabs (Qminus Shn Sn)))).
            + apply qeq_imp_qle. ring.
            + apply Qplus_le_compat.
              * apply Qle_refl.
              * apply (Qle_trans (Qminus Sn Shn) (Qabs (Qminus Sn Shn))
                                 (Qabs (Qminus Shn Sn))).
                { apply Qle_Qabs. }
                { apply qeq_imp_qle.
                  apply (Qeq_trans (Qabs (Qminus Sn Shn))
                                   (Qabs (Qopp (Qminus Shn Sn)))
                                   (Qabs (Qminus Shn Sn))).
                  - apply Qabs_wd. ring.
                  - apply (Qabs_opp (Qminus Shn Sn)). }
          - apply Qplus_le_compat.
            + apply Qle_refl.
            + exact Hdel. }
        (* cB ≤ cA − B0（Hlb_ineq）、cA ≤ Sn（HSnA）、Sn ≤ Shn + B0 ⟹ cB ≤ Shn *)
        nra. }
      (* 商分母证书：|Qinv(Shn)| ≤ QicB *)
      assert (HQB : Qle (Qabs (Qinv Shn)) QicB).
      { unfold Shn, QicB. apply (b5m_inv_le Shn cB HcB HShnB). }
      (* b5m_J_abs_tri 主步 *)
      set (RE := Qplus (Qmult (Qmult en kE) (Qabs (projT1 h n)))
                       (Qplus (Qmult en' kEp) (Qmult en' kapE))).
      set (RS := Qplus (Qmult (Qmult en kS) (Qabs (projT1 h n)))
                       (Qplus (Qmult en' kSp) (Qmult en' kapS))).
      assert (Hmain0 : Qle Dn (Qplus (Qmult QicB RE) (Qmult Mterm RS))).
      { unfold Dn.
        apply (b5m_J_abs_tri x h Hx Hxh n QicA QicB ME RE RS).
        - exact HQA.
        - exact HQB.
        - unfold Exn. exact HEx.
        - unfold rEn. exact HrE.
        - unfold rSn. exact HrS.
        - unfold QicA. apply Qlt_le_weak. apply Qinv_lt_0_compat. exact HcA.
        - unfold QicB. apply Qlt_le_weak. apply Qinv_lt_0_compat. exact HcB.
        - exact (HNdec n HnNdec). }
      (* 系数吸收：QicB·RE ≤ (1/8)·en·hn + (1/8)·en'；Mterm·RS ≤ 同形 *)
      assert (HT1 : Qle (Qmult QicB (Qmult (Qmult en kE) (Qabs (projT1 h n))))
                        (Qmult (1 # 8) (Qmult en hn))).
      { apply (Qle_trans (Qmult QicB (Qmult (Qmult en kE) (Qabs (projT1 h n))))
                         (Qmult (Qmult QicB kE) (Qmult en hn))
                         (Qmult (1 # 8) (Qmult en hn))).
        - apply qeq_imp_qle. unfold hn. ring.
        - apply (Qmult_le_compat_r (Qmult QicB kE) (1 # 8) (Qmult en hn)).
          + exact Hc1.
          + apply Qmult_le_0_compat.
            * exact Hen0.
            * exact Hhn0. }
      assert (HT2 : Qle (Qmult QicB (Qplus (Qmult en' kEp) (Qmult en' kapE)))
                        (Qmult (1 # 8) en')).
      { apply (Qle_trans (Qmult QicB (Qplus (Qmult en' kEp) (Qmult en' kapE)))
                         (Qmult (Qmult QicB (Qplus kEp kapE)) en')
                         (Qmult (1 # 8) en')).
        - apply qeq_imp_qle. ring.
        - apply (Qmult_le_compat_r (Qmult QicB (Qplus kEp kapE)) (1 # 8) en').
          + exact Hc1'.
          + exact Hen'0. }
      assert (HT3 : Qle (Qmult Mterm (Qmult (Qmult en kS) (Qabs (projT1 h n))))
                        (Qmult (1 # 8) (Qmult en hn))).
      { apply (Qle_trans (Qmult Mterm (Qmult (Qmult en kS) (Qabs (projT1 h n))))
                         (Qmult (Qmult Mterm kS) (Qmult en hn))
                         (Qmult (1 # 8) (Qmult en hn))).
        - apply qeq_imp_qle. unfold hn. ring.
        - apply (Qmult_le_compat_r (Qmult Mterm kS) (1 # 8) (Qmult en hn)).
          + exact Hc2.
          + apply Qmult_le_0_compat.
            * exact Hen0.
            * exact Hhn0. }
      assert (HT4 : Qle (Qmult Mterm (Qplus (Qmult en' kSp) (Qmult en' kapS)))
                        (Qmult (1 # 8) en')).
      { apply (Qle_trans (Qmult Mterm (Qplus (Qmult en' kSp) (Qmult en' kapS)))
                         (Qmult (Qmult Mterm (Qplus kSp kapS)) en')
                         (Qmult (1 # 8) en')).
        - apply qeq_imp_qle. ring.
        - apply (Qmult_le_compat_r (Qmult Mterm (Qplus kSp kapS)) (1 # 8) en').
          + exact Hc2'.
          + exact Hen'0. }
      (* 组装逐点主界：|Dn| ≤ en·hn + (3/4)·en' *)
      assert (Hmain : Qle Dn (Qplus (Qmult en hn) (Qmult (3 # 4) en'))).
      { apply (Qle_trans Dn
                         (Qplus (Qmult QicB RE) (Qmult Mterm RS))
                         (Qplus (Qmult en hn) (Qmult (3 # 4) en'))).
        - exact Hmain0.
        - (* 展开并吸收：QicB·RE + Mterm·RS ≤ (1/8)(en hn)+(1/8)en' 各两份 *)
          apply (Qle_trans (Qplus (Qmult QicB RE) (Qmult Mterm RS))
                           (Qplus (Qplus (Qmult QicB (Qmult (Qmult en kE) (Qabs (projT1 h n))))
                                         (Qmult QicB (Qplus (Qmult en' kEp) (Qmult en' kapE))))
                                  (Qplus (Qmult Mterm (Qmult (Qmult en kS) (Qabs (projT1 h n))))
                                         (Qmult Mterm (Qplus (Qmult en' kSp) (Qmult en' kapS)))))
                           (Qplus (Qmult en hn) (Qmult (3 # 4) en'))).
          + apply qeq_imp_qle. unfold RE, RS, hn. ring.
          + apply (Qle_trans
                     (Qplus (Qplus (Qmult QicB (Qmult (Qmult en kE) (Qabs (projT1 h n))))
                                   (Qmult QicB (Qplus (Qmult en' kEp) (Qmult en' kapE))))
                            (Qplus (Qmult Mterm (Qmult (Qmult en kS) (Qabs (projT1 h n))))
                                   (Qmult Mterm (Qplus (Qmult en' kSp) (Qmult en' kapS)))))
                     (Qplus (Qplus (Qmult (1 # 8) (Qmult en hn)) (Qmult (1 # 8) en'))
                            (Qplus (Qmult (1 # 8) (Qmult en hn)) (Qmult (1 # 8) en')))
                     (Qplus (Qmult en hn) (Qmult (3 # 4) en'))).
            * apply Qplus_le_compat.
              { apply Qplus_le_compat. { exact HT1. } { exact HT2. } }
              { apply Qplus_le_compat. { exact HT3. } { exact HT4. } }
            * nra. }
      (* margin：eta < (1/4)·en'；Hfin：eta < (en·hn + en') − Dn *)
      assert (Hq4e : Qlt eta (Qmult (1 # 4) en')).
      { unfold eta, en'. apply (b5n_quarter_gt e1 (projT1 eps' n)).
        - apply QltT_to_Qlt. exact He1T.
        - exact (He1lt n HnNe1). }
      assert (Hfin : Qlt eta (Qminus (Qplus (Qmult en hn) en') Dn)).
      { apply (b5n_close Dn hn en en' eta).
        - unfold Dn. exact Hmain.
        - unfold en'. exact Hq4e. }
      apply Qlt_to_QltT.
      apply (Qlt_le_trans eta
             (Qminus (Qplus (Qmult en hn) en') Dn)
             (Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                     (projT1 (real_abs (b5m_J_err x Hx h Hxh)) n))).
      - exact Hfin.
      - apply qeq_imp_qle. apply Qeq_sym.
        setoid_rewrite (real_plus_proj (real_mult eps (real_abs h)) eps' n).
        setoid_rewrite (real_mult_proj eps (real_abs h) n).
        setoid_rewrite (real_abs_proj h n).
        setoid_rewrite (real_abs_proj (b5m_J_err x Hx h Hxh) n).
        unfold en, en', hn, Dn.
        ring. } }
Defined.
(* ============================================================ *)
(* 完成标记：已编译；kernel 检验 5/5 全部通过（段 A r:=0 1#36864 /  *)
(*    δS1-c 1#5898240 / δS2-c 1#9216 / 主件 X = 49#10896801792 = *)
(*    δE-c——min 链极小者；尾形证书已验证）。                      *)
(* ============================================================ *)

(* ============================================================ *)
(* 块 item27（前缀 b5dQ_——主件 b5dQ_E_rational_zero）——来源：演变/.ablation/sc2_parallel/sc2_b5a_ode/sc2_b5a_item27.v。 *)
(* ============================================================ *)

(* ===== 段 P1（lb-E 链：机制件 + 值定义 vB/vSC/vE + lb_b3rr/atan/vdh/sin_cos/cos/E，29 Lemma + 5 Def）===== *)

(* ============================================================ *)
(* §0 机制件移植（probe_item27a.v 全真 Qed——E 侧）             *)
(* ============================================================ *)

(* T1 移植：real 层 min-lb glue（lb < X 且 lb < Y ⟹ lb < real_min X Y） *)
Lemma b5dQ_min_lb : forall (lb A B : Real),
  real_lt lb A -> real_lt lb B -> real_lt lb (real_min A B).
Proof.
  intros lb A B HltA HltB.
  destruct HltA as [e1 [He1 [N1 HN1]]].
  destruct HltB as [e2 [He2 [N2 HN2]]].
  set (e := Qmin e1 e2).
  assert (He : QltT 0 e).
  { apply Qlt_to_QltT.
    apply Q.min_glb_lt.
    - apply QltT_to_Qlt. exact He1.
    - apply QltT_to_Qlt. exact He2. }
  unfold real_lt.
  exists e.
  split.
  { exact He. }
  { exists (Nat.max N1 N2).
    intros n Hn.
    apply NatLe_drop in Hn.
    assert (Hn1 : NatLe N1 n) by (apply NatLe_lift; lia).
    assert (Hn2 : NatLe N2 n) by (apply NatLe_lift; lia).
    apply Qlt_to_QltT.
    set (cn := projT1 lb n).
    set (an := projT1 A n).
    set (bn := projT1 B n).
    assert (H1n : Qlt e1 (an - cn)).
    { unfold an, cn. apply QltT_to_Qlt. exact (HN1 n Hn1). }
    assert (H2n : Qlt e2 (bn - cn)).
    { unfold bn, cn. apply QltT_to_Qlt. exact (HN2 n Hn2). }
    assert (Hen1 : Qle e e1). { unfold e. apply Q.le_min_l. }
    assert (Hen2 : Qle e e2). { unfold e. apply Q.le_min_r. }
    assert (Hm1 : Qlt e (an - cn)).
    { apply (Qle_lt_trans e e1 (an - cn)); [exact Hen1 | exact H1n]. }
    assert (Hm2 : Qlt e (bn - cn)).
    { apply (Qle_lt_trans e e2 (bn - cn)); [exact Hen2 | exact H2n]. }
    assert (Ht1 : Qlt (e + cn) an).
    { apply (proj2 (Qlt_minus_iff (e + cn) an)).
      apply (Qlt_le_trans 0 ((an - cn) - e) (an - (e + cn))).
      - apply (proj1 (Qlt_minus_iff e (an - cn))). exact Hm1.
      - apply qeq_le. ring. }
    assert (Ht2 : Qlt (e + cn) bn).
    { apply (proj2 (Qlt_minus_iff (e + cn) bn)).
      apply (Qlt_le_trans 0 ((bn - cn) - e) (bn - (e + cn))).
      - apply (proj1 (Qlt_minus_iff e (bn - cn))). exact Hm2.
      - apply qeq_le. ring. }
    assert (Htg : Qlt (e + cn) (Qmin an bn)).
    { apply Q.min_glb_lt; [exact Ht1 | exact Ht2]. }
    rewrite (real_min_proj A B n).
    apply (proj2 (Qlt_minus_iff e (Qmin an bn - cn))).
    apply (Qlt_le_trans 0 (Qmin an bn - (e + cn)) ((Qmin an bn - cn) - e)).
    - apply (proj1 (Qlt_minus_iff (e + cn) (Qmin an bn))). exact Htg.
    - apply qeq_le. ring.
  }
  Qed.

(* T3a 移植：常坐标乘积叶 lb（real_lt (real_const lb) (real_const a · real_const d)） *)
Lemma b5dQ_const_mult_lb : forall (lb a d : Q),
  Qlt lb (a * d) ->
  real_lt (real_const lb) (real_mult (real_const a) (real_const d)).
Proof.
  intros lb a d Hlt.
  assert (Hpos : Qlt 0 ((a * d - lb) / 2)).
  { apply (Qlt_shift_div_l 0 (a * d - lb) 2).
    - change (Qlt 0 2). compute. reflexivity.
    - simpl. apply (proj1 (Qlt_minus_iff lb (a * d))). exact Hlt. }
  unfold real_lt.
  exists ((a * d - lb) / 2).
  split.
  - apply Qlt_to_QltT. exact Hpos.
  - exists 0%nat.
    intros n Hn.
    apply Qlt_to_QltT.
    apply (Qlt_le_trans _ (a * d - lb) _).
    + apply (proj2 (Qlt_minus_iff ((a * d - lb) / 2) (a * d - lb))).
      apply (Qlt_le_trans 0 ((a * d - lb) / 2) (a * d - lb - (a * d - lb) / 2)).
      * exact Hpos.
      * apply qeq_le. field.
    + apply qeq_le.
      rewrite (real_mult_proj (real_const a) (real_const d) n).
      rewrite (real_const_proj a n).
      rewrite (real_const_proj d n).
      rewrite (real_const_proj lb n).
      ring.
  Qed.


(* real_inv_pos 通用坐标（cert 抽象 destruct：N0 任意；And := A*B ⟹ snd）
   projT1 (real_inv_pos x Hx) n == if Nat.leb N0 n then Qinv (x_n)
    else Qinv (x_N0)，N0 := 证书见证尾指标 *)
Lemma b5dQ_inv_coord : forall (x : Real) (Hx : real_lt real_zero x) (n : nat),
  projT1 (real_inv_pos x Hx) n
  == (if Nat.leb (projT1 (snd (projT2 Hx))) n
      then Qinv (projT1 x n)
      else Qinv (projT1 x (projT1 (snd (projT2 Hx))))).
Proof.
  intros x Hx n.
  destruct x as [u Hu].
  destruct Hx as [eps0 [Heps0 [N0 HN0]]].
  cbn [projT1 projT2 snd fst real_inv_pos].
  reflexivity.
Qed.

(* ============================================================ *)
(* §1 闭式证书与值定义                                          *)
(* ============================================================ *)

Lemma b5dQ_Hq32T : QltT 0 (1 # 32). Proof. vm_compute. reflexivity. Qed.
Lemma b5dQ_Hq4T : QltT 0 (1 # 4). Proof. vm_compute. reflexivity. Qed.
Lemma b5dQ_Hq12288T : QltT 0 (1 # 12288). Proof. vm_compute. reflexivity. Qed.
Lemma b5dQ_H1T : QltT 0 1. Proof. vm_compute. reflexivity. Qed.
Lemma b5dQ_H1pos : Qlt 0 1. Proof. unfold Qlt. simpl. lia. Qed.
Lemma b5dQ_HC40 : Qle 0 b5d3_exp_arch4_C.
Proof. apply (Qle_trans _ 1 _). - exact Qle_0_1. - apply QleT'_to_Qle. exact b5d3_exp_arch4_C_ge1. Qed.

(* b3rr_C2 在 q 域的正性包装（M := (1#2)(1+q)，0<q<1 ⟹ 0 ≤ M < 1） *)
Lemma b5dQ_Cr_ge0 : forall (q : Q), Qle 0 q -> Qlt q 1 ->
  Qle 0 (b3rr_C2 (Qmult (1 # 2) (Qplus 1 q))).
Proof.
  intros q Hq0 Hq1.
  apply (b3rr_C2_0 (Qmult (1 # 2) (Qplus 1 q))).
  - apply (Qmult_le_0_compat (1 # 2) (Qplus 1 q)).
    + change (Qle 0 (1 # 2)). unfold Qle. simpl. lia.
    + nra.
  - (* (1#2)(1+q) < 1 ⟸ 1+q < 2 ⟸ q < 1 *)
    nra.
Qed.

(* b3rr k(q) := Qinv (4·(Cr+1)) 正性（0 < q 侧不需要——0 ≤ Cr 即足） *)
Lemma b5dQ_kbr_pos : forall (q : Q), Qle 0 q -> Qlt q 1 ->
  Qlt 0 (Qinv (Qmult 4 (Qplus (b3rr_C2 (Qmult (1 # 2) (Qplus 1 q))) 1))).
Proof.
  intros q Hq0 Hq1.
  apply Qinv_lt_0_compat.
  apply (Qmult_lt_0_compat 4 (Qplus (b3rr_C2 (Qmult (1 # 2) (Qplus 1 q))) 1)).
  - change (Qlt 0 4). unfold Qlt. simpl. lia.
  - apply (Qlt_le_trans 0 1 (Qplus (b3rr_C2 (Qmult (1 # 2) (Qplus 1 q))) 1)).
    + change (Qlt 0 1). unfold Qlt. simpl. lia.
    + apply (Qle_trans 1 (0 + 1) (Qplus (b3rr_C2 (Qmult (1 # 2) (Qplus 1 q))) 1)).
      * apply qeq_imp_qle. ring.
      * apply Qplus_le_compat.
        -- exact (b5dQ_Cr_ge0 q Hq0 Hq1).
        -- apply Qle_refl.
Qed.

(* E 链份额链坐标（嵌套 Qmult——与 piece 体 set 代入形逐字一致） *)
(* 3 链（sin-eps）：a·(1#32)·(1#4) *)
Definition b5dQ_chain3 (a : Q) : Q :=
  Qmult (Qmult a (1 # 32)) (1 # 4).
(* 4 链（b3rr-eps）：a·(1#32)·(1#4)·(1#12288) *)
Definition b5dQ_chain4 (a : Q) : Q :=
  Qmult (b5dQ_chain3 a) (1 # 12288).

(* b3rr 树坐标（q-分支 + 4 链乘积分支）——vB *)
Definition b5dQ_vB (q a : Q) : Q :=
  Qmin (Qmult (1 # 2) (Qminus 1 q))
       (Qmult (b5dQ_chain4 a)
              (Qinv (Qmult 4 (Qplus (b3rr_C2 (Qmult (1 # 2) (Qplus 1 q))) 1)))).

(* vB 正性（0<q<1 ∧ 0<a ⟹ 0 < vB） *)
Lemma b5dQ_vB_pos : forall (q a : Q), Qlt 0 q -> Qlt q 1 -> Qlt 0 a ->
  Qlt 0 (b5dQ_vB q a).
Proof.
  intros q a Hq0 Hq1 Ha.
  unfold b5dQ_vB.
  apply Q.min_glb_lt.
  - apply (Qmult_lt_0_compat (1 # 2) (Qminus 1 q)).
    + change (Qlt 0 (1 # 2)). unfold Qlt. simpl. lia.
    + apply (proj1 (Qlt_minus_iff q 1)). exact Hq1.
  - apply (Qmult_lt_0_compat (b5dQ_chain4 a)
           (Qinv (Qmult 4 (Qplus (b3rr_C2 (Qmult (1 # 2) (Qplus 1 q))) 1)))).
    + unfold b5dQ_chain4, b5dQ_chain3.
      apply (Qmult_lt_0_compat (Qmult (Qmult a (1 # 32)) (1 # 4)) (1 # 12288)).
      * apply (Qmult_lt_0_compat (Qmult a (1 # 32)) (1 # 4)).
        -- apply (Qmult_lt_0_compat a (1 # 32)).
           ++ exact Ha.
           ++ change (Qlt 0 (1 # 32)). unfold Qlt. simpl. lia.
        -- change (Qlt 0 (1 # 4)). unfold Qlt. simpl. lia.
      * change (Qlt 0 (1 # 12288)). unfold Qlt. simpl. lia.
    + exact (b5dQ_kbr_pos q (Qlt_le_weak 0 q Hq0) Hq1).
Qed.

(* vB ≤ 各叶（Q.min 投影——q 侧与乘积侧） *)
Lemma b5dQ_vB_le_q : forall (q a : Q),
  Qle (b5dQ_vB q a) (Qmult (1 # 2) (Qminus 1 q)).
Proof. intros q a. unfold b5dQ_vB. apply Q.le_min_l. Qed.
Lemma b5dQ_vB_le_p : forall (q a : Q),
  Qle (b5dQ_vB q a)
      (Qmult (b5dQ_chain4 a)
             (Qinv (Qmult 4 (Qplus (b3rr_C2 (Qmult (1 # 2) (Qplus 1 q))) 1)))).
Proof. intros q a. unfold b5dQ_vB. apply Q.le_min_r. Qed.

(* 叶正性（q 侧 + 乘积侧） *)
Lemma b5dQ_leaf1_pos : forall (q : Q), Qlt q 1 -> Qlt 0 (Qmult (1 # 2) (Qminus 1 q)).
Proof.
  intros q Hq1.
  apply (Qmult_lt_0_compat (1 # 2) (Qminus 1 q)).
  - change (Qlt 0 (1 # 2)). unfold Qlt. simpl. lia.
  - apply (proj1 (Qlt_minus_iff q 1)). exact Hq1.
Qed.
Lemma b5dQ_chain4_pos : forall (a : Q), Qlt 0 a -> Qlt 0 (b5dQ_chain4 a).
Proof.
  intros a Ha.
  unfold b5dQ_chain4, b5dQ_chain3.
  apply (Qmult_lt_0_compat (Qmult (Qmult a (1 # 32)) (1 # 4)) (1 # 12288)).
  - apply (Qmult_lt_0_compat (Qmult a (1 # 32)) (1 # 4)).
    + apply (Qmult_lt_0_compat a (1 # 32)).
      * exact Ha.
      * change (Qlt 0 (1 # 32)). unfold Qlt. simpl. lia.
    + change (Qlt 0 (1 # 4)). unfold Qlt. simpl. lia.
  - change (Qlt 0 (1 # 12288)). unfold Qlt. simpl. lia.
Qed.
Lemma b5dQ_leaf2_pos : forall (q a : Q), Qlt 0 q -> Qlt q 1 -> Qlt 0 a ->
  Qlt 0 (Qmult (b5dQ_chain4 a)
               (Qinv (Qmult 4 (Qplus (b3rr_C2 (Qmult (1 # 2) (Qplus 1 q))) 1)))).
Proof.
  intros q a Hq0 Hq1 Ha.
  apply (Qmult_lt_0_compat (b5dQ_chain4 a)
           (Qinv (Qmult 4 (Qplus (b3rr_C2 (Qmult (1 # 2) (Qplus 1 q))) 1)))).
  - exact (b5dQ_chain4_pos a Ha).
  - exact (b5dQ_kbr_pos q (Qlt_le_weak 0 q Hq0) Hq1).
Qed.

(* ============================================================ *)
(* §2 lb_b3rr：b3rr @ 4 链（值 = vB/2）                        *)
(* ============================================================ *)
Lemma b5dQ_lb_b3rr : forall (q : Q) (Hq0 : Qlt 0 q) (Hq1 : Qlt q 1)
  (x : Real) (Hxr : forall n : nat, QleT' (Qabs (projT1 x n)) q)
  (a : Q) (Ha : Qlt 0 a),
  real_lt (real_const (Qmult (b5dQ_vB q a) (1 # 2)))
    (projT1 (b5d1_b3rr_atan_deriv_lin q (Qlt_le_weak 0 q Hq0) Hq1 x Hxr
               (real_mult (real_mult (real_mult (real_const a) (real_const (1 # 32)))
                                     (real_const (1 # 4)))
                          (real_const (1 # 12288)))
               (b5dI_real_mult_positive_exp
                  (real_mult (real_mult (real_const a) (real_const (1 # 32)))
                             (real_const (1 # 4)))
                  (real_const (1 # 12288))
                  (b5dI_real_mult_positive_exp
                     (real_mult (real_const a) (real_const (1 # 32)))
                     (real_const (1 # 4))
                     (b5dI_real_mult_positive_exp (real_const a) (real_const (1 # 32))
                        (b5dM_real_const_pos a (Qlt_to_QltT 0 a Ha))
                        (b5dM_real_const_pos (1 # 32) b5dQ_Hq32T))
                     (b5dM_real_const_pos (1 # 4) b5dQ_Hq4T))
                  (b5dM_real_const_pos (1 # 12288) b5dQ_Hq12288T)))).
Proof.
  intros q Hq0 Hq1 x Hxr a Ha.
  assert (Hv : Qlt 0 (b5dQ_vB q a)) by (exact (b5dQ_vB_pos q a Hq0 Hq1 Ha)).
  assert (HvT : QltT 0 (Qmult (b5dQ_vB q a) (1 # 4))).
  { apply Qlt_to_QltT.
    apply (Qmult_lt_0_compat (b5dQ_vB q a) (1 # 4)).
    + exact Hv.
    + change (Qlt 0 (1 # 4)). unfold Qlt. simpl. lia. }
  unfold real_lt.
  exists (Qmult (b5dQ_vB q a) (1 # 4)).
  split.
  { exact HvT. }
  { exists 0%nat.
    intros n Hn.
    apply Qlt_to_QltT.
    cbn [projT1 b5d1_b3rr_atan_deriv_lin real_min real_mult real_const].
    (* 目标：QltT (vB/4) (Qmin c1 c2 − vB/2)——cbn 坐标 ≡ vB 值树（conv） *)
    apply (proj2 (Qlt_minus_iff (Qmult (b5dQ_vB q a) (1 # 4))
                                (Qminus (b5dQ_vB q a) (Qmult (b5dQ_vB q a) (1 # 2))))).
    apply (Qlt_le_trans 0 (Qmult (b5dQ_vB q a) (1 # 4))
                         (Qminus (Qminus (b5dQ_vB q a) (Qmult (b5dQ_vB q a) (1 # 2)))
                                 (Qmult (b5dQ_vB q a) (1 # 4)))).
    + apply QltT_to_Qlt. exact HvT.
    + apply qeq_imp_qle.
      ring.
  }
  Qed.

(* ============ §3 lb_atan（透传层：atan @ 4 链 ≡ b3rr @ 4 链） ============ *)
Lemma b5dQ_lb_atan : forall (q : Q) (Hq0 : Qlt 0 q) (Hq1 : Qlt q 1)
  (x : Real) (Hxr : forall n : nat, QleT' (Qabs (projT1 x n)) q)
  (a : Q) (Ha : Qlt 0 a),
  real_lt (real_const (Qmult (b5dQ_vB q a) (1 # 2)))
    (projT1 (b5dD_atan_deriv_b5a_r_exp q (Qlt_le_weak 0 q Hq0) Hq1 x Hxr
               (real_mult (real_mult (real_mult (real_const a) (real_const (1 # 32)))
                                     (real_const (1 # 4)))
                          (real_const (1 # 12288)))
               (b5dI_real_mult_positive_exp
                  (real_mult (real_mult (real_const a) (real_const (1 # 32)))
                             (real_const (1 # 4)))
                  (real_const (1 # 12288))
                  (b5dI_real_mult_positive_exp
                     (real_mult (real_const a) (real_const (1 # 32)))
                     (real_const (1 # 4))
                     (b5dI_real_mult_positive_exp (real_const a) (real_const (1 # 32))
                        (b5dM_real_const_pos a (Qlt_to_QltT 0 a Ha))
                        (b5dM_real_const_pos (1 # 32) b5dQ_Hq32T))
                     (b5dM_real_const_pos (1 # 4) b5dQ_Hq4T))
                  (b5dM_real_const_pos (1 # 12288) b5dQ_Hq12288T)))).
Proof.
  intros q Hq0 Hq1 x Hxr a Ha.
  assert (Hv : Qlt 0 (b5dQ_vB q a)) by (exact (b5dQ_vB_pos q a Hq0 Hq1 Ha)).
  assert (HvT : QltT 0 (Qmult (b5dQ_vB q a) (1 # 4))).
  { apply Qlt_to_QltT.
    apply (Qmult_lt_0_compat (b5dQ_vB q a) (1 # 4)).
    + exact Hv.
    + change (Qlt 0 (1 # 4)). unfold Qlt. simpl. lia. }
  unfold real_lt.
  exists (Qmult (b5dQ_vB q a) (1 # 4)).
  split.
  { exact HvT. }
  { exists 0%nat.
    intros n Hn.
    apply Qlt_to_QltT.
    cbn [projT1 b5dD_atan_deriv_b5a_r_exp b5d1_b3rr_atan_deriv_lin
         real_min real_mult real_const].
    apply (proj2 (Qlt_minus_iff (Qmult (b5dQ_vB q a) (1 # 4))
                                (Qminus (b5dQ_vB q a) (Qmult (b5dQ_vB q a) (1 # 2))))).
    apply (Qlt_le_trans 0 (Qmult (b5dQ_vB q a) (1 # 4))
                         (Qminus (Qminus (b5dQ_vB q a) (Qmult (b5dQ_vB q a) (1 # 2)))
                                 (Qmult (b5dQ_vB q a) (1 # 4)))).
    + apply QltT_to_Qlt. exact HvT.
    + apply qeq_imp_qle.
      ring.
  }
  Qed.

(* ============ §4 lb_vdh（透传层：vdh @ 3 链 + k2 := 1#12288 ≡ b3rr @ 4 链）
   k2p 值不进 δ（证明位）——登记偏差：语句 k2p := 1#12288（与 k2 同值简化；
   实际 sin 体内 k2p = C4 依赖形——不进值路径，零影响） ============ *)
Lemma b5dQ_lb_vdh : forall (q : Q) (Hq0 : Qlt 0 q) (Hq1 : Qlt q 1)
  (x : Real) (Hxr : forall n : nat, QleT' (Qabs (projT1 x n)) q)
  (a : Q) (Ha : Qlt 0 a),
  real_lt (real_const (Qmult (b5dQ_vB q a) (1 # 2)))
    (projT1 (b5dD_vdh_pts_r_exp q (Qlt_le_weak 0 q Hq0) Hq1 x Hxr
               (real_mult (real_mult (real_const a) (real_const (1 # 32)))
                          (real_const (1 # 4)))
               (b5dI_real_mult_positive_exp
                  (real_mult (real_const a) (real_const (1 # 32)))
                  (real_const (1 # 4))
                  (b5dI_real_mult_positive_exp (real_const a) (real_const (1 # 32))
                     (b5dM_real_const_pos a (Qlt_to_QltT 0 a Ha))
                     (b5dM_real_const_pos (1 # 32) b5dQ_Hq32T))
                  (b5dM_real_const_pos (1 # 4) b5dQ_Hq4T))
               (1 # 12288) (1 # 12288)
               b5dQ_Hq12288T b5dQ_Hq12288T)).
Proof.
  intros q Hq0 Hq1 x Hxr a Ha.
  assert (Hv : Qlt 0 (b5dQ_vB q a)) by (exact (b5dQ_vB_pos q a Hq0 Hq1 Ha)).
  assert (HvT : QltT 0 (Qmult (b5dQ_vB q a) (1 # 4))).
  { apply Qlt_to_QltT.
    apply (Qmult_lt_0_compat (b5dQ_vB q a) (1 # 4)).
    + exact Hv.
    + change (Qlt 0 (1 # 4)). unfold Qlt. simpl. lia. }
  unfold real_lt.
  exists (Qmult (b5dQ_vB q a) (1 # 4)).
  split.
  { exact HvT. }
  { exists 0%nat.
    intros n Hn.
    apply Qlt_to_QltT.
    cbn [projT1 b5dD_vdh_pts_r_exp b5dD_atan_deriv_b5a_r_exp
         b5d1_b3rr_atan_deriv_lin real_min real_mult real_const].
    apply (proj2 (Qlt_minus_iff (Qmult (b5dQ_vB q a) (1 # 4))
                                (Qminus (b5dQ_vB q a) (Qmult (b5dQ_vB q a) (1 # 2))))).
    apply (Qlt_le_trans 0 (Qmult (b5dQ_vB q a) (1 # 4))
                         (Qminus (Qminus (b5dQ_vB q a) (Qmult (b5dQ_vB q a) (1 # 2)))
                                 (Qmult (b5dQ_vB q a) (1 # 4)))).
    + apply QltT_to_Qlt. exact HvT.
    + apply qeq_imp_qle.
      ring.
  }
  Qed.

(* ============================================================ *)
(* §5 通用 margin 件 + vSC 值定义（sin/cos 树坐标——3 链实例）    *)
(* ============================================================ *)

(* 通用 margin：0 < v ⟹ QltT (v/4) (v − v/2)（坐标层收尾件） *)
Lemma b5dQ_margin_lemma : forall (v : Q), Qlt 0 v ->
  QltT (Qmult v (1 # 4)) (Qminus v (Qmult v (1 # 2))).
Proof.
  intros v Hv.
  apply Qlt_to_QltT.
  apply (proj2 (Qlt_minus_iff (Qmult v (1 # 4)) (Qminus v (Qmult v (1 # 2))))).
  apply (Qlt_le_trans 0 (Qmult v (1 # 4))
                       (Qminus (Qminus v (Qmult v (1 # 2))) (Qmult v (1 # 4)))).
  - apply (Qmult_lt_0_compat v (1 # 4)).
    + exact Hv.
    + change (Qlt 0 (1 # 4)). unfold Qlt. simpl. lia.
  - apply qeq_imp_qle. ring.
Qed.

Lemma b5dQ_chain3_pos : forall (a : Q), Qlt 0 a -> Qlt 0 (b5dQ_chain3 a).
Proof.
  intros a Ha.
  unfold b5dQ_chain3.
  apply (Qmult_lt_0_compat (Qmult a (1 # 32)) (1 # 4)).
  - apply (Qmult_lt_0_compat a (1 # 32)).
    + exact Ha.
    + change (Qlt 0 (1 # 32)). unfold Qlt. simpl. lia.
  - change (Qlt 0 (1 # 4)). unfold Qlt. simpl. lia.
Qed.

Lemma b5dQ_one_plus_c_pos : forall (c : Q), Qle 0 c -> Qlt 0 (Qplus 1 c).
Proof.
  intros c Hc.
  apply (Qlt_le_trans 0 1 (Qplus 1 c)).
  - change (Qlt 0 1). unfold Qlt. simpl. lia.
  - apply (Qle_trans 1 (Qplus 1 0) (Qplus 1 c)).
    + apply qeq_imp_qle. ring.
    + apply Qplus_le_compat; [ apply Qle_refl | exact Hc ].
Qed.

(* sin 树坐标（3 链实例）：min(min(min vB (1#2)) (chain3·(1#1536)))
   ((1#4)·Qinv(1 + chain3·(1#12288)))——δa 支 = vB（vdh/atan/b3rr 透传全链） *)
Definition b5dQ_vSC (q a : Q) : Q :=
  Qmin (Qmin (Qmin (b5dQ_vB q a) (1 # 2))
             (Qmult (b5dQ_chain3 a) (1 # 1536)))
       (Qmult (1 # 4) (Qinv (Qplus 1 (Qmult (b5dQ_chain3 a) (1 # 12288))))).

Lemma b5dQ_vSC_pos : forall (q a : Q), Qlt 0 q -> Qlt q 1 -> Qlt 0 a ->
  Qlt 0 (b5dQ_vSC q a).
Proof.
  intros q a Hq0 Hq1 Ha.
  unfold b5dQ_vSC.
  apply Q.min_glb_lt.
  - apply Q.min_glb_lt.
    + apply Q.min_glb_lt.
      * exact (b5dQ_vB_pos q a Hq0 Hq1 Ha).
      * change (Qlt 0 (1 # 2)). unfold Qlt. simpl. lia.
    + apply (Qmult_lt_0_compat (b5dQ_chain3 a) (1 # 1536)).
      * exact (b5dQ_chain3_pos a Ha).
      * change (Qlt 0 (1 # 1536)). unfold Qlt. simpl. lia.
  - apply (Qmult_lt_0_compat (1 # 4)
           (Qinv (Qplus 1 (Qmult (b5dQ_chain3 a) (1 # 12288))))).
    + change (Qlt 0 (1 # 4)). unfold Qlt. simpl. lia.
    + apply Qinv_lt_0_compat.
      apply (b5dQ_one_plus_c_pos (Qmult (b5dQ_chain3 a) (1 # 12288))).
      apply Qlt_le_weak.
      apply (Qmult_lt_0_compat (b5dQ_chain3 a) (1 # 12288)).
      * exact (b5dQ_chain3_pos a Ha).
      * change (Qlt 0 (1 # 12288)). unfold Qlt. simpl. lia.
Qed.

(* §6 lb_sin_cos：sin/cos @ 3 链（值 = vSC/2——sin/cos 同树同值） *)
(* ============================================================ *)
Lemma b5dQ_lb_sin_cos : forall (q : Q) (Hq0 : Qlt 0 q) (Hq1 : Qlt q 1)
  (x : Real) (Hxr : forall n : nat, QleT' (Qabs (projT1 x n)) q)
  (Hs : forall n : nat, Qle (Qabs (sin_partial n (arctan_partial n (projT1 x n)))) 1)
  (Hc : forall n : nat, Qle (Qabs (cos_partial n (arctan_partial n (projT1 x n)))) 1)
  (a : Q) (Ha : Qlt 0 a),
  real_lt (real_const (Qmult (b5dQ_vSC q a) (1 # 2)))
    (projT1 (b5dI_sin_atan_diff_closed_r_exp q (Qlt_le_weak 0 q Hq0) Hq1 x Hxr
              1 1 b5d3_exp_arch4_C b5dQ_H1pos b5dQ_H1pos b5dQ_HC40
              b5d3_exp_arch4_C_ge1 b5d3_exp_arch4_C_all Hs Hc
              (real_mult (real_mult (real_const a) (real_const (1 # 32)))
                         (real_const (1 # 4)))
              (b5dI_real_mult_positive_exp
                 (real_mult (real_const a) (real_const (1 # 32)))
                 (real_const (1 # 4))
                 (b5dI_real_mult_positive_exp (real_const a) (real_const (1 # 32))
                    (b5dM_real_const_pos a (Qlt_to_QltT 0 a Ha))
                    (b5dM_real_const_pos (1 # 32) b5dQ_Hq32T))
                 (b5dM_real_const_pos (1 # 4) b5dQ_Hq4T)))).
Proof.
  intros q Hq0 Hq1 x Hxr Hs Hc a Ha.
  assert (Hv : Qlt 0 (b5dQ_vSC q a)) by (exact (b5dQ_vSC_pos q a Hq0 Hq1 Ha)).
  unfold real_lt.
  exists (Qmult (b5dQ_vSC q a) (1 # 4)).
  split.
  - apply Qlt_to_QltT.
    apply (Qmult_lt_0_compat (b5dQ_vSC q a) (1 # 4)).
    + exact Hv.
    + change (Qlt 0 (1 # 4)). unfold Qlt. simpl. lia.
  - exists 0%nat.
    intros n Hn.
    cbn [projT1 b5dI_sin_atan_diff_closed_r_exp b5dD_vdh_pts_r_exp
         b5dD_atan_deriv_b5a_r_exp b5d1_b3rr_atan_deriv_lin
         b5dI_real_mult_positive_exp b5dM_b5i_one_plus_eps2_pos
         b5dM_real_const_pos real_min real_mult real_const real_plus
         real_one real_inv_pos Nat.leb Nat.max Nat.min].
    exact (b5dQ_margin_lemma (b5dQ_vSC q a) Hv).
  Qed.

(* ============================================================ *)
(* §7 lb_cos：cos @ 3 链（同树同值——Ms := Mc := 1 对称）       *)
(* ============================================================ *)
Lemma b5dQ_lb_cos : forall (q : Q) (Hq0 : Qlt 0 q) (Hq1 : Qlt q 1)
  (x : Real) (Hxr : forall n : nat, QleT' (Qabs (projT1 x n)) q)
  (Hs : forall n : nat, Qle (Qabs (sin_partial n (arctan_partial n (projT1 x n)))) 1)
  (Hc : forall n : nat, Qle (Qabs (cos_partial n (arctan_partial n (projT1 x n)))) 1)
  (a : Q) (Ha : Qlt 0 a),
  real_lt (real_const (Qmult (b5dQ_vSC q a) (1 # 2)))
    (projT1 (b5dI_cos_atan_diff_closed_r_exp q (Qlt_le_weak 0 q Hq0) Hq1 x Hxr
              1 1 b5d3_exp_arch4_C b5dQ_H1pos b5dQ_H1pos b5dQ_HC40
              b5d3_exp_arch4_C_ge1 b5d3_exp_arch4_C_all Hs Hc
              (real_mult (real_mult (real_const a) (real_const (1 # 32)))
                         (real_const (1 # 4)))
              (b5dI_real_mult_positive_exp
                 (real_mult (real_const a) (real_const (1 # 32)))
                 (real_const (1 # 4))
                 (b5dI_real_mult_positive_exp (real_const a) (real_const (1 # 32))
                    (b5dM_real_const_pos a (Qlt_to_QltT 0 a Ha))
                    (b5dM_real_const_pos (1 # 32) b5dQ_Hq32T))
                 (b5dM_real_const_pos (1 # 4) b5dQ_Hq4T)))).
Proof.
  intros q Hq0 Hq1 x Hxr Hs Hc a Ha.
  assert (Hv : Qlt 0 (b5dQ_vSC q a)) by (exact (b5dQ_vSC_pos q a Hq0 Hq1 Ha)).
  unfold real_lt.
  exists (Qmult (b5dQ_vSC q a) (1 # 4)).
  split.
  - apply Qlt_to_QltT.
    apply (Qmult_lt_0_compat (b5dQ_vSC q a) (1 # 4)).
    + exact Hv.
    + change (Qlt 0 (1 # 4)). unfold Qlt. simpl. lia.
  - exists 0%nat.
    intros n Hn.
    cbn [projT1 b5dI_cos_atan_diff_closed_r_exp b5dD_vdh_pts_r_exp
         b5dD_atan_deriv_b5a_r_exp b5d1_b3rr_atan_deriv_lin
         b5dI_real_mult_positive_exp b5dM_b5i_one_plus_eps2_pos
         b5dM_real_const_pos real_min real_mult real_const real_plus
         real_one real_inv_pos Nat.leb Nat.max Nat.min].
    exact (b5dQ_margin_lemma (b5dQ_vSC q a) Hv).
  Qed.

(* ============================================================ *)
(* §8 vE 值定义（E 树坐标——2 链实例）+ lb_E                     *)
(* ============================================================ *)

(* E 树坐标：min(min vSC vSC) ((a·(1#32))·(1#1024))——sin/cos 支同值 *)
Definition b5dQ_vE (q a : Q) : Q :=
  Qmin (Qmin (b5dQ_vSC q a) (b5dQ_vSC q a))
       (Qmult (Qmult a (1 # 32)) (1 # 1024)).

Lemma b5dQ_vE_pos : forall (q a : Q), Qlt 0 q -> Qlt q 1 -> Qlt 0 a ->
  Qlt 0 (b5dQ_vE q a).
Proof.
  intros q a Hq0 Hq1 Ha.
  unfold b5dQ_vE.
  apply Q.min_glb_lt.
  - apply Q.min_glb_lt.
    + exact (b5dQ_vSC_pos q a Hq0 Hq1 Ha).
    + exact (b5dQ_vSC_pos q a Hq0 Hq1 Ha).
  - apply (Qmult_lt_0_compat (Qmult a (1 # 32)) (1 # 1024)).
    + apply (Qmult_lt_0_compat a (1 # 32)).
      * exact Ha.
      * change (Qlt 0 (1 # 32)). unfold Qlt. simpl. lia.
    + change (Qlt 0 (1 # 1024)). unfold Qlt. simpl. lia.
Qed.

(* lb_E：E-diff @ 2 链（值 = vE/2） *)
Lemma b5dQ_lb_E : forall (q : Q) (Hq0 : Qlt 0 q) (Hq1 : Qlt q 1)
  (x : Real) (Hxr : forall n : nat, QleT' (Qabs (projT1 x n)) q)
  (Hs : forall n : nat, Qle (Qabs (sin_partial n (arctan_partial n (projT1 x n)))) 1)
  (Hc : forall n : nat, Qle (Qabs (cos_partial n (arctan_partial n (projT1 x n)))) 1)
  (a : Q) (Ha : Qlt 0 a),
  real_lt (real_const (Qmult (b5dQ_vE q a) (1 # 2)))
    (projT1 (b5dI_E_diff_closed_r_exp q (Qlt_le_weak 0 q Hq0) Hq1 x Hxr
              1 1 b5d3_exp_arch4_C b5dQ_H1pos b5dQ_H1pos b5dQ_HC40
              b5d3_exp_arch4_C_ge1 b5d3_exp_arch4_C_all Hs Hc
              (real_mult (real_const a) (real_const (1 # 32)))
              (b5dI_real_mult_positive_exp (real_const a) (real_const (1 # 32))
                 (b5dM_real_const_pos a (Qlt_to_QltT 0 a Ha))
                 (b5dM_real_const_pos (1 # 32) b5dQ_Hq32T)))).
Proof.
  intros q Hq0 Hq1 x Hxr Hs Hc a Ha.
  assert (Hv : Qlt 0 (b5dQ_vE q a)) by (exact (b5dQ_vE_pos q a Hq0 Hq1 Ha)).
  unfold real_lt.
  exists (Qmult (b5dQ_vE q a) (1 # 4)).
  split.
  - apply Qlt_to_QltT.
    apply (Qmult_lt_0_compat (b5dQ_vE q a) (1 # 4)).
    + exact Hv.
    + change (Qlt 0 (1 # 4)). unfold Qlt. simpl. lia.
  - exists 0%nat.
    intros n Hn.
    cbn [projT1 b5dI_E_diff_closed_r_exp b5dI_sin_atan_diff_closed_r_exp
         b5dI_cos_atan_diff_closed_r_exp b5dD_vdh_pts_r_exp
         b5dD_atan_deriv_b5a_r_exp b5d1_b3rr_atan_deriv_lin
         b5dI_real_mult_positive_exp b5dM_b5i_one_plus_eps2_pos
         b5dM_real_const_pos real_min real_mult real_const real_plus
         real_one real_inv_pos Nat.leb Nat.max Nat.min].
    exact (b5dQ_margin_lemma (b5dQ_vE q a) Hv).
  Qed.


(* ============================================================ *)
(* end sc2_b5a_item27_p1_lbE.v（P1 · lb-E 链 · b3rr/atan/vdh/sin_cos/E） *)
(* ============================================================ *)


(* ============================================================ *)
(* end sc2_b5a_item27_p1_lbE.v（P1 · lb-E 链 · b3rr/atan/vdh/sin_cos/E） *)
(* ============================================================ *)

(* ===== 段 P2（lb-log 链：helper 批 + lb_logdiff/logerr/gdiff/exp_part，27 Lemma）===== *)

(* ============================================================ *)
(* helper 1：Qinv ≤ 单调（x ≤ y 正 ⟹ Qinv y ≤ Qinv x）          *)
(* 检验件 p_qinv_le_mono 逐字移植（改名 b5dQ_ 前缀）。             *)
(* ============================================================ *)
Lemma b5dQ_p_qinv_le_mono : forall (x y : Q),
  Qlt 0 x -> Qlt 0 y -> Qle x y -> Qle (Qinv y) (Qinv x).
Proof.
  intros x y Hx Hy Hxy.
  destruct (Qlt_le_dec x y) as [Hlt | Hge].
  - apply Qlt_le_weak.
    apply (proj1 (Qinv_lt_contravar x y Hx Hy)). exact Hlt.
  - apply qeq_imp_qle.
    apply (Qinv_comp y x).
    apply Qeq_sym.
    exact (Qle_antisym x y Hxy Hge).
Qed.

(* ============================================================ *)
(* helper 2：invM 坐标件（S 原子保原子）                         *)
(* 检验件 p_inv_coord0 逐字移植（改名 b5dQ_p_invM_coord——段内      *)
(* 唯一命名，进度 §1.2 注登记）。                                *)
(* ============================================================ *)
Lemma b5dQ_p_invM_coord : forall (x : Real) (n : nat),
  projT1 (real_inv_pos (real_plus real_one (real_abs (b5a_S x)))
                       (b5dK_real_abs_plus_one_pos_exp (b5a_S x))) n
  == Qinv (1 + Qabs (projT1 (b5a_S x) n)).
Proof.
  intros x n.
  cbn [projT1 real_inv_pos real_plus real_abs real_one real_const
       b5dK_real_abs_plus_one_pos_exp].
  reflexivity.
Qed.


(* ============================================================ *)
(* helper 4：u 坐标件（u := b5f_u x = 1 + x·x，逐点）            *)
(* 坐标层小件：b5f_u 入 cbn 清单决策的配套（R-A 登记）。          *)
(* ============================================================ *)
Lemma b5dQ_p_u_coord : forall (x : Real) (n : nat),
  projT1 (b5f_u x) n == Qplus 1 (Qmult (projT1 x n) (projT1 x n)).
Proof.
  intros x n.
  unfold b5f_u.
  rewrite (real_plus_proj real_one (real_mult x x) n).
  rewrite (real_mult_proj x x n).
  cbn [projT1 real_one].
  reflexivity.
Qed.

(* ============================================================ *)
(* helper 5：u 坐标下界（u_n ≥ 1 逐点——平方非负，nra-on-Q 实证）*)
(* ============================================================ *)
Lemma b5dQ_p_u_ge1 : forall (x : Real) (n : nat),
  Qle 1 (projT1 (b5f_u x) n).
Proof.
  intros x n.
  rewrite (b5dQ_p_u_coord x n).
  nra.
Qed.

(* ============================================================ *)
(* helper 6：Qle-版 min-glb（min 分解下界）                  *)
(* ============================================================ *)
Lemma b5dQ_p_min_glb_le : forall (a b c : Q),
  Qle c a -> Qle c b -> Qle c (Qmin a b).
Proof.
  intros a b c Hca Hcb.
  destruct (Qlt_le_dec a b) as [Hlt | Hge].
  - rewrite (Q.min_l a b (Qlt_le_weak a b Hlt)). exact Hca.
  - rewrite (Q.min_r a b Hge). exact Hcb.
Qed.

(* ============================================================ *)
(* helper 7：Qeq (Qinv 2) (1#2)-类（坐标层归约产物归一化）      *)
(* ============================================================ *)
Lemma b5dQ_p_qinv2 : Qinv 2 == 1 # 2.
Proof. unfold Qinv. reflexivity. Qed.


Lemma b5dQ_p_qinv2sq : Qmult (Qinv 2) (Qinv 2) == 1 # 4.
Proof. unfold Qinv. reflexivity. Qed.

Lemma b5dQ_p_qinv3 : Qinv 3 == 1 # 3.
Proof. unfold Qinv. reflexivity. Qed.

(* ============================================================ *)
(* helper 8：Qmin 对减法的右分配（min 树 − c 分解）             *)
(* ============================================================ *)
Lemma b5dQ_p_qmin_sub_r : forall (a b c : Q),
  (Qmin a b) - c == Qmin (a - c) (b - c).
Proof.
  intros a b c.
  destruct (Qlt_le_dec a b) as [Hlt | Hge].
  - rewrite (Q.min_l a b (Qlt_le_weak a b Hlt)).
    assert (Hle : a - c <= b - c) by nra.
    rewrite (Q.min_l (a - c) (b - c) Hle).
    reflexivity.
  - rewrite (Q.min_r a b Hge).
    assert (Hle : b - c <= a - c) by nra.
    rewrite (Q.min_r (a - c) (b - c) Hle).
    reflexivity.
Qed.

(* ============================================================ *)
(* helper 9：floor-glue（支地板 ≥ f + 严格 margin）        *)
(* ============================================================ *)
Lemma b5dQ_p_lt_sub_floor : forall (b f lb e : Q),
  Qle f b -> Qlt e (f - lb) -> Qlt e (b - lb).
Proof.
  intros b f lb e Hfb Hlt.
  apply (Qlt_le_trans e (f - lb) (b - lb)).
  - exact Hlt.
  - apply (Qplus_le_compat f b (Qopp lb) (Qopp lb)); [exact Hfb | apply Qle_refl].
Qed.

(* ============================================================ *)
(* 件 1：b5dQ_lb_logdiff（δD2f L6 坐标层实施）                  *)
(* 语句：进度 §1.3 逐字。证法：real_lt 展开（margin e := lb/2、 *)
(*   N := 0）→ 坐标件 b5dQ_lb_logdiff_coord（change 到 δ 显式树  *)
(*   + 投影 rewrite + 闭式子件 cbn）→ Q 层（u ≥ 1 逐支严格界 +  *)
(*   Q.min_glb_lt + qmin_sub_r + nra/ring）。                    *)
(* ============================================================ *)
Lemma b5dQ_lb_logdiff_coord : forall (x : Real) (a : Q) (Ha : Qlt 0 a) (n : nat),
  projT1 (projT1 (b5dJ_log_diff_dx_exp (b5f_u x) (b5a_one_plus_sq_pos x)
                 (real_const a) (real_const_pos a (Qlt_to_QltT 0 a Ha)))) n
  == Qmin (Qmult (Qinv 2) (projT1 (b5f_u x) n))
          (Qmult (Qmult (Qinv 2) (Qinv 2))
                 (Qmult a (Qmult (projT1 (b5f_u x) n) (projT1 (b5f_u x) n)))).
Proof.
  intros x a Ha n.
  change (projT1 (real_min
    (real_mult (real_inv_pos (real_plus real_one real_one) (b5dJ_two_pos_exp)) (b5f_u x))
    (real_mult
      (real_mult (real_inv_pos (real_plus real_one real_one) (b5dJ_two_pos_exp))
                 (real_inv_pos (real_plus real_one real_one) (b5dJ_two_pos_exp)))
      (real_mult (real_const a) (real_mult (b5f_u x) (b5f_u x))))) n
  == Qmin (Qmult (Qinv 2) (projT1 (b5f_u x) n))
          (Qmult (Qmult (Qinv 2) (Qinv 2))
                 (Qmult a (Qmult (projT1 (b5f_u x) n) (projT1 (b5f_u x) n))))).
  rewrite (real_min_proj
    (real_mult (real_inv_pos (real_plus real_one real_one) (b5dJ_two_pos_exp)) (b5f_u x))
    (real_mult
      (real_mult (real_inv_pos (real_plus real_one real_one) (b5dJ_two_pos_exp))
                 (real_inv_pos (real_plus real_one real_one) (b5dJ_two_pos_exp)))
      (real_mult (real_const a) (real_mult (b5f_u x) (b5f_u x)))) n).
  repeat (rewrite real_mult_proj || rewrite real_const_proj).
  cbn [projT1 real_inv_pos real_plus real_one real_const Nat.leb
       b5dJ_two_pos_exp].
  reflexivity.
Qed.

Lemma b5dQ_lb_logdiff : forall (x : Real) (a : Q) (Ha : Qlt 0 a),
  real_lt (real_const (Qmult (Qmin (1 # 2) (Qmult (1 # 4) a)) (1 # 2)))
    (projT1 (b5dJ_log_diff_dx_exp (b5f_u x) (b5a_one_plus_sq_pos x)
            (real_const a) (real_const_pos a (Qlt_to_QltT 0 a Ha)))).
Proof.
  intros x a Ha.
  set (c := Qmin (1 # 2) (Qmult (1 # 4) a)).
  set (lb := Qmult c (1 # 2)).
  set (e := Qmult lb (1 # 2)).
  assert (H12 : Qlt 0 (1 # 2)) by (change (Qlt 0 (1 # 2)); unfold Qlt; simpl; lia).
  assert (H14 : Qlt 0 (1 # 4)) by (change (Qlt 0 (1 # 4)); unfold Qlt; simpl; lia).
  assert (Hcpos : Qlt 0 c).
  { unfold c. apply Q.min_glb_lt.
    - exact H12.
    - apply (Qmult_lt_0_compat (1 # 4) a); [exact H14 | exact Ha]. }
  assert (Hlbpos : Qlt 0 lb).
  { unfold lb. apply (Qmult_lt_0_compat c (1 # 2)); [exact Hcpos | exact H12]. }
  assert (Hepos : Qlt 0 e).
  { unfold e. apply (Qmult_lt_0_compat lb (1 # 2)); [exact Hlbpos | exact H12]. }
  assert (Hc1 : Qle c (1 # 2)) by (unfold c; apply Q.le_min_l).
  assert (Hc2 : Qle c (Qmult (1 # 4) a)) by (unfold c; apply Q.le_min_r).
  unfold real_lt.
  exists e.
  split.
  { apply Qlt_to_QltT. exact Hepos. }
  { exists 0%nat.
    intros n Hn.
    apply Qlt_to_QltT.
    rewrite (b5dQ_lb_logdiff_coord x a Ha n).
    set (u := projT1 (b5f_u x) n).
    assert (Hug : Qle 1 u) by (unfold u; apply b5dQ_p_u_ge1).
    (* 逐支严格界：e < b1 − lb、e < b2 − lb（u ≥ 1 + c 界） *)
    assert (S1 : Qlt e ((Qmult (Qinv 2) u) - lb)).
    { unfold e, lb.
      rewrite b5dQ_p_qinv2.
      nra. }
    (* u² ≥ 1（平方非负——nra-on-Q 仅线性，手动链） *)
    assert (Hu0 : Qle 0 u).
    { apply (Qle_trans 0 1 u); [apply Qlt_le_weak; exact (QltT_to_Qlt 0 1 qltT_0_1) | exact Hug]. }
    assert (Hsq : Qle 1 (Qmult u u)).
    { apply (Qle_trans 1 u (Qmult u u)).
      - exact Hug.
      - apply (Qle_trans u (Qmult 1 u) (Qmult u u)).
        + apply qeq_le. ring.
        + apply (Qmult_le_compat_r 1 u u); [exact Hug | exact Hu0]. }
    assert (S2 : Qlt e ((Qmult (Qmult (Qinv 2) (Qinv 2)) (Qmult a (Qmult u u))) - lb)).
    { unfold e, lb.
      rewrite b5dQ_p_qinv2sq.
      apply (b5dQ_p_lt_sub_floor
               (Qmult (1 # 4) (Qmult a (Qmult u u)))   (* b *)
               (Qmult (1 # 4) a)                       (* f *)
               (Qmult c (1 # 2))                       (* lb *)
               (Qmult (Qmult c (1 # 2)) (1 # 2))).     (* e *)
      - (* Qle f b：a ≤ a·u² 经 Qmult_le_compat_r + 环桥 *)
        assert (Ha1 : Qle a (Qmult a (Qmult u u))).
        { apply (Qle_trans a (Qmult 1 a) (Qmult a (Qmult u u))).
          - apply qeq_le. ring.
          - apply (Qle_trans (Qmult 1 a) (Qmult (Qmult u u) a)
                             (Qmult a (Qmult u u))).
            + apply (Qmult_le_compat_r 1 (Qmult u u) a);
                [ exact Hsq | apply Qlt_le_weak; exact Ha ].
            + apply qeq_le. ring. }
        assert (Hb2a : Qle (Qmult a (1 # 4)) (Qmult (Qmult a (Qmult u u)) (1 # 4))).
        { apply (Qmult_le_compat_r a (Qmult a (Qmult u u)) (1 # 4));
            [ exact Ha1 | apply Qlt_le_weak; exact H14 ]. }
        apply (Qle_trans (Qmult (1 # 4) a) (Qmult a (1 # 4))
                         (Qmult (1 # 4) (Qmult a (Qmult u u)))).
        + apply qeq_le. ring.
        + apply (Qle_trans (Qmult a (1 # 4))
                           (Qmult (Qmult a (Qmult u u)) (1 # 4))
                           (Qmult (1 # 4) (Qmult a (Qmult u u)))).
          * exact Hb2a.
          * apply qeq_le. ring.
      - (* Qlt e (f − lb)：线性——nra *)
        nra. }
    rewrite (b5dQ_p_qmin_sub_r (Qmult (Qinv 2) u)
             (Qmult (Qmult (Qinv 2) (Qinv 2)) (Qmult a (Qmult u u))) lb).
    apply Q.min_glb_lt; [exact S1 | exact S2].
  }
Qed.


(* ============================================================ *)
(* 件 2：b5dQ_lb_logerr（δD2f L7）                              *)
(* LogErr 体内 δ := destruct (logdiff @ (x0 := b5f_u x、同 eps))  *)
(* 后原样 exists ⟹ projT1 (LogErr-app) 与 projT1 (logdiff-app)   *)
(* 定义性可转换（kernel conv）⟹ 本件 = change + exact lb_logdiff。*)
(* ============================================================ *)
Lemma b5dQ_lb_logerr : forall (x : Real) (a : Q) (Ha : Qlt 0 a),
  real_lt (real_const (Qmult (Qmin (1 # 2) (Qmult (1 # 4) a)) (1 # 2)))
    (projT1 (b5dJ_LogErr_delta_exp x (real_const a)
            (real_const_pos a (Qlt_to_QltT 0 a Ha)))).
Proof.
  intros x a Ha.
  change (real_lt (real_const (Qmult (Qmin (1 # 2) (Qmult (1 # 4) a)) (1 # 2)))
    (projT1 (b5dJ_log_diff_dx_exp (b5f_u x) (b5a_one_plus_sq_pos x)
            (real_const a) (real_const_pos a (Qlt_to_QltT 0 a Ha))))).
  exact (b5dQ_lb_logdiff x a Ha).
Qed.

(* ============================================================ *)
(* helper 10：u² ≥ 1 / 乘子吸收（u² 坐标链，nra 仅线性故手动）  *)
(* ============================================================ *)
Lemma b5dQ_p_q_square_ge1 : forall (u : Q), Qle 1 u -> Qle 1 (Qmult u u).
Proof.
  intros u Hug.
  assert (Hu0 : Qle 0 u).
  { apply (Qle_trans 0 1 u); [apply Qlt_le_weak; exact (QltT_to_Qlt 0 1 qltT_0_1) | exact Hug]. }
  apply (Qle_trans 1 u (Qmult u u)).
  - exact Hug.
  - apply (Qle_trans u (Qmult 1 u) (Qmult u u)).
    + apply qeq_le. ring.
    + apply (Qmult_le_compat_r 1 u u); [exact Hug | exact Hu0].
Qed.

Lemma b5dQ_p_q_mul_abs : forall (m u : Q),
  Qle 0 m -> Qle 1 u -> Qle m (Qmult m (Qmult u u)).
Proof.
  intros m u Hm0 Hug.
  assert (Hsq : Qle 1 (Qmult u u)) by (apply b5dQ_p_q_square_ge1; exact Hug).
  apply (Qle_trans m (Qmult 1 m) (Qmult m (Qmult u u))).
  - apply qeq_le. ring.
  - apply (Qle_trans (Qmult 1 m) (Qmult (Qmult u u) m) (Qmult m (Qmult u u))).
    + apply (Qmult_le_compat_r 1 (Qmult u u) m); [exact Hsq | exact Hm0].
    + apply qeq_le. ring.
Qed.

(* ============================================================ *)
(* 件 3：b5dQ_lb_gdiff（δD2f L8 坐标层实施）                    *)
(* gdiff 体内：kL := k2·(1#2)；epsL := eps·real_const kL；δL := *)
(*   projT1 (LogErr x epsL …)；δg := min(min(δL·(1#12),         *)
(*   eps·real_const kL), (1#2))。坐标件 + δL 坐标件 + Q 层。      *)
(* ============================================================ *)
Lemma b5dQ_p_epsL_pos : forall (a : Q) (Ha : Qlt 0 a) (k2 : Q) (Hk2 : QltT 0 k2),
  real_lt real_zero (real_mult (real_const a) (real_const (Qmult k2 (1 # 2)))).
Proof.
  intros a Ha k2 Hk2.
  apply real_mult_positive.
  - apply real_const_pos. apply Qlt_to_QltT. exact Ha.
  - apply real_const_pos. apply Qlt_to_QltT.
    apply (Qmult_lt_0_compat k2 (1 # 2)).
    + apply QltT_to_Qlt. exact Hk2.
    + change (Qlt 0 (1 # 2)). unfold Qlt. simpl. lia.
Qed.

Lemma b5dQ_lb_logerr_coord : forall (x : Real) (a : Q) (Ha : Qlt 0 a)
  (k2 : Q) (Hk2 : QltT 0 k2) (n : nat),
  projT1 (projT1 (b5dJ_LogErr_delta_exp x
                 (real_mult (real_const a) (real_const (Qmult k2 (1 # 2))))
                 (b5dQ_p_epsL_pos a Ha k2 Hk2))) n
  == Qmin (Qmult (Qinv 2) (projT1 (b5f_u x) n))
          (Qmult (Qmult (Qinv 2) (Qinv 2))
                 (Qmult (Qmult a (Qmult k2 (1 # 2)))
                        (Qmult (projT1 (b5f_u x) n) (projT1 (b5f_u x) n)))).
Proof.
  intros x a Ha k2 Hk2 n.
  change (projT1 (projT1 (b5dJ_log_diff_dx_exp (b5f_u x) (b5a_one_plus_sq_pos x)
                 (real_mult (real_const a) (real_const (Qmult k2 (1 # 2))))
                 (b5dQ_p_epsL_pos a Ha k2 Hk2))) n
  == Qmin (Qmult (Qinv 2) (projT1 (b5f_u x) n))
          (Qmult (Qmult (Qinv 2) (Qinv 2))
                 (Qmult (Qmult a (Qmult k2 (1 # 2)))
                        (Qmult (projT1 (b5f_u x) n) (projT1 (b5f_u x) n))))).
  change (projT1 (real_min
    (real_mult (real_inv_pos (real_plus real_one real_one) (b5dJ_two_pos_exp)) (b5f_u x))
    (real_mult
      (real_mult (real_inv_pos (real_plus real_one real_one) (b5dJ_two_pos_exp))
                 (real_inv_pos (real_plus real_one real_one) (b5dJ_two_pos_exp)))
      (real_mult (real_mult (real_const a) (real_const (Qmult k2 (1 # 2))))
                 (real_mult (b5f_u x) (b5f_u x))))) n
  == Qmin (Qmult (Qinv 2) (projT1 (b5f_u x) n))
          (Qmult (Qmult (Qinv 2) (Qinv 2))
                 (Qmult (Qmult a (Qmult k2 (1 # 2)))
                        (Qmult (projT1 (b5f_u x) n) (projT1 (b5f_u x) n))))).
  rewrite (real_min_proj
    (real_mult (real_inv_pos (real_plus real_one real_one) (b5dJ_two_pos_exp)) (b5f_u x))
    (real_mult
      (real_mult (real_inv_pos (real_plus real_one real_one) (b5dJ_two_pos_exp))
                 (real_inv_pos (real_plus real_one real_one) (b5dJ_two_pos_exp)))
      (real_mult (real_mult (real_const a) (real_const (Qmult k2 (1 # 2))))
                 (real_mult (b5f_u x) (b5f_u x)))) n).
  repeat (rewrite real_mult_proj || rewrite real_const_proj).
  cbn [projT1 real_inv_pos real_plus real_one real_const Nat.leb
       b5dJ_two_pos_exp].
  reflexivity.
Qed.

(* ============================================================ *)
(* helper 12：支严格 margin（floor-支；e := lb/2 线性）     *)
(* ============================================================ *)
Lemma b5dQ_p_branch_lt : forall (b f c : Q),
  Qle f b -> Qle c f -> Qlt 0 c ->
  Qlt (Qmult (Qmult c (1 # 2)) (1 # 2)) (b - Qmult c (1 # 2)).
Proof.
  intros b f c Hfb Hcf Hc.
  nra.
Qed.

Lemma b5dQ_p_q_scaled_le : forall (c m u : Q),
  Qle 0 c -> Qle 0 m -> Qle 1 u ->
  Qle (Qmult c m) (Qmult c (Qmult m (Qmult u u))).
Proof.
  intros c m u Hc0 Hm0 Hug.
  assert (Habs : Qle m (Qmult m (Qmult u u))).
  { apply b5dQ_p_q_mul_abs; [exact Hm0 | exact Hug]. }
  apply (Qle_trans (Qmult c m) (Qmult m c) (Qmult c (Qmult m (Qmult u u)))).
  - apply qeq_le. ring.
  - apply (Qle_trans (Qmult m c) (Qmult (Qmult m (Qmult u u)) c)
                     (Qmult c (Qmult m (Qmult u u)))).
    + apply (Qmult_le_compat_r m (Qmult m (Qmult u u)) c);
        [exact Habs | exact Hc0].
    + apply qeq_le. ring.
Qed.

(* ============================================================ *)
(* 件 3：b5dQ_lb_gdiff（δD2f L8 坐标层实施）                    *)
(* gdiff 体内：kL := k2·(1#2)；epsL := eps·real_const kL；δL := *)
(*   projT1 (LogErr x epsL …)；δg := min(min(δL·(1#12),         *)
(*   eps·real_const kL), (1#2))。坐标件 + Q 层（δL 坐标经         *)
(*   b5dQ_lb_logerr_coord 全展开）。                             *)
(* ============================================================ *)
Lemma b5dQ_lb_gdiff_coord : forall (q : Q) (Hq0 : Qle 0 q) (Hq1 : Qlt q 1)
  (x : Real) (Hxr : forall n : nat, QleT' (Qabs (projT1 x n)) q)
  (a : Q) (Ha : Qlt 0 a) (k2 k2p : Q) (Hk2 : QltT 0 k2) (Hk2p : QltT 0 k2p)
  (n : nat),
  projT1 (projT1 (b5dK_gdiff_pts_r_exp q Hq0 Hq1 x Hxr (real_const a)
                 (real_const_pos a (Qlt_to_QltT 0 a Ha))
                 k2 k2p Hk2 Hk2p)) n
  == Qmin (Qmin
      (Qmult (Qmin (Qmult (Qinv 2) (projT1 (b5f_u x) n))
                   (Qmult (Qmult (Qinv 2) (Qinv 2))
                          (Qmult (Qmult a (Qmult k2 (1 # 2)))
                                 (Qmult (projT1 (b5f_u x) n)
                                        (projT1 (b5f_u x) n)))))
             (1 # 12))
      (Qmult a (Qmult k2 (1 # 2))))
    (1 # 2).
Proof.
  intros q Hq0 Hq1 x Hxr a Ha k2 k2p Hk2 Hk2p n.
  change (projT1 (real_min (real_min
    (real_mult (projT1 (b5dJ_LogErr_delta_exp x
                 (real_mult (real_const a) (real_const (Qmult k2 (1 # 2))))
                 (b5dQ_p_epsL_pos a Ha k2 Hk2)))
               (real_const (1 # 12)))
    (real_mult (real_const a) (real_const (Qmult k2 (1 # 2)))))
    (real_const (1 # 2))) n
  == Qmin (Qmin
      (Qmult (Qmin (Qmult (Qinv 2) (projT1 (b5f_u x) n))
                   (Qmult (Qmult (Qinv 2) (Qinv 2))
                          (Qmult (Qmult a (Qmult k2 (1 # 2)))
                                 (Qmult (projT1 (b5f_u x) n)
                                        (projT1 (b5f_u x) n)))))
             (1 # 12))
      (Qmult a (Qmult k2 (1 # 2))))
    (1 # 2)).
  rewrite (real_min_proj
    (real_min
      (real_mult (projT1 (b5dJ_LogErr_delta_exp x
                   (real_mult (real_const a) (real_const (Qmult k2 (1 # 2))))
                   (b5dQ_p_epsL_pos a Ha k2 Hk2)))
                 (real_const (1 # 12)))
      (real_mult (real_const a) (real_const (Qmult k2 (1 # 2)))))
    (real_const (1 # 2)) n).
  rewrite (real_min_proj
    (real_mult (projT1 (b5dJ_LogErr_delta_exp x
                 (real_mult (real_const a) (real_const (Qmult k2 (1 # 2))))
                 (b5dQ_p_epsL_pos a Ha k2 Hk2)))
               (real_const (1 # 12)))
    (real_mult (real_const a) (real_const (Qmult k2 (1 # 2)))) n).
  rewrite (real_mult_proj
    (projT1 (b5dJ_LogErr_delta_exp x
                 (real_mult (real_const a) (real_const (Qmult k2 (1 # 2))))
                 (b5dQ_p_epsL_pos a Ha k2 Hk2)))
    (real_const (1 # 12)) n).
  rewrite (real_mult_proj (real_const a) (real_const (Qmult k2 (1 # 2))) n).
  rewrite (b5dQ_lb_logerr_coord x a Ha k2 Hk2 n).
  repeat (rewrite real_const_proj).
  reflexivity.
Qed.

(* ============================================================ *)
(* 件 3 主件：b5dQ_lb_gdiff                                     *)
(* ============================================================ *)
Lemma b5dQ_lb_gdiff : forall (q : Q) (Hq0 : Qle 0 q) (Hq1 : Qlt q 1)
  (x : Real) (Hxr : forall n : nat, QleT' (Qabs (projT1 x n)) q)
  (a : Q) (Ha : Qlt 0 a)
  (k2 k2p : Q) (Hk2 : QltT 0 k2) (Hk2p : QltT 0 k2p),
  real_lt (real_const (Qmult (Qmin (Qmin
            (Qmult (Qmin (1 # 2) (Qmult (1 # 4) (Qmult a (Qmult k2 (1 # 2)))))
                   (1 # 12))
            (Qmult a (Qmult k2 (1 # 2))))
          (1 # 2)) (1 # 2)))
    (projT1 (b5dK_gdiff_pts_r_exp q Hq0 Hq1 x Hxr (real_const a)
            (real_const_pos a (Qlt_to_QltT 0 a Ha)) k2 k2p Hk2 Hk2p)).
Proof.
  intros q Hq0 Hq1 x Hxr a Ha k2 k2p Hk2 Hk2p.
  set (m := Qmult a (Qmult k2 (1 # 2))).
  set (floorL := Qmin (1 # 2) (Qmult (1 # 4) m)).
  set (floorA := Qmult floorL (1 # 12)).
  set (floorB := m).
  set (c := Qmin (Qmin floorA floorB) (1 # 2)).
  set (lb := Qmult c (1 # 2)).
  set (e := Qmult lb (1 # 2)).
  assert (H12 : Qlt 0 (1 # 2)) by (change (Qlt 0 (1 # 2)); unfold Qlt; simpl; lia).
  assert (H14 : Qlt 0 (1 # 4)) by (change (Qlt 0 (1 # 4)); unfold Qlt; simpl; lia).
  assert (H112 : Qlt 0 (1 # 12)) by (change (Qlt 0 (1 # 12)); unfold Qlt; simpl; lia).
  assert (Hk2Q : Qlt 0 k2) by (apply QltT_to_Qlt; exact Hk2).
  assert (Hmpos : Qlt 0 m).
  { unfold m. apply (Qmult_lt_0_compat a (Qmult k2 (1 # 2))).
    - exact Ha.
    - apply (Qmult_lt_0_compat k2 (1 # 2)); [exact Hk2Q | exact H12]. }
  assert (HfloorLpos : Qlt 0 floorL).
  { unfold floorL. apply Q.min_glb_lt.
    - exact H12.
    - apply (Qmult_lt_0_compat (1 # 4) m); [exact H14 | exact Hmpos]. }
  assert (HfloorApos : Qlt 0 floorA).
  { unfold floorA. apply (Qmult_lt_0_compat floorL (1 # 12));
      [exact HfloorLpos | exact H112]. }
  assert (Hcpos : Qlt 0 c).
  { unfold c. apply Q.min_glb_lt.
    - apply Q.min_glb_lt; [exact HfloorApos | exact Hmpos].
    - exact H12. }
  assert (Hlbpos : Qlt 0 lb).
  { unfold lb. apply (Qmult_lt_0_compat c (1 # 2)); [exact Hcpos | exact H12]. }
  assert (Hepos : Qlt 0 e).
  { unfold e. apply (Qmult_lt_0_compat lb (1 # 2)); [exact Hlbpos | exact H12]. }
  assert (HcA : Qle c floorA).
  { unfold c. apply (Qle_trans (Qmin (Qmin floorA floorB) (1 # 2))
                               (Qmin floorA floorB) floorA).
    - apply Q.le_min_l.
    - apply Q.le_min_l. }
  assert (HcB : Qle c floorB).
  { unfold c. apply (Qle_trans (Qmin (Qmin floorA floorB) (1 # 2))
                               (Qmin floorA floorB) floorB).
    - apply Q.le_min_l.
    - apply Q.le_min_r. }
  assert (HcC : Qle c (1 # 2)).
  { unfold c. apply Q.le_min_r. }
  assert (HmL : Qle floorL (1 # 2)) by (unfold floorL; apply Q.le_min_l).
  assert (Hm2 : Qle floorL (Qmult (1 # 4) m)) by (unfold floorL; apply Q.le_min_r).
  unfold real_lt.
  exists e.
  split.
  { apply Qlt_to_QltT. exact Hepos. }
  { exists 0%nat.
    intros n Hn.
    apply Qlt_to_QltT.
    rewrite (b5dQ_lb_gdiff_coord q Hq0 Hq1 x Hxr a Ha k2 k2p Hk2 Hk2p n).
    rewrite b5dQ_p_qinv2sq.
    rewrite b5dQ_p_qinv2.
    cbn [projT1 real_const].
    set (u := projT1 (b5f_u x) n).
    assert (Hug : Qle 1 u) by (unfold u; apply b5dQ_p_u_ge1).
    assert (Hm0 : Qle 0 m) by (apply Qlt_le_weak; exact Hmpos).
    (* 内层 δL 坐标 ≥ floorL：min-glb 逐支 *)
    assert (HdL1 : Qle floorL (Qmult (1 # 2) u)).
    { apply (Qle_trans floorL (1 # 2) (Qmult (1 # 2) u)).
      - exact HmL.
      - nra. }
    assert (HdL2 : Qle floorL (Qmult (1 # 4) (Qmult m (Qmult u u)))).
    { apply (Qle_trans floorL (Qmult (1 # 4) m)
                       (Qmult (1 # 4) (Qmult m (Qmult u u)))).
      - exact Hm2.
      - apply b5dQ_p_q_scaled_le; [apply Qlt_le_weak; exact H14 | exact Hm0 | exact Hug]. }
    assert (HdL : Qle floorL
      (Qmin (Qmult (1 # 2) u)
            (Qmult (1 # 4) (Qmult m (Qmult u u))))).
    { apply b5dQ_p_min_glb_le; [exact HdL1 | exact HdL2]. }
    (* 三支 floor 事实 *)
    assert (FA : Qle floorA (Qmult (Qmin (Qmult (1 # 2) u)
            (Qmult (1 # 4) (Qmult m (Qmult u u)))) (1 # 12))).
    { unfold floorA.
      apply (Qmult_le_compat_r floorL
        (Qmin (Qmult (1 # 2) u) (Qmult (1 # 4) (Qmult m (Qmult u u))))
        (1 # 12)); [exact HdL | apply Qlt_le_weak; exact H112]. }
    assert (FB : Qle m (Qmult a (Qmult k2 (1 # 2)))).
    { unfold m. apply Qle_refl. }
    (* 三支严格 margin *)
    assert (S1 : Qlt e (Qminus (Qmult (Qmin (Qmult (1 # 2) u)
            (Qmult (1 # 4) (Qmult m (Qmult u u)))) (1 # 12)) lb)).
    { unfold e, lb.
      apply (b5dQ_p_branch_lt
               (Qmult (Qmin (Qmult (1 # 2) u)
                            (Qmult (1 # 4) (Qmult m (Qmult u u)))) (1 # 12))
               floorA c); [exact FA | exact HcA | exact Hcpos]. }
    assert (S2 : Qlt e (Qminus (Qmult a (Qmult k2 (1 # 2))) lb)).
    { unfold e, lb.
      apply (b5dQ_p_branch_lt (Qmult a (Qmult k2 (1 # 2))) m c);
        [exact FB | exact HcB | exact Hcpos]. }
    assert (S3 : Qlt e (Qminus (1 # 2) lb)).
    { unfold e, lb.
      apply (b5dQ_p_branch_lt (1 # 2) (1 # 2) c);
        [apply Qle_refl | exact HcC | exact Hcpos]. }
    (* 组装：X_n − lb 的 min 树分解（两级 Qmin 减 lb） *)
    rewrite (b5dQ_p_qmin_sub_r
      (Qmin (Qmult (Qmin (Qmult (1 # 2) u)
                         (Qmult (1 # 4)
                                (Qmult (Qmult a (Qmult k2 (1 # 2)))
                                       (Qmult u u)))) (1 # 12))
            (Qmult a (Qmult k2 (1 # 2))))
      (1 # 2) lb).
    rewrite (b5dQ_p_qmin_sub_r
      (Qmult (Qmin (Qmult (1 # 2) u)
                   (Qmult (1 # 4)
                          (Qmult (Qmult a (Qmult k2 (1 # 2)))
                                 (Qmult u u)))) (1 # 12))
      (Qmult a (Qmult k2 (1 # 2))) lb).
    apply Q.min_glb_lt.
    - apply Q.min_glb_lt; [exact S1 | exact S2].
    - exact S3.
  }
Qed.

(* ============================================================ *)
(* 件 4：b5dQ_lb_exp_part（δD2f L9 坐标层实施——S 叶@尾证书）    *)
(* exp_part 体内：Sx := b5a_S x；invM := real_inv_pos (1+|Sx|)； *)
(*   eps0 := eps·real_const (Qinv (Kvq q))·invM；δL := LogErr @  *)
(*   real_const b5j_kL；δlin := linear @ eps0；δ :=               *)
(*   min(min(δlin·(1#4), δL·(1#12)), (1#2))。                    *)
(* ============================================================ *)
Lemma b5dQ_p_eps0_pos : forall (q : Q) (Hq0 : Qle 0 q) (a : Q) (Ha : Qlt 0 a)
  (x : Real),
  real_lt real_zero (real_mult
    (real_mult (real_const a) (real_const (Qinv (b5j_Kvq q))))
    (real_inv_pos (real_plus real_one (real_abs (b5a_S x)))
                  (b5dK_real_abs_plus_one_pos_exp (b5a_S x)))).
Proof.
  intros q Hq0 a Ha x.
  apply real_mult_positive.
  - apply real_mult_positive.
    + apply real_const_pos. apply Qlt_to_QltT. exact Ha.
    + apply real_const_pos. apply Qlt_to_QltT.
      apply Qinv_lt_0_compat. exact (b5j_Kvq_pos q Hq0).
  - apply (real_inv_pos_pos (real_plus real_one (real_abs (b5a_S x)))
                            (b5dK_real_abs_plus_one_pos_exp (b5a_S x))).
Qed.

Lemma b5dQ_p_logerr_kL_coord : forall (x : Real) (n : nat),
  projT1 (projT1 (b5dJ_LogErr_delta_exp x (real_const b5j_kL)
                 (real_const_pos b5j_kL (Qlt_to_QltT 0 b5j_kL (QltT_to_Qlt 0 b5j_kL b5j_kL_posT))))) n
  == Qmin (Qmult (Qinv 2) (projT1 (b5f_u x) n))
          (Qmult (Qmult (Qinv 2) (Qinv 2))
                 (Qmult b5j_kL (Qmult (projT1 (b5f_u x) n)
                                      (projT1 (b5f_u x) n)))).
Proof.
  intros x n.
  change (projT1 (projT1 (b5dJ_log_diff_dx_exp (b5f_u x) (b5a_one_plus_sq_pos x)
                 (real_const b5j_kL)
                 (real_const_pos b5j_kL (Qlt_to_QltT 0 b5j_kL (QltT_to_Qlt 0 b5j_kL b5j_kL_posT))))) n
  == Qmin (Qmult (Qinv 2) (projT1 (b5f_u x) n))
          (Qmult (Qmult (Qinv 2) (Qinv 2))
                 (Qmult b5j_kL (Qmult (projT1 (b5f_u x) n)
                                      (projT1 (b5f_u x) n))))).
  change (projT1 (real_min
    (real_mult (real_inv_pos (real_plus real_one real_one) (b5dJ_two_pos_exp)) (b5f_u x))
    (real_mult
      (real_mult (real_inv_pos (real_plus real_one real_one) (b5dJ_two_pos_exp))
                 (real_inv_pos (real_plus real_one real_one) (b5dJ_two_pos_exp)))
      (real_mult (real_const b5j_kL) (real_mult (b5f_u x) (b5f_u x))))) n
  == Qmin (Qmult (Qinv 2) (projT1 (b5f_u x) n))
          (Qmult (Qmult (Qinv 2) (Qinv 2))
                 (Qmult b5j_kL (Qmult (projT1 (b5f_u x) n)
                                      (projT1 (b5f_u x) n))))).
  rewrite (real_min_proj
    (real_mult (real_inv_pos (real_plus real_one real_one) (b5dJ_two_pos_exp)) (b5f_u x))
    (real_mult
      (real_mult (real_inv_pos (real_plus real_one real_one) (b5dJ_two_pos_exp))
                 (real_inv_pos (real_plus real_one real_one) (b5dJ_two_pos_exp)))
      (real_mult (real_const b5j_kL) (real_mult (b5f_u x) (b5f_u x)))) n).
  repeat (rewrite real_mult_proj || rewrite real_const_proj).
  cbn [projT1 real_inv_pos real_plus real_one real_const Nat.leb
       b5dJ_two_pos_exp b5j_kL].
  reflexivity.
Qed.

(* ============================================================ *)
(* exp_part 坐标件（change 到 δ 显式树 + 投影 rewrite；S 原子    *)
(* 保原子；b5j_kL/Kvq-inv 闭式照抄）                            *)
(* ============================================================ *)
Lemma b5dQ_lb_exp_part_coord : forall (q : Q) (Hq0 : Qle 0 q) (Hq1 : Qlt q 1)
  (x : Real) (Hxr : forall n : nat, QleT' (Qabs (projT1 x n)) q)
  (a : Q) (Ha : Qlt 0 a) (n : nat),
  projT1 (projT1 (b5dK_exp_part_bound_closed_r_exp q Hq0 Hq1 x Hxr
                 (real_const a) (real_const_pos a (Qlt_to_QltT 0 a Ha)))) n
  == Qmin (Qmin
      (Qmult (Qmin (1 # 2)
                   (Qmult (Qmult (Qmult a (Qinv (b5j_Kvq q)))
                                 (Qinv (Qplus 1 (Qabs (projT1 (b5a_S x) n)))))
                          (1 # 4)))
             (1 # 4))
      (Qmult (Qmin (Qmult (Qinv 2) (projT1 (b5f_u x) n))
                   (Qmult (Qmult (Qinv 2) (Qinv 2))
                          (Qmult b5j_kL (Qmult (projT1 (b5f_u x) n)
                                               (projT1 (b5f_u x) n)))))
             (1 # 12)))
    (1 # 2).
Proof.
  intros q Hq0 Hq1 x Hxr a Ha n.
  set (K := Qinv (b5j_Kvq q)).
  set (eps0t := real_mult (real_mult (real_const a) (real_const K))
                  (real_inv_pos (real_plus real_one (real_abs (b5a_S x)))
                                (b5dK_real_abs_plus_one_pos_exp (b5a_S x)))).
  change (projT1 (real_min (real_min
    (real_mult (projT1 (b5dK_exp_minus_one_linear_closed_exp eps0t
                       (b5dQ_p_eps0_pos q Hq0 a Ha x)))
               (real_const (1 # 4)))
    (real_mult (projT1 (b5dJ_LogErr_delta_exp x (real_const b5j_kL)
                       (real_const_pos b5j_kL
                          (Qlt_to_QltT 0 b5j_kL (QltT_to_Qlt 0 b5j_kL b5j_kL_posT)))))
               (real_const (1 # 12))))
    (real_const (1 # 2))) n
  == Qmin (Qmin
      (Qmult (Qmin (1 # 2)
                   (Qmult (Qmult (Qmult a K) (Qinv (Qplus 1 (Qabs (projT1 (b5a_S x) n)))))
                          (1 # 4)))
             (1 # 4))
      (Qmult (Qmin (Qmult (Qinv 2) (projT1 (b5f_u x) n))
                   (Qmult (Qmult (Qinv 2) (Qinv 2))
                          (Qmult b5j_kL (Qmult (projT1 (b5f_u x) n)
                                               (projT1 (b5f_u x) n)))))
             (1 # 12)))
    (1 # 2)).
  rewrite (real_min_proj
    (real_min
      (real_mult (projT1 (b5dK_exp_minus_one_linear_closed_exp eps0t
                         (b5dQ_p_eps0_pos q Hq0 a Ha x)))
                 (real_const (1 # 4)))
      (real_mult (projT1 (b5dJ_LogErr_delta_exp x (real_const b5j_kL)
                         (real_const_pos b5j_kL
                            (Qlt_to_QltT 0 b5j_kL (QltT_to_Qlt 0 b5j_kL b5j_kL_posT)))))
                 (real_const (1 # 12))))
    (real_const (1 # 2)) n).
  rewrite (real_min_proj
    (real_mult (projT1 (b5dK_exp_minus_one_linear_closed_exp eps0t
                       (b5dQ_p_eps0_pos q Hq0 a Ha x)))
               (real_const (1 # 4)))
    (real_mult (projT1 (b5dJ_LogErr_delta_exp x (real_const b5j_kL)
                       (real_const_pos b5j_kL
                          (Qlt_to_QltT 0 b5j_kL (QltT_to_Qlt 0 b5j_kL b5j_kL_posT)))))
               (real_const (1 # 12))) n).
  rewrite (real_mult_proj
    (projT1 (b5dK_exp_minus_one_linear_closed_exp eps0t
            (b5dQ_p_eps0_pos q Hq0 a Ha x)))
    (real_const (1 # 4)) n).
  rewrite (real_mult_proj
    (projT1 (b5dJ_LogErr_delta_exp x (real_const b5j_kL)
            (real_const_pos b5j_kL
               (Qlt_to_QltT 0 b5j_kL (QltT_to_Qlt 0 b5j_kL b5j_kL_posT)))))
    (real_const (1 # 12)) n).
  rewrite (b5dQ_p_logerr_kL_coord x n).
  change (Qmin (Qmin
      (Qmult (projT1 (real_min (real_const (1 # 2))
                               (real_mult eps0t (real_const (1 # 4)))) n)
             (1 # 4))
      (Qmult (Qmin (Qmult (Qinv 2) (projT1 (b5f_u x) n))
                   (Qmult (Qmult (Qinv 2) (Qinv 2))
                          (Qmult b5j_kL (Qmult (projT1 (b5f_u x) n)
                                               (projT1 (b5f_u x) n)))))
             (1 # 12)))
    (1 # 2)
  == Qmin (Qmin
      (Qmult (Qmin (1 # 2)
                   (Qmult (Qmult (Qmult a K) (Qinv (Qplus 1 (Qabs (projT1 (b5a_S x) n)))))
                          (1 # 4)))
             (1 # 4))
      (Qmult (Qmin (Qmult (Qinv 2) (projT1 (b5f_u x) n))
                   (Qmult (Qmult (Qinv 2) (Qinv 2))
                          (Qmult b5j_kL (Qmult (projT1 (b5f_u x) n)
                                               (projT1 (b5f_u x) n)))))
             (1 # 12)))
    (1 # 2)).
  rewrite (real_min_proj (real_const (1 # 2)) (real_mult eps0t (real_const (1 # 4))) n).
  rewrite (real_mult_proj eps0t (real_const (1 # 4)) n).
  unfold eps0t, K.
  rewrite (real_mult_proj
    (real_mult (real_const a) (real_const (Qinv (b5j_Kvq q))))
    (real_inv_pos (real_plus real_one (real_abs (b5a_S x)))
                  (b5dK_real_abs_plus_one_pos_exp (b5a_S x))) n).
  repeat (rewrite real_mult_proj || rewrite real_const_proj).
  rewrite (b5dQ_p_invM_coord x n).
  cbn [projT1 real_inv_pos real_plus real_abs real_one real_const Nat.leb
       b5dK_real_abs_plus_one_pos_exp b5j_kL].
  reflexivity.
Qed.

(* ============================================================ *)
(* 件 4 主件：b5dQ_lb_exp_part（S 叶@尾证书；N := Nub）          *)
(* ============================================================ *)
Lemma b5dQ_lb_exp_part : forall (q : Q) (Hq0 : Qle 0 q) (Hq1 : Qlt q 1)
  (x : Real) (Hxr : forall n : nat, QleT' (Qabs (projT1 x n)) q)
  (a : Q) (Ha : Qlt 0 a)
  (Nub : nat)
  (Hcert : forall n : nat, (Nub <= n)%nat ->
           Qle (Qabs (projT1 (b5a_S x) n)) 2),
  real_lt (real_const (Qmult (Qmin (Qmin
            (Qmult (Qmin (1 # 2)
                         (Qmult (Qmult (Qmult a (Qinv (b5j_Kvq q))) (1 # 3)) (1 # 4)))
                   (1 # 4))
            (Qmult (Qmin (1 # 2) (Qmult (1 # 4) b5j_kL)) (1 # 12)))
          (1 # 2)) (1 # 2)))
    (projT1 (b5dK_exp_part_bound_closed_r_exp q Hq0 Hq1 x Hxr
            (real_const a) (real_const_pos a (Qlt_to_QltT 0 a Ha)))).
Proof.
  intros q Hq0 Hq1 x Hxr a Ha Nub Hcert.
  set (K := Qinv (b5j_Kvq q)).
  set (floorL2 := Qmult (Qmult (Qmult a K) (1 # 3)) (1 # 4)).
  set (floorL := Qmin (1 # 2) floorL2).
  set (floorA := Qmult floorL (1 # 4)).
  set (floorD2 := Qmult (1 # 4) b5j_kL).
  set (floorD := Qmin (1 # 2) floorD2).
  set (floorB := Qmult floorD (1 # 12)).
  set (c := Qmin (Qmin floorA floorB) (1 # 2)).
  set (lb := Qmult c (1 # 2)).
  set (e := Qmult lb (1 # 2)).
  assert (H12 : Qlt 0 (1 # 2)) by (change (Qlt 0 (1 # 2)); unfold Qlt; simpl; lia).
  assert (H14 : Qlt 0 (1 # 4)) by (change (Qlt 0 (1 # 4)); unfold Qlt; simpl; lia).
  assert (H13 : Qlt 0 (1 # 3)) by (change (Qlt 0 (1 # 3)); unfold Qlt; simpl; lia).
  assert (H112 : Qlt 0 (1 # 12)) by (change (Qlt 0 (1 # 12)); unfold Qlt; simpl; lia).
  assert (HKpos : Qlt 0 K).
  { unfold K. apply Qinv_lt_0_compat. exact (b5j_Kvq_pos q Hq0). }
  assert (HkLposQ : Qlt 0 b5j_kL) by (apply QltT_to_Qlt; exact b5j_kL_posT).
  assert (HmL2pos : Qlt 0 floorL2).
  { unfold floorL2. apply (Qmult_lt_0_compat (Qmult (Qmult a K) (1 # 3)) (1 # 4)).
    - apply (Qmult_lt_0_compat (Qmult a K) (1 # 3)).
      + apply (Qmult_lt_0_compat a K); [exact Ha | exact HKpos].
      + exact H13.
    - exact H14. }
  assert (HfloorLpos : Qlt 0 floorL).
  { unfold floorL. apply Q.min_glb_lt; [exact H12 | exact HmL2pos]. }
  assert (HfloorApos : Qlt 0 floorA).
  { unfold floorA. apply (Qmult_lt_0_compat floorL (1 # 4));
      [exact HfloorLpos | exact H14]. }
  assert (HfloorD2pos : Qlt 0 floorD2).
  { unfold floorD2. apply (Qmult_lt_0_compat (1 # 4) b5j_kL);
      [exact H14 | exact HkLposQ]. }
  assert (HfloorDpos : Qlt 0 floorD).
  { unfold floorD. apply Q.min_glb_lt; [exact H12 | exact HfloorD2pos]. }
  assert (HfloorBpos : Qlt 0 floorB).
  { unfold floorB. apply (Qmult_lt_0_compat floorD (1 # 12));
      [exact HfloorDpos | exact H112]. }
  assert (Hcpos : Qlt 0 c).
  { unfold c. apply Q.min_glb_lt.
    - apply Q.min_glb_lt; [exact HfloorApos | exact HfloorBpos].
    - exact H12. }
  assert (Hlbpos : Qlt 0 lb).
  { unfold lb. apply (Qmult_lt_0_compat c (1 # 2)); [exact Hcpos | exact H12]. }
  assert (Hepos : Qlt 0 e).
  { unfold e. apply (Qmult_lt_0_compat lb (1 # 2)); [exact Hlbpos | exact H12]. }
  assert (HcA : Qle c floorA).
  { unfold c. apply (Qle_trans (Qmin (Qmin floorA floorB) (1 # 2))
                               (Qmin floorA floorB) floorA).
    - apply Q.le_min_l.
    - apply Q.le_min_l. }
  assert (HcB : Qle c floorB).
  { unfold c. apply (Qle_trans (Qmin (Qmin floorA floorB) (1 # 2))
                               (Qmin floorA floorB) floorB).
    - apply Q.le_min_l.
    - apply Q.le_min_r. }
  assert (HcC : Qle c (1 # 2)).
  { unfold c. apply Q.le_min_r. }
  assert (HfL1 : Qle floorL (1 # 2)) by (unfold floorL; apply Q.le_min_l).
  assert (HfL2 : Qle floorL floorL2) by (unfold floorL; apply Q.le_min_r).
  assert (HfD1 : Qle floorD (1 # 2)) by (unfold floorD; apply Q.le_min_l).
  assert (HfD2 : Qle floorD floorD2) by (unfold floorD; apply Q.le_min_r).
  unfold real_lt.
  exists e.
  split.
  { apply Qlt_to_QltT. exact Hepos. }
  { exists Nub.
    intros n Hn.
    apply Qlt_to_QltT.
    rewrite (b5dQ_lb_exp_part_coord q Hq0 Hq1 x Hxr a Ha n).
    rewrite b5dQ_p_qinv2sq.
    rewrite b5dQ_p_qinv2.
    cbn [projT1 real_const].
    set (Sn := projT1 (b5a_S x) n).
    set (u := projT1 (b5f_u x) n).
    assert (Hug : Qle 1 u) by (unfold u; apply b5dQ_p_u_ge1).
    assert (HcSn : Qle (Qabs Sn) 2) by (exact (Hcert n (NatLe_drop Nub n Hn))).
    (* invM 坐标 ≥ 1#3（|Sn| ≤ 2 尾证书封底） *)
    assert (Hinv : Qle (1 # 3) (Qinv (Qplus 1 (Qabs Sn)))).
    { rewrite <- (b5dQ_p_qinv3).
      apply b5dQ_p_qinv_le_mono.
      - apply (Qlt_le_trans 0 1 (Qplus 1 (Qabs Sn))).
        + apply (QltT_to_Qlt 0 1 qltT_0_1).
        + apply (Qplus_le_compat 1 1 0 (Qabs Sn));
            [apply Qle_refl | apply Qabs_nonneg].
      - exact H13.
      - nra. }
    (* 内层 δlin 坐标 ≥ floorL（min-glb 逐支） *)
    assert (He0 : Qle (Qmult (Qmult a K) (1 # 3))
                     (Qmult (Qmult a K) (Qinv (Qplus 1 (Qabs Sn))))).
    { apply (Qle_trans (Qmult (Qmult a K) (1 # 3)) (Qmult (1 # 3) (Qmult a K))
                       (Qmult (Qmult a K) (Qinv (Qplus 1 (Qabs Sn))))).
      - apply qeq_le. ring.
      - apply (Qle_trans (Qmult (1 # 3) (Qmult a K))
                         (Qmult (Qinv (Qplus 1 (Qabs Sn))) (Qmult a K))
                         (Qmult (Qmult a K) (Qinv (Qplus 1 (Qabs Sn))))).
        + apply (Qmult_le_compat_r (1 # 3) (Qinv (Qplus 1 (Qabs Sn)))
                                   (Qmult a K));
            [ exact Hinv | apply Qlt_le_weak; exact (Qmult_lt_0_compat a K Ha HKpos) ].
        + apply qeq_le. ring. }
    assert (HdL2 : Qle floorL2
        (Qmult (Qmult (Qmult a K) (Qinv (Qplus 1 (Qabs Sn)))) (1 # 4))).
    { unfold floorL2.
      apply (Qmult_le_compat_r (Qmult (Qmult a K) (1 # 3))
                               (Qmult (Qmult a K) (Qinv (Qplus 1 (Qabs Sn))))
                               (1 # 4));
        [ exact He0 | apply Qlt_le_weak; exact H14 ]. }
    assert (HdL : Qle floorL
        (Qmin (1 # 2)
              (Qmult (Qmult (Qmult a K) (Qinv (Qplus 1 (Qabs Sn)))) (1 # 4)))).
    { apply b5dQ_p_min_glb_le; [exact HfL1 | ].
      apply (Qle_trans floorL floorL2
             (Qmult (Qmult (Qmult a K) (Qinv (Qplus 1 (Qabs Sn)))) (1 # 4)));
        [exact HfL2 | exact HdL2]. }
    (* 内层 δL 坐标 ≥ floorD（u ≥ 1 逐支） *)
    assert (Hq1u : Qle (1 # 2) (Qmult (1 # 2) u)) by nra.
    assert (Hq2u : Qle (Qmult (1 # 4) b5j_kL)
                     (Qmult (1 # 4) (Qmult b5j_kL (Qmult u u)))).
    { apply b5dQ_p_q_scaled_le;
        [ apply Qlt_le_weak; exact H14 | apply Qlt_le_weak; exact HkLposQ | exact Hug ]. }
    assert (HfD : Qle floorD
        (Qmin (Qmult (1 # 2) u)
              (Qmult (1 # 4) (Qmult b5j_kL (Qmult u u))))).
    { apply b5dQ_p_min_glb_le.
      - apply (Qle_trans floorD (1 # 2) (Qmult (1 # 2) u));
          [exact HfD1 | exact Hq1u].
      - apply (Qle_trans floorD floorD2
                         (Qmult (1 # 4) (Qmult b5j_kL (Qmult u u))));
          [exact HfD2 | exact Hq2u]. }
    (* 两支 floor 事实（A/B 支） *)
    assert (FA : Qle floorA (Qmult (Qmin (1 # 2)
              (Qmult (Qmult (Qmult a K) (Qinv (Qplus 1 (Qabs Sn)))) (1 # 4)))
              (1 # 4))).
    { unfold floorA.
      apply (Qmult_le_compat_r floorL
        (Qmin (1 # 2)
              (Qmult (Qmult (Qmult a K) (Qinv (Qplus 1 (Qabs Sn)))) (1 # 4)))
        (1 # 4)); [exact HdL | apply Qlt_le_weak; exact H14]. }
    assert (FB : Qle floorB
        (Qmult (Qmin (Qmult (1 # 2) u)
                     (Qmult (1 # 4) (Qmult b5j_kL (Qmult u u)))) (1 # 12))).
    { unfold floorB.
      apply (Qmult_le_compat_r floorD
        (Qmin (Qmult (1 # 2) u) (Qmult (1 # 4) (Qmult b5j_kL (Qmult u u))))
        (1 # 12)); [exact HfD | apply Qlt_le_weak; exact H112]. }
    (* 三支严格 margin *)
    assert (S1 : Qlt e (Qminus (Qmult (Qmin (1 # 2)
              (Qmult (Qmult (Qmult a K) (Qinv (Qplus 1 (Qabs Sn)))) (1 # 4)))
              (1 # 4)) lb)).
    { unfold e, lb.
      apply (b5dQ_p_branch_lt
               (Qmult (Qmin (1 # 2)
                     (Qmult (Qmult (Qmult a K) (Qinv (Qplus 1 (Qabs Sn)))) (1 # 4)))
                      (1 # 4))
               floorA c); [exact FA | exact HcA | exact Hcpos]. }
    assert (S2 : Qlt e (Qminus (Qmult (Qmin (Qmult (1 # 2) u)
                     (Qmult (1 # 4) (Qmult b5j_kL (Qmult u u)))) (1 # 12)) lb)).
    { unfold e, lb.
      apply (b5dQ_p_branch_lt
               (Qmult (Qmin (Qmult (1 # 2) u)
                            (Qmult (1 # 4) (Qmult b5j_kL (Qmult u u)))) (1 # 12))
               floorB c); [exact FB | exact HcB | exact Hcpos]. }
    assert (S3 : Qlt e (Qminus (1 # 2) lb)).
    { unfold e, lb.
      apply (b5dQ_p_branch_lt (1 # 2) (1 # 2) c);
        [apply Qle_refl | exact HcC | exact Hcpos]. }
    (* 组装：X_n − lb 的 min 树分解（两级 Qmin 减 lb） *)
    rewrite (b5dQ_p_qmin_sub_r
      (Qmin (Qmult (Qmin (1 # 2)
                   (Qmult (Qmult (Qmult a (Qinv (b5j_Kvq q)))
                                 (Qinv (Qplus 1 (Qabs Sn)))) (1 # 4))) (1 # 4))
            (Qmult (Qmin (Qmult (1 # 2) u)
                         (Qmult (1 # 4) (Qmult b5j_kL (Qmult u u)))) (1 # 12)))
      (1 # 2) lb).
    rewrite (b5dQ_p_qmin_sub_r
      (Qmult (Qmin (1 # 2)
                   (Qmult (Qmult (Qmult a (Qinv (b5j_Kvq q)))
                                 (Qinv (Qplus 1 (Qabs Sn)))) (1 # 4))) (1 # 4))
      (Qmult (Qmin (Qmult (1 # 2) u)
                   (Qmult (1 # 4) (Qmult b5j_kL (Qmult u u)))) (1 # 12)) lb).
    apply Q.min_glb_lt.
    - apply Q.min_glb_lt; [exact S1 | exact S2].
    - exact S3.
  }
Qed.

(* ============================================================ *)
(* end sc2_b5a_item27_p2_lbLog.v · P2 批           *)
(* ============================================================ *)

(* ===== 段 P3（证书族 C1-C5 + glue G1-G9 + Q 层小件，17 Lemma）===== *)

(* ============================================================ *)
(* §0 小件（Q 层正性证书；b5dQ_ 独占；全部真 Qed）              *)
(* ============================================================ *)

(* QltT 0 (1#4)（C1 的 real_eq 实例 eps 证书） *)
Lemma b5dQ_Hq14T : QltT 0 (1 # 4).
Proof. apply Qlt_to_QltT. unfold Qlt. simpl. lia. Qed.

(* QltT 0 1（C3 的 real_eq 实例 eps 证书） *)
Lemma b5dQ_Hq1T : QltT 0 1.
Proof. apply Qlt_to_QltT. unfold Qlt. simpl. lia. Qed.

(* Qlt 0 (1#4)（q_abs_gt_neg 系引理用） *)
Lemma b5dQ_Hq14 : Qlt 0 (1 # 4).
Proof. unfold Qlt. simpl. lia. Qed.

(* ============================================================ *)
(* G2 b5dQ_S_tk0_eq_one：S(t_0) == 1 实层桥（k=0 支证书的基底） *)
(*   语句 = 设计 §4 G2 行 + 进度 §4.1（t_0 := tkq q M 0）。      *)
(*   链：b5dL_tkq_0（Qeq t_0 0）+ b5dH_real_const_qeq +          *)
(*     b5m_S_wd（根 L86539）+ item8 b5d4_S_const0_eq_one +       *)
(*     real_eq_trans。                                           *)
(* ============================================================ *)
Lemma b5dQ_S_tk0_eq_one : forall (q : Q) (M : nat),
  real_eq (b5a_S (real_const (b5dL_tkq q M 0))) real_one.
Proof.
  intros q M.
  apply (real_eq_trans _ (b5a_S (real_const 0)) _).
  - apply b5m_S_wd.
    apply b5dH_real_const_qeq.
    exact (b5dL_tkq_0 q M).
  - exact b5d4_S_const0_eq_one.
Qed.

(* ============================================================ *)
(* Q 层内核：p == 1 ∧ |x − p| < 1/4 ⟹ Qle (1#2) x               *)
(*   （C1 尾界：同构 item8 b5d4_q_lb_half 结构，eps := 1/4， *)
(*     先经 Qlt_minus_iff 得 3/4 < x 再 Qle (1#2) ≤ 3/4 传递）    *)
(* ============================================================ *)
Lemma b5dQ_q_close_one_lb : forall (x p : Q),
  p == 1 -> Qlt (Qabs (x - p)) (1 # 4) -> Qle (1 # 2) x.
Proof.
  intros x p Hp H.
  setoid_rewrite Hp in H.
  assert (H34 : Qlt (3 # 4) x).
  { apply (proj2 (Qlt_minus_iff (3 # 4) x)).
    setoid_replace (x - (3 # 4)) with ((x - 1) - - (1 # 4)) by ring.
    apply (proj1 (Qlt_minus_iff (- (1 # 4)) (x - 1))).
    apply (q_abs_gt_neg (x - 1) (1 # 4) b5dQ_Hq14). exact H. }
  apply (Qle_trans (1 # 2) (3 # 4) x).
  - apply Qlt_le_weak. unfold Qlt. simpl. lia.
  - apply Qlt_le_weak. exact H34.
Qed.

(* ============================================================ *)
(* C1 b5dQ_S_lb_tail_k0：k=0 支 S 下界尾证书（cA := 1/2 直写）  *)
(*   语句 = 设计 §4 C1 行（sigT N (N≤n)%nat 尾 Qle (1#2)）。     *)
(*   证法 = G2 @ eps := 1/4（|S_n − 1| < 1/4 ⟹ S_n > 3/4 ≥ 1/2）*)
(*   + 经 b5dQ_q_close_one_lb。                               *)
(* ============================================================ *)
Lemma b5dQ_S_lb_tail_k0 : forall (q : Q) (M : nat),
  sigT (fun N : nat => forall n : nat, (N <= n)%nat ->
    Qle (1 # 2) (projT1 (b5a_S (real_const (b5dL_tkq q M 0))) n)).
Proof.
  intros q M.
  destruct (b5dQ_S_tk0_eq_one q M (1 # 4) b5dQ_Hq14T) as [N HN].
  exists N.
  intros n Hn.
  apply (b5dQ_q_close_one_lb (projT1 (b5a_S (real_const (b5dL_tkq q M 0))) n)
                             (projT1 real_one n)).
  - cbn [projT1 real_one]. reflexivity.
  - apply QltT_to_Qlt. exact (HN n (NatLe_lift _ _ Hn)).
Qed.

(* ============================================================ *)
(* C3 b5dQ_S_ub_tail_k0：k=0 支 S 上界尾证书（M_S := 2 直写）   *)
(*   语句 = 设计 §4 C3 行。                                     *)
(*   证法 = G2 @ eps := 1（|S_n − 1| < 1 ⟹ 0 < S_n < 2 ⟹        *)
(*     |S_n| ≤ 2）+ item8 b5d4_q_ub_two。                  *)
(* ============================================================ *)
Lemma b5dQ_S_ub_tail_k0 : forall (q : Q) (M : nat),
  sigT (fun N : nat => forall n : nat, (N <= n)%nat ->
    Qle (Qabs (projT1 (b5a_S (real_const (b5dL_tkq q M 0))) n)) 2).
Proof.
  intros q M.
  destruct (b5dQ_S_tk0_eq_one q M 1 b5dQ_Hq1T) as [N HN].
  exists N.
  intros n Hn.
  apply (b5d4_q_ub_two (projT1 (b5a_S (real_const (b5dL_tkq q M 0))) n)
                       (projT1 real_one n)).
  - cbn [projT1 real_one]. reflexivity.
  - apply QltT_to_Qlt. exact (HN n (NatLe_lift _ _ Hn)).
Qed.

(* ============================================================ *)
(* G9 b5dQ_S_ub_tail_restate：NatLe 形尾 → (N≤n)%nat 形重述 +    *)
(*   Qle 1 弱化到 Qle (1#2)（b5a_S_ge_one 输出侧的通用 glue；    *)
(*   设计 §4 G9 行：C2 的 lb 尾证书直用）。                      *)
(* ============================================================ *)
Lemma b5dQ_S_ub_tail_restate : forall (u : nat -> Q),
  sigT (fun N : nat => forall n : nat, NatLe N n -> Qle 1 (u n)) ->
  sigT (fun N : nat => forall n : nat, (N <= n)%nat -> Qle (1 # 2) (u n)).
Proof.
  intros u [N HN].
  exists N.
  intros n Hn.
  apply (Qle_trans (1 # 2) 1 (u n)).
  - apply Qlt_le_weak. unfold Qlt. simpl. lia.
  - exact (HN n (NatLe_lift _ _ Hn)).
Qed.

(* ============================================================ *)
(* C2 b5dQ_S_lb_tail_kS：k≥1 支 S 下界尾证书（cA := 1/2 直写）  *)
(*   语句 = 设计 §4 C2 行（0<q ∧ 0<M ∧ 0<k ⟹ sigT N 尾           *)
(*     Qle (1#2) (S(real_const t_k))；0<t_k 由 tkq_pos 内取）。  *)
(*   证法 = b5a_S_ge_one（根 L84807）@ real_const_pos_f1 +       *)
(*     G9（NatLe 重述 + 1 → 1/2 弱化）。                        *)
(* ============================================================ *)
Lemma b5dQ_S_lb_tail_kS : forall (q : Q) (M k : nat),
  Qlt 0 q -> (0 < M)%nat -> (0 < k)%nat ->
  sigT (fun N : nat => forall n : nat, (N <= n)%nat ->
    Qle (1 # 2) (projT1 (b5a_S (real_const (b5dL_tkq q M k))) n)).
Proof.
  intros q M k Hq0 HM Hk0.
  apply (b5dQ_S_ub_tail_restate
           (fun n : nat => projT1 (b5a_S (real_const (b5dL_tkq q M k))) n)).
  apply b5a_S_ge_one.
  apply real_const_pos_f1.
  exact (b5dL_tkq_pos q M k Hq0 HM Hk0).
Qed.

(* ============================================================ *)
(* C4 b5dQ_S_ub_tail_kS：k≥1 支 S 上界尾证书（M_S := 2 直写）   *)
(*   语句 = 设计 §4 C4 行（0<q ∧ q<1 ∧ 0<M ∧ 0<k ∧ k≤M ⟹        *)
(*     sigT N 尾 Qle |S(real_const t_k)| 2；0<t_k/t_k<1 由       *)
(*     tkq_pos/tkq_lt1 内取）。                                 *)
(*   证法 = item15 b5dE_S_ub_tail_q @ q := tkq 直供（(N≤n)%nat  *)
(*     形直供，零 glue）。                                      *)
(* ============================================================ *)
Lemma b5dQ_S_ub_tail_kS : forall (q : Q) (M k : nat),
  Qlt 0 q -> Qlt q 1 -> (0 < M)%nat -> (0 < k)%nat -> (k <= M)%nat ->
  sigT (fun N : nat => forall n : nat, (N <= n)%nat ->
    Qle (Qabs (projT1 (b5a_S (real_const (b5dL_tkq q M k))) n)) 2).
Proof.
  intros q M k Hq0 Hq1 HM Hk0 HkM.
  apply (b5dE_S_ub_tail_q (b5dL_tkq q M k)).
  - exact (b5dL_tkq_pos q M k Hq0 HM Hk0).
  - exact (b5dL_tkq_lt1 q M k (b5dH_q_pos_le q Hq0) HM HkM Hq1).
Qed.

(* ============================================================ *)
(* C5 b5dQ_sincos_all_k：sin/cos 界全 n 证书（HMs_all/HMc_all   *)
(*   实例，Ms := Mc := 1）——进度 §4.1 草案（cos 对应式并入 And） *)
(*   语句：0<q ∧ q<1 ∧ 0<M ∧ k≤M ⟹                             *)
(*     And (∀n Qle |sin_partial n (arctan_partial n t_k_n)| 1)  *)
(*         (∀n Qle |cos_partial n (arctan_partial n t_k_n)| 1)  *)
(*   证法 = item6 M4a/M4b @ x := real_const t_k + item22         *)
(*     b5dL_tkC（域证书）直接应用（全 n 零分支）。                  *)
(* ============================================================ *)
Lemma b5dQ_sincos_all_k : forall (q : Q) (Hq0 : Qlt 0 q) (Hq1 : Qlt q 1)
  (M : nat) (k : nat), (0 < M)%nat -> (k <= M)%nat ->
  And (forall n : nat,
         QleT' (Qabs (sin_partial n (arctan_partial n
                (projT1 (real_const (b5dL_tkq q M k)) n)))) 1)
      (forall n : nat,
         QleT' (Qabs (cos_partial n (arctan_partial n
                (projT1 (real_const (b5dL_tkq q M k)) n)))) 1).
Proof.
  intros q Hq0 Hq1 M k HM Hk.
  split.
  - intro n.
    exact (Qle_to_QleT' _ _ (b5d2_sinA_abs_le1 (real_const (b5dL_tkq q M k))
                              (b5dL_tkC q Hq0 Hq1 M k HM Hk) n)).
  - intro n.
    exact (Qle_to_QleT' _ _ (b5d2_cosA_abs_le1 (real_const (b5dL_tkq q M k))
                              (b5dL_tkC q Hq0 Hq1 M k HM Hk) n)).
Qed.

(* ============================================================ *)
(* G1 b5dQ_tkq_Hxr：网格点 t_k 的 Hxr 形逐点界（J-mod 实例的    *)
(*   r := q 侧证书）——进度 §4.1 G1 语句逐字。                  *)
(*   语句：Qle 0 q ∧ 0<M ∧ k≤M ⟹ ∀n QleT' |t_k| q。             *)
(*   证法 = b5c_const_unit 模式：Qle_to_QleT' + real_const_proj  *)
(*     + Qabs_pos（tkq_nonneg）+ tkq_le_q。                     *)
(* ============================================================ *)
Lemma b5dQ_tkq_Hxr : forall (q : Q) (M k : nat),
  Qle 0 q -> (0 < M)%nat -> (k <= M)%nat ->
  forall n : nat, QleT' (Qabs (projT1 (real_const (b5dL_tkq q M k)) n)) q.
Proof.
  intros q M k Hq0 HM Hk n.
  apply Qle_to_QleT'.
  rewrite (real_const_proj (b5dL_tkq q M k) n).
  apply (Qle_trans _ (b5dL_tkq q M k) _).
  - apply qeq_imp_qle. apply (Qabs_pos (b5dL_tkq q M k)).
    exact (b5dL_tkq_nonneg q M k Hq0 HM).
  - exact (b5dL_tkq_le_q q M k Hq0 HM Hk).
Qed.

(* ============================================================ *)
(* G3 b5dQ_xph_unit：t_k + η（η := q/M）的单位证书（J-mod 实例  *)
(*   的 Hxh 侧：real_plus (real_const t_k) (real_const η)）      *)
(*   语句 = 设计 §4 G3 行（0<q ∧ q<1 ∧ 0<M ∧ k<M ⟹ cw_unit）。   *)
(*   证法 = 坐标桥：t_k + η == t_{S k}（tkq_succ 反向）+          *)
(*     |t_{S k}| == t_{S k}（tkq_nonneg）+ t_{S k} ≤ q ≤ 1       *)
(*     （tkq_le1，S k ≤ M 由 k < M 经 lia）。                   *)
(* ============================================================ *)
Lemma b5dQ_xph_unit : forall (q : Q) (M k : nat),
  Qlt 0 q -> Qlt q 1 -> (0 < M)%nat -> (k < M)%nat ->
  cw_unit (real_plus (real_const (b5dL_tkq q M k))
                     (real_const (b5dL_qdiv q M))).
Proof.
  intros q M k Hq0 Hq1 HM Hk.
  unfold cw_unit.
  intro n.
  apply Qle_to_QleT'.
  rewrite (real_plus_proj (real_const (b5dL_tkq q M k)) (real_const (b5dL_qdiv q M)) n).
  rewrite (real_const_proj (b5dL_tkq q M k) n).
  rewrite (real_const_proj (b5dL_qdiv q M) n).
  rewrite <- (b5dL_tkq_succ q M k HM).
  apply (Qle_trans _ (b5dL_tkq q M (Datatypes.S k)) _).
  - apply qeq_imp_qle. apply (Qabs_pos (b5dL_tkq q M (Datatypes.S k))).
    exact (b5dL_tkq_nonneg q M (Datatypes.S k) (b5dH_q_pos_le q Hq0) HM).
  - apply (b5dL_tkq_le1 q M (Datatypes.S k) (b5dH_q_pos_le q Hq0)
                        (b5dH_q_lt1_le q Hq1) HM).
    lia.
Qed.

(* ============================================================ *)
(* G4 b5dQ_eps_shares_pos：两 eps 份额的 Q 正性（J-mod 实例的   *)
(*   eps := real_const (epsQ/(2q)) 与 eps' := real_const         *)
(*   (epsQ1 M epsQ) 侧）——设计 §4 G4 行（Qlt 对；QltT 变体与    *)
(*   real_lt real_zero (real_const ·) 证书为取用侧 1 行派生：     *)
(*   Qlt_to_QltT + 根 real_const_pos（或 real_const_pos_f1）。   *)
(*   证法：Qmult/Qinv 正性（item22 b5dL_two_q_pos 同构）+        *)
(*     直接应用 item22 b5dL_epsQ1_pos。                             *)
(* ============================================================ *)
Lemma b5dQ_eps_shares_pos : forall (q epsQ : Q) (M : nat),
  Qlt 0 q -> Qlt 0 epsQ -> (0 < M)%nat ->
  And (QltT 0 (epsQ / (2 * q))) (QltT 0 (b5dL_epsQ1 M epsQ)).
Proof.
  intros q epsQ M Hq0 Heps HM.
  split.
  - apply Qlt_to_QltT. unfold Qdiv.
    apply (Qmult_lt_0_compat epsQ (Qinv (2 * q))).
    + exact Heps.
    + apply Qinv_lt_0_compat. exact (b5dL_two_q_pos q Hq0).
  - exact (Qlt_to_QltT _ _ (b5dL_epsQ1_pos epsQ M Heps HM)).
Qed.

(* ============================================================ *)
(* G5 b5dQ_rhs_bk：C5 结论 RHS（eps·|h| + eps' 实例）==          *)
(*   real_const (b5dL_bk q M epsQ k) 的 real_eq 桥（Hstep 形     *)
(*   RHS 侧）——设计 §4 G5 行 + §2.4 bk 分解核对。              *)
(*   链：b5dL_abs_const（|η| == real_const (Qabs η)）+ Qabs_pos  *)
(*     （η ≥ 0）+ b5dH_real_const_qeq + b5dL_mult_const +        *)
(*     RealSetoid 相容 + b5dH_plus_const_eq + bk/epsQ1 定义性    *)
(*     （real_eq_refl）。                                  *)
(* ============================================================ *)
Lemma b5dQ_rhs_bk : forall (q : Q) (M k : nat) (epsQ : Q),
  Qlt 0 q -> (0 < M)%nat ->
  real_eq (real_plus (real_mult (real_const (epsQ / (2 * q)))
                                (real_abs (real_const (b5dL_qdiv q M))))
                     (real_const (b5dL_epsQ1 M epsQ)))
          (real_const (b5dL_bk q M epsQ k)).
Proof.
  intros q M k epsQ Hq0 HM.
  (* η ≥ 0（η := qdiv q M） *)
  assert (Heta0 : Qle 0 (b5dL_qdiv q M)).
  { unfold b5dL_qdiv. unfold Qdiv.
    apply Qmult_le_0_compat.
    - apply Qlt_le_weak. exact Hq0.
    - apply Qinv_le_0_compat. apply Qlt_le_weak.
      destruct M as [| m]; [exfalso; lia | exact (b5dL_lift_pos2 m)]. }
  (* |η| == η *)
  assert (Heta : real_eq (real_abs (real_const (b5dL_qdiv q M)))
                         (real_const (b5dL_qdiv q M))).
  { apply (real_eq_trans _ (real_const (Qabs (b5dL_qdiv q M))) _).
    - exact (b5dL_abs_const (b5dL_qdiv q M)).
    - apply b5dH_real_const_qeq.
      apply (Qabs_pos (b5dL_qdiv q M)). exact Heta0. }
  (* (epsQ/(2q))·|η| == real_const ((epsQ/(2q))·η) *)
  assert (Hm : real_eq
    (real_mult (real_const (epsQ / (2 * q)))
               (real_abs (real_const (b5dL_qdiv q M))))
    (real_const ((epsQ / (2 * q)) * (b5dL_qdiv q M)))).
  { apply (real_eq_trans _ (real_mult (real_const (epsQ / (2 * q)))
                                      (real_const (b5dL_qdiv q M))) _).
    - apply (RealSetoid.real_eq_mult_compat
               (real_const (epsQ / (2 * q)))
               (real_abs (real_const (b5dL_qdiv q M)))
               (real_const (epsQ / (2 * q)))
               (real_const (b5dL_qdiv q M)));
        [ apply real_eq_refl | exact Heta ].
    - exact (b5dL_mult_const (epsQ / (2 * q)) (b5dL_qdiv q M)). }
  (* + real_const epsQ1；再 + 桥 == real_const (bk)（定义性） *)
  apply (real_eq_trans _
           (real_plus (real_const ((epsQ / (2 * q)) * (b5dL_qdiv q M)))
                      (real_const (b5dL_epsQ1 M epsQ))) _).
  - apply (RealSetoid.real_eq_plus_compat
             (real_mult (real_const (epsQ / (2 * q)))
                        (real_abs (real_const (b5dL_qdiv q M))))
             (real_const (b5dL_epsQ1 M epsQ))
             (real_const ((epsQ / (2 * q)) * (b5dL_qdiv q M)))
             (real_const (b5dL_epsQ1 M epsQ)));
      [ exact Hm | apply real_eq_refl ].
  - apply (real_eq_trans _
             (real_const ((epsQ / (2 * q)) * (b5dL_qdiv q M)
                          + b5dL_epsQ1 M epsQ)) _).
    + exact (b5dH_plus_const_eq ((epsQ / (2 * q)) * (b5dL_qdiv q M))
                                (b5dL_epsQ1 M epsQ)).
    + apply real_eq_refl.
Qed.

(* ============================================================ *)
(* G6 b5dQ_min_lb_3：三元 min 树 lb glue（设计 §4 G6 行 min_lb_3*)
(*   ——P1 段文件已占二元 b5dQ_min_lb（跨段名不重叠纪律 ⟹ 本段    *)
(*   只含三元版；二元版由 P1 段文件提供）。                 *)
(*   语句：real_lt lb X/Y/Z ⟹ real_lt lb (real_min (real_min X Y) *)
(*     Z)。证法 = 检验件 p_min_lb 坐标 margin 组合直移植（e :=      *)
(*     Qmin (Qmin e1 e2) e3 + Q.min_glb_lt 双层应用）。          *)
(* ============================================================ *)
Lemma b5dQ_min_lb_3 : forall (lb A B C : Real),
  real_lt lb A -> real_lt lb B -> real_lt lb C ->
  real_lt lb (real_min (real_min A B) C).
Proof.
  intros lb A B C HltA HltB HltC.
  destruct HltA as [e1 [He1 [N1 HN1]]].
  destruct HltB as [e2 [He2 [N2 HN2]]].
  destruct HltC as [e3 [He3 [N3 HN3]]].
  set (e := Qmin (Qmin e1 e2) e3).
  assert (He : QltT 0 e).
  { apply Qlt_to_QltT. unfold e.
    apply Q.min_glb_lt.
    - apply Q.min_glb_lt.
      + apply QltT_to_Qlt. exact He1.
      + apply QltT_to_Qlt. exact He2.
    - apply QltT_to_Qlt. exact He3. }
  unfold real_lt.
  exists e.
  split.
  { exact He. }
  { exists (Nat.max (Nat.max N1 N2) N3).
    intros n Hn.
    apply NatLe_drop in Hn.
    assert (Hn1 : NatLe N1 n) by (apply NatLe_lift; lia).
    assert (Hn2 : NatLe N2 n) by (apply NatLe_lift; lia).
    assert (Hn3 : NatLe N3 n) by (apply NatLe_lift; lia).
    apply Qlt_to_QltT.
    set (cn := projT1 lb n).
    set (an := projT1 A n).
    set (bn := projT1 B n).
    set (dn := projT1 C n).
    assert (H1n : Qlt e1 (an - cn)).
    { unfold an, cn. apply QltT_to_Qlt. exact (HN1 n Hn1). }
    assert (H2n : Qlt e2 (bn - cn)).
    { unfold bn, cn. apply QltT_to_Qlt. exact (HN2 n Hn2). }
    assert (H3n : Qlt e3 (dn - cn)).
    { unfold dn, cn. apply QltT_to_Qlt. exact (HN3 n Hn3). }
    assert (He12 : Qle e (Qmin e1 e2)). { unfold e. apply Q.le_min_l. }
    assert (He3b : Qle e e3). { unfold e. apply Q.le_min_r. }
    assert (Hm1 : Qlt e (an - cn)).
    { apply (Qle_lt_trans e e1 (an - cn)).
      - apply (Qle_trans e (Qmin e1 e2) e1); [ exact He12 | apply Q.le_min_l ].
      - exact H1n. }
    assert (Hm2 : Qlt e (bn - cn)).
    { apply (Qle_lt_trans e e2 (bn - cn)).
      - apply (Qle_trans e (Qmin e1 e2) e2); [ exact He12 | apply Q.le_min_r ].
      - exact H2n. }
    assert (Hm3 : Qlt e (dn - cn)).
    { apply (Qle_lt_trans e e3 (dn - cn)); [ exact He3b | exact H3n ]. }
    assert (Ht1 : Qlt (e + cn) an).
    { apply (proj2 (Qlt_minus_iff (e + cn) an)).
      apply (Qlt_le_trans 0 ((an - cn) - e) (an - (e + cn))).
      - apply (proj1 (Qlt_minus_iff e (an - cn))). exact Hm1.
      - apply qeq_le. ring. }
    assert (Ht2 : Qlt (e + cn) bn).
    { apply (proj2 (Qlt_minus_iff (e + cn) bn)).
      apply (Qlt_le_trans 0 ((bn - cn) - e) (bn - (e + cn))).
      - apply (proj1 (Qlt_minus_iff e (bn - cn))). exact Hm2.
      - apply qeq_le. ring. }
    assert (Ht3 : Qlt (e + cn) dn).
    { apply (proj2 (Qlt_minus_iff (e + cn) dn)).
      apply (Qlt_le_trans 0 ((dn - cn) - e) (dn - (e + cn))).
      - apply (proj1 (Qlt_minus_iff e (dn - cn))). exact Hm3.
      - apply qeq_le. ring. }
    assert (Htg : Qlt (e + cn) (Qmin (Qmin an bn) dn)).
    { apply Q.min_glb_lt.
      - apply Q.min_glb_lt; [ exact Ht1 | exact Ht2 ].
      - exact Ht3. }
    rewrite (real_min_proj (real_min A B) C n).
    rewrite (real_min_proj A B n).
    apply (proj2 (Qlt_minus_iff e (Qmin (Qmin an bn) dn - cn))).
    apply (Qlt_le_trans 0 (Qmin (Qmin an bn) dn - (e + cn))
                         ((Qmin (Qmin an bn) dn - cn) - e)).
    - apply (proj1 (Qlt_minus_iff (e + cn) (Qmin (Qmin an bn) dn))).
      exact Htg.
    - apply qeq_le. ring.
  }
Qed.

(* ============================================================ *)
(* G8 b5dQ_qdiv_lt_arch：q_arch_inv 链的 Q 层证明（设计 §4 G8 行）*)
(*   语句：0<q ∧ 0<δ0 ∧ Qlt (1/(M#1)) (δ0/q) ⟹ Qlt (qdiv q M)   *)
(*     δ0。证法 = 两侧乘 q（Qmult_lt_compat_r）+ q·(1/(M#1)) ==  *)
(*     q/(M#1)（ring）+ q·(δ0/q) == δ0（Qmult_inv_l，q ≠ 0 由    *)
(*     b5dL_q_lt0_nz）。                                        *)
(* ============================================================ *)
Lemma b5dQ_qdiv_lt_arch : forall (q delta0 : Q) (M : nat),
  Qlt 0 q -> Qlt 0 delta0 ->
  Qlt (1 / (Z.of_nat M # 1)) (delta0 / q) ->
  Qlt (b5dL_qdiv q M) delta0.
Proof.
  intros q delta0 M Hq0 Hd0 Harch.
  unfold b5dL_qdiv.
  assert (Hqnz : ~ q == 0).
  { apply (b5dL_q_lt0_nz q). exact Hq0. }
  (* Harch 两侧右乘 q（Qmult_lt_compat_r） *)
  assert (Hm2 : Qlt ((1 / (Z.of_nat M # 1)) * q) ((delta0 / q) * q)).
  { apply (Qmult_lt_compat_r (1 / (Z.of_nat M # 1)) (delta0 / q) q Hq0).
    exact Harch. }
  (* 桥：q·(1/(M#1)) == q/(M#1)（ring）；(δ0/q)·q == δ0（inv 消去） *)
  assert (Hq1 : q * (1 / (Z.of_nat M # 1)) == q / (Z.of_nat M # 1)).
  { unfold Qdiv. ring. }
  assert (Hq2 : (delta0 / q) * q == delta0).
  { field.
    all: try (exact (b5dL_q_lt0_nz q Hq0)).
    all: try (intro Hz; apply (b5dL_q_lt0_nz q Hq0); exact Hz). }
  (* 左乘形归位：q·(1/(M#1)) ≤ (1/(M#1))·q（comm）+ Hm2 证毕 *)
  assert (Hm : Qlt (q * (1 / (Z.of_nat M # 1))) ((delta0 / q) * q)).
  { apply (Qle_lt_trans (q * (1 / (Z.of_nat M # 1)))
                        ((1 / (Z.of_nat M # 1)) * q)
                        ((delta0 / q) * q)).
    - apply qeq_imp_qle. apply (Qmult_comm q (1 / (Z.of_nat M # 1))).
    - exact Hm2. }
  rewrite Hq2 in Hm.
  rewrite Hq1 in Hm.
  exact Hm.
Qed.

(* ============================================================ *)
(* P3 段终。                                                      *)
(* ============================================================ *)

(* ===== 段 P4a（桥接引理：J_tk_succ_bridge / J_cert_wd / step_inst，3 Lemma）===== *)

(* ============================================================ *)
(* 件 1 b5dQ_J_tk_succ_bridge：t_k + η ↔ t_{k+1} 桥（J Proper）   *)
(*   语句 = item22 进度 §3.7 L273–278 逐字（= δD2f §2.8(a) 同文， *)
(*   前缀 b5dL_ → b5dQ_ 映射）——item22 实测未闭（仅注释提及），   *)
(*   本件新建。                                                  *)
(*   证法（设计 §2.8(a) 照准，~8–12 行）：b5p2_J_wd +             *)
(*     b5dL_tkq_succ（Qeq）→ b5dH_real_const_qeq（实层）→         *)
(*     b5dH_plus_const_eq（反向，real_eq_sym）→ real_eq_trans。   *)
(* ============================================================ *)
Lemma b5dQ_J_tk_succ_bridge : forall (q : Q) (M k : nat) (HMpos : (0 < M)%nat)
  (Hk1 : cw_unit (real_const (b5dL_tkq q M (Datatypes.S k))))
  (Hp : cw_unit (real_plus (real_const (b5dL_tkq q M k)) (real_const (b5dL_qdiv q M)))),
  real_eq (b5c_J (real_const (b5dL_tkq q M (Datatypes.S k))) Hk1)
          (b5c_J (real_plus (real_const (b5dL_tkq q M k)) (real_const (b5dL_qdiv q M))) Hp).
Proof.
  intros q M k HMpos Hk1 Hp.
  apply (b5p2_J_wd (real_const (b5dL_tkq q M (Datatypes.S k)))
                   (real_plus (real_const (b5dL_tkq q M k)) (real_const (b5dL_qdiv q M)))
                   Hk1 Hp).
  apply (real_eq_trans (real_const (b5dL_tkq q M (Datatypes.S k)))
                       (real_const (b5dL_tkq q M k + b5dL_qdiv q M))
                       (real_plus (real_const (b5dL_tkq q M k)) (real_const (b5dL_qdiv q M)))).
  - apply b5dH_real_const_qeq.
    exact (b5dL_tkq_succ q M k HMpos).
  - apply real_eq_sym.
    exact (b5dH_plus_const_eq (b5dL_tkq q M k) (b5dL_qdiv q M)).
Qed.

(* ============================================================ *)
(* 件 2 b5dQ_J_cert_wd：J 证书形态桥（同 x 两证书互换）           *)
(*   语句 = 设计 §2.8(b)/§4 描述形逐字（∀Hx Hx' : cw_unit        *)
(*     (real_const t)：real_eq (b5c_J (real_const t) Hx)          *)
(*     (b5c_J (real_const t) Hx')——设计表注 5–8 行）。            *)
(*   用途：Hmod 形 Hk 任意证书 ↔ 模量件左点固定证书               *)
(*     （b3rr_dom_r1 (real_const t_k) q Hxr Hq1，根 L71826——      *)
(*     输出类型与 cw_unit 定义性同形）。                          *)
(*   证法：b5p2_J_wd（同 x 两证书）+ real_eq_refl（~5 行）。       *)
(* ============================================================ *)
Lemma b5dQ_J_cert_wd : forall (t : Q) (Hx Hx' : cw_unit (real_const t)),
  real_eq (b5c_J (real_const t) Hx) (b5c_J (real_const t) Hx').
Proof.
  intros t Hx Hx'.
  apply (b5p2_J_wd (real_const t) (real_const t) Hx Hx').
  apply real_eq_refl.
Qed.

(* ============================================================ *)
(* 件 3 b5dQ_step_inst：模量输出 → 骨架 Hstep 形桥（缺口件）      *)
(*   设计 §2.8(c) step_inst 描述 = 把 C5 实例结论整体桥到骨架形   *)
(*   （取用 (a)(b)(c) 全件）——其中 RHS==real_const(bk) 部 = §4    *)
(*   G5 = 已闭 b5dQ_rhs_bk（本段禁 Require 该件                    *)
(*   P3——零依赖纪律）⟹ 功能重叠如实报告，本件只补缺口 = LHS/      *)
(*   证书形桥：模量结论（左点证书 b3rr_dom_r1 形固定证书）→       *)
(*   Hstep 形（Hk/Hk1 任意证书）的 real_le 桥，RHS 抽象参数 R     *)
(*   （P4 装配实例化 R := eps·|h|+eps' 实形后经 b5dQ_rhs_bk       *)
(*   一步 real_le_id_r 收 real_const (bk)——设计记录 §5 衔接注记）。*)
(*   参数面 = 模量件实例面：x := real_const (tkq q M k)（Hxr 为    *)
(*   其 |x_n| ≤ q 证书参数）、h := real_const (qdiv q M)、         *)
(*   Hxh := cw_unit (real_plus …)（P4 侧由 b5dQ_xph_unit 实例     *)
(*   供入）、Hk/Hk1 为 Hmod 形任意证书、Hq1 供左点 b3rr_dom_r1    *)
(*   第三参数、HMpos 供件 1 tkq_succ 前提。                       *)
(*   证法（~12 行）：件 1（Hp := Hxh 实例）桥右点两证书形 +        *)
(*     件 2（左点两证书）桥左点 + real_eq_opp_compat /            *)
(*     real_eq_plus_compat / real_abs_eq_compat（根 L32803/       *)
(*     32767/46326）+ real_le_id_l（根 L33011）收 real_le 形。     *)
(* ============================================================ *)
Lemma b5dQ_step_inst : forall (q : Q) (M k : nat) (HMpos : (0 < M)%nat)
  (Hq1 : Qlt q 1)
  (Hxr : forall n : nat, QleT' (Qabs (projT1 (real_const (b5dL_tkq q M k)) n)) q)
  (Hk1 : cw_unit (real_const (b5dL_tkq q M (Datatypes.S k))))
  (Hk : cw_unit (real_const (b5dL_tkq q M k)))
  (Hxh : cw_unit (real_plus (real_const (b5dL_tkq q M k)) (real_const (b5dL_qdiv q M)))),
  forall (R : Real),
  real_le (real_abs (real_plus (b5c_J (real_plus (real_const (b5dL_tkq q M k))
                                                 (real_const (b5dL_qdiv q M))) Hxh)
                               (real_opp (b5c_J (real_const (b5dL_tkq q M k))
                                                (b3rr_dom_r1 (real_const (b5dL_tkq q M k))
                                                             q Hxr Hq1)))))
          R ->
  real_le (real_abs (real_plus (b5c_J (real_const (b5dL_tkq q M (Datatypes.S k))) Hk1)
                               (real_opp (b5c_J (real_const (b5dL_tkq q M k)) Hk))))
          R.
Proof.
  intros q M k HMpos Hq1 Hxr Hk1 Hk Hxh R Hmain.
  apply (RealSetoid.real_le_id_l
    (real_abs (real_plus (b5c_J (real_const (b5dL_tkq q M (Datatypes.S k))) Hk1)
                         (real_opp (b5c_J (real_const (b5dL_tkq q M k)) Hk))))
    (real_abs (real_plus (b5c_J (real_plus (real_const (b5dL_tkq q M k))
                                           (real_const (b5dL_qdiv q M))) Hxh)
                         (real_opp (b5c_J (real_const (b5dL_tkq q M k))
                                          (b3rr_dom_r1 (real_const (b5dL_tkq q M k))
                                                       q Hxr Hq1)))))
    R).
  - apply real_abs_eq_compat.
    apply (RealSetoid.real_eq_plus_compat
      (b5c_J (real_const (b5dL_tkq q M (Datatypes.S k))) Hk1)
      (real_opp (b5c_J (real_const (b5dL_tkq q M k)) Hk))
      (b5c_J (real_plus (real_const (b5dL_tkq q M k)) (real_const (b5dL_qdiv q M))) Hxh)
      (real_opp (b5c_J (real_const (b5dL_tkq q M k))
                       (b3rr_dom_r1 (real_const (b5dL_tkq q M k)) q Hxr Hq1)))).
    + exact (b5dQ_J_tk_succ_bridge q M k HMpos Hk1 Hxh).
    + apply (RealSetoid.real_eq_opp_compat
        (b5c_J (real_const (b5dL_tkq q M k)) Hk)
        (b5c_J (real_const (b5dL_tkq q M k))
               (b3rr_dom_r1 (real_const (b5dL_tkq q M k)) q Hxr Hq1))).
      exact (b5dQ_J_cert_wd (b5dL_tkq q M k) Hk
                            (b3rr_dom_r1 (real_const (b5dL_tkq q M k)) q Hxr Hq1)).
  - exact Hmain.
Qed.

(* ===== 段 M1（lb_Sdiff 族：lb_exp_part 坐标件 + cS/lb_gdiff 值 + lb_Sdiff 6 分支，17 Lemma/Def） ===== *)

(* ============================================================ *)
(* M1 前件：闭式证书 + Sdiff 地板值定义族 + 正性                  *)
(* ============================================================ *)

(* Qlt 0 2（Sdiff 件 M-参数 M_S := 2 的 HMpos 闭式） *)
Lemma b5dQ_p4_two_pos : Qlt 0 2.
Proof. unfold Qlt. simpl. lia. Qed.

(* Qlt 0 (1#2)（cA := 1#2 的 HcA 闭式） *)
Lemma b5dQ_p4_half_pos : Qlt 0 (1 # 2).
Proof. unfold Qlt. simpl. lia. Qed.

(* Sdiff k2 := Qinv(8·(2+1))（M_S := 2 闭式）正性：Qlt 0 *)
Lemma b5dQ_p4_k2t_pos : Qlt 0 (Qinv (Qmult 8 (Qplus 2 1))).
Proof.
  apply Qinv_lt_0_compat.
  unfold Qlt. simpl. lia.
Qed.

(* exp 支地板树（δexp-支：floorA/floorB/C 之 min；坐标件 RHS 的
   exp 支同构——P2 lb_exp_part 地板以 (a·(1#2)) 代 a） *)
Definition b5dQ_lbSdiff_cE (q a : Q) : Q :=
  Qmin (Qmin
    (Qmult (Qmin (1 # 2)
                 (Qmult (Qmult (Qmult (Qmult a (1 # 2))
                                      (Qinv (b5j_Kvq q))) (1 # 3))
                        (1 # 4)))
           (1 # 4))
    (Qmult (Qmin (1 # 2) (Qmult (1 # 4) b5j_kL)) (1 # 12)))
  (1 # 2).

(* g 支地板树（δg-支：floorA2/floorB2/C 之 min；坐标件 RHS 的
   g 支同构——P2 lb_gdiff 地板以 (a·(1#4)) 代 a、k2 := k2t 闭式） *)
Definition b5dQ_lbSdiff_cG (q a : Q) : Q :=
  Qmin (Qmin
    (Qmult (Qmin (1 # 2)
                 (Qmult (1 # 4)
                        (Qmult (Qmult a (1 # 4))
                               (Qmult (Qinv (Qmult 8 (Qplus 2 1)))
                                      (1 # 2)))))
           (1 # 12))
    (Qmult (Qmult a (1 # 4))
           (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2))))
  (1 # 2).

(* Sdiff 值定义（lb := cS/2；δ0 汇合分量源） *)
Definition b5dQ_lbSdiff_cS (q a : Q) : Q :=
  Qmin (b5dQ_lbSdiff_cE q a) (b5dQ_lbSdiff_cG q a).

Definition b5dQ_lbSdiff_val (q a : Q) : Q :=
  Qmult (b5dQ_lbSdiff_cS q a) (1 # 2).

(* cS 正性（Qle 0 q ∧ 0 < a ⟹ 0 < cS——分支地板全正） *)
Lemma b5dQ_lbSdiff_cS_pos : forall (q a : Q),
  Qle 0 q -> Qlt 0 a -> Qlt 0 (b5dQ_lbSdiff_cS q a).
Proof.
  intros q a Hq0 Ha.
  assert (H12 : Qlt 0 (1 # 2)) by exact b5dQ_p4_half_pos.
  assert (H13 : Qlt 0 (1 # 3)) by (unfold Qlt; simpl; lia).
  assert (H14 : Qlt 0 (1 # 4)) by (unfold Qlt; simpl; lia).
  assert (H112 : Qlt 0 (1 # 12)) by (unfold Qlt; simpl; lia).
  assert (HKpos : Qlt 0 (Qinv (b5j_Kvq q))).
  { apply Qinv_lt_0_compat. exact (b5j_Kvq_pos q Hq0). }
  assert (HkLpos : Qlt 0 b5j_kL) by (apply QltT_to_Qlt; exact b5j_kL_posT).
  assert (Hk2pos : Qlt 0 (Qinv (Qmult 8 (Qplus 2 1)))) by exact b5dQ_p4_k2t_pos.
  assert (Ha2 : Qlt 0 (Qmult a (1 # 2))).
  { apply (Qmult_lt_0_compat a (1 # 2)); [exact Ha | exact H12]. }
  assert (Ha4 : Qlt 0 (Qmult a (1 # 4))).
  { apply (Qmult_lt_0_compat a (1 # 4)); [exact Ha | exact H14]. }
  assert (HkL2 : Qlt 0 (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2))).
  { apply (Qmult_lt_0_compat (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2));
      [exact Hk2pos | exact H12]. }
  (* cE 正性（三分支全正） *)
  assert (HmL2pos : Qlt 0 (Qmult (Qmult (Qmult (Qmult a (1 # 2))
                                               (Qinv (b5j_Kvq q))) (1 # 3))
                                 (1 # 4))).
  { apply (Qmult_lt_0_compat (Qmult (Qmult (Qmult a (1 # 2))
                                           (Qinv (b5j_Kvq q))) (1 # 3)) (1 # 4));
      [ | exact H14 ].
    apply (Qmult_lt_0_compat (Qmult (Qmult a (1 # 2)) (Qinv (b5j_Kvq q))) (1 # 3));
      [ | exact H13 ].
    apply (Qmult_lt_0_compat (Qmult a (1 # 2)) (Qinv (b5j_Kvq q)));
      [exact Ha2 | exact HKpos]. }
  assert (HfloorLpos : Qlt 0 (Qmin (1 # 2)
     (Qmult (Qmult (Qmult (Qmult a (1 # 2)) (Qinv (b5j_Kvq q))) (1 # 3)) (1 # 4)))).
  { apply Q.min_glb_lt; [exact H12 | exact HmL2pos]. }
  assert (HfloorApos : Qlt 0 (Qmult (Qmin (1 # 2)
     (Qmult (Qmult (Qmult (Qmult a (1 # 2)) (Qinv (b5j_Kvq q))) (1 # 3)) (1 # 4)))
                                   (1 # 4))).
  { apply (Qmult_lt_0_compat
      (Qmin (1 # 2)
        (Qmult (Qmult (Qmult (Qmult a (1 # 2)) (Qinv (b5j_Kvq q))) (1 # 3)) (1 # 4)))
      (1 # 4)); [exact HfloorLpos | exact H14]. }
  assert (HfloorDpos : Qlt 0 (Qmin (1 # 2) (Qmult (1 # 4) b5j_kL))).
  { apply Q.min_glb_lt; [exact H12 | ].
    apply (Qmult_lt_0_compat (1 # 4) b5j_kL); [exact H14 | exact HkLpos]. }
  assert (HfloorBpos : Qlt 0 (Qmult (Qmin (1 # 2) (Qmult (1 # 4) b5j_kL)) (1 # 12))).
  { apply (Qmult_lt_0_compat (Qmin (1 # 2) (Qmult (1 # 4) b5j_kL)) (1 # 12));
      [exact HfloorDpos | exact H112]. }
  assert (HcEpos : Qlt 0 (b5dQ_lbSdiff_cE q a)).
  { unfold b5dQ_lbSdiff_cE.
    apply Q.min_glb_lt.
    - apply Q.min_glb_lt; [exact HfloorApos | exact HfloorBpos].
    - exact H12. }
  (* cG 正性（三分支全正） *)
  assert (Hmpos : Qlt 0 (Qmult (Qmult a (1 # 4))
                               (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2)))).
  { apply (Qmult_lt_0_compat (Qmult a (1 # 4))
                             (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2)));
      [exact Ha4 | exact HkL2]. }
  assert (HfloorA2pos : Qlt 0 (Qmult (Qmin (1 # 2)
     (Qmult (1 # 4) (Qmult (Qmult a (1 # 4))
                           (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2)))))
                                     (1 # 12))).
  { apply (Qmult_lt_0_compat
      (Qmin (1 # 2)
        (Qmult (1 # 4) (Qmult (Qmult a (1 # 4))
                              (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2)))))
      (1 # 12)); [ | exact H112 ].
    apply Q.min_glb_lt; [exact H12 | ].
    apply (Qmult_lt_0_compat (1 # 4)
                             (Qmult (Qmult a (1 # 4))
                                    (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2))));
      [exact H14 | exact Hmpos]. }
  assert (HcGpos : Qlt 0 (b5dQ_lbSdiff_cG q a)).
  { unfold b5dQ_lbSdiff_cG.
    apply Q.min_glb_lt.
    - apply Q.min_glb_lt; [exact HfloorA2pos | exact Hmpos].
    - exact H12. }
  unfold b5dQ_lbSdiff_cS.
  apply Q.min_glb_lt; [exact HcEpos | exact HcGpos].
Qed.

(* lbSdiff_val 正性（cS-pos 推论） *)
Lemma b5dQ_lbSdiff_pos : forall (q a : Q),
  Qle 0 q -> Qlt 0 a -> Qlt 0 (b5dQ_lbSdiff_val q a).
Proof.
  intros q a Hq0 Ha.
  assert (H12 : Qlt 0 (1 # 2)) by exact b5dQ_p4_half_pos.
  unfold b5dQ_lbSdiff_val.
  apply (Qmult_lt_0_compat (b5dQ_lbSdiff_cS q a) (1 # 2));
    [exact (b5dQ_lbSdiff_cS_pos q a Hq0 Ha) | exact H12].
Qed.

(* ============================================================ *)
(* M1 坐标件支撑：份额坐标小件（P2 坐标件模式的 c 泛化）          *)
(* ============================================================ *)

(* QltT 0 k2t（g 支 k2 闭式证书） *)
Lemma b5dQ_p4_k2t_posT : QltT 0 (Qinv (Qmult 8 (Qplus 2 1))).
Proof. apply Qlt_to_QltT. exact b5dQ_p4_k2t_pos. Qed.

(* real_mult (real_const a) (real_const c) 的正性证书（份额 eps 的
   real_lt-证书；证明位，透明性无关） *)
Lemma b5dQ_p4_mul_pos : forall (a c : Q) (Ha : Qlt 0 a) (Hc : Qlt 0 c),
  real_lt real_zero (real_mult (real_const a) (real_const c)).
Proof.
  intros a c Ha Hc.
  apply real_mult_positive.
  - apply real_const_pos. apply Qlt_to_QltT. exact Ha.
  - apply real_const_pos. apply Qlt_to_QltT. exact Hc.
Qed.

(* eps0 := eps·K·invM（eps := real_const a·real_const c）的正性证书 *)
Lemma b5dQ_p4_eps0_c_pos : forall (q : Q) (Hq0 : Qle 0 q)
  (a c : Q) (Ha : Qlt 0 a) (Hc : Qlt 0 c) (x : Real),
  real_lt real_zero (real_mult
    (real_mult (real_mult (real_const a) (real_const c))
               (real_const (Qinv (b5j_Kvq q))))
    (real_inv_pos (real_plus real_one (real_abs (b5a_S x)))
                  (b5dK_real_abs_plus_one_pos_exp (b5a_S x)))).
Proof.
  intros q Hq0 a c Ha Hc x.
  apply real_mult_positive.
  - apply real_mult_positive.
    + exact (b5dQ_p4_mul_pos a c Ha Hc).
    + apply real_const_pos. apply Qlt_to_QltT.
      apply Qinv_lt_0_compat. exact (b5j_Kvq_pos q Hq0).
  - apply (real_inv_pos_pos (real_plus real_one (real_abs (b5a_S x)))
                            (b5dK_real_abs_plus_one_pos_exp (b5a_S x))).
Qed.

(* exp-part @ eps := real_mult (real_const a) (real_const c) 的坐标件
   （P2 b5dQ_lb_exp_part_coord 的 c 泛化——a 代 (a·c)；S 原子保
   原子；δL 支同 b5j_kL） *)
Lemma b5dQ_lb_exp_part_c_coord : forall (q : Q) (Hq0 : Qle 0 q) (Hq1 : Qlt q 1)
  (x : Real) (Hxr : forall n : nat, QleT' (Qabs (projT1 x n)) q)
  (a : Q) (Ha : Qlt 0 a) (c : Q) (Hc : Qlt 0 c) (n : nat),
  projT1 (projT1 (b5dK_exp_part_bound_closed_r_exp q Hq0 Hq1 x Hxr
                 (real_mult (real_const a) (real_const c))
                 (b5dQ_p4_mul_pos a c Ha Hc))) n
  == Qmin (Qmin
      (Qmult (Qmin (1 # 2)
                   (Qmult (Qmult (Qmult (Qmult a c) (Qinv (b5j_Kvq q)))
                                 (Qinv (Qplus 1 (Qabs (projT1 (b5a_S x) n)))))
                          (1 # 4)))
             (1 # 4))
      (Qmult (Qmin (Qmult (Qinv 2) (projT1 (b5f_u x) n))
                   (Qmult (Qmult (Qinv 2) (Qinv 2))
                          (Qmult b5j_kL (Qmult (projT1 (b5f_u x) n)
                                               (projT1 (b5f_u x) n)))))
             (1 # 12)))
    (1 # 2).
Proof.
  intros q Hq0 Hq1 x Hxr a Ha c Hc n.
  set (K := Qinv (b5j_Kvq q)).
  set (eps0t := real_mult (real_mult (real_mult (real_const a) (real_const c))
                                     (real_const K))
                  (real_inv_pos (real_plus real_one (real_abs (b5a_S x)))
                                (b5dK_real_abs_plus_one_pos_exp (b5a_S x)))).
  change (projT1 (real_min (real_min
    (real_mult (projT1 (b5dK_exp_minus_one_linear_closed_exp eps0t
                       (b5dQ_p4_eps0_c_pos q Hq0 a c Ha Hc x)))
               (real_const (1 # 4)))
    (real_mult (projT1 (b5dJ_LogErr_delta_exp x (real_const b5j_kL)
                       (real_const_pos b5j_kL
                          (Qlt_to_QltT 0 b5j_kL (QltT_to_Qlt 0 b5j_kL b5j_kL_posT)))))
               (real_const (1 # 12))))
    (real_const (1 # 2))) n
  == Qmin (Qmin
      (Qmult (Qmin (1 # 2)
                   (Qmult (Qmult (Qmult (Qmult a c) (Qinv (b5j_Kvq q)))
                                 (Qinv (Qplus 1 (Qabs (projT1 (b5a_S x) n)))))
                          (1 # 4)))
             (1 # 4))
      (Qmult (Qmin (Qmult (Qinv 2) (projT1 (b5f_u x) n))
                   (Qmult (Qmult (Qinv 2) (Qinv 2))
                          (Qmult b5j_kL (Qmult (projT1 (b5f_u x) n)
                                               (projT1 (b5f_u x) n)))))
             (1 # 12)))
    (1 # 2)).
  rewrite (real_min_proj
    (real_min
      (real_mult (projT1 (b5dK_exp_minus_one_linear_closed_exp eps0t
                         (b5dQ_p4_eps0_c_pos q Hq0 a c Ha Hc x)))
                 (real_const (1 # 4)))
      (real_mult (projT1 (b5dJ_LogErr_delta_exp x (real_const b5j_kL)
                         (real_const_pos b5j_kL
                            (Qlt_to_QltT 0 b5j_kL (QltT_to_Qlt 0 b5j_kL b5j_kL_posT)))))
                 (real_const (1 # 12))))
    (real_const (1 # 2)) n).
  rewrite (real_min_proj
    (real_mult (projT1 (b5dK_exp_minus_one_linear_closed_exp eps0t
                       (b5dQ_p4_eps0_c_pos q Hq0 a c Ha Hc x)))
               (real_const (1 # 4)))
    (real_mult (projT1 (b5dJ_LogErr_delta_exp x (real_const b5j_kL)
                       (real_const_pos b5j_kL
                          (Qlt_to_QltT 0 b5j_kL (QltT_to_Qlt 0 b5j_kL b5j_kL_posT)))))
               (real_const (1 # 12))) n).
  rewrite (real_mult_proj
    (projT1 (b5dK_exp_minus_one_linear_closed_exp eps0t
            (b5dQ_p4_eps0_c_pos q Hq0 a c Ha Hc x)))
    (real_const (1 # 4)) n).
  rewrite (real_mult_proj
    (projT1 (b5dJ_LogErr_delta_exp x (real_const b5j_kL)
            (real_const_pos b5j_kL
               (Qlt_to_QltT 0 b5j_kL (QltT_to_Qlt 0 b5j_kL b5j_kL_posT)))))
    (real_const (1 # 12)) n).
  rewrite (b5dQ_p_logerr_kL_coord x n).
  change (Qmin (Qmin
      (Qmult (projT1 (real_min (real_const (1 # 2))
                               (real_mult eps0t (real_const (1 # 4)))) n)
             (1 # 4))
      (Qmult (Qmin (Qmult (Qinv 2) (projT1 (b5f_u x) n))
                   (Qmult (Qmult (Qinv 2) (Qinv 2))
                          (Qmult b5j_kL (Qmult (projT1 (b5f_u x) n)
                                               (projT1 (b5f_u x) n)))))
             (1 # 12)))
    (1 # 2)
  == Qmin (Qmin
      (Qmult (Qmin (1 # 2)
                   (Qmult (Qmult (Qmult (Qmult a c) (Qinv (b5j_Kvq q)))
                                 (Qinv (Qplus 1 (Qabs (projT1 (b5a_S x) n)))))
                          (1 # 4)))
             (1 # 4))
      (Qmult (Qmin (Qmult (Qinv 2) (projT1 (b5f_u x) n))
                   (Qmult (Qmult (Qinv 2) (Qinv 2))
                          (Qmult b5j_kL (Qmult (projT1 (b5f_u x) n)
                                               (projT1 (b5f_u x) n)))))
             (1 # 12)))
    (1 # 2)).
  rewrite (real_min_proj (real_const (1 # 2)) (real_mult eps0t (real_const (1 # 4))) n).
  rewrite (real_mult_proj eps0t (real_const (1 # 4)) n).
  unfold eps0t, K.
  rewrite (real_mult_proj
    (real_mult (real_mult (real_const a) (real_const c)) (real_const (Qinv (b5j_Kvq q))))
    (real_inv_pos (real_plus real_one (real_abs (b5a_S x)))
                  (b5dK_real_abs_plus_one_pos_exp (b5a_S x))) n).
  rewrite (real_mult_proj
    (real_mult (real_const a) (real_const c)) (real_const (Qinv (b5j_Kvq q))) n).
  repeat (rewrite real_mult_proj || rewrite real_const_proj).
  rewrite (b5dQ_p_invM_coord x n).
  cbn [projT1 real_inv_pos real_plus real_abs real_one real_const Nat.leb
       b5dK_real_abs_plus_one_pos_exp b5j_kL].
  reflexivity.
Qed.

(* epsL := eps·real_const kL（eps := real_const a·real_const c）正性证书 *)
Lemma b5dQ_p4_epsLt_pos : forall (a c k2 : Q) (Ha : Qlt 0 a) (Hc : Qlt 0 c)
  (Hk2 : Qlt 0 k2),
  real_lt real_zero (real_mult (real_mult (real_const a) (real_const c))
                               (real_const (Qmult k2 (1 # 2)))).
Proof.
  intros a c k2 Ha Hc Hk2.
  apply real_mult_positive.
  - exact (b5dQ_p4_mul_pos a c Ha Hc).
  - apply real_const_pos. apply Qlt_to_QltT.
    apply (Qmult_lt_0_compat k2 (1 # 2)); [exact Hk2 | exact b5dQ_p4_half_pos].
Qed.


(* gdiff @ eps := real_mult (real_const a) (real_const c) + k2 := k2t 的
   坐标件（P2 b5dQ_lb_gdiff_coord 的 c 泛化——a 代 (a·c)、k2 闭式；
   δL' 支内联展开） *)
Lemma b5dQ_lb_gdiff_c_coord : forall (q : Q) (Hq0 : Qle 0 q) (Hq1 : Qlt q 1)
  (x : Real) (Hxr : forall n : nat, QleT' (Qabs (projT1 x n)) q)
  (a : Q) (Ha : Qlt 0 a) (c : Q) (Hc : Qlt 0 c) (n : nat),
  projT1 (projT1 (b5dK_gdiff_pts_r_exp q Hq0 Hq1 x Hxr
                 (real_mult (real_const a) (real_const c))
                 (b5dQ_p4_mul_pos a c Ha Hc)
                 (Qinv (Qmult 8 (Qplus 2 1))) (Qinv (Qmult 8 (Qplus 2 1)))
                 b5dQ_p4_k2t_posT b5dQ_p4_k2t_posT)) n
  == Qmin (Qmin
      (Qmult (Qmin (Qmult (Qinv 2) (projT1 (b5f_u x) n))
                   (Qmult (Qmult (Qinv 2) (Qinv 2))
                          (Qmult (Qmult (Qmult a c)
                                        (Qmult (Qinv (Qmult 8 (Qplus 2 1)))
                                               (1 # 2)))
                                 (Qmult (projT1 (b5f_u x) n)
                                        (projT1 (b5f_u x) n)))))
             (1 # 12))
      (Qmult (Qmult a c)
             (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2))))
    (1 # 2).
Proof.
  intros q Hq0 Hq1 x Hxr a Ha c Hc n.
  set (k2t := Qinv (Qmult 8 (Qplus 2 1))).
  set (epsLt := real_mult (real_mult (real_const a) (real_const c))
                          (real_const (Qmult k2t (1 # 2)))).
  change (projT1 (real_min (real_min
    (real_mult (projT1 (b5dJ_LogErr_delta_exp x epsLt
                       (b5dQ_p4_epsLt_pos a c k2t Ha Hc (QltT_to_Qlt 0 k2t b5dQ_p4_k2t_posT))))
               (real_const (1 # 12)))
    (real_mult (real_mult (real_const a) (real_const c))
               (real_const (Qmult k2t (1 # 2)))))
    (real_const (1 # 2))) n
  == Qmin (Qmin
      (Qmult (Qmin (Qmult (Qinv 2) (projT1 (b5f_u x) n))
                   (Qmult (Qmult (Qinv 2) (Qinv 2))
                          (Qmult (Qmult (Qmult a c)
                                        (Qmult k2t (1 # 2)))
                                 (Qmult (projT1 (b5f_u x) n)
                                        (projT1 (b5f_u x) n)))))
             (1 # 12))
      (Qmult (Qmult a c) (Qmult k2t (1 # 2))))
    (1 # 2)).
  rewrite (real_min_proj
    (real_min
      (real_mult (projT1 (b5dJ_LogErr_delta_exp x epsLt
                         (b5dQ_p4_epsLt_pos a c k2t Ha Hc (QltT_to_Qlt 0 k2t b5dQ_p4_k2t_posT))))
                 (real_const (1 # 12)))
      (real_mult (real_mult (real_const a) (real_const c))
                 (real_const (Qmult k2t (1 # 2)))))
    (real_const (1 # 2)) n).
  rewrite (real_min_proj
    (real_mult (projT1 (b5dJ_LogErr_delta_exp x epsLt
                       (b5dQ_p4_epsLt_pos a c k2t Ha Hc (QltT_to_Qlt 0 k2t b5dQ_p4_k2t_posT))))
               (real_const (1 # 12)))
    (real_mult (real_mult (real_const a) (real_const c))
               (real_const (Qmult k2t (1 # 2)))) n).
  rewrite (real_mult_proj
    (projT1 (b5dJ_LogErr_delta_exp x epsLt
            (b5dQ_p4_epsLt_pos a c k2t Ha Hc (QltT_to_Qlt 0 k2t b5dQ_p4_k2t_posT))))
    (real_const (1 # 12)) n).
  rewrite (real_mult_proj
    (real_mult (real_const a) (real_const c)) (real_const (Qmult k2t (1 # 2))) n).
  change (Qmin (Qmin
      (Qmult (projT1 (projT1 (b5dJ_log_diff_dx_exp (b5f_u x)
                 (b5a_one_plus_sq_pos x) epsLt
                 (b5dQ_p4_epsLt_pos a c k2t Ha Hc (QltT_to_Qlt 0 k2t b5dQ_p4_k2t_posT)))) n)
             (1 # 12))
      (Qmult (Qmult a c) (Qmult k2t (1 # 2))))
    (1 # 2)
  == Qmin (Qmin
      (Qmult (Qmin (Qmult (Qinv 2) (projT1 (b5f_u x) n))
                   (Qmult (Qmult (Qinv 2) (Qinv 2))
                          (Qmult (Qmult (Qmult a c)
                                        (Qmult k2t (1 # 2)))
                                 (Qmult (projT1 (b5f_u x) n)
                                        (projT1 (b5f_u x) n)))))
             (1 # 12))
      (Qmult (Qmult a c) (Qmult k2t (1 # 2))))
    (1 # 2)).
  change (Qmin (Qmin
      (Qmult (projT1 (real_min
        (real_mult (real_inv_pos (real_plus real_one real_one) (b5dJ_two_pos_exp))
                   (b5f_u x))
        (real_mult
          (real_mult (real_inv_pos (real_plus real_one real_one) (b5dJ_two_pos_exp))
                     (real_inv_pos (real_plus real_one real_one) (b5dJ_two_pos_exp)))
          (real_mult epsLt (real_mult (b5f_u x) (b5f_u x))))) n)
             (1 # 12))
      (Qmult (Qmult a c) (Qmult k2t (1 # 2))))
    (1 # 2)
  == Qmin (Qmin
      (Qmult (Qmin (Qmult (Qinv 2) (projT1 (b5f_u x) n))
                   (Qmult (Qmult (Qinv 2) (Qinv 2))
                          (Qmult (Qmult (Qmult a c)
                                        (Qmult k2t (1 # 2)))
                                 (Qmult (projT1 (b5f_u x) n)
                                        (projT1 (b5f_u x) n)))))
             (1 # 12))
      (Qmult (Qmult a c) (Qmult k2t (1 # 2))))
    (1 # 2)).
  rewrite (real_min_proj
    (real_mult (real_inv_pos (real_plus real_one real_one) (b5dJ_two_pos_exp))
               (b5f_u x))
    (real_mult
      (real_mult (real_inv_pos (real_plus real_one real_one) (b5dJ_two_pos_exp))
                 (real_inv_pos (real_plus real_one real_one) (b5dJ_two_pos_exp)))
      (real_mult epsLt (real_mult (b5f_u x) (b5f_u x)))) n).
  repeat (rewrite real_mult_proj || rewrite real_const_proj).
  unfold epsLt, k2t.
  repeat (rewrite real_mult_proj || rewrite real_const_proj).
  cbn [projT1 real_inv_pos real_plus real_abs real_one real_const Nat.leb
       b5dJ_two_pos_exp].
  reflexivity.
Qed.

(* ============================================================ *)
(* M1 坐标件：projT1(projT1(Sdiff-app)) n == 显式坐标树           *)
(*   Sdiff 体内：eps1 := eps·(1#2)（exp 部）/ eps2 := eps·(1#4)   *)
(*   （g 部）+ k2 := Qinv(8·(2+1))（M_S := 2 闭式）。             *)
(*   RHS = P2 exp-part/gdiff 坐标公式以 (a·(1#2))/(a·(1#4))       *)
(*   代 a 的机械替换形（change 到 δ 显式树 + 投影 rewrite）。     *)
(* ============================================================ *)
Lemma b5dQ_lb_Sdiff_coord : forall (q : Q) (Hq0 : Qle 0 q) (Hq1 : Qlt q 1)
  (x : Real) (Hxr : forall n : nat, QleT' (Qabs (projT1 x n)) q)
  (a : Q) (Ha : Qlt 0 a)
  (Nub : nat)
  (Hcert : forall n : nat, (Nub <= n)%nat ->
           Qle (Qabs (projT1 (b5a_S x) n)) 2)
  (n : nat),
  projT1 (projT1 (b5dP_S_diff_closed_r_M_exp_tail q Hq0 Hq1 x Hxr 2
    b5dQ_p4_two_pos Nub Hcert (real_const a)
    (real_const_pos a (Qlt_to_QltT 0 a Ha)))) n
  == Qmin (Qmin (Qmin
      (Qmult (Qmin (1 # 2)
                   (Qmult (Qmult (Qmult (Qmult a (1 # 2))
                                        (Qinv (b5j_Kvq q)))
                                 (Qinv (Qplus 1 (Qabs (projT1 (b5a_S x) n)))))
                          (1 # 4)))
             (1 # 4))
      (Qmult (Qmin (Qmult (Qinv 2) (projT1 (b5f_u x) n))
                   (Qmult (Qmult (Qinv 2) (Qinv 2))
                          (Qmult b5j_kL (Qmult (projT1 (b5f_u x) n)
                                               (projT1 (b5f_u x) n)))))
             (1 # 12)))
    (1 # 2))
  (Qmin (Qmin
      (Qmult (Qmin (Qmult (Qinv 2) (projT1 (b5f_u x) n))
                   (Qmult (Qmult (Qinv 2) (Qinv 2))
                          (Qmult (Qmult (Qmult a (1 # 4))
                                        (Qmult (Qinv (Qmult 8 (Qplus 2 1)))
                                               (1 # 2)))
                                 (Qmult (projT1 (b5f_u x) n)
                                        (projT1 (b5f_u x) n)))))
             (1 # 12))
      (Qmult (Qmult a (1 # 4))
             (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2))))
    (1 # 2)).
Proof.
  intros q Hq0 Hq1 x Hxr a Ha Nub Hcert n.
  set (Eapp := b5dK_exp_part_bound_closed_r_exp q Hq0 Hq1 x Hxr
    (real_mult (real_const a) (real_const (1 # 2)))
    (b5dQ_p4_mul_pos a (1 # 2) Ha b5dQ_p4_half_pos)).
  set (Gapp := b5dK_gdiff_pts_r_exp q Hq0 Hq1 x Hxr
    (real_mult (real_const a) (real_const (1 # 4)))
    (b5dQ_p4_mul_pos a (1 # 4) Ha b5dQ_Hq14)
    (Qinv (Qmult 8 (Qplus 2 1))) (Qinv (Qmult 8 (Qplus 2 1)))
    b5dQ_p4_k2t_posT b5dQ_p4_k2t_posT).
  change (projT1 (real_min (projT1 Eapp) (projT1 Gapp)) n
  == Qmin (Qmin (Qmin
      (Qmult (Qmin (1 # 2)
                   (Qmult (Qmult (Qmult (Qmult a (1 # 2))
                                        (Qinv (b5j_Kvq q)))
                                 (Qinv (Qplus 1 (Qabs (projT1 (b5a_S x) n)))))
                          (1 # 4)))
             (1 # 4))
      (Qmult (Qmin (Qmult (Qinv 2) (projT1 (b5f_u x) n))
                   (Qmult (Qmult (Qinv 2) (Qinv 2))
                          (Qmult b5j_kL (Qmult (projT1 (b5f_u x) n)
                                               (projT1 (b5f_u x) n)))))
             (1 # 12)))
    (1 # 2))
  (Qmin (Qmin
      (Qmult (Qmin (Qmult (Qinv 2) (projT1 (b5f_u x) n))
                   (Qmult (Qmult (Qinv 2) (Qinv 2))
                          (Qmult (Qmult (Qmult a (1 # 4))
                                        (Qmult (Qinv (Qmult 8 (Qplus 2 1)))
                                               (1 # 2)))
                                 (Qmult (projT1 (b5f_u x) n)
                                        (projT1 (b5f_u x) n)))))
             (1 # 12))
      (Qmult (Qmult a (1 # 4))
             (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2))))
    (1 # 2))).
  rewrite (real_min_proj (projT1 Eapp) (projT1 Gapp) n).
  unfold Eapp, Gapp.
  rewrite (b5dQ_lb_exp_part_c_coord q Hq0 Hq1 x Hxr a Ha (1 # 2)
                                    b5dQ_p4_half_pos n).
  rewrite (b5dQ_lb_gdiff_c_coord q Hq0 Hq1 x Hxr a Ha (1 # 4)
                                 b5dQ_Hq14 n).
  reflexivity.
Qed.

(* ============================================================ *)
(* M1 主件：b5dQ_lb_Sdiff（S-diff 层 lb——δexp/δg 支按 P2 §4     *)
(*   注记实例化；N := Nub（S 尾证书并入）；margin := lb/2）      *)
(*   证法：real_lt 展开（e := lb/2、N := Nub）→ 坐标件 rewrite +  *)
(*   qinv2/qinv2sq 归一 → Q 层（六分支：exp 支三分 + g 支三分，   *)
(*   逐支 floor ≤ 坐标（S 叶 1#3 封底 + u ≥ 1 + q_scaled_le）+   *)
(*   branch_lt 严格 margin + qmin_sub_r ×3 组装 + min_glb_lt）。  *)
(* ============================================================ *)
Lemma b5dQ_lb_Sdiff : forall (q : Q) (Hq0 : Qle 0 q) (Hq1 : Qlt q 1)
  (x : Real) (Hxr : forall n : nat, QleT' (Qabs (projT1 x n)) q)
  (a : Q) (Ha : Qlt 0 a)
  (Nub : nat)
  (Hcert : forall n : nat, (Nub <= n)%nat ->
           Qle (Qabs (projT1 (b5a_S x) n)) 2),
  real_lt (real_const (b5dQ_lbSdiff_val q a))
    (projT1 (b5dP_S_diff_closed_r_M_exp_tail q Hq0 Hq1 x Hxr 2
      b5dQ_p4_two_pos Nub Hcert (real_const a)
      (real_const_pos a (Qlt_to_QltT 0 a Ha)))).
Proof.
  intros q Hq0 Hq1 x Hxr a Ha Nub Hcert.
  set (cE := b5dQ_lbSdiff_cE q a).
  set (cG := b5dQ_lbSdiff_cG q a).
  set (cS := b5dQ_lbSdiff_cS q a).
  set (lb := Qmult cS (1 # 2)).
  set (e := Qmult lb (1 # 2)).
  assert (H12 : Qlt 0 (1 # 2)) by exact b5dQ_p4_half_pos.
  assert (H13 : Qlt 0 (1 # 3)) by (unfold Qlt; simpl; lia).
  assert (H14 : Qlt 0 (1 # 4)) by (unfold Qlt; simpl; lia).
  assert (H112 : Qlt 0 (1 # 12)) by (unfold Qlt; simpl; lia).
  assert (Hcpos : Qlt 0 cS).
  { unfold cS. exact (b5dQ_lbSdiff_cS_pos q a Hq0 Ha). }
  assert (Hlbpos : Qlt 0 lb).
  { unfold lb. apply (Qmult_lt_0_compat cS (1 # 2)); [exact Hcpos | exact H12]. }
  assert (Hepos : Qlt 0 e).
  { unfold e. apply (Qmult_lt_0_compat lb (1 # 2)); [exact Hlbpos | exact H12]. }
  (* cS ≤ 各 floor（六 floor 投影链） *)
  assert (HcA : Qle cS (Qmult (Qmin (1 # 2)
                 (Qmult (Qmult (Qmult (Qmult a (1 # 2))
                                      (Qinv (b5j_Kvq q))) (1 # 3))
                        (1 # 4)))
                           (1 # 4))).
  { apply (Qle_trans cS cE
      (Qmult (Qmin (1 # 2)
             (Qmult (Qmult (Qmult (Qmult a (1 # 2))
                                  (Qinv (b5j_Kvq q))) (1 # 3)) (1 # 4)))
             (1 # 4))).
    - unfold cS. apply Q.le_min_l.
    - unfold cE. apply (Qle_trans (Qmin (Qmin
          (Qmult (Qmin (1 # 2)
                 (Qmult (Qmult (Qmult (Qmult a (1 # 2))
                                      (Qinv (b5j_Kvq q))) (1 # 3)) (1 # 4)))
                 (1 # 4))
          (Qmult (Qmin (1 # 2) (Qmult (1 # 4) b5j_kL)) (1 # 12)))
          (1 # 2))
          (Qmin
            (Qmult (Qmin (1 # 2)
                   (Qmult (Qmult (Qmult (Qmult a (1 # 2))
                                        (Qinv (b5j_Kvq q))) (1 # 3)) (1 # 4)))
                   (1 # 4))
            (Qmult (Qmin (1 # 2) (Qmult (1 # 4) b5j_kL)) (1 # 12)))
          (Qmult (Qmin (1 # 2)
                 (Qmult (Qmult (Qmult (Qmult a (1 # 2))
                                      (Qinv (b5j_Kvq q))) (1 # 3)) (1 # 4)))
                 (1 # 4))).
      + apply Q.le_min_l.
      + apply Q.le_min_l. }
  assert (HcB : Qle cS (Qmult (Qmin (1 # 2) (Qmult (1 # 4) b5j_kL)) (1 # 12))).
  { apply (Qle_trans cS cE
      (Qmult (Qmin (1 # 2) (Qmult (1 # 4) b5j_kL)) (1 # 12))).
    - unfold cS. apply Q.le_min_l.
    - unfold cE. apply (Qle_trans (Qmin (Qmin
          (Qmult (Qmin (1 # 2)
                 (Qmult (Qmult (Qmult (Qmult a (1 # 2))
                                      (Qinv (b5j_Kvq q))) (1 # 3)) (1 # 4)))
                 (1 # 4))
          (Qmult (Qmin (1 # 2) (Qmult (1 # 4) b5j_kL)) (1 # 12)))
          (1 # 2))
          (Qmin
            (Qmult (Qmin (1 # 2)
                   (Qmult (Qmult (Qmult (Qmult a (1 # 2))
                                        (Qinv (b5j_Kvq q))) (1 # 3)) (1 # 4)))
                   (1 # 4))
            (Qmult (Qmin (1 # 2) (Qmult (1 # 4) b5j_kL)) (1 # 12)))
          (Qmult (Qmin (1 # 2) (Qmult (1 # 4) b5j_kL)) (1 # 12))).
      + apply Q.le_min_l.
      + apply (Qle_trans (Qmin
            (Qmult (Qmin (1 # 2)
                   (Qmult (Qmult (Qmult (Qmult a (1 # 2))
                                        (Qinv (b5j_Kvq q))) (1 # 3)) (1 # 4)))
                   (1 # 4))
            (Qmult (Qmin (1 # 2) (Qmult (1 # 4) b5j_kL)) (1 # 12)))
          (Qmult (Qmin (1 # 2) (Qmult (1 # 4) b5j_kL)) (1 # 12))
          (Qmult (Qmin (1 # 2) (Qmult (1 # 4) b5j_kL)) (1 # 12)));
          [ apply Q.le_min_r | apply Qle_refl ]. }
  assert (HcC : Qle cS (1 # 2)).
  { apply (Qle_trans cS cE (1 # 2)).
    - unfold cS. apply Q.le_min_l.
    - unfold cE. apply Q.le_min_r. }
  assert (HcA2 : Qle cS (Qmult (Qmin (1 # 2)
                 (Qmult (1 # 4)
                        (Qmult (Qmult a (1 # 4))
                               (Qmult (Qinv (Qmult 8 (Qplus 2 1)))
                                      (1 # 2)))))
                           (1 # 12))).
  { apply (Qle_trans cS cG
      (Qmult (Qmin (1 # 2)
             (Qmult (1 # 4)
                    (Qmult (Qmult a (1 # 4))
                           (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2)))))
             (1 # 12))).
    - unfold cS. apply Q.le_min_r.
    - unfold cG. apply (Qle_trans (Qmin (Qmin
          (Qmult (Qmin (1 # 2)
                 (Qmult (1 # 4)
                        (Qmult (Qmult a (1 # 4))
                               (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2)))))
                 (1 # 12))
          (Qmult (Qmult a (1 # 4))
                 (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2))))
          (1 # 2))
          (Qmin
            (Qmult (Qmin (1 # 2)
                   (Qmult (1 # 4)
                          (Qmult (Qmult a (1 # 4))
                                 (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2)))))
                   (1 # 12))
            (Qmult (Qmult a (1 # 4))
                   (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2))))
          (Qmult (Qmin (1 # 2)
                 (Qmult (1 # 4)
                        (Qmult (Qmult a (1 # 4))
                               (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2)))))
                 (1 # 12))).
      + apply Q.le_min_l.
      + apply Q.le_min_l. }
  assert (HcB2 : Qle cS (Qmult (Qmult a (1 # 4))
                               (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2)))).
  { apply (Qle_trans cS cG
      (Qmult (Qmult a (1 # 4))
             (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2)))).
    - unfold cS. apply Q.le_min_r.
    - unfold cG. apply (Qle_trans (Qmin (Qmin
          (Qmult (Qmin (1 # 2)
                 (Qmult (1 # 4)
                        (Qmult (Qmult a (1 # 4))
                               (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2)))))
                 (1 # 12))
          (Qmult (Qmult a (1 # 4))
                 (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2))))
          (1 # 2))
          (Qmin
            (Qmult (Qmin (1 # 2)
                   (Qmult (1 # 4)
                          (Qmult (Qmult a (1 # 4))
                                 (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2)))))
                   (1 # 12))
            (Qmult (Qmult a (1 # 4))
                   (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2))))
          (Qmult (Qmult a (1 # 4))
                 (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2)))).
      + apply Q.le_min_l.
      + apply (Qle_trans (Qmin
            (Qmult (Qmin (1 # 2)
                   (Qmult (1 # 4)
                          (Qmult (Qmult a (1 # 4))
                                 (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2)))))
                   (1 # 12))
            (Qmult (Qmult a (1 # 4))
                   (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2))))
          (Qmult (Qmult a (1 # 4))
                 (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2)))
          (Qmult (Qmult a (1 # 4))
                 (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2))));
          [ apply Q.le_min_r | apply Qle_refl ]. }
  assert (HcC2 : Qle cS (1 # 2)).
  { apply (Qle_trans cS cG (1 # 2)).
    - unfold cS. apply Q.le_min_r.
    - unfold cG. apply Q.le_min_r. }
  unfold real_lt.
  exists e.
  split.
  { apply Qlt_to_QltT. exact Hepos. }
  { exists Nub.
    intros n Hn.
    apply Qlt_to_QltT.
    rewrite (b5dQ_lb_Sdiff_coord q Hq0 Hq1 x Hxr a Ha Nub Hcert n).
    rewrite b5dQ_p_qinv2sq.
    rewrite b5dQ_p_qinv2.
    cbn [projT1 real_const].
    set (Sn := projT1 (b5a_S x) n).
    set (u := projT1 (b5f_u x) n).
    assert (Hug : Qle 1 u) by (unfold u; apply b5dQ_p_u_ge1).
    assert (HcSn : Qle (Qabs Sn) 2) by (exact (Hcert n (NatLe_drop Nub n Hn))).
    assert (HmK0 : Qle 0 (Qmult (Qmult a (1 # 2)) (Qinv (b5j_Kvq q)))).
    { apply Qlt_le_weak.
      apply (Qmult_lt_0_compat (Qmult a (1 # 2)) (Qinv (b5j_Kvq q))).
      - apply (Qmult_lt_0_compat a (1 # 2)); [exact Ha | exact H12].
      - apply Qinv_lt_0_compat. exact (b5j_Kvq_pos q Hq0). }
    assert (HmG0 : Qle 0 (Qmult (Qmult a (1 # 4))
                                (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2)))).
    { apply Qlt_le_weak.
      apply (Qmult_lt_0_compat (Qmult a (1 # 4))
                               (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2))).
      - apply (Qmult_lt_0_compat a (1 # 4)); [exact Ha | exact H14].
      - apply (Qmult_lt_0_compat (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2));
          [exact b5dQ_p4_k2t_pos | exact H12]. }
    (* invM 坐标 ≥ 1#3（|Sn| ≤ 2 尾证书封底） *)
    assert (Hinv : Qle (1 # 3) (Qinv (Qplus 1 (Qabs Sn)))).
    { rewrite <- (b5dQ_p_qinv3).
      apply b5dQ_p_qinv_le_mono.
      - apply (Qlt_le_trans 0 1 (Qplus 1 (Qabs Sn))).
        + apply (QltT_to_Qlt 0 1 qltT_0_1).
        + apply (Qplus_le_compat 1 1 0 (Qabs Sn));
            [apply Qle_refl | apply Qabs_nonneg].
      - exact H13.
      - nra. }
    (* exp 支内层 δlin 第二支 ≥ floorL2（Qinv-封底） *)
    assert (He0 : Qle (Qmult (Qmult (Qmult a (1 # 2)) (Qinv (b5j_Kvq q))) (1 # 3))
                     (Qmult (Qmult (Qmult a (1 # 2)) (Qinv (b5j_Kvq q)))
                            (Qinv (Qplus 1 (Qabs Sn))))).
    { apply (Qle_trans
        (Qmult (Qmult (Qmult a (1 # 2)) (Qinv (b5j_Kvq q))) (1 # 3))
        (Qmult (1 # 3) (Qmult (Qmult a (1 # 2)) (Qinv (b5j_Kvq q))))
        (Qmult (Qmult (Qmult a (1 # 2)) (Qinv (b5j_Kvq q)))
               (Qinv (Qplus 1 (Qabs Sn))))).
      - apply qeq_le. ring.
      - apply (Qle_trans
          (Qmult (1 # 3) (Qmult (Qmult a (1 # 2)) (Qinv (b5j_Kvq q))))
          (Qmult (Qinv (Qplus 1 (Qabs Sn)))
                 (Qmult (Qmult a (1 # 2)) (Qinv (b5j_Kvq q))))
          (Qmult (Qmult (Qmult a (1 # 2)) (Qinv (b5j_Kvq q)))
                 (Qinv (Qplus 1 (Qabs Sn))))).
        + apply (Qmult_le_compat_r (1 # 3) (Qinv (Qplus 1 (Qabs Sn)))
                                   (Qmult (Qmult a (1 # 2)) (Qinv (b5j_Kvq q))));
            [ exact Hinv | exact HmK0 ].
        + apply qeq_le. ring. }
    assert (HdL2 : Qle (Qmult (Qmult (Qmult (Qmult a (1 # 2))
                                            (Qinv (b5j_Kvq q))) (1 # 3)) (1 # 4))
                       (Qmult (Qmult (Qmult (Qmult a (1 # 2))
                                            (Qinv (b5j_Kvq q)))
                                     (Qinv (Qplus 1 (Qabs Sn)))) (1 # 4))).
    { apply (Qmult_le_compat_r
        (Qmult (Qmult (Qmult a (1 # 2)) (Qinv (b5j_Kvq q))) (1 # 3))
        (Qmult (Qmult (Qmult a (1 # 2)) (Qinv (b5j_Kvq q)))
               (Qinv (Qplus 1 (Qabs Sn))))
        (1 # 4)); [ exact He0 | apply Qlt_le_weak; exact H14 ]. }
    (* exp 支 floorL ≤ 内层 δlin 坐标（min-glb 逐支） *)
    assert (HdL : Qle (Qmin (1 # 2)
          (Qmult (Qmult (Qmult (Qmult a (1 # 2)) (Qinv (b5j_Kvq q)))
                        (1 # 3)) (1 # 4)))
                      (Qmin (1 # 2)
        (Qmult (Qmult (Qmult (Qmult a (1 # 2)) (Qinv (b5j_Kvq q)))
                      (Qinv (Qplus 1 (Qabs Sn)))) (1 # 4)))).
    { apply b5dQ_p_min_glb_le.
      - apply Q.le_min_l.
      - apply (Qle_trans (Qmin (1 # 2)
          (Qmult (Qmult (Qmult (Qmult a (1 # 2)) (Qinv (b5j_Kvq q)))
                        (1 # 3)) (1 # 4)))
          (Qmult (Qmult (Qmult (Qmult a (1 # 2)) (Qinv (b5j_Kvq q)))
                        (1 # 3)) (1 # 4))
          (Qmult (Qmult (Qmult (Qmult a (1 # 2)) (Qinv (b5j_Kvq q)))
                        (Qinv (Qplus 1 (Qabs Sn)))) (1 # 4)));
          [ apply Q.le_min_r | exact HdL2 ]. }
    (* exp 支 δL 坐标 ≥ floorD（u ≥ 1 逐支） *)
    assert (HkLpos : Qlt 0 b5j_kL) by (apply QltT_to_Qlt; exact b5j_kL_posT).
    assert (Hq1u : Qle (1 # 2) (Qmult (1 # 2) u)) by nra.
    assert (Hq2u : Qle (Qmult (1 # 4) b5j_kL)
                     (Qmult (1 # 4) (Qmult b5j_kL (Qmult u u)))).
    { apply b5dQ_p_q_scaled_le;
        [ apply Qlt_le_weak; exact H14 | apply Qlt_le_weak; exact HkLpos | exact Hug ]. }
    assert (HfD : Qle (Qmin (1 # 2) (Qmult (1 # 4) b5j_kL))
        (Qmin (Qmult (1 # 2) u)
              (Qmult (1 # 4) (Qmult b5j_kL (Qmult u u))))).
    { apply b5dQ_p_min_glb_le.
      - apply (Qle_trans (Qmin (1 # 2) (Qmult (1 # 4) b5j_kL)) (1 # 2)
                         (Qmult (1 # 2) u));
          [ apply Q.le_min_l | exact Hq1u ].
      - apply (Qle_trans (Qmin (1 # 2) (Qmult (1 # 4) b5j_kL))
                         (Qmult (1 # 4) b5j_kL)
                         (Qmult (1 # 4) (Qmult b5j_kL (Qmult u u))));
          [ apply Q.le_min_r | exact Hq2u ]. }
    (* exp 支两支 floor ≤ 坐标（A1/B1） *)
    assert (FA1 : Qle (Qmult (Qmin (1 # 2)
           (Qmult (Qmult (Qmult (Qmult a (1 # 2)) (Qinv (b5j_Kvq q)))
                         (1 # 3)) (1 # 4))) (1 # 4))
                      (Qmult (Qmin (1 # 2)
        (Qmult (Qmult (Qmult (Qmult a (1 # 2)) (Qinv (b5j_Kvq q)))
                      (Qinv (Qplus 1 (Qabs Sn)))) (1 # 4))) (1 # 4))).
    { apply (Qmult_le_compat_r
        (Qmin (1 # 2)
          (Qmult (Qmult (Qmult (Qmult a (1 # 2)) (Qinv (b5j_Kvq q)))
                        (1 # 3)) (1 # 4)))
        (Qmin (1 # 2)
          (Qmult (Qmult (Qmult (Qmult a (1 # 2)) (Qinv (b5j_Kvq q)))
                        (Qinv (Qplus 1 (Qabs Sn)))) (1 # 4)))
        (1 # 4)); [ exact HdL | apply Qlt_le_weak; exact H14 ]. }
    assert (FB1 : Qle (Qmult (Qmin (1 # 2) (Qmult (1 # 4) b5j_kL)) (1 # 12))
        (Qmult (Qmin (Qmult (1 # 2) u)
                     (Qmult (1 # 4) (Qmult b5j_kL (Qmult u u)))) (1 # 12))).
    { apply (Qmult_le_compat_r (Qmin (1 # 2) (Qmult (1 # 4) b5j_kL))
        (Qmin (Qmult (1 # 2) u)
              (Qmult (1 # 4) (Qmult b5j_kL (Qmult u u))))
        (1 # 12)); [ exact HfD | apply Qlt_le_weak; exact H112 ]. }
    (* g 支内层 δL' 坐标 ≥ floorL'（u ≥ 1 逐支；m := (a·1#4)·k2t·1#2） *)
    assert (Hq1g : Qle (1 # 2) (Qmult (1 # 2) u)) by nra.
    assert (Hq2g : Qle (Qmult (1 # 4)
             (Qmult (Qmult a (1 # 4))
                    (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2))))
                     (Qmult (1 # 4)
        (Qmult (Qmult (Qmult a (1 # 4))
                      (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2)))
               (Qmult u u)))).
    { apply b5dQ_p_q_scaled_le;
        [ apply Qlt_le_weak; exact H14 | exact HmG0 | exact Hug ]. }
    assert (HfG : Qle (Qmin (1 # 2)
        (Qmult (1 # 4)
               (Qmult (Qmult a (1 # 4))
                      (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2)))))
        (Qmin (Qmult (1 # 2) u)
              (Qmult (1 # 4)
        (Qmult (Qmult (Qmult a (1 # 4))
                      (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2)))
               (Qmult u u))))).
    { apply b5dQ_p_min_glb_le.
      - apply (Qle_trans (Qmin (1 # 2)
            (Qmult (1 # 4)
                   (Qmult (Qmult a (1 # 4))
                          (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2)))))
                         (1 # 2) (Qmult (1 # 2) u));
          [ apply Q.le_min_l | exact Hq1g ].
      - apply (Qle_trans (Qmin (1 # 2)
            (Qmult (1 # 4)
                   (Qmult (Qmult a (1 # 4))
                          (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2)))))
                         (Qmult (1 # 4)
                                (Qmult (Qmult a (1 # 4))
                                       (Qmult (Qinv (Qmult 8 (Qplus 2 1)))
                                              (1 # 2))))
                         (Qmult (1 # 4)
        (Qmult (Qmult (Qmult a (1 # 4))
                      (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2)))
               (Qmult u u))));
          [ apply Q.le_min_r | exact Hq2g ]. }
    assert (FA2 : Qle (Qmult (Qmin (1 # 2)
           (Qmult (1 # 4)
                  (Qmult (Qmult a (1 # 4))
                         (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2)))))
                         (1 # 12))
        (Qmult (Qmin (Qmult (1 # 2) u)
              (Qmult (1 # 4)
        (Qmult (Qmult (Qmult a (1 # 4))
                      (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2)))
               (Qmult u u)))) (1 # 12))).
    { apply (Qmult_le_compat_r (Qmin (1 # 2)
           (Qmult (1 # 4)
                  (Qmult (Qmult a (1 # 4))
                         (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2)))))
        (Qmin (Qmult (1 # 2) u)
              (Qmult (1 # 4)
        (Qmult (Qmult (Qmult a (1 # 4))
                      (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2)))
               (Qmult u u))))
        (1 # 12)); [ exact HfG | apply Qlt_le_weak; exact H112 ]. }
    (* 六分支严格 margin（branch_lt；floor 投影链在上） *)
    assert (S1 : Qlt e (Qminus (Qmult (Qmin (1 # 2)
        (Qmult (Qmult (Qmult (Qmult a (1 # 2)) (Qinv (b5j_Kvq q)))
                      (Qinv (Qplus 1 (Qabs Sn)))) (1 # 4))) (1 # 4)) lb)).
    { unfold e, lb.
      apply (b5dQ_p_branch_lt
        (Qmult (Qmin (1 # 2)
          (Qmult (Qmult (Qmult (Qmult a (1 # 2)) (Qinv (b5j_Kvq q)))
                        (Qinv (Qplus 1 (Qabs Sn)))) (1 # 4))) (1 # 4))
        (Qmult (Qmin (1 # 2)
          (Qmult (Qmult (Qmult (Qmult a (1 # 2)) (Qinv (b5j_Kvq q)))
                        (1 # 3)) (1 # 4))) (1 # 4))
        cS); [exact FA1 | exact HcA | exact Hcpos]. }
    assert (S2 : Qlt e (Qminus (Qmult (Qmin (Qmult (1 # 2) u)
              (Qmult (1 # 4) (Qmult b5j_kL (Qmult u u)))) (1 # 12)) lb)).
    { unfold e, lb.
      apply (b5dQ_p_branch_lt
        (Qmult (Qmin (Qmult (1 # 2) u)
                     (Qmult (1 # 4) (Qmult b5j_kL (Qmult u u)))) (1 # 12))
        (Qmult (Qmin (1 # 2) (Qmult (1 # 4) b5j_kL)) (1 # 12))
        cS); [exact FB1 | exact HcB | exact Hcpos]. }
    assert (S3 : Qlt e (Qminus (1 # 2) lb)).
    { unfold e, lb.
      apply (b5dQ_p_branch_lt (1 # 2) (1 # 2) cS);
        [apply Qle_refl | exact HcC | exact Hcpos]. }
    assert (S4 : Qlt e (Qminus (Qmult (Qmin (Qmult (1 # 2) u)
              (Qmult (1 # 4)
        (Qmult (Qmult (Qmult a (1 # 4))
                      (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2)))
               (Qmult u u)))) (1 # 12)) lb)).
    { unfold e, lb.
      apply (b5dQ_p_branch_lt
        (Qmult (Qmin (Qmult (1 # 2) u)
              (Qmult (1 # 4)
        (Qmult (Qmult (Qmult a (1 # 4))
                      (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2)))
               (Qmult u u)))) (1 # 12))
        (Qmult (Qmin (1 # 2)
           (Qmult (1 # 4)
                  (Qmult (Qmult a (1 # 4))
                         (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2)))))
                         (1 # 12))
        cS); [exact FA2 | exact HcA2 | exact Hcpos]. }
    assert (S5 : Qlt e (Qminus (Qmult (Qmult a (1 # 4))
          (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2))) lb)).
    { unfold e, lb.
      apply (b5dQ_p_branch_lt
        (Qmult (Qmult a (1 # 4))
               (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2)))
        (Qmult (Qmult a (1 # 4))
               (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2)))
        cS); [apply Qle_refl | exact HcB2 | exact Hcpos]. }
    assert (S6 : Qlt e (Qminus (1 # 2) lb)).
    { unfold e, lb.
      apply (b5dQ_p_branch_lt (1 # 2) (1 # 2) cS);
        [apply Qle_refl | exact HcC2 | exact Hcpos]. }
    (* 组装：X_n − lb 的 min 树分解（两级 Qmin 减 lb ×3 + min_glb） *)
    rewrite (b5dQ_p_qmin_sub_r
      (Qmin (Qmin
        (Qmult (Qmin (1 # 2)
               (Qmult (Qmult (Qmult (Qmult a (1 # 2))
                                    (Qinv (b5j_Kvq q)))
                             (Qinv (Qplus 1 (Qabs Sn)))) (1 # 4))) (1 # 4))
        (Qmult (Qmin (Qmult (1 # 2) u)
                     (Qmult (1 # 4) (Qmult b5j_kL (Qmult u u)))) (1 # 12)))
        (1 # 2))
      (Qmin (Qmin
        (Qmult (Qmin (Qmult (1 # 2) u)
              (Qmult (1 # 4)
        (Qmult (Qmult (Qmult a (1 # 4))
                      (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2)))
               (Qmult u u)))) (1 # 12))
        (Qmult (Qmult a (1 # 4))
               (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2))))
        (1 # 2))
      (b5dQ_lbSdiff_val q a)).
    rewrite (b5dQ_p_qmin_sub_r
      (Qmin
        (Qmult (Qmin (1 # 2)
               (Qmult (Qmult (Qmult (Qmult a (1 # 2))
                                    (Qinv (b5j_Kvq q)))
                             (Qinv (Qplus 1 (Qabs Sn)))) (1 # 4))) (1 # 4))
        (Qmult (Qmin (Qmult (1 # 2) u)
                     (Qmult (1 # 4) (Qmult b5j_kL (Qmult u u)))) (1 # 12)))
      (1 # 2) (b5dQ_lbSdiff_val q a)).
    rewrite (b5dQ_p_qmin_sub_r
      (Qmult (Qmin (1 # 2)
             (Qmult (Qmult (Qmult (Qmult a (1 # 2))
                                  (Qinv (b5j_Kvq q)))
                           (Qinv (Qplus 1 (Qabs Sn)))) (1 # 4)))
             (1 # 4))
      (Qmult (Qmin (Qmult (1 # 2) u)
                   (Qmult (1 # 4) (Qmult b5j_kL (Qmult u u)))) (1 # 12))
      (b5dQ_lbSdiff_val q a)).
    rewrite (b5dQ_p_qmin_sub_r
      (Qmin
        (Qmult (Qmin (Qmult (1 # 2) u)
              (Qmult (1 # 4)
        (Qmult (Qmult (Qmult a (1 # 4))
                      (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2)))
               (Qmult u u)))) (1 # 12))
        (Qmult (Qmult a (1 # 4))
               (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2))))
      (1 # 2) (b5dQ_lbSdiff_val q a)).
    rewrite (b5dQ_p_qmin_sub_r
      (Qmult (Qmin (Qmult (1 # 2) u)
        (Qmult (1 # 4)
        (Qmult (Qmult (Qmult a (1 # 4))
                      (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2)))
               (Qmult u u)))) (1 # 12))
      (Qmult (Qmult a (1 # 4))
             (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2)))
      (b5dQ_lbSdiff_val q a)).
    apply Q.min_glb_lt.
    - apply Q.min_glb_lt.
      + apply Q.min_glb_lt; [exact S1 | exact S2].
      + exact S3.
    - apply Q.min_glb_lt.
      + apply Q.min_glb_lt; [exact S4 | exact S5].
      + exact S6.
  }
Qed.

(* ===== 段 M23（值族 canonical + G7：tau/kS/m4/delta0 定义与正性，9 Lemma/Def） ===== *)

(* ============================================================ *)
(* M2/M3：δ0 值定义族 + 正性（lb_Jmod 输出 + G7 补闭）            *)
(* ============================================================ *)

(* τ := cA·Qinv(8·K1)（cA := 1#2、M_S := 2：K1 := 2q+1 的 zeta 形） *)
Definition b5dQ_tau (q : Q) : Q :=
  Qmult (1 # 2) (Qinv (Qmult 8 (Qplus (Qmult q 2) 1))).

(* kS := (cA·cB)·(1#8)·invM1 的 zeta 形（cA := 1#2、cB := cA·(1#2)、
   invM1 := Qinv(1+q+1)——J-mod 内部 δS1 叶 eps 份额坐标系数） *)
Definition b5dQ_kS (q : Q) : Q :=
  Qmult (Qmult (Qmult (1 # 2) (Qmult (1 # 2) (1 # 2))) (1 # 8))
        (Qinv (Qplus (Qplus 1 (Qmult q 1)) 1)).

(* eps 份额坐标 a := epsQ/(2q) 正性（J-mod eps 坐标） *)
Lemma b5dQ_p4_a_pos : forall (q epsQ : Q), Qlt 0 q -> Qlt 0 epsQ ->
  Qlt 0 (epsQ / (2 * q)).
Proof.
  intros q epsQ Hq0 Heps.
  unfold Qdiv.
  apply (Qmult_lt_0_compat epsQ (Qinv (2 * q))).
  - exact Heps.
  - apply Qinv_lt_0_compat. exact (b5dL_two_q_pos q Hq0).
Qed.

(* kS(q) 正性（0 < q） *)
Lemma b5dQ_kS_pos : forall (q : Q), Qlt 0 q -> Qlt 0 (b5dQ_kS q).
Proof.
  intros q Hq0.
  unfold b5dQ_kS.
  apply (Qmult_lt_0_compat
    (Qmult (Qmult (1 # 2) (Qmult (1 # 2) (1 # 2))) (1 # 8))
    (Qinv (Qplus (Qplus 1 (Qmult q 1)) 1))).
  - apply (Qmult_lt_0_compat (Qmult (1 # 2) (Qmult (1 # 2) (1 # 2))) (1 # 8)).
    + apply (Qmult_lt_0_compat (1 # 2) (Qmult (1 # 2) (1 # 2))).
      * exact b5dQ_p4_half_pos.
      * apply (Qmult_lt_0_compat (1 # 2) (1 # 2));
          [exact b5dQ_p4_half_pos | exact b5dQ_p4_half_pos].
    + change (Qlt 0 (1 # 8)). unfold Qlt. simpl. lia.
  - apply Qinv_lt_0_compat.
    assert (Hq10 : Qle 0 (Qmult q 1)).
    { apply (Qmult_le_0_compat q 1).
      - apply Qlt_le_weak. exact Hq0.
      - change (Qle 0 1). unfold Qle. simpl. lia. }
    assert (H1p : Qle 1 (Qplus 1 (Qmult q 1))).
    { apply (Qle_trans 1 (Qplus 1 0) (Qplus 1 (Qmult q 1))).
      - apply qeq_imp_qle. ring.
      - apply Qplus_le_compat; [apply Qle_refl | exact Hq10]. }
    apply (Qlt_le_trans 0 1 (Qplus (Qplus 1 (Qmult q 1)) 1)).
    + change (Qlt 0 1). unfold Qlt. simpl. lia.
    + apply (Qle_trans 1 (Qplus 1 0) (Qplus (Qplus 1 (Qmult q 1)) 1)).
      * apply qeq_imp_qle. ring.
      * apply Qplus_le_compat; [exact H1p | apply Qlt_le_weak;
          change (Qlt 0 1); unfold Qlt; simpl; lia].
Qed.

(* τ(q) 正性（0 < q ⟹ 8(2q+1) > 0） *)
Lemma b5dQ_tau_pos : forall (q : Q), Qlt 0 q -> Qlt 0 (b5dQ_tau q).
Proof.
  intros q Hq0.
  unfold b5dQ_tau.
  apply (Qmult_lt_0_compat (1 # 2) (Qinv (Qmult 8 (Qplus (Qmult q 2) 1)))).
  - exact b5dQ_p4_half_pos.
  - apply Qinv_lt_0_compat.
    assert (Hq20 : Qlt 0 (Qmult q 2)).
    { apply (Qmult_lt_0_compat q 2).
      - exact Hq0.
      - unfold Qlt. simpl. lia. }
    assert (H8p : Qlt 0 (Qmult 8 (Qplus (Qmult q 2) 1))).
    { apply (Qmult_lt_0_compat 8 (Qplus (Qmult q 2) 1)).
      - unfold Qlt. simpl. lia.
      - apply (Qlt_le_trans 0 (Qmult q 2) (Qplus (Qmult q 2) 1)).
        + exact Hq20.
        + apply (Qle_trans (Qmult q 2) (Qplus (Qmult q 2) 0)
                           (Qplus (Qmult q 2) 1)).
          * apply qeq_imp_qle. ring.
          * apply Qplus_le_compat; [apply Qle_refl | apply Qlt_le_weak;
              change (Qlt 0 1); unfold Qlt; simpl; lia]. }
    exact H8p.
Qed.

(* m4 := min(τ, lb_E@a, lb_S@a1, lb_S@1)（四分支 lb 值之 min——
   顺序照 J-mod δ 树：min(min(min δE δS1) δS2) τ） *)
Definition b5dQ_m4 (q epsQ : Q) : Q :=
  Qmin (Qmin (Qmin
    (Qmult (b5dQ_vE q (epsQ / (2 * q))) (1 # 2))
    (b5dQ_lbSdiff_val q (Qmult (epsQ / (2 * q)) (b5dQ_kS q))))
    (b5dQ_lbSdiff_val q 1))
  (b5dQ_tau q).

(* δ0 := m4/2（lb_Jmod 输出；严格下界裕量） *)
Definition b5dQ_delta0 (q epsQ : Q) : Q :=
  Qmult (b5dQ_m4 q epsQ) (1 # 2).

(* m4 正性（M3 前置：四分量正 + min-glb） *)
Lemma b5dQ_m4_pos : forall (q epsQ : Q),
  Qlt 0 q -> Qlt q 1 -> Qlt 0 epsQ -> Qlt 0 (b5dQ_m4 q epsQ).
Proof.
  intros q epsQ Hq0 Hq1 Heps.
  assert (Ha : Qlt 0 (epsQ / (2 * q))) by (exact (b5dQ_p4_a_pos q epsQ Hq0 Heps)).
  assert (Ha1 : Qlt 0 (Qmult (epsQ / (2 * q)) (b5dQ_kS q))).
  { apply (Qmult_lt_0_compat (epsQ / (2 * q)) (b5dQ_kS q));
      [exact Ha | exact (b5dQ_kS_pos q Hq0)]. }
  unfold b5dQ_m4.
  apply Q.min_glb_lt.
  - apply Q.min_glb_lt.
    + apply Q.min_glb_lt.
      * apply (Qmult_lt_0_compat (b5dQ_vE q (epsQ / (2 * q))) (1 # 2));
          [ exact (b5dQ_vE_pos q (epsQ / (2 * q)) Hq0 Hq1 Ha)
          | exact b5dQ_p4_half_pos ].
      * exact (b5dQ_lbSdiff_pos q (Qmult (epsQ / (2 * q)) (b5dQ_kS q))
                 (b5dH_q_pos_le q Hq0) Ha1).
    + exact (b5dQ_lbSdiff_pos q 1 (b5dH_q_pos_le q Hq0) b5dQ_H1pos).
  - exact (b5dQ_tau_pos q Hq0).
Qed.

(* M3：δ0 正性（G7 补闭——~10 行照 P3 §4 遗留 1 机制） *)
Lemma b5dQ_delta0_pos : forall (q epsQ : Q),
  Qlt 0 q -> Qlt q 1 -> Qlt 0 epsQ -> Qlt 0 (b5dQ_delta0 q epsQ).
Proof.
  intros q epsQ Hq0 Hq1 Heps.
  unfold b5dQ_delta0.
  apply (Qmult_lt_0_compat (b5dQ_m4 q epsQ) (1 # 2));
    [ exact (b5dQ_m4_pos q epsQ Hq0 Hq1 Heps)
    | exact b5dQ_p4_half_pos ].
Qed.

(* ===== 段 P4g（变体件：b5dQ_p4g_J_tail_lb_var 三层证书 + Part 0-2，13 Lemma/Def） ===== *)

(* ============================================================ *)
(* Part 0：Q 层——δ0 := m4/2 < 四分支 lb 值（依设计 §3 模式）       *)
(* ============================================================ *)

(* 半量严格：Qle m b -> Qlt 0 b -> Qlt (m·(1#2)) b *)
Lemma b5dQ_p4g_half_strict : forall (m b : Q),
  Qle m b -> Qlt 0 b -> Qlt (Qmult m (1 # 2)) b.
Proof.
  intros m b Hmb Hb0.
  apply (Qle_lt_trans (Qmult m (1 # 2)) (Qmult b (1 # 2)) b).
  - apply (Qmult_le_compat_r m b (1 # 2)).
    + exact Hmb.
    + change (Qle 0 (1 # 2)). unfold Qle. simpl. lia.
  - nra.
Qed.

(* m4 ≤ lbE 支（A := vE(q,a)/2——min 树左最内投影） *)
Lemma b5dQ_p4g_m4_le_E : forall (q epsQ : Q),
  Qle (b5dQ_m4 q epsQ)
      (Qmult (b5dQ_vE q (epsQ / (2 * q))) (1 # 2)).
Proof.
  intros q epsQ.
  unfold b5dQ_m4.
  apply (Qle_trans _ (Qmin
    (Qmin (Qmult (b5dQ_vE q (epsQ / (2 * q))) (1 # 2))
          (b5dQ_lbSdiff_val q (Qmult (epsQ / (2 * q)) (b5dQ_kS q))))
    (b5dQ_lbSdiff_val q 1)) _).
  - apply Q.le_min_l.
  - apply (Qle_trans _ (Qmin
      (Qmult (b5dQ_vE q (epsQ / (2 * q))) (1 # 2))
      (b5dQ_lbSdiff_val q (Qmult (epsQ / (2 * q)) (b5dQ_kS q)))) _).
    + apply Q.le_min_l.
    + apply Q.le_min_l.
Qed.

(* m4 ≤ lbS1 支（B := lbSdiff_val q (a·kS(q))） *)
Lemma b5dQ_p4g_m4_le_S1 : forall (q epsQ : Q),
  Qle (b5dQ_m4 q epsQ)
      (b5dQ_lbSdiff_val q (Qmult (epsQ / (2 * q)) (b5dQ_kS q))).
Proof.
  intros q epsQ.
  unfold b5dQ_m4.
  apply (Qle_trans _ (Qmin
    (Qmin (Qmult (b5dQ_vE q (epsQ / (2 * q))) (1 # 2))
          (b5dQ_lbSdiff_val q (Qmult (epsQ / (2 * q)) (b5dQ_kS q))))
    (b5dQ_lbSdiff_val q 1)) _).
  - apply Q.le_min_l.
  - apply (Qle_trans _ (Qmin
      (Qmult (b5dQ_vE q (epsQ / (2 * q))) (1 # 2))
      (b5dQ_lbSdiff_val q (Qmult (epsQ / (2 * q)) (b5dQ_kS q)))) _).
    + apply Q.le_min_l.
    + apply Q.le_min_r.
Qed.

(* m4 ≤ lbS2 支（C := lbSdiff_val q 1） *)
Lemma b5dQ_p4g_m4_le_S2 : forall (q epsQ : Q),
  Qle (b5dQ_m4 q epsQ) (b5dQ_lbSdiff_val q 1).
Proof.
  intros q epsQ.
  unfold b5dQ_m4.
  apply (Qle_trans _ (Qmin
    (Qmin (Qmult (b5dQ_vE q (epsQ / (2 * q))) (1 # 2))
          (b5dQ_lbSdiff_val q (Qmult (epsQ / (2 * q)) (b5dQ_kS q))))
    (b5dQ_lbSdiff_val q 1)) _).
  - apply Q.le_min_l.
  - apply Q.le_min_r.
Qed.

(* m4 ≤ τ 支（D := b5dQ_tau q） *)
Lemma b5dQ_p4g_m4_le_tau : forall (q epsQ : Q),
  Qle (b5dQ_m4 q epsQ) (b5dQ_tau q).
Proof.
  intros q epsQ.
  unfold b5dQ_m4.
  apply Q.le_min_r.
Qed.

(* Qlt (m4/2) (lbE 值) *)
Lemma b5dQ_p4g_qlt_E : forall (q epsQ : Q),
  Qlt 0 q -> Qlt q 1 -> Qlt 0 epsQ ->
  Qlt (b5dQ_delta0 q epsQ)
      (Qmult (b5dQ_vE q (epsQ / (2 * q))) (1 # 2)).
Proof.
  intros q epsQ Hq0 Hq1 HepsQ.
  assert (Ha : Qlt 0 (epsQ / (2 * q)))
    by (exact (b5dQ_p4_a_pos q epsQ Hq0 HepsQ)).
  unfold b5dQ_delta0.
  apply b5dQ_p4g_half_strict.
  - exact (b5dQ_p4g_m4_le_E q epsQ).
  - apply (Qmult_lt_0_compat (b5dQ_vE q (epsQ / (2 * q))) (1 # 2)).
    + exact (b5dQ_vE_pos q (epsQ / (2 * q)) Hq0 Hq1 Ha).
    + exact b5dQ_p4_half_pos.
Qed.

(* Qlt (m4/2) (lbS1 值) *)
Lemma b5dQ_p4g_qlt_S1 : forall (q epsQ : Q),
  Qlt 0 q -> Qlt q 1 -> Qlt 0 epsQ ->
  Qlt (b5dQ_delta0 q epsQ)
      (b5dQ_lbSdiff_val q (Qmult (epsQ / (2 * q)) (b5dQ_kS q))).
Proof.
  intros q epsQ Hq0 Hq1 HepsQ.
  assert (Ha : Qlt 0 (epsQ / (2 * q)))
    by (exact (b5dQ_p4_a_pos q epsQ Hq0 HepsQ)).
  assert (Ha1 : Qlt 0 (Qmult (epsQ / (2 * q)) (b5dQ_kS q))).
  { apply (Qmult_lt_0_compat (epsQ / (2 * q)) (b5dQ_kS q)).
    - exact Ha.
    - exact (b5dQ_kS_pos q Hq0). }
  unfold b5dQ_delta0.
  apply b5dQ_p4g_half_strict.
  - exact (b5dQ_p4g_m4_le_S1 q epsQ).
  - exact (b5dQ_lbSdiff_pos q (Qmult (epsQ / (2 * q)) (b5dQ_kS q))
             (Qlt_le_weak 0 q Hq0) Ha1).
Qed.

(* Qlt (m4/2) (lbS2 值) *)
Lemma b5dQ_p4g_qlt_S2 : forall (q epsQ : Q),
  Qlt 0 q -> Qlt q 1 -> Qlt 0 epsQ ->
  Qlt (b5dQ_delta0 q epsQ) (b5dQ_lbSdiff_val q 1).
Proof.
  intros q epsQ Hq0 Hq1 HepsQ.
  unfold b5dQ_delta0.
  apply b5dQ_p4g_half_strict.
  - exact (b5dQ_p4g_m4_le_S2 q epsQ).
  - exact (b5dQ_lbSdiff_pos q 1 (Qlt_le_weak 0 q Hq0) b5dQ_H1pos).
Qed.

(* Qlt (m4/2) (τ 值) *)
Lemma b5dQ_p4g_qlt_tau : forall (q epsQ : Q),
  Qlt 0 q -> Qlt q 1 -> Qlt 0 epsQ ->
  Qlt (b5dQ_delta0 q epsQ) (b5dQ_tau q).
Proof.
  intros q epsQ Hq0 Hq1 HepsQ.
  unfold b5dQ_delta0.
  apply b5dQ_p4g_half_strict.
  - exact (b5dQ_p4g_m4_le_tau q epsQ).
  - exact (b5dQ_tau_pos q Hq0).
Qed.

(* ============================================================ *)
(* Part 1：三叶 canonical app 封装 + 叶 lb 直实例化               *)
(*   （语句 = b5dQ_lb_E/b5dQ_lb_Sdiff 结论逐字——app 参数形照抄   *)
(*     零偏差；证书 = 构造子形——b5dM_/b5dQ_ 透明族 + 参数直传，   *)
(*     非段B 体内派生（P4 定案墙类）；绕墙核心）                  *)
(* ============================================================ *)

(* E 叶封装（lb_E 直实例化——canonical E-app @ 份额 a·(1#32)） *)
Lemma b5dQ_p4g_leaf_E : forall (q : Q) (Hq0 : Qlt 0 q) (Hq1 : Qlt q 1)
  (x : Real) (Hxr : forall n : nat, QleT' (Qabs (projT1 x n)) q)
  (Hs : forall n : nat,
         Qle (Qabs (sin_partial n (arctan_partial n (projT1 x n)))) 1)
  (Hc : forall n : nat,
         Qle (Qabs (cos_partial n (arctan_partial n (projT1 x n)))) 1)
  (a : Q) (Ha : Qlt 0 a),
  real_lt (real_const (Qmult (b5dQ_vE q a) (1 # 2)))
    (projT1 (b5dI_E_diff_closed_r_exp q (Qlt_le_weak 0 q Hq0) Hq1 x Hxr
              1 1 b5d3_exp_arch4_C b5dQ_H1pos b5dQ_H1pos b5dQ_HC40
              b5d3_exp_arch4_C_ge1 b5d3_exp_arch4_C_all Hs Hc
              (real_mult (real_const a) (real_const (1 # 32)))
              (b5dI_real_mult_positive_exp (real_const a) (real_const (1 # 32))
                 (b5dM_real_const_pos a (Qlt_to_QltT 0 a Ha))
                 (b5dM_real_const_pos (1 # 32) b5dQ_Hq32T)))).
Proof.
  intros q Hq0 Hq1 x Hxr Hs Hc a Ha.
  exact (b5dQ_lb_E q Hq0 Hq1 x Hxr Hs Hc a Ha).
Qed.

(* S 叶封装（lb_Sdiff 直实例化——canonical S-app @ const 形份额 a） *)
Lemma b5dQ_p4g_leaf_S : forall (q : Q) (Hq0 : Qle 0 q) (Hq1 : Qlt q 1)
  (x : Real) (Hxr : forall n : nat, QleT' (Qabs (projT1 x n)) q)
  (a : Q) (Ha : Qlt 0 a)
  (Nub : nat)
  (Hcert : forall n : nat, (Nub <= n)%nat ->
           Qle (Qabs (projT1 (b5a_S x) n)) 2),
  real_lt (real_const (b5dQ_lbSdiff_val q a))
    (projT1 (b5dP_S_diff_closed_r_M_exp_tail q Hq0 Hq1 x Hxr 2
      b5dQ_p4_two_pos Nub Hcert (real_const a)
      (real_const_pos a (Qlt_to_QltT 0 a Ha)))).
Proof.
  intros q Hq0 Hq1 x Hxr a Ha Nub Hcert.
  exact (b5dQ_lb_Sdiff q Hq0 Hq1 x Hxr a Ha Nub Hcert).
Qed.

(* ============================================================ *)
(* Part 2：树 lb——real_lt (real_const δ0) (real_min 树)          *)
(*   min-glue（b5dQ_min_lb ×3）+ real_lt_trans（泛 x）      *)
(* ============================================================ *)

Lemma b5dQ_p4g_tree_lb :
  forall (q : Q) (Hq0 : Qlt 0 q) (Hq1 : Qlt q 1)
  (epsQ : Q) (HepsQ : Qlt 0 epsQ)
  (x : Real) (Hxr : forall n : nat, QleT' (Qabs (projT1 x n)) q)
  (NM : nat)
  (HMall : forall n : nat, (NM <= n)%nat ->
           Qle (Qabs (projT1 (b5a_S x) n)) 2)
  (Hs : forall n : nat,
         Qle (Qabs (sin_partial n (arctan_partial n (projT1 x n)))) 1)
  (Hc : forall n : nat,
         Qle (Qabs (cos_partial n (arctan_partial n (projT1 x n)))) 1),
  real_lt (real_const (b5dQ_delta0 q epsQ))
    (real_min (real_min (real_min
      (projT1 (b5dI_E_diff_closed_r_exp q (Qlt_le_weak 0 q Hq0) Hq1 x Hxr
                1 1 b5d3_exp_arch4_C b5dQ_H1pos b5dQ_H1pos b5dQ_HC40
                b5d3_exp_arch4_C_ge1 b5d3_exp_arch4_C_all Hs Hc
                (real_mult (real_const (epsQ / (2 * q))) (real_const (1 # 32)))
                (b5dI_real_mult_positive_exp (real_const (epsQ / (2 * q)))
                   (real_const (1 # 32))
                   (b5dM_real_const_pos (epsQ / (2 * q))
                      (Qlt_to_QltT 0 (epsQ / (2 * q))
                         (b5dQ_p4_a_pos q epsQ Hq0 HepsQ)))
                   (b5dM_real_const_pos (1 # 32) b5dQ_Hq32T))))
      (projT1 (b5dP_S_diff_closed_r_M_exp_tail q (Qlt_le_weak 0 q Hq0) Hq1 x Hxr
                2 b5dQ_p4_two_pos NM HMall
                (real_const (Qmult (epsQ / (2 * q)) (b5dQ_kS q)))
                (real_const_pos (Qmult (epsQ / (2 * q)) (b5dQ_kS q))
                   (Qlt_to_QltT 0 (Qmult (epsQ / (2 * q)) (b5dQ_kS q))
                      (Qmult_lt_0_compat (epsQ / (2 * q)) (b5dQ_kS q)
                         (b5dQ_p4_a_pos q epsQ Hq0 HepsQ)
                         (b5dQ_kS_pos q Hq0)))))))
      (projT1 (b5dP_S_diff_closed_r_M_exp_tail q (Qlt_le_weak 0 q Hq0) Hq1 x Hxr
                2 b5dQ_p4_two_pos NM HMall
                (real_const 1)
                (real_const_pos 1 (Qlt_to_QltT 0 1 b5dQ_H1pos)))))
      (real_const (b5dQ_tau q))).
Proof.
  intros q Hq0 Hq1 epsQ HepsQ x Hxr NM HMall Hs Hc.
  assert (Ha : Qlt 0 (epsQ / (2 * q)))
    by (exact (b5dQ_p4_a_pos q epsQ Hq0 HepsQ)).
  assert (Ha1 : Qlt 0 (Qmult (epsQ / (2 * q)) (b5dQ_kS q))).
  { apply (Qmult_lt_0_compat (epsQ / (2 * q)) (b5dQ_kS q)).
    - exact Ha.
    - exact (b5dQ_kS_pos q Hq0). }
  set (dE := projT1 (b5dI_E_diff_closed_r_exp q (Qlt_le_weak 0 q Hq0) Hq1 x Hxr
           1 1 b5d3_exp_arch4_C b5dQ_H1pos b5dQ_H1pos b5dQ_HC40
           b5d3_exp_arch4_C_ge1 b5d3_exp_arch4_C_all Hs Hc
           (real_mult (real_const (epsQ / (2 * q))) (real_const (1 # 32)))
           (b5dI_real_mult_positive_exp (real_const (epsQ / (2 * q)))
              (real_const (1 # 32))
              (b5dM_real_const_pos (epsQ / (2 * q))
                 (Qlt_to_QltT 0 (epsQ / (2 * q))
                    (b5dQ_p4_a_pos q epsQ Hq0 HepsQ)))
              (b5dM_real_const_pos (1 # 32) b5dQ_Hq32T)))).
  set (dS1 := projT1 (b5dP_S_diff_closed_r_M_exp_tail q (Qlt_le_weak 0 q Hq0) Hq1 x Hxr
           2 b5dQ_p4_two_pos NM HMall
           (real_const (Qmult (epsQ / (2 * q)) (b5dQ_kS q)))
           (real_const_pos (Qmult (epsQ / (2 * q)) (b5dQ_kS q))
              (Qlt_to_QltT 0 (Qmult (epsQ / (2 * q)) (b5dQ_kS q))
                 (Qmult_lt_0_compat (epsQ / (2 * q)) (b5dQ_kS q)
                    (b5dQ_p4_a_pos q epsQ Hq0 HepsQ)
                    (b5dQ_kS_pos q Hq0)))))).
  set (dS2 := projT1 (b5dP_S_diff_closed_r_M_exp_tail q (Qlt_le_weak 0 q Hq0) Hq1 x Hxr
           2 b5dQ_p4_two_pos NM HMall
           (real_const 1)
           (real_const_pos 1 (Qlt_to_QltT 0 1 b5dQ_H1pos)))).
  assert (HqE : real_lt (real_const (b5dQ_delta0 q epsQ))
                        (real_const (Qmult (b5dQ_vE q (epsQ / (2 * q))) (1 # 2)))).
  { apply real_const_lt. exact (b5dQ_p4g_qlt_E q epsQ Hq0 Hq1 HepsQ). }
  assert (HlbE : real_lt (real_const (Qmult (b5dQ_vE q (epsQ / (2 * q))) (1 # 2))) dE).
  { unfold dE. exact (b5dQ_p4g_leaf_E q Hq0 Hq1 x Hxr Hs Hc
                        (epsQ / (2 * q)) Ha). }
  assert (HdE : real_lt (real_const (b5dQ_delta0 q epsQ)) dE).
  { apply (real_lt_trans (real_const (b5dQ_delta0 q epsQ))
                         (real_const (Qmult (b5dQ_vE q (epsQ / (2 * q))) (1 # 2)))
                         dE HqE HlbE). }
  assert (HqS1 : real_lt (real_const (b5dQ_delta0 q epsQ))
                         (real_const (b5dQ_lbSdiff_val q
                            (Qmult (epsQ / (2 * q)) (b5dQ_kS q))))).
  { apply real_const_lt. exact (b5dQ_p4g_qlt_S1 q epsQ Hq0 Hq1 HepsQ). }
  assert (HlbS1 : real_lt (real_const (b5dQ_lbSdiff_val q
                            (Qmult (epsQ / (2 * q)) (b5dQ_kS q)))) dS1).
  { unfold dS1. exact (b5dQ_p4g_leaf_S q (Qlt_le_weak 0 q Hq0) Hq1 x Hxr
                         (Qmult (epsQ / (2 * q)) (b5dQ_kS q)) Ha1 NM HMall). }
  assert (HdS1 : real_lt (real_const (b5dQ_delta0 q epsQ)) dS1).
  { apply (real_lt_trans (real_const (b5dQ_delta0 q epsQ))
                         (real_const (b5dQ_lbSdiff_val q
                            (Qmult (epsQ / (2 * q)) (b5dQ_kS q))))
                         dS1 HqS1 HlbS1). }
  assert (HqS2 : real_lt (real_const (b5dQ_delta0 q epsQ))
                         (real_const (b5dQ_lbSdiff_val q 1))).
  { apply real_const_lt. exact (b5dQ_p4g_qlt_S2 q epsQ Hq0 Hq1 HepsQ). }
  assert (HlbS2 : real_lt (real_const (b5dQ_lbSdiff_val q 1)) dS2).
  { unfold dS2. exact (b5dQ_p4g_leaf_S q (Qlt_le_weak 0 q Hq0) Hq1 x Hxr
                         1 b5dQ_H1pos NM HMall). }
  assert (HdS2 : real_lt (real_const (b5dQ_delta0 q epsQ)) dS2).
  { apply (real_lt_trans (real_const (b5dQ_delta0 q epsQ))
                         (real_const (b5dQ_lbSdiff_val q 1))
                         dS2 HqS2 HlbS2). }
  assert (HdT : real_lt (real_const (b5dQ_delta0 q epsQ))
                        (real_const (b5dQ_tau q))).
  { apply real_const_lt. exact (b5dQ_p4g_qlt_tau q epsQ Hq0 Hq1 HepsQ). }
  apply (b5dQ_min_lb (real_const (b5dQ_delta0 q epsQ))
                     (real_min (real_min dE dS1) dS2)
                     (real_const (b5dQ_tau q))).
  - apply (b5dQ_min_lb (real_const (b5dQ_delta0 q epsQ))
                       (real_min dE dS1) dS2).
    + apply (b5dQ_min_lb (real_const (b5dQ_delta0 q epsQ)) dE dS1).
      * exact HdE.
      * exact HdS1.
    + exact HdS2.
  - exact HdT.
Qed.

(* ============================================================ *)
Lemma b5dQ_p4g_J_tail_lb_var :
  forall (q : Q) (Hq0 : Qlt 0 q) (Hq1 : Qlt q 1)
  (epsQ : Q) (HepsQ : Qlt 0 epsQ)
  (M : nat) (HMpos : (0 < M)%nat) (k : nat) (HkM : (k < M)%nat)
  (Hxr : forall n : nat,
     QleT' (Qabs (projT1 (real_const (b5dL_tkq q M k)) n)) q)
  (NA : nat)
  (HNA : forall n : nat, (NA <= n)%nat ->
         Qle (1 # 2) (projT1 (b5a_S (real_const (b5dL_tkq q M k))) n))
  (NM : nat)
  (HMall : forall n : nat, (NM <= n)%nat ->
           Qle (Qabs (projT1 (b5a_S (real_const (b5dL_tkq q M k))) n)) 2)
  (Hs : forall n : nat,
         Qle (Qabs (sin_partial n (arctan_partial n
                (projT1 (real_const (b5dL_tkq q M k)) n)))) 1)
  (Hc : forall n : nat,
         Qle (Qabs (cos_partial n (arctan_partial n
                (projT1 (real_const (b5dL_tkq q M k)) n)))) 1),
  sigT (fun delta : Real => And (real_lt real_zero delta)
    (And (forall (h : Real), real_lt (real_abs h) delta ->
       forall (Hxh : forall n : nat,
          QleT' (Qabs (projT1 (real_plus (real_const (b5dL_tkq q M k)) h) n)) 1),
       forall (eps' : Real), real_lt real_zero eps' ->
       real_le (real_abs (real_plus
                  (b5c_J (real_plus (real_const (b5dL_tkq q M k)) h) Hxh)
                  (real_opp (b5c_J (real_const (b5dL_tkq q M k))
                             (b3rr_dom_r1 (real_const (b5dL_tkq q M k)) q Hxr Hq1)))))
               (real_plus (real_mult (real_const (epsQ / (2 * q))) (real_abs h)) eps'))
         (real_lt (real_const (b5dQ_delta0 q epsQ)) delta))).
Proof.
  intros q Hq0 Hq1 epsQ HepsQ Mg HMpos k HkM Hxr NA HNA NM HMall HMs_all HMc_all.
  (* ---- 实例面数据（实例化：x := real_const (b5dL_tkq q Mg k)、
     a := epsQ/(2q)、r := q、cA := 1#2、M := 2、Ms := Mc := 1、
     eps := real_const a——段B 体内参数在实例面的闭值） ---- *)
  set (x := real_const (b5dL_tkq q Mg k)).
  set (a := epsQ / (2 * q)).
  assert (Ha : Qlt 0 a).
  { unfold a. exact (b5dQ_p4_a_pos q epsQ Hq0 HepsQ). }
  set (r := q).
  assert (Hr0 : Qle 0 r).
  { unfold r. exact (Qlt_le_weak 0 q Hq0). }
  assert (Hr1 : Qlt r 1).
  { unfold r. exact Hq1. }
  set (cA := (1 # 2)).
  assert (HcA : Qlt 0 cA).
  { unfold cA. exact b5dQ_p4_half_pos. }
  set (M := 2).
  assert (HM : Qlt 0 M).
  { unfold M. exact b5dQ_p4_two_pos. }
  set (Ms := 1).
  assert (HMs : QltT 0 Ms).
  { unfold Ms. exact b5dQ_H1T. }
  set (Mc := 1).
  assert (HMc : QltT 0 Mc).
  { unfold Mc. exact b5dQ_H1T. }
  set (eps := real_const a).
  assert (Heps : real_lt real_zero eps).
  { unfold eps. exact (real_const_pos a (Qlt_to_QltT 0 a Ha)). }

  set (Hx := b3rr_dom_r1 x r Hxr Hq1).
  (* ---- 固定数据 ---- *)
  (* cA：S(x) 逐点正下界——语句显式 Q 参数 cA/HcA + NA 尾界前提 HNA； *)
  (* δ-C C5：4 处黑盒 destruct（源 L389/396/399/400）→ intros 参数束 *)
  set (cB := Qmult cA (1 # 2)).
  assert (HcB : Qlt 0 cB).
  { unfold cB. apply (Qmult_lt_0_compat cA (1 # 2)).
    - exact HcA.
    - change (Qlt 0 (1 # 2)). unfold Qlt. simpl. lia. }
  (* M/Ms/Mc：语句显式 Q 参数；全 n 前提 HMall/HMs_all/HMc_all 直接应用 *)
  assert (HM0 : Qle 0 M). { apply Qlt_le_weak. exact HM. }
  (* Ms/Mc：sinA/cosA 逐点界 ⟹ ME := Ms + r·Mc（|E(x)_n| ≤ ME）     *)
  assert (HMs0 : Qle 0 Ms). { apply Qlt_le_weak. apply QltT_to_Qlt. exact HMs. }
  assert (HMc0 : Qle 0 Mc). { apply Qlt_le_weak. apply QltT_to_Qlt. exact HMc. }
  (* E/S-diff 换源证书（item25 改动 S3：b5dI_E_diff_closed_r_exp 束参数——
     QltT_to_Qlt 证明侧应用；C4 闭值 = item7 b5d3_exp_arch4_C） *)
  assert (HMsQ : Qlt 0 Ms). { apply QltT_to_Qlt. exact HMs. }
  assert (HMcQ : Qlt 0 Mc). { apply QltT_to_Qlt. exact HMc. }
  assert (HC40C : Qle 0 b5d3_exp_arch4_C).
  { apply (Qle_trans _ 1 _). { exact Qle_0_1. } { apply QleT'_to_Qle. exact b5d3_exp_arch4_C_ge1. } }
  assert (Hr0' : Qle 0 r). { exact Hr0. }
  set (ME := Qplus Ms (Qmult r Mc)).
  assert (HME0 : Qle 0 ME).
  { unfold ME. nra. }
  (* 逆常数与份额（全部只依赖 x 数据；QltT 0 用于 real_const_pos） *)
  set (QicA := Qinv cA).
  set (QicB := Qinv cB).
  set (kE := Qmult cB (1 # 8)).
  set (kEp := Qmult cB (1 # 16)).
  set (kapE := Qmult cB (1 # 16)).
  set (invM1 := Qinv (Qplus ME 1)).
  set (kS := Qmult (Qmult (Qmult cA cB) (1 # 8)) invM1).
  set (kSp := Qmult (Qmult (Qmult cA cB) (1 # 16)) invM1).
  set (kapS := Qmult (Qmult (Qmult cA cB) (1 # 16)) invM1).
  set (K1 := Qplus (Qmult r M) 1).
  set (tau := Qmult cA (Qinv (Qmult 8 K1))).
  set (mu := Qmult cA (1 # 16)).
  set (kapS2 := Qmult cA (1 # 16)).
  (* 正性事实 *)
  assert (HkET : QltT 0 kE).
  { unfold kE. apply Qlt_to_QltT. apply (Qmult_lt_0_compat cB (1 # 8)).
    - exact HcB.
    - change (Qlt 0 (1 # 8)). unfold Qlt. simpl. lia. }
  assert (HkEpT : QltT 0 kEp).
  { unfold kEp. apply Qlt_to_QltT. apply (Qmult_lt_0_compat cB (1 # 16)).
    - exact HcB.
    - change (Qlt 0 (1 # 16)). unfold Qlt. simpl. lia. }
  assert (HkapET : QltT 0 kapE).
  { unfold kapE. apply Qlt_to_QltT. apply (Qmult_lt_0_compat cB (1 # 16)).
    - exact HcB.
    - change (Qlt 0 (1 # 16)). unfold Qlt. simpl. lia. }
  assert (HME1 : Qlt 0 (Qplus ME 1)).
  { nra. }
  assert (HME1ne : ~ Qplus ME 1 == 0).
  { apply q_neq_of_lt. exact HME1. }
  assert (Hinv1T : QltT 0 invM1).
  { unfold invM1. apply Qlt_to_QltT. apply Qinv_lt_0_compat. exact HME1. }
  assert (HcAcB0 : Qlt 0 (Qmult (Qmult cA cB) (1 # 8))).
  { apply (Qmult_lt_0_compat (Qmult cA cB) (1 # 8)).
    - apply (Qmult_lt_0_compat cA cB). { exact HcA. } { exact HcB. }
    - change (Qlt 0 (1 # 8)). unfold Qlt. simpl. lia. }
  assert (HcAcB0b : Qlt 0 (Qmult (Qmult cA cB) (1 # 16))).
  { apply (Qmult_lt_0_compat (Qmult cA cB) (1 # 16)).
    - apply (Qmult_lt_0_compat cA cB). { exact HcA. } { exact HcB. }
    - change (Qlt 0 (1 # 16)). unfold Qlt. simpl. lia. }
  assert (HkST : QltT 0 kS).
  { unfold kS. apply Qlt_to_QltT.
    apply (Qmult_lt_0_compat (Qmult (Qmult cA cB) (1 # 8)) invM1).
    - exact HcAcB0.
    - apply QltT_to_Qlt. exact Hinv1T. }
  assert (HkSpT : QltT 0 kSp).
  { unfold kSp. apply Qlt_to_QltT.
    apply (Qmult_lt_0_compat (Qmult (Qmult cA cB) (1 # 16)) invM1).
    - exact HcAcB0b.
    - apply QltT_to_Qlt. exact Hinv1T. }
  assert (HkapST : QltT 0 kapS).
  { unfold kapS. apply Qlt_to_QltT.
    apply (Qmult_lt_0_compat (Qmult (Qmult cA cB) (1 # 16)) invM1).
    - exact HcAcB0b.
    - apply QltT_to_Qlt. exact Hinv1T. }
  assert (HK1 : Qlt 0 K1).
  { unfold K1. nra. }
  assert (HtauT : QltT 0 tau).
  { unfold tau. apply Qlt_to_QltT.
    apply (Qmult_lt_0_compat cA (Qinv (Qmult 8 K1))).
    - exact HcA.
    - apply Qinv_lt_0_compat. nra. }
  assert (HmuT : QltT 0 mu).
  { unfold mu. apply Qlt_to_QltT. apply (Qmult_lt_0_compat cA (1 # 16)).
    - exact HcA.
    - change (Qlt 0 (1 # 16)). unfold Qlt. simpl. lia. }
  assert (HkapS2T : QltT 0 kapS2).
  { unfold kapS2. apply Qlt_to_QltT. apply (Qmult_lt_0_compat cA (1 # 16)).
    - exact HcA.
    - change (Qlt 0 (1 # 16)). unfold Qlt. simpl. lia. }
  assert (H1T : QltT 0 1) by (apply Qlt_to_QltT; change (Qlt 0 1); unfold Qlt; simpl; lia).
  assert (HcA0 : Qle 0 cA). { apply Qlt_le_weak. exact HcA. }
  assert (HcB0 : Qle 0 cB). { apply Qlt_le_weak. exact HcB. }
  assert (HcAne : ~ cA == 0). { apply q_neq_of_lt. exact HcA. }
  assert (HcBne : ~ cB == 0). { apply q_neq_of_lt. exact HcB. }
  assert (H8K1ne : ~ Qmult 8 K1 == 0).
  { apply q_neq_of_lt. nra. }
  assert (HK1ne : ~ K1 == 0).
  { apply q_neq_of_lt. exact HK1. }
  (* ---- 系数预算事实（Q 层固定，供逐点吸收） ---- *)
  (* Hc1：QicB·kE == 1/8；Hc2：QicB·(kEp+kapE) == 1/8 *)
  assert (Hc1 : Qle (Qmult QicB kE) (1 # 8)).
  { apply qeq_imp_qle.
    unfold QicB, kE.
    field. exact HcBne. }
  assert (Hc1' : Qle (Qmult QicB (Qplus kEp kapE)) (1 # 8)).
  { apply qeq_imp_qle.
    unfold QicB, kEp, kapE.
    field. exact HcBne. }
  (* Hc2/Hc2'：ME·QicA·QicB·kS ≤ 1/8、ME·QicA·QicB·(kSp+kapS) ≤ 1/8 *)
  set (Mterm := Qmult ME (Qmult QicA QicB)).
  assert (Hc2 : Qle (Qmult Mterm kS) (1 # 8)).
  { apply (Qle_trans (Qmult Mterm kS)
                     (Qmult (Qmult ME (1 # 8)) (Qinv (Qplus ME 1)))
                     (1 # 8)).
    - apply qeq_imp_qle.
      unfold Mterm, QicA, QicB, kS, invM1.
      field. all: repeat split; assumption.
    - apply (Qle_trans (Qmult (Qmult ME (1 # 8)) (Qinv (Qplus ME 1)))
                       (Qinv 8)
                       (1 # 8)).
      + apply (b5n_xinv_le (Qmult ME (1 # 8)) (Qplus ME 1) 8).
        * exact HME1.
        * change (Qlt 0 8). unfold Qlt. simpl. lia.
        * nra.
      + apply qeq_imp_qle. unfold Qinv. reflexivity. }
  assert (Hc2' : Qle (Qmult Mterm (Qplus kSp kapS)) (1 # 8)).
  { apply (Qle_trans (Qmult Mterm (Qplus kSp kapS))
                     (Qmult (Qmult ME (1 # 8)) (Qinv (Qplus ME 1)))
                     (1 # 8)).
    - apply qeq_imp_qle.
      unfold Mterm, QicA, QicB, kSp, kapS, invM1.
      field. all: repeat split; assumption.
    - apply (Qle_trans (Qmult (Qmult ME (1 # 8)) (Qinv (Qplus ME 1)))
                       (Qinv 8)
                       (1 # 8)).
      + apply (b5n_xinv_le (Qmult ME (1 # 8)) (Qplus ME 1) 8).
        * exact HME1.
        * change (Qlt 0 8). unfold Qlt. simpl. lia.
        * nra.
      + apply qeq_imp_qle. unfold Qinv. reflexivity. }
  (* 下界不等式：(K1·τ) + μ + kapS2 ≤ cA − cB（== cA/2，LHS == cA/4） *)
  assert (Htau_eq : Qle (Qmult K1 tau) (Qmult cA (1 # 8))).
  { apply qeq_imp_qle.
    unfold tau.
    field. all: repeat split; assumption. }
  assert (Hlb_ineq : Qle (Qplus (Qmult K1 tau) (Qplus mu kapS2)) (Qminus cA cB)).
  { apply (Qle_trans (Qplus (Qmult K1 tau) (Qplus mu kapS2))
                     (Qplus (Qmult cA (1 # 8)) (Qmult cA (1 # 8)))
                     (Qminus cA cB)).
    - apply Qplus_le_compat.
      + apply (Qle_trans (Qmult K1 tau) (Qmult cA (1 # 8)) (Qmult cA (1 # 8))).
        * exact Htau_eq.
        * apply Qle_refl.
      + apply (Qle_trans (Qplus mu kapS2) (Qmult cA (1 # 8)) (Qmult cA (1 # 8))).
        * apply qeq_imp_qle. unfold mu, kapS2. ring.
        * apply Qle_refl.
    - unfold cB. nra. }
  (* ---- eps 见证与份额 ---- *)
  assert (H2T : QltT 0 (1 # 2)) by (apply Qlt_to_QltT; change (Qlt 0 (1 # 2)); unfold Qlt; simpl; lia).
  assert (H4T : QltT 0 (1 # 4)) by (apply Qlt_to_QltT; change (Qlt 0 (1 # 4)); unfold Qlt; simpl; lia).
  assert (H8T : QltT 0 (1 # 8)) by (apply Qlt_to_QltT; change (Qlt 0 (1 # 8)); unfold Qlt; simpl; lia).
  assert (H16T : QltT 0 (1 # 16)) by (apply Qlt_to_QltT; change (Qlt 0 (1 # 16)); unfold Qlt; simpl; lia).
  (* ---- eps 份额（Real）：epsE / epsS（E-diff 与 S-diff 主实例的斜率份额）
     ——本件构造子形：E 份额 = canonical mult 形（lb_E 同形）；
     S 份额 = canonical const 形（lb_Sdiff 同形——设计 §1 (b)）；
     见证全部内联 canonical 项（零 assert 变量进 app——conv 构造保证） ---- *)
  set (epsE := real_mult eps (real_const kE)).
  assert (Ha1 : Qlt 0 (Qmult a (b5dQ_kS q))).
  { apply (Qmult_lt_0_compat a (b5dQ_kS q)).
    - exact Ha.
    - exact (b5dQ_kS_pos q Hq0). }
  (* epsS 坐标 = a·kS（kS = 段B set-var zeta——与 b5dQ_kS q 计算相等；
     canonical 见证 Ha1 用 b5dQ_kS q 形——lb_Sdiff 直实例化所需） *)
  set (epsS := real_const (Qmult a kS)).
  (* 三叶自建（canonical app——构造子形证书：E 叶 HMsQ/HMcQ := b5dQ_H1pos、
     HC40C := b5dQ_HC40、eps 见证 := b5dM_real_const_pos 双叶；S 叶 Heps :=
     real_const_pos——与 lb_E/lb_Sdiff canonical app 项同一（全部证书位
     内联闭式/参数直传，零 assert 变量进 app）；δ 定义性 = projT1 (app)
     ——lb 证书构造时可及（绕墙核心：零 J 内部证书匹配） *)
  pose (δE := projT1 (b5dI_E_diff_closed_r_exp r (Qlt_le_weak 0 q Hq0) Hq1 x Hxr
           1 1 b5d3_exp_arch4_C b5dQ_H1pos b5dQ_H1pos b5dQ_HC40
           b5d3_exp_arch4_C_ge1 b5d3_exp_arch4_C_all
           HMs_all HMc_all epsE
           (b5dI_real_mult_positive_exp (real_const a) (real_const (1 # 32))
              (b5dM_real_const_pos a (Qlt_to_QltT 0 a Ha))
              (b5dM_real_const_pos (1 # 32) b5dQ_Hq32T)))).
  assert (HδE0 := fst (projT2 (b5dI_E_diff_closed_r_exp r (Qlt_le_weak 0 q Hq0) Hq1 x Hxr
           1 1 b5d3_exp_arch4_C b5dQ_H1pos b5dQ_H1pos b5dQ_HC40
           b5d3_exp_arch4_C_ge1 b5d3_exp_arch4_C_all
           HMs_all HMc_all epsE
           (b5dI_real_mult_positive_exp (real_const a) (real_const (1 # 32))
              (b5dM_real_const_pos a (Qlt_to_QltT 0 a Ha))
              (b5dM_real_const_pos (1 # 32) b5dQ_Hq32T))))).
  assert (HδE := snd (projT2 (b5dI_E_diff_closed_r_exp r (Qlt_le_weak 0 q Hq0) Hq1 x Hxr
           1 1 b5d3_exp_arch4_C b5dQ_H1pos b5dQ_H1pos b5dQ_HC40
           b5d3_exp_arch4_C_ge1 b5d3_exp_arch4_C_all
           HMs_all HMc_all epsE
           (b5dI_real_mult_positive_exp (real_const a) (real_const (1 # 32))
              (b5dM_real_const_pos a (Qlt_to_QltT 0 a Ha))
              (b5dM_real_const_pos (1 # 32) b5dQ_Hq32T))))).
  pose (δS1 := projT1 (b5dP_S_diff_closed_r_M_exp_tail r (Qlt_le_weak 0 q Hq0) Hq1 x Hxr
           2 b5dQ_p4_two_pos NM HMall epsS
           (real_const_pos (Qmult a kS) (Qlt_to_QltT 0 (Qmult a kS) Ha1)))).
  assert (HδS10 := fst (projT2 (b5dP_S_diff_closed_r_M_exp_tail r (Qlt_le_weak 0 q Hq0) Hq1 x Hxr
           2 b5dQ_p4_two_pos NM HMall epsS
           (real_const_pos (Qmult a kS) (Qlt_to_QltT 0 (Qmult a kS) Ha1))))).
  assert (HδS1 := snd (projT2 (b5dP_S_diff_closed_r_M_exp_tail r (Qlt_le_weak 0 q Hq0) Hq1 x Hxr
           2 b5dQ_p4_two_pos NM HMall epsS
           (real_const_pos (Qmult a kS) (Qlt_to_QltT 0 (Qmult a kS) Ha1))))).
  pose (δS2 := projT1 (b5dP_S_diff_closed_r_M_exp_tail r (Qlt_le_weak 0 q Hq0) Hq1 x Hxr
           2 b5dQ_p4_two_pos NM HMall (real_const 1)
           (real_const_pos 1 (Qlt_to_QltT 0 1 b5dQ_H1pos)))).
  assert (HδS20 := fst (projT2 (b5dP_S_diff_closed_r_M_exp_tail r (Qlt_le_weak 0 q Hq0) Hq1 x Hxr
           2 b5dQ_p4_two_pos NM HMall (real_const 1)
           (real_const_pos 1 (Qlt_to_QltT 0 1 b5dQ_H1pos))))).
  assert (HδS2 := snd (projT2 (b5dP_S_diff_closed_r_M_exp_tail r (Qlt_le_weak 0 q Hq0) Hq1 x Hxr
           2 b5dQ_p4_two_pos NM HMall (real_const 1)
           (real_const_pos 1 (Qlt_to_QltT 0 1 b5dQ_H1pos))))).
  (* δ := min(min(min(δE, δS1), δS2), real_const τ)（段B L645 同款——τ 叶
     坐标 = b5dQ_tau q 闭式） *)
  set (delta := real_min (real_min (real_min δE δS1) δS2) (real_const tau)).
  assert (Hdpos : real_lt real_zero delta).
  { unfold delta.
    apply real_min_pos.
    { apply real_min_pos.
      { apply real_min_pos. { exact HδE0. } { exact HδS10. } }
      { exact HδS20. } }
    { apply real_const_pos. exact HtauT. } }
  exists delta.
  split.
  { exact Hdpos. }
  { split.
    { intros h Hh Hxh eps' Heps'.
    (* eps 见证分解（item25 改动 S4：自 item11 L244 下移——spine-clean：
       e0/He0T/Ne0/He0lt 不进 δ 值；换源 b5dM_b5n_eps_proj_lt） *)
    destruct (b5dM_b5n_eps_proj_lt eps Heps) as [e0 [He0T [Ne0 He0lt]]].
    (* 提取 |h| < 分量 *)
    assert (Hh1 : real_lt (real_abs h) (real_min (real_min δE δS1) δS2)).
    { apply (real_min_lt_l h (real_min (real_min δE δS1) δS2) (real_const tau)).
      unfold delta in Hh. exact Hh. }
    assert (Hhτ : real_lt (real_abs h) (real_const tau)).
    { apply (real_min_lt_r h (real_min (real_min δE δS1) δS2) (real_const tau)).
      unfold delta in Hh. exact Hh. }
    assert (Hh2 : real_lt (real_abs h) (real_min δE δS1)).
    { apply (real_min_lt_l h (real_min δE δS1) δS2). exact Hh1. }
    assert (HhS2 : real_lt (real_abs h) δS2).
    { apply (real_min_lt_r h (real_min δE δS1) δS2). exact Hh1. }
    assert (HhE : real_lt (real_abs h) δE).
    { apply (real_min_lt_l h δE δS1). exact Hh2. }
    assert (HhS1 : real_lt (real_abs h) δS1).
    { apply (real_min_lt_r h δE δS1). exact Hh2. }
    destruct (b5dM_b5n_eps_proj_lt eps' Heps') as [e1 [He1T [Ne1 He1lt]]].
    set (eta := Qmult (1 # 8) e1).
    assert (HetaT : QltT 0 eta).
    { unfold eta. apply Qlt_to_QltT.
      apply (Qmult_lt_0_compat (1 # 8) e1).
      - change (Qlt 0 (1 # 8)). unfold Qlt. simpl. lia.
      - apply QltT_to_Qlt. exact He1T. }
    (* eps' 份额（Real）：E-diff epsE'/margin shE、S-diff epsS'/margin shS *)
    set (epsE' := real_mult eps' (real_const kEp)).
    assert (HepsE' : real_lt real_zero epsE').
    { unfold epsE'. apply real_mult_positive. { exact Heps'. } { apply real_const_pos. exact HkEpT. } }
    set (shE := real_mult eps' (real_const kapE)).
    assert (HshE : real_lt real_zero shE).
    { unfold shE. apply real_mult_positive. { exact Heps'. } { apply real_const_pos. exact HkapET. } }
    set (epsS' := real_mult eps' (real_const kSp)).
    assert (HepsS' : real_lt real_zero epsS').
    { unfold epsS'. apply real_mult_positive. { exact Heps'. } { apply real_const_pos. exact HkSpT. } }
    set (shS := real_mult eps' (real_const kapS)).
    assert (HshS : real_lt real_zero shS).
    { unfold shS. apply real_mult_positive. { exact Heps'. } { apply real_const_pos. exact HkapST. } }
    (* 下界实例的常份额（Real，不依赖 eps'） *)
    assert (Hcμ : real_lt real_zero (real_const mu)).
    { apply real_const_pos. exact HmuT. }
    assert (HcκS2 : real_lt real_zero (real_const kapS2)).
    { apply real_const_pos. exact HkapS2T. }
    (* 逐点转换（real_le → per-n，margin 松弛） *)
    set (BE := real_plus (real_mult epsE (real_abs h)) epsE').
    destruct (b5i_abs_le_pointwise (b5e_E_err x Hx h Hxh) BE
               (HδE h HhE Hxh epsE' HepsE') shE HshE) as [NE HNE].
    set (BS1 := real_plus (real_mult epsS (real_abs h)) epsS').
    destruct (b5i_abs_le_pointwise (b5m_rS x h) BS1
               (HδS1 h HhS1 epsS' HepsS') shS HshS) as [NS HNS].
    set (BS2 := real_plus (real_mult (real_const 1) (real_abs h)) (real_const mu)).
    destruct (b5i_abs_le_pointwise (b5m_rS x h) BS2
               (HδS2 h HhS2 (real_const mu) Hcμ) (real_const kapS2) HcκS2) as [NS2 HNS2].
    (* |h_n| ≤ tau（b5i_h_le_const）、|d_n| ≤ 1 尾、逐点恒等 N *)
    destruct (b5i_h_le_const h tau Hhτ HtauT) as [Nτ HNτ].
    destruct (b5dM_b5c_d_proj_le_one x) as [Nd Hd].
    destruct (b5m_J_dec_proj x h Hx Hxh) as [Ndec HNdec].
    (* 逐点预算（对 eps/eps' 见证） *)
    assert (Hen'g : forall n : nat, NatLe Ne1 n -> Qle 0 (projT1 eps' n)).
    { intros n Hn.
      apply (Qle_trans 0 e1 (projT1 eps' n)).
      { apply Qlt_le_weak. apply QltT_to_Qlt. exact He1T. }
      { apply Qlt_le_weak. exact (He1lt n Hn). } }
    set (Nmax := Nat.max NM (Nat.max (Nat.max Ne0 Ne1)
                 (Nat.max (Nat.max Ndec Nτ)
                  (Nat.max (Nat.max NE (Nat.max NS NS2)) (Nat.max NA Nd))))).
    (* 主装配：real_le → real_lt（左支），见证 eta *)
    left.
    exists eta.
    split.
    { exact HetaT. }
    { exists Nmax.
      intros n Hn.
      apply NatLe_drop in Hn.
      set (en := projT1 eps n).
      set (en' := projT1 eps' n).
      set (hn := Qabs (projT1 h n)).
      set (Dn := Qabs (projT1 (b5m_J_err x Hx h Hxh) n)).
      set (Sn := projT1 (b5a_S x) n).
      set (Shn := projT1 (b5a_S (real_plus x h)) n).
      set (dn := projT1 (b5a_atan_d x) n).
      set (rEn := projT1 (b5e_E_err x Hx h Hxh) n).
      set (rSn := projT1 (b5m_rS x h) n).
      set (Exn := projT1 (b5a_E x Hx) n).
      (* 尾指标 *)
      assert (HnNe0 : NatLe Ne0 n) by (apply NatLe_lift; lia).
      assert (HnNe1 : NatLe Ne1 n) by (apply NatLe_lift; lia).
      assert (HnNE : NatLe NE n) by (apply NatLe_lift; lia).
      assert (HnNS : NatLe NS n) by (apply NatLe_lift; lia).
      assert (HnNS2 : NatLe NS2 n) by (apply NatLe_lift; lia).
      assert (HnNτ : NatLe Nτ n) by (apply NatLe_lift; lia).
      assert (HnNd : (Nd <= n)%nat) by lia.
      assert (HnNdec : (Ndec <= n)%nat) by lia.
      assert (HnNA : (NA <= n)%nat) by lia.
      assert (HnNM : (NM <= n)%nat) by lia.
      (* 非负 *)
      assert (Hen0 : Qle 0 en).
      { unfold en. apply (Qle_trans 0 e0 (projT1 eps n)).
        - apply Qlt_le_weak. apply QltT_to_Qlt. exact He0T.
        - apply Qlt_le_weak. exact (He0lt n HnNe0). }
      assert (Hen'0 : Qle 0 en').
      { unfold en'. exact (Hen'g n HnNe1). }
      assert (Hhn0 : Qle 0 hn). { unfold hn. apply Qabs_nonneg. }
      (* |h_n| ≤ tau、|d_n| ≤ 1、Sn ≥ cA *)
      assert (Hhτn : Qle (Qabs (projT1 h n)) tau).
      { unfold tau in *. exact (HNτ n HnNτ). }
      assert (Hdn1 : Qle (Qabs dn) 1).
      { unfold dn. exact (Hd n HnNd). }
      assert (HSnA : Qle cA Sn).
      { unfold Sn. exact (HNA n HnNA). }
      (* |rE_n| ≤ kE·en·hn + (kEp+kapE)·en'（E-diff 逐点化） *)
      assert (HrE : Qle (Qabs rEn)
                        (Qplus (Qmult (Qmult en kE) (Qabs (projT1 h n)))
                               (Qplus (Qmult en' kEp) (Qmult en' kapE)))).
      { apply (Qle_trans (Qabs rEn)
                         (Qplus (projT1 BE n) (projT1 shE n))
                         (Qplus (Qmult (Qmult en kE) (Qabs (projT1 h n)))
                                (Qplus (Qmult en' kEp) (Qmult en' kapE)))).
        - unfold rEn. exact (HNE n HnNE).
        - apply qeq_imp_qle.
          unfold BE, shE, en, en'.
          setoid_rewrite (real_plus_proj (real_mult epsE (real_abs h)) epsE' n).
          setoid_rewrite (real_mult_proj epsE (real_abs h) n).
          unfold epsE, epsE'.
          setoid_rewrite (real_mult_proj eps (real_const kE) n).
          rewrite (real_const_proj kE n).
          setoid_rewrite (real_abs_proj h n).
          setoid_rewrite (real_mult_proj eps' (real_const kEp) n).
          rewrite (real_const_proj kEp n).
          setoid_rewrite (real_mult_proj eps' (real_const kapE) n).
          rewrite (real_const_proj kapE n).
          ring. }
      (* |rS_n| ≤ kS·en·hn + (kSp+kapS)·en'（S-diff 主实例逐点化） *)
      assert (HrS : Qle (Qabs rSn)
                        (Qplus (Qmult (Qmult en kS) (Qabs (projT1 h n)))
                               (Qplus (Qmult en' kSp) (Qmult en' kapS)))).
      { apply (Qle_trans (Qabs rSn)
                         (Qplus (projT1 BS1 n) (projT1 shS n))
                         (Qplus (Qmult (Qmult en kS) (Qabs (projT1 h n)))
                                (Qplus (Qmult en' kSp) (Qmult en' kapS)))).
        - unfold rSn. exact (HNS n HnNS).
        - apply qeq_imp_qle.
          unfold BS1, shS, en, en'.
          setoid_rewrite (real_plus_proj (real_mult epsS (real_abs h)) epsS' n).
          setoid_rewrite (real_mult_proj epsS (real_abs h) n).
          unfold epsS.
          rewrite (real_const_proj (Qmult a kS) n).
          unfold epsS'.
          setoid_rewrite (real_abs_proj h n).
          setoid_rewrite (real_mult_proj eps' (real_const kSp) n).
          rewrite (real_const_proj kSp n).
          setoid_rewrite (real_mult_proj eps' (real_const kapS) n).
          rewrite (real_const_proj kapS n).
          unfold eps.
          rewrite (real_const_proj a n).
          ring. }
      (* |rS_n| ≤ 1·hn + mu + kapS2（S-diff 常份额实例逐点化，下界用） *)
      assert (HrS2 : Qle (Qabs rSn)
                         (Qplus (Qabs (projT1 h n)) (Qplus mu kapS2))).
      { apply (Qle_trans (Qabs rSn)
                         (Qplus (projT1 BS2 n) (projT1 (real_const kapS2) n))
                         (Qplus (Qabs (projT1 h n)) (Qplus mu kapS2))).
        - unfold rSn. exact (HNS2 n HnNS2).
        - apply qeq_imp_qle.
          unfold BS2.
          setoid_rewrite (real_plus_proj (real_mult (real_const 1) (real_abs h))
                                         (real_const mu) n).
          setoid_rewrite (real_mult_proj (real_const 1) (real_abs h) n).
          rewrite (real_const_proj 1 n).
          setoid_rewrite (real_abs_proj h n).
          rewrite (real_const_proj mu n).
          rewrite (real_const_proj kapS2 n).
          ring. }
      (* |Ex_n| ≤ ME（sinA/cosA 逐点界 + |x_n| ≤ r；Exn == sAn − xn·cAn） *)
      assert (HEx : Qle (Qabs Exn) ME).
      { unfold Exn, b5a_E.
        rewrite (real_plus_proj (cauchy_real_sin (cauchy_real_arctan x Hx))
                                (real_opp (real_mult x (cauchy_real_cos (cauchy_real_arctan x Hx)))) n).
        rewrite (real_opp_proj (real_mult x (cauchy_real_cos (cauchy_real_arctan x Hx))) n).
        rewrite (real_mult_proj x (cauchy_real_cos (cauchy_real_arctan x Hx)) n).
        apply (Qle_trans
                 (Qabs (Qplus (projT1 (cauchy_real_sin (cauchy_real_arctan x Hx)) n)
                              (Qopp (Qmult (projT1 x n)
                                           (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n)))))
                 (Qplus (Qabs (projT1 (cauchy_real_sin (cauchy_real_arctan x Hx)) n))
                        (Qabs (Qmult (projT1 x n)
                                     (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n))))
                 ME).
        - apply (Qle_trans
                   (Qabs (Qplus (projT1 (cauchy_real_sin (cauchy_real_arctan x Hx)) n)
                                (Qopp (Qmult (projT1 x n)
                                             (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n)))))
                   (Qplus (Qabs (projT1 (cauchy_real_sin (cauchy_real_arctan x Hx)) n))
                          (Qabs (Qopp (Qmult (projT1 x n)
                                             (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n)))))
                   (Qplus (Qabs (projT1 (cauchy_real_sin (cauchy_real_arctan x Hx)) n))
                          (Qabs (Qmult (projT1 x n)
                                       (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n))))).
          + apply Qabs_triangle.
          + apply Qplus_le_compat.
            * apply Qle_refl.
            * apply qeq_imp_qle.
              apply (Qabs_opp (Qmult (projT1 x n)
                                     (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n))).
        - (* |sA| + |x·cA| ≤ Ms + r·Mc ≤ ME *)
          apply (Qle_trans
                   (Qplus (Qabs (projT1 (cauchy_real_sin (cauchy_real_arctan x Hx)) n))
                          (Qabs (Qmult (projT1 x n)
                                       (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n))))
                   (Qplus Ms (Qmult r Mc))
                   ME).
          + apply Qplus_le_compat.
            * apply (Qle_trans (Qabs (projT1 (cauchy_real_sin (cauchy_real_arctan x Hx)) n))
                               (Qabs (sin_partial n (arctan_partial n (projT1 x n))))
                               Ms).
              { apply qeq_imp_qle. apply Qabs_wd. apply Qeq_sym.
                setoid_rewrite (real_sin_proj (cauchy_real_arctan x Hx) n).
                setoid_rewrite (arctan_real_proj x Hx n).
                reflexivity. }
              { exact (HMs_all n). }
            * apply (Qle_trans (Qabs (Qmult (projT1 x n)
                                            (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n)))
                               (Qmult r (Qabs (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n)))
                               (Qmult r Mc)).
              { apply (Qle_trans (Qabs (Qmult (projT1 x n)
                                              (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n)))
                                 (Qmult (Qabs (projT1 x n))
                                        (Qabs (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n)))
                                 (Qmult r (Qabs (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n)))).
                - apply qeq_imp_qle.
                  apply (Qabs_Qmult (projT1 x n)
                                    (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n)).
                - apply (Qmult_le_compat_r (Qabs (projT1 x n)) r
                                           (Qabs (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n))).
                  + apply QleT'_to_Qle. exact (Hxr n).
                  + apply Qabs_nonneg. }
              { apply (sc_qmult_le_l (Qabs (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n))
                                     Mc r).
                - apply (Qle_trans (Qabs (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n))
                                   (Qabs (cos_partial n (arctan_partial n (projT1 x n))))
                                   Mc).
                  + apply qeq_imp_qle. apply Qabs_wd. apply Qeq_sym.
                    setoid_rewrite (real_cos_proj (cauchy_real_arctan x Hx) n).
                    setoid_rewrite (arctan_real_proj x Hx n).
                    reflexivity.
                  + exact (HMc_all n).
                - exact Hr0'. }
          + unfold ME. nra. }
      (* 商分母证书：|Qinv(Sn)| ≤ QicA *)
      assert (HQA : Qle (Qabs (Qinv Sn)) QicA).
      { unfold Sn, QicA. apply (b5m_inv_le Sn cA HcA HSnA). }
      (* Sxh ≥ cB：|ΔS| 界（r·M·hn + |rS|）→ K1·tau + mu + kapS2 ≤ cA − cB *)
      assert (Hdel0 : Qle (Qabs (Qminus Shn Sn))
                          (Qplus (Qmult (Qmult r M) (Qabs (projT1 h n)))
                                 (Qplus (Qabs (projT1 h n)) (Qplus mu kapS2)))).
      { (* Shn − Sn == (x·S·d·h)_n + rS_n *)
        apply (Qle_trans (Qabs (Qminus Shn Sn))
                         (Qplus (Qabs (Qmult (Qmult (projT1 x n) Sn) (Qmult dn (projT1 h n))))
                                (Qabs rSn))
                         (Qplus (Qmult (Qmult r M) (Qabs (projT1 h n)))
                                (Qplus (Qabs (projT1 h n)) (Qplus mu kapS2)))).
        - (* triangle：|Shn − Sn| == |P + rS| ≤ |P| + |rS| *)
          apply (Qle_trans (Qabs (Qminus Shn Sn))
                           (Qabs (Qplus (Qmult (Qmult (projT1 x n) Sn) (Qmult dn (projT1 h n))) rSn))
                           (Qplus (Qabs (Qmult (Qmult (projT1 x n) Sn) (Qmult dn (projT1 h n))))
                                  (Qabs rSn))).
          + apply qeq_imp_qle.
            apply (Qabs_wd (Qminus Shn Sn)
                           (Qplus (Qmult (Qmult (projT1 x n) Sn) (Qmult dn (projT1 h n))) rSn)).
            unfold Shn, Sn, dn, rSn.
            unfold b5m_rS.
            rewrite (real_plus_proj (b5a_S (real_plus x h))
                                    (real_opp (real_plus (b5a_S x)
                                               (real_mult (real_mult x (b5a_S x))
                                                          (real_mult (b5a_atan_d x) h)))) n).
            rewrite (real_opp_proj (real_plus (b5a_S x)
                                    (real_mult (real_mult x (b5a_S x))
                                               (real_mult (b5a_atan_d x) h))) n).
            rewrite (real_plus_proj (b5a_S x)
                                    (real_mult (real_mult x (b5a_S x))
                                               (real_mult (b5a_atan_d x) h)) n).
            rewrite (real_mult_proj (real_mult x (b5a_S x))
                                    (real_mult (b5a_atan_d x) h) n).
            rewrite (real_mult_proj x (b5a_S x) n).
            rewrite (real_mult_proj (b5a_atan_d x) h n).
            cbn [projT1 real_zero].
            ring.
          + apply Qabs_triangle.
        - (* |P| ≤ r·M·1·hn、|rS_n| ≤ hn + mu + kapS2（HrS2） *)
          apply Qplus_le_compat.
          + (* |(x·S·d·h)_n| ≤ r·M·1·hn *)
            apply (Qle_trans (Qabs (Qmult (Qmult (projT1 x n) Sn) (Qmult dn (projT1 h n))))
                             (Qmult (Qmult (Qabs (projT1 x n)) (Qabs Sn)) (Qmult (Qabs dn) (Qabs (projT1 h n))))
                             (Qmult (Qmult r M) (Qabs (projT1 h n)))).
            * apply qeq_imp_qle.
              apply (Qeq_trans (Qabs (Qmult (Qmult (projT1 x n) Sn) (Qmult dn (projT1 h n))))
                               (Qmult (Qabs (Qmult (projT1 x n) Sn)) (Qabs (Qmult dn (projT1 h n))))
                               (Qmult (Qmult (Qabs (projT1 x n)) (Qabs Sn)) (Qmult (Qabs dn) (Qabs (projT1 h n))))).
              { apply (Qabs_Qmult (Qmult (projT1 x n) Sn) (Qmult dn (projT1 h n))). }
              { apply Qmult_comp.
                - apply (Qabs_Qmult (projT1 x n) Sn).
                - apply (Qabs_Qmult dn (projT1 h n)). }
            * (* (|xn|·|Sn|)·(|dn|·|hn|) ≤ (r·M)·(1·hn) *)
              apply (Qle_trans (Qmult (Qmult (Qabs (projT1 x n)) (Qabs Sn)) (Qmult (Qabs dn) (Qabs (projT1 h n))))
                               (Qmult (Qmult r M) (Qmult 1 (Qabs (projT1 h n))))
                               (Qmult (Qmult r M) (Qabs (projT1 h n)))).
              { apply (Qle_trans (Qmult (Qmult (Qabs (projT1 x n)) (Qabs Sn)) (Qmult (Qabs dn) (Qabs (projT1 h n))))
                                 (Qmult (Qmult r M) (Qmult (Qabs dn) (Qabs (projT1 h n))))
                                 (Qmult (Qmult r M) (Qmult 1 (Qabs (projT1 h n))))).
                - apply (Qmult_le_compat_r (Qmult (Qabs (projT1 x n)) (Qabs Sn)) (Qmult r M)
                                           (Qmult (Qabs dn) (Qabs (projT1 h n)))).
                  + apply (Qle_trans (Qmult (Qabs (projT1 x n)) (Qabs Sn))
                                     (Qmult r (Qabs Sn))
                                     (Qmult r M)).
                    * apply (Qmult_le_compat_r (Qabs (projT1 x n)) r (Qabs Sn)).
                      { apply QleT'_to_Qle. exact (Hxr n). }
                      { apply Qabs_nonneg. }
                    * apply (sc_qmult_le_l (Qabs Sn) M r).
                      { unfold Sn. exact (HMall n HnNM). }
                      { exact Hr0'. }
                  + apply Qmult_le_0_compat.
                    * apply Qabs_nonneg.
                    * apply Qabs_nonneg.
                - apply (sc_qmult_le_l (Qmult (Qabs dn) (Qabs (projT1 h n)))
                                       (Qmult 1 (Qabs (projT1 h n)))
                                       (Qmult r M)).
                  + apply (Qmult_le_compat_r (Qabs dn) 1 (Qabs (projT1 h n))).
                    * exact Hdn1.
                    * apply Qabs_nonneg.
                  + apply Qmult_le_0_compat.
                    * exact Hr0'.
                    * exact HM0. }
              { apply qeq_imp_qle. ring. }
          + (* |rS_n| ≤ hn + mu + kapS2 *)
            apply (Qle_trans (Qabs rSn)
                             (Qplus (Qabs (projT1 h n)) (Qplus mu kapS2))
                             (Qplus (Qabs (projT1 h n)) (Qplus mu kapS2))).
            * exact HrS2.
            * apply Qle_refl. }
      (* |ΔS| ≤ K1·tau + mu + kapS2（hn ≤ tau） *)
      assert (Hdel : Qle (Qabs (Qminus Shn Sn))
                         (Qplus (Qmult K1 tau) (Qplus mu kapS2))).
      { apply (Qle_trans (Qabs (Qminus Shn Sn))
                         (Qplus (Qmult (Qmult r M) tau) (Qplus tau (Qplus mu kapS2)))
                         (Qplus (Qmult K1 tau) (Qplus mu kapS2))).
        - apply (Qle_trans (Qabs (Qminus Shn Sn))
                           (Qplus (Qmult (Qmult r M) (Qabs (projT1 h n)))
                                  (Qplus (Qabs (projT1 h n)) (Qplus mu kapS2)))
                           (Qplus (Qmult (Qmult r M) tau) (Qplus tau (Qplus mu kapS2)))).
          + exact Hdel0.
          + apply Qplus_le_compat.
            * apply (sc_qmult_le_l (Qabs (projT1 h n)) tau (Qmult r M)).
              { exact Hhτn. }
              { apply Qmult_le_0_compat. { exact Hr0'. } { exact HM0. } }
            * apply Qplus_le_compat.
              { exact Hhτn. }
              { apply Qle_refl. }
        - apply qeq_imp_qle. unfold K1. ring. }
      (* Shn ≥ cB（Sn ≥ cA、|ΔS| ≤ B0、B0 ≤ cA − cB） *)
      assert (HShnB : Qle cB Shn).
      { (* Sn ≤ Shn + |Δ| 且 |Δ| ≤ B0（Hdel）⟹ Sn ≤ Shn + B0 *)
        assert (HS2 : Qle Sn (Qplus Shn (Qplus (Qmult K1 tau) (Qplus mu kapS2)))).
        { apply (Qle_trans Sn (Qplus Shn (Qabs (Qminus Shn Sn)))
                              (Qplus Shn (Qplus (Qmult K1 tau) (Qplus mu kapS2)))).
          - apply (Qle_trans Sn (Qplus Shn (Qminus Sn Shn))
                                (Qplus Shn (Qabs (Qminus Shn Sn)))).
            + apply qeq_imp_qle. ring.
            + apply Qplus_le_compat.
              * apply Qle_refl.
              * apply (Qle_trans (Qminus Sn Shn) (Qabs (Qminus Sn Shn))
                                 (Qabs (Qminus Shn Sn))).
                { apply Qle_Qabs. }
                { apply qeq_imp_qle.
                  apply (Qeq_trans (Qabs (Qminus Sn Shn))
                                   (Qabs (Qopp (Qminus Shn Sn)))
                                   (Qabs (Qminus Shn Sn))).
                  - apply Qabs_wd. ring.
                  - apply (Qabs_opp (Qminus Shn Sn)). }
          - apply Qplus_le_compat.
            + apply Qle_refl.
            + exact Hdel. }
        (* cB ≤ cA − B0（Hlb_ineq）、cA ≤ Sn（HSnA）、Sn ≤ Shn + B0 ⟹ cB ≤ Shn *)
        nra. }
      (* 商分母证书：|Qinv(Shn)| ≤ QicB *)
      assert (HQB : Qle (Qabs (Qinv Shn)) QicB).
      { unfold Shn, QicB. apply (b5m_inv_le Shn cB HcB HShnB). }
      (* b5m_J_abs_tri 主步 *)
      set (RE := Qplus (Qmult (Qmult en kE) (Qabs (projT1 h n)))
                       (Qplus (Qmult en' kEp) (Qmult en' kapE))).
      set (RS := Qplus (Qmult (Qmult en kS) (Qabs (projT1 h n)))
                       (Qplus (Qmult en' kSp) (Qmult en' kapS))).
      assert (Hmain0 : Qle Dn (Qplus (Qmult QicB RE) (Qmult Mterm RS))).
      { unfold Dn.
        apply (b5m_J_abs_tri x h Hx Hxh n QicA QicB ME RE RS).
        - exact HQA.
        - exact HQB.
        - unfold Exn. exact HEx.
        - unfold rEn. exact HrE.
        - unfold rSn. exact HrS.
        - unfold QicA. apply Qlt_le_weak. apply Qinv_lt_0_compat. exact HcA.
        - unfold QicB. apply Qlt_le_weak. apply Qinv_lt_0_compat. exact HcB.
        - exact (HNdec n HnNdec). }
      (* 系数吸收：QicB·RE ≤ (1/8)·en·hn + (1/8)·en'；Mterm·RS ≤ 同形 *)
      assert (HT1 : Qle (Qmult QicB (Qmult (Qmult en kE) (Qabs (projT1 h n))))
                        (Qmult (1 # 8) (Qmult en hn))).
      { apply (Qle_trans (Qmult QicB (Qmult (Qmult en kE) (Qabs (projT1 h n))))
                         (Qmult (Qmult QicB kE) (Qmult en hn))
                         (Qmult (1 # 8) (Qmult en hn))).
        - apply qeq_imp_qle. unfold hn. ring.
        - apply (Qmult_le_compat_r (Qmult QicB kE) (1 # 8) (Qmult en hn)).
          + exact Hc1.
          + apply Qmult_le_0_compat.
            * exact Hen0.
            * exact Hhn0. }
      assert (HT2 : Qle (Qmult QicB (Qplus (Qmult en' kEp) (Qmult en' kapE)))
                        (Qmult (1 # 8) en')).
      { apply (Qle_trans (Qmult QicB (Qplus (Qmult en' kEp) (Qmult en' kapE)))
                         (Qmult (Qmult QicB (Qplus kEp kapE)) en')
                         (Qmult (1 # 8) en')).
        - apply qeq_imp_qle. ring.
        - apply (Qmult_le_compat_r (Qmult QicB (Qplus kEp kapE)) (1 # 8) en').
          + exact Hc1'.
          + exact Hen'0. }
      assert (HT3 : Qle (Qmult Mterm (Qmult (Qmult en kS) (Qabs (projT1 h n))))
                        (Qmult (1 # 8) (Qmult en hn))).
      { apply (Qle_trans (Qmult Mterm (Qmult (Qmult en kS) (Qabs (projT1 h n))))
                         (Qmult (Qmult Mterm kS) (Qmult en hn))
                         (Qmult (1 # 8) (Qmult en hn))).
        - apply qeq_imp_qle. unfold hn. ring.
        - apply (Qmult_le_compat_r (Qmult Mterm kS) (1 # 8) (Qmult en hn)).
          + exact Hc2.
          + apply Qmult_le_0_compat.
            * exact Hen0.
            * exact Hhn0. }
      assert (HT4 : Qle (Qmult Mterm (Qplus (Qmult en' kSp) (Qmult en' kapS)))
                        (Qmult (1 # 8) en')).
      { apply (Qle_trans (Qmult Mterm (Qplus (Qmult en' kSp) (Qmult en' kapS)))
                         (Qmult (Qmult Mterm (Qplus kSp kapS)) en')
                         (Qmult (1 # 8) en')).
        - apply qeq_imp_qle. ring.
        - apply (Qmult_le_compat_r (Qmult Mterm (Qplus kSp kapS)) (1 # 8) en').
          + exact Hc2'.
          + exact Hen'0. }
      (* 组装逐点主界：|Dn| ≤ en·hn + (3/4)·en' *)
      assert (Hmain : Qle Dn (Qplus (Qmult en hn) (Qmult (3 # 4) en'))).
      { apply (Qle_trans Dn
                         (Qplus (Qmult QicB RE) (Qmult Mterm RS))
                         (Qplus (Qmult en hn) (Qmult (3 # 4) en'))).
        - exact Hmain0.
        - (* 展开并吸收：QicB·RE + Mterm·RS ≤ (1/8)(en hn)+(1/8)en' 各两份 *)
          apply (Qle_trans (Qplus (Qmult QicB RE) (Qmult Mterm RS))
                           (Qplus (Qplus (Qmult QicB (Qmult (Qmult en kE) (Qabs (projT1 h n))))
                                         (Qmult QicB (Qplus (Qmult en' kEp) (Qmult en' kapE))))
                                  (Qplus (Qmult Mterm (Qmult (Qmult en kS) (Qabs (projT1 h n))))
                                         (Qmult Mterm (Qplus (Qmult en' kSp) (Qmult en' kapS)))))
                           (Qplus (Qmult en hn) (Qmult (3 # 4) en'))).
          + apply qeq_imp_qle. unfold RE, RS, hn. ring.
          + apply (Qle_trans
                     (Qplus (Qplus (Qmult QicB (Qmult (Qmult en kE) (Qabs (projT1 h n))))
                                   (Qmult QicB (Qplus (Qmult en' kEp) (Qmult en' kapE))))
                            (Qplus (Qmult Mterm (Qmult (Qmult en kS) (Qabs (projT1 h n))))
                                   (Qmult Mterm (Qplus (Qmult en' kSp) (Qmult en' kapS)))))
                     (Qplus (Qplus (Qmult (1 # 8) (Qmult en hn)) (Qmult (1 # 8) en'))
                            (Qplus (Qmult (1 # 8) (Qmult en hn)) (Qmult (1 # 8) en')))
                     (Qplus (Qmult en hn) (Qmult (3 # 4) en'))).
            * apply Qplus_le_compat.
              { apply Qplus_le_compat. { exact HT1. } { exact HT2. } }
              { apply Qplus_le_compat. { exact HT3. } { exact HT4. } }
            * nra. }
      (* margin：eta < (1/4)·en'；Hfin：eta < (en·hn + en') − Dn *)
      assert (Hq4e : Qlt eta (Qmult (1 # 4) en')).
      { unfold eta, en'. apply (b5n_quarter_gt e1 (projT1 eps' n)).
        - apply QltT_to_Qlt. exact He1T.
        - exact (He1lt n HnNe1). }
      assert (Hfin : Qlt eta (Qminus (Qplus (Qmult en hn) en') Dn)).
      { apply (b5n_close Dn hn en en' eta).
        - unfold Dn. exact Hmain.
        - unfold en'. exact Hq4e. }
      apply Qlt_to_QltT.
      apply (Qlt_le_trans eta
             (Qminus (Qplus (Qmult en hn) en') Dn)
             (Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                     (projT1 (real_abs (b5m_J_err x Hx h Hxh)) n))).
      - exact Hfin.
      - apply qeq_imp_qle. apply Qeq_sym.
        setoid_rewrite (real_plus_proj (real_mult eps (real_abs h)) eps' n).
        setoid_rewrite (real_mult_proj eps (real_abs h) n).
        setoid_rewrite (real_abs_proj h n).
        setoid_rewrite (real_abs_proj (b5m_J_err x Hx h Hxh) n).
        unfold en, en', hn, Dn.
        ring. } }
    { (* lb 证书：real_lt (real_const δ0) delta——逐叶 real_lt 下界
         （b5dQ_p4g_qlt_* 之 Q 界 + b5dQ_p4g_leaf_* 之叶证书）经
         real_lt_trans 提升，再以 b5dQ_min_lb 三层组合（conv 分步付清） *)
      assert (HqE : real_lt (real_const (b5dQ_delta0 q epsQ))
                            (real_const (Qmult (b5dQ_vE q (epsQ / (2 * q))) (1 # 2)))).
      { apply real_const_lt. exact (b5dQ_p4g_qlt_E q epsQ Hq0 Hq1 HepsQ). }
      assert (HlbE : real_lt (real_const (Qmult (b5dQ_vE q (epsQ / (2 * q))) (1 # 2))) δE).
      { unfold δE.
        exact (b5dQ_p4g_leaf_E q Hq0 Hq1 x Hxr HMs_all HMc_all
                 (epsQ / (2 * q)) Ha). }
      assert (HdE : real_lt (real_const (b5dQ_delta0 q epsQ)) δE).
      { apply (real_lt_trans (real_const (b5dQ_delta0 q epsQ))
                             (real_const (Qmult (b5dQ_vE q (epsQ / (2 * q))) (1 # 2)))
                             δE HqE HlbE). }
      assert (HqS1 : real_lt (real_const (b5dQ_delta0 q epsQ))
                             (real_const (b5dQ_lbSdiff_val q
                                (Qmult (epsQ / (2 * q)) (b5dQ_kS q))))).
      { apply real_const_lt. exact (b5dQ_p4g_qlt_S1 q epsQ Hq0 Hq1 HepsQ). }
      assert (HlbS1 : real_lt (real_const (b5dQ_lbSdiff_val q
                                (Qmult (epsQ / (2 * q)) (b5dQ_kS q)))) δS1).
      { unfold δS1.
        exact (b5dQ_p4g_leaf_S q (Qlt_le_weak 0 q Hq0) Hq1 x Hxr
                 (Qmult (epsQ / (2 * q)) (b5dQ_kS q)) Ha1 NM HMall). }
      assert (HdS1 : real_lt (real_const (b5dQ_delta0 q epsQ)) δS1).
      { apply (real_lt_trans (real_const (b5dQ_delta0 q epsQ))
                             (real_const (b5dQ_lbSdiff_val q
                                (Qmult (epsQ / (2 * q)) (b5dQ_kS q))))
                             δS1 HqS1 HlbS1). }
      assert (HqS2 : real_lt (real_const (b5dQ_delta0 q epsQ))
                             (real_const (b5dQ_lbSdiff_val q 1))).
      { apply real_const_lt. exact (b5dQ_p4g_qlt_S2 q epsQ Hq0 Hq1 HepsQ). }
      assert (HlbS2 : real_lt (real_const (b5dQ_lbSdiff_val q 1)) δS2).
      { unfold δS2.
        exact (b5dQ_p4g_leaf_S q (Qlt_le_weak 0 q Hq0) Hq1 x Hxr
                 1 b5dQ_H1pos NM HMall). }
      assert (HdS2 : real_lt (real_const (b5dQ_delta0 q epsQ)) δS2).
      { apply (real_lt_trans (real_const (b5dQ_delta0 q epsQ))
                             (real_const (b5dQ_lbSdiff_val q 1))
                             δS2 HqS2 HlbS2). }
      apply (b5dQ_min_lb (real_const (b5dQ_delta0 q epsQ))
                         (real_min (real_min δE δS1) δS2)
                         (real_const tau)).
      - apply (b5dQ_min_lb (real_const (b5dQ_delta0 q epsQ))
                           (real_min δE δS1) δS2).
        + apply (b5dQ_min_lb (real_const (b5dQ_delta0 q epsQ)) δE δS1).
          * exact HdE.
          * exact HdS1.
        + exact HdS2.
      - apply real_const_lt. exact (b5dQ_p4g_qlt_tau q epsQ Hq0 Hq1 HepsQ). }
  }
Defined.

(* ============================================================ *)
(* end sc2_b5a_item27_p4g.v（Part 0–2 + Part 3 主件全落——终验后定稿） *)

(* ===== 段 P4b（Hmod/主件换真：去桩去复制件 + 改名 canonical，3 Lemma/Def） ===== *)

(* ============================================================ *)
(* §C M4：Hstep 逐 k 步证书 + Hmod（q_arch_inv M := K+2 + 逐 k） *)
(* ============================================================ *)

(* b5dQ_Hstep：单步装配（证书现场 → P4g 变体件实例 + δ/lb    *)
(*   证书 → |η|<δ 链 → step_inst/P4a 桥 + rhs_bk → Hstep            *)
(*   forall-证书形——语句内层 = item22 b5dL_E_rational_zero_premise *)
(*   （L888-893）；Hetaδ（Qlt (qdiv q M) δ0）= Hmod 外层            *)
(*   q_arch_inv 选 M 的输出，本件以参数给出（无环）。）            *)
Lemma b5dQ_Hstep : forall (q : Q) (Hq0 : Qlt 0 q) (Hq1 : Qlt q 1)
  (epsQ : Q) (HepsQ : Qlt 0 epsQ)
  (M : nat) (HMpos : (0 < M)%nat) (k : nat) (HkM : (k < M)%nat)
  (Hetaδ : Qlt (b5dL_qdiv q M) (b5dQ_delta0 q epsQ))
  (Hxr : forall n : nat, QleT' (Qabs (projT1 (real_const (b5dL_tkq q M k)) n)) q)
  (NA : nat)
  (HNA : forall n : nat, (NA <= n)%nat ->
         Qle (1 # 2) (projT1 (b5a_S (real_const (b5dL_tkq q M k))) n))
  (NM : nat)
  (HMall : forall n : nat, (NM <= n)%nat ->
           Qle (Qabs (projT1 (b5a_S (real_const (b5dL_tkq q M k))) n)) 2)
  (Hs : forall n : nat,
         Qle (Qabs (sin_partial n (arctan_partial n
                (projT1 (real_const (b5dL_tkq q M k)) n)))) 1)
  (Hc : forall n : nat,
         Qle (Qabs (cos_partial n (arctan_partial n
                (projT1 (real_const (b5dL_tkq q M k)) n)))) 1)
  (Hk : cw_unit (real_const (b5dL_tkq q M k)))
  (Hk1 : cw_unit (real_const (b5dL_tkq q M (Datatypes.S k)))),
  real_le (real_abs (real_plus (b5c_J (real_const (b5dL_tkq q M (Datatypes.S k))) Hk1)
                               (real_opp (b5c_J (real_const (b5dL_tkq q M k)) Hk))))
          (real_const (b5dL_bk q M epsQ k)).
Proof.
  intros q Hq0 Hq1 epsQ HepsQ M HMpos k HkM Hetaδ Hxr NA HNA NM HMall Hs Hc Hk Hk1.
  (* 变体件实例（b5dQ_p4g_J_tail_lb_var @ 实例——参数束 = 桩语句
     参数束逐字；destruct 式访问三层证书：δ / 0<δ ∧（J-tail 模量
     性质 ∧ lb 证书）——零 conv、零公理面） *)
  set (vapp := b5dQ_p4g_J_tail_lb_var q Hq0 Hq1 epsQ HepsQ M HMpos k HkM
                 Hxr NA HNA NM HMall Hs Hc).
  destruct vapp as [δ [Hdpos [Hmod Hlb]]].
  (* |η| < δ0 常值实比较链 *)
  assert (Hηc : real_lt (real_const (b5dL_qdiv q M))
                        (real_const (b5dQ_delta0 q epsQ))).
  { apply real_const_lt. exact Hetaδ. }
  assert (Hηd : real_lt (real_const (b5dL_qdiv q M)) δ).
  { apply (real_lt_trans (real_const (b5dL_qdiv q M))
                         (real_const (b5dQ_delta0 q epsQ))
                         δ Hηc Hlb). }
  (* η ≥ 0 ⟹ |η| == η（real_const 侧） *)
  assert (Heta0 : Qle 0 (b5dL_qdiv q M)).
  { unfold b5dL_qdiv. unfold Qdiv.
    apply Qmult_le_0_compat.
    - apply Qlt_le_weak. exact Hq0.
    - apply Qinv_le_0_compat. apply Qlt_le_weak.
      destruct M as [| m]; [exfalso; lia | exact (b5dL_lift_pos2 m)]. }
  assert (Heta : real_eq (real_abs (real_const (b5dL_qdiv q M)))
                         (real_const (b5dL_qdiv q M))).
  { apply (real_eq_trans _ (real_const (Qabs (b5dL_qdiv q M))) _).
    - exact (b5dL_abs_const (b5dL_qdiv q M)).
    - apply b5dH_real_const_qeq.
      apply (Qabs_pos (b5dL_qdiv q M)). exact Heta0. }
  (* 模量前提：real_lt (real_abs (real_const η)) δ(t_k) *)
  assert (Hηabs : real_lt (real_abs (real_const (b5dL_qdiv q M))) δ).
  { apply (RealSetoid.real_lt_compat (real_const (b5dL_qdiv q M))
                          (real_abs (real_const (b5dL_qdiv q M)))
                          δ δ).
    - apply real_eq_sym. exact Heta.
    - apply real_eq_refl.
    - exact Hηd. }
  (* 证书现场：Hxh := xph_unit 实例；eps' := real_const (epsQ1 M epsQ) *)
  assert (Hxh : cw_unit (real_plus (real_const (b5dL_tkq q M k))
                                   (real_const (b5dL_qdiv q M)))).
  { exact (b5dQ_xph_unit q M k Hq0 Hq1 HMpos HkM). }
  assert (Heps1pos : real_lt real_zero (real_const (b5dL_epsQ1 M epsQ))).
  { apply real_const_pos. apply Qlt_to_QltT.
    exact (b5dL_epsQ1_pos epsQ M HepsQ HMpos). }
  (* 模量结论 @ h := real_const η（Hmod 直取——P4g 变体件第二层   *)
  (*   第二分量 = J-tail 模量性质；零 conv、零 destruct 投影链）  *)
  assert (Hcore : real_le
    (real_abs (real_plus (b5c_J (real_plus (real_const (b5dL_tkq q M k))
                                           (real_const (b5dL_qdiv q M))) Hxh)
                         (real_opp (b5c_J (real_const (b5dL_tkq q M k))
                                          (b3rr_dom_r1 (real_const (b5dL_tkq q M k))
                                                       q Hxr Hq1)))))
    (real_plus (real_mult (real_const (epsQ / (2 * q)))
                          (real_abs (real_const (b5dL_qdiv q M))))
               (real_const (b5dL_epsQ1 M epsQ)))).
  { exact (Hmod (real_const (b5dL_qdiv q M)) Hηabs Hxh
           (real_const (b5dL_epsQ1 M epsQ)) Heps1pos). }
  (* step_inst 桥（模量左点固定证书形 → Hmod 形任意证书 Hk/Hk1） *)
  assert (HstepR : real_le
    (real_abs (real_plus (b5c_J (real_const (b5dL_tkq q M (Datatypes.S k))) Hk1)
                         (real_opp (b5c_J (real_const (b5dL_tkq q M k)) Hk))))
    (real_plus (real_mult (real_const (epsQ / (2 * q)))
                          (real_abs (real_const (b5dL_qdiv q M))))
               (real_const (b5dL_epsQ1 M epsQ)))).
  { exact (b5dQ_step_inst q M k HMpos Hq1 Hxr Hk1 Hk Hxh
             (real_plus (real_mult (real_const (epsQ / (2 * q)))
                                   (real_abs (real_const (b5dL_qdiv q M))))
                        (real_const (b5dL_epsQ1 M epsQ)))
             Hcore). }
  (* RHS == real_const (bk)（rhs_bk 桥）+ real_le_id_r *)
  exact (RealSetoid.real_le_id_r
    (real_abs (real_plus (b5c_J (real_const (b5dL_tkq q M (Datatypes.S k))) Hk1)
                         (real_opp (b5c_J (real_const (b5dL_tkq q M k)) Hk))))
    (real_plus (real_mult (real_const (epsQ / (2 * q)))
                          (real_abs (real_const (b5dL_qdiv q M))))
               (real_const (b5dL_epsQ1 M epsQ)))
    (real_const (b5dL_bk q M epsQ k))
    (b5dQ_rhs_bk q M k epsQ Hq0 HMpos)
    HstepR).
Qed.

(* b5dQ_Hmod：∀q 0<q<1 → ∀epsQ>0 → ∃M，0<M ∧ ∀k<M 步界      *)
(*   （语句 = item22 b5dL_E_rational_zero_premise 内层逐字——     *)
(*   主件 exact 的唯一接口）                                  *)
(*   证法：δ0 正性 → q_arch_inv（根 L4733）@ δ0/q 选 K、M := K+2  *)
(*   → G8 qdiv_lt_arch 收 Qlt (qdiv q M) δ0 → 逐 k：destruct k    *)
(*   （k=0 用 P3 C1/C3 证书支；k=S k' 用 C2/C4 支）+              *)
(*   sincos_all_k/tkq_Hxr 证书现场 → b5dQ_Hstep。        *)
(* ============================================================ *)
Lemma b5dQ_Hmod : forall (q : Q) (Hq0 : Qlt 0 q) (Hq1 : Qlt q 1),
  forall (epsQ : Q), Qlt 0 epsQ ->
  sigT (fun M : nat => And (NatLe 1 M)
    (forall (k : nat), (k < M)%nat ->
       forall (Hk : cw_unit (real_const (b5dL_tkq q M k)))
              (Hk1 : cw_unit (real_const (b5dL_tkq q M (Datatypes.S k)))),
       real_le (real_abs (real_plus (b5c_J (real_const (b5dL_tkq q M (Datatypes.S k))) Hk1)
                                    (real_opp (b5c_J (real_const (b5dL_tkq q M k)) Hk))))
               (real_const (b5dL_bk q M epsQ k)))).
Proof.
  intros q Hq0 Hq1 epsQ HepsQ.
  (* δ0 > 0 与 δ0/q > 0（q_arch_inv 前提） *)
  assert (Hd0pos : Qlt 0 (b5dQ_delta0 q epsQ)).
  { exact (b5dQ_delta0_pos q epsQ Hq0 Hq1 HepsQ). }
  assert (Hd0q : Qlt 0 (b5dQ_delta0 q epsQ / q)).
  { unfold Qdiv.
    apply (Qmult_lt_0_compat (b5dQ_delta0 q epsQ) (Qinv q)).
    - exact Hd0pos.
    - apply Qinv_lt_0_compat. exact Hq0. }
  (* q_arch_inv 选 K；M := K+2（δD2f §2.7：一阶选取闭环） *)
  destruct (q_arch_inv (b5dQ_delta0 q epsQ / q) Hd0q) as [K HK].
  set (M := (K + 2)%nat).
  assert (HMpos : (0 < M)%nat).
  { unfold M. lia. }
  (* G8：Qlt (qdiv q M) δ0（|η| 侧 Q 层） *)
  assert (Hqdiv : Qlt (b5dL_qdiv q M) (b5dQ_delta0 q epsQ)).
  { apply (b5dQ_qdiv_lt_arch q (b5dQ_delta0 q epsQ) M Hq0 Hd0pos).
    exact HK. }
  exists M.
  split.
  - exact (NatLe_lift 1 M HMpos).
  - intros k HkM.
    destruct k as [| k'].
    + (* k = 0 支：C1/C3 证书（S(real_const (tkq q M 0)) 尾界） *)
      destruct (b5dQ_S_lb_tail_k0 q M) as [NA HNA].
      destruct (b5dQ_S_ub_tail_k0 q M) as [NM HMall].
      assert (HkleM : (0 <= M)%nat) by lia.
      destruct (b5dQ_sincos_all_k q Hq0 Hq1 M 0 HMpos HkleM) as [Hs Hc].
      intros Hk Hk1.
      exact (b5dQ_Hstep q Hq0 Hq1 epsQ HepsQ M HMpos 0 HkM Hqdiv
               (b5dQ_tkq_Hxr q M 0 (b5dH_q_pos_le q Hq0) HMpos HkleM)
               NA HNA NM HMall (fun n => QleT'_to_Qle _ _ (Hs n))
                    (fun n => QleT'_to_Qle _ _ (Hc n)) Hk Hk1).
    + (* k = S k' 支：C2/C4 证书（b5a_S_ge_one/item15 @ tkq (S k')） *)
      assert (Hk0s : (0 < Datatypes.S k')%nat) by lia.
      assert (HkleM : (Datatypes.S k' <= M)%nat) by lia.
      destruct (b5dQ_S_lb_tail_kS q M (Datatypes.S k') Hq0 HMpos Hk0s)
        as [NA HNA].
      destruct (b5dQ_S_ub_tail_kS q M (Datatypes.S k') Hq0 Hq1 HMpos Hk0s HkleM)
        as [NM HMall].
      destruct (b5dQ_sincos_all_k q Hq0 Hq1 M (Datatypes.S k') HMpos HkleM)
        as [Hs Hc].
      intros Hk Hk1.
      exact (b5dQ_Hstep q Hq0 Hq1 epsQ HepsQ M HMpos (Datatypes.S k')
               HkM Hqdiv
               (b5dQ_tkq_Hxr q M (Datatypes.S k') (b5dH_q_pos_le q Hq0)
                  HMpos HkleM)
               NA HNA NM HMall (fun n => QleT'_to_Qle _ _ (Hs n))
                    (fun n => QleT'_to_Qle _ _ (Hc n)) Hk Hk1).
Qed.

(* ============================================================ *)
(* §D M5 主件：b5dQ_E_rational_zero（语句 = 契约逐字）          *)
(*   证法 = exact (b5dL_E_rational_zero_premise …) 级直接引用        *)
(*   （item22 L885 已闭：Hmod 传入即得）                         *)
(* ============================================================ *)
Lemma b5dQ_E_rational_zero : forall (q : Q), Qlt 0 q -> Qlt q 1 ->
  forall (Hq : cw_unit (real_const q)),
  real_eq (real_E (real_const q) Hq) real_zero.
Proof.
  intros q Hq0 Hq1 Hq.
  exact (b5dL_E_rational_zero_premise q Hq0 Hq1
           (b5dQ_Hmod q Hq0 Hq1) Hq).
Qed.

(* ============================================================ *)
(* end sc2_b5a_item27_p4b_hmode.v（P4b · Hmod + 主件） *)
(* ============================================================ *)

(* ============================================================ *)
(* 块 item29（前缀 b5dS_——主件 b5dS_E_zero_on_unit）——来源：演变/.ablation/sc2_parallel/sc2_b5a_ode/sc2_b5a_item29.v。 *)
(* ============================================================ *)

(* ============================================================ *)
(* 段 A：pair 形 gap（b5dS_E_pair_gap）                           *)
(* 同构源：根 b5b_E_gap L73729–73853（体 L73738–73853）。         *)
(* 通用化改动（审查 §6.1 M1 行数估：ring/abs 小件 2–3 通用化）：  *)
(*   ① ring 恒等：b5b_ring_Ediff（(1−g,1) 特例）→ b5dS_ring_Ediff *)
(*     （∀a b pair 形——a := 1−g、b := 1 时逐字退化）；            *)
(*   ② abs 乘法界：b5b_abs_gmult（0 ≤ g 形）→ b5dS_abs_le1_mult   *)
(*     （|x| ≤ 1 ⟹ |x·y| ≤ |y|——pair 化后 b 系数无符号前提）；    *)
(*   ③ abs 换向：b5b_abs_oneminusg 角色 → b5dS_abs_sub_mult       *)
(*     （|(b−a)·x| == |a−b|·|x|——Qabs_Qmult + q_abs_minus_sym）。 *)
(* 域证书 b5b_unitQ 不再需要（|a|≤1、|b|≤1 前提直供）。           *)
(* ============================================================ *)

(* ---- 段 A 小件 ①：pair 形 ring 恒等（(a,b) 通用；             *)
(*        a := 1−g、b := 1 退化 = b5b_ring_Ediff 逐字） ---- *)
Lemma b5dS_ring_Ediff : forall (sA sB cA cB a b : Q),
  (sA - a * cA) - (sB - b * cB) ==
  (sA - sB) + (b * (cB - cA) + (b - a) * cA).
Proof.
  intros. ring.
Qed.

(* ---- 段 A 小件 ②：|x| ≤ 1 ⟹ |x·y| ≤ |y|（abs_gmult 的           *)
(*        pair 化通用形——b 系数无 0 ≤ b 前提） ---- *)
Lemma b5dS_abs_le1_mult : forall (x y : Q),
  QleT' (Qabs x) 1 -> Qle (Qabs (x * y)) (Qabs y).
Proof.
  intros x y Hx.
  apply (Qle_trans _ (Qmult (Qabs x) (Qabs y)) _).
  - apply qeq_le. apply (Qabs_Qmult x y).
  - apply (Qle_trans _ (Qmult 1 (Qabs y)) _).
    + apply (Qmult_le_compat_r (Qabs x) 1 (Qabs y)).
      * apply QleT'_to_Qle. exact Hx.
      * apply Qabs_nonneg.
    + apply qeq_le. ring.
Qed.

(* ---- 段 A 小件 ③：|(b−a)·x| == |a−b|·|x|（Qabs_Qmult +         *)
(*        q_abs_minus_sym；根 abs_oneminusg/abs_gmult 角色替代） ---- *)
Lemma b5dS_abs_sub_mult : forall (a b x : Q),
  Qabs ((b - a) * x) == Qabs (a - b) * Qabs x.
Proof.
  intros a b x.
  rewrite (Qabs_Qmult (b - a) x).
  rewrite (q_abs_minus_sym b a).
  reflexivity.
Qed.

(* ---- 主件：pair 形 gap（|E_n(a) − E_n(b)| ≤ 4cT +              *)
(*        |a−b|·(2c·(S M)#1 + 2c + 1)）                            *)
(*        语句 = 审查 §4.1 逐字；体 = b5b_E_gap 体 L73738–73853    *)
(*        对应：(1−g,1) ↦ (a,b)、g ↦ Qabs (a−b)、域前提 ↦         *)
(*        QleT' (Qabs a) 1 ∧ QleT' (Qabs b) 1） ---- *)
Lemma b5dS_E_pair_gap : forall (n M : nat) (a b c : Q),
  Qle 0 c ->
  (forall j : nat, QleT' (exp_series j 2) c) ->
  QleT' (Qabs a) 1 -> QleT' (Qabs b) 1 ->
  NatLe M n ->
  Qle (Qabs (b5b_En n a - b5b_En n b))
      (Qplus (Qmult (Qmult 4 c) (1 / (Z.of_nat (2 * M + 3) # 1)))
             (Qmult (Qabs (a - b))
                    (Qplus (Qmult (Qmult 2 c) (Z.of_nat (Datatypes.S M) # 1))
                           (Qplus (Qmult 2 c) 1)))).
Proof.
  intros n M a b c Hc0 HC Ha Hb HMn.
  set (A := arctan_partial n a).
  set (B := arctan_partial n b).
  set (T := 1 / (Z.of_nat (2 * M + 3) # 1)).
  set (G := Z.of_nat (Datatypes.S M) # 1).
  set (W := Qplus (Qmult 2 c) 1).
  set (U := Qplus T (Qplus (Qmult G (Qabs (a - b))) T)).
  set (cU := Qmult c U).
  (* |A| ≤ 2、|B| ≤ 2（apT2 @ 前提 Ha/Hb） *)
  assert (HAn : QleT' (Qabs A) 2).
  { unfold A. apply (b5b_apT2 a n). exact Ha. }
  assert (HBn : QleT' (Qabs B) 2).
  { unfold B. apply (b5b_apT2 b n). exact Hb. }
  (* 分裂界：Ab := |A−B| ≤ T + G·|a−b| + T（ap_split 直引——        *)
  (*   pair 形输出即 |a−b|，无需 abs_oneminusg 步骤） *)
  assert (Hsplit : Qle (Qabs (A - B))
                       (Qplus T (Qplus (Qmult G (Qabs (a - b))) T))).
  { apply (Qle_trans _ (Qplus (Qplus T (Qmult G (Qabs (a - b)))) T) _).
    - unfold A, B, T, G.
      apply (b5b_ap_split M n a b HMn Ha Hb).
    - apply qeq_le. exact (b5b_ring_assoc_q T (Qmult G (Qabs (a - b))) T). }
  (* HabU：|A−B| ≤ U *)
  assert (HabU : Qle (Qabs (A - B)) U).
  { unfold U. exact Hsplit. }
  (* 三角 1：|En a − En b| ≤ |sinA−sinB| + (|b·(cB−cA)| + |(b−a)·cA|) *)
  assert (Htri1 : Qle (Qabs (b5b_En n a - b5b_En n b))
                      (Qplus (Qabs (sin_partial n A - sin_partial n B))
                             (Qplus (Qabs (cos_partial n B - cos_partial n A))
                                    (Qmult (Qabs (a - b)) (Qabs (cos_partial n A)))))).
  { unfold b5b_En.
    apply (Qle_trans _ (Qabs ((sin_partial n A - sin_partial n B) +
                              (b * (cos_partial n B - cos_partial n A) +
                               (b - a) * cos_partial n A))) _).
    - apply qeq_le.
      apply (Qabs_wd (sin_partial n A - a * cos_partial n A -
                      (sin_partial n B - b * cos_partial n B))
                     ((sin_partial n A - sin_partial n B) +
                      (b * (cos_partial n B - cos_partial n A) + (b - a) * cos_partial n A))).
      exact (b5dS_ring_Ediff (sin_partial n A) (sin_partial n B)
                             (cos_partial n A) (cos_partial n B) a b).
    - apply (Qle_trans _ (Qplus (Qabs (sin_partial n A - sin_partial n B))
                                (Qabs (b * (cos_partial n B - cos_partial n A) +
                                       (b - a) * cos_partial n A))) _).
      + apply Qabs_triangle.
      + apply Qplus_le_compat.
        * apply Qle_refl.
        * apply (Qle_trans _ (Qplus (Qabs (b * (cos_partial n B - cos_partial n A)))
                                    (Qabs ((b - a) * cos_partial n A))) _).
          -- apply Qabs_triangle.
          -- apply Qplus_le_compat.
             ++ apply (b5dS_abs_le1_mult b (cos_partial n B - cos_partial n A)).
                exact Hb.
             ++ apply qeq_le.
                apply (b5dS_abs_sub_mult a b (cos_partial n A)). }
  (* 片界：sin/cos-lip 与 cos_val @ |A|,|B| ≤ 2 *)
  assert (Hs : Qle (Qabs (sin_partial n A - sin_partial n B))
                   (Qmult (Qabs (A - B)) c)).
  { apply (b5b_sin_lip2 n A B c HC HAn HBn). }
  assert (Hco : Qle (Qabs (cos_partial n A - cos_partial n B))
                    (Qmult (Qabs (A - B)) c)).
  { apply (b5b_cos_lip2 n A B c HC Hc0 HAn HBn). }
  assert (Hval : Qle (Qabs (cos_partial n A)) (Qplus (Qmult 2 c) 1)).
  { apply (b5b_cos_val2 n A c HC Hc0 HAn). }
  assert (Hgv : Qle (Qmult (Qabs (a - b)) (Qabs (cos_partial n A)))
                    (Qmult (Qabs (a - b)) W)).
  { unfold W.
    apply (sc_qmult_le_l (Qabs (cos_partial n A)) (Qplus (Qmult 2 c) 1)
                         (Qabs (a - b))).
    - exact Hval.
    - apply Qabs_nonneg. }
  (* |cosB−cosA| ≤ |A−B|·c（换向桥） *)
  assert (Hco2 : Qle (Qabs (cos_partial n B - cos_partial n A))
                     (Qmult (Qabs (A - B)) c)).
  { apply (Qle_trans _ (Qabs (cos_partial n A - cos_partial n B)) _).
    - apply qeq_le. apply Qeq_sym.
      apply (q_abs_minus_sym (cos_partial n A) (cos_partial n B)).
    - exact Hco. }
  (* 汇总 S1 *)
  assert (HS1 : Qle (Qabs (b5b_En n a - b5b_En n b))
                    (Qplus (Qmult (Qabs (A - B)) c)
                           (Qplus (Qmult (Qabs (A - B)) c)
                                  (Qmult (Qabs (a - b)) W)))).
  { apply (Qle_trans _ (Qplus (Qabs (sin_partial n A - sin_partial n B))
                              (Qplus (Qabs (cos_partial n B - cos_partial n A))
                                     (Qmult (Qabs (a - b)) (Qabs (cos_partial n A))))) _).
    - exact Htri1.
    - apply Qplus_le_compat.
      + exact Hs.
      + apply Qplus_le_compat.
        * exact Hco2.
        * exact Hgv. }
  (* Ab·c ≤ cU *)
  assert (HcAb : Qle (Qmult (Qabs (A - B)) c) cU).
  { apply (Qle_trans _ (Qmult c (Qabs (A - B))) _).
    - apply qeq_le. exact (Qmult_comm (Qabs (A - B)) c).
    - unfold cU.
      apply (sc_qmult_le_l (Qabs (A - B)) U c).
      + exact HabU.
      + exact Hc0. }
  (* S1 ≤ cU + (cU + gW) *)
  assert (HS2 : Qle (Qabs (b5b_En n a - b5b_En n b))
                    (Qplus cU (Qplus cU (Qmult (Qabs (a - b)) W)))).
  { apply (Qle_trans _ (Qplus (Qmult (Qabs (A - B)) c)
                              (Qplus (Qmult (Qabs (A - B)) c)
                                     (Qmult (Qabs (a - b)) W))) _).
    - exact HS1.
    - apply Qplus_le_compat.
      + exact HcAb.
      + apply Qplus_le_compat.
        * exact HcAb.
        * apply Qle_refl. }
  (* 结论：cU + (cU + gW) ≤ Tgt（ring_close @ g := Qabs (a−b)） *)
  apply (Qle_trans _ (Qplus cU (Qplus cU (Qmult (Qabs (a - b)) W))) _).
  - exact HS2.
  - apply qeq_le.
    unfold cU, U, W, G, T.
    exact (b5b_ring_close c (Qabs (a - b)) T G W).
Qed.

(* ============================================================ *)
(* 段 B：pair 形等度连续（b5dS_E_pair_close）                     *)
(* 同构源：根 b5b_E_close_q L77321–77408（体 L77326–77408）。     *)
(* 改动：窗前提 (Qlt 0 g / Qle g g0) ↦ (QleT' (Qabs a) 1 /         *)
(*   QleT' (Qabs b) 1 / Qle (Qabs (a−b)) d0)；输出 N := M（arch）、 *)
(*   d0 := X（= (2·(eps/3))/K——pair 版窗不需 min(1,X) 帽：         *)
(*   域前提独立于窗，gap 不需 |a−b| ≤ 1 侧）；eps 预算体           *)
(*   （4cT < eps/3；|a−b|·K ≤ X·K == 2·(eps/3)；third_sum）    *)
(*   逐字同构。b5b_ecl_* 族全直引（div_pos/arch_in/arch_cancel/   *)
(*   third_sum/third_pos/mult_lt_l/K_ge1/XK_cancel）。             *)
(* 语句 = 审查 §4.1 逐字（sigT 输出 [Nc, d0]，纯 Q 层、与 x 无关）。*)
(* ============================================================ *)

Lemma b5dS_E_pair_close : forall (eps : Q), Qlt 0 eps ->
  sigT (fun N : nat => sigT (fun d0 : Q => And (QltT 0 d0)
    (forall (n : nat) (a b : Q), NatLe N n ->
      QleT' (Qabs a) 1 -> QleT' (Qabs b) 1 ->
      Qle (Qabs (a - b)) d0 ->
      Qlt (Qabs (b5b_En n a - b5b_En n b)) eps))).
Proof.
  intros eps Heps.
  (* c := b5b_arch2（c ≥ 1；HC := ∀j exp_series j 2 ≤T c） *)
  destruct b5b_arch2 as [c [Hc1T HC]].
  assert (Hc1 : Qle 1 c) by (exact (QleT'_to_Qle 1 c Hc1T)).
  assert (Hcpos : Qlt 0 c).
  { apply (Qlt_le_trans 0 1 c); [unfold Qlt; simpl; lia | exact Hc1]. }
  assert (Hc0 : Qle 0 c).
  { apply (Qle_trans _ 1 _); [unfold Qle; simpl; lia | exact Hc1]. }
  (* arch 输入正性，q_arch_inv 取 M：1/(M+2) < eps/(12c) *)
  assert (Harchpos : Qlt 0 (eps / (12 * c))) by
    (apply (b5b_ecl_arch_in c eps Hcpos Heps)).
  destruct (q_arch_inv (eps / (12 * c)) Harchpos) as [M HM].
  (* 记 T := 1/(2M+3)、K := 2c·(S M)#1 + 2c + 1（与 b5dS_E_pair_gap *)
  (*   RHS 逐字一致）；X := (2·(eps/3))/K；d0 := X                  *)
  set (T := 1 / (Z.of_nat (2 * M + 3) # 1)).
  set (K := 2 * c * (Z.of_nat (Datatypes.S M) # 1) + (2 * c + 1)).
  set (X := (2 * (eps / 3)) / K).
  (* 事实：K ≥ 1、K > 0、K ≠ 0；X > 0；X·K == 2·(eps/3)；0<eps/3 *)
  assert (He3 : Qlt 0 (eps / 3)) by (apply (b5b_ecl_third_pos eps); exact Heps).
  assert (Hk1 : Qle 1 K).
  { unfold K. apply (b5b_ecl_K_ge1 M c). exact Hc1. }
  assert (Hkpos : Qlt 0 K).
  { apply (Qlt_le_trans 0 1 K); [unfold Qlt; simpl; lia | exact Hk1]. }
  assert (Hk0 : Qle 0 K).
  { apply (Qle_trans _ 1 _); [unfold Qle; simpl; lia | exact Hk1]. }
  assert (Hkneq : ~ (K == 0)) by (apply (q_neq_of_lt K); exact Hkpos).
  assert (H2e3 : Qlt 0 (2 * (eps / 3))).
  { apply (Qmult_lt_0_compat 2 (eps / 3)); [unfold Qlt; simpl; lia | exact He3]. }
  assert (HXpos : Qlt 0 X).
  { unfold X. apply (b5b_ecl_div_pos (2 * (eps / 3)) K); [exact H2e3 | exact Hkpos]. }
  assert (HXK : X * K == 2 * (eps / 3)).
  { unfold X. apply (b5b_ecl_XK_cancel eps K Hkneq). }
  (* 返回 N := M、d0 := X *)
  exists M. exists X. split.
  - exact (Qlt_to_QltT 0 X HXpos).
  - intros n a b Hn Ha Hb Hab.
    (* 域前提直供（pair gap 前提逐字：QleT' (Qabs a) 1 / QleT' (Qabs b) 1） *)
    (* b5dS_E_pair_gap：|Δ| ≤ 4cT + |a−b|·K *)
    assert (Hgap : Qle (Qabs (b5b_En n a - b5b_En n b))
                       ((4 * c) * T + (Qabs (a - b)) * K)).
    { apply (b5dS_E_pair_gap n M a b c Hc0 HC Ha Hb Hn). }
    (* 第 1 项：4cT < eps/3（T ≤ 1/(M+2) < eps/(12c)，乘 4c>0，field 收） *)
    assert (Ht_le : Qle T (1 / (Z.of_nat (M + 2) # 1))).
    { unfold T. apply (atan_inv_chain M M). lia. }
    assert (Ht_arch : Qlt T (eps / (12 * c))).
    { apply (Qle_lt_trans T (1 / (Z.of_nat (M + 2) # 1)) (eps / (12 * c)));
        [exact Ht_le | exact HM]. }
    assert (H4c : Qlt 0 (4 * c)) by
      (apply (Qmult_lt_0_compat 4 c); [unfold Qlt; simpl; lia | exact Hcpos]).
    assert (Ht1m : Qlt ((4 * c) * T) ((4 * c) * (eps / (12 * c)))).
    { apply (b5b_ecl_mult_lt_l T (eps / (12 * c)) (4 * c));
        [exact H4c | exact Ht_arch]. }
    assert (Ht1 : Qlt ((4 * c) * T) (eps / 3)).
    { apply (Qlt_le_trans ((4 * c) * T) ((4 * c) * (eps / (12 * c))) (eps / 3));
        [exact Ht1m | apply qeq_le; apply (b5b_ecl_arch_cancel c eps Hcpos Heps)]. }
    (* 第 2 项：|a−b|·K ≤ X·K == 2·(eps/3)（K ≥ 0 乘 |a−b| ≤ X） *)
    assert (HgK : Qle ((Qabs (a - b)) * K) (X * K)).
    { apply (Qmult_le_compat_r (Qabs (a - b)) X K); [exact Hab | exact Hk0]. }
    assert (Ht2 : Qle ((Qabs (a - b)) * K) (2 * (eps / 3))).
    { apply (Qle_trans ((Qabs (a - b)) * K) (X * K) (2 * (eps / 3)));
        [exact HgK | apply qeq_le; exact HXK]. }
    (* 总和：4cT + |a−b|·K < eps/3 + 2·(eps/3) == eps *)
    assert (Hsum : Qlt ((4 * c) * T + (Qabs (a - b)) * K)
                      (eps / 3 + 2 * (eps / 3))).
    { apply (Qplus_lt_le_compat ((4 * c) * T) (eps / 3)
                                ((Qabs (a - b)) * K) (2 * (eps / 3)));
        [exact Ht1 | exact Ht2]. }
    assert (Hsum2 : Qlt ((4 * c) * T + (Qabs (a - b)) * K) eps).
    { apply (Qlt_le_trans ((4 * c) * T + (Qabs (a - b)) * K)
                          (eps / 3 + 2 * (eps / 3)) eps);
        [exact Hsum | apply qeq_le; apply (b5b_ecl_third_sum eps Heps)]. }
    (* 结论：|Δ| ≤ 4cT + |a−b|·K < eps *)
    apply (Qle_lt_trans (Qabs (b5b_En n a - b5b_En n b))
                         ((4 * c) * T + (Qabs (a - b)) * K) eps);
      [exact Hgap | exact Hsum2].
Qed.

(* ============================================================ *)
(* 段 C 占位（本件不写——待 item27 .vo 就位后另派）：              *)
(* 段 C 主件 = F1 目标语句逐字（= T4 §4 = b5b_f1_closure' L78187   *)
(*   前提逐字）：                                                 *)
(*   Lemma b5dS_E_zero_on_unit : forall (x : Real) (Hx : cw_unit x), *)
(*     real_lt real_zero x -> real_lt x (real_const 1) ->         *)
(*     real_eq (real_E x Hx) real_zero.                           *)
(* 段 C 依赖：CW + item27 b5dQ_E_rational_zero（上游 sc2_b5a_item27） *)
(*   ——段 A/B 零上游依赖。                *)
(* ============================================================ *)

(* ============================================================ *)
(* 验证记录：3 小件真 Qed + 段 A 主件 Qed + 段 B 主件 Qed；       *)
(*   前缀 b5dS_ 独占。                                           *)
(* ============================================================ *)


(* ============================================================ *)
(* 段 C：b5dS_E_zero_on_unit（主件）+ 证书族小件——文本预置       *)
(* （预置先行模式：item24/25 先例——不编译，如实标注）            *)
(* 设计契约：F1 扩展分支 A item29 段 C 预置。                    *)
(*   （权威设计 = 密度闭合审查 §4.1     *)
(*     装配骨架逐条落实，见下方代码注释分步标记）。              *)
(* 本段取代 L336-344 占位注释（占位 = 段 A/B 会话所留——只增不改   *)
(*   纪律：本段全部为新追加文本，段 A/B 正文与既有注释零改动）。  *)
(* ------------------------------------------------------------ *)
(* 状态标注：本段依赖上游合并件 sc2_b5a_item27.v，该件就位前     *)
(*   本段不编译；下述 Require 行为其占位标注，就位后仅需编译     *)
(*   验证。                                                      *)
(* ------------------------------------------------------------ *)
(* 主件语句 = T4 §4 逐字 = 根 b5b_f1_closure'（L78187-78191）    *)
(*   前提逐字（仅 Lemma 名 b5a_E_zero_on_unit ↦ b5dS_E_zero_on_   *)
(*   unit；机器 diff 核对：与 E-ODE-T4-闭合 §4 L49-51 / 审查      *)
(*   §1 L34-37 + §4.1 L139-141 / 根 L78188-78190 / 本文件 L339-341 *)
(*   占位 / item30.v L61-63 六源 panel 零漂移——本会话逐字实测）： *)
(*   Lemma b5dS_E_zero_on_unit : forall (x : Real) (Hx : cw_unit x), *)
(*     real_lt real_zero x -> real_lt x (real_const 1) ->         *)
(*     real_eq (real_E x Hx) real_zero.                           *)
(* item27 主件语句（唯一上游取用点——语句契约逐字，名映射        *)
(*   b5dH_→b5dQ_，语句不变；本件已复核）： *)
(*   b5dQ_E_rational_zero : forall (q : Q), Qlt 0 q -> Qlt q 1 -> *)
(*     forall (Hq : cw_unit (real_const q)),                      *)
(*     real_eq (real_E (real_const q) Hq) real_zero.              *)
(*   取用形（本段步骤 4）：destruct (b5dQ_E_rational_zero q Hq0    *)
(*     Hq1 Hq (epsQ / 2) HhalfT) as [Nz HNz]。                    *)
(* ------------------------------------------------------------ *)
(* 装配骨架（依设计 §4.1 步骤 1-5 逐条落实——每步语义已核）：       *)
(*   1. 等度连续取窗：destruct (b5dS_E_pair_close (epsQ/2) ...)   *)
(*      取 [Nc, d0]——d0 纯 Q 层、与 x 无关（先于坐标选择：无环）；*)
(*   2. 坐标分离 + Cauchy 选 q：destruct Hx0 得 e0/N0s（尾        *)
(*      x_n − 0 > e0）、destruct Hx1 得 e1/N1s（尾 1 − x_n > e1）、*)
(*      Cauchy @ d0 得 Nτ；Nq := max(max N0s N1s) Nτ（三数全部在  *)
(*      d0 之前可 destruct——无环）；q := x_Nq（Cauchy 直给坐标     *)
(*      逼近，不需 arch 选坐标）；                               *)
(*   3. q 的证书族：b5dS_sep0_lt（0 < e0 < x_Nq − 0 ⟹ 0 < q）与  *)
(*      b5dS_sep1_lt（0 < e1 < 1 − x_Nq ⟹ q < 1）两分离证书构造   *)
(*      严格 0 < q < 1；b5c_const_unit @ (Qle 0 q / Qle q 1) 给   *)
(*      Hq : cw_unit (real_const q)；b5dS_const_unit_qle1 给      *)
(*      |q| ≤ 1 形（段 B 的 b 前提）；                           *)
(*   4. 有理零：b5dQ_E_rational_zero @ q := x_Nq（步骤 3 证书）    *)
(*      destruct @ epsQ/2 取 [Nz HNz]：n ≥ Nz ⟹ |E(q)_n − 0| <    *)
(*      epsQ/2；                                                   *)
(*   5. 结论：N := max(max Nc Nq) Nz；对 n ≥ N（Q 层纯算术）：     *)
(*      - 三角：|E(x)_n − 0_n| ≤ |E(x)_n − E(q)_n| + |E(q)_n − 0_n|；*)
(*      - 坐标恒等（b5b_En_proj ×2 + real_const 投影 kernel 收）：*)
(*        |E(x)_n − E(q)_n| == |b5b_En n (x_n) − b5b_En n q|；    *)
(*      - 段 B（pair_close_step glue ⑤）@ (a := x_n, b := q)：    *)
(*        前提 |x_n| ≤ 1（Hx n）/ |q| ≤ 1（③）/ |x_n − x_Nq| ≤ d0  *)
(*        （Cauchy：n ≥ Nq ≥ Nτ 且 Nq ≥ Nτ 双侧达标——③）⟹         *)
(*        < epsQ/2（n ≥ Nc）；                                   *)
(*      - 第二项 < epsQ/2（n ≥ Nz）；两项和 < epsQ                 *)
(*        （Qplus_lt_compat + b5b_ep_half_sum）⟹ real_eq 定义     *)
(*        （L3448）直接闭合。                                     *)
(*   结论形逐句同构根 b5b_endpoint（L78062-78177，已闭样板）。    *)
(* 端点说明：x ∈ (0,1) 由两 real_lt 前提给正分离度（e0、e1），    *)
(*   q := x_Nq 对 Nq ≥ max(N0s, N1s) 严格落入 (0,1)——x 贴 0/贴 1  *)
(*   情形由前提自动排除（端点不在量化域）——无拼接件（审查 R3）。  *)
(* 依赖：CW.ConstructiveWorld（b5b_En_proj L73696 / b5c_const_unit *)
(*   L74348 / b5b_ep_half_sum L78001 / q_half_pos L45573 /        *)
(*   b5b_En L73692 / real_eq L3448 / real_lt L3517 / cauchy L3441）  *)
(*   + 段 A/B（本文件 b5dS_E_pair_close）+ item27 b5dQ_E_rational_ *)
(*   zero（上游 sc2_b5a_item27）。                         *)
(* 收尾形：全 Qed 正常收尾（前提式取用 + real_eq 尾证书闭合——     *)
(*   段 C 不产出值路径见证，与 item16/18 同型）。                  *)
(* ============================================================ *)
(* 注：上游 sc2_b5a_item27 就位后本 Require 行方可编译；         *)
(*   本段其余文本与其无文本依赖。                                 *)

(* ============================================================ *)
(* 段 C 证书族小件 ①：分离证书 e0 侧——0 < q 严格证书构造          *)
(*   输入 = real_lt real_zero x 的坐标见证 e0（QltT 0 e0 与尾      *)
(*   QltT e0 (u N − 0)，后者 projT1 real_zero N 定义性 == 0）     *)
(*   证法：Qlt_trans 0 e0 (u N − 0)（两 QltT 见证转 Qlt）+         *)
(*   proj2 (Qlt_minus_iff 0 (u N))：0 < (u N) − 0 ⟺ 0 < u N。    *)
(* ============================================================ *)
Lemma b5dS_sep0_lt : forall (u : Qseq) (N : nat) (e0 : Q),
  QltT 0 e0 ->
  QltT e0 (u N - 0) ->
  Qlt 0 (u N).
Proof.
  intros u N e0 He0 He0N.
  apply (proj2 (Qlt_minus_iff 0 (u N))).
  apply (Qlt_trans 0 e0 (u N - 0)).
  - apply QltT_to_Qlt. exact He0.
  - apply QltT_to_Qlt. exact He0N.
Qed.

(* ============================================================ *)
(* 段 C 证书族小件 ②：分离证书 e1 侧——q < 1 严格证书构造          *)
(*   输入 = real_lt x (real_const 1) 的坐标见证 e1（QltT 0 e1 与   *)
(*   尾 QltT e1 (1 − u N)，projT1 (real_const 1) N 定义性 == 1）  *)
(*   证法：Qlt_trans 0 e1 (1 − u N) + proj2 (Qlt_minus_iff (u N) 1)*)
(*   ：0 < 1 − u N ⟺ u N < 1。                                  *)
(* ============================================================ *)
Lemma b5dS_sep1_lt : forall (u : Qseq) (N : nat) (e1 : Q),
  QltT 0 e1 ->
  QltT e1 (1 - u N) ->
  Qlt (u N) 1.
Proof.
  intros u N e1 He1 He1N.
  apply (proj2 (Qlt_minus_iff (u N) 1)).
  apply (Qlt_trans 0 e1 (1 - u N)).
  - apply QltT_to_Qlt. exact He1.
  - apply QltT_to_Qlt. exact He1N.
Qed.

(* ============================================================ *)
(* 段 C 证书族小件 ③：Cauchy 逼近证书（距离 ≤ d0 形）             *)
(*   cauchy（根 L3441）输出 QltT 严格形；段 B 窗前提 = Qle 形      *)
(*   ⟹ QltT_to_Qlt + Qlt_le_weak 弱化（主件步骤 5 的 |x_n −       *)
(*   x_Nq| ≤ d0 证书：m := n 运行下标、n := Nq 固定下标——双侧     *)
(*   ≥ Nτ 由 Nq ≥ Nτ 与 n ≥ Nq 保证）。                          *)
(* ============================================================ *)
Lemma b5dS_cauchy_le : forall (u : Qseq) (Ntau : nat) (d0 : Q) (m n : nat),
  (forall (m0 n0 : nat), NatLe Ntau m0 -> NatLe Ntau n0 ->
    QltT (Qabs (u m0 - u n0)) d0) ->
  NatLe Ntau m -> NatLe Ntau n ->
  Qle (Qabs (u m - u n)) d0.
Proof.
  intros u Ntau d0 m n Hc Hm Hn.
  apply Qlt_le_weak.
  apply QltT_to_Qlt.
  exact (Hc m n Hm Hn).
Qed.

(* ============================================================ *)
(* 段 C 证书族小件 ④：|q| ≤ 1 glue（QleT' 形——段 B 的 b 前提；    *)
(*   Hq 证书逐点投影 projT1 (real_const q) n 定义性 == q）        *)
(* ============================================================ *)
Lemma b5dS_const_unit_qle1 : forall (q : Q) (Hq : cw_unit (real_const q)),
  QleT' (Qabs q) 1.
Proof.
  intros q Hq.
  exact (Hq 0%nat).
Qed.

(* ============================================================ *)
(* 段 C 证书族小件 ⑤：pair-close 实例化 glue                      *)
(*   段 B 内层窗（b5dS_E_pair_close 第二分量）→ 坐标差 QltT 形     *)
(*   ——主件步骤 5 term1 直接应用（a := x_n、b := q 实例化）           *)
(* ============================================================ *)
Lemma b5dS_pair_close_step : forall (eps d0 : Q) (Nc : nat) (a b : Q) (n : nat),
  (forall (n0 : nat) (a0 b0 : Q), NatLe Nc n0 ->
    QleT' (Qabs a0) 1 -> QleT' (Qabs b0) 1 ->
    Qle (Qabs (a0 - b0)) d0 ->
    Qlt (Qabs (b5b_En n0 a0 - b5b_En n0 b0)) eps) ->
  NatLe Nc n ->
  QleT' (Qabs a) 1 -> QleT' (Qabs b) 1 ->
  Qle (Qabs (a - b)) d0 ->
  QltT (Qabs (b5b_En n a - b5b_En n b)) eps.
Proof.
  intros eps d0 Nc a b n Hw Hn Ha Hb Hab.
  apply Qlt_to_QltT.
  exact (Hw n a b Hn Ha Hb Hab).
Qed.

(* ============================================================ *)
(* 段 C 主件：b5dS_E_zero_on_unit                                *)
(* 语句 = T4 §4 = b5b_f1_closure' 前提逐字（六源 panel 零漂移，   *)
(*   见段头注）；体 = 设计 §4.1 骨架步骤 1–5（段头注逐条）+ 结论   *)
(*   形同构根 b5b_endpoint（L78062–78177）。                      *)
(* ============================================================ *)
Lemma b5dS_E_zero_on_unit : forall (x : Real) (Hx : cw_unit x),
  real_lt real_zero x -> real_lt x (real_const 1) ->
  real_eq (real_E x Hx) real_zero.
Proof.
  intros x Hx Hx0 Hx1.
  (* real_eq 的 eps 输入 + epsQ/2 半预算（b5b_endpoint L78064–78067 同款） *)
  intros epsQ HepsQT.
  assert (HepsQ : Qlt 0 epsQ) by (apply QltT_to_Qlt; exact HepsQT).
  assert (HhalfQ : Qlt 0 (epsQ / 2)) by (apply QltT_to_Qlt; apply q_half_pos; exact HepsQT).
  assert (HhalfT : QltT 0 (epsQ / 2)) by (apply Qlt_to_QltT; exact HhalfQ).
  (* 步骤 1：等度连续取窗——pair-close @ epsQ/2 得 [Nc, d0]        *)
  (*   d0 纯 Q 层、与 x 无关——先于坐标选择（无环，审查 R7）        *)
  destruct (b5dS_E_pair_close (epsQ / 2) HhalfQ) as [Nc [d0 [Hd0pos Hpair]]].
  (* 步骤 2：坐标分离（e0/N0s、e1/N1s）+ Cauchy @ d0 取 Nτ        *)
  destruct Hx0 as [e0 [He0pos [N0s HN0s]]].
  destruct Hx1 as [e1 [He1pos [N1s HN1s]]].
  assert (Hd0T : QltT 0 d0) by exact Hd0pos.
  destruct (projT2 x d0 Hd0T) as [Ntau HNtau].
  (* Nq := max(max N0s N1s) Nτ；q := x_Nq（Cauchy 直给坐标逼近）   *)
  set (Nq := Nat.max (Nat.max N0s N1s) Ntau).
  set (q := projT1 x Nq).
  (* nat 层序号事实：N0s/N1s/Nτ ≤ Nq（显式 le_max 链，零 lia 依赖） *)
  assert (H0q : (N0s <= Nq)%nat).
  { unfold Nq.
    apply (Nat.le_trans N0s (Nat.max N0s N1s) (Nat.max (Nat.max N0s N1s) Ntau)).
    - apply Nat.le_max_l.
    - apply Nat.le_max_l. }
  assert (H1q : (N1s <= Nq)%nat).
  { unfold Nq.
    apply (Nat.le_trans N1s (Nat.max N0s N1s) (Nat.max (Nat.max N0s N1s) Ntau)).
    - apply Nat.le_max_r.
    - apply Nat.le_max_l. }
  assert (Htq : (Ntau <= Nq)%nat).
  { unfold Nq. apply Nat.le_max_r. }
  (* 步骤 3：q 的证书族——分离证书（小件 ①②）+ 单位证书 + |q|≤1    *)
  (*   glue（小件 ④）                                            *)
  assert (Hq0 : Qlt 0 q).
  { unfold q.
    apply (b5dS_sep0_lt (projT1 x) Nq e0).
    - exact He0pos.
    - exact (HN0s Nq (NatLe_lift _ _ H0q)). }
  assert (Hq1 : Qlt q 1).
  { unfold q.
    apply (b5dS_sep1_lt (projT1 x) Nq e1).
    - exact He1pos.
    - exact (HN1s Nq (NatLe_lift _ _ H1q)). }
  assert (Hq0le : Qle 0 q) by (apply (Qlt_le_weak 0 q); exact Hq0).
  assert (Hq1le : Qle q 1) by (apply (Qlt_le_weak q 1); exact Hq1).
  assert (Hq : cw_unit (real_const q)).
  { exact (b5c_const_unit q Hq0le Hq1le). }
  assert (Hqabs : QleT' (Qabs q) 1) by (exact (b5dS_const_unit_qle1 q Hq)).
  (* 步骤 4：有理零——item27 主件 b5dQ_E_rational_zero @ q := x_Nq  *)
  (*   （本段唯一上游取用点）destruct @ epsQ/2 取 [Nz, HNz]       *)
  destruct (b5dQ_E_rational_zero q Hq0 Hq1 Hq (epsQ / 2) HhalfT) as [Nz HNz].
  (* 步骤 5：结论——N := max(max Nc Nq) Nz；对 n ≥ N（坐标级）     *)
  exists (Nat.max (Nat.max Nc Nq) Nz).
  intros n Hn.
  apply NatLe_drop in Hn.
  assert (HnNc : (Nc <= n)%nat).
  { exact (Nat.le_trans Nc (Nat.max (Nat.max Nc Nq) Nz) n
             (Nat.le_trans Nc (Nat.max Nc Nq) (Nat.max (Nat.max Nc Nq) Nz)
                (Nat.le_max_l Nc Nq) (Nat.le_max_l (Nat.max Nc Nq) Nz)) Hn). }
  assert (HnNq : (Nq <= n)%nat).
  { exact (Nat.le_trans Nq (Nat.max (Nat.max Nc Nq) Nz) n
             (Nat.le_trans Nq (Nat.max Nc Nq) (Nat.max (Nat.max Nc Nq) Nz)
                (Nat.le_max_r Nc Nq) (Nat.le_max_l (Nat.max Nc Nq) Nz)) Hn). }
  assert (HnNz : (Nz <= n)%nat).
  { exact (Nat.le_trans Nz (Nat.max (Nat.max Nc Nq) Nz) n
             (Nat.le_max_r (Nat.max Nc Nq) Nz) Hn). }
  assert (HnNtau : (Ntau <= n)%nat).
  { exact (Nat.le_trans Ntau Nq n Htq HnNq). }
  (* term1 坐标恒等：|E(x)_n − E(q)_n| == |b5b_En n (x_n) −         *)
  (*   b5b_En n q|（b5b_En_proj ×2；real_const 投影 kernel 收——   *)
  (*   b5b_endpoint L78108–78117 同款）                            *)
  assert (Ht1eq : (projT1 (real_E x Hx) n - projT1 (real_E (real_const q) Hq) n) ==
                  (b5b_En n (projT1 x n) - b5b_En n q)).
  { rewrite (b5b_En_proj x Hx n).
    rewrite (b5b_En_proj (real_const q) Hq n).
    reflexivity. }
  assert (Ht1abs : Qabs (projT1 (real_E x Hx) n - projT1 (real_E (real_const q) Hq) n) ==
                   Qabs (b5b_En n (projT1 x n) - b5b_En n q)).
  { apply (Qabs_wd (projT1 (real_E x Hx) n - projT1 (real_E (real_const q) Hq) n)
                   (b5b_En n (projT1 x n) - b5b_En n q)).
    exact Ht1eq. }
  (* term1 界：段 B（pair-close 实例化 glue ⑤）@ (a := x_n, b := q) *)
  (*   前提：n ≥ Nc（HnNc）/ |x_n| ≤ 1（Hx n）/ |q| ≤ 1（Hqabs）/  *)
  (*   |x_n − x_Nq| ≤ d0（Cauchy 逼近证书 ③——m := n、n := Nq，     *)
  (*   双侧 ≥ Nτ：n ≥ Nq ≥ Nτ 且 Nq ≥ Nτ）⟹ < epsQ/2              *)
  assert (Ht1w : QltT (Qabs (b5b_En n (projT1 x n) - b5b_En n q)) (epsQ / 2)).
  { apply (b5dS_pair_close_step (epsQ / 2) d0 Nc (projT1 x n) q n Hpair).
    - apply NatLe_lift. exact HnNc.
    - exact (Hx n).
    - exact Hqabs.
    - apply (b5dS_cauchy_le (projT1 x) Ntau d0 n Nq HNtau).
      + apply NatLe_lift. exact HnNtau.
      + apply NatLe_lift. exact Htq. }
  (* term1 重述到实层差（qltT_eq_compat_l——b5b_endpoint            *)
  (*   L78125–78135 同款）                                        *)
  assert (Hterm1T : QltT (Qabs (projT1 (real_E x Hx) n - projT1 (real_E (real_const q) Hq) n))
                          (epsQ / 2)).
  { apply (qltT_eq_compat_l (Qabs (b5b_En n (projT1 x n) - b5b_En n q))
                            (Qabs (projT1 (real_E x Hx) n - projT1 (real_E (real_const q) Hq) n))
                            (epsQ / 2)).
    - apply Qeq_sym. exact Ht1abs.
    - exact Ht1w. }
  assert (Hterm1 : Qlt (Qabs (projT1 (real_E x Hx) n - projT1 (real_E (real_const q) Hq) n))
                        (epsQ / 2))
    by (apply QltT_to_Qlt; exact Hterm1T).
  (* term2 界：|E(q)_n − 0_n| < epsQ/2（item27 尾证书 HNz 直给——   *)
  (*   b5b_endpoint L78137–78142 同款）                            *)
  assert (Hterm2T : QltT (Qabs (projT1 (real_E (real_const q) Hq) n - projT1 real_zero n))
                          (epsQ / 2)).
  { exact (HNz n (NatLe_lift _ _ HnNz)). }
  assert (Hterm2 : Qlt (Qabs (projT1 (real_E (real_const q) Hq) n - projT1 real_zero n))
                        (epsQ / 2))
    by (apply QltT_to_Qlt; exact Hterm2T).
  (* 三角：|E(x)_n − 0_n| ≤ |E(x)_n − E(q)_n| + |E(q)_n − 0_n|    *)
  assert (Htri : Qle (Qabs (projT1 (real_E x Hx) n - projT1 real_zero n))
                     (Qplus (Qabs (projT1 (real_E x Hx) n - projT1 (real_E (real_const q) Hq) n))
                            (Qabs (projT1 (real_E (real_const q) Hq) n - projT1 real_zero n)))).
  { apply (Qle_trans _
             (Qabs ((projT1 (real_E x Hx) n - projT1 (real_E (real_const q) Hq) n) +
                    (projT1 (real_E (real_const q) Hq) n - projT1 real_zero n))) _).
    - apply qeq_le.
      apply (Qabs_wd (projT1 (real_E x Hx) n - projT1 real_zero n)
                     ((projT1 (real_E x Hx) n - projT1 (real_E (real_const q) Hq) n) +
                      (projT1 (real_E (real_const q) Hq) n - projT1 real_zero n))).
      ring.
    - apply Qabs_triangle. }
  (* 两项和 < epsQ/2 + epsQ/2 == epsQ ⟹ real_eq 闭合              *)
  assert (Hsum : Qlt (Qplus (Qabs (projT1 (real_E x Hx) n - projT1 (real_E (real_const q) Hq) n))
                            (Qabs (projT1 (real_E (real_const q) Hq) n - projT1 real_zero n)))
                     (Qplus (epsQ / 2) (epsQ / 2))).
  { apply (Qplus_lt_compat (Qabs (projT1 (real_E x Hx) n - projT1 (real_E (real_const q) Hq) n))
                           (epsQ / 2)
                           (Qabs (projT1 (real_E (real_const q) Hq) n - projT1 real_zero n))
                           (epsQ / 2)).
    - exact Hterm1.
    - exact Hterm2. }
  apply Qlt_to_QltT.
  apply (Qle_lt_trans (Qabs (projT1 (real_E x Hx) n - projT1 real_zero n))
                      (Qplus (Qabs (projT1 (real_E x Hx) n - projT1 (real_E (real_const q) Hq) n))
                             (Qabs (projT1 (real_E (real_const q) Hq) n - projT1 real_zero n)))
                      epsQ).
  - exact Htri.
  - apply (Qlt_le_trans (Qplus (Qabs (projT1 (real_E x Hx) n - projT1 (real_E (real_const q) Hq) n))
                               (Qabs (projT1 (real_E (real_const q) Hq) n - projT1 real_zero n)))
                        (Qplus (epsQ / 2) (epsQ / 2)) epsQ).
    + exact Hsum.
    + apply qeq_le. exact (b5b_ep_half_sum epsQ).
Qed.

(* ============================================================ *)
(* 段 C 预置状态记录（文本预置，未编译——如实）：                 *)
(*   新增 Lemma 6（证书族小件 5 + 主件 1，全 Qed 收尾意图）；      *)
(*   Lemma 计数预期：11（段 A/B 5 + 段 C 6）；前缀 b5dS_ 独占；    *)
(*   只增不改（段 A/B 零触碰——仅追加本段 + Require 行）；         *)
(*   上游 item27 就位后需真编译验证。                             *)
(*   预验证（scratch 副本内以契约语句占位后全件编译通过）：        *)
(*   语法 + 段 C 全证明体类型级闭合已实证；占位件未入本文件。      *)
(* ============================================================ *)

(* ============================================================ *)
(* 块 item30（前缀 b5dT_——主件 b5dT_f1_pi_geom_eq_leibniz_univ）——来源：演变/.ablation/sc2_parallel/sc2_b5a_ode/sc2_b5a_item30.v。 *)
(* ============================================================ *)

(* ============================================================ *)
(* 件 1（B′ 单点轨）：F1 无假设闭式                              *)
(*   链：b5dQ_E_rational_zero → b5dF_E_one_zero_of_rational →    *)
(*        b5b_hsc_main（L72994）→ a3_closure_f1（L67997）        *)
(*   体 4 战术 + Qed（纯应用链，零新证明）；                     *)
(*   等价一行形：exact (a3_closure_f1 (b5b_hsc_main               *)
(*     (b5dF_E_one_zero_of_rational b5dQ_E_rational_zero))).      *)
(*   依赖：item27 .vo（b5dQ_E_rational_zero）+ item16 .vo（已闭） *)
(* ============================================================ *)
(* ============================================================ *)
(* pi_triangle_direct_edge —— cos_pi_half == 2·arctan_one_real 闭式等式。 *)
(* 数学使命：cos_pi_half 为余弦在区间 (3/2,2) 内的唯一零点（即 π/2 的   *)
(*   构造性表示，见 cos_pi_half_unique_widened）；本件给出它与反正切    *)
(*   终值 2·arctan_one_real 的单条零前提等式，与 real_pi_geom ==        *)
(*   2·cos_pi_half 及 4·arctan_one_real == cauchy_real_pi_leibniz       *)
(*   相配，构成三量互连三角形的直接边。                                 *)
(* 依赖：S10_KVQuantTrig（cos_pi_half、cauchy_real_pi_leibniz）；       *)
(*   S11_TP3B5（arctan_one_real、a3_h4_value_bridge、                   *)
(*   channel_w_eq_two_theta、channel_w_eq_cos_pi_half、                 *)
(*   b5b_hsc_theorem）；本件段 C（b5dS_E_zero_on_unit）。               *)
(* 对标：mathlib Real.arctan_one_eq_pi_div_four 与 Real.cos_pi_two      *)
(*   的组合事实；本件为单条闭式引理。                                   *)
(* 构造性注记：零前提、零公理；Set 层承载（real_eq 为 sigT 上的逐项     *)
(*   收敛等价）；可提取。                                               *)
(* 编译配方：Rocq 9.1 coqc -native-compiler no -Q . ""，cpu_guard 限载。 *)
(* ============================================================ *)
(* 证明策略：由 a3_h4_value_bridge（4·arctan_one_real ==                *)
(*   cauchy_real_pi_leibniz）代入 N10Channel 节两件：                   *)
(*   channel_w_eq_cos_pi_half（另需 sin(arctan_one_real) ==             *)
(*   cos(arctan_one_real)，由 b5b_hsc_theorem b5dS_E_zero_on_unit       *)
(*   实例化）得 π_L/2 == cos_pi_half；channel_w_eq_two_theta 得         *)
(*   π_L/2 == 2·arctan_one_real；对称后传递合成。                       *)
Lemma pi_triangle_direct_edge :
  real_eq cos_pi_half (real_mult (real_const 2) arctan_one_real).
Proof.
  exact (real_eq_trans cos_pi_half
           (real_mult cauchy_real_pi_leibniz (real_const (1 / 2)))
           (real_mult (real_const 2) arctan_one_real)
           (real_eq_sym
              (real_mult cauchy_real_pi_leibniz (real_const (1 / 2)))
              cos_pi_half
              (channel_w_eq_cos_pi_half a3_h4_value_bridge
                 (b5b_hsc_theorem b5dS_E_zero_on_unit)))
           (channel_w_eq_two_theta a3_h4_value_bridge)).
Qed.
Lemma b5dT_f1_pi_geom_eq_leibniz_single :
  real_eq real_pi_geom cauchy_real_pi_leibniz.
Proof.
  apply a3_closure_f1.
  apply b5b_hsc_main.
  apply b5dF_E_one_zero_of_rational.
  exact b5dQ_E_rational_zero.
Qed.

(* ============================================================ *)
(* 件 2（∀x 轨）：F1 无假设闭式（依赖 item29 段 C——待段 C .vo） *)
(*   链：b5dS_E_zero_on_unit → b5b_f1_closure'（L78187）         *)
(*   体 2 战术 + Qed；语句 = 件 1 同（闭式）；                   *)
(*   等价一行形：exact (b5b_f1_closure' b5dS_E_zero_on_unit).    *)
(* ============================================================ *)
Lemma b5dT_f1_pi_geom_eq_leibniz_univ :
  real_eq real_pi_geom cauchy_real_pi_leibniz.
Proof.
  apply b5b_f1_closure'.
  exact b5dS_E_zero_on_unit.
Qed.

(* ============================================================ *)
(* 验证记录（预置时点 = 未编译——如实）：                         *)
(*   上游依赖（item27/item29 段 C）就位后需编译验证；              *)
(*   Lemma 计数预期：2 Lemma = 2 Qed；前缀 b5dT_ 独占；            *)
(*   语句核对：件 1/件 2 结论 = 终件 B 目标                        *)
(*     real_eq real_pi_geom cauchy_real_pi_leibniz 逐字；          *)
(*     体内引用五源件名/类型 = 头注契约逐字。                      *)
(* 终件 B 衔接：终件 B = real_pi_geom_eq_leibniz（论文点名名）——   *)
(*   两件已给实质闭式；论文名别名待终件 B 就位（与根件名零冲突）。   *)
(* ============================================================ *)

(* ============================================================ *)
(* 块 finalc（前缀 b5dU_——主件 b5dU_cos_piL_half_zero）——来源：演变/.ablation/sc2_parallel/sc2_b5a_ode/sc2_b5a_finalc.v。 *)
(* ============================================================ *)

(* ============================================================ *)
(* Route C：b5dU_cos_piL_half_zero_alt（零新证——a3_closure_n5   *)
(*   现成闭包；输入 = tan 通道 Hsc，与 F1 单点轨同源 E1——         *)
(*   probe_b5dU_p2 逐字实证）                   *)
(* ============================================================ *)
Lemma b5dU_cos_piL_half_zero_alt :
  real_eq (cauchy_real_cos (real_mult cauchy_real_pi_leibniz (real_const (1 / 2))))
          real_zero.
Proof.
  exact (a3_closure_n5 (b5b_hsc_main (b5dF_E_one_zero_of_rational b5dQ_E_rational_zero))).
Qed.

(* ============================================================ *)
(* Route A helper：b5dU_routeA_from_f1（F1 前提形——预研          *)
(*   probe_b5dU_p1 体逐字实证——验后已删重建）  *)
(*   环 A1：π_L·(1/2) == π_geom·(1/2)（F1 反向 + 乘法相容）；     *)
(*   环 A2：π_geom·(1/2) == cos_pi_half（unfold real_pi_geom +    *)
(*     结合律 + real_double_half_cancel）；                       *)
(*   环 A3+A4：cos 相容 ×2 + real_cos_pi_half_zero。          *)
(* ============================================================ *)
Lemma b5dU_routeA_from_f1 :
  real_eq real_pi_geom cauchy_real_pi_leibniz ->
  real_eq (cauchy_real_cos (real_mult cauchy_real_pi_leibniz (real_const (1 / 2))))
          real_zero.
Proof.
  intro Hf.
  assert (H1 : real_eq (real_mult cauchy_real_pi_leibniz (real_const (1 / 2)))
                       (real_mult real_pi_geom (real_const (1 / 2)))).
  { apply (RealSetoid.real_eq_mult_compat cauchy_real_pi_leibniz (real_const (1 / 2))
                                          real_pi_geom (real_const (1 / 2))).
    - apply real_eq_sym. exact Hf.
    - apply real_eq_refl. }
  assert (H2 : real_eq (real_mult real_pi_geom (real_const (1 / 2))) cos_pi_half).
  { unfold real_pi_geom.
    apply (real_eq_trans _ (real_mult (real_const 2) (real_mult cos_pi_half (real_const (1 / 2)))) _).
    - apply real_eq_sym. apply real_mult_assoc.
    - apply real_double_half_cancel. }
  apply (real_eq_trans _ (cauchy_real_cos (real_mult real_pi_geom (real_const (1 / 2)))) _).
  - apply real_cos_eq_compat. exact H1.
  - apply (real_eq_trans _ (cauchy_real_cos cos_pi_half) _).
    + apply real_cos_eq_compat. exact H2.
    + exact real_cos_pi_half_zero.
Qed.

(* ============================================================ *)
(* Route A 主件：b5dU_cos_piL_half_zero（实例化 item30 单点轨     *)
(*   b5dT_f1_pi_geom_eq_leibniz_single——_univ 同语句可选，单点轨  *)
(*   为 215 主链）                                              *)
(* ============================================================ *)
Lemma b5dU_cos_piL_half_zero :
  real_eq (cauchy_real_cos (real_mult cauchy_real_pi_leibniz (real_const (1 / 2))))
          real_zero.
Proof.
  exact (b5dU_routeA_from_f1 b5dT_f1_pi_geom_eq_leibniz_single).
Qed.

(* ============================================================ *)
(* 验证记录：Lemma 计数 3 = 3 Qed（_alt + routeA_from_f1 + 主件）； *)
(*   前缀 b5dU_ 独占。                                          *)
(* ============================================================ *)

(* ============================================================ *)
(* 块 25 · UpLogMono（Real 层 log 单调 le 版）  *)
(*   real_log_le_mono + real_log_le_zero_of_le_one    *)
(*   （HlogZ 前提直接应用形态）+ 桥接引理 real_lt_le_bridge/        *)
(*   real_eq_le_bridge；源：UpLogMono.v（上游）；零公理面、零承认件；4 Qed         *)
(* ============================================================ *)
(* ============================================================ *)
(* UpLogMono.v —— Real 层 log 单调 le 版      *)
(*                                                                *)
(* 论文 1 KLProjection（审计=KL投影）主定理的 HlogZ 前提            *)
(* （le (log Z_aud) zero）前提消解的最后一块：Z_aud ≤ 1 ⟹         *)
(* log Z_aud ≤ 0 需要「log 单调 le 版」——蓝图展望点名项。  *)
(* Real 层（cw_log/real_log）上 Or 编码的 le 逐支证明：              *)
(*   lt 支走 real_log_lt_mono（严格单调，根内已证）；                 *)
(*   eq 支走 real_log_wd（等式替换，根内已证）。                      *)
(* 纪律：零公理面、零承认件；Set 层语句；全 Qed；可提取。             *)
(* ============================================================ *)


(* lt → le 桥（real_le = Or (real_lt) (real_eq)，inl 直取） *)
Lemma real_lt_le_bridge : forall a b : Real, real_lt a b -> real_le a b.
Proof. intros a b H. exact (inl H). Qed.

(* eq → le 桥 *)
Lemma real_eq_le_bridge : forall a b : Real, real_eq a b -> real_le a b.
Proof. intros a b H. exact (inr H). Qed.

(* ========== 主引理：real_log 单调 le 版（Or 编码逐支证明） ========== *)
Lemma real_log_le_mono : forall (a b : Real) (Ha : real_lt real_zero a)
    (Hb : real_lt real_zero b),
  real_le a b -> real_le (real_log a Ha) (real_log b Hb).
Proof.
  intros a b Ha Hb Hab.
  destruct Hab as [Hlt | Heq].
  - (* lt 支：严格单调升 le *)
    exact (real_lt_le_bridge (real_log a Ha) (real_log b Hb)
             (real_log_lt_mono a b Ha Hb Hlt)).
  - (* eq 支：等式替换升 le *)
    exact (real_eq_le_bridge (real_log a Ha) (real_log b Hb)
             (real_log_wd a b Ha Hb Heq)).
Qed.

(* ========== 直用形态：Z ≤ 1 ⟹ log Z ≤ 0（HlogZ 前提消解） ========== *)
Lemma real_log_le_zero_of_le_one : forall (Z : Real) (HZ : real_lt real_zero Z),
  real_le Z real_one -> real_le (real_log Z HZ) real_zero.
Proof.
  intros Z HZ HZ1.
  assert (Hone : real_lt real_zero real_one).
  { exact real_lt_zero_one. }
  apply (real_le_trans _ (real_log real_one Hone) _).
  - exact (real_log_le_mono Z real_one HZ Hone HZ1).
  - (* real_log one == 0 经 eq 桥升 le *)
    exact (real_eq_le_bridge (real_log real_one Hone) real_zero
             (real_log_one Hone)).
Qed.

(* 提取检验 *)

(* ============================================================ *)
(* 块 26 · UpFEP：attention = 变分自由能唯一最小点 *)
(*   attention_minimizes_free_energy_unique（FEP 闭   *)
(*   环）+ bs_kernel_row_is_softmax_temp（行视图，论文 2 §10.2    *)
(*   点名件）；源：UpFEP.v（上游）；零公理面、零承认件；5 Qed                                      *)
(* ============================================================ *)
(* ============================================================ *)
(* UpFEP.v —— 二轮增量批·P5：attention = 变分自由能的唯一最小点      *)
(*            + 行视图引理（bs_kernel 行 = 单查询 softmax_temp）      *)
(*                                                                *)
(* P5（FEP × Gibbs 桥闭合，纯组装）：以 base_loss := −z、D := T      *)
(*   实例化自由能-KL 分解三件套（free_energy_kl_decomp/             *)
(*   min_free_energy_is_boltzmann/free_energy_min_unique，对        *)
(*   base_loss/D/Z 全泛化），配对齐引理（boltzmann 因子 = softmax    *)
(*   分子，经 opp_mult_l）与 F 外延引理，得：                       *)
(*   softmax_temp z 是 F_T[p] = −E_p[z] + T·Σ p log p 的唯一最小点。  *)
(*   把论文 2 §5.4(b) 的「attention 侧自由能最小化」从 interpretation *)
(*   升格为机器检查定理；§9.1 统一视角补上 FEP-attention 缺环。       *)
(* 行视图：AttnDoeblin 的行 softmax 核 bs_kernel 的每一行与论文      *)
(*   §5.2 的单查询 softmax_temp 是同一对象（经 expf 与 exp_pos_fn    *)
(*   的一致性前提）——论文 2 §10.2 点名的对接件。                     *)
(* 纪律：零公理面、零承认件；Set 层语句；全 Qed。                    *)
(* ============================================================ *)


(* ################ Part 1：P5 FEP 闭环 ################ *)

(* ToyR 系替换定理假设面查证 *)
Print Assumptions b5d1_Heps4.
Print Assumptions b5dE_zero_le_one.
