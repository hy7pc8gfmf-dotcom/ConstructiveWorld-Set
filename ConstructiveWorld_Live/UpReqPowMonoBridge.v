(* 五字段指针｜使命：本件定理／引理声明面所述性质的形式化。 依赖：件内 Require 声明面所列库件。 构造性：零承认式语句（机械核验）。 编译配方：coqc -native-compiler no -q -Q . ""。  ============================================================ *)
(* UpReqPowMonoBridge.v *)
(* 目的： le_b 乘法保序闭包（非负右因子版）合成器。 *)
(* 主件： x3d_le_b_mult_r_nonneg_or / x3d_le_b_mult_l_nonneg_or 与 x3d_le_b_mult_r_pos。 *)
(* 依赖： CW_ConstructiveWorld_219、UpRealLeB、UpRealLeB2、UpRealLeB3。 *)
(* 备注： 零上界的纯 B 形因子版仍为显式假设（见尾注）；本件为有界闭包的定理化。 *)
(* ============================================================ *)
(* X3d：任务说明源 = UpReqGeomIter.v 尾注【结论 I4｜PowB 幂单调衔接差距】：            *)
(*   「t ≤ t1 ⟹ KL_{t1} ≤_B κ^t·KL_0」合成链 ①主件 B 伴件 ②KL_0 非负伴件               *)
(*   ③powb_one_minus_eta_mono_dec 皆已绿，缺④「le_b 乘法保序闭包：a ≤_B b ∧ 0 ≤_B c     *)
(*   ⟹ a·c ≤_B b·c」——本件补④的合成器族。难度定位：④的逐 eps 证卡在「把严格序乘上      *)
(*   仅 B 形已知的因子 c」一步——B 形 0 ≤_B c 不给 Or 形 0≤c（两者构造性可分，单向桥       *)
(*   x3d_le_nonneg_or_to_b）。强度三面：主面走 real_le_closure_b_nonneg（UpRealLeB2      *)
(*   F.1 非负系数完成器，Or 形 0≤C 即可反用）＋ Or 形乘法单调三件套（S07：                 *)
(*   real_le_mult_compat_weak 非负右/real_le_mult_compat_r 非负左/                        *)
(*   RealSetoid.real_lt_le_iff_req lt 转 Or）。六件清单：件0 x3d_e0_key_lt（逆元压缩       *)
(*   严格界子件 (w·inv(D))·M < w，件5 的 δ 乘出压回引擎，亦独立可复用）；件1                *)
(*   x3d_le_b_mult_r_nonneg_or（Or 形 0≤c ⟹ a·c ≤_B b·c，主合成器）；件2                    *)
(*   x3d_le_b_mult_l_nonneg_or（左因子形 c·a ≤_B c·b，comm 双运输）；件3                    *)
(*   x3d_le_b_mult_r_pos（严格因子对照形，UpRealLeB3 件6 原证零重证）；件4                  *)
(*   x3d_le_nonneg_or_to_b（非负证书 Or⟹B 单向桥，接口面说明件）；件5                       *)
(*   x3d_le_b_mult_r_nonneg_bnd（有界版：a ≤_B b ∧ 0≤c ∧ c≤M ⟹ a·c ≤_B b·c，逐 eps 直证      *)
(*   e₀:=eps·inv(M+1) 压回——结论 I4 定理化）。对接位（使用式验证件 _x3d_I4BridgeCheck，      *)
(*   临时件不落正式树）：geodi_policy_iter_kl_geom_iter_B（①）＋件1（④）＋                 *)
(*   powb_one_minus_eta_mono_dec（③）经 real_le_b_trans 合成 I4 链。红线自检：零未闭合      *)
(*   证明（全 Qed）；零新依赖面；语句面全 Set 值；纯 term-mode 组装；禁词全零。编译配方：    *)
(*   vo 树前置 -Q（EMPTY 处实为空串实参），cpu_guard 包装零裸调（CoreN 2），先 -vos 秒审    *)
(*   再全量。                                                                              *)
(* ============================================================ *)

From Stdlib Require Import PeanoNat.
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
Require Import UpRealLeB.
Require Import UpRealLeB2.
Require Import UpRealLeB3.

(* ============================================================ *)
(* 〇、逆元压缩严格界子件                                                 *)
(* ============================================================ *)

(* 件0：(w·inv(D))·M < w，前提 M<D、D>0、w>0。
   链：inv(D)·M < inv(D)·D==1（严格乘法保序两跳）
   ⟹ w·(inv(D)·M) < w·1==w（左因子 w>0 严格保序）⟹ assoc 换形完成。 *)
Lemma x3d_e0_key_lt : forall (w M : Real)
    (HMlt1 : real_lt M (real_plus M real_one))
    (HMp : real_lt real_zero (real_plus M real_one))
    (Hw : real_lt real_zero w),
  real_lt
    (real_mult (real_mult w (real_inv_pos (real_plus M real_one) HMp)) M)
    w.
Proof.
  intros w M HMlt1 HMp Hw.
  assert (HiD : real_lt real_zero
                  (real_inv_pos (real_plus M real_one) HMp))
    by exact (real_inv_pos_pos (real_plus M real_one) HMp).
  (* 跳1：M·inv(D) < (M+1)·inv(D)（M<M+1、inv(D)>0）经 comm 换形 *)
  assert (Hs1 : real_lt (real_mult (real_inv_pos (real_plus M real_one) HMp) M)
                  (real_mult (real_inv_pos (real_plus M real_one) HMp)
                     (real_plus M real_one))).
  { exact (RealSetoid.real_lt_compat
             (real_mult M (real_inv_pos (real_plus M real_one) HMp))
             (real_mult (real_inv_pos (real_plus M real_one) HMp) M)
             (real_mult (real_plus M real_one)
                (real_inv_pos (real_plus M real_one) HMp))
             (real_mult (real_inv_pos (real_plus M real_one) HMp)
                (real_plus M real_one))
             (real_mult_comm M (real_inv_pos (real_plus M real_one) HMp))
             (real_mult_comm (real_plus M real_one)
                (real_inv_pos (real_plus M real_one) HMp))
             (real_mult_lt_compat M (real_plus M real_one)
                (real_inv_pos (real_plus M real_one) HMp) HMlt1 HiD)). }
  (* 跳2：右端 inv(D)·(M+1)==1 归一（先 comm 至 D·inv(D) 形再归一），
     得 inv(D)·M < 1 *)
  assert (Hs2 : real_lt (real_mult (real_inv_pos (real_plus M real_one) HMp) M)
                  real_one).
  { exact (RealSetoid.real_lt_id_r
             (real_mult (real_inv_pos (real_plus M real_one) HMp) M)
             (real_mult (real_inv_pos (real_plus M real_one) HMp)
                (real_plus M real_one))
             real_one
             (real_eq_trans
                (real_mult (real_inv_pos (real_plus M real_one) HMp)
                   (real_plus M real_one))
                (real_mult (real_plus M real_one)
                   (real_inv_pos (real_plus M real_one) HMp))
                real_one
                (real_mult_comm (real_inv_pos (real_plus M real_one) HMp)
                   (real_plus M real_one))
                (real_inv_pos_correct (real_plus M real_one) HMp))
             Hs1). }
  (* 跳3：左乘 w>0 严格保序，w·(inv(D)·M) < w·1 *)
  assert (Hs3 : real_lt (real_mult w
                   (real_mult (real_inv_pos (real_plus M real_one) HMp) M))
                  (real_mult w real_one))
    by exact (real_mult_lt_compat_l
                (real_mult (real_inv_pos (real_plus M real_one) HMp) M)
                real_one w Hs2 Hw).
  (* assoc 换形 + w·1==w 归一完成 *)
  exact (RealSetoid.real_lt_id_l
           (real_mult (real_mult w
              (real_inv_pos (real_plus M real_one) HMp)) M)
           (real_mult w
              (real_mult (real_inv_pos (real_plus M real_one) HMp) M))
           w
           (real_eq_sym _ _
              (real_mult_assoc w
                 (real_inv_pos (real_plus M real_one) HMp) M))
           (RealSetoid.real_lt_id_r
              (real_mult w
                 (real_mult (real_inv_pos (real_plus M real_one) HMp) M))
              (real_mult w real_one) w (real_mult_one w) Hs3)).
Qed.

(* ============================================================ *)
(* 一、主合成器：Or 形非负右因子的 le_b 乘法保序                          *)
(* ============================================================ *)

(* 件1：a ≤_B b 且 0≤c（Or 形）给 a·c ≤_B b·c。
   完成器反用（C:=c，Or 形非负即可）：给 e>0 只需 Or 形 a·c ≤ b·c+c·e——
   a<b+e 经 lt 转 Or 与非负右因子弱单调 ⟹ a·c ≤ (b+e)·c，
   再 (b+e)·c==b·c+c·e 分配换形完成。 *)
Lemma x3d_le_b_mult_r_nonneg_or : forall a b c : Real,
  real_le_b a b -> real_le real_zero c ->
  real_le_b (real_mult a c) (real_mult b c).
Proof.
  intros a b c H Hc.
  apply (real_le_closure_b_nonneg (real_mult a c) (real_mult b c) c Hc).
  intros eps Heps. unfold real_le.
  assert (Hdist : real_eq (real_mult (real_plus b eps) c)
                    (real_plus (real_mult b c) (real_mult c eps))).
  { apply (real_eq_trans _ (real_mult c (real_plus b eps)) _).
    - apply real_mult_comm.
    - apply (real_eq_trans _
               (real_plus (real_mult c b) (real_mult c eps)) _).
      + apply real_distrib.
      + apply (RealSetoid.real_eq_plus_compat (real_mult c b)
                 (real_mult c eps) (real_mult b c) (real_mult c eps)).
        * apply real_mult_comm.
        * apply real_eq_refl. }
  exact (RealSetoid.real_le_id_r (real_mult a c)
           (real_mult (real_plus b eps) c)
           (real_plus (real_mult b c) (real_mult c eps))
           Hdist
           (real_le_mult_compat_weak a (real_plus b eps) c Hc
              (RealSetoid.real_lt_le_iff_req a (real_plus b eps)
                 (inl (H eps Heps))))).
Qed.

(* 件2：左因子形（c·a ≤_B c·b 方向），comm 双运输平移件1 *)
Lemma x3d_le_b_mult_l_nonneg_or : forall a b c : Real,
  real_le_b a b -> real_le real_zero c ->
  real_le_b (real_mult c a) (real_mult c b).
Proof.
  intros a b c H Hc.
  apply (leb3_le_b_eq_l (real_mult a c) (real_mult c a) (real_mult c b)).
  - apply real_mult_comm.
  - apply (leb3_le_b_eq_r (real_mult a c) (real_mult b c) (real_mult c b)).
    + exact (x3d_le_b_mult_r_nonneg_or a b c H Hc).
    + apply real_mult_comm.
Qed.

(* ============================================================ *)
(* 二、对照锚与接口面说明件                                               *)
(* ============================================================ *)

(* 件3：严格因子对照形（0<c 版）：UpRealLeB3 件6 leb3_le_b_pos_scale
   签名对齐别名（原证零重证；本件三面对照的「严格面」锚）。 *)
Lemma x3d_le_b_mult_r_pos : forall a b c : Real,
  real_le_b a b -> real_lt real_zero c ->
  real_le_b (real_mult a c) (real_mult b c).
Proof.
  intros a b c H Hc.
  exact (leb3_le_b_pos_scale a b c H Hc).
Qed.

(* 件4：非负证书单向桥：Or 形 0≤c 给 B 形 0 ≤_B c。
   反向（B⟹Or）构造性不可通——④的因子若仅 B 形已知，本桥不通，
   即结论 I4 显式假设的精确位置（件5 以有界上界 M 绕行，见下）。 *)
Lemma x3d_le_nonneg_or_to_b : forall c : Real,
  real_le real_zero c -> real_le_b real_zero c.
Proof.
  intro c. apply real_le_to_le_b.
Qed.

(* ============================================================ *)
(* 三、有界非负右因子版（结论 I4「上界材料」条件的定理化）                  *)
(*   a ≤_B b ∧ 0≤c ∧ c≤M ⟹ a·c ≤_B b·c：逐 eps 直证，                     *)
(*   见证 e₀:=eps·inv(M+1)：a<b+e₀ 乘出后 e₀·c ≤ e₀·M < eps               *)
(*   （件0 引擎）——δ 乘出压回 eps。                                       *)
(* ============================================================ *)
Lemma x3d_le_b_mult_r_nonneg_bnd : forall a b c M : Real,
  real_le_b a b -> real_le real_zero c -> real_le c M ->
  real_le_b (real_mult a c) (real_mult b c).
Proof.
  intros a b c M H Hc0 HCm. unfold real_le_b. intros eps Heps.
  assert (HMle0 : real_le real_zero M)
    by exact (real_le_trans real_zero c M Hc0 HCm).
  assert (HMlt1 : real_lt M (real_plus M real_one)).
  { apply (RealSetoid.real_lt_id_l M (real_plus M real_zero)
             (real_plus M real_one)).
    - apply real_eq_sym. apply real_plus_zero.
    - apply (real_lt_plus_translate M real_zero real_one).
      exact real_lt_zero_one. }
  assert (HMp : real_lt real_zero (real_plus M real_one)).
  { apply (real_lt_le_trans real_zero real_one (real_plus M real_one)
             real_lt_zero_one).
    apply (RealSetoid.real_le_id_l real_one (real_plus real_zero real_one)
             (real_plus M real_one)).
    - apply real_eq_sym. apply real_plus_comm.
    - apply (real_le_plus_compat real_zero M real_one real_one).
      + exact HMle0.
      + apply real_le_refl. }
  (* 见证 e₀ := eps·inv(M+1) > 0 与件0 关键界 e₀·M < eps *)
  assert (HinvMp : real_lt real_zero
    (real_inv_pos (real_plus M real_one) HMp))
    by exact (real_inv_pos_pos (real_plus M real_one) HMp).
  assert (He0pos : real_lt real_zero
    (real_mult eps (real_inv_pos (real_plus M real_one) HMp)))
    by exact (real_mult_positive eps
                (real_inv_pos (real_plus M real_one) HMp) Heps HinvMp).
  assert (Hkey : real_lt
    (real_mult (real_mult eps (real_inv_pos (real_plus M real_one) HMp)) M)
    eps)
    by exact (x3d_e0_key_lt eps M HMlt1 HMp Heps).
  (* Or 形链：a ≤ b+e₀ ⟹ a·c ≤ (b+e₀)·c（非负右因子弱单调） *)
  assert (Hmono1 : real_le (real_mult a c)
                     (real_mult (real_plus b
                        (real_mult eps
                           (real_inv_pos (real_plus M real_one) HMp))) c))
    by exact (real_le_mult_compat_weak a
                (real_plus b
                   (real_mult eps
                      (real_inv_pos (real_plus M real_one) HMp))) c Hc0
                (RealSetoid.real_lt_le_iff_req a
                   (real_plus b
                      (real_mult eps
                         (real_inv_pos (real_plus M real_one) HMp)))
                   (inl (H (real_mult eps
                          (real_inv_pos (real_plus M real_one) HMp))
                          He0pos)))).
  (* 分配换形：(b+e₀)·c == b·c + e₀·c（comm→左分配→compat 换序） *)
  assert (Hdist : real_eq
    (real_mult (real_plus b
       (real_mult eps (real_inv_pos (real_plus M real_one) HMp))) c)
    (real_plus (real_mult b c)
       (real_mult (real_mult eps
          (real_inv_pos (real_plus M real_one) HMp)) c))).
  { apply (real_eq_trans _
             (real_mult c
                (real_plus b
                   (real_mult eps
                      (real_inv_pos (real_plus M real_one) HMp)))) _).
    - apply real_mult_comm.
    - apply (real_eq_trans _
               (real_plus (real_mult c b)
                  (real_mult c
                     (real_mult eps
                        (real_inv_pos (real_plus M real_one) HMp)))) _).
      + apply real_distrib.
      + apply (RealSetoid.real_eq_plus_compat (real_mult c b)
                 (real_mult c
                    (real_mult eps
                       (real_inv_pos (real_plus M real_one) HMp)))
                 (real_mult b c)
                 (real_mult (real_mult eps
                    (real_inv_pos (real_plus M real_one) HMp)) c)).
        * apply real_mult_comm.
        * apply real_mult_comm. }
  assert (Hmid1 : real_le (real_mult a c)
    (real_plus (real_mult b c)
       (real_mult (real_mult eps
          (real_inv_pos (real_plus M real_one) HMp)) c)))
    by exact (RealSetoid.real_le_id_r (real_mult a c) _ _ Hdist Hmono1).
  (* e₀·c ≤ e₀·M（非负左因子单调：e₀>0、c≤M） *)
  assert (Hmono2 : real_le
    (real_mult (real_mult eps (real_inv_pos (real_plus M real_one) HMp)) c)
    (real_mult (real_mult eps (real_inv_pos (real_plus M real_one) HMp)) M))
    by exact (real_le_mult_compat_r
                (real_mult eps (real_inv_pos (real_plus M real_one) HMp))
                c M
                (RealSetoid.real_lt_le_iff_req real_zero _
                   (inl He0pos)) HCm).
  assert (Hmid2 : real_le
    (real_plus (real_mult b c)
       (real_mult (real_mult eps
          (real_inv_pos (real_plus M real_one) HMp)) c))
    (real_plus (real_mult b c)
       (real_mult (real_mult eps
          (real_inv_pos (real_plus M real_one) HMp)) M)))
    by exact (real_le_plus_compat (real_mult b c) (real_mult b c) _ _
                (real_le_refl (real_mult b c)) Hmono2).
  assert (Hmid3 : real_le (real_mult a c)
    (real_plus (real_mult b c)
       (real_mult (real_mult eps
          (real_inv_pos (real_plus M real_one) HMp)) M)))
    by exact (real_le_trans _ _ _ Hmid1 Hmid2).
  exact (real_le_lt_trans _ _
           (real_plus (real_mult b c) eps) Hmid3
           (real_lt_plus_translate (real_mult b c) _
             eps Hkey)).
Qed.

(* ============================================================ *)
(* 四、假设审计（全件 Closed，证据在编译日志）                             *)
(* ============================================================ *)

Print Assumptions x3d_e0_key_lt.
Print Assumptions x3d_le_b_mult_r_nonneg_or.
Print Assumptions x3d_le_b_mult_l_nonneg_or.
Print Assumptions x3d_le_b_mult_r_pos.
Print Assumptions x3d_le_nonneg_or_to_b.
Print Assumptions x3d_le_b_mult_r_nonneg_bnd.

(* ============================================================ *)
(* 尾注：诚实登记表                                                        *)

(*   「B 形因子＋上界面」（件5，结论所指上界材料的定理化）；③powb 单调、  *)
(*   ①② GeomIter 伴件的合成闭环在使用式验证件 _x3d_I4BridgeCheck.v       *)
(*   完成：Hkl0or（Or 形 KL_0 非负证书）在位时「t ≤ t1 ⟹ KL_{t1} ≤_B     *)
(*   κ^t·KL_0」全闭合。零上界且因子仅 B 形已知的④仍显式假设——卡点即          *)
(*   B⟹Or 转换位（件4 反向），禁特设构造（分层保底纪律）。                    *)
(* ============================================================ *)
