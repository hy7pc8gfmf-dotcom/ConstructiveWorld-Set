(* ===================================================================== *)
(*  u5c_ln2_gap2_bridge.v —— ln2 供给链缺口乙：真族↔规范对改接桥          *)
(*  使命：把真族线值承载面（I : nat -> Real，规格形 lns_Ibreal 形）上的线值下/上界对，沿 *)
(*    恒等式肢 real_eq 的衔接缝（lnb3_conv_slot 经 docks 级联后的形态）改接到规范分子对    *)
(*    A B : nat -> Z 的 ln2b_line 面，并与三头肢（θ<1、0<|A_n|、0<clo_n）汇合，产出五层供给  *)
(*    接口（规格形态 2＝Ln2Bridge.v:63 ln2i_pade_supply 的逐字复刻面，X 参数化）的 inhabited  *)
(*    见证。本件与缺口甲（卷积/二项式幂系数基建，并行件 u5c_ln2_gap1_convbinom）完全独立：    *)
(*    零使用 lng_* 与 abl_ln2_qpoly_gen 任何语句。 *)
(*  依赖：池内已绿件：S01_BaseRing S02_CauchyComplete S03_QExp UpReqBanachNormOpp           *)
(*    UpReqIrrationalCriterion；Stdlib：QArith Qabs ZArith Arith Lia Setoid Qfield。 *)
(*  对标：勘察形态 2（Ln2Bridge.v:63 ln2i_pade_supply＝本件输出面）；                       *)
(*    abl_ln2_assembly2.v:347 lnb3_conv_slot（＝衔接缝假设位原面）；                        *)
(*    abl_ln2_assembly.v lna_supply_rem'_assemble（规范面两肢先行位，本件把前提面后退到真族  *)
(*    承载面并为五肢装配形）。 *)
(*  构造性注记：语句面全 Set 层（sigT/And/Or/QeqT/QltT/real_le/real_lt/real_eq）；主件证体＝  *)
(*    六肢 And 解构＋sigT 四层填充＋沿衔接缝 real_eq 的 real_le 两侧迁移（Or 两支分情形）；    *)
(*    传递肢为分情形实质推导；Q 层锚组为数值判定件（辅助面豁免）。零承认、零经典逻辑。 *)
(*  诚实面（规格形承载申报）：语句面按规格形态复刻并以 Observable 参数位承载链件（A B clo th I X *)
(*    全显式参数），留待后续装配逐位代入闭合（lna_Amod/lna_Bmod/lna_clo_mod/lna_theta_mod/    *)
(*    lns_Ibreal lnb2_cauchy/lnb3_Ibreal_lineL_bridge/lna_supply_pair_dock 逐位代入即得       *)
(*    ln2i_pade_supply 原面 inhabited）。 *)
(*    接口假设位清单（待消解项，非全局假设，Print Assumptions 仍 Closed）：                   *)
(*    ① 衔接缝肢 Hw：∀n, real_eq (I n) (线 X A B n)——恒等式肢 real_eq（在案存量件             *)
(*       lnb3_conv_slot 的级联形态）； *)
(*    ② 真族面界对 Hlo/Hup：clo_n ≤ I n ≤ θⁿ——其下界肢依赖缺口 cloₙ 下界 witness（I'ₙ 首项     *)
(*       正项导出，非本件范围），上界肢 θ 档衰减真族重述（lnb3_theta_slot 同内容位）；         *)
(*    ③ 三头肢 Hth/Hap/Hclo：θ<1、0<|A_n|、0<clo_n——在位见 lna_head_three_legs 三肢之逐位对应形。 *)
(*  编译配方：source Live/toolchain/env.sh && rocq c -native-compiler no -q -Q . "" 本件       *)
(*    （池根单飞；产物 .vo/.glob/.ml 落池内本文件名下）。 *)
(* ===================================================================== *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqBanachNormOpp.
Require Import UpReqIrrationalCriterion.
From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith
  Arith.Arith.
From Stdlib Require Import Lia Setoid Qfield.

Open Scope nat_scope.

(* ============================================================ *)
(* §0 规范供给面复刻（规格形态 2 逐字，X 参数化承载）                      *)
(* ============================================================ *)

(* 规范线对象：|A_n·X − B_n|（Ln2Bridge ln2b_line 复刻，X 显式参数） *)
Definition u5c_ln2b_line (X : Real) (A B : nat -> Z) (n : nat) : Real :=
  real_abs (real_plus (real_mult (real_const ((A n) # 1)%Q) X)
                      (real_opp (real_const ((B n) # 1)%Q))).

(* 下界肢定义面：clo_n ≤ |A_n·X − B_n|（real_le Or-编码） *)
Definition u5c_ln2b_line_lower (X : Real) (A B : nat -> Z) (clo : nat -> Q)
  : Set :=
  forall n : nat, real_le (real_const (clo n)) (u5c_ln2b_line X A B n).

(* 上界肢定义面：|A_n·X − B_n| ≤ θⁿ *)
Definition u5c_ln2b_line_upper (X : Real) (A B : nat -> Z) (th : Q) : Set :=
  forall n : nat, real_le (u5c_ln2b_line X A B n) (real_const (q_pow th n)).

(* 五层供给型（Ln2Bridge ln2i_pade_supply 复刻：①θ<1 ②0<|A_n| ③0<clo_n
   ④下界肢 ⑤上界肢，A B clo th 全显式 sigT 层） *)
Definition u5c_ln2i_pade_supply (X : Real) : Set :=
  sigT (fun A : nat -> Z =>
    sigT (fun B : nat -> Z =>
      sigT (fun clo : nat -> Q =>
        sigT (fun th : Q =>
          And (QltT th (1 # 1))
            (And (forall n : nat, QltT 0 (Qabs ((A n) # 1)))
              (And (forall n : nat, QltT 0 (clo n))
                (And (u5c_ln2b_line_lower X A B clo)
                     (u5c_ln2b_line_upper X A B th)))))))).

(* ============================================================ *)
(* §1 改接传递肢（real_le 沿 real_eq 两侧迁移；Q 层换算辅助）               *)
(* ============================================================ *)

(* 左侧迁移：x ≤ y 且 x ≈ z ⟹ z ≤ y（Or 两支分情形） *)
Lemma gap2_le_eq_l : forall x y z : Real,
  real_le x y -> real_eq x z -> real_le z y.
Proof.
  intros x y z Hle Heq. destruct Hle as [Hlt | Heqxy].
  - exact (inl (real_eq_lt_lt z x y (real_eq_sym x z Heq) Hlt)).
  - exact (inr (real_eq_trans z x y (real_eq_sym x z Heq) Heqxy)).
Qed.

(* 右侧迁移：x ≤ y 且 y ≈ z ⟹ x ≤ z（Or 两支分情形） *)
Lemma gap2_le_eq_r : forall x y z : Real,
  real_le x y -> real_eq y z -> real_le x z.
Proof.
  intros x y z Hle Heq. destruct Hle as [Hlt | Heqxy].
  - exact (inl (real_lt_eq_lt x y z Hlt Heq)).
  - exact (inr (real_eq_trans x y z Heqxy Heq)).
Qed.

(* QeqT 传递与左乘相容（Q 层换算） *)
Lemma gap2_qeqT_trans : forall a b c : Q, QeqT a b -> QeqT b c -> QeqT a c.
Proof.
  intros a b c H1 H2. apply qeq_imp_qeqT.
  apply (Qeq_trans a b c).
  - apply qeqT_imp_qeq. exact H1.
  - apply qeqT_imp_qeq. exact H2.
Qed.

Lemma gap2_qeqT_mult_l : forall c a b : Q, QeqT a b -> QeqT (c * a) (c * b).
Proof.
  intros c a b H. apply qeq_imp_qeqT.
  setoid_rewrite (qeqT_imp_qeq a b H). apply Qeq_refl.
Qed.

(* 头肢②面迁移：|a|>0 沿 QeqT 迁到 b（规范 A 面换算肢的 Q 层核） *)
Lemma gap2_abs_pos_transfer : forall a b : Q,
  QeqT a b -> QltT 0 (Qabs a) -> QltT 0 (Qabs b).
Proof.
  intros a b Heq Hpos.
  assert (Habs : (Qabs a == Qabs b)%Q).
  { apply Qabs_wd. apply qeqT_imp_qeq. exact Heq. }
  assert (Hcmp : Qcompare 0%Q (Qabs a) = Qcompare 0%Q (Qabs b)).
  { apply (Qcompare_comp 0%Q 0%Q); [apply Qeq_refl | exact Habs]. }
  unfold QltT, Qlt_bool in *. rewrite <- Hcmp. exact Hpos.
Qed.

(* 锚组：θ=4/5<1（在位 lna_theta_mod 取值的 Q 层见证，三头肢①原值） *)
Theorem gap2_theta_45_lt1 : QltT (4 # 5)%Q (1 # 1)%Q.
Proof. apply Qlt_to_QltT. unfold Qlt. cbn [Qnum Qden]. lia. Qed.

(* ============================================================ *)
(* §2 接口假设位与改接主件                                                *)
(* ============================================================ *)

(* 接口假设位总形（六肢 And，全 Observable 显式参数位）：
   Hth/Hap/Hclo＝三头肢；Hw＝衔接缝肢（真族线值承载面 I 与规范线对象的
   real_eq 族形，规格形 lnb3_conv_slot 沿 docks 级联后的形态）；
   Hlo/Hup＝真族面下/上界对（缺口件③与 θ 参数位的使用位） *)
Definition u5c_gap2_slot (X : Real) (A B : nat -> Z) (clo : nat -> Q)
  (th : Q) (I : nat -> Real) : Set :=
  And (QltT th (1 # 1))
    (And (forall n : nat, QltT 0 (Qabs ((A n) # 1)))
      (And (forall n : nat, QltT 0 (clo n))
        (And (forall n : nat, real_eq (I n) (u5c_ln2b_line X A B n))
          (And (forall n : nat, real_le (real_const (clo n)) (I n))
               (forall n : nat, real_le (I n)
                                       (real_const (q_pow th n))))))).

(* 改接主件：接口假设位给定 ⟹ 五层供给 inhabited
   （④⑤两肢＝真族面界对沿衔接缝 real_eq 右迁移到规范线面；①②③肢逐位迁移） *)
Definition u5c_gap2_bridge (X : Real) (A B : nat -> Z) (clo : nat -> Q)
  (th : Q) (I : nat -> Real) (Hs : u5c_gap2_slot X A B clo th I)
  : u5c_ln2i_pade_supply X.
Proof.
  unfold u5c_ln2i_pade_supply, u5c_gap2_slot in *.
  destruct Hs as [Hth [Hap [Hclo [Hw [Hlo Hup]]]]].
  exists A. exists B. exists clo. exists th.
  split.
  - (* ① θ < 1 *)
    exact Hth.
  - split.
    + (* ② 0 < |A_n| *)
      exact Hap.
    + split.
      * (* ③ 0 < clo_n *)
        exact Hclo.
      * split.
        -- (* ④ 下界肢：clo_n ≤ |A_n·X − B_n|（Hlo 沿衔接缝右迁移） *)
           intro n.
           exact (gap2_le_eq_r (real_const (clo n)) (I n)
                    (u5c_ln2b_line X A B n) (Hlo n) (Hw n)).
        -- (* ⑤ 上界肢：|A_n·X − B_n| ≤ θⁿ（Hup 沿衔接缝左迁移） *)
           intro n.
           exact (gap2_le_eq_l (I n) (real_const (q_pow th n))
                    (u5c_ln2b_line X A B n) (Hup n) (Hw n)).
Defined.

(* 头肢②面迁移实例化：规范 A 面换算闭合（后续装配以 lna_Amod/Aface 位代入：
   gap2_abs_pos_transfer (Aface n#1) (Amod n#1) (面迁移 QeqT) 头肢②即得） *)
Theorem gap2_head2_rewire : forall (a b : Q),
  QeqT a b -> (forall n : nat, QltT 0 (Qabs a)) ->
  forall n : nat, QltT 0 (Qabs b).
Proof. intros a b Heq H n. exact (gap2_abs_pos_transfer a b Heq (H n)). Qed.

(* ============================================================ *)
(* 提取与假设审计（零承认复核）                                            *)
(* ============================================================ *)

Separate Extraction u5c_gap2_bridge gap2_le_eq_l gap2_le_eq_r.

Print Assumptions gap2_le_eq_l.
Print Assumptions gap2_le_eq_r.
Print Assumptions gap2_qeqT_trans.
Print Assumptions gap2_qeqT_mult_l.
Print Assumptions gap2_abs_pos_transfer.
Print Assumptions gap2_theta_45_lt1.
Print Assumptions gap2_head2_rewire.
Print Assumptions u5c_gap2_bridge.
