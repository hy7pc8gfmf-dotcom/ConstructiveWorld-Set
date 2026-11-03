(* 五字段指针｜使命：D4-S1「e-π 模量对照·对照主语句＋双侧 witness 换形」——对照
   主语句 lw4c_contrast_face（Set 面并置）＋双侧 witness 换形（lic 形→sigT 嵌套
   Set 面纯机械拆装，零数学新内容）。依赖：S01/S02/S03 基础层与判据面。             
   PiEnvelope、SumInvFactEscape 等。材料源：UpReqIrrationalCriterion        
   (lic_witness_e :723【M】)、LW0MLicBridge (lw0m_e :16/lw0m_xL :20)、LW0LeibWindow
   (:941 认证同形)、PiEnvelope (S2 后续预留)。构造性：零承认式语句；语句面全 Set 层
   （sigT 嵌套＝:941 认证同形；And＝S01 :46 A×B Set 值）；π 侧供件只立名不构造，
   (b) 依赖收拢于 lw4c_pi_lic_face 供件缺位，候 585 β 定理 S5/S6（零伪造）。纪律：
   禁Lra/Reals；提取＋PA 验 Obj.magic=0。编译配方：9.1直调。   *)
From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith.
From Stdlib Require Import Extraction.
Require Import S01_BaseRing.        (* Set 层逻辑件：And :46【M】(A×B 面)/NatLe :88【M】 *)
Require Import S02_CauchyComplete.  (* QltT :48【M】/Real/real_metric *)
Require Import S03_QExp.            (* q_fact :43【T】/exp_series :788【T】 *)
Require Import SumInvFactEscape.    (* sif 逃逸机件（lic_witness_e 证明体依赖随件） *)
Require Import LW0LeibWindow.       (* leiblw_Id/Qltb 砖/形态分离族——S2 预留＋备案 B 面 *)
Require Import PiEnvelope.          (* pie_mag 系——S2 后续预留；S1 面零消费名 *)
Require Import LW0MLicBridge.       (* lw0m_e :16/lw0m_xL :20 *)
Require Import UpReqIrrationalCriterion.  (* lic_witness_e :723【M】/lic_escape_window :242【M】 *)

(* ============================================================ *)
(* §1 模量记录（对照对象面）                                      *)
(* ============================================================ *)
(* e 侧窗＝1/n!（阶乘衰减）。逐 token 同 lic_witness_e 第二参 lambda
   （:723-724【M】）——exact 使用零转换缺口（594 细化：581 稿 (1#1) 形
   改 1%Q 形，语义同分、转换风险归零） *)
Definition lw4c_e_win (n : nat) : Q := 1%Q / q_fact n.

(* π 侧窗＝5·pie_mag n＝5/(2n+1)（调和衰减）。lw0m_e 不透明直代 *)
Definition lw4c_pi_win (n : nat) : Q := lw0m_e n.

(* 模量并置记录：A×B 逐字（红线②）；prod 双参 (nat->Q):Set，零 Prop 位 *)
Definition lw4c_modulus_pair : prod (nat -> Q) (nat -> Q) :=
  pair lw4c_e_win lw4c_pi_win.

(* ============================================================ *)
(* §2 e 侧支（lic_witness_e 换形随件）——语句面＝LW0LeibWindow :941
   认证同形：sigT 嵌套＋Prop 守卫位＋Set 值序判定（QltT＝S02 :48【M】） *)
(* ============================================================ *)
Definition lw4c_e_escape (q : Q) : Set :=
  sigT (fun n : nat =>
    sigT (fun _ : (1 <= n)%nat =>
      QltT (lw4c_e_win n) (Qabs ((q - exp_series n 1)%Q)))).

Lemma lw4c_e_escape_supply : forall q : Q, lw4c_e_escape q.
Proof.
  intro q.
  destruct (lic_witness_e q) as [n [Hn1 Hlt]].
  exists n. exists Hn1. exact Hlt.
Qed.
(* 换形逐 token 对照＝§五.二处方表；exact 若因转换停摆，插入
   `unfold lw4c_e_win.` 于 exact 前一行（预案，禁其他改动）。 *)

(* ============================================================ *)
(* §2' e 侧 lic 形直承面（换形第 0 步：定义性零证直代）
   ——检验①⑤放行前提；如环境拒承：删本段两件、以 §2 面为准，
   备案 B 切换零级联（§2 面不依赖 §2'）                            *)
(* ============================================================ *)
Definition lw4c_e_lic_face : Set :=
  lic_escape_window (fun n => exp_series n 1) lw4c_e_win.
Definition lw4c_e_lic_supply : lw4c_e_lic_face := lic_witness_e.

(* ============================================================ *)
(* §3 π 侧支（LIC 窗形，与 e 侧同构；供件＝(b) 随件，本切片零构造
   ——占位件规格与零伪造护栏＝§六）                                *)
(* ============================================================ *)
Definition lw4c_pi_escape (q : Q) : Set :=
  sigT (fun n : nat =>
    sigT (fun _ : (1 <= n)%nat =>
      QltT (lw4c_pi_win n) (Qabs ((q - lw0m_xL n)%Q)))).

Definition lw4c_pi_lic_face : Set :=
  lic_escape_window lw0m_xL lw4c_pi_win.

Lemma lw4c_pi_escape_of_lic :
  lw4c_pi_lic_face -> forall q : Q, lw4c_pi_escape q.
Proof.
  intro Hlic. intro q.
  destruct (Hlic q) as [n [Hn1 Hlt]].
  exists n. exists Hn1. exact Hlt.
Qed.
(* 纯 destruct 拆装引理：非 (b) 依赖（供件位假设化），本切片可闭合；
   此处源面与目标面 token 逐字同一（lic_escape_window lw0m_xL lw4c_pi_win
   展开体≡lw4c_pi_escape 体），exact 零转换。 *)

(* ============================================================ *)
(* §4 对照主语句＋参数化闭合                                      *)
(* ============================================================ *)
(* And＝S01 :46【M】Set 值 And（A×B 逐字，红线②）；两参各为
   `forall q : Q, …escape q`——Q:Set 上 Set 值全称，落 Set ✓。
   备案 B（检验⑤若判 And 位不可承 Type 级支）：改嵌套 sigT 面
   sigT (fun He : forall q, lw4c_e_escape q => forall q, lw4c_pi_escape q)
   （:941 同构先例零 And），证体改 intro Hlic. exists lw4c_e_escape_supply.
   exact (lw4c_pi_escape_of_lic Hlic). 零级联。 *)
Definition lw4c_contrast_face : Set :=
  And (forall q : Q, lw4c_e_escape q)
      (forall q : Q, lw4c_pi_escape q).

Theorem lw4c_contrast_param : lw4c_pi_lic_face -> lw4c_contrast_face.
Proof.
  intro Hlic. split.
  - exact lw4c_e_escape_supply.
  - exact (lw4c_pi_escape_of_lic Hlic).
Qed.
(* 左支在库直代（lic_witness_e 换形）；右支假设位承载——585 β 定理
   S5/S6 出闸后以闭式供件消去假设位，升格 lw4c_contrast（§6 注记区）。 *)

(* ============================================================ *)
(* §5 对照数值随件（在库承引，不重铸；vm_compute 判例落 S2）        *)
(* ============================================================ *)
Check leiblw_margin_tbl.
Check leiblw_natwin_tbl.

(* ============================================================ *)
(* §6 注记区（S2/(b) 后预留名——本切片零落，禁进编译面）            *)
(*   lw4c_shape_separation   ：S2 形态定理（引件 leiblw_family_separation
     :971、leiblw_nivwin_bounded :962、leiblw_natwin_unbounded :894；
     对照语义限「窗族形态」，581 §四.四/§五全款承引）
   lw4c_pi_lic_supply        ：(b) 供件（585 β 定理出闸随件，闭式 c(a,b)）
   lw4c_contrast             ：无条件升格
     := pair lw4c_e_escape_supply (lw4c_pi_escape_of_lic lw4c_pi_lic_supply)
   lw4c_pi_escape_of_b    ：(b) 定格接口换形引理（待 (b) 闭合出已证结论）   *)
(* ============================================================ *)

(* ============================================================ *)
(* §7 提取＋PA（关面；红线④）                                     *)
(* ============================================================ *)
Separate Extraction lw4c_modulus_pair lw4c_e_win lw4c_pi_win
  lw4c_e_escape lw4c_e_escape_supply lw4c_pi_escape
  lw4c_pi_escape_of_lic lw4c_contrast_face lw4c_contrast_param.
Print Assumptions lw4c_e_escape_supply.
Print Assumptions lw4c_contrast_param.
(* 目标：提取零 Obj.magic；PA 双发均 Closed under the global context。
   π 侧供件不存在（占位），不进提取值域、不进 PA 面。 *)


From Stdlib Require Import Lia.  (* nat/Z 域辅助算术；Q 域走显式链 *)

(* ============================================================ *)
(* §8 窗宽对照（S2；全 Set 层；零 (b)）                            *)
(* ============================================================ *)

(* A1a 阶乘恒 ≥ 1（归纳基座） *)
Lemma lw4c_qfact_ge_1 : forall n : nat, QleT' 1%Q (q_fact n).
Proof.
  intro n. apply Qle_to_QleT'. induction n as [| m IH]; simpl.
  - unfold Qle. simpl. lia.
  - apply (Qle_trans _ (1%Q * q_fact m)).
    + setoid_rewrite (Qmult_1_l (q_fact m)). exact IH.
    + apply (Qmult_le_compat_r 1%Q (Z.of_nat (Datatypes.S m) # 1)%Q (q_fact m)).
      * apply QleT'_to_Qle. apply (Qle_of_nat 1 (Datatypes.S m)). lia.
      * apply (Qlt_le_weak 0%Q (q_fact m)). apply QltT_to_Qlt. apply q_fact_pos.
Qed.

(* A1b 阶乘不小于序号：n ≥ 1 蕴含 n ≤ n!（A2/A3 的公共链砖） *)
Lemma lw4c_qfact_ge_nat : forall n : nat, (1 <= n)%nat ->
  QleT' ((Z.of_nat n) # 1)%Q (q_fact n).
Proof.
  intro n. induction n as [| m IH]; intro Hn; apply Qle_to_QleT'.
  - unfold Qle. simpl. lia.
  - pose proof (qeqT_imp_qeq _ _ (q_fact_succ m)) as Hfs. setoid_rewrite Hfs.
    setoid_rewrite (Qmult_comm (Z.of_nat (Datatypes.S m) # 1)%Q (q_fact m)).
    apply (Qle_trans _ (1%Q * (Z.of_nat (Datatypes.S m) # 1)%Q)).
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. symmetry. apply Qmult_1_l.
    + apply (Qmult_le_compat_r 1%Q (q_fact m) (Z.of_nat (Datatypes.S m) # 1)%Q).
      * exact (QleT'_to_Qle 1%Q (q_fact m) (lw4c_qfact_ge_1 m)).
      * apply QleT'_to_Qle. apply (Qle_of_nat 0 (Datatypes.S m)). lia.
Qed.

(* A2 逐点非严对照：n ≥ 1 蕴含 1/n! ≤ 5/(2n+1) *)
Lemma lw4c_e_win_le_pi_win : forall n : nat, (1 <= n)%nat ->
  QleT' (lw4c_e_win n) (lw4c_pi_win n).
Proof.
  intros n Hn. apply Qle_to_QleT'.
  unfold lw4c_e_win, lw4c_pi_win.
  setoid_replace (lw0m_e n) with ((5 # 1)%Q / (Z.of_nat (2 * n + 1) # 1)%Q).
  2: { unfold lw0m_e, pie_mag, Qdiv. ring. }
  apply QleT'_to_Qle. apply (q_le_div_le 1%Q (q_fact n) (5 # 1)%Q (Z.of_nat (2 * n + 1) # 1)%Q).
  - apply q_fact_pos.
  - apply (Qlt_of_nat_lt 0 (2 * n + 1)). lia.
  - apply Qle_to_QleT'. apply (Qle_trans _ ((5 # 1)%Q * (Z.of_nat n # 1))).
    + unfold Qle. cbn [Qnum Qden Qmult]. lia.
    + apply (Qle_trans _ ((Z.of_nat n # 1) * (5 # 1)%Q)).
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
      * apply (Qle_trans _ (q_fact n * (5 # 1)%Q)).
        -- apply (Qmult_le_compat_r (Z.of_nat n # 1) (q_fact n) (5 # 1)%Q).
           ++ exact (QleT'_to_Qle (Z.of_nat n # 1) (q_fact n) (lw4c_qfact_ge_nat n Hn)).
           ++ apply QleT'_to_Qle. apply (Qle_of_nat 0 5). lia.
        -- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
Qed.

(* A3 逐点严对照：n ≥ 2 蕴含 1/n! < 5/(2n+1)（阶乘压制强于调和率的逐点形）
   ——箭头位 Prop 前提＝leiblw_natwin_unbounded 认证先例形 *)
Lemma lw4c_e_win_lt_pi_win : forall n : nat, (2 <= n)%nat ->
  QltT (lw4c_e_win n) (lw4c_pi_win n).
Proof.
  intros n Hn. apply Qlt_to_QltT.
  assert (H1 : (1 <= n)%nat) by lia.
  unfold lw4c_e_win, lw4c_pi_win.
  setoid_replace (lw0m_e n) with ((5 # 1)%Q / (Z.of_nat (2 * n + 1) # 1)%Q).
  2: { unfold lw0m_e, pie_mag, Qdiv. ring. }
  apply (Qle_lt_trans _ ((4 # 1)%Q / (Z.of_nat (2 * n + 1) # 1)%Q)).
  - apply QleT'_to_Qle. apply (q_le_div_le 1%Q (q_fact n) (4 # 1)%Q (Z.of_nat (2 * n + 1) # 1)%Q).
    + apply q_fact_pos.
    + apply (Qlt_of_nat_lt 0 (2 * n + 1)). lia.
    + apply Qle_to_QleT'. apply (Qle_trans _ ((4 # 1)%Q * (Z.of_nat n # 1))).
      * unfold Qle. cbn [Qnum Qden Qmult]. lia.
      * apply (Qle_trans _ ((Z.of_nat n # 1) * (4 # 1)%Q)).
        -- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
        -- apply (Qle_trans _ (q_fact n * (4 # 1)%Q)).
           ++ apply (Qmult_le_compat_r (Z.of_nat n # 1) (q_fact n) (4 # 1)%Q).
              ** exact (QleT'_to_Qle (Z.of_nat n # 1) (q_fact n) (lw4c_qfact_ge_nat n H1)).
              ** apply QleT'_to_Qle. apply (Qle_of_nat 0 4). lia.
           ++ apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
  - unfold Qdiv.
    apply (Qmult_lt_compat_r _ _ (Qinv (Z.of_nat (2 * n + 1) # 1)%Q)).
    + apply (Qinv_lt_0_compat (Z.of_nat (2 * n + 1) # 1)%Q).
      unfold Qlt. simpl. lia.
    + apply QltT_to_Qlt. apply (Qlt_of_nat_lt 4 5). lia.
Qed.

(* A4 π 窗高于一切固定幂率窗：k ≥ 1, n ≥ 1 蕴含 1/(n+1)^k < 5/(2n+1)
   ——「π 窗幂率级压制」的构造性逐点反驳 *)
Definition lw4c_powwin (k n : nat) : Q :=
  1%Q / q_pow ((Z.of_nat (Datatypes.S n)) # 1)%Q k.
Lemma lw4c_pi_win_gt_powwin : forall k n : nat, (1 <= k)%nat -> (1 <= n)%nat ->
  QltT (lw4c_powwin k n) (lw4c_pi_win n).
Proof.
  intro k. intro n. intro Hk. intro Hn. apply Qlt_to_QltT.
  unfold lw4c_powwin, lw4c_pi_win.
  setoid_replace (lw0m_e n) with ((5 # 1)%Q / (Z.of_nat (2 * n + 1) # 1)%Q).
  2: { unfold lw0m_e, pie_mag, Qdiv. ring. }
  assert (Hpowpos : forall j : nat, Qlt 0 (q_pow (Z.of_nat (Datatypes.S n) # 1)%Q j)).
  { intro j. induction j as [| j IHj]; simpl.
    - unfold Qlt. simpl. lia.
    - apply (Qmult_lt_0_compat (Z.of_nat (Datatypes.S n) # 1)%Q
               (q_pow (Z.of_nat (Datatypes.S n) # 1)%Q j)).
      + apply QltT_to_Qlt. apply (Qlt_of_nat_lt 0 (Datatypes.S n)). lia.
      + exact IHj. }
  assert (Hpowge : forall j : nat, (1 <= j)%nat ->
    Qle (Z.of_nat (Datatypes.S n) # 1)%Q (q_pow (Z.of_nat (Datatypes.S n) # 1)%Q j)).
  { intro j. induction j as [| j IHj]; intro Hj.
    - exfalso. lia.
    - destruct j as [| j'].
      + pose proof (qeqT_imp_qeq _ _ (q_pow_succ (Z.of_nat (Datatypes.S n) # 1)%Q 0)) as Hps0.
        setoid_rewrite Hps0.
        assert (H0 : q_pow (Z.of_nat (Datatypes.S n) # 1)%Q 0 == 1%Q)
          by (simpl; reflexivity).
        rewrite H0. apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
      + pose proof (qeqT_imp_qeq _ _
            (q_pow_succ (Z.of_nat (Datatypes.S n) # 1)%Q (Datatypes.S j'))) as Hps1.
        setoid_rewrite Hps1.
        apply (Qle_trans _ ((Z.of_nat (Datatypes.S n) # 1)%Q * 1)%Q).
        * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
        * apply (Qle_trans _ (1%Q * q_pow (Z.of_nat (Datatypes.S n) # 1)%Q (Datatypes.S j'))).
          -- setoid_rewrite (Qmult_1_r (Z.of_nat (Datatypes.S n) # 1)%Q).
             setoid_rewrite (Qmult_1_l (q_pow (Z.of_nat (Datatypes.S n) # 1)%Q (Datatypes.S j'))).
             assert (H1 : (1 <= Datatypes.S j')%nat) by lia.
             exact (IHj H1).
          -- apply (Qmult_le_compat_r 1%Q (Z.of_nat (Datatypes.S n) # 1)%Q
                     (q_pow (Z.of_nat (Datatypes.S n) # 1)%Q (Datatypes.S j'))).
             ++ apply QleT'_to_Qle. apply (Qle_of_nat 1 (Datatypes.S n)). lia.
             ++ apply (Qlt_le_weak 0%Q
                        (q_pow (Z.of_nat (Datatypes.S n) # 1)%Q (Datatypes.S j'))).
                apply (Hpowpos (Datatypes.S j')). }
  apply (Qle_lt_trans _ ((4 # 1)%Q / (Z.of_nat (2 * n + 1) # 1)%Q)).
  - apply QleT'_to_Qle. apply (q_le_div_le 1%Q (q_pow (Z.of_nat (Datatypes.S n) # 1)%Q k) (4 # 1)%Q
             (Z.of_nat (2 * n + 1) # 1)%Q).
    + apply Qlt_to_QltT. exact (Hpowpos k).
    + apply (Qlt_of_nat_lt 0 (2 * n + 1)). lia.
    + apply Qle_to_QleT'. apply (Qle_trans _ ((4 # 1)%Q * (Z.of_nat (Datatypes.S n) # 1)%Q)).
      * unfold Qle. cbn [Qnum Qden Qmult]. lia.
      * apply (Qle_trans _ ((Z.of_nat (Datatypes.S n) # 1)%Q * (4 # 1)%Q)).
        -- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
        -- apply (Qle_trans _ (q_pow (Z.of_nat (Datatypes.S n) # 1)%Q k * (4 # 1)%Q)).
           ++ apply (Qmult_le_compat_r (Z.of_nat (Datatypes.S n) # 1)%Q
                       (q_pow (Z.of_nat (Datatypes.S n) # 1)%Q k) (4 # 1)%Q).
              ** apply (Hpowge k). exact Hk.
              ** apply QleT'_to_Qle. apply (Qle_of_nat 0 4). lia.
           ++ apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
  - unfold Qdiv.
    apply (Qmult_lt_compat_r _ _ (Qinv (Z.of_nat (2 * n + 1) # 1)%Q)).
    + apply (Qinv_lt_0_compat (Z.of_nat (2 * n + 1) # 1)%Q).
      apply QltT_to_Qlt. apply (Qlt_of_nat_lt 0 (2 * n + 1)). lia.
    + apply QltT_to_Qlt. apply (Qlt_of_nat_lt 4 5). lia.
Qed.

(* A5 阶乘窗不超指数率窗：∀m, 1/(S m)! ≤ 2^{-m}（nat 减法零出现形） *)
Lemma lw4c_e_win_le_expwin : forall m : nat,
  QleT' (lw4c_e_win (Datatypes.S m)) (1%Q / q_pow (2 # 1)%Q m).
Proof.
  intro m. apply Qle_to_QleT'. unfold lw4c_e_win.
  assert (Hpowpos : Qlt 0 (q_pow (2 # 1)%Q m)).
  { induction m as [| m IHm]; simpl.
    - unfold Qlt. simpl. lia.
    - apply (Qmult_lt_0_compat (2 # 1)%Q (q_pow (2 # 1)%Q m)).
      + exact (QltT_to_Qlt _ _ Q2_pos).
      + exact IHm. }
  assert (Hfact : Qle (q_pow (2 # 1)%Q m) (q_fact (Datatypes.S m))).
  { clear Hpowpos. induction m as [| m IHm].
    - simpl. unfold Qle. simpl. lia.
    - pose proof (qeqT_imp_qeq _ _ (q_pow_succ (2 # 1)%Q m)) as Hpsm.
      setoid_rewrite Hpsm.
      pose proof (qeqT_imp_qeq _ _ (q_fact_succ (Datatypes.S m))) as Hfsm.
      setoid_rewrite Hfsm.
      setoid_rewrite (Qmult_comm (2 # 1)%Q (q_pow (2 # 1)%Q m)).
      setoid_rewrite (Qmult_comm (Z.of_nat (Datatypes.S (Datatypes.S m)) # 1)%Q
                       (q_fact (Datatypes.S m))).
      apply (Qle_trans _ (q_fact (Datatypes.S m) * (2 # 1)%Q)).
      + apply (Qmult_le_compat_r (q_pow (2 # 1)%Q m) (q_fact (Datatypes.S m))
                 (2 # 1)%Q).
        * exact IHm.
        * apply QleT'_to_Qle. apply (Qle_of_nat 0 2). lia.
      + setoid_rewrite (Qmult_comm (q_fact (Datatypes.S m)) (2 # 1)%Q).
        setoid_rewrite (Qmult_comm (q_fact (Datatypes.S m))
                         (Z.of_nat (Datatypes.S (Datatypes.S m)) # 1)%Q).
        apply (Qmult_le_compat_r (2 # 1)%Q
                   (Z.of_nat (Datatypes.S (Datatypes.S m)) # 1)%Q
                   (q_fact (Datatypes.S m))).
        * apply QleT'_to_Qle. apply (Qle_of_nat 2 (Datatypes.S (Datatypes.S m))). lia.
        * apply (Qlt_le_weak 0%Q (q_fact (Datatypes.S m))). apply QltT_to_Qlt.
          apply q_fact_pos. }
  apply QleT'_to_Qle. apply (q_le_div_le 1%Q (q_fact (Datatypes.S m)) 1%Q (q_pow (2 # 1)%Q m)).
  - apply q_fact_pos.
  - apply Qlt_to_QltT. exact Hpowpos.
  - apply Qle_to_QleT'. apply (Qle_trans _ (1%Q * q_pow (2 # 1)%Q m)).
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
    + setoid_rewrite (Qmult_1_l (q_pow (2 # 1)%Q m)).
      setoid_rewrite (Qmult_1_l (q_fact (Datatypes.S m))).
      exact Hfact.
Qed.

(* A6 形态分离主句（S1 §6 注记区预留名启用；前提位与 sigT 守卫位均取
   NatLe Set 序界（S01 :88，Id (Nat.leb) true 面）——And 内嵌前提 Set
   承载与窗族认证正本 And 内嵌 QltT 前提同法；And＝S01 A×B 逐字） *)
Definition lw4c_shape_separation : Set :=
  And (forall n : nat, NatLe 2 n ->
         sigT (fun _ : NatLe 2 n =>
           QltT (lw4c_e_win n) (lw4c_pi_win n)))
      (forall k n : nat, NatLe 1 k -> NatLe 1 n ->
         sigT (fun _ : NatLe 1 k =>
           sigT (fun _ : NatLe 1 n =>
             QltT (lw4c_powwin k n) (lw4c_pi_win n)))).
Theorem lw4c_shape_separation_intro : lw4c_shape_separation.
Proof.
  split.
  - intro n. intro H. exists H.
    exact (lw4c_e_win_lt_pi_win n (NatLe_drop 2 n H)).
  - intro k. intro n. intro Hk. intro Hn.
    exists Hk. exists Hn.
    exact (lw4c_pi_win_gt_powwin k n (NatLe_drop 1 k Hk) (NatLe_drop 1 n Hn)).
Qed.

(* ============================================================ *)
(* §9 数值区（Set 面闭项表；id_refl 承收；vm_compute 判例随件）      *)
(* ============================================================ *)

(* T1 窗宽对照闭项表：1/6 < 5/7、1/120 < 5/11、1/16 < 5/7 *)
Lemma lw4c_win_tbl :
  And (QltT (lw4c_e_win 3) (lw4c_pi_win 3))
      (And (QltT (lw4c_e_win 5) (lw4c_pi_win 5))
           (QltT (lw4c_powwin 2 3) (lw4c_pi_win 3))).
Proof. repeat split; exact id_refl. Qed.

(* e 侧见证数值表位（预置 T2）：lic_witness_e 的计算面在 vm_compute 下不终止，
   本位暂缺；窗宽对照表 T1 在位。 *)

(* ============================================================ *)
(* §10 高度坐标预建区（定义件 (b)-独立；证书面候 (b) 上游）          *)
(* ============================================================ *)

(* A7 高度函数：S (Pos.to_nat (Qden (Qred q))) 形 *)
Definition lw4c_height (q : Q) : nat := Datatypes.S (Pos.to_nat (Qden (Qred q))).

(* A8 幂率窗的 q 坐标版（纯算术定义，(b)-独立） *)
Definition lw4c_powwin_q (mu0 : nat) (C : Q) (q : Q) : Q :=
  C / q_pow ((Z.of_nat (lw4c_height q)) # 1)%Q mu0.

(* ============================================================ *)
(* §11 提取＋PA 扩面（五块七名；T2 位暂缺；红线④）                  *)
(* ============================================================ *)
Separate Extraction lw4c_powwin lw4c_pi_win_gt_powwin
  lw4c_shape_separation lw4c_shape_separation_intro
  lw4c_height lw4c_powwin_q lw4c_win_tbl.
Print Assumptions lw4c_e_win_lt_pi_win.
Print Assumptions lw4c_shape_separation_intro.
Print Assumptions lw4c_win_tbl.
