(* ============================================================
   使命：本件数学使命叙述见下方原头注首段（既有件注记型头注整编尚待后续）。
   依赖：见原头注 Require 面与依赖段。
   对标：见原头注来源/对标行。
   构造性：纯构造性、零承认件（详见原头注红线自审段）。
   编译配方：coqc -native-compiler no -q -Q . ""。
   ============================================================ *)
(* ============================================================ *)
(*                                                              *)
(* 使命：UpFirewall.v:102 inv_pos_lt_compat 诚实接口槽 C 类兑现。  *)
(*   槽语句（UpFirewall.v:102-103，根 L17119 同名 Variable 复刻）： *)
(*     forall a b : R, lt zero a -> lt zero b ->                *)
(*       lt a b -> lt (inv_pos b Hb) (inv_pos a Ha)             *)
(*   （正倒数严格反变：升温 ⟹ 1/t 严格降，温度严格单调链的      *)
(*     核心序槽；接口已有 le 版字段 inv_pos_le_compat，          *)
(*     S01:249——严格版此前仅具体 Real 层 real_inv_pos_lt_contra  *)
(*     S07:6040 在册，抽象层缺口本件补齐。）                     *)
(*                                                              *)
(* 闭合原理：纯序-代数链，无需可判定序扩展（DecidableOrder 不     *)
(*   入依赖面，比 fa53/fa57 兄弟槽更干净）：                      *)
(*     inv b == (inv a·a)·inv b < (inv a·b)·inv b == inv a       *)
(*   ① 单侧严格左乘（lt_mult_compat 右乘形 + 两次 mult_comm      *)
(*    运河，fa53_lt_plus_translate 同构运河法）；                 *)
(*   ② 再右乘 inv b（lt_mult_compat 直接给出，正性由 inv_pos_pos）；  *)
(*   ③ 左运河：(inv a·a) ≡ one（mult_comm + inv_pos_correct）    *)
(*      叠 one 左乘归位（mult_comm + mult_one）；                 *)
(*   ④ 右运河：(inv a·b)·inv b ≡ inv a（mult_assoc 重排 +        *)
(*      inv_pos_correct + mult_one）；                           *)
(*   ⑤ lt_id_l/lt_id_r 双端转换闭合。                            *)
(*   ——库内坐标实测：槽使用位 UpFirewall:102；Real 层佐证         *)
(*     real_inv_pos_lt_contra S07:6040（使用 S07:6792、          *)
(*     CW220:1044、S08:637、S09:1390、UpBudgetReal:322、          *)
(*     UpRealLeB:134、S11:8059、UpReqMinPKLChain:949 等）。       *)
(*                                                              *)
(* 纪律：纯构造性 / 语句面全 Set 层（Id/lt，Not=S01:70            *)
(*   Empty_set 函数形）/ 非平凡真证（四段字段链）/ 原树零改；     *)
(*   前缀 ipl_ 全库防同名冲突已核；尾嵌 Print Assumptions 自检段。      *)
(* ============================================================ *)

Require Import S01_BaseRing.

Section InvPosLtCompat.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.

(* 投影别名（UpFirewall.v:85-92 同款解包） *)
Let R := @R RI.
Let zero := @zero RI.
Let one := @one RI.
Let mult := @mult RI.
Let inv_pos := @inv_pos RI.
Let lt := @lt RI.

(* ---- 支撑①：单侧严格左乘（新形：lt_mult_compat 字段是右乘形，
        接口层左乘严格此前缺位，fa53 平移件同构运河法补齐） ---- *)
Lemma ipl_lt_mult_compat_l :
  forall a b c : R, lt zero c -> lt a b -> lt (mult c a) (mult c b).
Proof.
  intros a b c Hc Hab.
  apply (lt_id_r (mult c a) (mult b c) (mult c b) (mult_comm b c)).
  apply (lt_id_l (mult c a) (mult a c) (mult b c) (mult_comm c a)).
  exact (lt_mult_compat a b c Hc Hab).
Qed.

(* ---- 主件：正倒数严格反变（UpFirewall:102 槽消融主件） ----
   inv b == (inv a·a)·inv b < (inv a·b)·inv b == inv a。 *)
Theorem ipl_inv_pos_lt_compat :
  forall a b : R, forall Ha : lt zero a, forall Hb : lt zero b,
    lt a b -> lt (inv_pos b Hb) (inv_pos a Ha).
Proof.
  intros a b Ha Hb Hab.
  (* 中项严格：inv a·a < inv a·b（左乘 inv a > 0），
     再整体右乘 inv b > 0（E-STAGING-ReqAlignRestA 链式真证同型） *)
  assert (Hmid : lt (mult (inv_pos a Ha) a) (mult (inv_pos a Ha) b)).
  { exact (ipl_lt_mult_compat_l a b (inv_pos a Ha) (inv_pos_pos a Ha) Hab). }
  assert (Hstep : lt (mult (mult (inv_pos a Ha) a) (inv_pos b Hb))
                     (mult (mult (inv_pos a Ha) b) (inv_pos b Hb))).
  { exact (lt_mult_compat (mult (inv_pos a Ha) a) (mult (inv_pos a Ha) b)
                          (inv_pos b Hb) (inv_pos_pos b Hb) Hmid). }
  (* 左运河：X := (inv a·a)·inv b ≡ inv b（(inv a·a) ≡ one + one 左乘归位） *)
  assert (Hl : Id (mult (mult (inv_pos a Ha) a) (inv_pos b Hb))
                  (inv_pos b Hb)).
  { exact (id_trans
             (id_cong (fun w => mult w (inv_pos b Hb))
                      (id_trans (mult_comm (inv_pos a Ha) a)
                                (inv_pos_correct a Ha)))
             (id_trans (mult_comm one (inv_pos b Hb))
                       (mult_one (inv_pos b Hb)))). }
  (* 右运河：Y := (inv a·b)·inv b ≡ inv a（assoc 重排 +
     inv b·inv b ≡ one + mult_one 右乘归位） *)
  assert (Hr : Id (mult (mult (inv_pos a Ha) b) (inv_pos b Hb))
                  (inv_pos a Ha)).
  { exact (id_trans (id_sym (mult_assoc (inv_pos a Ha) b (inv_pos b Hb)))
                    (id_trans (id_cong (fun w => mult (inv_pos a Ha) w)
                                       (inv_pos_correct b Hb))
                              (mult_one (inv_pos a Ha)))). }
  (* 双端转换闭合 *)
  exact (lt_id_r (inv_pos b Hb)
                 (mult (mult (inv_pos a Ha) b) (inv_pos b Hb))
                 (inv_pos a Ha) Hr
                 (lt_id_l (inv_pos b Hb)
                          (mult (mult (inv_pos a Ha) a) (inv_pos b Hb))
                          (mult (mult (inv_pos a Ha) b) (inv_pos b Hb))
                          (id_sym Hl) Hstep)).
Qed.

(* ---- 槽互核形：与 UpFirewall.v:102 逐字同语句的改喂锚 ---- *)
Corollary ipl_upfirewall_102_shape :
  forall a b : R, forall Ha : lt zero a, forall Hb : lt zero b,
    lt a b -> lt (inv_pos b Hb) (inv_pos a Ha).
Proof.
  exact (fun a b Ha Hb Hab => ipl_inv_pos_lt_compat a b Ha Hb Hab).
Qed.

(* ---- 对偶形：正倒数严格正变（lt (inv a) (inv b) 方向，
        兄弟槽族 real_inv_pos_lt 形；由主件 + lt_id 双向转换） ---- *)
Lemma ipl_lt_inv_pos_mono :
  forall a b : R, forall Ha : lt zero a, forall Hb : lt zero b,
    lt b a -> lt (inv_pos a Ha) (inv_pos b Hb).
Proof.
  intros a b Ha Hb Hba.
  exact (ipl_inv_pos_lt_compat b a Hb Ha Hba).
Qed.

(* ---- le 版相容性核验：主件 ⟹ 接口字段 inv_pos_le_compat 同型
        （严格蕴非严，lt_le_iff 字段运河；确认与 S01:249 字段无冲突） ---- *)
Corollary ipl_inv_pos_le_of_lt :
  forall a b : R, forall Ha : lt zero a, forall Hb : lt zero b,
    lt a b -> le (inv_pos b Hb) (inv_pos a Ha).
Proof.
  intros a b Ha Hb Hab.
  exact (lt_le_iff (inv_pos b Hb) (inv_pos a Ha)
           (inl (ipl_inv_pos_lt_compat a b Ha Hb Hab))).
Qed.

End InvPosLtCompat.

(* ---- G1 内嵌自检段（四道核验前置：文件内显式 PA 声明） ---- *)
Print Assumptions ipl_lt_mult_compat_l.
Print Assumptions ipl_inv_pos_lt_compat.
Print Assumptions ipl_upfirewall_102_shape.
Print Assumptions ipl_lt_inv_pos_mono.
Print Assumptions ipl_inv_pos_le_of_lt.
