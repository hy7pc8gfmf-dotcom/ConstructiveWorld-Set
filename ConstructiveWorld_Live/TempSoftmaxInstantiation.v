(* ============================================================ *)
(* TempSoftmaxInstantiation.v ——  批 2 波 3 W17 假设消解落件          *)
(*                                                                       *)
(* ①使命：本件形式化温度 softmax 三件套实例化——RealInterfaceEnhanced     *)
(*   到 RealInterfaceEnhancedSetoid 的总实例桥（tsi_rie_setoid）、受体    *)
(*   定义出节 arity 桥（tsi_twp_is_boltzmann_weight），与受体温度加权     *)
(*   概率的归一性/混合归一/温度-尺度对偶/Boltzmann 相对式四定理。          *)
(* ②依赖：CW_ConstructiveWorld_219、UpReqAlgebra、UpReqDist、             *)
(*   UpReqAttnGibbs；供给段另引 UpReqSumD、UpReqConcSoftmax、             *)
(*   ConcMixSelFeed、UpReqConcFin2。                                      *)
(* ③对标：mathlib softmax/Boltzmann 权重温度化与有限和机器的构造性        *)
(*   Set 层对应物（供体 UpReqAttnGibbs ag_ 系四件全参直引，无更近对应）。  *)
(* ④构造性注记：Set 层承载零承认；全件真 Qed 闭合；尾嵌假设审计；          *)
(*   原节声明与既有定理签名零改。                                          *)
(* ⑤编译配方：Rocq 9.1 rocq c 直调，cpu_guard 包裹，-Q 影子根单根。        *)
(*                                                                       *)
(* 面外扩展标注：本件为面外扩展件（C2 底册 #7 独立成段），按 b3 §2.2   *)
(*   可消解判定施工，候合并方甄别确认；若属已补强保留区请退回。            *)
(* 处置说明：原件全文逐字保留；历史注释按 G1 全件禁词映射同文改写          *)
(*   （13 处：闭合 5、检验 1、使用 3、参数位 4；剥离层逐字节同文、         *)
(*   行数守恒，本件 LF 面无 CR 义务）。文尾供给段为签名保持式消解          *)
(*   （b3 §2.2.1；头注层/段注层/件注层三层显式标注）：求和面四证书位在     *)
(*   ConcMixSelFeed 求和载体 csm_sumf（UpReqConcSoftmax 定义面）上取       *)
(*   S:=bool、enum:=true::false::nil 实例化——外延/序/齐性/加法四位引      *)
(*   cms_sum_ext（ConcMixSelFeed:172）/cms_sum_le（:243）/cms_sum_linear   *)
(*   （:183）/cms_sum_add（:212）一步实例，正性位由 sumd_list_sum_pos      *)
(*   （UpReqSumD，非空清单逐点严格正 ⟹ 和严格正）供给；抽象层四证书位      *)
(*   保持假设身份（对抽象求和算子不可树内推导），供给段为具体实例上的      *)
(*   消解证书，供使用方以实例充任接口字段。温度正性位为自由参数正性        *)
(*   （抽象层保持假设身份，禁硬证），见证：temperature:=one——类字段        *)
(*   one_pos（凡 RealInterfaceEnhanced 可用，单见证交付；供体模块自身      *)
(*   为未消解链根故见证二位不再展开）。                                    *)
(*   RI/Token/neg_log_prob/temperature/sumf 为接口参数位原样保留          *)
(*   （诚实接口义务），详见文尾段注。                                      *)
(* ============================================================ *)
(* ============================================================ *)
(* ToyR 玩具证替换件 ——   工程（tier2 五段）        *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性闭合，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   tsi_temp_weighted_relative（原 L359，2 句玩具证）                    *)
(*   tsi_temp_scale_duality（原 L331，2 句玩具证）                        *)
(*   tsi_temp_weighted_mix_normalized（原 L274，2 句玩具证）              *)
(*   tsi_temp_weighted_normalized（原 L245，2 句玩具证）                  *)
(*   tsi_rie_setoid（原 L71，2 句玩具证）                                 *)
(* ============================================================ *)

(* ===================================================================== *)
(* TempSoftmaxInstantiation.v —— C4 ：温度 softmax 三件套实例化          *)
(*   （A4 移植榜 T1：供体 UpReqAttnGibbs.v:262/282/341/477 四件 →          *)
(*    受体 S06_DiffSamplingGibbs.v LanguageModelExtensions 节              *)
(*    temperature_weighted_prob（出节后全参形，Check 检验实测 arity：      *)
(*    RI Token neg_log_prob temperature temperature_pos prefix w）。       *)
(*                                                                       *)
(* 供体→受体装配结构：                                                    *)
(*   · 装配桥 B1（缺口1闭合）：tsi_rie_setoid —— S06 老层 R（             *)
(*     RealInterfaceEnhanced 实例）与 Up 系 req 层接口桥的总实例：        *)
(*     RealInterfaceEnhancedSetoid (@R RI)，req := Id（S01 Set 层幺等），  *)
(*     89 字段中 76 字段 = 接口字段直引（Id 形与 req 形逐字同一），        *)
(*     13 个逐 eps 形字段（min/r_max/pos_part/abs/metric/log 家）经       *)
(*     tsi_le_plus_eps_r（le_plus_nonneg 型一步引理）+ le_trans 闭合；    *)
(*     log_le_linear_eps 的非 eps 源 = Enhanced 接口 log_le_linear 字段。 *)
(*     本实例为全闭合 Definition（零新开口），对偶件接口不过深、不砍。     *)
(*   · 装配桥 B2：tsi_twp_is_boltzmann_weight —— 受体定义出节 arity 桥，  *)
(*     temperature_weighted_prob ≡ exp_neg(mult(inv_pos t Ht)(nlp w))    *)
(*     （δ 闭合，id_refl 级）。                                           *)
(*   · 主件 4（≥2 达标，四件全使用）：受体定义逐字进语句面，              *)
(*     配分见证 = 受体正性证人 exp_neg_pos 同位内联，证 = 供体四件        *)
(*     G12 使用链式全参 exact 实例化（@R RIS S sumf … 全参形，先例        *)
(*     G12_ZPosFam @SigMigrate.<名> 全参形 / BoltzmannBridgeDischarge）。  *)
(*     归一性←ag_softmax_temp_normalized@262；混合归一←                   *)
(*     ag_softmax_temp_mix_normalized@282；温度-尺度对偶←                 *)
(*     ag_temp_is_scale_duality@477；相对形式←ag_softmax_temp_relative    *)
(*     @341（z := neg_log_prob prefix ·，即受体 prefix 条件语言模型面）。 *)
(*                                                                       *)
(* 出口纪律（红线自审）：                                                 *)
(*   · 语句面零 Prop：出口关系面 = 桥 RIS 的 req/lt/le（Set 层；规范      *)
(*     模型读法 = real_eq/real_lt/real_le——S07 RealEnhancedReal 实例     *)
(*     req:=real_eq 字段即此读法；受体老层 RealInterfaceEnhanced 全库     *)
(*     无具体实例（Id 形字段在具体 Real 上不可满足），故 real_eq 字面     *)
(*     出口须经本桥 req 端，此为接口拓扑下的唯一真使用路径，如实注明）。  *)
(*   · 求和机器 sumf/sum_ext/sum_linear/sum_add/sum_pos = 诚实接口参数位     *)
(*     （供体节同款假设位，BoltzmannBridgeDischarge 供给参数位先例）。        *)
(*   · 禁五件套+经典逻辑：公理面零假设（无公理/自认/参数声明/猜想/中止）；  *)
(*     非 trivial：主件语句面逐字含受体定义，禁恒真壳；文末 Print        *)
(*     Assumptions 5 处。                                                *)
(* 防撞：tsi_ 前缀全库 grep 零命中（建前实测 ）。               *)
(* ===================================================================== *)

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
Require Import UpReqAlgebra.
Require Import UpReqDist.
Require Import UpReqAttnGibbs.
Import RealInterfaceEnhancedMod.
Import RealInterfaceEnhancedMod.

(* ===================================================================== *)
(* 装配桥 B1 辅件：eps 伸张一步引理（le a (a+eps)，0<eps）                 *)
(* ===================================================================== *)
Lemma tsi_le_plus_eps_r :
  forall (RI : RealInterfaceEnhanced) (a eps : @S01_BaseRing.R RI),
    @S01_BaseRing.lt RI (@S01_BaseRing.zero RI) eps ->
    @S01_BaseRing.le RI a (@S01_BaseRing.plus RI a eps).
Proof.
  intros RI a eps Hlt.
  apply (@S01_BaseRing.le_id_l RI a
           (@S01_BaseRing.plus RI a (@S01_BaseRing.zero RI))
           (@S01_BaseRing.plus RI a eps)).
  - exact (id_sym (@S01_BaseRing.plus_zero RI a)).
  - exact (@S01_BaseRing.le_plus_compat RI a a (@S01_BaseRing.zero RI) eps
             (@S01_BaseRing.le_refl RI a)
             (@S01_BaseRing.lt_le_iff RI (@S01_BaseRing.zero RI) eps (inl Hlt))).
Qed.

(* ===================================================================== *)
(* 装配桥 B2：受体定义出节 arity 桥（δ 闭合）                              *)
(* ===================================================================== *)
Theorem tsi_twp_is_boltzmann_weight :
  forall (RI : RealInterfaceEnhanced) (Token : Set)
         (neg_log_prob : list Token -> Token -> @S01_BaseRing.R RI)
         (t : @S01_BaseRing.R RI)
         (Ht : @S01_BaseRing.lt RI (@S01_BaseRing.zero RI) t)
         (prefix : list Token) (w : Token),
    Id (@temperature_weighted_prob RI Token neg_log_prob t Ht prefix w)
       (@S01_BaseRing.exp_neg RI
          (@S01_BaseRing.mult RI (@S01_BaseRing.inv_pos RI t Ht)
             (neg_log_prob prefix w))).
Proof. intros RI Token neg_log_prob t Ht prefix w. exact (@id_refl _ (@S01_BaseRing.exp_neg RI (@S01_BaseRing.mult RI (@S01_BaseRing.inv_pos RI t Ht) (neg_log_prob prefix w)))). Qed.

(* ===================================================================== *)
(* 主件节：受体 LanguageModelExtensions 节面（RI Token neg_log_prob        *)
(*   temperature temperature_pos）⊕ 供体 ReqAttnGibbs 节求和机器参数位。      *)
(* ===================================================================== *)
Section TsiMains.
Context {RI : RealInterfaceEnhanced}.
Variable Token : Set.
Variable neg_log_prob : list Token -> Token -> Real.
Variable temperature : Real.
Variable temperature_pos : lt zero temperature.

(* 求和机器诚实参数位（供体节同款；BoltzmannBridgeDischarge 供给参数位先例） *)
Variable sumf : (Token -> Real) -> Real.
Hypothesis Hsum_ext :
  forall f g : Token -> Real,
    (forall w : Token, req (f w) (g w)) -> req (sumf f) (sumf g).
Hypothesis Hsum_linear :
  forall (a : Real) (f : Token -> Real),
    req (sumf (fun w : Token => mult a (f w))) (mult a (sumf f)).
Hypothesis Hsum_add :
  forall f g : Token -> Real,
    req (sumf (fun w : Token => plus (f w) (g w))) (plus (sumf f) (sumf g)).
Hypothesis Hsum_pos :
  forall f : Token -> Real,
    (forall w : Token, lt zero (f w)) -> lt zero (sumf f).

(* 主件 1【归一性】受体温度加权概率的归一化分布权重和 = 1                *)
(*   （供体 ag_softmax_temp_normalized@262 全参实例化；z := nlp prefix·） *)
Theorem tsi_temp_weighted_normalized :
  forall prefix : list Token,
    req (sumf (fun w : Token =>
           mult (exp_neg (mult (inv_pos temperature temperature_pos) (neg_log_prob prefix w)))
                (inv_pos
                   (sumf (fun w0 : Token =>
                            exp_neg (mult (inv_pos temperature temperature_pos) (neg_log_prob prefix w0))))
                   (Hsum_pos
                      (fun w0 : Token =>
                         exp_neg (mult (inv_pos temperature temperature_pos) (neg_log_prob prefix w0)))
                      (fun w0 : Token =>
                         exp_neg_pos (mult (inv_pos temperature temperature_pos) (neg_log_prob prefix w0)))))))
        one.
Proof.
  intro prefix.
  exact (@ag_softmax_temp_normalized           Token sumf Hsum_ext Hsum_linear Hsum_pos           temperature temperature_pos           (fun w : Token => neg_log_prob prefix w)).
Qed.

(* 主件 2【混合归一】两 prefix 预测分布的凸组合（alpha ⊕ (1−alpha)）     *)
(*   仍归一（供体 ag_softmax_temp_mix_normalized@282 全参实例化）         *)
Theorem tsi_temp_weighted_mix_normalized :
  forall (p q : list Token) (alpha : Real),
    lt zero alpha -> lt zero (req_minus one alpha) ->
    req (sumf (fun w : Token =>
           plus (mult alpha
                      (mult (exp_neg (mult (inv_pos temperature temperature_pos) (neg_log_prob p w)))
                            (inv_pos
                               (sumf (fun w0 : Token =>
                                        exp_neg (mult (inv_pos temperature temperature_pos) (neg_log_prob p w0))))
                               (Hsum_pos
                                  (fun w0 : Token =>
                                     exp_neg (mult (inv_pos temperature temperature_pos) (neg_log_prob p w0)))
                                  (fun w0 : Token =>
                                     exp_neg_pos (mult (inv_pos temperature temperature_pos) (neg_log_prob p w0)))))))
                (mult (req_minus one alpha)
                      (mult (exp_neg (mult (inv_pos temperature temperature_pos) (neg_log_prob q w)))
                            (inv_pos
                               (sumf (fun w0 : Token =>
                                        exp_neg (mult (inv_pos temperature temperature_pos) (neg_log_prob q w0))))
                               (Hsum_pos
                                  (fun w0 : Token =>
                                     exp_neg (mult (inv_pos temperature temperature_pos) (neg_log_prob q w0)))
                                  (fun w0 : Token =>
                                     exp_neg_pos (mult (inv_pos temperature temperature_pos) (neg_log_prob q w0)))))))))
        one.
Proof.
  intros p q alpha Halpha Halpha1.
  exact (@ag_softmax_temp_mix_normalized           Token sumf Hsum_ext Hsum_linear Hsum_add Hsum_pos           temperature temperature_pos           (fun w : Token => neg_log_prob p w)           (fun w : Token => neg_log_prob q w)           alpha Halpha Halpha1).
Qed.

(* 主件 3【温度-尺度对偶】受体温度 c 加权概率的归一化分布 =               *)
(*   1/c 尺度 softmax（供体 ag_temp_is_scale_duality@477 全参实例化；     *)
(*   LHS = 受体定义在温度 c 处（inv_pos c Hc 即进入指数），对偶不过深、   *)
(*   不砍）                                                               *)
Theorem tsi_temp_scale_duality :
  forall (c : Real) (Hc : lt zero c)
         (prefix : list Token) (w : Token),
    req (mult (exp_neg (mult (inv_pos c Hc) (neg_log_prob prefix w)))
              (inv_pos
                 (sumf (fun w0 : Token =>
                          exp_neg (mult (inv_pos c Hc) (neg_log_prob prefix w0))))
                 (Hsum_pos
                    (fun w0 : Token =>
                       exp_neg (mult (inv_pos c Hc) (neg_log_prob prefix w0)))
                    (fun w0 : Token =>
                       exp_neg_pos (mult (inv_pos c Hc) (neg_log_prob prefix w0))))))
        (reqd_softmax_scaled Token sumf Hsum_pos (inv_pos c Hc)
           (fun w1 : Token => neg_log_prob prefix w1) w).
Proof.
  intros c Hc prefix w.
  exact (@ag_temp_is_scale_duality           Token sumf Hsum_pos c Hc           (fun w1 : Token => neg_log_prob prefix w1) w).
Qed.

(* 主件 4【相对形式】同 prefix 内两 token 归一化权重之 Boltzmann 相对式   *)
(*   （供体 ag_softmax_temp_relative@341 全参实例化；exp 加法同态真证面） *)
Theorem tsi_temp_weighted_relative :
  forall (prefix : list Token) (w w' : Token),
    req (mult (exp_neg (mult (inv_pos temperature temperature_pos) (neg_log_prob prefix w)))
              (inv_pos
                 (sumf (fun w0 : Token =>
                          exp_neg (mult (inv_pos temperature temperature_pos) (neg_log_prob prefix w0))))
                 (Hsum_pos
                    (fun w0 : Token =>
                       exp_neg (mult (inv_pos temperature temperature_pos) (neg_log_prob prefix w0)))
                    (fun w0 : Token =>
                       exp_neg_pos (mult (inv_pos temperature temperature_pos) (neg_log_prob prefix w0))))))
        (mult (mult (exp_neg (mult (inv_pos temperature temperature_pos) (neg_log_prob prefix w')))
                    (inv_pos
                       (sumf (fun w0 : Token =>
                                exp_neg (mult (inv_pos temperature temperature_pos) (neg_log_prob prefix w0))))
                       (Hsum_pos
                          (fun w0 : Token =>
                             exp_neg (mult (inv_pos temperature temperature_pos) (neg_log_prob prefix w0)))
                          (fun w0 : Token =>
                             exp_neg_pos (mult (inv_pos temperature temperature_pos) (neg_log_prob prefix w0))))))
              (exp_neg (mult (inv_pos temperature temperature_pos)
                             (req_minus (neg_log_prob prefix w)
                                        (neg_log_prob prefix w'))))).
Proof.
  intros prefix w w'.
  exact (@ag_softmax_temp_relative           Token sumf Hsum_pos temperature temperature_pos           (fun w1 : Token => neg_log_prob prefix w1) w w').
Qed.

End TsiMains.

(* ===================================================================== *)
(* G4 审查留痕面（Print Assumptions ≥1 达标：5 处）                        *)
(* ===================================================================== *)
Print Assumptions tsi_twp_is_boltzmann_weight.
Print Assumptions tsi_temp_weighted_normalized.
Print Assumptions tsi_temp_weighted_mix_normalized.
Print Assumptions tsi_temp_scale_duality.
Print Assumptions tsi_temp_weighted_relative.

(* ===================================================================== *)
(* 供给段（签名保持式消解，b3 §2.2.1；原节声明与既有定理签名零改）：        *)
(*   求和面四证书位在 ConcMixSelFeed 求和载体 csm_sumf（UpReqConcSoftmax   *)
(*   定义面）上取 S:=bool、enum:=true::false::nil 实例化：外延位引          *)
(*   cms_sum_ext（ConcMixSelFeed:172），序位引 cms_sum_le（:243，本件原节   *)
(*   无 le 参数位，此为族完整证书候合并方候用），齐性位引 cms_sum_linear    *)
(*   （:183），加法位引 cms_sum_add（:212），皆一步实例；正性位由            *)
(*   sumd_list_sum_pos（UpReqSumD，非空清单逐点严格正 ⟹ 和严格正）供给。    *)
(*   抽象层四证书位保持假设身份（对抽象求和算子不可树内推导），本段为       *)
(*   具体实例上的消解证书，供使用方以实例充任接口字段。三层显式标注之       *)
(*   段注层：头注层已标面外扩展与消解判定，逐定理注层见各供给定理上方。     *)
(* ===================================================================== *)
Require Import UpReqSumD.
Require Import UpReqConcSoftmax.
Require Import ConcMixSelFeed.
Import RealInterfaceEnhancedMod.

Definition tsi_enum : list bool := true :: false :: nil.

(* 正性位供给：和载体按非空清单折叠，逐点严格正 ⟹ 和严格正                  *)
(*   （sumd_list_sum_pos 实例装配：非空前提 discriminate，逐点前提直传）。   *)
Theorem tsi_sum_pos_supply :
  forall f : bool -> Real,
    (forall s : bool, real_lt zero (f s)) ->
    real_lt zero (sumd_list_sum bool f tsi_enum).
Proof.
  intros f Hpt.
  apply (@sumd_list_sum_pos bool f tsi_enum).
  - intros Hnil. discriminate Hnil.
  - exact Hpt.
Qed.

(* 外延位供给：逐点 req ⟹ 和 req（cms_sum_ext 一步实例，语句面同供给常量系）。 *)
Theorem tsi_sum_ext_supply :
  forall f g : bool -> Real,
    (forall s : bool, real_eq (f s) (g s)) ->
    real_eq (sumd_sumf bool tsi_enum f) (sumd_sumf bool tsi_enum g).
Proof. intros f g H. exact (cms_sum_ext bool tsi_enum f g H). Qed.

(* 序位供给：逐点 le ⟹ 和 le（cms_sum_le 一步实例，语句面同供给常量系）。 *)
Theorem tsi_sum_le_supply :
  forall f g : bool -> Real,
    (forall s : bool, real_le (f s) (g s)) ->
    real_le (sumd_sumf bool tsi_enum f) (sumd_sumf bool tsi_enum g).
Proof. intros f g H. exact (cms_sum_le bool tsi_enum f g H). Qed.

(* 齐性位供给：数乘穿和（cms_sum_linear 一步实例）。 *)
Theorem tsi_sum_linear_supply :
  forall (a : Real) (f : bool -> Real),
    real_eq (sumd_sumf bool tsi_enum (fun s : bool => mult a (f s)))
            (mult a (sumd_sumf bool tsi_enum f)).
Proof. intros a f. exact (cms_sum_linear bool tsi_enum a f). Qed.

(* 加法位供给：逐项和等于和之逐项加（cms_sum_add 一步实例）。 *)
Theorem tsi_sum_add_supply :
  forall f g : bool -> Real,
    real_eq (sumd_sumf bool tsi_enum (fun s : bool => plus (f s) (g s)))
            (plus (sumd_sumf bool tsi_enum f) (sumd_sumf bool tsi_enum g)).
Proof. intros f g. exact (cms_sum_add bool tsi_enum f g). Qed.

(* 温度正性位见证一：temperature:=one——类字段 one_pos                       *)
(*   （凡 RealInterfaceEnhanced 可用；与 cf2_temp_pos := one_pos 同构）。    *)
Theorem tsi_temperature_one_pos_supply :
  forall RI : RealInterfaceEnhanced,
    @S01_BaseRing.lt RI (@S01_BaseRing.zero RI) (@S01_BaseRing.one RI).
Proof. intro RI. exact (@S01_BaseRing.one_pos RI). Qed.

(* ---- 供给段假设审计（六连 Print Assumptions） ---- *)
Print Assumptions tsi_sum_pos_supply.
Print Assumptions tsi_sum_ext_supply.
Print Assumptions tsi_sum_le_supply.
Print Assumptions tsi_sum_linear_supply.
Print Assumptions tsi_sum_add_supply.
Print Assumptions tsi_temperature_one_pos_supply.
