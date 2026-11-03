(* ===================================================================== *)
(*  abl_audit_base_v10.v —— 审计载体扩容 v10·S04_RealExpLogConv 直审闭合     *)
(*                          甲形态直审闭合件                                *)
(* ===================================================================== *)
(*  使命: S04_RealExpLogConv（全树 Require 下游最宽柱之二，池拷源 md5          *)
(*        6396aec4e4a2bb239e51c35acf14b437 与预编译树/Live 三侧逐字一致）      *)
(*        r_pow 系／exp 系／log 系／收敛预算面主定理铸五条轻量真使用载体      *)
(*        （使用＝证明体真实行使上游定理非空壳），共五载体九使用点：          *)
(*        ① abk_rpow_pos_engine_concrete——幂正性引擎（r_pow 系）             *)
(*          r_pow_pos 一般形直引＋具体实例翼：引擎在 x:=plus one one、        *)
(*          n:=2 参数位实例化消解，前提 0<(1+1) 经 plus_positive 双 one_pos 真推导      *)
(*          （一翼使用两定理）两使用点；                                     *)
(*        ② abk_rpow_dec_decay_and_budget——幂衰减序面（r_pow 系）            *)
(*          r_pow_dec 一般形直引＋双步推进翼（两引擎实例化消解于 S(S n)/S n 邻接    *)
(*          参数位＋le_trans 真链，语句面非上游转述）＋one_minus_pow_le_one      *)
(*          收敛尾界一般形直引（一翼使用三定理）三使用点；                   *)
(*        ③ abk_log_pow_cc_zero_chain——log 幂展开引擎（log 系）              *)
(*          log_pow_cc 一般形直引＋具体实例翼：log((1)^2)==0 零化计算链      *)
(*          （引擎实例化消解＋log_one＋mult_zero 两段 id_cong 运输）两使用点；      *)
(*        ④ abk_sum_exp_cons_head_pos——指数和非负引擎（exp 系）              *)
(*          sum_exp_positive（上游 Not 前提经核验为 S01:48 Set 版 Not        *)
(*          A->Empty_set，非 Prop）cons 头形重述翼（引擎实例化消解＋Id 构造子分裂   *)
(*          消解管件）＋双 cons 头形复合翼（两引擎实例化消解＋plus_positive）       *)
(*          两使用点；                                                       *)
(*        ⑤ abk_rarch_log_budget_and_geo——log 闭式击穿预算（收敛预算面）     *)
(*          r_arch_pow_log_budget 一般形直引＋函数本体投影参数位实例化消解翼           *)
(*          （sigT projT1/projT2 双层投影＋snd 取几何分量，主定理作为函数    *)
(*          本体在投影参数位实例化消解）两使用点。                                     *)
(*  岛值: 直审 S04＝审计覆盖首次伸入该塔主定理面：核验在卷——S04 主定理塔为    *)
(*        Id 版抽象接口形（Context {RI : RealInterfaceEnhanced}），全树该类   *)
(*        具体实例零个（grep 核验），S08:2896 判例「Id 版不可实例化到 Real   *)
(*        层」；G05_LogSmall Require S04 而定理名零消费（grep 核验，死依赖）  *)
(*        ——本次五载体使用＋尾舱 PA 直审为 S04 主定理面首次审计实例化消解。        *)
(*  依赖: S04_RealExpLogConv（预编译树 vo_local_world_unified_0930 只读      *)
(*        .vo 使用；池拷源只读不编译，逻辑名单根）；S01_BaseRing 显式导入    *)
(*        （Id/And/Or/Not/ExistsT 全 Set 层连接词声明面，S01:41-51 核验）；  *)
(*        Stdlib（Lists.List、Arith、Extraction 出口舱）。                   *)
(*  构造性: 零承认语句、零经典逻辑、零 Prop 载体：S01 全部连接词为 Set 定义  *)
(*        （Id:41 / And:46 := A*B / Or:47 := A+B / Not:48 := A->Empty_set /  *)
(*        ExistsT:51 := sigT），载体语句面全 Set 层——sigT 存在形、prod 合取  *)
(*        （*）、lt/le Set 序、Id Set 等式；无 eq/exists/and/or 任何 Prop    *)
(*        连词书写，无 Prop 前提位；证明体全 exact 显式项直交（唯一管件      *)
(*        abk_not_cons_nil 亦为 Definition 项形 Id 构造子分裂消解器）。      *)
(*  编译配方: source Live/toolchain/env.sh && unset COQLIB ROCQLIB &&        *)
(*        ulimit -s 65532 && rocq c -native-compiler no -q -Q <本池> ""      *)
(*        -Q vo_local_world_unified_0930 "" <本池>/abl_audit_base_v10.v      *)
(*        （独占池 audit_s04/，道闸 ≤1，单件无池内链序；9.1.0 工具链）。     *)
(*  核验注: ①审计目标选型（S04 源 5024 行主定理面实拍，池拷源行号同源）：     *)
(*        r_pow_pos:367／r_pow_dec:385／one_minus_pow_le_one:564／           *)
(*        iterate_cauchy:811／log_pow_cc:850／r_arch_pow_log_budget:875／    *)
(*        iterate_cauchy_explicit_N:893／dynamics_converges:1128／           *)
(*        sum_exp_positive:1550——覆盖 r_pow 系/exp 系/log 系/      *)
(*        收敛面四代表位。②discharge 签名两轮检验判定（abk_probe.v 签名实拍  *)
(*        ＋abk_probe2.v 八翼复合项烟测全部通过后入稿）。③abk_ 前缀现役池与     *)
(*        主树 grep 零命中（防撞核验在卷）。④池影坑排查（DS 系教训照   *)
(*        防）：S04.vo 预编译树有（使用根）；缓存根 #187/ConstructiveWorld_  *)
(*        vo/ 亦有但配方不映射不触碰；池拷源不编译不成 .vo——逻辑名单根，    *)
(*        无双影。⑤诚实边界：两收敛主定理 iterate_cauchy_explicit_N／      *)
(*        dynamics_converges 结论自嵌 nat 序前提骨架（(N<=m)%nat -> 形，    *)
(*        Probe 签名实拍在卷）——增严口径下不可重述入载体语句，按 v9 Prop 位  *)
(*        弃样纪律对偶调形为尾舱 PA 直审位（Print Assumptions 直审，不入    *)
(*        载体、不独立实例化消解），其面由同族全 Set 形 iterate_cauchy（直审）与   *)
(*        r_arch_pow_log_budget（载体⑤）邻接承担；S04 塔 Id 版零 Real 层   *)
(*        实例（判例在卷），故各具体实例翼在接口通用层具体参数位实例化消解（x:=plus    *)
(*        one one／one、n:=2），非 Real 层实例化——非空壳性由前提真推导链    *)
(*        与投影参数位函数本体实例化消解承担。⑥本件自身提取面魔数自审在出口舱后记。    *)
(* ===================================================================== *)

From Stdlib Require Import Lists.List Arith.Arith.
Require Import S01_BaseRing.
Require Import S04_RealExpLogConv.

(* 接口通用层载体区：RI 为 Id 版增强接口抽象参数位（全树零具体实例，判例在卷） *)
Section AbkCarriers.
Context {RI : RealInterfaceEnhanced}.

(* ============================================================ *)
(* §0 内部管件舱（Id 构造子分裂消解器，非载体语句）                  *)
(*    S01:48 Not 为 Set 版（A -> Empty_set），本管件全 Set 层。      *)
(* ============================================================ *)

(* 消解形证体：指标 (a::l) 与 nil 无同一构造支可统一，矛盾支就地封闭。 *)
Lemma abk_not_cons_nil :
  forall (A : Set) (a : A) (l : list A), Not (Id (a :: l) nil).
Proof.
  intros A a l Hc. inversion Hc.
Qed.

(* ============================================================ *)
(* §1 载体一·幂正性引擎（r_pow 系）：一般形直引＋                       *)
(*    具体实例翼（x := 1+1、n := 2 参数位实例化消解，前提真推导链）               *)
(* ============================================================ *)

Theorem abk_rpow_pos_engine_concrete :
  (forall (x : R) (n : nat), lt zero x -> lt zero (r_pow x n)) *
  lt zero (r_pow (plus one one) 2).
Proof.
  split.
  - (* 幂正性主定理一般形逐字直引。 *)
    intros x n Hx. exact (r_pow_pos x n Hx).
  - (* 具体实例：引擎于 x := plus one one、n := 2 参数位实例化消解；                 *)
    (* 前提 0 < (1+1) 经 plus_positive 于双 one_pos 叶真推导（非转述）。   *)
    exact (r_pow_pos (plus one one) 2
             (plus_positive one one one_pos one_pos)).
Qed.

(* ============================================================ *)
(* §2 载体二·幂衰减序面（r_pow 系）：一般形直引＋双步推进真链＋          *)
(*    收敛尾界 one_minus_pow_le_one 直引                                *)
(* ============================================================ *)

Theorem abk_rpow_dec_decay_and_budget :
  (forall (b : R) (n : nat), lt zero b -> lt b one ->
     le (r_pow b (Datatypes.S n)) (r_pow b n)) *
  (forall (b : R) (n : nat), lt zero b -> lt b one ->
     le (r_pow b (Datatypes.S (Datatypes.S n))) (r_pow b n)) *
  (forall (kappa : R), lt zero kappa ->
     forall m : nat, le (minus one (r_pow kappa m)) one).
Proof.
  split.
  - split.
    + (* 衰减主定理一般形逐字直引。 *)
      intros b n Hb Hb1. exact (r_pow_dec b n Hb Hb1).
    + (* 双步推进翼：两引擎实例化消解于 S(S n)／S n 邻接参数位＋le_trans 真链——     *)
      (* 语句面为本件新形（非上游转述），两翼独立行使引擎。               *)
      intros b n Hb Hb1.
      exact (le_trans (r_pow b (Datatypes.S (Datatypes.S n)))
                      (r_pow b (Datatypes.S n)) (r_pow b n)
                      (r_pow_dec b (Datatypes.S n) Hb Hb1)
                      (r_pow_dec b n Hb Hb1)).
  - (* 收敛尾界（one − κ^m ≤ 1）一般形逐字直引。 *)
    exact one_minus_pow_le_one.
Qed.

(* ============================================================ *)
(* §3 载体三·log 幂展开引擎（log 系）：一般形直引＋                      *)
(*    具体实例翼 log(1²) == 0 零化计算链（引擎＋两段运输）              *)
(* ============================================================ *)

Theorem abk_log_pow_cc_zero_chain :
  (forall (x : R) (n : nat), lt zero x ->
     Id (log (r_pow x n)) (mult (nat_to_R n) (log x))) *
  Id (log (r_pow one 2)) zero.
Proof.
  split.
  - (* log 幂展开主定理一般形逐字直引（log_mult 归纳引擎）。 *)
    intros x n Hx. exact (log_pow_cc x n Hx).
  - (* 具体实例：引擎于 x := one、n := 2 参数位实例化消解；右端 (nat_to_R 2)·log 1   *)
    (* 经 log_one 换形＋mult_zero 两段 id_cong 运输零化（真计算链）。      *)
    exact (id_trans (log_pow_cc one 2 one_pos)
             (id_trans (id_cong (mult (nat_to_R 2)) log_one)
                       (mult_zero (nat_to_R 2)))).
Qed.

(* ============================================================ *)
(* §4 载体四·指数和非负引擎（exp 系）：cons 头形重述翼＋                 *)
(*    双 cons 复合翼（上游 Not 前提为 S01 Set 版，管件同 Set 层）        *)
(* ============================================================ *)

Theorem abk_sum_exp_cons_head_pos :
  (forall (Token : Set) (neg_log_prob : list Token -> Token -> R)
     (prefix : list Token) (w : Token) (rest : list Token),
     lt zero (sum_exp Token neg_log_prob prefix (w :: rest))) *
  (forall (Token : Set) (neg_log_prob : list Token -> Token -> R)
     (prefix : list Token) (w1 w2 : Token) (rest : list Token),
     lt zero (sum_exp Token neg_log_prob prefix (w1 :: w2 :: rest))).
Proof.
  split.
  - (* cons 头形：引擎实例化消解＋Id 构造子分裂消解管件（非空表见证真构造）。     *)
    intros Token neg_log_prob prefix w rest.
    exact (sum_exp_positive Token neg_log_prob prefix (w :: rest)
             (abk_not_cons_nil Token w rest)).
  - (* 双 cons 复合翼：两引擎实例化消解（w1 参数位／w2 参数位）＋plus_positive 真复合——  *)
    (* 语句面为本件新形，两翼独立行使引擎。                                *)
    intros Token neg_log_prob prefix w1 w2 rest.
    exact (plus_positive (exp_neg (neg_log_prob prefix w1))
             (sum_exp Token neg_log_prob prefix (w2 :: rest))
             (exp_neg_pos (neg_log_prob prefix w1))
             (sum_exp_positive Token neg_log_prob prefix (w2 :: rest)
                (abk_not_cons_nil Token w2 rest))).
Qed.

(* ============================================================ *)
(* §5 载体五·log 闭式击穿预算（收敛预算面）：一般形直引＋                *)
(*    函数本体投影参数位实例化消解翼（sigT 双层投影取几何分量）                    *)
(* ============================================================ *)

Theorem abk_rarch_log_budget_and_geo :
  (forall (kappa : R) (Hk : lt zero kappa)
     (rap : forall a : R, lt zero a -> forall eps : R, lt zero eps ->
              sigT (fun n : nat => lt (mult a (r_pow kappa n)) eps))
     (lmono : forall a b : R, lt zero a -> lt zero b -> lt a b -> lt (log a) (log b)),
   forall (a eps : R) (Ha : lt zero a) (Hep : lt zero eps),
     sigT (fun N : nat =>
       And (le (log (mult a (r_pow kappa N))) (log eps))
           (lt (mult a (r_pow kappa N)) eps))) *
  (forall (kappa : R) (Hk : lt zero kappa)
     (rap : forall a : R, lt zero a -> forall eps : R, lt zero eps ->
              sigT (fun n : nat => lt (mult a (r_pow kappa n)) eps))
     (lmono : forall a b : R, lt zero a -> lt zero b -> lt a b -> lt (log a) (log b))
     (a eps : R) (Ha : lt zero a) (Hep : lt zero eps),
   lt (mult a (r_pow kappa
          (projT1 (r_arch_pow_log_budget kappa Hk rap lmono a Ha eps Hep)))) eps).
Proof.
  split.
  - (* 预算主定理一般形逐字直引（log 单调面升级链）。 *)
    intros kappa Hk rap lmono a eps Ha Hep.
    exact (r_arch_pow_log_budget kappa Hk rap lmono a Ha eps Hep).
  - (* 函数本体投影参数位实例化消解：主定理作为函数本体在投影参数位实例化消解——                *)
    (* projT1 取预算 N、projT2∘snd 取几何分量，双重真行使。                *)
    intros kappa Hk rap lmono a eps Ha Hep.
    exact (snd (projT2 (r_arch_pow_log_budget kappa Hk rap lmono a Ha eps Hep))).
Qed.

End AbkCarriers.

(* ============================================================ *)
(* §6 尾舱·假设审计（S04 主定理面九直审位＋本件五载体自审）              *)
(*    判读判据：十四条全输出 Closed under the global context。           *)
(*    前 9 条＝直审位（r_pow 双引擎／尾界／log 幂展开／指数和非负／      *)
(*    log 击穿预算／柯西收敛双形／显式收敛率主定理／收敛主定理）——       *)
(*    S04 主定理面此前全树 PA 直审缺位（G05 死依赖核验在卷）；           *)
(*    其中 iterate_cauchy_explicit_N／dynamics_converges 因结论自嵌      *)
(*    nat 序前提骨架（增严口径不可重述入载体）按核验注⑤调形纯 PA 直审。  *)
(*    后 5 条＝本件五载体自审。                                          *)
(*    注：Require 闭包含 S01-S03 全链，coqchk 环境公理面与逐定理 PA      *)
(*    定检分账，非本件引入。                                             *)
(* ============================================================ *)

Print Assumptions r_pow_pos.
Print Assumptions r_pow_dec.
Print Assumptions one_minus_pow_le_one.
Print Assumptions log_pow_cc.
Print Assumptions sum_exp_positive.
Print Assumptions r_arch_pow_log_budget.
Print Assumptions iterate_cauchy.
Print Assumptions iterate_cauchy_explicit_N.
Print Assumptions dynamics_converges.
Print Assumptions abk_rpow_pos_engine_concrete.
Print Assumptions abk_rpow_dec_decay_and_budget.
Print Assumptions abk_log_pow_cc_zero_chain.
Print Assumptions abk_sum_exp_cons_head_pos.
Print Assumptions abk_rarch_log_budget_and_geo.

(* ============================================================ *)
(* §7 出口舱：载体兼任提取端口（G3：提取面零魔数）                       *)
(* ============================================================ *)

From Stdlib Require Import Extraction.
Separate Extraction abk_rpow_pos_engine_concrete
  abk_rpow_dec_decay_and_budget abk_log_pow_cc_zero_chain
  abk_sum_exp_cons_head_pos abk_rarch_log_budget_and_geo.
