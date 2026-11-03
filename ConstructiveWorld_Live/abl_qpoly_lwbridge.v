(* ===================================================================== *)
(*  五字段指针｜使命：同事塔 LW0QPoly（二代代数供给源）→ 本地 qpd 除法线     *)
(*    桥接使用件——容器互转 + 求值机一致桥 + 点态律 Set 面直使用 + qpd 引擎   *)
(*    真使用示范。 依赖：Stdlib QArith/Qring/Qfield/List/Arith/ZArith/     *)
(*    Extraction；S01_BaseRing S02_CauchyComplete PolyIntegral（池外世界树  *)
(*    在册件）；LW0QPoly（同事塔甲形态直拷，md5 6f836288，byte-identity）    *)
(*    abl_qpoly_divmod（本地 qpd 除法引擎首件，md5 3f2bbb3c）。 构造性：     *)
(*    纯构造性、零承认件；本件语句面全 Set（QeqT/Id bool/qpd_lin_pred      *)
(*    And-of-Set），零 Prop 载体——LW0QPoly 的 13 件 Qeq（Prop 根）恒等式    *)
(*    【不重述、不硬吸收】，仅作证内推理脚手架（CG 缺口①草案授权位）。      *)
(*    编译配方：source Live/toolchain/env.sh && unset COQLIB ROCQLIB &&    *)
(*    ulimit -s 65532 && nice -19 rocq c -native-compiler no               *)
(*    -Q vo_local_world_unified_0930 "" -Q 沙箱/现役/abl_tmine04_pool/     *)
(*    qpoly_lwbridge "" abl_qpoly_lwbridge.v（道闸≤1＝单进程串行，先编       *)
(*    LW0QPoly.v → abl_qpoly_divmod.v → 本件）。 对标：CG 勘验报告缺口①     *)
(*    （LW0QPoly 二代代数供给源草案）；CJ 直收档条款登记（挂载前先落 QeqT    *)
(*    重述桥接件＋头注加桥注——本件即该桥接件本身）。                            *)
(* ===================================================================== *)
(*  abl_qpoly_lwbridge.v —— LW0QPoly→qpd 桥接使用件                         *)
(*                                                                        *)
(*  桥注（CJ 条款）：本件为「本地链挂载同事塔 LW0QPoly」前置 QeqT 重述桥接件。  *)
(*  三道门登记（源 md5 6f83628843129b922aa7df610be1e06c）：       *)
(*    ①红线门：承认式词面与经典逻辑词面全名单 grep        *)
(*      零命中；Qed 13/13 闭合；件尾自declare PA 4 件。           *)
(*    ②语句面甄别：13 Lem 全为 forall…, _==_（Qeq＝stdlib Prop 根）；        *)
(*      定义面 2 Def＋9 Fixpoint 全 Set 计算内容（Defined）。                *)
(*    ③CJ 条款：恒等式面 Qeq 根禁硬吸收成立——本件零重述其 Prop 恒等式，      *)
(*      仅做容器互转＋求值一致桥＋点态律 QeqT 重述（证内脚手架使用）。        *)
(*  容器形态判定：同构且更强——QPoly := list Q 与本地 list Q 为同一集合       *)
(*  （定义性互转零成本），头=常数项两系一致；求值机 qpoly_eval/pint_eval    *)
(*  同为 Horner 头递归，逐点相等（qlb_eval_agree）。桥=轻桥。               *)
(* ===================================================================== *)

From Stdlib Require Import QArith.QArith QArith.Qring QArith.Qfield.
From Stdlib Require Import Lists.List Arith.Arith ZArith.ZArith Extraction.
Import ListNotations.
Require Import S01_BaseRing S02_CauchyComplete PolyIntegral.
Require Import LW0QPoly abl_qpoly_divmod.

Open Scope Q_scope.

(* ============================================================ *)
(* §1 容器形态判定桥（互转＝恒等映射，零数据迁移）                  *)
(*    QPoly 展开即 list Q：同一 Set，双向往返为 definitional。     *)
(* ============================================================ *)

Definition qlb_lw_to_local (p : QPoly) : list Q := p.
Definition qlb_local_to_lw (p : list Q) : QPoly := p.

Lemma qlb_lw_local_roundtrip : forall p : QPoly,
  Id (qlb_local_to_lw (qlb_lw_to_local p)) p.
Proof. intros p. exact id_refl. Qed.

Lemma qlb_local_lw_roundtrip : forall p : list Q,
  Id (qlb_lw_to_local (qlb_local_to_lw p)) p.
Proof. intros p. exact id_refl. Qed.

(* ============================================================ *)
(* §2 求值机一致桥（核心件：Horner 同构，lw 系律 ⇒ 本地 pint_eval 面） *)
(*    方向约定：qlb_eval_agree 供「lw 代数 → 本地使用」方向；        *)
(*    逆方向由 Qeq 对称性即得，不另立件。                          *)
(* ============================================================ *)

Lemma qlb_eval_agree : forall (p : list Q) (x : Q),
  QeqT (pint_eval p x) (qpoly_eval p x).
Proof.
  intros p x. apply qeq_imp_qeqT.
  induction p as [|a p IH]; simpl.
  - apply Qeq_refl.
  - rewrite IH. apply Qeq_refl.
Qed.

(* QeqT 面工作件（证内改写弹药；语句面已为 QeqT，使用处经 qeqT_imp_qeq 转换后改写） *)
Lemma qlb_eval_agree_q : forall (p : list Q) (x : Q),
  QeqT (pint_eval p x) (qpoly_eval p x).
Proof. intros p x. exact (qlb_eval_agree p x). Qed.

(* ============================================================ *)
(* §3 点态律直使用桥（lw 13 件中供弹四件的 QeqT 重述；              *)
(*    每件一行桥接：qeq_imp_qeqT 挂 S02 运输件，证内直取 lw 原件）   *)
(* ============================================================ *)

(* 加法律（lw qpoly_eval_add 的 Set 面） *)
Lemma qlb_lw_eval_add : forall (p q : list Q) (x : Q),
  QeqT (qpoly_eval (qpoly_add p q) x)
       (qpoly_eval p x + qpoly_eval q x).
Proof. intros p q x. apply qeq_imp_qeqT. apply qpoly_eval_add. Qed.

(* 数乘律（lw qpoly_eval_scalar 的 Set 面） *)
Lemma qlb_lw_eval_scalar : forall (a : Q) (p : list Q) (x : Q),
  QeqT (qpoly_eval (qpoly_scalar a p) x) (a * qpoly_eval p x).
Proof. intros a p x. apply qeq_imp_qeqT. apply qpoly_eval_scalar. Qed.

(* 乘法求值律（lw qpoly_eval_mul 的 Set 面） *)
Lemma qlb_lw_eval_mul : forall (p q : list Q) (x : Q),
  QeqT (qpoly_eval (qpoly_mul p q) x)
       (qpoly_eval p x * qpoly_eval q x).
Proof. intros p q x. apply qeq_imp_qeqT. apply qpoly_eval_mul. Qed.

(* 乘法求值律落本地 pint_eval 面（经 §2 桥的平移形态——qpd 使用形） *)
Lemma qlb_lw_eval_mul_pint : forall (p q : list Q) (x : Q),
  QeqT (pint_eval (qpoly_mul p q) x)
       (pint_eval p x * pint_eval q x).
Proof.
  intros p q x. apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (qlb_eval_agree_q (qpoly_mul p q) x)).
  rewrite (qeqT_imp_qeq _ _ (qlb_eval_agree_q p x)). rewrite (qeqT_imp_qeq _ _ (qlb_eval_agree_q q x)).
  apply qpoly_eval_mul.
Qed.

(* 乘积律落本地 pint_eval 面（lw qpoly_deriv_mul 供给——                       *)
(*  (f·g)′ = f′·g + f·g′ 的 qpd 可使用形态，替代本地重复建律）                  *)
Lemma qlb_lw_deriv_mul_pint : forall (p q : list Q) (x : Q),
  QeqT (pint_eval (qpoly_deriv (qpoly_mul p q)) x)
       (pint_eval (qpoly_add (qpoly_mul (qpoly_deriv p) q)
                             (qpoly_mul p (qpoly_deriv q))) x).
Proof.
  intros p q x. apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (qlb_eval_agree_q (qpoly_deriv (qpoly_mul p q)) x)).
  rewrite (qeqT_imp_qeq _ _ (qlb_eval_agree_q (qpoly_add (qpoly_mul (qpoly_deriv p) q)
                                       (qpoly_mul p (qpoly_deriv q))) x)).
  apply qpoly_deriv_mul.
Qed.

(* ============================================================ *)
(* §4 真使用示范：lw 代数件 × qpd 除法引擎求值一致性               *)
(*    被除式由 lw 乘法代数（qpoly_mul）构造，经 qpd_synth 线性     *)
(*    综合除法引擎出（商, 余），三肢全 Set 面一致闭合。            *)
(* ============================================================ *)

Definition qlb_consume_pred (a : Q) (p : list Q) : Set :=
  qpd_lin_pred a p (fst (qpd_synth a p)) (snd (qpd_synth a p)).

(* 使用肢①：lw 乘积多项式整件接入 qpd 引擎，双正确性肢成立 *)
Lemma qlb_consume_lwprod_div : forall (f g : list Q) (a : Q),
  qlb_consume_pred a (qpoly_mul f g).
Proof.
  intros f g a. unfold qlb_consume_pred, qpd_lin_pred.
  exact (qpd_synth_sound a (qpoly_mul f g)).
Qed.

(* 使用肢②：度肢独立抽取（Id bool 面，可判定） *)
Lemma qlb_consume_lwprod_deg : forall (f g : list Q) (a : Q),
  qpd_deglt (snd (qpd_synth a (qpoly_mul f g)) :: nil) (a :: 1 :: nil).
Proof.
  intros f g a.
  pose proof (qpd_synth_sound a (qpoly_mul f g)) as H.
  unfold qpd_lin_pred in H.
  destruct H as [_ Hdeg].
  exact Hdeg.
Qed.

(* 使用肢③（主示范）：求值一致性——                                        *)
(*  lw 乘积的求值（pint_eval 面，经 §2 桥分解为 f·g 求值之积）              *)
(*  ＝ 除式求值 × 商求值 ＋ 余数，即 lw 代数在 qpd 引擎下语义无损。          *)
Lemma qlb_consume_lwprod_eval : forall (f g : list Q) (a x : Q),
  QeqT (pint_eval f x * pint_eval g x)
       (pint_eval (a :: 1 :: nil) x
        * pint_eval (fst (qpd_synth a (qpoly_mul f g))) x
        + snd (qpd_synth a (qpoly_mul f g))).
Proof.
  intros f g a x. apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (qlb_eval_agree_q f x)). rewrite (qeqT_imp_qeq _ _ (qlb_eval_agree_q g x)).
  rewrite <- (qpoly_eval_mul f g x).
  rewrite <- (qeqT_imp_qeq _ _ (qlb_eval_agree_q (qpoly_mul f g) x)).
  exact (qeqT_imp_qeq _ _ (fst (qpd_synth_sound a (qpoly_mul f g)) x)).
Qed.

(* 数值烟测（BF 模式：vm_compute 零公设定装）：                            *)
(*  f₁ = x²+1，g₁ = x+2 ⟹ lw 乘积 = x³+2x²+x+2；÷(x+1) ⟹ 商 x²+x 余 2。    *)
Definition qlb_f1 : list Q := 1 :: 0 :: 1 :: nil.
Definition qlb_g1 : list Q := 2 :: 1 :: nil.

Lemma qlb_smoke1_prod :
  Id (qpoly_mul qlb_f1 qlb_g1) (2 :: 1 :: 2 :: 1 :: nil).
Proof. vm_compute. exact id_refl. Qed.

Lemma qlb_smoke1_quot :
  Id (fst (qpd_synth 1 (qpoly_mul qlb_f1 qlb_g1))) (0 :: 1 :: 1 :: 0 :: nil).
Proof. vm_compute. exact id_refl. Qed.

Lemma qlb_smoke1_rem :
  QeqT (snd (qpd_synth 1 (qpoly_mul qlb_f1 qlb_g1))) 2.
Proof. vm_compute. exact id_refl. Qed.

(* 烟测语义面：使用肢③ 在 f₁/g₁/a=1 的实化（引擎原形逐字） *)
Lemma qlb_smoke1_sem : forall x : Q,
  QeqT (pint_eval qlb_f1 x * pint_eval qlb_g1 x)
       (pint_eval (1 :: 1 :: nil) x
        * pint_eval (fst (qpd_synth 1 (qpoly_mul qlb_f1 qlb_g1))) x
        + snd (qpd_synth 1 (qpoly_mul qlb_f1 qlb_g1))).
Proof. intros x. exact (qlb_consume_lwprod_eval qlb_f1 qlb_g1 1 x). Qed.

(* ============================================================ *)
(* §5 闭合：提取面 + Print Assumptions（红线四条逐条 PA）          *)
(* ============================================================ *)

Separate Extraction qlb_lw_to_local qlb_local_to_lw qlb_f1 qlb_g1.

Print Assumptions qlb_lw_local_roundtrip.
Print Assumptions qlb_local_lw_roundtrip.
Print Assumptions qlb_eval_agree.
Print Assumptions qlb_eval_agree_q.
Print Assumptions qlb_lw_eval_add.
Print Assumptions qlb_lw_eval_scalar.
Print Assumptions qlb_lw_eval_mul.
Print Assumptions qlb_lw_eval_mul_pint.
Print Assumptions qlb_lw_deriv_mul_pint.
Print Assumptions qlb_consume_lwprod_div.
Print Assumptions qlb_consume_lwprod_deg.
Print Assumptions qlb_consume_lwprod_eval.
Print Assumptions qlb_smoke1_prod.
Print Assumptions qlb_smoke1_quot.
Print Assumptions qlb_smoke1_rem.
Print Assumptions qlb_smoke1_sem.
