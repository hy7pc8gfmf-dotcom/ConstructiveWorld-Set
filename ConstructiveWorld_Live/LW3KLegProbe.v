(* LW3KLegProbe.v                                                        *)
(* 使命：M3 K 非零判据一般形勘形首件——零例多项式 -46 + 7t 在指数一阶     *)
(*       实例上使 K 面见证型空化，无条件一般形由值级机械证伪；另附锚例    *)
(*       泛函值 -265 被节点位移 5 整除的结构钉。                          *)
(* 依赖：LW3ETranscendental（只读正本）及其 Require 闭包 S02/S03/LW0/     *)
(*       LW1/LW2 系。                                                    *)
(* 对标：E-STAGING-LW3-PROBEPIN 坑4；E-STAGING-LW3-KNZWALL；             *)
(*       _tlw372 同配方绿件。                                            *)
(* 构造性：语句面全 Set（见证型空化定理一件、非零前提入住一件、透明路径  *)
(*       值钉两件），语句与前提位零 Prop；提取并集仅数据名，魔数=0；      *)
(*       禁引六族零命中。                                                *)
(* 编译配方：coqc 全路径 -q -Q . "" -Q ConstructiveWorld-Main/           *)
(*       ConstructiveWorld_vo ""，cpu_guard 包裹，SW2 双 export 全字面。 *)
Require Import QArith Lia Arith ZArith List.
From Stdlib Require Import QArith_base.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import LW0QPoly.
Require Import LW1ZPoly.
Require Import LW2Hermite.
Require Import LW2IntegMachine.
Require Import LW0FactGrowth.
Require Import LW2UpperBound.
Require Import LW2NivenInt.
Require Import LW3ETranscendental.

(* The zero instance: the polynomial -46 + 7 t, whose node functional    *)
(* vanishes at the first exponent instance, so the K witness type is     *)
(* empty there although the polynomial witness is inhabited.             *)
Definition p377 : zpoly := cons (-46)%Z (cons 7%Z nil).

(* The master nonzero witness is inhabited on this datum: the coefficient *)
(* at index zero compares below zero in the decidable integer order.     *)
Definition p377_nz : lw3_nz p377 := existT _ 0%nat tt.

(* The node functional of the built integrand vanishes: the boolean      *)
(* decision against zero takes the true branch on the transparent path.  *)
Definition lam377_zero :
  match Qeq_bool (lw2_lambda (lw3_nodecount p377 1)
                             (lw3_fbuild p377 (lw3_deg p377) 1))
                 (0 # 1)%Q
  with true => unit | false => Empty_set end := tt.

(* Collapse face: the K witness type is uninhabited at this instance,    *)
(* since the integer value rides the vanishing functional through the    *)
(* lambda bridge.  Together with p377_nz this certifies that the         *)
(* unconditional production of the K witness from the polynomial witness *)
(* admits no construction.                                               *)
Theorem kleg377_empty :
  lw3_qnz ((lw3_Kinst p377 1) # 1)%Q -> Empty_set.
Proof.
  intro Hk.
  assert (HzK : lw3_Kinst p377 1 = 0%Z).
  { assert (Eb : Qeq_bool (lw2_lambda (lw3_nodecount p377 1)
                                      (lw3_fbuild p377 (lw3_deg p377) 1))
                          0%Q = true)
      by (vm_compute; reflexivity).
    pose proof (qeqT_imp_qeq _ _ (lw3_Kinst_spec p377 1)) as Es.
    apply Qeq_bool_eq in Eb.
    unfold Qeq in Eb, Es.
    cbn [Qnum Qden] in Eb, Es.
    rewrite Z.mul_1_r in Eb, Es.
    rewrite Z.mul_0_l in Eb.
    rewrite Eb in Es.
    symmetry in Es.
    apply Z.mul_eq_0 in Es.
    destruct Es as [Hz | Hd].
    - exact Hz.
    - discriminate Hd. }
  unfold lw3_qnz in Hk.
  rewrite HzK in Hk.
  rewrite Qeq_bool_refl in Hk.
  cbn in Hk. exact Hk.
Qed.

(* Divisibility face on the recorded anchor: the functional value -265   *)
(* leaves no remainder under the node shift 5, the trace of the termwise *)
(* congruence of each derivative value against its coefficient factorial.*)
Definition p377b : zpoly := cons 1%Z (cons 1%Z nil).
Definition lam377b_div :
  match Z.eqb (Z.modulo
                 (Qnum (lw2_lambda (lw3_nodecount p377b 1)
                                   (lw3_fbuild p377b (lw3_deg p377b) 1)))
                 5%Z)
              0%Z
  with true => unit | false => Empty_set end := tt.

Print Assumptions p377_nz.
Print Assumptions kleg377_empty.
Print Assumptions lam377b_div.

Separate Extraction p377 p377b.
