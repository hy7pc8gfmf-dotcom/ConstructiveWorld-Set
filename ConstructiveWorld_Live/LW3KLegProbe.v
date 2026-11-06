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
Require Import S01_BaseRing.
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

(* The master nonzero witness on this datum: the coefficient at index    *)
(* zero compares nonzero in the decidable integer order, recorded as the *)
(* uniform Id verdict data (the decidable content of lw3_nz p377).       *)
Definition p377_nz :
  @Id bool false (Z.eqb (nth 0 p377 0%Z) 0%Z) := id_refl.

(* The node functional of the built integrand vanishes: the boolean      *)
(* decision against zero takes the true branch on the transparent path,  *)
(* recorded in the uniform Id carrier for the match-typed witness face.  *)
Definition lam377_zero :
  @Id bool true (Qeq_bool (lw2_lambda (lw3_nodecount p377 1)
                                       (lw3_fbuild p377 (lw3_deg p377) 1))
                          (0 # 1)%Q) := id_refl.

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
  (* Discharged inside a Prop-level False, which the extraction face      *)
  (* erases; False_rect then finishes the Set-sorted Empty_set            *)
  (* conclusion, so the extracted body renders without magic.             *)
  assert (HC : False).
  { unfold lw3_qnz in Hk.
    destruct (Qeq_bool ((lw3_Kinst p377 1) # 1)%Q 0%Q) eqn:Eb.
    - destruct Hk.
    - assert (Et : Qeq_bool ((lw3_Kinst p377 1) # 1)%Q 0%Q = true).
      { rewrite HzK. apply Qeq_bool_refl. }
      rewrite Et in Eb. discriminate Eb. }
  exact (False_rect Empty_set HC).
Qed.

(* Divisibility face on the recorded anchor: the functional value -265   *)
(* leaves no remainder under the node shift 5, the trace of the termwise *)
(* congruence of each derivative value against its coefficient factorial.*)
Definition p377b : zpoly := cons 1%Z (cons 1%Z nil).
(* The divisibility pin in the uniform Id carrier: the boolean decision  *)
(* "no remainder" holds on the transparent computation path.             *)
Definition lam377b_div :
  @Id bool true (Z.eqb (Z.modulo
                          (Qnum (lw2_lambda (lw3_nodecount p377b 1)
                                            (lw3_fbuild p377b (lw3_deg p377b) 1)))
                          5%Z)
                       0%Z) := id_refl.

Print Assumptions p377_nz.
Print Assumptions kleg377_empty.
Print Assumptions lam377b_div.

Separate Extraction p377 p377b.
