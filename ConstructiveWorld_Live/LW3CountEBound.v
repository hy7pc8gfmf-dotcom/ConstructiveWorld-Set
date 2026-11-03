(* LW3CountEBound.v                                                       *)
(* 使命：M3 主语句 count·E<1 前提的数值实例化——锚例多项式 1+t 上显式给出  *)
(*       尺度与衰减形标量，使节点计数因子乘标量严格小于一的严格比较在      *)
(*       Set 层以可判定比较闭合；并附逐节点界网格的数值边界件。            *)
(* 依赖：LW3ETranscendental（只读正本）及其 Require 闭包 S02/S03/LW0/     *)
(*       LW1/LW2 系；衰减常数正性取在库生产件 lw3_decay_E_posT。          *)
(* 对标：E-STAGING-LW3-PROBEPIN；E-STAGING-LW3-KNZWALL（纯 Set 值钉形    *)
(*       与透明归约工艺）；M0 数值门槛判例工艺。                           *)
(* 构造性：语句面全 Set（sigT 见证＋And 积形＋QltT 严格形），语句与前提   *)
(*       位零 Prop；提取并集仅数据名；禁引六族零命中。                     *)
(* 编译配方：coqc 全路径 -q -Q . "" -Q ConstructiveWorld-Main/            *)
(*       ConstructiveWorld_vo ""，cpu_guard 包裹，SW2 双 export 全字面。  *)
Require Import QArith Lia Arith ZArith List.
From Stdlib Require Import QArith.Qabs.
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

(* Anchor instance: the source polynomial one plus t, scale one.         *)
Definition p374 : zpoly := cons 1%Z (cons 1%Z nil).

(* Explicit instantiation data: the scale of the built integrand and the *)
(* derivative-order index of the registered decay form, whose value is   *)
(* the reciprocal of six factorial.                                      *)
Definition N374 : nat := 1.
Definition m374 : nat := 3.
Definition E374 : Q := lw3_decay_E m374.

(* The node-count factor of the master statement on the anchor instance. *)
Definition count374 : nat :=
  Datatypes.S (Datatypes.S (lw3_nodecount p374 N374)) *
  length (lw3_fbuild p374 (lw3_deg p374) N374).

(* Main brick: the count-times-E strict premise of the master statement  *)
(* is witnessed at the explicit pair, with positivity of the decay scale *)
(* supplied by the library production lemma and the strict comparison    *)
(* decided on the transparent computation path.                          *)
Theorem lw3_countE374 :
  sigT (fun N : nat => sigT (fun E : Q =>
    And (QltT 0%Q E)
        (QltT (lw0_q_of_nat (Datatypes.S (Datatypes.S (lw3_nodecount p374 N)) *
                            length (lw3_fbuild p374 (lw3_deg p374) N)) * E)
              (1 # 1)%Q))).
Proof.
  exists N374. exists E374. split.
  - exact (lw3_decay_E_posT m374).
  - vm_compute. constructor.
Qed.

(* Machine pin: the node-count factor equals twenty-four.                *)
Definition lw3_count374_val :
  match Qeq_bool (lw0_q_of_nat count374) (24 # 1)%Q with
  | true => unit
  | false => Empty_set
  end := tt.

(* Machine pin: the decay scalar equals the reciprocal of seven hundred  *)
(* twenty.                                                               *)
Definition lw3_e374_val :
  match Qeq_bool E374 (1 # 720)%Q with
  | true => unit
  | false => Empty_set
  end := tt.

(* Boundary datum: the decay scalar is strictly below the anchor value   *)
(* of the second derivative at the endpoint node five, so the decay      *)
(* scalar cannot serve the per-node bound premise at scale one.          *)
Theorem lw3_p3viol374 :
  QltT E374 (Qabs (qpoly_eval
    (qpoly_deriv_iter 2 (lw3_fbuild p374 (lw3_deg p374) N374))
    (lw2_node 5))).
Proof. vm_compute. constructor. Qed.

(* Boundary datum: the four endpoint values of the per-node grid at the  *)
(* top node five, machine-pinned; every derivative of the anchor         *)
(* integrand has nonnegative coefficients, so each grid value is bounded *)
(* by its endpoint value.                                                *)
Definition lw3_f5374_val :
  match Qeq_bool (qpoly_eval (lw3_fbuild p374 (lw3_deg p374) N374)
                             (lw2_node 5)) (150 # 1)%Q with
  | true => unit
  | false => Empty_set
  end := tt.

Definition lw3_f15_374_val :
  match Qeq_bool (qpoly_eval (qpoly_deriv_iter 1 (lw3_fbuild p374 (lw3_deg p374) N374))
                             (lw2_node 5)) (85 # 1)%Q with
  | true => unit
  | false => Empty_set
  end := tt.

Definition lw3_f25_374_val :
  match Qeq_bool (qpoly_eval (qpoly_deriv_iter 2 (lw3_fbuild p374 (lw3_deg p374) N374))
                             (lw2_node 5)) (32 # 1)%Q with
  | true => unit
  | false => Empty_set
  end := tt.

Definition lw3_f35_374_val :
  match Qeq_bool (qpoly_eval (qpoly_deriv_iter 3 (lw3_fbuild p374 (lw3_deg p374) N374))
                             (lw2_node 5)) (6 # 1)%Q with
  | true => unit
  | false => Empty_set
  end := tt.

(* Boundary datum: the node-count factor times the endpoint maximum      *)
(* value exceeds one, so at scale one the strict count premise forces a  *)
(* scalar strictly below the reciprocal of the node-count factor, while  *)
(* the per-node premise forces at least the endpoint maximum.            *)
Theorem lw3_joint374 :
  QltT (1 # 1)%Q (lw0_q_of_nat count374 * (150 # 1)%Q).
Proof. vm_compute. constructor. Qed.

Print Assumptions lw3_countE374.
Print Assumptions lw3_count374_val.
Print Assumptions lw3_e374_val.
Print Assumptions lw3_p3viol374.
Print Assumptions lw3_f5374_val.
Print Assumptions lw3_f15_374_val.
Print Assumptions lw3_f25_374_val.
Print Assumptions lw3_f35_374_val.
Print Assumptions lw3_joint374.

From Stdlib Require Import Extraction.
Separate Extraction p374 N374 m374 count374 E374.
