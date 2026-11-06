(* LW3KnzValue.v                                                         *)
(* 使命：Niven 辅助族 K 非零判据肢首砖——锚例上 K 面（lw3_Kinst）可判定    *)
(*       非零见证由 λ 面透明计算钉与 lw3_Kinst_spec 桥回传闭合；首项      *)
(*       系数面经生产件 lw3_niven_lc_nz 实例化闭合。                      *)
(* 依赖：LW3ETranscendental（只读正本）及其 Require 闭包 S02/S03/LW0/     *)
(*       LW1/LW2 系（PROBEPIN 卡 Require 全展开清单同面）。               *)
(* 对标：E-STAGING-LW3-PROBEPIN 坑4；E-STAGING-LW3-KNZWALL 判例           *)
(*       _tlw211_knz。                                                    *)
(* 构造性：语句面全 Set（lw3_qnz 见证三件＋Set 级值钉一件），语句与前提   *)
(*       位零 Prop；提取并集仅数据名 p372，魔数=0；禁引六族零命中。       *)
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

(* Anchor instance: the source polynomial 1 + t with scale one; its      *)
(* integer functional value is the recorded kernel value -265.           *)
Definition p372 : zpoly := cons 1%Z (cons 1%Z nil).

(* Lambda face: the functional value of the built integrand is nonzero   *)
(* on the fully transparent computation path.                            *)
Theorem lw3_lam372_nz :
  @Id bool false (Qeq_bool (lw2_lambda (lw3_nodecount p372 1)
                                        (lw3_fbuild p372 (lw3_deg p372) 1))
                           0%Q).
Proof.
  (* The anchor lambda value -265 is the leading coefficient (-1)^1 *    *)
  (* 265 of the Niven instance a = 0, b = 265 at n = 1, so the           *)
  (* production theorem lw3_niven_lc_nz supplies the decidable verdict   *)
  (* data directly.                                                      *)
  exact (lw3_niven_lc_nz 0 265 1 ltac:(intro Hz; discriminate Hz)).
Qed.

(* K face: the instantiated integer functional value carries the same    *)
(* decidable nonzero witness.  The witness rides the lambda face: the    *)
(* boolean decision on the lambda face computes to false on the          *)
(* transparent path, and the lambda bridge transports it onto the K      *)
(* face, so the true branch of the K-face decision is impossible.        *)
Theorem lw3_kinst372_nz :
  @Id bool false (Qeq_bool ((lw3_Kinst p372 1) # 1)%Q 0%Q).
Proof.
  (* The K-face value rides the lambda bridge: on the true branch the    *)
  (* Kinst specification transports the equation onto the lambda face,   *)
  (* whose transparent value -265 makes the branch absurd; the false     *)
  (* branch is the reflexivity data of the decidable verdict.            *)
  destruct (Qeq_bool ((lw3_Kinst p372 1) # 1)%Q 0%Q) eqn:E.
  - rewrite <- (qeqT_imp_qeq _ _ (lw3_Kinst_spec p372 1)) in E.
    assert (Ef : Qeq_bool (lw2_lambda (lw3_nodecount p372 1)
                                      (lw3_fbuild p372 (lw3_deg p372) 1)) 0%Q
                 = false)
      by (vm_compute; reflexivity).
    rewrite Ef in E. discriminate E.
  - exact id_refl.
Qed.

(* Lambda face value: the functional value agrees with the integer       *)
(* -265 over one; the decidable verdict is carried by the reflexivity    *)
(* data of the true branch on the transparent computation path.          *)
Definition lw3_lam372_val :
  @Id bool true (Qeq_bool (lw2_lambda (lw3_nodecount p372 1)
                                      (lw3_fbuild p372 (lw3_deg p372) 1))
                          ((-265) # 1)%Q) :=
  (* The anchor value -265 agrees on the transparent computation path,   *)
  (* so the decidable verdict is the reflexivity data of the true        *)
  (* branch.                                                             *)
  id_refl.

(* Leading-coefficient face: the nonzero witness of the source           *)
(* polynomial leading coefficient instantiates through the production    *)
(* theorem lw3_niven_lc_nz.                                              *)
Theorem lw3_lc372_nz :
  @Id bool false (Qeq_bool (lw0_coef (1 + 1) (lw2_niven_int_f 0 1 1)) 0%Q).
Proof.
  apply (lw3_niven_lc_nz 0 1 1).
  intro Hz. discriminate Hz.
Qed.

Print Assumptions lw3_lam372_nz.
Print Assumptions lw3_kinst372_nz.
Print Assumptions lw3_lam372_val.
Print Assumptions lw3_lc372_nz.

From Stdlib Require Import Extraction.
Separate Extraction p372.
