(* ============================================================ *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体替换为玩具证      *)
(*   （实质非平凡三口径），声明面与引用面零改动、零新增 Require、纯构造性闭合；    *)
(*   清单：zab_Z_align_nonneg（原 L89，5 句玩具证）、zab_Z_align_pos（原 L73，4 句）。 *)
(* ============================================================ *)
(* UpAblZpos.v —— Z_align 正性的抽象接口层消解件。使命：为 S05_AlignmentGRPO 的     *)
(*   抽象假设 Z_align_pos（lt zero Z_align，主节与迭代节同一导出形 lt zero (Z_align   *)
(*   reward beta beta_pos pi_ref)）给出独立消解件：在显式前提 Hsum_pos（forall f，     *)
(*   (forall s, lt zero (f s)) -> lt zero (sum_over_S f)）之下证明 lt zero (Z_align …)；  *)
(*   le zero (Z_align …) 的无条件伴件另件兑现，见 zab_Z_align_nonneg。条件形缘由：现     *)
(*   接口 sum_over_S 仅有 linear/add/ext/le/nonneg 字段，「和正」在本层不可证，故将该步   *)
(*   写成显式 forall 前提。数学内容：求和项逐项正链（zab_summand_pos）——pi_ref_pos 逐点  *)
(*   正 × exp_neg_pos 恒正，经 mult_positive 合成、inv_pos 换形，与 S05 的 Z_rel_pos 证明 *)
(*   链同构。升级方向：接口补 strict 求和正性字段（或 Real 层以 sumd_sum_pos 直接实例化）， *)
(*   显式前提即可消去。依赖（本库）：S01_BaseRing（接口与 sum_over_S 字段族）；           *)
(*   S05_AlignmentGRPO 只读对应，不改原件。构造性注记：纯构造性，语句面全 Set 层，零承认；  *)
(*   zab_ 前缀为本件专名。编译配方：Rocq 9.1 直调，unset COQLIB/ROCQLIB，cpu_guard 包裹。  *)
(* ============================================================ *)

Require Import S01_BaseRing.

Section ZabZPos.

Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpace RI}.
Context {SO : SumOver RI SS}.

Let R := @R RI.
Let S := @S RI SS.
Let zero := @zero RI.
Let mult := @mult RI.
Let opp := @opp RI.
Let inv_pos := @inv_pos RI.
Let le := @le RI.
Let lt := @lt RI.
Let exp_neg := @exp_neg RI.
Let sum_over_S := @sum_over_S RI SS SO.

(* S05 主节 Z_align 的出节实形同构（迭代节使用同形）：                  *)
(* Z_align := Σ_s pi_ref(s)·exp_neg(−r(s)/β)，beta_pos 为显式参。        *)
Definition zab_Z_align (reward : S -> R) (beta : R) (beta_pos : lt zero beta)
           (pi_ref : S -> R) : R :=
  sum_over_S (fun s => mult (pi_ref s)
                            (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))).

(* 求和项逐项正：pi_ref 逐点正 × exp_neg 恒正 ⟹ 乘积正（mult_positive 与 exp_neg_pos 合成）。 *)
Lemma zab_summand_pos :
  forall (reward : S -> R) (beta : R) (beta_pos : lt zero beta)
         (pi_ref : S -> R) (pi_ref_pos : forall s : S, lt zero (pi_ref s)),
    forall s : S,
      lt zero (mult (pi_ref s)
                    (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))).
Proof.
  intros reward beta beta_pos pi_ref pi_ref_pos s.
  apply mult_positive.
  - exact (pi_ref_pos s).
  - apply exp_neg_pos.
Qed.

(* 主定理（条件形）：显式前提 Hsum_pos 即 S05 中 sum_over_S 正性假设的实形， *)
(* 在此前提下消解 lt zero (Z_align …)（对应 S05 主节与迭代节同一接口假设，   *)
(* 语句逐字同形）。                                                       *)
Theorem zab_Z_align_pos :
  forall (reward : S -> R) (beta : R) (beta_pos : lt zero beta)
         (pi_ref : S -> R) (pi_ref_pos : forall s : S, lt zero (pi_ref s))
         (Hsum_pos : forall f : S -> R,
                       (forall s : S, lt zero (f s)) -> lt zero (sum_over_S f)),
    lt zero (zab_Z_align reward beta beta_pos pi_ref).
Proof.
  intros reward beta beta_pos pi_ref pi_ref_pos Hsum_pos.
  unfold zab_Z_align.
  apply Hsum_pos.
  exact (zab_summand_pos reward beta beta_pos pi_ref pi_ref_pos).
Qed.

(* 接口面无条件伴件（接口可证部分全量兑现）：不取求和正性前提，            *)
(* 仅用 sum_over_S_nonneg 接口字段，逐项正经 lt_le_iff 降为非负，          *)
(* 得整体非负——le zero (Z_align …) 无条件成立。                          *)
Theorem zab_Z_align_nonneg :
  forall (reward : S -> R) (beta : R) (beta_pos : lt zero beta)
         (pi_ref : S -> R) (pi_ref_pos : forall s : S, lt zero (pi_ref s)),
    le zero (zab_Z_align reward beta beta_pos pi_ref).
Proof.
  intros reward beta beta_pos pi_ref pi_ref_pos.
  unfold zab_Z_align.
  apply sum_over_S_nonneg.
  intro s.
  exact (lt_le_iff _ _           (inl (zab_summand_pos reward beta beta_pos pi_ref pi_ref_pos s))).
Qed.

End ZabZPos.

(* ---- 假设面自检（Print Assumptions） ---- *)
Print Assumptions zab_summand_pos.
Print Assumptions zab_Z_align_pos.
Print Assumptions zab_Z_align_nonneg.
