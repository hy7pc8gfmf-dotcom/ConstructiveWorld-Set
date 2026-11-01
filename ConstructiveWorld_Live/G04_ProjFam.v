(* ==========================================================================)
   G04_ProjFam.v — 投影算子族与投影 KL 代价分解
   使命: 抽象投影节（Z_P/Proj/proj_drop_zero/proj_keep_ge/proj_normalized/proj_uniform_full）、KL 分解节（KL_f/KL_P/KL_T 项与 proj_kl_cost）、KV/审计/最小 p 三实例节（kev_*_via_proj、Zaud_le_one_via_proj、minp_normalized_via_proj）及 tid 群结构的族命题。
   依赖: CW_ConstructiveWorld_219；Stdlib ZArith、ZArithRing、ZArith_dec、Arith、Lia。
   对标: 投影/正交分解下的 KL 散度代价分解（信息论投影不等式）。
   构造性: 全件 Qed 闭合、零承认词面、无经典逻辑；语句面以 Set 层承载（序谓词与等词为 Set 值，零 Prop 泄露）。
   编译配方: Rocq 9.1 直调 coqc -Q . "" -native-compiler no（vo 影子树同世界重编），cpu_guard 包裹限载。
   ========================================================================== *)

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

(* ---------- 通用助推（Set 层，规避根内 match-Hin 污染源） ---------- *)
(* Id 沿 Bool 的双子目标投影（UpKVEv kvev_id_transport 先例：       *)
(* 规避 destruct-eqn 对前提的静默代换）。                           *)
Lemma projp_id_transport : forall (A : Set) (x y : A) (M : A -> Set),
  M x -> Id x y -> M y.
Proof.
  intros A x y M m H. exact (match H with id_refl => m end).
Qed.

(* 单项 ≤ 全和（对 InT 推导本身归纳，Nil 矛盾支不进证明项——       *)
(* 根内 single_le_sum_aux 的空 match 提取会产生魔力包装，不复用）。  *)
Lemma projp_single_le_sum : forall (A : Set) (f : A -> Real) (x : A) (l : list A),
  InT x l -> (forall y : A, real_le real_zero (f y)) ->
  real_le (f x) (real_list_sum A f l).
Proof.
  intros A f x l Hin. induction Hin as [l0 | y l0 Hin IH].
  - intro Hnn. cbn [real_list_sum].
    apply real_le_plus_nonneg_r_aux.
    apply (real_list_sum_nonneg A f l0 Hnn).
  - intro Hnn. cbn [real_list_sum].
    apply (real_le_trans _ (real_list_sum A f l0)).
    + exact (IH Hnn).
    + apply (RealSetoid.real_le_id_r (real_list_sum A f l0)
               (real_plus (real_list_sum A f l0) (f y))
               (real_plus (f y) (real_list_sum A f l0))
               (real_plus_comm (real_list_sum A f l0) (f y))).
      apply real_le_plus_nonneg_r_aux. apply Hnn.
Qed.

(* ---------- 基础代数（real_eq 层小工具） ---------- *)

Lemma projp_plus_zero_l : forall x : Real, real_eq (real_plus real_zero x) x.
Proof.
  intro x. apply (real_eq_trans _ (real_plus x real_zero) _).
  - apply real_plus_comm.
  - apply real_plus_zero.
Qed.

Lemma projp_plus_zero_opp : forall a : Real, real_eq (real_plus (real_opp a) a) real_zero.
Proof.
  intro a. apply (real_eq_trans _ (real_plus a (real_opp a)) _).
  - apply real_plus_comm.
  - apply real_plus_opp.
Qed.

(* a − c == (a − b) + (b − c)（minus_split 的 Real 形态） *)
Lemma projp_minus_split : forall a b c : Real,
  real_eq (real_plus a (real_opp c))
          (real_plus (real_plus a (real_opp b)) (real_plus b (real_opp c))).
Proof.
  intros a b c.
  apply (real_eq_trans _ (real_plus a (real_plus (real_opp b) (real_plus b (real_opp c)))) _).
  - apply (RealSetoid.real_eq_plus_compat a (real_opp c) a
             (real_plus (real_opp b) (real_plus b (real_opp c)))
             (real_eq_refl a)
             (real_eq_sym _ _
               (real_eq_trans (real_plus (real_opp b) (real_plus b (real_opp c)))
                              (real_plus (real_plus (real_opp b) b) (real_opp c))
                              (real_opp c)
                              (real_plus_assoc (real_opp b) b (real_opp c))
                              (real_eq_trans
                                 (real_plus (real_plus (real_opp b) b) (real_opp c))
                                 (real_plus real_zero (real_opp c))
                                 (real_opp c)
                                 (RealSetoid.real_eq_plus_compat
                                    (real_plus (real_opp b) b) (real_opp c)
                                    real_zero (real_opp c)
                                    (projp_plus_zero_opp b) (real_eq_refl _))
                                 (projp_plus_zero_l (real_opp c)))))).
  - apply (real_plus_assoc a (real_opp b) (real_plus b (real_opp c))).
Qed.

(* (x − L) − x == −L（minus_plus_opp 的 Real 形态） *)
Lemma projp_minus_plus_opp : forall x L : Real,
  real_eq (real_plus (real_plus x (real_opp L)) (real_opp x)) (real_opp L).
Proof.
  intros x L.
  exact (real_eq_trans _ _ _
    (RealSetoid.real_eq_plus_compat (real_plus x (real_opp L)) (real_opp x)
                                    (real_plus (real_opp L) x) (real_opp x)
                                    (real_plus_comm x (real_opp L))
                                    (real_eq_refl (real_opp x)))
    (real_eq_trans _ _ _
      (real_eq_sym _ _ (real_plus_assoc (real_opp L) x (real_opp x)))
      (real_eq_trans _ _ _
        (RealSetoid.real_eq_plus_compat (real_opp L) (real_plus x (real_opp x))
                                        (real_opp L) real_zero
                                        (real_eq_refl (real_opp L))
                                        (real_plus_opp x))
        (real_eq_trans _ _ _
          (real_plus_comm (real_opp L) real_zero)
          (projp_plus_zero_l (real_opp L)))))).
Qed.

(* log inv == −log x（log_inv_one_inv 的 Real 层形态） *)
Lemma projp_log_inv_neg : forall (x : Real) (Hx : real_lt real_zero x),
  real_eq (real_log (real_inv_pos x Hx) (real_inv_pos_pos x Hx))
          (real_opp (real_log x Hx)).
Proof.
  intros x Hx.
  assert (Hsum : real_eq (real_plus (real_log x Hx)
                                    (real_log (real_inv_pos x Hx) (real_inv_pos_pos x Hx)))
                         real_zero).
  { apply (real_eq_trans _ (real_log (real_mult x (real_inv_pos x Hx))
                                     (real_mult_positive x (real_inv_pos x Hx) Hx
                                       (real_inv_pos_pos x Hx))) _).
    - apply (real_eq_sym _ _ (real_log_mult x (real_inv_pos x Hx) Hx (real_inv_pos_pos x Hx))).
    - apply (real_eq_trans _ (real_log real_one real_lt_zero_one) _).
      + apply (real_log_wd (real_mult x (real_inv_pos x Hx)) real_one
                 (real_mult_positive x (real_inv_pos x Hx) Hx (real_inv_pos_pos x Hx))
                 real_lt_zero_one (real_inv_pos_correct x Hx)).
      + apply (real_log_one real_lt_zero_one). }
  assert (Hdir : real_eq (real_opp (real_log x Hx))
                         (real_log (real_inv_pos x Hx) (real_inv_pos_pos x Hx))).
  { apply (real_eq_trans _ (real_plus (real_opp (real_log x Hx)) real_zero) _).
    - apply (real_eq_sym _ _ (real_plus_zero (real_opp (real_log x Hx)))).
    - apply (real_eq_trans _ (real_plus (real_opp (real_log x Hx))
                                        (real_plus (real_log x Hx)
                                                   (real_log (real_inv_pos x Hx)
                                                             (real_inv_pos_pos x Hx)))) _).
      + apply (RealSetoid.real_eq_plus_compat (real_opp (real_log x Hx)) real_zero
                 (real_opp (real_log x Hx))
                 (real_plus (real_log x Hx)
                            (real_log (real_inv_pos x Hx) (real_inv_pos_pos x Hx)))
                 (real_eq_refl _)
                 (real_eq_sym (real_plus (real_log x Hx)
                                         (real_log (real_inv_pos x Hx)
                                                   (real_inv_pos_pos x Hx)))
                              real_zero Hsum)).
      + apply (real_eq_trans _
                 (real_plus (real_plus (real_opp (real_log x Hx)) (real_log x Hx))
                            (real_log (real_inv_pos x Hx) (real_inv_pos_pos x Hx))) _).
        * apply (real_plus_assoc (real_opp (real_log x Hx)) (real_log x Hx)
                    (real_log (real_inv_pos x Hx) (real_inv_pos_pos x Hx))).
        * apply (real_eq_trans _ (real_plus real_zero
                                   (real_log (real_inv_pos x Hx) (real_inv_pos_pos x Hx))) _).
          -- apply (RealSetoid.real_eq_plus_compat
                       (real_plus (real_opp (real_log x Hx)) (real_log x Hx))
                       (real_log (real_inv_pos x Hx) (real_inv_pos_pos x Hx))
                       real_zero (real_log (real_inv_pos x Hx) (real_inv_pos_pos x Hx))
                       (projp_plus_zero_opp (real_log x Hx)) (real_eq_refl _)).
          -- apply projp_plus_zero_l. }
  apply (real_eq_sym _ _ Hdir).
Qed.

(* ============================================================ *)
(* 母 Section：抽象投影核（四象归一的规范形）                      *)
(*   Z_P = 保留质量；Proj = 保留支 f·inv(Z_P)、逐出支零。          *)
(* ============================================================ *)
Section AbstractProjection.

Variable I : Set.                          (* 索引类型 *)
Variable f : I -> Real.                    (* 被投影权重 *)
Variable P : I -> bool.                    (* 保留谓词 *)
Variable idx : list I.                     (* 枚举 *)
Variable f_norm : real_eq (real_list_sum I f idx) real_one.   (* f 归一化 *)
Variable f_pos : forall i : I, real_lt real_zero (f i).       (* f 逐点正 *)
Variable P_witness : sigT (fun i : I => And (Id (P i) true) (InT i idx)).

(* 保留质量（三象分母的公共形态：Σ if P then f else 0） *)
Definition Z_P : Real :=
  real_list_sum I (fun i : I => if P i then f i else real_zero) idx.

(* ---------- 件 0a：Z_P > 0（由 P 有点 + f_pos + single_le_sum 证明） ---------- *)
(* UpKVEv Z_keep_pos 同款——ZP_pos 由 Variable 升级为定理。           *)
Lemma Z_P_entry_nonneg : forall (y : I),
  real_le real_zero (if P y then f y else real_zero).
Proof.
  intro y. destruct (P y).
  - apply real_le_from_lt_aux. apply f_pos.
  - apply real_le_refl.
Qed.

Theorem ZP_pos : real_lt real_zero Z_P.
Proof.
  destruct P_witness as [i0 [Hk0 Hin0]].
  assert (Hlt0 : real_lt real_zero (if P i0 then f i0 else real_zero)).
  { apply (projp_id_transport bool true (P i0)
             (fun b : bool => real_lt real_zero (if b then f i0 else real_zero))).
    - exact (f_pos i0).
    - exact (id_sym Hk0). }
  assert (Hle : real_le (if P i0 then f i0 else real_zero) Z_P).
  { apply (projp_single_le_sum I
             (fun y : I => if P y then f y else real_zero) i0 idx Hin0).
    intro y. apply Z_P_entry_nonneg. }
  destruct Hle as [Hlt | Heq].
  - exact (real_lt_trans real_zero
             (if P i0 then f i0 else real_zero) Z_P Hlt0 Hlt).
  - exact (real_lt_eq_lt real_zero
             (if P i0 then f i0 else real_zero) Z_P Hlt0 Heq).
Qed.

(* ---------- 件 0b：Z_P ≤ 1（保留子集和 ≤ 全和 + f_norm 桥） ---------- *)
Theorem ZP_le_one : real_le Z_P real_one.
Proof.
  apply (real_le_trans _ (real_list_sum I f idx)).
  - apply (real_list_sum_le I
             (fun i : I => if P i then f i else real_zero) f idx).
    intro y. destruct (P y).
    + apply real_le_refl.
    + apply real_le_from_lt_aux. apply f_pos.
  - apply (RealSetoid.real_eq_le _ _). exact f_norm.
Qed.

(* 保留支形态（Proj 的 keep 支；log 证书的载体） *)
Definition keep_form (i : I) : Real :=
  real_mult (f i) (real_inv_pos Z_P ZP_pos).

(* keep 支正性证书（透明 Definition——log 项的随身证书） *)
Definition keep_form_pos (i : I) : real_lt real_zero (keep_form i) :=
  real_mult_positive (f i) (real_inv_pos Z_P ZP_pos)
                     (f_pos i) (real_inv_pos_pos Z_P ZP_pos).

(* 投影核（母形态：if P i then f i·inv(Z_P) else 0） *)
Definition Proj (i : I) : Real :=
  if P i then real_mult (f i) (real_inv_pos Z_P ZP_pos) else real_zero.

(* ---------- 件 3：逐出支归零 ---------- *)
Theorem proj_drop_zero : forall i : I,
  Id (P i) false -> real_eq (Proj i) real_zero.
Proof.
  intros i Hb.
  apply (projp_id_transport bool false (P i)
           (fun b : bool =>
              real_eq (if b then
                         real_mult (f i) (real_inv_pos Z_P ZP_pos)
                       else real_zero)
                 real_zero)).
  - apply real_eq_refl.
  - exact (id_sym Hb).
Qed.

(* ---------- keep 支放大器：f i ≤ f i·inv(Z_P)（Z_P ≤ 1 + inv 反单调） ---------- *)
Lemma proj_keep_form_ge : forall i : I,
  real_le (f i) (real_mult (f i) (real_inv_pos Z_P ZP_pos)).
Proof.
  intro i.
  apply (real_le_trans _ (real_mult (f i) (real_inv_pos real_one real_lt_zero_one))).
  - (* f i == f·inv(1) 的 eq→le 桥 *)
    apply (RealSetoid.real_eq_le (f i)
             (real_mult (f i) (real_inv_pos real_one real_lt_zero_one))).
    apply real_eq_sym.
    apply (real_eq_trans _ (real_mult (f i) real_one) _).
    + apply (RealSetoid.real_eq_mult_compat
                (f i) (real_inv_pos real_one real_lt_zero_one)
                (f i) real_one).
      * apply real_eq_refl.
      * apply (real_eq_trans _
                  (real_mult real_one (real_inv_pos real_one real_lt_zero_one)) _).
        -- apply real_eq_sym. apply b4_one_mult.
        -- apply real_inv_pos_correct.
    + apply real_mult_one.
  - apply (real_le_mult_compat_r (f i)
             (real_inv_pos real_one real_lt_zero_one)
             (real_inv_pos Z_P ZP_pos)).
    + apply real_le_from_lt_aux. apply f_pos.
    + apply (real_inv_pos_le_compat Z_P real_one ZP_pos real_lt_zero_one).
      apply ZP_le_one.
Qed.

(* ---------- 件 2：保留者放大（keep 支 f ≤ Proj） ---------- *)
Theorem proj_keep_ge : forall i : I,
  Id (P i) true -> real_le (f i) (Proj i).
Proof.
  intros i Hb.
  apply (projp_id_transport bool true (P i)
           (fun b : bool =>
              real_le (f i)
                (if b then real_mult (f i) (real_inv_pos Z_P ZP_pos)
                 else real_zero))).
  - apply proj_keep_form_ge.
  - exact (id_sym Hb).
Qed.

(* ---------- 件 1：行归一化 Σ Proj == 1 ---------- *)
Theorem proj_normalized :
  real_eq (real_list_sum I (fun i : I => Proj i) idx) real_one.
Proof.
  (* 第一步：逐点改写 Proj 为 g(i)·inv(Z_P)，drop 支经 0·x == 0 归零 *)
  apply (real_eq_trans _
           (real_list_sum I
              (fun i : I =>
                 real_mult (if P i then f i else real_zero)
                           (real_inv_pos Z_P ZP_pos))
              idx) _).
  { apply (real_list_sum_ext I (fun i : I => Proj i) _ idx).
    intro y. destruct (P y) eqn:Hk.
    - unfold Proj. rewrite Hk. apply real_eq_refl.
    - unfold Proj. rewrite Hk.
      apply (real_eq_trans _
               (real_mult (real_inv_pos Z_P ZP_pos) real_zero) _).
      + apply real_eq_sym. apply real_mult_zero.
      + apply real_mult_comm. }
  (* 第二步：linear_r 提取常数 inv(Z_P) *)
  apply (real_eq_trans _
           (real_mult (real_inv_pos Z_P ZP_pos) Z_P) _).
  { apply (real_list_sum_linear_r I
             (real_inv_pos Z_P ZP_pos)
             (fun i : I => if P i then f i else real_zero) idx). }
  (* 第三步：inv(Z_P)·Z_P == 1（comm 桥 + real_inv_pos_correct） *)
  apply (real_eq_trans _ (real_mult Z_P (real_inv_pos Z_P ZP_pos)) _).
  - apply real_mult_comm.
  - apply real_inv_pos_correct.
Qed.

(* ---------- 件 5：minorization 传送（δ·u ≤ f ⟹ δ·u ≤ Proj，无条件式） ---------- *)
Variable u : I -> Real.                    (* 参考分布 *)
Variable delta : Real.
Variable delta_minor : forall i : I,
  real_le (real_mult delta (u i)) (f i).

Theorem proj_minor_uncond : forall i : I,
  real_le (if P i then real_mult delta (u i) else real_zero) (Proj i).
Proof.
  intro i. destruct (P i) eqn:Hk.
  - unfold Proj. rewrite Hk.
    apply (real_le_trans _ (f i)).
    + apply delta_minor.
    + apply proj_keep_form_ge.
  - unfold Proj. rewrite Hk. apply real_le_refl.
Qed.

(* ---------- 件 6：退化象（P ≡ true ⟹ Proj ≡ f；温度极限象的推论级连接） ---------- *)
Theorem proj_uniform_full :
  (forall i : I, Id (P i) true) -> forall i : I, real_eq (Proj i) (f i).
Proof.
  intro P_all. intro i.
  assert (HZ1 : real_eq Z_P real_one).
  { apply (real_eq_trans _ (real_list_sum I f idx) _).
    - apply (real_list_sum_ext I
               (fun i : I => if P i then f i else real_zero) f idx).
      intro y. apply (projp_id_transport bool true (P y)
                 (fun b : bool => real_eq (if b then f y else real_zero) (f y))).
      + apply real_eq_refl.
      + exact (id_sym (P_all y)).
    - exact f_norm. }
  apply (projp_id_transport bool true (P i)
           (fun b : bool =>
              real_eq (if b then real_mult (f i) (real_inv_pos Z_P ZP_pos)
                       else real_zero)
                 (f i))).
  - apply (real_eq_trans _
             (real_mult (f i) (real_inv_pos real_one real_lt_zero_one)) _).
    + apply (RealSetoid.real_eq_mult_compat
                (f i) (real_inv_pos Z_P ZP_pos)
                (f i) (real_inv_pos real_one real_lt_zero_one)).
      * apply real_eq_refl.
      * apply (real_inv_pos_ext Z_P real_one ZP_pos real_lt_zero_one HZ1).
    + apply (real_eq_trans _ (real_mult (f i) real_one) _).
      * apply (RealSetoid.real_eq_mult_compat
                  (f i) (real_inv_pos real_one real_lt_zero_one) (f i) real_one).
        -- apply real_eq_refl.
        -- apply (real_eq_trans _
                      (real_mult real_one (real_inv_pos real_one real_lt_zero_one)) _).
           ++ apply real_eq_sym. apply b4_one_mult.
           ++ apply real_inv_pos_correct.
      * apply real_mult_one.
  - exact (id_sym (P_all i)).
Qed.

End AbstractProjection.

(* ============================================================ *)
(* 件 4：代价恒等（母形态，root kl_sum_split/kl_tail_eval 的       *)
(*   Real 层 list 版）。KL 项按「log 正性证书随身」纪律定义：       *)
(*   对 Proj 的 KL 用掩码形态（keep 支即 keep_form，delta 相等）    *)
(*   规避 drop 支 log 零前提；fail 支由 Hq_fail 归零。             *)
(* ============================================================ *)
Section AbstractKL.

Variable I : Set.
Variable f : I -> Real.
Variable P : I -> bool.
Variable idx : list I.
Variable f_norm : real_eq (real_list_sum I f idx) real_one.
Variable f_pos : forall i : I, real_lt real_zero (f i).
Variable P_witness : sigT (fun i : I => And (Id (P i) true) (InT i idx)).

Definition ZK : Real := Z_P I f P idx.
Definition keepK (i : I) : Real := keep_form I f P idx f_pos P_witness i.
Definition keepK_pos (i : I) : real_lt real_zero (keepK i) :=
  keep_form_pos I f P idx f_pos P_witness i.

(* KL 逐项（q‖f：无条件正性；q‖Proj 与尾项：P 掩码形态） *)
Definition KL_f_term (q : I -> Real) (Hq : forall i : I, real_lt real_zero (q i))
  (i : I) : Real :=
  real_mult (q i) (real_plus (real_log (q i) (Hq i))
                             (real_opp (real_log (f i) (f_pos i)))).
Definition KL_P_term (q : I -> Real) (Hq : forall i : I, real_lt real_zero (q i))
  (i : I) : Real :=
  if P i then
    real_mult (q i) (real_plus (real_log (q i) (Hq i))
                               (real_opp (real_log (keepK i) (keepK_pos i))))
  else real_zero.
Definition KL_T_term (q : I -> Real) (i : I) : Real :=
  if P i then
    real_mult (q i) (real_plus (real_log (keepK i) (keepK_pos i))
                               (real_opp (real_log (f i) (f_pos i))))
  else real_zero.
Definition KL_f_masked (q : I -> Real) (Hq : forall i : I, real_lt real_zero (q i))
  (i : I) : Real :=
  if P i then KL_f_term q Hq i else real_zero.

Definition KLqf (q : I -> Real) (Hq : forall i : I, real_lt real_zero (q i)) : Real :=
  real_list_sum I (KL_f_term q Hq) idx.
Definition KLfm (q : I -> Real) (Hq : forall i : I, real_lt real_zero (q i)) : Real :=
  real_list_sum I (KL_f_masked q Hq) idx.
Definition KLqp (q : I -> Real) (Hq : forall i : I, real_lt real_zero (q i)) : Real :=
  real_list_sum I (KL_P_term q Hq) idx.
Definition KLqt (q : I -> Real) : Real :=
  real_list_sum I (KL_T_term q) idx.

(* 第 1 步：桥——兼容 q 在 drop 支归零后，无掩码和 == 掩码和 *)
Lemma proj_kl_bridge : forall (q : I -> Real)
  (Hq : forall i : I, real_lt real_zero (q i))
  (Hq_fail : forall i : I, Id (P i) false -> real_eq (q i) real_zero),
  real_eq (KLqf q Hq) (KLfm q Hq).
Proof.
  intros q Hq Hq_fail.
  apply (real_list_sum_ext I (KL_f_term q Hq) (KL_f_masked q Hq) idx).
  intro y. unfold KL_f_masked. destruct (P y) eqn:Hb.
  - apply real_eq_refl.
  - assert (Hid : Id (P y) false). { rewrite Hb. apply id_refl. }
    pose proof (Hq_fail y Hid) as Hq0.
    apply (real_eq_trans _ (real_mult real_zero
               (real_plus (real_log (q y) (Hq y))
                          (real_opp (real_log (f y) (f_pos y))))) _).
    + apply (RealSetoid.real_eq_mult_compat (q y)
               (real_plus (real_log (q y) (Hq y))
                          (real_opp (real_log (f y) (f_pos y))))
               real_zero
               (real_plus (real_log (q y) (Hq y))
                          (real_opp (real_log (f y) (f_pos y))))
               Hq0 (real_eq_refl _)).
    + apply (real_eq_trans _
               (real_mult (real_plus (real_log (q y) (Hq y))
                                     (real_opp (real_log (f y) (f_pos y))))
                          real_zero) _).
      * apply real_mult_comm.
      * apply real_mult_zero.
Qed.

(* 第 2 步：掩码逐点分解（keep 支经 minus_split+distrib；drop 支零和零） *)
Lemma proj_kl_pointwise_split : forall (q : I -> Real)
  (Hq : forall i : I, real_lt real_zero (q i)) (i : I),
  real_eq (KL_f_masked q Hq i) (real_plus (KL_P_term q Hq i) (KL_T_term q i)).
Proof.
  intros q Hq i. unfold KL_f_masked, KL_P_term, KL_T_term.
  destruct (P i).
  - apply (real_eq_trans _
             (real_mult (q i)
                (real_plus
                   (real_plus (real_log (q i) (Hq i))
                              (real_opp (real_log (keepK i) (keepK_pos i))))
                   (real_plus (real_log (keepK i) (keepK_pos i))
                              (real_opp (real_log (f i) (f_pos i)))))) _).
    + apply (RealSetoid.real_eq_mult_compat (q i)
               (real_plus (real_log (q i) (Hq i))
                          (real_opp (real_log (f i) (f_pos i))))
               (q i)
               (real_plus
                  (real_plus (real_log (q i) (Hq i))
                             (real_opp (real_log (keepK i) (keepK_pos i))))
                  (real_plus (real_log (keepK i) (keepK_pos i))
                             (real_opp (real_log (f i) (f_pos i)))))
               (real_eq_refl _)
               (projp_minus_split (real_log (q i) (Hq i))
                                  (real_log (keepK i) (keepK_pos i))
                                  (real_log (f i) (f_pos i)))).
    + apply (real_distrib (q i)
               (real_plus (real_log (q i) (Hq i))
                          (real_opp (real_log (keepK i) (keepK_pos i))))
               (real_plus (real_log (keepK i) (keepK_pos i))
                          (real_opp (real_log (f i) (f_pos i))))).
  - apply real_eq_sym. apply real_plus_zero.
Qed.

(* 第 3 步：和级分解 Σ(q‖f 掩码) == Σ(q‖Proj) + Σ 尾项 *)
Lemma proj_kl_split_sum : forall (q : I -> Real)
  (Hq : forall i : I, real_lt real_zero (q i)),
  real_eq (KLfm q Hq) (real_plus (KLqp q Hq) (KLqt q)).
Proof.
  intros q Hq.
  apply (real_eq_trans _
           (real_list_sum I
              (fun i : I => real_plus (KL_P_term q Hq i) (KL_T_term q i)) idx) _).
  - apply (real_list_sum_ext I (KL_f_masked q Hq)
             (fun i : I => real_plus (KL_P_term q Hq i) (KL_T_term q i)) idx).
    exact (proj_kl_pointwise_split q Hq).
  - apply (real_list_sum_add I (KL_P_term q Hq) (KL_T_term q) idx).
Qed.

(* 第 4 步：尾项逐点 == (−log Z_P)·q（keep 支经 log_mult+log_inv_neg；
   drop 支 q 归零两侧归零，照抄根 kl_tail_eval 骨架） *)
Lemma proj_kl_tail_pt : forall (q : I -> Real)
  (Hq_fail : forall i : I, Id (P i) false -> real_eq (q i) real_zero) (i : I),
  real_eq (KL_T_term q i)
          (real_mult (real_opp (real_log ZK (ZP_pos I f P idx f_pos P_witness)))
                     (q i)).
Proof.
  intros q Hq_fail i. unfold KL_T_term. destruct (P i) eqn:Hb.
  - assert (HL : real_eq (real_log (keepK i) (keepK_pos i))
                         (real_plus (real_log (f i) (f_pos i))
                                    (real_opp (real_log ZK
                                                (ZP_pos I f P idx f_pos P_witness))))).
    { apply (real_eq_trans _
               (real_log (real_mult (f i) (real_inv_pos ZK (ZP_pos I f P idx f_pos P_witness)))
                         (real_mult_positive (f i) (real_inv_pos ZK (ZP_pos I f P idx f_pos P_witness))
                                             (f_pos i)
                                             (real_inv_pos_pos ZK (ZP_pos I f P idx f_pos P_witness)))) _).
      - apply (real_log_wd (keepK i)
                 (real_mult (f i) (real_inv_pos ZK (ZP_pos I f P idx f_pos P_witness)))
                 (keepK_pos i)
                 (real_mult_positive (f i) (real_inv_pos ZK (ZP_pos I f P idx f_pos P_witness))
                                     (f_pos i)
                                     (real_inv_pos_pos ZK (ZP_pos I f P idx f_pos P_witness)))
                 (real_eq_refl (real_mult (f i) (real_inv_pos ZK (ZP_pos I f P idx f_pos P_witness))))).
      - apply (real_eq_trans _
                 (real_plus (real_log (f i) (f_pos i))
                            (real_log (real_inv_pos ZK (ZP_pos I f P idx f_pos P_witness))
                                      (real_inv_pos_pos ZK (ZP_pos I f P idx f_pos P_witness)))) _).
        + apply (real_log_mult (f i) (real_inv_pos ZK (ZP_pos I f P idx f_pos P_witness))
                   (f_pos i) (real_inv_pos_pos ZK (ZP_pos I f P idx f_pos P_witness))).
        + apply (RealSetoid.real_eq_plus_compat _ _ _ _ (real_eq_refl _)
                   (projp_log_inv_neg ZK (ZP_pos I f P idx f_pos P_witness))). }
    assert (Hmid : real_eq (real_plus (real_log (keepK i) (keepK_pos i))
                                      (real_opp (real_log (f i) (f_pos i))))
                           (real_opp (real_log ZK (ZP_pos I f P idx f_pos P_witness)))).
    { apply (real_eq_trans _
               (real_plus (real_plus (real_log (f i) (f_pos i))
                                     (real_opp (real_log ZK (ZP_pos I f P idx f_pos P_witness))))
                          (real_opp (real_log (f i) (f_pos i)))) _).
      - apply (RealSetoid.real_eq_plus_compat _ _ _ _ HL (real_eq_refl _)).
      - apply projp_minus_plus_opp. }
    apply (real_eq_trans _
             (real_mult (q i)
                (real_opp (real_log ZK (ZP_pos I f P idx f_pos P_witness)))) _).
    + apply (RealSetoid.real_eq_mult_compat (q i)
               (real_plus (real_log (keepK i) (keepK_pos i))
                          (real_opp (real_log (f i) (f_pos i))))
               (q i)
               (real_opp (real_log ZK (ZP_pos I f P idx f_pos P_witness)))
               (real_eq_refl _) Hmid).
    + apply real_mult_comm.
  - assert (Hid : Id (P i) false). { rewrite Hb. apply id_refl. }
    pose proof (Hq_fail i Hid) as Hq0.
    apply (real_eq_trans _
             (real_mult (real_opp (real_log ZK (ZP_pos I f P idx f_pos P_witness)))
                        real_zero) _).
    + apply real_eq_sym. apply real_mult_zero.
    + apply (RealSetoid.real_eq_mult_compat
               (real_opp (real_log ZK (ZP_pos I f P idx f_pos P_witness)))
               real_zero
               (real_opp (real_log ZK (ZP_pos I f P idx f_pos P_witness)))
               (q i) (real_eq_refl _) (real_eq_sym (q i) real_zero Hq0)).
Qed.

(* 第 5 步：尾项求值 Σ 尾 == −log Z_P（ext + linear + 归一化消去） *)
Lemma proj_kl_tail_eval : forall (q : I -> Real)
  (Hq_norm : real_eq (real_list_sum I q idx) real_one)
  (Hq_fail : forall i : I, Id (P i) false -> real_eq (q i) real_zero),
  real_eq (KLqt q) (real_opp (real_log ZK (ZP_pos I f P idx f_pos P_witness))).
Proof.
  intros q Hq_norm Hq_fail.
  apply (real_eq_trans _
           (real_list_sum I
              (fun i : I => real_mult (real_opp (real_log ZK (ZP_pos I f P idx f_pos P_witness)))
                                      (q i)) idx) _).
  - apply (real_list_sum_ext I (KL_T_term q)
             (fun i : I => real_mult (real_opp (real_log ZK (ZP_pos I f P idx f_pos P_witness)))
                                     (q i)) idx).
    intro w. exact (proj_kl_tail_pt q Hq_fail w).
  - apply (real_eq_trans _
             (real_mult (real_opp (real_log ZK (ZP_pos I f P idx f_pos P_witness)))
                        (real_list_sum I q idx)) _).
    + apply (real_list_sum_linear I
               (real_opp (real_log ZK (ZP_pos I f P idx f_pos P_witness))) q idx).
    + apply (real_eq_trans _
               (real_mult (real_opp (real_log ZK (ZP_pos I f P idx f_pos P_witness)))
                          real_one) _).
      * apply (RealSetoid.real_eq_mult_compat
                 (real_opp (real_log ZK (ZP_pos I f P idx f_pos P_witness)))
                 (real_list_sum I q idx)
                 (real_opp (real_log ZK (ZP_pos I f P idx f_pos P_witness)))
                 real_one (real_eq_refl _) Hq_norm).
      * apply real_mult_one.
Qed.

(* 件 4（主件·代价恒等）：KL(q‖f) == KL(q‖Proj) + (−log Z_P)。
   审计/截断/逐出的信息代价 = 保留质量亏损对数，一次证明三象通用。 *)
Theorem proj_kl_cost : forall (q : I -> Real)
  (Hq_norm : real_eq (real_list_sum I q idx) real_one)
  (Hq_pos : forall i : I, real_lt real_zero (q i))
  (Hq_fail : forall i : I, Id (P i) false -> real_eq (q i) real_zero),
   real_eq (KLqf q Hq_pos)
          (real_plus (KLqp q Hq_pos)
                     (real_opp (real_log ZK (ZP_pos I f P idx f_pos P_witness)))).
Proof.
  intros q Hq_norm Hq_pos Hq_fail.
  apply (real_eq_trans _ (real_plus (KLqp q Hq_pos) (KLqt q)) _).
  - apply (real_eq_trans _ (KLfm q Hq_pos) _).
    + exact (proj_kl_bridge q Hq_pos Hq_fail).
    + exact (proj_kl_split_sum q Hq_pos).
  - apply (RealSetoid.real_eq_plus_compat _ _ _ _ (real_eq_refl _)
             (proj_kl_tail_eval q Hq_norm Hq_fail)).
Qed.

End AbstractKL.

(* ============================================================ *)
(* 实例接入（三象复原）。判据：实例引理证明体短于原证明体。          *)
(* 接缝注记见各 Section 头注释。                                   *)
(* ============================================================ *)

(* ---------- 实例 A：KV 逐出（UpKVEv 的行归一化/件 0/2/2b/3 复原） ----------
   接缝：母签名与 UpKVEv 世界逐参对齐（I:=Tok，f:=K s 固定行，P:=keep）。
   f_norm:=Krow s、f_pos:=Kpos s、P_witness:=keep_nonempty 直通；           *)
Section InstKV.

Variables (Tok : Set) (states : list Tok) (K : Tok -> Tok -> Real)
          (keep : Tok -> bool).
Variable Krow : forall s : Tok,
  real_eq (real_list_sum Tok (fun s' : Tok => K s s') states) real_one.
Variable Kpos : forall s s' : Tok, real_lt real_zero (K s s').
Variable keep_nonempty : sigT (fun s0 : Tok => And (Id (keep s0) true) (InT s0 states)).

Definition Zkv (s : Tok) : Real :=
  real_list_sum Tok (fun s' : Tok => if keep s' then K s s' else real_zero) states.
Definition Kev (s s' : Tok) : Real :=
  if keep s' then
    real_mult (K s s') (real_inv_pos (Zkv s) (ZP_pos Tok (K s) keep states (Kpos s) keep_nonempty))
  else real_zero.

Theorem kev_Zkv_le_one_via_proj : forall s : Tok, real_le (Zkv s) real_one.
Proof.
  intro s. exact (ZP_le_one Tok (K s) keep states (Krow s) (Kpos s)).
Qed.

Theorem kev_row_normalized_via_proj : forall s : Tok,
  real_eq (real_list_sum Tok (fun s' : Tok => Kev s s') states) real_one.
Proof.
  intro s. exact (proj_normalized Tok (K s) keep states (Kpos s) keep_nonempty).
Qed.

Theorem kev_drop_zero_via_proj : forall s s' : Tok,
  Id (keep s') false -> real_eq (Kev s s') real_zero.
Proof.
  intros s s' H. unfold Kev.
  exact (projp_id_transport bool false (keep s')
           (fun b : bool => real_eq (if b then
              real_mult (K s s') (real_inv_pos (Zkv s)
                (ZP_pos Tok (K s) keep states (Kpos s) keep_nonempty))
            else real_zero) real_zero)
           (real_eq_refl real_zero) (id_sym H)).
Qed.

Theorem kev_keep_ge_via_proj : forall s s' : Tok,
  Id (keep s') true -> real_le (K s s') (Kev s s').
Proof.
  intros s s' H. exact (proj_keep_ge Tok (K s) keep states (Krow s) (Kpos s) keep_nonempty s' H).
Qed.

Variables (Ukv : Tok -> Real) (deltakv : Real).
Variable delta_minor_kv : forall s s' : Tok,
  real_le (real_mult deltakv (Ukv s')) (K s s').

Theorem kev_minor_uncond_via_proj : forall s s' : Tok,
  real_le (if keep s' then real_mult deltakv (Ukv s') else real_zero) (Kev s s').
Proof.
  intros s s'.
  exact (proj_minor_uncond Tok (K s) keep states (Krow s) (Kpos s) keep_nonempty
                           Ukv deltakv (delta_minor_kv s) s').
Qed.

End InstKV.

(* ---------- 实例 B：安全过滤（根 KLProjection 的 Real 层重述） ----------
   接缝：根 projected_normalized 在接口 R 层（sum_over_S/StateSpace），
   本实例按母定理在 Real-list 层同形重述（Z_aud/投影分布/归一化三件
   同构）；根侧接缝留接口实例化，不在此桥。                             *)
Section InstAudit.

Variables (St : Set) (states : list St) (p : St -> Real) (post_aud : St -> bool).
Variable p_norm : real_eq (real_list_sum St p states) real_one.
Variable p_pos : forall s : St, real_lt real_zero (p s).
Variable aud_witness : sigT (fun s : St => And (Id (post_aud s) true) (InT s states)).

Definition ZaudP : Real :=
  real_list_sum St (fun s : St => if post_aud s then p s else real_zero) states.
Definition proj_dist (s : St) : Real :=
  if post_aud s then
    real_mult (p s) (real_inv_pos ZaudP (ZP_pos St p post_aud states p_pos aud_witness))
  else real_zero.

Theorem Zaud_le_one_via_proj : real_le ZaudP real_one.
Proof.
  exact (ZP_le_one St p post_aud states p_norm p_pos).
Qed.

Theorem projected_normalized_via_proj :
  real_eq (real_list_sum St (fun s : St => proj_dist s) states) real_one.
Proof.
  exact (proj_normalized St p post_aud states p_pos aud_witness).
Qed.

Theorem projected_drop_zero_via_proj : forall s : St,
  Id (post_aud s) false -> real_eq (proj_dist s) real_zero.
Proof.
  intros s H. exact (proj_drop_zero St p post_aud states p_pos aud_witness s H).
Qed.

Theorem projected_keep_ge_via_proj : forall s : St,
  Id (post_aud s) true -> real_le (p s) (proj_dist s).
Proof.
  intros s H. exact (proj_keep_ge St p post_aud states p_norm p_pos aud_witness s H).
Qed.

End InstAudit.

(* ---------- 实例 C：Min-P（Set 载体重述 real_minp_markov_kernel） ----------
   接缝：根 RealMinPMain 的保留谓词是 Set 层命题+Or 判定器（非 bool）。
   本实例经 minp_bool（判定器的 bool 载体，构造性合法）接入母定理，
   再以 ext + inv_ext 双桥复原 match 形核的归一化；root Token:Type 与
   本文件 Set 载体的差异为纯载体泛化（内容逐字同构）。                     *)
Section InstMinP.

Variables (W : Set) (vocab : list W).
Variable tf : W -> Real.
Variable tf_norm : real_eq (real_list_sum W tf vocab) real_one.
Variable tf_pos : forall w : W, real_lt real_zero (tf w).
(* 忠实转写根 RealMinPMain 的判定接口（Set 谓词 + Or 判定器，非 bool） *)
Variable Kw : W -> Set.
Variable keep_dec : forall w : W, Or (Kw w) (Not (Kw w)).

Definition minp_bool (w : W) : bool :=
  match keep_dec w with inl _ => true | inr _ => false end.
Definition temp_sum : Real :=
  real_list_sum W
    (fun w : W => match keep_dec w with inl _ => tf w | inr _ => real_zero end) vocab.
Variable temp_sum_pos : real_lt real_zero temp_sum.
(* 母形态见证（对应 root pick_max witness + in-vocab；root 侧非平凡部分
   已由 pick_max_token_minp_keep/pick_best_in_vocab' 证毕，此处为诚实接口） *)
Variable kept_witness : sigT (fun w : W => And (Id (minp_bool w) true) (InT w vocab)).

Definition minp_kernel (w : W) : Real :=
  match keep_dec w with
  | inl _ => real_mult (tf w) (real_inv_pos temp_sum temp_sum_pos)
  | inr _ => real_zero
  end.

Theorem minp_normalized_via_proj :
  real_eq (real_list_sum W (fun w : W => minp_kernel w) vocab) real_one.
Proof.
  pose proof (proj_normalized W tf minp_bool vocab tf_pos kept_witness) as HP.
  assert (HZeq : real_eq (Z_P W tf minp_bool vocab) temp_sum).
  { apply (real_list_sum_ext W (fun w : W => if minp_bool w then tf w else real_zero)
             (fun w : W => match keep_dec w with inl _ => tf w | inr _ => real_zero end)
             vocab).
    intro w. unfold minp_bool. destruct (keep_dec w) as [Hk | Hd].
    - apply real_eq_refl.
    - apply real_eq_refl. }
  apply (real_eq_trans _
           (real_list_sum W
              (fun w : W => if minp_bool w then
                              real_mult (tf w) (real_inv_pos temp_sum temp_sum_pos)
                            else real_zero) vocab) _).
  - apply (real_list_sum_ext W (fun w : W => minp_kernel w) _ vocab).
    intro w. unfold minp_kernel, minp_bool. destruct (keep_dec w) as [Hk | Hd].
    + apply real_eq_refl.
    + apply real_eq_refl.
  - apply (real_eq_trans _
             (real_list_sum W
                (fun w : W => Proj W tf minp_bool vocab tf_pos kept_witness w) vocab) _).
    + apply (real_list_sum_ext W
               (fun w : W => if minp_bool w then
                               real_mult (tf w) (real_inv_pos temp_sum temp_sum_pos)
                             else real_zero)
               (fun w : W => Proj W tf minp_bool vocab tf_pos kept_witness w) vocab).
      intro w. unfold minp_bool, Proj. destruct (keep_dec w) as [Hk | Hd].
      * apply (RealSetoid.real_eq_mult_compat (tf w)
                 (real_inv_pos temp_sum temp_sum_pos)
                 (tf w)
                 (real_inv_pos (Z_P W tf minp_bool vocab)
                               (ZP_pos W tf minp_bool vocab tf_pos kept_witness))).
      -- apply real_eq_refl.
      -- apply (real_inv_pos_ext temp_sum (Z_P W tf minp_bool vocab)
                   temp_sum_pos (ZP_pos W tf minp_bool vocab tf_pos kept_witness)
                   (real_eq_sym (Z_P W tf minp_bool vocab) temp_sum HZeq)).
      * apply real_eq_refl.
    + exact HP.
Qed.

End InstMinP.

(* ======== G04_ProjFam 成员件：UpPLA（原样并入，自带 Require）======== *)
(* ===================================================================== *)
(* UpPLA.v — PLA v2 Coq 落实：p-adic 分层商 + 残基契约 + VCA 估值账户机      *)
(*                                                                       *)
(* 二轮圆桌头部候选（3 票）正式设立。理论来源：                              *)
(*   ROUNDTABLE2.md 上游会话 段落末尾【PLA v2 终稿】四击正面闭合 + VCA 杂交；      *)
(*   排队模块位方案-二轮成果Coq化.md Q1 条目。                        *)
(*                                                                       *)
(* 载体全程 Z/nat/bool 判定层；零 eps、零序比较、零见证借贷。                 *)
(* 纪律：纯构造性（无 公理/承认件/参数/中断）；语句零 Prop           *)
(* （Set 层 tid 恒等型 + nle 序型 + sumbool 判定分支）；stdlib only。         *)
(*                                                                       *)
(* 四件：                                                                 *)
(*   件 1  p-adic 估值机器 vp（乘法可加 + 整除表征）                          *)
(*   件 2  分层商主件（layer_closed / layer_decide / pla_stratified_quotient  *)
(*         + 上游会话 分岔反例并入对照定理）                                     *)
(*   件 3  残基契约显式化（contract 双档，调度器输入参数非隐藏前提）            *)
(*   件 4  VCA 估值账户机（入场费可判定 / 耗散单调 / 进位清结调度）             *)
(* ===================================================================== *)

From Stdlib Require Import ZArith.
From Stdlib Require Import ZArithRing.
From Stdlib Require Import ZArith_dec.
From Stdlib Require Import Lia.

Open Scope Z_scope.

(* ===================================================================== *)
(* 0. Set 层基建：tid 恒等型 / nle 序型 / 判定存活工具                        *)
(* ===================================================================== *)

(* Set 层恒等型（语句零 Prop 的等式载体） *)
Inductive tid (A : Type) : A -> A -> Type := tid_refl : forall x : A, tid A x x.

Definition tid_sym (A : Type) (x y : A) (H : tid A x y) : tid A y x :=
  match H in tid _ a b return tid _ b a with
  | tid_refl _ a0 => @tid_refl _ a0
  end.

Definition tid_trans (A : Type) (x y z : A) (H1 : tid A x y) (H2 : tid A y z) :
  tid A x z :=
  match H1 in tid _ a b return tid _ b z -> tid _ a z with
  | tid_refl _ a0 => fun H => H
  end H2.

(* 恒等型的泛函同余（transport 万能件） *)
Definition tid_cong {A B : Type} (f : A -> B) (x y : A) (H : tid A x y) :
  tid B (f x) (f y) :=
  match H in tid _ a b return tid B (f a) (f b) with
  | tid_refl _ a0 => @tid_refl _ (f a0)
  end.

(* Set 层自然数序型（k < m 编码为 nle (Datatypes.S k) m） *)
Inductive nle (n : nat) : nat -> Set :=
| nle_n : nle n n
| nle_S : forall m : nat, nle n m -> nle n (Datatypes.S m).

Ltac tidE H :=
  pose proof (match H in tid _ a b return a = b with tid_refl _ _ => eq_refl end) as HE.

(* bool 恒等矛盾关闭器：H1 : tid bool X true、H2 : tid bool X false *)
Ltac tid_kill H1 H2 :=
  pose proof (match H1 in tid _ a b return a = b with tid_refl _ _ => eq_refl end) as KE1;
  pose proof (match H2 in tid _ a b return a = b with tid_refl _ _ => eq_refl end) as KE2;
  rewrite KE1 in KE2; discriminate KE2.

(* Set 层 nle 基本件 *)
Lemma leb_refl_tid : forall a : nat, tid bool (Nat.leb a a) true.
Proof.
  intros a. rewrite Nat.leb_refl. apply tid_refl.
Qed.

Lemma leb_S : forall a m : nat,
  tid bool (Nat.leb a m) true -> tid bool (Nat.leb a (Datatypes.S m)) true.
Proof.
  intros a m. revert a. induction m as [| m1 IH]; intros a H.
  - destruct a as [| a1].
    + apply tid_refl.
    + change (tid bool false true) in H. tidE H. discriminate HE.
  - destruct a as [| a1].
    + apply tid_refl.
    + exact (IH a1 H).
Qed.

Fixpoint nle_lebF (a b : nat) (H : nle a b) {struct H} :
  tid bool (Nat.leb a b) true :=
  match H as H0 in nle _ bb
  return tid bool (Nat.leb a bb) true with
  | nle_n _ => leb_refl_tid a
  | nle_S _ m H1 => leb_S a m (nle_lebF a m H1)
  end.

Definition nle_leb (b a : nat) (H : nle a b) : tid bool (Nat.leb a b) true :=
  nle_lebF a b H.

(* nle -> nat ≤ 提取（仅证明内部推理用；可重复调用，自动起新名） *)
Ltac nleP H :=
  let HN := fresh "HNle" in
  pose proof
    (proj1 (Nat.leb_le _ _)
       (match (nle_leb _ _ H) in tid _ x y return x = y with
        | tid_refl _ _ => eq_refl
        end)) as HN.

Lemma nle_SS : forall a b : nat, nle a b -> nle (Datatypes.S a) (Datatypes.S b).
Proof.
  intros a b H. induction H as [| m H IH].
  - apply nle_n.
  - apply nle_S. exact IH.
Qed.

Lemma nle_0 : forall m : nat, nle O m.
Proof.
  induction m as [| m1 IH].
  - apply nle_n.
  - apply nle_S. exact IH.
Qed.

Lemma nle_of_leb : forall b a : nat,
  tid bool (Nat.leb a b) true -> nle a b.
Proof.
  induction b as [| b1 IB]; intros a H.
  - destruct a as [| a1].
    + apply nle_n.
    + change (tid bool false true) in H. tidE H. discriminate HE.
  - destruct a as [| a1].
    + apply nle_0.
    + exact (nle_SS a1 b1 (IB a1 H)).
Qed.

Lemma nle_trans : forall a b c : nat, nle a b -> nle b c -> nle a c.
Proof.
  intros a b c H1 H2. induction H2 as [| c H2 IH].
  - exact H1.
  - apply nle_S. exact IH.
Qed.

(* nle 前驱消解：nle (Datatypes.S a) (Datatypes.S b) -> nle a b *)
Lemma nle_pred : forall a b : nat, nle (Datatypes.S a) (Datatypes.S b) -> nle a b.
Proof.
  intros a b H. apply nle_of_leb.
  exact (nle_leb (Datatypes.S b) (Datatypes.S a) H).
Qed.

Lemma nle_add_r : forall a b : nat, nle a (a + b).
Proof.
  intros a b. revert b. induction a as [| a1 IH]; intro b.
  - apply nle_0.
  - exact (nle_SS a1 (a1 + b) (IH b)).
Qed.


(* nle (Datatypes.S O) O 荒谬件（索引不交配的空消去，合法关闭任意 Set 目标） *)
Lemma nle_10_absurd : forall P : Type, nle (Datatypes.S O) O -> P.
Proof.
  intros P H. inversion H.
Qed.

(* Z 层严格序 → nle 编码桥（Set 面：Z.leb/Z.ltb bool 载体；stdlib 序
   仅限证明体内经 Z.leb_le/Z.ltb_lt 桥入）：
   Z.leb 0 a = true 且 Z.ltb a b = true ⟹ nle (Datatypes.S (to_nat a)) (to_nat b) *)
Lemma zle_to_nle_S : forall a b : Z,
  tid bool (Z.leb 0 a) true -> tid bool (Z.ltb a b) true ->
  nle (Datatypes.S (Z.to_nat a)) (Z.to_nat b).
Proof.
  intros a b Ha Hlt.
  pose proof (match Ha in tid _ x y return x = y with tid_refl _ _ => eq_refl end) as HEa.
  pose proof (match Hlt in tid _ x y return x = y with tid_refl _ _ => eq_refl end) as HElt.
  assert (HaP : (0 <= a)%Z) by (apply (proj1 (Z.leb_le 0 a)); exact HEa).
  assert (HltP : (a < b)%Z) by (apply (proj1 (Z.ltb_lt a b)); exact HElt).
  assert (Hb : (0 <= b)%Z) by lia.
  apply nle_of_leb.
  assert (Hleb : (Nat.leb (Datatypes.S (Z.to_nat a)) (Z.to_nat b)) = true).
  { apply Nat.leb_le.
    exact (proj1 (Z2Nat.inj_lt a b HaP Hb) HltP). }
  rewrite Hleb. apply tid_refl.
Qed.

(* n≠0 ⟹ |n| 的 nat 编码 ≥ (Datatypes.S O) *)
Lemma to_nat_abs_pos : forall n : Z,
  tid bool (Z.eqb n 0) false -> nle (Datatypes.S O) (Z.to_nat (Z.abs n)).
Proof.
  intros n H. tidE H.
  assert (Hne : n <> 0) by (intro Hc; rewrite Hc in HE; discriminate HE).
  apply (zle_to_nle_S 0 (Z.abs n)).
  - apply tid_refl.
  - rewrite (proj2 (Z.ltb_lt 0 (Z.abs n)) (proj2 (Z.abs_pos n) Hne)).
    apply tid_refl.
Qed.

(* |x| ≥ (Datatypes.S O) ⟹ x ≠ 0 的 bool 形 *)
Lemma eqb0_false_of_pos : forall x : Z,
  nle (Datatypes.S O) (Z.to_nat (Z.abs x)) -> tid bool (Z.eqb x 0) false.
Proof.
  intros x H. destruct (Z.eqb x 0) eqn:HEq.
  - apply (proj1 (Z.eqb_eq _ _)) in HEq. rewrite HEq in H.
    exact (nle_10_absurd _ H).
  - apply tid_refl.
Qed.

(* ===================================================================== *)
(* 件 1. p-adic 估值机器                                                  *)
(* ===================================================================== *)

(* p 的 Z 形 / 整除测试 / p^k / p^k 整除测试 *)
Definition pZ (p : nat) : Z := Z.of_nat p.
Definition dvdtest (p : nat) (x : Z) : bool := Z.eqb (Z.modulo x (pZ p)) 0.
Definition powZN (p k : nat) : Z := Z.pow (pZ p) (Z.of_nat k).
Definition dwtest (p k : nat) (x : Z) : bool := Z.eqb (Z.modulo x (powZN p k)) 0.

(* 燃料式估值计数。vp p 0 := 0 专用编码（零态由 Z.eqb 守卫直派 0，避免
   nat 编码无穷；消耗方以 Z.eqb n 0 守卫非零——报告注 1）。 *)
Fixpoint vpF (p : nat) (f : nat) (n : Z) {struct f} : nat :=
  match f with
  | O => O
  | Datatypes.S g =>
      if Z.eqb n 0 then O
      else if dvdtest p n then Datatypes.S (vpF p g (Z.div n (pZ p)))
      else O
  end.

(* 公开估值：燃料取 |n|+1（n≠0 且 p≥2 时每步 |n| 至少折半，燃料充分） *)
Definition vp (p : nat) (n : Z) : nat := vpF p (Datatypes.S (Z.to_nat (Z.abs n))) n.

(* 关键递减：p≥2、n≠0、p∣n ⟹ |n/p| < |n|（nle (Datatypes.S k) m 编码 k<m） *)
Lemma zdiv_abs_decr : forall (p : nat) (n : Z), tid bool (Nat.leb 2 p) true ->
  tid bool (Z.eqb n 0) false -> tid bool (dvdtest p n) true ->
  nle (Datatypes.S (Z.to_nat (Z.abs (Z.div n (pZ p))))) (Z.to_nat (Z.abs n)).
Proof.
  intros p n Hp Hnz Hd.
  pose proof (match Hp in tid _ x y return x = y with tid_refl _ _ => eq_refl end) as HEp.
  pose proof (proj1 (Nat.leb_le 2 p) HEp) as Hple.
  tidE Hnz.
  pose proof (match Hd in tid _ a b return a = b with tid_refl _ _ => eq_refl end) as HE2.
  assert (Hne : n <> 0) by (intro Hc; rewrite Hc in HE; discriminate HE).
  assert (Hpz : (2 <= pZ p)%Z).
  { unfold pZ. apply (proj1 (Nat2Z.inj_le 2 p)). exact Hple. }
  assert (Hpp : (0 <= pZ p)%Z) by lia.
  assert (Hpz0 : pZ p <> 0) by lia.
  assert (Hmod : Z.modulo n (pZ p) = 0) by (apply (proj1 (Z.eqb_eq _ _)); exact HE2).
  assert (Hex : n = pZ p * (Z.div n (pZ p))).
  { pose proof (Z.div_mod n (pZ p) Hpz0) as Hdm. rewrite Hmod in Hdm. lia. }
  assert (Hq0 : Z.div n (pZ p) <> 0).
  { intro Hc. rewrite Hc in Hex. lia. }
  assert (Hqa : (0 < Z.abs (Z.div n (pZ p)))%Z).
  { apply (proj2 (Z.abs_pos (Z.div n (pZ p)))). exact Hq0. }
  assert (Habsm : Z.abs n = pZ p * Z.abs (Z.div n (pZ p))).
  { rewrite Hex at 1. rewrite Z.abs_mul. rewrite (Z.abs_eq (pZ p) Hpp).
    reflexivity. }
  assert (Hm2 : (2 * Z.abs (Z.div n (pZ p)) <= Z.abs n)%Z).
  { rewrite Habsm. apply Z.mul_le_mono_nonneg_r.
    - apply Z.abs_nonneg.
    - exact Hpz. }
  assert (Hlt : (Z.abs (Z.div n (pZ p)) < Z.abs n)%Z) by lia.
  apply zle_to_nle_S.
  - rewrite (proj2 (Z.leb_le 0 (Z.abs (Z.div n (pZ p)))) (Z.abs_nonneg _)).
    apply tid_refl.
  - rewrite (proj2 (Z.ltb_lt (Z.abs (Z.div n (pZ p))) (Z.abs n)) Hlt).
    apply tid_refl.
Qed.

(* 除法保持非零：p≥2、n≠0、p∣n ⟹ n/p ≠ 0（bool 形） *)
Lemma zdiv_nz : forall (p : nat) (n : Z), tid bool (Nat.leb 2 p) true ->
  tid bool (Z.eqb n 0) false -> tid bool (dvdtest p n) true ->
  tid bool (Z.eqb (Z.div n (pZ p)) 0) false.
Proof.
  intros p n Hp Hnz Hd.
  pose proof (match Hp in tid _ x y return x = y with tid_refl _ _ => eq_refl end) as HEp.
  pose proof (proj1 (Nat.leb_le 2 p) HEp) as Hple.
  assert (Hpz : (2 <= pZ p)%Z).
  { unfold pZ. apply (proj1 (Nat2Z.inj_le 2 p)). exact Hple. }
  assert (Hpz0 : pZ p <> 0) by lia.
  tidE Hnz.
  pose proof (match Hd in tid _ a b return a = b with tid_refl _ _ => eq_refl end) as HE2.
  assert (Hne : n <> 0) by (intro Hc; rewrite Hc in HE; discriminate HE).
  assert (Hmod : Z.modulo n (pZ p) = 0) by (apply (proj1 (Z.eqb_eq _ _)); exact HE2).
  assert (Hdm : n = pZ p * (Z.div n (pZ p))).
  { pose proof (Z.div_mod n (pZ p) Hpz0) as Hd0. rewrite Hmod in Hd0. lia. }
  assert (Hq0z : Z.div n (pZ p) <> 0).
  { intro Hc. rewrite Hc in Hdm. lia. }
  apply eqb0_false_of_pos.
  apply (zle_to_nle_S 0 (Z.abs (Z.div n (pZ p)))).
  - apply tid_refl.
  - rewrite (proj2 (Z.ltb_lt 0 (Z.abs (Z.div n (pZ p))))
               (proj2 (Z.abs_pos (Z.div n (pZ p))) Hq0z)).
    apply tid_refl.
Qed.

(* 燃料无关性：燃料均盖住 |n| 时计数唯一 *)
Lemma vpF_indep : forall (p B : nat), tid bool (Nat.leb 2 p) true ->
  forall (f1 f2 : nat) (n : Z),
    nle (Z.to_nat (Z.abs n)) B ->
    tid bool (Z.eqb n 0) false ->
    nle (Z.to_nat (Z.abs n)) f1 ->
    nle (Z.to_nat (Z.abs n)) f2 ->
    tid nat (vpF p f1 n) (vpF p f2 n).
Proof.
  intros p B Hp. induction B as [| B1 IB]; intros f1 f2 n HnB Hnz Hf1 Hf2.
  - assert (H1 := to_nat_abs_pos n Hnz).
    pose proof (nle_trans _ _ _ H1 HnB) as HC. inversion HC.
  - destruct f1 as [| g1].
    + assert (H1 := to_nat_abs_pos n Hnz).
      pose proof (nle_trans _ _ _ H1 Hf1) as HC. inversion HC.
    + destruct f2 as [| g2].
      * assert (H1 := to_nat_abs_pos n Hnz).
        pose proof (nle_trans _ _ _ H1 Hf2) as HC. inversion HC.
      * cbn [vpF]. tidE Hnz. rewrite HE.
        destruct (dvdtest p n) eqn:Hd.
        -- (* p ∣ n：两边同进入位支，递归比较 n/p 的计数 *)
           assert (Hdt : tid bool (dvdtest p n) true)
             by (rewrite Hd; apply tid_refl).
           apply (tid_cong Datatypes.S).
           apply IB with (n := Z.div n (pZ p)).
           ++ exact (nle_pred _ _
                 (nle_trans _ _ _ (zdiv_abs_decr p n Hp Hnz Hdt) HnB)).
           ++ exact (zdiv_nz p n Hp Hnz Hdt).
           ++ exact (nle_pred _ _
                 (nle_trans _ _ _ (zdiv_abs_decr p n Hp Hnz Hdt) Hf1)).
           ++ exact (nle_pred _ _
                 (nle_trans _ _ _ (zdiv_abs_decr p n Hp Hnz Hdt) Hf2)).
        -- (* p ∤ n：else 支直派 O（destruct 已代入，iota 归约即闭） *)
           apply tid_refl.
Qed.

Close Scope Z_scope.

(* ======== G04_ProjFam 成员件：UpPredRelax（原样并入，自带 Require）======== *)
(* ============================================================ *)
(* UpPredRelax.v —— B8 升级：预测区弛豫单调（假设→定性推论最小件） *)
(* 日期：。源：热点扫描 B8（分析-219平凡定理热点扫描）    *)
(* 件 4 heat_relaxation_decreasing（预测 1 热弛豫单调衰减）        *)
(* 件 5a fluctuation_scale_decreasing（预测 4，副本 L1671 模板）   *)
(* 件 5b landauer_bound_pos（预测 3，三正相乘）                    *)
(* 件 5c disturbance_hierarchical_transitive / chain（预测 6）     *)
(* 件 5d total_loss_multi_epoch_decreasing（预测 7，多 epoch 链）   *)
(* 诚实边界（在册边界 #3）：预测区 1–7 无具体动力学/能量定义可使用  *)
(*   （equilibrium_dist、prediction_landauer 等均无构造性定义），   *)
(*   完全定理化不可行；本文件为"假设→定性推论"最小件，全部额外      *)
(*   前提（正性/单调/log 正性）显式声明为 Section Variable，零隐藏。 *)
(*   预测 5（cross_domain_scaling，sigT 前提）无定量杠杆，不做。    *)
(* 纪律：纯构造性 / Set 层 / 零 公理 / 零 承认件 / 零经典。      *)
(* ============================================================ *)

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
From Stdlib Require Import Arith.

(* ============================================================ *)
(* 件 4：预测 1 热弛豫的单调衰减                                  *)
(*   前提：heat_relaxation_exponential（根内 Prediction1 同批）+   *)
(*   γ ≥ 0、T₀ ≥ 0、of_nat 单调（显式新增，见诚实边界）。          *)
(* ============================================================ *)
Section PredRelaxHeat.

Context {RI : RealInterfaceEnhanced}.

Let R := @R RI.
Let mult := @mult RI.
Let exp_neg := @exp_neg RI.
Let le := @le RI.

Variable temperature_difference : nat -> R.
Variable gamma : R.
Variable of_nat : nat -> R.
Variable temperature_difference0 : R.

Variable gamma_nonneg : le zero gamma.
Variable temperature_difference0_nonneg : le zero temperature_difference0.
Variable of_nat_mono : forall t : nat, le (of_nat t) (of_nat (Nat.succ t)).

Variable heat_relaxation_exponential :
  forall t : nat,
    Id (temperature_difference t)
       (mult (exp_neg (mult gamma (of_nat t))) temperature_difference0).

(* 弛豫单调衰减：T(S t) ≤ T(t)
   （γ·of_nat 单调 ⟹ exp_neg 反序单调 ⟹ 乘 T₀ ≥ 0 保序）。 *)
Theorem heat_relaxation_decreasing : forall t : nat,
  le (temperature_difference (Nat.succ t)) (temperature_difference t).
Proof.
  intro t.
  assert (Hg : le (mult gamma (of_nat t)) (mult gamma (of_nat (Nat.succ t)))).
  { (* 接口 le_mult_compat_weak 为右乘形态：经 mult_comm 双端换形 *)
    apply (le_id_l (mult gamma (of_nat t)) (mult (of_nat t) gamma)
                   (mult gamma (of_nat (Nat.succ t)))).
    - apply (mult_comm gamma (of_nat t)).
    - apply (le_id_r (mult (of_nat t) gamma) (mult (of_nat (Nat.succ t)) gamma)
                     (mult gamma (of_nat (Nat.succ t)))).
      + apply (mult_comm (of_nat (Nat.succ t)) gamma).
      + apply (le_mult_compat_weak (of_nat t) (of_nat (Nat.succ t)) gamma).
        * exact gamma_nonneg.
        * exact (of_nat_mono t). }
  assert (He : le (exp_neg (mult gamma (of_nat (Nat.succ t))))
                  (exp_neg (mult gamma (of_nat t))))
    by exact (exp_neg_le_decr _ _ Hg).
  assert (Hm : le (mult (exp_neg (mult gamma (of_nat (Nat.succ t)))) temperature_difference0)
                  (mult (exp_neg (mult gamma (of_nat t))) temperature_difference0))
    by exact (le_mult_compat_weak _ _ temperature_difference0
              temperature_difference0_nonneg He).
  apply (le_id_l (temperature_difference (Nat.succ t))
                 (mult (exp_neg (mult gamma (of_nat (Nat.succ t)))) temperature_difference0)
                 (temperature_difference t)).
  - exact (heat_relaxation_exponential (Nat.succ t)).
  - apply (le_id_r (mult (exp_neg (mult gamma (of_nat (Nat.succ t)))) temperature_difference0)
                   (mult (exp_neg (mult gamma (of_nat t))) temperature_difference0)
                   (temperature_difference t)).
    + exact (id_sym (heat_relaxation_exponential t)).
    + exact Hm.
Qed.

End PredRelaxHeat.

(* ============================================================ *)
(* 件 5a：预测 4 涨落标度的单调衰减（副本根内 L1671               *)
(*   prediction_fluctuation_scale 的已验收升级模板）。             *)
(* ============================================================ *)
Section PredRelaxFluct.

Context {RI : RealInterfaceEnhanced}.

Let R := @R RI.
Let mult := @mult RI.
Let exp_neg := @exp_neg RI.
Let le := @le RI.

Variable prob_negative_entropy : R -> R.
Variable k_B : R.
Variable k_B_pos : lt zero k_B.

Variable fluctuation_scale :
  forall N : R,
    Id (prob_negative_entropy N)
       (exp_neg (mult N (inv_pos k_B k_B_pos))).

(* 涨落概率随 N 单调衰减：P(N+1) ≤ P(N)。
   核：N ≤ N+1 乘 1/k_B ≥ 0（L1671 同链），exp_neg 反序。 *)
Theorem fluctuation_scale_decreasing : forall N : R,
  le (prob_negative_entropy (plus N one)) (prob_negative_entropy N).
Proof.
  intro N.
  assert (Hcore : le (exp_neg (mult (plus N one) (inv_pos k_B k_B_pos)))
                     (exp_neg (mult N (inv_pos k_B k_B_pos)))).
  { apply exp_neg_le_decr.
    apply (le_mult_compat_weak N (plus N one) (inv_pos k_B k_B_pos)).
    - apply (lt_le_iff _ _). left. apply inv_pos_pos.
    - apply le_plus_nonneg_r. exact (lt_le_iff _ _ (inl one_pos)). }
  apply (le_id_l (prob_negative_entropy (plus N one))
                 (exp_neg (mult (plus N one) (inv_pos k_B k_B_pos)))
                 (prob_negative_entropy N)).
  - exact (fluctuation_scale (plus N one)).
  - apply (le_id_r (exp_neg (mult (plus N one) (inv_pos k_B k_B_pos)))
                   (exp_neg (mult N (inv_pos k_B k_B_pos)))
                   (prob_negative_entropy N)).
    + exact (id_sym (fluctuation_scale N)).
    + exact Hcore.
Qed.

End PredRelaxFluct.

(* ============================================================ *)
(* 件 5b：预测 3 Landauer 界的正性（假设→定性推论最小件）。        *)
(*   前提：prediction_landauer（根内 Prediction3 同批）+ k_B>0、   *)
(*   T>0、log 2>0（显式新增；接口 log 无序字段，见诚实边界）。     *)
(* ============================================================ *)
Section PredRelaxLandauer.

Context {RI : RealInterfaceEnhanced}.

Let R := @R RI.
Let mult := @mult RI.
Let log := @log RI.
Let le := @le RI.
Let lt := @lt RI.

Variable E_min : R.
Variable k_B : R.
Variable T_landauer : R.

Variable k_B_pos : lt zero k_B.
Variable T_pos : lt zero T_landauer.
Variable log_two_pos : lt zero (log (plus one one)).

Variable prediction_landauer :
  Id E_min (mult k_B (mult T_landauer (log (plus one one)))).

(* Landauer 界为正：E_min = k_B·T·log 2 > 0（三正相乘 + 恒等换形）。 *)
Theorem landauer_bound_pos : lt zero E_min.
Proof.
  assert (Hinner : lt zero (mult T_landauer (log (plus one one))))
    by exact (mult_positive T_landauer (log (plus one one)) T_pos log_two_pos).
  assert (Houter : lt zero (mult k_B (mult T_landauer (log (plus one one)))))
    by exact (mult_positive k_B (mult T_landauer (log (plus one one)))
                              k_B_pos Hinner).
  apply (lt_id_r zero _ E_min (id_sym prediction_landauer) Houter).
Qed.

End PredRelaxLandauer.

(* ============================================================ *)
(* 件 5c：预测 6 层级稳定性的扰动传递（假设→定性推论最小件）。     *)
(* ============================================================ *)
Section PredRelaxHier.

Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpace RI}.

Let R := @R RI.
Let le := @le RI.
Let PropType := @PropositionConvergenceCore.Proposition RI SS.

Variable disturbance : PropType -> R.
Variable hierarchical_relation : PropType -> PropType -> Set.

Variable hierarchical_stability_prediction :
  forall (upper lower : PropType),
    hierarchical_relation upper lower ->
    le (disturbance upper) (disturbance lower).

(* 两步传递：上层扰动 ≤ 中层扰动 ≤ 下层扰动 ⟹ 上 ≤ 下。 *)
Theorem disturbance_hierarchical_transitive : forall (u m l : PropType),
  hierarchical_relation u m -> hierarchical_relation m l ->
  le (disturbance u) (disturbance l).
Proof.
  intros u m l Hum Hml.
  apply (le_trans (disturbance u) (disturbance m) (disturbance l)).
  - exact (hierarchical_stability_prediction u m Hum).
  - exact (hierarchical_stability_prediction m l Hml).
Qed.

(* 有限链版本：沿层级链 n 步，扰动单调不增
   （le_refl + le_trans 的 nat 归纳；链前提逐点显式）。 *)
Theorem disturbance_chain_decreasing : forall (chain : nat -> PropType),
  (forall k : nat, hierarchical_relation (chain k) (chain (Nat.succ k))) ->
  forall (k n : nat), le (disturbance (chain k)) (disturbance (chain (k + n))).
Proof.
  intros chain Hrel k n.
  induction n as [| n IH].
  - rewrite Nat.add_0_r. apply le_refl.
  - replace (k + Datatypes.S n) with (Nat.succ (k + n))
      by apply (eq_sym (Nat.add_succ_r k n)).
    apply (le_trans (disturbance (chain k)) (disturbance (chain (k + n)))
                    (disturbance (chain (Nat.succ (k + n))))).
    + exact IH.
    + exact (hierarchical_stability_prediction (chain (k + n))
                                               (chain (Nat.succ (k + n)))
                                               (Hrel (k + n))).
Qed.

End PredRelaxHier.

(* ============================================================ *)
(* 件 5d：预测 7 语言模型结构相关的多 epoch 损失下降链             *)
(*   （假设→定性推论最小件；单步相关性前提逐点显式）。             *)
(* ============================================================ *)
Section PredRelaxLM.

Context {RI : RealInterfaceEnhanced}.

Let R := @R RI.
Let le := @le RI.

Variable Token : Set.
Variable model : nat -> list Token.
Variable grammar_error : list Token -> R.
Variable total_loss : list Token -> R.

Variable loss_structure_correlation :
  forall epoch : nat,
    le (grammar_error (model epoch)) (grammar_error (model (Nat.succ epoch))) ->
    le (total_loss (model epoch)) (total_loss (model (Nat.succ epoch))).

(* 多 epoch 损失下降链：grammar_error 逐 epoch 单调
   ⟹ total_loss 沿任意 n 步单调不增。 *)
Theorem total_loss_multi_epoch_decreasing : forall (start n : nat),
  (forall k : nat, le (grammar_error (model k)) (grammar_error (model (Nat.succ k)))) ->
  le (total_loss (model start)) (total_loss (model (start + n))).
Proof.
  intros start n Hg.
  induction n as [| n IH].
  - rewrite Nat.add_0_r. apply le_refl.
  - replace (start + Datatypes.S n) with (Nat.succ (start + n))
      by apply (eq_sym (Nat.add_succ_r start n)).
    apply (le_trans (total_loss (model start)) (total_loss (model (start + n)))
                    (total_loss (model (Nat.succ (start + n))))).
    + exact IH.
    + exact (loss_structure_correlation (start + n) (Hg (start + n))).
Qed.

End PredRelaxLM.

(* ======== G04_ProjFam 成员件：UpProjBPC（原样并入，自带 Require）======== *)
(* ============================================================ *)
(* UpProjBPC.v — BPC：KL 区间乘法复合链（上游会话 杂交增量）           *)
(*                                                              *)
(* 上游：UpProj.v（抽象投影核母定理，807 行 32 引理，四项关卡全部通过）。   *)
(* 本文件在母定理件 1/4 直推半径内，给出闭合链经复合掩码的          *)
(* 代价区间端点精确乘法复合：                                     *)
(*   Z_{P1∩P2} == Z1·(Z2|kept1)，其中 Z2|kept1 为 P1 保留集内     *)
(*   二级掩码的条件保留质量（构造性比值形态 Z12·inv Z1）。          *)
(*   代价侧：−log Z12 == (−log Z1) + (−log Zc) 精确分裂，          *)
(*   KL 代价沿闭合链可加：KL_{P1}(q) == KL_{P12}(q) + (−log Zc)。  *)
(*                                                              *)
(* 件 4（对照注记，注释级）——四近邻均无 KL 区间乘法链语义：        *)
(*   · PCD 并集界：并集质量重算只给界，无乘法分解恒等式；           *)
(*   · PKI notAfter：时点有效性陈述，无 KL 核算；                  *)
(*   · 级数余项：|S−S_t| ≤ B 型余项界，非端点级精确分裂；           *)
(*   · Doob 塔性质：L2 收敛定理，无可计算证书与代价核算。           *)
(*   本件新度 = 闭合点的代数：复合掩码上端点恒等式 + 链式可加。     *)
(*                                                              *)
(* 世界：Real 层 list 世界（UpProj 同款，CW_ConstructiveWorld_219 根）。              *)
(* 全部 Set 层（Id/And/Or/sigT）；语句零 Prop 泄露；              *)
(* 纯构造性：仅依赖 CW_ConstructiveWorld_219 与 UpProj，           *)
(* 零外部假设；log 正性证书随身（透明 Definition 纪律）。          *)
(* ============================================================ *)

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


(* ============================================================ *)
(* 顶层助推（Set 层 real_eq 代数小工具，命名前缀 bpc_ 独占）       *)
(* ============================================================ *)

(* −0 == 0（有符号零桥；区间端点 0 形态归零用） *)
Lemma bpc_opp_zero : real_eq (real_opp real_zero) real_zero.
Proof.
  apply (real_eq_trans _ (real_plus (real_opp real_zero) real_zero) _).
  - apply real_eq_sym. apply real_plus_zero.
  - apply (real_eq_trans _ (real_plus real_zero (real_opp real_zero)) _).
    + apply real_plus_comm.
    + apply real_plus_opp.
Qed.

(* 1·x == x（右单位桥；real_mult_one 是 x·1 形态的副本） *)
Lemma bpc_one_mult : forall x : Real, real_eq (real_mult real_one x) x.
Proof.
  intro x.
  apply (real_eq_trans _ (real_mult x real_one) _).
  - apply real_mult_comm.
  - apply real_mult_one.
Qed.

(* (−t)+t == 0（反序消去零；plus_opp 是 t+(−t) 形态的副本） *)
Lemma bpc_opp_plus_zero : forall t : Real, real_eq (real_plus (real_opp t) t) real_zero.
Proof.
  intro t.
  apply (real_eq_trans _ (real_plus t (real_opp t)) _).
  - apply real_plus_comm.
  - apply real_plus_opp.
Qed.

(* 消去律：(a+(−t))+t == a（链式 KL 恒等式的两侧搬移臂） *)
Lemma bpc_cancel_add_opp : forall a t : Real,
  real_eq (real_plus (real_plus a (real_opp t)) t) a.
Proof.
  intros a t.
  apply (real_eq_trans _ (real_plus a (real_plus (real_opp t) t)) _).
  - apply real_eq_sym. apply real_plus_assoc.
  - apply (real_eq_trans _ (real_plus a real_zero) _).
    + apply (RealSetoid.real_eq_plus_compat a (real_plus (real_opp t) t)
               a real_zero).
      * apply real_eq_refl.
      * apply bpc_opp_plus_zero.
    + apply real_plus_zero.
Qed.

(* 加法交换重排：(a+b)+c == (a+c)+b（链式恒等式的中项换位臂） *)
Lemma bpc_assoc_swap : forall a b c : Real,
  real_eq (real_plus (real_plus a b) c) (real_plus (real_plus a c) b).
Proof.
  intros a b c.
  apply (real_eq_trans _ (real_plus a (real_plus b c)) _).
  - apply real_eq_sym. apply real_plus_assoc.
  - apply (real_eq_trans _ (real_plus a (real_plus c b)) _).
    + apply (RealSetoid.real_eq_plus_compat a (real_plus b c)
               a (real_plus c b)).
      * apply real_eq_refl.
      * apply real_plus_comm.
    + apply real_plus_assoc.
Qed.

(* 乘法换位：x·(y·z) == y·(x·z)（吸收链的中项重排臂） *)
Lemma bpc_mult_swap : forall x y z : Real,
  real_eq (real_mult x (real_mult y z)) (real_mult y (real_mult x z)).
Proof.
  intros x y z.
  apply (real_eq_trans _ (real_mult (real_mult x y) z) _).
  - apply real_mult_assoc.
  - apply (real_eq_trans _ (real_mult (real_mult y x) z) _).
    + apply (RealSetoid.real_eq_mult_compat (real_mult x y) z
               (real_mult y x) z).
      * apply real_mult_comm.
      * apply real_eq_refl.
    + apply real_eq_sym. apply real_mult_assoc.
Qed.

(* ============================================================ *)
(* 母 Section：两级掩码复合（与 UpProj 母 Section 同形扩展）        *)
(*   I/f/idx/f_norm/f_pos 与 UpProj 逐参对齐；P1 P2 两级掩码，     *)
(*   各带非空见证（P1_witness 复用源模块件 0，P12_witness 复合级）。    *)
(* ============================================================ *)
Section BPChain.

Variable I : Set.                          (* 索引类型（同母） *)
Variable f : I -> Real.                    (* 被投影权重（同母） *)
Variable P1 : I -> bool.                   (* 一级保留谓词 *)
Variable P2 : I -> bool.                   (* 二级保留谓词 *)
Variable idx : list I.                     (* 枚举（同母） *)
Variable f_norm : real_eq (real_list_sum I f idx) real_one.
Variable f_pos : forall i : I, real_lt real_zero (f i).
Variable P1_witness : sigT (fun i : I => And (Id (P1 i) true) (InT i idx)).

(* 复合掩码：P1∩P2（bool 合取） *)
Definition P12 (i : I) : bool := andb (P1 i) (P2 i).

Variable P12_witness : sigT (fun i : I => And (Id (P12 i) true) (InT i idx)).

(* ---------- 质量与证书（透明 Definition：log 证书随身纪律） ------ *)
(* Z1 = 一级保留质量；Z12 = 复合保留质量（即 Z_{P1∩P2}） *)
Definition Z1 : Real := Z_P I f P1 idx.
Definition Z12 : Real := Z_P I f P12 idx.

Definition p1 : real_lt real_zero Z1 := ZP_pos I f P1 idx f_pos P1_witness.
Definition p12 : real_lt real_zero Z12 := ZP_pos I f P12 idx f_pos P12_witness.

(* 条件保留质量 Zc := Z12·inv Z1（= Σ_{P1∧P2} f / Z1，即 Z2|kept1） *)
Definition Zc : Real := real_mult Z12 (real_inv_pos Z1 p1).
(* 正性证书随身（透明，非 Qed 封死） *)
Definition Zc_pos : real_lt real_zero Zc :=
  real_mult_positive Z12 (real_inv_pos Z1 p1) p12 (real_inv_pos_pos Z1 p1).

(* 一级投影核（母形态实例化）与条件质量和的核上形态 *)
Definition Proj1 (i : I) : Real := Proj I f P1 idx f_pos P1_witness i.
Definition Zc_proj1 : Real :=
  real_list_sum I (fun i : I => if P12 i then Proj1 i else real_zero) idx.

(* ---------- 件 1 核 A：点级四支掩码桥 -------------------------- *)
(* P12 支的 Proj1 == P12 支的 f·inv Z1（P1∧P2 保留 ⟹ 一级保留支）； *)
(* P12 逐出支两侧归零。destruct 逐支独立证明，无空 match。          *)
Lemma bpc_pt_bridge : forall y : I,
  real_eq (if P12 y then Proj1 y else real_zero)
          (real_mult (if P12 y then f y else real_zero)
                     (real_inv_pos Z1 p1)).
Proof.
  intro y. unfold P12, Proj1, Proj.
  destruct (P1 y) eqn:H1y; destruct (P2 y) eqn:H2y; cbn [andb].
  - (* true,true：双侧 f·inv Z1，conversion 相等 *)
    apply real_eq_refl.
  - (* true,false：0·inv == 0（sym 转 mult 头，comm + mult_zero） *)
    apply real_eq_sym.
    apply (real_eq_trans _ (real_mult (real_inv_pos Z1 p1) real_zero) _).
    + apply real_mult_comm.
    + apply real_mult_zero.
  - (* false,true：0·inv == 0 *)
    apply real_eq_sym.
    apply (real_eq_trans _ (real_mult (real_inv_pos Z1 p1) real_zero) _).
    + apply real_mult_comm.
    + apply real_mult_zero.
  - (* false,false：0·inv == 0 *)
    apply real_eq_sym.
    apply (real_eq_trans _ (real_mult (real_inv_pos Z1 p1) real_zero) _).
    + apply real_mult_comm.
    + apply real_mult_zero.
Qed.

(* ---------- 件 1 核 B：两级掩码和的分解（线性提取） ------------- *)
(* Σ_{P12} Proj1 == inv Z1 · Z12：条件质量和（二级掩码在一级投影核  *)
(* 上的和）经逐点桥 + real_list_sum_linear_r 提取线性因子。         *)
Lemma bpc_Zc_proj1_sum : real_eq Zc_proj1
  (real_mult (real_inv_pos Z1 p1) Z12).
Proof.
  apply (real_eq_trans _
           (real_list_sum I
              (fun i : I =>
                 real_mult (if P12 i then f i else real_zero)
                           (real_inv_pos Z1 p1))
              idx) _).
  - apply (real_list_sum_ext I
             (fun i : I => if P12 i then Proj1 i else real_zero)
             (fun i : I =>
                real_mult (if P12 i then f i else real_zero)
                          (real_inv_pos Z1 p1))
             idx).
    intro y. apply bpc_pt_bridge.
  - apply (real_list_sum_linear_r I (real_inv_pos Z1 p1)
             (fun i : I => if P12 i then f i else real_zero) idx).
Qed.

(* ---------- 复合支配：Z12 ≤ Z1（两级掩码和 ≤ 一级掩码和） ------- *)
Lemma bpc_Z12_le_Z1 : real_le Z12 Z1.
Proof.
  apply (real_list_sum_le I
           (fun i : I => if P12 i then f i else real_zero)
           (fun i : I => if P1 i then f i else real_zero) idx).
  intro y. unfold P12. destruct (P1 y); destruct (P2 y).
  - apply real_le_refl.
  - apply real_le_from_lt_aux. apply f_pos.
  - apply real_le_refl.
  - apply real_le_refl.
Qed.

(* ---------- 件 1（主件·乘法分解）：Z12 == Z1·Zc ----------------- *)
(* 纸笔推导：Z1·Zc == Z1·(Z12·inv Z1) == Z12·(Z1·inv Z1)（换位）    *)
(*   == Z12·1 == Z12。核心 = inv 的分配吸收（换位 + inv_correct     *)
(*   + mult_one）；条件占比形态的循环由「Zc 由 Z12/Z1/见证构造、    *)
(*   分解核独立（核 A/B）」排除。                                   *)
Theorem Z_compound_mul : real_eq Z12 (real_mult Z1 Zc).
Proof.
  apply real_eq_sym.
  apply (real_eq_trans _ (real_mult Z1 (real_mult Z12 (real_inv_pos Z1 p1))) _).
  - apply (RealSetoid.real_eq_mult_compat Z1 Zc Z1
             (real_mult Z12 (real_inv_pos Z1 p1))).
    + apply real_eq_refl.
    + apply real_eq_refl.
  - apply (real_eq_trans _ (real_mult Z12 (real_mult Z1 (real_inv_pos Z1 p1))) _).
    + apply bpc_mult_swap.
    + apply (real_eq_trans _ (real_mult Z12 real_one) _).
      * apply (RealSetoid.real_eq_mult_compat Z12
                 (real_mult Z1 (real_inv_pos Z1 p1)) Z12 real_one).
        -- apply real_eq_refl.
        -- apply real_inv_pos_correct.
      * apply real_mult_one.
Qed.

(* ---------- 件 1 卫星（语义桥）：条件质量和 == 比值形态 ---------- *)
(* Z2|kept1 的两个构造形态重合：Σ_{P12} Proj1 == Z12·inv Z1。       *)
Lemma bpc_cond_semantics : real_eq Zc_proj1 Zc.
Proof.
  apply (real_eq_trans _ (real_mult (real_inv_pos Z1 p1) Z12) _).
  - apply bpc_Zc_proj1_sum.
  - unfold Zc. apply real_mult_comm.
Qed.

(* ---------- 复合件 0：条件质量 ∈ (0,1] ------------------------- *)
(* Zc ≤ 1：Zc == Z12·inv Z1 ≤ Z1·inv Z1 == 1（支配 + inv 吸收）。   *)
Theorem Zc_le_one : real_le Zc real_one.
Proof.
  apply (real_le_trans _ (real_mult Z1 (real_inv_pos Z1 p1))).
  - exact (real_le_mult_compat Z12 Z1 (real_inv_pos Z1 p1)
             (real_inv_pos_pos Z1 p1) bpc_Z12_le_Z1).
  - apply (RealSetoid.real_eq_le (real_mult Z1 (real_inv_pos Z1 p1)) real_one).
    apply real_inv_pos_correct.
Qed.

(* ---------- log 复合核：log Z12 == log Z1 + log Zc -------------- *)
(* 端点乘法复合的 log 侧形态；real_log_mult 证书参数位与 wd 桥同形       *)
(* （real_mult_positive Z1 Zc p1 Zc_pos，透明证书纪律）。            *)
Lemma bpc_log_Z12_split :
  real_eq (real_log Z12 p12)
          (real_plus (real_log Z1 p1) (real_log Zc Zc_pos)).
Proof.
  apply (real_eq_trans _
           (real_log (real_mult Z1 Zc) (real_mult_positive Z1 Zc p1 Zc_pos)) _).
  - exact (real_log_wd Z12 (real_mult Z1 Zc) p12
             (real_mult_positive Z1 Zc p1 Zc_pos) Z_compound_mul).
  - exact (real_log_mult Z1 Zc p1 Zc_pos).
Qed.

(* ---------- 代价端点乘法复合：−log Z1 + −log Zc == −log Z12 ----- *)
Lemma bpc_cost_mul_split :
  real_eq (real_plus (real_opp (real_log Z1 p1))
                     (real_opp (real_log Zc Zc_pos)))
          (real_opp (real_log Z12 p12)).
Proof.
  apply (real_eq_trans _
           (real_opp (real_plus (real_log Z1 p1) (real_log Zc Zc_pos))) _).
  - apply real_eq_sym. apply real_opp_plus.
  - apply (RealSetoid.real_eq_opp_compat
             (real_plus (real_log Z1 p1) (real_log Zc Zc_pos))
             (real_log Z12 p12)).
    apply real_eq_sym. apply bpc_log_Z12_split.
Qed.

(* ---------- 件 2（主件·KL 代价链可加）--------------------------- *)
(* 母定理两次（P1 与 P12）+ 代价端点分裂 + 三臂消元：                *)
(*   A+(−(real_log Z1 p1)) == KLqf == B+(−l12) == B+((−(real_log Z1 p1))+(−lc)) == (B+(−(real_log Z1 p1)))+(−lc) *)
(*   两侧经 (x+(−t))+t 搬移得 A == B+(−lc)。                         *)
(* q 前提诚实给出：归一化 + 逐点正 + 复合掩码兼容（P12 假 ⟹ q=0，    *)
(* 由 andb false 支定义性导出一级兼容，单一前提覆盖两级）。           *)
Theorem proj_kl_chain : forall (q : I -> Real)
  (Hq_norm : real_eq (real_list_sum I q idx) real_one)
  (Hq_pos : forall i : I, real_lt real_zero (q i))
  (Hq_fail : forall i : I, Id (andb (P1 i) (P2 i)) false -> real_eq (q i) real_zero),
  real_eq (KLqp I f P1 idx f_pos P1_witness q Hq_pos)
          (real_plus (KLqp I f P12 idx f_pos P12_witness q Hq_pos)
                     (real_opp (real_log Zc Zc_pos))).
Proof.
  intros q Hq_norm Hq_pos Hq_fail.
  assert (Hqf1 : forall i : I, Id (P1 i) false -> real_eq (q i) real_zero).
  { intro i. intro Heq1. apply (Hq_fail i).
    exact (projp_id_transport bool false (P1 i)
             (fun b : bool => Id (andb b (P2 i)) false)
             id_refl (id_sym Heq1)). }
  pose proof (proj_kl_cost I f P1 idx f_pos P1_witness q Hq_norm Hq_pos Hqf1) as H1.
  pose proof (proj_kl_cost I f P12 idx f_pos P12_witness q Hq_norm Hq_pos Hq_fail) as H2.
  assert (Hj1 : real_eq (real_plus (KLqp I f P1 idx f_pos P1_witness q Hq_pos)
                                   (real_opp (real_log Z1 p1)))
                        (real_plus (KLqp I f P12 idx f_pos P12_witness q Hq_pos)
                                   (real_opp (real_log Z12 p12)))).
  { apply (real_eq_trans _ (KLqf I f idx f_pos q Hq_pos) _).
    - apply real_eq_sym. exact H1.
    - exact H2. }
  assert (Hj2 : real_eq (real_plus (KLqp I f P12 idx f_pos P12_witness q Hq_pos)
                                   (real_opp (real_log Z12 p12)))
                        (real_plus (real_plus (KLqp I f P12 idx f_pos P12_witness q Hq_pos)
                                              (real_opp (real_log Z1 p1)))
                                   (real_opp (real_log Zc Zc_pos)))).
  { apply (real_eq_trans _
             (real_plus (KLqp I f P12 idx f_pos P12_witness q Hq_pos)
                        (real_plus (real_opp (real_log Z1 p1))
                                   (real_opp (real_log Zc Zc_pos)))) _).
    - apply (RealSetoid.real_eq_plus_compat
               (KLqp I f P12 idx f_pos P12_witness q Hq_pos)
               (real_opp (real_log Z12 p12))
               (KLqp I f P12 idx f_pos P12_witness q Hq_pos)
               (real_plus (real_opp (real_log Z1 p1))
                          (real_opp (real_log Zc Zc_pos)))).
      + apply real_eq_refl.
      + apply real_eq_sym. apply bpc_cost_mul_split.
    - apply real_plus_assoc. }
  assert (Hjoin : real_eq (real_plus (KLqp I f P1 idx f_pos P1_witness q Hq_pos)
                                     (real_opp (real_log Z1 p1)))
                          (real_plus (real_plus (KLqp I f P12 idx f_pos P12_witness q Hq_pos)
                                                (real_opp (real_log Z1 p1)))
                                     (real_opp (real_log Zc Zc_pos)))).
  { apply (real_eq_trans _ (real_plus (KLqp I f P12 idx f_pos P12_witness q Hq_pos)
                                      (real_opp (real_log Z12 p12))) _).
    - exact Hj1.
    - exact Hj2. }
  assert (Hright : real_eq
    (real_plus (real_plus (real_plus (KLqp I f P12 idx f_pos P12_witness q Hq_pos)
                                     (real_opp (real_log Z1 p1)))
                          (real_opp (real_log Zc Zc_pos)))
               (real_log Z1 p1))
    (real_plus (KLqp I f P12 idx f_pos P12_witness q Hq_pos)
               (real_opp (real_log Zc Zc_pos)))).
  { apply (real_eq_trans _
             (real_plus (real_plus (real_plus (KLqp I f P12 idx f_pos P12_witness q Hq_pos)
                                              (real_opp (real_log Z1 p1))) (real_log Z1 p1))
                        (real_opp (real_log Zc Zc_pos))) _) .
    - exact (bpc_assoc_swap (real_plus (KLqp I f P12 idx f_pos P12_witness q Hq_pos)
                                       (real_opp (real_log Z1 p1)))
                            (real_opp (real_log Zc Zc_pos)) (real_log Z1 p1)) .
    - apply (RealSetoid.real_eq_plus_compat
               (real_plus (real_plus (KLqp I f P12 idx f_pos P12_witness q Hq_pos)
                                     (real_opp (real_log Z1 p1))) (real_log Z1 p1))
               (real_opp (real_log Zc Zc_pos))
               (KLqp I f P12 idx f_pos P12_witness q Hq_pos)
               (real_opp (real_log Zc Zc_pos))).
      + apply bpc_cancel_add_opp.
      + apply real_eq_refl. }
  apply (real_eq_trans _
           (real_plus (real_plus (KLqp I f P1 idx f_pos P1_witness q Hq_pos)
                                 (real_opp (real_log Z1 p1))) (real_log Z1 p1)) _).
  - apply real_eq_sym. apply bpc_cancel_add_opp.
  - apply (real_eq_trans _
             (real_plus (real_plus (real_plus (KLqp I f P12 idx f_pos P12_witness q Hq_pos)
                                              (real_opp (real_log Z1 p1)))
                                   (real_opp (real_log Zc Zc_pos)))
                        (real_log Z1 p1)) _).
    + apply (RealSetoid.real_eq_plus_compat
               (real_plus (KLqp I f P1 idx f_pos P1_witness q Hq_pos)
                          (real_opp (real_log Z1 p1))) (real_log Z1 p1)
               (real_plus (real_plus (KLqp I f P12 idx f_pos P12_witness q Hq_pos)
                                     (real_opp (real_log Z1 p1)))
                          (real_opp (real_log Zc Zc_pos))) (real_log Z1 p1)).
      * exact Hjoin.
      * apply real_eq_refl.
    + exact Hright.
Qed.

(* ---------- 件 3a：闭合代价区间端点（质量夹逼）------------------- *)
(* 单侧信息投影版：S ≤ Z12 ≤ S+U（S,U,S+U > 0 的证书前提）⟹          *)
(*   −log(S+U) ≤ −log Z12 ≤ −log S。                                  *)
(* 两端皆定理：log 单调（real_log_le_mono）+ 取负反向                  *)
(* （real_opp_le_compat）；端点乘法复合见 bpc_cost_mul_split。         *)
Theorem proj_cost_interval : forall (S U : Real)
  (HSp : real_lt real_zero S)
  (HUp : real_lt real_zero (real_plus S U))
  (Hlo : real_le S Z12) (Hhi : real_le Z12 (real_plus S U)),
  And (real_le (real_opp (real_log (real_plus S U) HUp))
               (real_opp (real_log Z12 p12)))
      (real_le (real_opp (real_log Z12 p12))
               (real_opp (real_log S HSp))).
Proof.
  intros S U HSp HUp Hlo Hhi.
  split.
  - apply (real_opp_le_compat (real_log Z12 p12)
             (real_log (real_plus S U) HUp)).
    apply (real_log_le_mono Z12 (real_plus S U) p12 HUp).
    exact Hhi.
  - apply (real_opp_le_compat (real_log S HSp) (real_log Z12 p12)).
    apply (real_log_le_mono S Z12 HSp p12).
    exact Hlo.
Qed.

(* ---------- 件 3b：全保留端点（下端点精确值 0）------------------- *)
(* P12 ≡ true ⟹ Z12 == 1（f_norm 桥）⟹ −log Z12 == 0：                *)
(* 闭合代价区间 [−log(S_t+U_t), −log S_t] 的 U_t→0 / S_t→1 退化象，    *)
(* 与件 3a 夹逼件在端点处精确闭合。                                   *)
Theorem proj_cost_full_mask_zero :
  (forall i : I, Id (P12 i) true) ->
  real_eq (real_opp (real_log Z12 p12)) real_zero.
Proof.
  intro Hall.
  assert (HZ1 : real_eq Z12 real_one).
  { apply (real_eq_trans _ (real_list_sum I f idx) _).
    - apply (real_list_sum_ext I
               (fun i : I => if P12 i then f i else real_zero) f idx).
      intro y. apply (projp_id_transport bool true (P12 y)
                 (fun b : bool => real_eq (if b then f y else real_zero) (f y))).
      + apply real_eq_refl.
      + exact (id_sym (Hall y)).
    - exact f_norm. }
  assert (Hlog : real_eq (real_log Z12 p12) real_zero).
  { apply (real_eq_trans _ (real_log real_one real_lt_zero_one) _).
    - exact (real_log_wd Z12 real_one p12 real_lt_zero_one HZ1).
    - apply (real_log_one real_lt_zero_one). }
  apply (real_eq_trans _ (real_opp real_zero) _).
  - apply (RealSetoid.real_eq_opp_compat (real_log Z12 p12) real_zero Hlog).
  - apply bpc_opp_zero.
Qed.

End BPChain.

(* ===================================================================== *)
(* 文尾供给段：签名保持式消解（b3 §2.2.1 形态二·外部供给）                  *)
(*                                                                       *)
(* 三态甄别结论（b3 §2.2，全 71 位表见附表）：                              *)
(*  · 已施工供给（C3 点名四位）：P_witness（AbstractProjection:203，        *)
(*    AbstractKL:422 同形覆盖）/P12_witness（BPChain:1543）/Krow            *)
(*    （InstKV:667）/keep_dec（InstMinP:778，Set 重述核准形）；            *)
(*    另附 f_norm/f_pos 同形供给与 ZP_pos 实例充任示范。                   *)
(*  · 同形可复制（方向登记）：Kpos/keep_nonempty/p_norm/p_pos/             *)
(*    aud_witness/tf_norm/tf_pos/temp_sum_pos/kept_witness/P1_witness/     *)
(*    BPChain f_norm/f_pos——同单点配方机械复制，候合并方案甄别后确认。    *)
(*  · 真前提（保留·禁硬证）：delta_minor/delta_minor_kv（Doeblin 间隙      *)
(*    证书，自由 u/δ 上独立义务）；PredRelax 五节叙述假设（gamma_nonneg/   *)
(*    of_nat_mono/heat_relaxation_exponential/k_B_pos/fluctuation_scale/   *)
(*    T_pos/log_two_pos/prediction_landauer/hierarchical_stability_        *)
(*    prediction/loss_structure_correlation——物理叙述级，墙族登记）。      *)
(*  · 接口参数位（保留）：各节数据参数原样保留，接口义务。                 *)
(* 实例载体（单点形，Fin2/B1/B2 enum:=[tt] 先例同构）：            *)
(*   供给定理为具体实例上的消解证书，供使用方以实例充任接口字段。           *)
(* ===================================================================== *)

(* 单点实例载体 *)
Definition g04pf_idx1 : list unit := tt :: nil.
Definition g04pf_f1 : unit -> Real := fun _ : unit => real_one.
Definition g04pf_P1t : unit -> bool := fun _ : unit => true.
Definition g04pf_P2t : unit -> bool := fun _ : unit => true.
Definition g04pf_K1 : unit -> unit -> Real := fun _ _ : unit => real_one.
Definition g04pf_Kw1 : unit -> Set := fun _ : unit => unit.

(* 单点归一证书：Σ_{tt::nil} 1 == 1（换位 + 零元收束，两步实和） *)
Lemma g04pf_f_norm_supply :
  real_eq (real_list_sum unit (fun _ : unit => real_one) g04pf_idx1) real_one.
Proof.
  exact (real_eq_trans (real_plus real_one real_zero)
           (real_plus real_zero real_one) real_one
           (real_plus_comm real_one real_zero)
           (projp_plus_zero_l real_one)).
Qed.

(* 单点正性证书：恒一权重逐点严格正（real_lt_zero_one 直锚） *)
Lemma g04pf_f_pos_supply :
  forall i : unit, real_lt real_zero (g04pf_f1 i).
Proof. intro i. exact real_lt_zero_one. Qed.

(* 供给一（C3 点名）：P_witness 单点见证——existT 直构                      *)
(*   （id_refl 恒等肢 + InT_here 枚举肢，And 合取封装）。                   *)
Lemma g04pf_p_witness_supply :
  sigT (fun i : unit => And (Id (g04pf_P1t i) true) (InT i g04pf_idx1)).
Proof.
  exists tt. split.
  - exact (@id_refl bool true).
  - apply InT_here.
Qed.

(* 供给二（C3 点名）：Krow 单点核行归一——(fun s' => K1 s s') 与恒一权重    *)
(*   定义性一致，归一证书同 g04pf_f_norm_supply。                          *)
Lemma g04pf_krow_supply : forall s : unit,
  real_eq (real_list_sum unit (fun s' : unit => g04pf_K1 s s') g04pf_idx1)
          real_one.
Proof.
  intro s.
  exact (real_eq_trans (real_plus real_one real_zero)
           (real_plus real_zero real_one) real_one
           (real_plus_comm real_one real_zero)
           (projp_plus_zero_l real_one)).
Qed.

(* 供给三（C3 点名·Set 重述核准形）：keep_dec 单点判定证书——               *)
(*   Kw 取 inhabited 形，inl 正支直构（Or/Not 为 S01:78-80 Set 层和型       *)
(*   别名，供给形与 sumbool 载体同层同义）。                                *)
Lemma g04pf_keep_dec_supply :
  forall w : unit, Or (g04pf_Kw1 w) (Not (g04pf_Kw1 w)).
Proof. intro w. exact (@inl (g04pf_Kw1 w) (Not (g04pf_Kw1 w)) tt). Qed.

(* 供给四（C3 点名）：P12_witness 单点复合见证——P1/P2 恒真 ⟹              *)
(*   P12 tt = andb true true 定义性归 true，见证直构。                      *)
Lemma g04pf_p12_witness_supply :
  sigT (fun i : unit =>
    And (Id (P12 unit g04pf_P1t g04pf_P2t i) true) (InT i g04pf_idx1)).
Proof.
  exists tt. split.
  - exact (@id_refl bool true).
  - apply InT_here.
Qed.

(* 实例充任示范：单点实例五字段充任母定理 ZP_pos 接口字段                   *)
(*   （f_norm/f_pos/P_witness 三供给全参直引），正性证书随身。              *)
Lemma g04pf_zp_pos_supply :
  real_lt real_zero (Z_P unit g04pf_f1 g04pf_P1t g04pf_idx1).
Proof.
  exact (ZP_pos unit g04pf_f1 g04pf_P1t g04pf_idx1
           g04pf_f_pos_supply g04pf_p_witness_supply).
Qed.

(* ======== ToyR 专项切片二 · 验证证据段（正文语句面零改，仅追加取证） ======== *)
Print Assumptions projp_id_transport.
Print Assumptions projp_minus_plus_opp.
Print Assumptions kev_Zkv_le_one_via_proj.
Print Assumptions kev_row_normalized_via_proj.
Print Assumptions kev_drop_zero_via_proj.
Print Assumptions kev_keep_ge_via_proj.
Print Assumptions kev_minor_uncond_via_proj.
Print Assumptions Zaud_le_one_via_proj.
Print Assumptions projected_normalized_via_proj.
Print Assumptions projected_drop_zero_via_proj.
Print Assumptions projected_keep_ge_via_proj.
Print Assumptions nle_pred.

(* ----- W20 供给段假设审计追加（七条同审计门） ----- *)
Print Assumptions g04pf_f_norm_supply.
Print Assumptions g04pf_f_pos_supply.
Print Assumptions g04pf_p_witness_supply.
Print Assumptions g04pf_krow_supply.
Print Assumptions g04pf_keep_dec_supply.
Print Assumptions g04pf_p12_witness_supply.
Print Assumptions g04pf_zp_pos_supply.
