(* ==========================================================================)
   ToyR_fa56b_ext —— singleton/cons/append 非空族（enum 非空谓词的居民性与闭包构造）、逐点 Id 到和 Id 的引擎扩展、detailed_bal；同域语句面
   使命：本件形式化singleton/cons/append 非空族（enum 非空谓词的居民性与闭包构造）、逐点 Id 到和 Id 的引擎扩展、detailed_bal。
   本件并载：S:=bool、reward 分档常值、beta:=1、pi_ref:=恒 1、Z_align:=1 的全显式见证；三处正性由 real_lt_zero；fa52_EDP_E_B_pos_unsat（能量全正支 ⟹ False）与 fa52_EntropyDiffReal_premises_unsat（熵。
   依赖：S02_CauchyComplete, S07_RealSetoidExpLog, S08_RealMainlineDPO, S09_EntropyReal, S01_BaseRing, fa51_sumpos_id, fa56_id_carrier, Lists.List
   构造性：零公理、零承认式语句；语句面 Set 层承载，Print Assumptions 全 Closed。
   编译配方：Rocq 9.1 coqc -native-compiler no -Q . ""，cpu_guard 包裹限载。
   ========================================================================== *)

(* ============================ §1 S:=bool、reward 分档常值、beta:=1、pi_ref:=恒 1、Z_align:=1 的全显式见证；三处正性由 real_lt_zero ============================ *)
Require Import S02_CauchyComplete.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.

(* ---------- 具体见证 ---------- *)
Definition fa52_dpo_S : Type := bool.
Definition fa52_dpo_reward : bool -> Real :=
  fun s : bool => if s then real_plus real_one real_one else real_one.
Definition fa52_dpo_pi_ref : bool -> Real := fun _ : bool => real_one.
Definition fa52_dpo_pi_ref_pos : forall s : bool, real_lt real_zero (fa52_dpo_pi_ref s) :=
  fun _ : bool => real_lt_zero_one.

(* ---------- 1 < 2（0<1 复合 + 代数归位） ---------- *)
Lemma fa52_one_two_lt : real_lt real_one (real_plus real_one real_one).
Proof.
  assert (HL : real_eq (real_plus real_zero real_one) real_one).
  { apply (real_eq_trans _ (real_plus real_one real_zero)).
    - apply (real_plus_comm real_zero real_one).
    - apply (real_plus_zero real_one). }
  assert (Hstep : real_lt (real_plus real_zero real_one)
                          (real_plus real_one real_one)).
  { exact (real_lt_plus_compat_lt_le real_zero real_one real_one real_one
             real_lt_zero_one (real_le_refl real_one)). }
  exact (real_eq_lt_lt _ _ _ (real_eq_sym _ _ HL) Hstep).
Qed.

Lemma fa52_dpo_reward_spread :
  real_lt (fa52_dpo_reward false) (fa52_dpo_reward true).
Proof.
  unfold fa52_dpo_reward.
  simpl.
  exact fa52_one_two_lt.
Qed.

(* ---------- 主件一：DPO 损失在 π* 处 (0, ln2) 有界——见证特化闭语句 ---------- *)
Theorem fa52_dpo_bounded_both_concrete :
  S01_BaseRing.And
    (real_lt real_zero
       (real_dpo_loss_pair bool real_one fa52_dpo_pi_ref fa52_dpo_pi_ref_pos
          (real_pi_star bool fa52_dpo_reward real_one real_lt_zero_one
             fa52_dpo_pi_ref real_one real_lt_zero_one)
          (real_pi_star_pos bool fa52_dpo_reward real_one real_lt_zero_one
             fa52_dpo_pi_ref fa52_dpo_pi_ref_pos real_one real_lt_zero_one)
          true false))
    (real_lt
       (real_dpo_loss_pair bool real_one fa52_dpo_pi_ref fa52_dpo_pi_ref_pos
          (real_pi_star bool fa52_dpo_reward real_one real_lt_zero_one
             fa52_dpo_pi_ref real_one real_lt_zero_one)
          (real_pi_star_pos bool fa52_dpo_reward real_one real_lt_zero_one
             fa52_dpo_pi_ref fa52_dpo_pi_ref_pos real_one real_lt_zero_one)
          true false)
       (real_log (real_plus real_one real_one) real_two_pos)).
Proof.
  exact (real_dpo_loss_pi_star_bounded_both bool fa52_dpo_reward real_one           real_lt_zero_one fa52_dpo_pi_ref fa52_dpo_pi_ref_pos           real_one real_lt_zero_one true false fa52_dpo_reward_spread).
Qed.

(* ---------- 主件二：闭式奖励复原——见证特化（β:=1, Z:=1 分离出 log1 修正项） ---------- *)
Theorem fa52_dpo_reward_recovery_concrete : forall s : bool,
  real_eq
    (real_dpo_reward_explicit bool real_one fa52_dpo_pi_ref fa52_dpo_pi_ref_pos
       (real_pi_star bool fa52_dpo_reward real_one real_lt_zero_one
          fa52_dpo_pi_ref real_one real_lt_zero_one)
       (real_pi_star_pos bool fa52_dpo_reward real_one real_lt_zero_one
          fa52_dpo_pi_ref fa52_dpo_pi_ref_pos real_one real_lt_zero_one)
       s)
    (real_plus (fa52_dpo_reward s)
                (real_opp (real_mult real_one
                            (real_log real_one real_lt_zero_one)))).
Proof.
  intro s.
  exact (real_dpo_reward_recovers_up_to_baseline bool fa52_dpo_reward real_one           real_lt_zero_one fa52_dpo_pi_ref fa52_dpo_pi_ref_pos           real_one real_lt_zero_one s).
Qed.

Print Assumptions fa52_dpo_bounded_both_concrete.
Print Assumptions fa52_dpo_reward_recovery_concrete.

(* ============================ §2 fa52_EDP_E_B_pos_unsat（能量全正支 ⟹ False）与 fa52_EntropyDiffReal_premises_unsat（熵 ============================ *)
Require Import S02_CauchyComplete.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.

(* ---------- 核心：E_B_pos 单槽不可满足 ---------- *)
Theorem fa52_EDP_E_B_pos_unsat :
  forall E_total : Real,
    (forall E : Real, real_lt real_zero E ->
       real_lt real_zero (real_plus E_total (real_opp E))) -> False.
Proof.
  intros E_total eB.
  (* 第一步：eB 1：0 < E_total - 1 *)
  pose proof (eB real_one real_lt_zero_one) as H1.
  (* 第二步：混合加保序 0+1 < (E_total-1)+1 *)
  assert (Hstep : real_lt (real_plus real_zero real_one)
                          (real_plus (real_plus E_total (real_opp real_one)) real_one)).
  { exact (real_lt_plus_compat_lt_le real_zero
             (real_plus E_total (real_opp real_one)) real_one real_one H1
             (real_le_refl real_one)). }
  (* 0+1 == 1 *)
  assert (HL : real_eq (real_plus real_zero real_one) real_one).
  { apply (real_eq_trans _ (real_plus real_one real_zero)).
    - apply (real_plus_comm real_zero real_one).
    - apply (real_plus_zero real_one). }
  (* (E_total-1)+1 == E_total *)
  assert (HR : real_eq (real_plus (real_plus E_total (real_opp real_one)) real_one)
                       E_total).
  { apply (real_eq_trans _ (real_plus E_total (real_plus (real_opp real_one) real_one))).
    - apply real_eq_sym.
      apply (real_plus_assoc E_total (real_opp real_one) real_one).
    - apply (real_eq_trans _ (real_plus E_total real_zero)).
      + apply (RealSetoid.real_eq_plus_compat E_total
                 (real_plus (real_opp real_one) real_one) E_total real_zero).
        * apply (real_eq_refl E_total).
        * apply (real_eq_trans _ (real_plus real_one (real_opp real_one))).
          -- apply (real_plus_comm (real_opp real_one) real_one).
          -- apply (real_plus_opp real_one).
      + apply (real_plus_zero E_total). }
  (* 得 1 < E_total，再降 0 < E_total *)
  assert (H1ET : real_lt real_one E_total).
  { exact (real_eq_lt_lt _ _ _ (real_eq_sym _ _ HL) (real_lt_eq_lt _ _ _ Hstep HR)). }
  assert (H2 : real_lt real_zero E_total).
  { exact (real_lt_le_trans real_zero real_one E_total real_lt_zero_one (inl H1ET)). }
  (* 第三步：eB E_total：0 < E_total - E_total == 0，矛盾 *)
  pose proof (real_lt_eq_lt real_zero (real_plus E_total (real_opp E_total)) real_zero
                (eB E_total H2) (real_plus_opp E_total)) as Hcon.
  (* Empty_set（S01_BaseRing.Not 的结论型）无构造子，destruct 即清任意目标 *)
  destruct (real_lt_irrefl real_zero Hcon).
Qed.

(* ---------- 包装：EntropyDiffReal 全 10 槽空虚真 ---------- *)
Theorem fa52_EntropyDiffReal_premises_unsat :
  forall (Omega_A : forall E_A : Real, real_lt real_zero E_A -> Real)
         (Omega_B : forall E_B : Real, real_lt real_zero E_B -> Real)
         (dA : RealDifferentiable Omega_A)
         (dB : RealDifferentiable Omega_B)
         (pA : forall (E_A : Real) (H : real_lt real_zero E_A),
                real_lt real_zero (Omega_A E_A H))
         (pB : forall (E_B : Real) (H : real_lt real_zero E_B),
                real_lt real_zero (Omega_B E_B H))
         (wdB : forall (a b : Real) (Ha : real_lt real_zero a) (Hb : real_lt real_zero b),
                real_eq a b -> real_eq (Omega_B a Ha) (Omega_B b Hb))
         (E_total k_B : Real)
         (eB : forall (E_A : Real) (H : real_lt real_zero E_A),
                real_lt real_zero (real_plus E_total (real_opp E_A))),
    False.
Proof.
  intros Omega_A Omega_B dA dB pA pB wdB E_total k_B eB.
  exact (fa52_EDP_E_B_pos_unsat E_total eB).
Qed.

Print Assumptions fa52_EDP_E_B_pos_unsat.
Print Assumptions fa52_EntropyDiffReal_premises_unsat.

Require Import S01_BaseRing.
Require Import fa51_sumpos_id.
Require Import fa56_id_carrier.
From Stdlib Require Import Lists.List.
Import ListNotations.

Section Fa56bExt.

Context {RI : RealInterfaceEnhanced}.
Variable S : Set.
Variable enum : list S.

Let R        := @R RI.
Let zero     := @zero RI.
Let one      := @one RI.
Let plus     := @plus RI.
Let mult     := @mult RI.
Let le       := @le RI.
Let lt       := @lt RI.

(* ============ 槽VI：J 消去器 + list 判别核 + 非空构造族 =========== *)
(* S04:1588-1589 vocab_nonempty 先例形的构造兑现。核心技术：        *)
(* Id 的依赖匹配消去（本载体首用 J 规则；fa51/fa56 只用过            *)
(* id_sym/id_trans/id_cong 三件套）。                               *)

(* 通用传输（J 消去器）：p : Id x y 把 Q x 中的元素搬到 Q y。        *)
Definition fa56b_id_transport (A : Set) (Q : A -> Set) (x y : A)
                              (p : Id x y) (h : Q x) : Q y :=
  match p in Id _ a return Q a with
  | id_refl => h
  end.

(* list 判别核：nil 与 cons 的 Id 分离（Set 值型别检验函数）。      *)
Definition fa56b_list_case (T : Set) (l : list T) : Set :=
  match l with
  | nil => unit
  | _ => Empty_set
  end.

(* 判别核引理：Id (t::l) nil 无居民（cons ≠ nil）。
   证体以 Id 指标剪除形收束：指标 (t::l) 与 nil 无同一构造支可统一，
   矛盾支就地封闭。 *)
Lemma fa56b_cons_nil_id_contra : forall (T : Set) (t : T) (l : list T),
  Id (t :: l) nil -> Empty_set.
Proof.
  intros T t l H. inversion H.
Qed.

(* 槽语句实例化：单点词表满足 vocab_nonempty（S04:1589 形）。        *)
Theorem fa56b_singleton_nonempty :
  forall (T : Set) (t0 : T), Not (Id (cons t0 (@nil T)) (@nil T)).
Proof.
  intros T t0 H.
  exact (fa56b_cons_nil_id_contra T t0 nil H).
Qed.

(* 非空闭包·cons：头加元素保非空。                                  *)
Theorem fa56b_cons_nonempty :
  forall (T : Set) (t0 : T) (l : list T),
    Not (Id l nil) -> Not (Id (cons t0 l) nil).
Proof.
  intros T t0 l Hne H.
  exact (fa56b_cons_nil_id_contra T t0 l H).
Qed.

(* 非空闭包·append 左：左支非空则并非空。                           *)
Theorem fa56b_append_nonempty_l :
  forall (T : Set) (l l' : list T),
    Not (Id l nil) -> Not (Id (l ++ l') nil).
Proof.
  intros T l l' Hne H. destruct l as [| t r].
  - exact (Hne (@id_refl (list T) (@nil T))).
  - exact (fa56b_cons_nil_id_contra T t (r ++ l') H).
Qed.

(* 非空闭包·append 右：右支非空则并非空（逐支 case）。              *)
Theorem fa56b_append_nonempty_r :
  forall (T : Set) (l l' : list T),
    Not (Id l' nil) -> Not (Id (l ++ l') nil).
Proof.
  intros T l l' Hne H. destruct l as [| t r].
  - exact (Hne H).
  - exact (fa56b_cons_nil_id_contra T t (r ++ l') H).
Qed.

(* 伴件：严格正性的 Id 不变性（引擎前提在 Id 重整下稳定）。          *)
Theorem fa56b_lt_transport :
  forall (a b : R), Id a b -> lt zero a -> lt zero b.
Proof.
  intros a b p H.
  exact (fa56b_id_transport R (fun w => lt zero w) a b p H).
Qed.

(* 伴件：非负性的 Id 不变性。                                       *)
Theorem fa56b_le_transport :
  forall (a b : R), Id a b -> le zero a -> le zero b.
Proof.
  intros a b p H.
  exact (fa56b_id_transport R (fun w => le zero w) a b p H).
Qed.

(* ============ 槽VII：引擎扩展——逐点 Id ⟹ 和 Id ==================== *)
(* S04 steady_state_boltzmann（L1921）依存的 sum_over_S_ext 之       *)
(* fa51_sumd 列表载体副本；为槽VIII 稳态副本的关键件。               *)

Theorem fa56b_sumd_cong :
  forall (f g : S -> R) (l : list S),
    (forall s : S, Id (f s) (g s)) ->
    Id (fa51_sumd S f l) (fa51_sumd S g l).
Proof.
  intros f g l Hpt. induction l as [| x t IH].
  - exact (@id_refl R zero).
  - exact (id_cong2 (fun a b => plus a b) (Hpt x) IH).
Qed.

(* 乘积换序过和（槽VIII 逐点平衡的批量版）。                         *)
Theorem fa56b_sumd_swap_mult :
  forall (f g : S -> R) (l : list S),
    Id (fa51_sumd S (fun s => mult (f s) (g s)) l)
       (fa51_sumd S (fun s => mult (g s) (f s)) l).
Proof.
  intros f g l.
  exact (fa56b_sumd_cong (fun s => mult (f s) (g s))                         (fun s => mult (g s) (f s)) l                         (fun s => mult_comm (f s) (g s))).
Qed.

(* ============ 槽VIII：S04:1905-1907 detailed_balance 槽 + ========= *)
(*              S04:1913 steady_state_boltzmann 列表载体副本 ========== *)
(* 兑现：转移取独立提议核 k(s,s') := π(s')（Boltzmann-Gibbs 稳态分布  *)
(* 自身），平衡槽由 mult_comm 闭合；稳态件为主非平凡件（sumd_cong  *)
(* + fa56 线性件 + 行归一 + mult_one 四段链）。π 取 fa56_markov_kernel *)
(* 同项（正性/非负/归一化三伴件由 fa56 已证件直接继承，零重复施工）。 *)

Definition fa56b_boltzmann_prob (base_loss : S -> R) (D : R) (D_pos : lt zero D)
                                (Hne : Not (Id enum nil)) (s : S) : R :=
  fa56_markov_kernel S enum base_loss D D_pos
    (fa51_Z_temp_pos S enum base_loss D D_pos Hne) s.

Definition fa56b_independence_transition
           (base_loss : S -> R) (D : R) (D_pos : lt zero D)
           (Hne : Not (Id enum nil)) (s s' : S) : R :=
  fa56b_boltzmann_prob base_loss D D_pos Hne s'.

(* S04:1905-1907 槽语句实例：独立提议核逐点满足详细平衡。             *)
Theorem fa56b_detailed_balance :
  forall (base_loss : S -> R) (D : R) (D_pos : lt zero D)
         (Hne : Not (Id enum nil)) (s s' : S),
    Id (mult (fa56b_boltzmann_prob base_loss D D_pos Hne s)
             (fa56b_independence_transition base_loss D D_pos Hne s s'))
       (mult (fa56b_boltzmann_prob base_loss D D_pos Hne s')
             (fa56b_independence_transition base_loss D D_pos Hne s' s)).
Proof.
  intros base_loss D D_pos Hne s s'.
  exact (mult_comm (fa56b_boltzmann_prob base_loss D D_pos Hne s)                   (fa56b_boltzmann_prob base_loss D D_pos Hne s')).
Qed.

(* S04:1913 steady_state_boltzmann 之 fa51_sumd 列表载体副本：        *)
(* 逐点平衡 + 行归一 ⟹ π 是平稳分布（Σ_{s'} π(s')k(s',s) = π(s)）。  *)
Theorem fa56b_boltzmann_stationary :
  forall (pi : S -> R) (k : S -> S -> R),
    (forall s s' : S,
        Id (mult (pi s') (k s' s)) (mult (pi s) (k s s'))) ->
    (forall s : S, Id (fa51_sumd S (fun s' => k s s') enum) one) ->
    forall s : S,
      Id (fa51_sumd S (fun s' => mult (pi s') (k s' s)) enum) (pi s).
Proof.
  intros pi k Hdb Hnorm s.
  exact (id_trans           (fa56b_sumd_cong (fun s' => mult (pi s') (k s' s))                            (fun s' => mult (pi s) (k s s')) enum                            (fun x => Hdb s x))           (id_trans              (fa56_sumd_mult_const S (pi s) (fun s' => k s s') enum)              (id_trans                 (id_cong (fun y => mult (pi s) y) (Hnorm s))                 (mult_one (pi s))))).
Qed.

(* ============ 槽IX：S05:5968-5983 跨域标度槽（sigT 形） ============ *)
(* 槽语句：cross_domain_scaling : sigT (fun alpha : R => forall N,    *)
(*   Id (loss_drop N) (mult (power (of_nat N) alpha) (f_N N)))。      *)
(* 兑现：loss_drop 装法定义件（幂律形式），槽的 sigT 见证由 existT    *)
(* 直接装配；alpha:=one、power:=mult 特化伴件走 mult_one 归一链。     *)

Definition fa56b_loss_drop (power : R -> R -> R) (of_nat_R : nat -> R)
                           (f_N : nat -> R) (alpha : R) (N : nat) : R :=
  mult (power (of_nat_R N) alpha) (f_N N).

(* 槽语句的 sigT 见证装配（存在性面一次兑现）。                       *)
Theorem fa56b_cross_domain_scaling :
  forall (power : R -> R -> R) (of_nat_R : nat -> R) (f_N : nat -> R)
         (alpha : R),
    sigT (fun a : R => forall N : nat,
            Id (fa56b_loss_drop power of_nat_R f_N a N)
               (mult (power (of_nat_R N) a) (f_N N))).
Proof.
  intros power of_nat_R f_N alpha.
  exact (existT _ alpha (fun N => @id_refl R _)).
Qed.

(* 特化伴件：alpha := one、power := mult 时幂律退化线性标度           *)
(* （mult_one 右单位元经 id_cong 提升进乘积，非平凡归一链）。         *)
Theorem fa56b_cross_domain_linear :
  forall (of_nat_R : nat -> R) (f_N : nat -> R) (N : nat),
    Id (fa56b_loss_drop mult of_nat_R f_N one N)
       (mult (of_nat_R N) (f_N N)).
Proof.
  intros of_nat_R f_N N.
  unfold fa56b_loss_drop.
  exact (id_cong (fun y => mult y (f_N N)) (mult_one (of_nat_R N))).
Qed.

End Fa56bExt.

(* ============ 假设面闭合申报 ============ *)

Print Assumptions fa56b_id_transport.
Print Assumptions fa56b_cons_nil_id_contra.
Print Assumptions fa56b_singleton_nonempty.
Print Assumptions fa56b_cons_nonempty.
Print Assumptions fa56b_append_nonempty_l.
Print Assumptions fa56b_append_nonempty_r.
Print Assumptions fa56b_lt_transport.
Print Assumptions fa56b_le_transport.
Print Assumptions fa56b_sumd_cong.
Print Assumptions fa56b_sumd_swap_mult.
Print Assumptions fa56b_detailed_balance.
Print Assumptions fa56b_boltzmann_stationary.
Print Assumptions fa56b_cross_domain_scaling.
Print Assumptions fa56b_cross_domain_linear.
