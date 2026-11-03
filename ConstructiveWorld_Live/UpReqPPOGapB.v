(* UpReqPPOGapB.v —— ppo_gap_exact 的 ≤_B 对偶面件。              *) (* 使命： 本件在 Real 层建造 PPO 保守族 B 形精确恒等式线的对偶     *) (*   第二层：gapb_gap 恒等式、差非负 ≤_B 主件与保守性推论。       *) (* 依赖： CW_ConstructiveWorld_219、UpRealLeB、UpRealLeB2、UpRealLeB3。 *)
(* 构造性： real_le_b 为 Set 值 forall 型；real_lt sigT 见证型；  *) (*   零 Prop 泄露；纯项模式 term-mode 显式组装（real_eq 非 Id，   *)
(*   禁改写，全链 real_eq_trans/compat）；全 Qed 闭合；零公理。   *) (* 编译配方： 9.1 直调（toolchain env.sh 同源）、cpu_guard 绑核。 *)
(* 结论诚实边界：本件全库只主张 ≤_B（real_le_b）形；Or 形精确     *) (*   real_le zero gapb_gap 不主张——该面须 real_min Or 形下界      *)
(*   （Real 层仅 real_min_le_l_eps 逐 eps 形在案），Or 形精确完成 *) (*   构造性不可证（UpRealLeB 已知限制同源），不越界。             *)
(* 备注：既有文件零改（UpReqPPO.v/UpReqPPOPlain.v/G06_BForm.v/   *) (*   UpRealLeB*.v 只读）；gapb_ 前缀库内独占。                    *)
(* 节 GapBPPOLeB：节参面 = RealPPOMain / UpRealLeB Part C /       *) (*   G06_BForm RealPPOLeBFull 同位（ext/le/add/linear 四参数位 +  *)
(*   数据参），减 sum_pos 参数位（本件 E≥0 路线不需要）。          *) (* 件表：[标量内机 2] gapb_plus_mid_opp / gapb_plus_opp_swap；    *)
(*   [副本件] gapb_gap_exact；[保底件] gapb_gap_exact_res_nonneg_B；*) (*   [内机] gapb_res_weight_nonneg；[主件] gapb_gap_nonneg_B；    *)
(*   [连接件] gapb_le_b_of_gap_nonneg_b / gapb_conservative_B。   *) (* 上游侦察：rppo_ppo_gap_exact（UpReqPPO，req 层恒等式：          *)
(*   req_minus IS PPO == Σ π_old·((r − min(r, clip r))·adv)，     *) (*   min/r_max 符号载体零 le 依存）在本库 Real 层副本建造；兄弟件  *)
(*   G06_BForm.real_ppo_conservative_B_full / UpRealLeB.real_ppo_ *) (*   conservative_B 给「PPO ≤_B IS」下界；本件做恒等式差的逐 eps  *)
(*   非负化层（≤_B 对偶面）。                                     *) (* 本件清单（前缀 gapb_；9 定义 + 8 件）：                        *)
(*   [标量内机 2]                                                *) (*     gapb_plus_mid_opp      a+(b+−a) == b（中位对翻退化）       *)
(*     gapb_plus_opp_swap     (y+x)+−y == x（换位退化）           *) (*   [依存机器链副本件] gapb_gap_exact：real_eq gapb_gap gapb_gap_sum *)
(*     （rppo_ppo_gap_exact 的 Real 层逐位副本：逐点双层分配拆分   *) (*       π·(r·A) == π·(m·A)+π·((r+−m)·A)（distrib/distrib_r 零   *)
(*       opp 求和机器路线）+ sum_ext 输运 + sum_add 拆项 + 换位退化完成） *) (*   [保底件] gapb_gap_exact_res_nonneg_B：0 ≤_B (恒等式两侧差)   *)
(*     （逐 eps 层：两侧差 ≡ 恒等式两端之 self-diff ≡ 0，leb3 运输单步） *) (*   [内机] gapb_res_weight_nonneg：0 ≤ E（E := Σ π_old·adv 的非负性 *)
(*     接口内可导：逐点双正 mult_positive + sum_le 参数位 + Σ0≡0 换形）  *) (*   [主件·完整对偶件] gapb_gap_nonneg_B：0 ≤_B (IS − PPO)        *)
(*     （real_le_closure_b_nonneg 完成：C := E 仅需非负——广义完成器 *) (*       解锁，零新增前提；逐 eps 体 = conservative_eps + Or 形差非负 *)
(*       real_le_minus_nonneg_aux + res_fold 换形）               *) (*   [连接件 1] gapb_le_b_of_gap_nonneg_b：0 ≤_B (x+−y) ⟹ y ≤_B x *)
(*     （纯 Bishop 代数对翻桥：平移基元 + 中位对翻退化 + lt 换形） *) (*   [连接件 2] gapb_conservative_B：PPO ≤_B IS                   *)
(*     （语句面 = G06_BForm.real_ppo_conservative_B_full 结论     *) (*       逐字同形——对偶件 ⟹ 已有 B 形保守件的推论关系，消解即核； *)
(*       前提面较 B_full 减 sum_pos 参数位（E≥0 路线替代 E>0 证书路线）） *) (* 结论诚实边界（不越 Or 不可证结果面）：                          *)
(*   1. 本件全库只主张 ≤_B（real_le_b，Set 值 forall 型）形；Or 形 *) (*      精确 real_le zero gapb_gap（进而 real_le PPO IS）不主张——  *)
(*      该面须 real_min Or 形下界（Real 层仅 real_min_le_l_eps    *) (*      逐 eps 形在案），UpRealLeB 结论 2「Or 形精确完成构造性     *)
(*      不可证」同源，不越。                                      *) (*   2. E 的非负性（0 ≤ E 接口内可导，见内机），严格正性参数仍归    *)
(*      温度界结论位。                                            *) (*   3. 与兄弟件语义互补零重复：G06_BForm/rpl_ 簇给「PPO ≤_B IS」  *)
(*      下界，本件给「差 ≡ 恒等式右端（逐 eps 非负化）」精确层+对翻桥。 *) (* 红线：real_le_b Set 值 forall 型、real_lt sigT 见证型零 Prop 泄露；*)
(*   既有文件零改（依存件只读）；纯项模式 term-mode 显式组装       *) (*   （real_eq 非 Id 禁改写）；全 Qed 闭合；零公理面。             *)

From Stdlib Require Import QArith.Qring.
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
Require Import UpRealLeB.
Require Import UpRealLeB2.
Require Import UpRealLeB3.

(* ============================================================ *)
(* 节 GapBPPOLeB：节参面 = RealPPOMain / UpRealLeB Part C /          *)
(*   G06_BForm RealPPOLeBFull 同位（ext/le/add/linear 四参数位 + 数据参），     *)
(*   减 sum_pos 参数位（本件 E≥0 路线不需要）。                                *)
(* ============================================================ *)
Section GapBPPOLeB.

Variable S : Type.
Variable real_sum_over_S : (S -> Real) -> Real.
Variable real_sum_over_S_ext : forall (f g : S -> Real),
  (forall s : S, real_eq (f s) (g s)) -> real_eq (real_sum_over_S f) (real_sum_over_S g).
Variable real_sum_over_S_le : forall (f g : S -> Real),
  (forall s : S, real_le (f s) (g s)) -> real_le (real_sum_over_S f) (real_sum_over_S g).
Variable real_sum_over_S_add : forall (f g : S -> Real),
  real_eq (real_sum_over_S (fun s : S => real_plus (f s) (g s)))
          (real_plus (real_sum_over_S f) (real_sum_over_S g)).
Variable real_sum_over_S_linear : forall (a : Real) (f : S -> Real),
  real_eq (real_sum_over_S (fun s : S => real_mult a (f s)))
          (real_mult a (real_sum_over_S f)).

Variable real_pi_star_ : S -> Real.
Variable real_pi_old : S -> Real.
Variable real_pi_old_pos : forall s : S, real_lt real_zero (real_pi_old s).
Variable real_advantage_fn : S -> Real.
Variable real_advantage_pos : forall s : S, real_lt real_zero (real_advantage_fn s).
Variable epsilon : Real.

(* ---- 节内定义（RealPPOMain 同位 δ 透明） ---- *)
Definition gapb_ratio (s : S) : Real :=
  real_importance_ratio_ S real_pi_star_ real_pi_old real_pi_old_pos s.
Definition gapb_clip (r : Real) : Real := real_ppo_clip_ epsilon r.
Definition gapb_min_ratio (s : S) : Real :=
  real_min (gapb_ratio s) (gapb_clip (gapb_ratio s)).
(* 裁剪 PPO 目标（B_full 结论左端同形） *)
Definition gapb_ppo_objective : Real :=
  real_sum_over_S (fun s : S =>
    real_mult (real_pi_old s)
              (real_mult (gapb_min_ratio s) (real_advantage_fn s))).
(* IS 目标（B_full 结论右端同形） *)
Definition gapb_is_objective : Real :=
  real_sum_over_S (fun s : S =>
    real_mult (real_pi_old s) (real_mult (gapb_ratio s) (real_advantage_fn s))).
(* gap：IS − PPO（Real 层 minus 形 real_plus+opp；无 real_minus） *)
Definition gapb_gap : Real :=
  real_plus gapb_is_objective (real_opp gapb_ppo_objective).
(* 恒等式右端逐点项/求和（rppo_ppo_gap_exact 展开形状：r − min(r, clip r)） *)
Definition gapb_gap_pointwise (s : S) : Real :=
  real_mult (real_pi_old s)
            (real_mult (real_plus (gapb_ratio s) (real_opp (gapb_min_ratio s)))
                       (real_advantage_fn s)).
Definition gapb_gap_sum : Real := real_sum_over_S gapb_gap_pointwise.
(* 残差权系数 E := Σ π_old·adv（real_ppo_res_weight 同位 δ 透明，res_fold 直接匹配） *)
Definition gapb_res_weight : Real :=
  real_ppo_res_weight S real_sum_over_S real_pi_old real_advantage_fn.

(* ============ 标量内机 ============ *)

(* 内机 1：中位对翻退化 a+(b+−a) == b（连接桥与恒等式逐点共用） *)
Lemma gapb_plus_mid_opp : forall a b : Real,
  real_eq (real_plus a (real_plus b (real_opp a))) b.
Proof.
  intros a b.
  apply (real_eq_trans _ (real_plus a (real_plus (real_opp a) b)) _).
  - apply (RealSetoid.real_eq_plus_compat a (real_plus b (real_opp a))
                                          a (real_plus (real_opp a) b)).
    + apply real_eq_refl.
    + apply real_plus_comm.
  - apply (real_eq_trans _ (real_plus (real_plus a (real_opp a)) b) _).
    + apply real_plus_assoc.
    + apply (real_eq_trans _ (real_plus real_zero b) _).
      * apply (RealSetoid.real_eq_plus_compat (real_plus a (real_opp a))
                 b real_zero b).
        -- apply real_plus_opp.
        -- apply real_eq_refl.
      * apply (real_eq_trans _ (real_plus b real_zero) _).
        -- apply real_plus_comm.
        -- apply real_plus_zero.
Qed.

(* 内机 2：换位退化 (y+x)+−y == x（恒等式完成位） *)
Lemma gapb_plus_opp_swap : forall x y : Real,
  real_eq (real_plus (real_plus y x) (real_opp y)) x.
Proof.
  intros x y.
  apply (real_eq_trans _ (real_plus y (real_plus x (real_opp y))) _).
  - apply real_eq_sym. apply real_plus_assoc.
  - exact (gapb_plus_mid_opp y x).
Qed.

(* ============ 内机：E 的非负性（接口内可导，零严格正性主张） ============ *)
Lemma gapb_res_weight_nonneg : real_le real_zero gapb_res_weight.
Proof.
  (* Σ 常零 ≡ 0（ext 逐点 + linear 标量提取 + mult_zero） *)
  assert (Hzero : real_eq (real_sum_over_S (fun _ : S => real_zero)) real_zero).
  { apply (real_eq_trans _
             (real_sum_over_S (fun s : S =>
                real_mult real_zero (real_mult (real_pi_old s) (real_advantage_fn s)))) _).
    - apply (real_sum_over_S_ext (fun _ : S => real_zero)).
      intro s.
      apply (real_eq_trans _
               (real_mult (real_mult (real_pi_old s) (real_advantage_fn s)) real_zero) _).
      + apply real_eq_sym. apply real_mult_zero.
      + apply real_eq_sym. apply real_mult_comm.
    - apply (real_eq_trans _
               (real_mult real_zero
                  (real_sum_over_S (fun s : S =>
                     real_mult (real_pi_old s) (real_advantage_fn s)))) _).
      + apply (real_sum_over_S_linear real_zero
                 (fun s : S => real_mult (real_pi_old s) (real_advantage_fn s))).
      + apply (real_eq_trans _
                 (real_mult (real_sum_over_S (fun s : S =>
                     real_mult (real_pi_old s) (real_advantage_fn s))) real_zero) _).
        * apply real_eq_sym. apply real_mult_comm.
        * apply real_mult_zero. }
  exact (RealSetoid.real_le_id_l real_zero
           (real_sum_over_S (fun _ : S => real_zero))
           gapb_res_weight
           (real_eq_sym _ _ Hzero)
           (real_sum_over_S_le (fun _ : S => real_zero)
              (fun s : S => real_mult (real_pi_old s) (real_advantage_fn s))
              (fun s : S => real_le_from_lt_aux real_zero
                 (real_mult (real_pi_old s) (real_advantage_fn s))
                 (real_mult_positive (real_pi_old s) (real_advantage_fn s)
                    (real_pi_old_pos s) (real_advantage_pos s))))).
Qed.

(* ============ 依存机器链副本件：恒等式（rppo_ppo_gap_exact Real 层） ============ *)
(* 逐点拆分 π·(r·A) == π·(m·A) + π·((r+−m)·A)：distrib/distrib_r 双层分配， *)
(* 零 opp 求和机器（Σ opp 免建——拆分形先走 sum_add 再换位退化）。           *)
Lemma gapb_gap_exact : real_eq gapb_gap gapb_gap_sum.
Proof.
  assert (Hpt : forall s : S,
    real_eq (real_mult (real_pi_old s) (real_mult (gapb_ratio s) (real_advantage_fn s)))
            (real_plus (real_mult (real_pi_old s)
                                  (real_mult (gapb_min_ratio s) (real_advantage_fn s)))
                       (gapb_gap_pointwise s))).
  { intro s.
    apply (real_eq_trans _
             (real_mult (real_pi_old s)
                        (real_mult (real_plus (gapb_min_ratio s)
                                              (real_plus (gapb_ratio s)
                                                         (real_opp (gapb_min_ratio s))))
                                   (real_advantage_fn s))) _).
    - apply (RealSetoid.real_eq_mult_compat (real_pi_old s)
               (real_mult (gapb_ratio s) (real_advantage_fn s))
               (real_pi_old s)
               (real_mult (real_plus (gapb_min_ratio s)
                                     (real_plus (gapb_ratio s)
                                                (real_opp (gapb_min_ratio s))))
                          (real_advantage_fn s))).
      + apply real_eq_refl.
      + apply (RealSetoid.real_eq_mult_compat (gapb_ratio s) (real_advantage_fn s)
                 (real_plus (gapb_min_ratio s)
                            (real_plus (gapb_ratio s) (real_opp (gapb_min_ratio s))))
                 (real_advantage_fn s)).
        * exact (real_eq_sym _ _
                   (gapb_plus_mid_opp (gapb_min_ratio s) (gapb_ratio s))).
        * apply real_eq_refl.
    - apply (real_eq_trans _
               (real_mult (real_pi_old s)
                          (real_plus (real_mult (gapb_min_ratio s) (real_advantage_fn s))
                                     (real_mult (real_plus (gapb_ratio s)
                                                           (real_opp (gapb_min_ratio s)))
                                                (real_advantage_fn s)))) _).
      + apply (RealSetoid.real_eq_mult_compat (real_pi_old s)
                 (real_mult (real_plus (gapb_min_ratio s)
                                       (real_plus (gapb_ratio s)
                                                  (real_opp (gapb_min_ratio s))))
                            (real_advantage_fn s))
                 (real_pi_old s)
                 (real_plus (real_mult (gapb_min_ratio s) (real_advantage_fn s))
                            (real_mult (real_plus (gapb_ratio s)
                                                  (real_opp (gapb_min_ratio s)))
                                       (real_advantage_fn s)))).
        * apply real_eq_refl.
        * apply real_eq_sym.
          exact (real_distrib_r (gapb_min_ratio s)
                  (real_plus (gapb_ratio s) (real_opp (gapb_min_ratio s)))
                  (real_advantage_fn s)).
      + apply real_distrib. }
  assert (Hsplit : real_eq gapb_is_objective
                     (real_plus gapb_ppo_objective gapb_gap_sum)).
  { apply (real_eq_trans _
             (real_sum_over_S (fun s : S =>
                real_plus (real_mult (real_pi_old s)
                                     (real_mult (gapb_min_ratio s) (real_advantage_fn s)))
                          (gapb_gap_pointwise s))) _).
    - apply (real_sum_over_S_ext (fun s : S =>
         real_mult (real_pi_old s) (real_mult (gapb_ratio s) (real_advantage_fn s)))).
      intro s. exact (Hpt s).
    - exact (real_sum_over_S_add (fun s : S =>
         real_mult (real_pi_old s) (real_mult (gapb_min_ratio s) (real_advantage_fn s)))
         gapb_gap_pointwise). }
  unfold gapb_gap.
  apply (real_eq_trans _
           (real_plus (real_plus gapb_ppo_objective gapb_gap_sum)
                      (real_opp gapb_ppo_objective)) _).
  - apply (RealSetoid.real_eq_plus_compat gapb_is_objective
             (real_opp gapb_ppo_objective)
             (real_plus gapb_ppo_objective gapb_gap_sum)
             (real_opp gapb_ppo_objective)).
    + exact Hsplit.
    + apply real_eq_refl.
  - exact (gapb_plus_opp_swap gapb_gap_sum gapb_ppo_objective).
Qed.

(* ============ 保底件：恒等式两侧差的非负性逐 eps 层 ============ *)
(* 0 ≤_B (gapb_gap − gapb_gap_sum)：两侧差 ≡ 恒等式两端 self-diff ≡ 0。     *)
Lemma gapb_gap_exact_res_nonneg_B :
  real_le_b real_zero (real_plus gapb_gap (real_opp gapb_gap_sum)).
Proof.
  apply (leb3_le_b_eq_r real_zero real_zero
           (real_plus gapb_gap (real_opp gapb_gap_sum))).
  - apply leb3_le_b_refl.
  - apply real_eq_sym.
    apply (real_eq_trans _ (real_plus gapb_gap_sum (real_opp gapb_gap_sum)) _).
    + apply (RealSetoid.real_eq_plus_compat gapb_gap (real_opp gapb_gap_sum)
               gapb_gap_sum (real_opp gapb_gap_sum)).
      * exact gapb_gap_exact.
      * apply real_eq_refl.
    + apply real_plus_opp.
Qed.

(* ============ 主件：完整对偶件——0 ≤_B (IS − PPO)，零新增前提 ============ *)
(* 完成路线：real_le_closure_b_nonneg（F.1，C := E 仅需非负）+ 逐 eps 体     *)
(*   = conservative_eps（13 参消解）+ real_le_minus_nonneg_aux（Or 形差     *)
(*   非负，顶层）+ res_fold 残差折叠换形。                            *)
Lemma gapb_gap_nonneg_B : real_le_b real_zero gapb_gap.
Proof.
  apply (real_le_closure_b_nonneg real_zero gapb_gap gapb_res_weight
           gapb_res_weight_nonneg).
  intros eps Heps.
  pose proof (real_ppo_conservative_eps S real_sum_over_S real_sum_over_S_ext
                real_sum_over_S_le real_sum_over_S_add real_pi_star_ real_pi_old
                real_pi_old_pos real_advantage_fn real_advantage_pos
                epsilon eps Heps) as Hce.
  apply (RealSetoid.real_le_id_r real_zero
           (real_plus (real_plus gapb_is_objective
                        (real_sum_over_S (fun s : S =>
                           real_mult (real_pi_old s)
                                     (real_mult eps (real_advantage_fn s)))))
                      (real_opp gapb_ppo_objective))
           (real_plus gapb_gap (real_mult gapb_res_weight eps))).
  - (* 换形：((IS+R)+−PPO) ≡ gapb_gap + E·eps（assoc/comm 三步 + res_fold） *)
    apply (real_eq_trans _
             (real_plus gapb_is_objective
                        (real_plus (real_sum_over_S (fun s : S =>
                           real_mult (real_pi_old s)
                                     (real_mult eps (real_advantage_fn s))))
                                   (real_opp gapb_ppo_objective))) _).
    + apply real_eq_sym. apply real_plus_assoc.
    + apply (real_eq_trans _
               (real_plus gapb_is_objective
                          (real_plus (real_opp gapb_ppo_objective)
                                     (real_sum_over_S (fun s : S =>
                                        real_mult (real_pi_old s)
                                                  (real_mult eps (real_advantage_fn s)))))) _).
      * apply (RealSetoid.real_eq_plus_compat gapb_is_objective
                 (real_plus (real_sum_over_S (fun s : S =>
                    real_mult (real_pi_old s) (real_mult eps (real_advantage_fn s))))
                    (real_opp gapb_ppo_objective))
                 gapb_is_objective
                 (real_plus (real_opp gapb_ppo_objective)
                            (real_sum_over_S (fun s : S =>
                               real_mult (real_pi_old s)
                                         (real_mult eps (real_advantage_fn s)))))).
        -- apply real_eq_refl.
        -- apply real_plus_comm.
      * apply (real_eq_trans _
                 (real_plus (real_plus gapb_is_objective (real_opp gapb_ppo_objective))
                            (real_sum_over_S (fun s : S =>
                               real_mult (real_pi_old s)
                                         (real_mult eps (real_advantage_fn s))))) _).
        -- apply real_plus_assoc.
        -- apply (RealSetoid.real_eq_plus_compat
                     (real_plus gapb_is_objective (real_opp gapb_ppo_objective))
                     (real_sum_over_S (fun s : S =>
                        real_mult (real_pi_old s) (real_mult eps (real_advantage_fn s))))
                     (real_plus gapb_is_objective (real_opp gapb_ppo_objective))
                     (real_mult gapb_res_weight eps)).
          ++ apply real_eq_refl.
          ++ exact (real_ppo_res_fold S real_sum_over_S real_sum_over_S_ext
                      real_sum_over_S_linear real_pi_old real_advantage_fn eps).
  - exact (real_le_minus_nonneg_aux gapb_ppo_objective
             (real_plus gapb_is_objective
                (real_sum_over_S (fun s : S =>
                   real_mult (real_pi_old s) (real_mult eps (real_advantage_fn s)))))
             Hce).
Qed.

(* ============ 连接件 1：对翻桥（纯 Bishop 代数，全泛型可复用） ============ *)
Lemma gapb_le_b_of_gap_nonneg_b :
  forall x y : Real,
    real_le_b real_zero (real_plus x (real_opp y)) -> real_le_b y x.
Proof.
  intros x y H.
  unfold real_le_b in H. unfold real_le_b.
  intros d Hd.
  pose proof (H d Hd) as Hlt.
  pose proof (real_lt_plus_translate y real_zero
                (real_plus (real_plus x (real_opp y)) d) Hlt) as Htr.
  assert (Htr2 : real_lt y (real_plus y (real_plus (real_plus x (real_opp y)) d))).
  { apply (RealSetoid.real_lt_id_l y (real_plus y real_zero)
             (real_plus y (real_plus (real_plus x (real_opp y)) d))).
    - apply real_eq_sym. apply real_plus_zero.
    - exact Htr. }
  assert (Heq : real_eq (real_plus y (real_plus (real_plus x (real_opp y)) d))
                        (real_plus x d)).
  { apply (real_eq_trans _
             (real_plus (real_plus y (real_plus x (real_opp y))) d) _).
    - apply real_plus_assoc.
    - apply (RealSetoid.real_eq_plus_compat
               (real_plus y (real_plus x (real_opp y))) d x d).
      + exact (gapb_plus_mid_opp y x).
      + apply real_eq_refl. }
  exact (real_lt_eq_lt y (real_plus y (real_plus (real_plus x (real_opp y)) d))
           (real_plus x d) Htr2 Heq).
Qed.

(* ============ 连接件 2：对偶件 ⟹ 已有 B 形保守件（推论关系消解） ============ *)
(* 语句面 = G06_BForm.real_ppo_conservative_B_full 结论逐字同形；  *)
(* 证明 = 连接件 1 ← 主件 单链（零 sum_pos 参数位、零 E>0 证书前提）。           *)
Theorem gapb_conservative_B :
  real_le_b
    (real_sum_over_S (fun s : S =>
      real_mult (real_pi_old s)
        (real_mult (real_min (real_importance_ratio_ S real_pi_star_ real_pi_old real_pi_old_pos s)
                             (real_ppo_clip_ epsilon (real_importance_ratio_ S real_pi_star_ real_pi_old real_pi_old_pos s)))
                   (real_advantage_fn s))))
    (real_sum_over_S (fun s : S =>
      real_mult (real_pi_old s)
        (real_mult (real_importance_ratio_ S real_pi_star_ real_pi_old real_pi_old_pos s)
                   (real_advantage_fn s)))).
Proof.
  exact (gapb_le_b_of_gap_nonneg_b gapb_is_objective gapb_ppo_objective           gapb_gap_nonneg_B).
Qed.

End GapBPPOLeB.

(* ============================================================ *)
(* 尾注：诚实登记表                                              *)
(*   [分级] 内机 2（标量退化，结构同 rppo 内机 6 之 Real 副本）+ 内机 1 *)
(*     （E≥0：mult_positive 两喂 + sum_le 参数位 + Σ0≡0）+ 恒等式件 *)
(*     （逐点双层分配 + sum_ext 输运 + sum_add + 换位退化——依存    *)
(*     机器链 Real 层逐位副本，路线改良：拆分形先 sum_add 免 Σopp  *)
(*     机器）+ 保底件（leb3 运输单步）+ 主件（非负完成器——E 仅需   *)
(*     ≥0，完整升格零新增前提）+ 连接件 1（对翻桥，泛型）+         *)
(*     连接件 2（B_full 结论面逐字推论消解）。                     *)
(*   [结论边界] Or 形 real_le zero gapb_gap 不主张（同源不可越）； *)
(*     E>0 严格正性结论不被推翻（本件只依存 E≥0 接口内可导非负性）。 *)
(*   [对位] 恒等式件为 rppo_ppo_gap_exact（req 层真证在案）的 Real *)
(*     层副本——两件跨层互证（req 侧依存 UpReqPPO.v）。             *)
(*                                                              *)
(*                                                              *)
(*                                                              *)
(* ============================================================ *)

Print Assumptions gapb_res_weight_nonneg.
Print Assumptions gapb_gap_exact.
Print Assumptions gapb_gap_exact_res_nonneg_B.
Print Assumptions gapb_gap_nonneg_B.
Print Assumptions gapb_le_b_of_gap_nonneg_b.
Print Assumptions gapb_conservative_B.
