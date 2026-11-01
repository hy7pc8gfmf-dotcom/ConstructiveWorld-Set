(* ============================================================
   使命：论文7《率即算法》BoundedSoftmax Section 接口假设深层消融：
     P7A 已证结论 19 Variable 三分类（A8/B11/C6）；本件对 B 类 11 条
     逐个判定「能否从库内更基本原则导出非平凡定理」并施工——bs_swap
     可消融（由 sum_eq_list＋纯 list 组合学 list-Fubini 导出，字段面
     19→18，主定理双定理 no-swap 重述）；enum_nonempty 与其使用产物
     nR>0 逻辑等价；temp/Delta 产物加深（hi>1 与 1≤hi²）；expf 因子-
     倒数恒等式；z 界导出独立上带定理。逐条判定表见文尾附注。
   依赖：S01_BaseRing…S15_TailFEPUp＋AttnDoeblin（bs_nR_pos/
     bs_lo_hi_eq/bs_lo_lt_hi/bs_hi_pos/bs_inv_hi_lo/bs_Zrow_pos/
     bs_Zrow_ge/bs_factor_le_hi/bs_kernel/Zrow/nat_to_R/
     plus_exchange/两主定理）＋Stdlib List，见 Require 面。
   对标：AttnDoeblin 两主定理（no-swap 重述）；S01_BaseRing 有序域
     引理面（lt_irrefl/mult_positive/inv_pos_le_compat 等）。
   构造性：纯构造性、零承认件；Set 层语句；全 Qed；文尾 Print
     Assumptions 全 Closed；红线＝零 公理/承认件/参数/猜想/弃证。
   编译配方：coqc -native-compiler no -q -Q . ""。
   ============================================================ *)
(* ===================================================================== *)
(*   玩具证明体换轨稿：语句面/声明序/依赖面零改动，仅按玩具清单以异构构造性   *)
(*   证明体替换标注定理。头注全中文；零承认件；纯构造性；Set 层零泄露；      *)
(*   真闭合守恒；替换刀刀唯一命中断言；尾取证段原样保留。                   *)
(* ===================================================================== *)

From Stdlib Require Import List.
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
Require Import AttnDoeblin.

(* ################ 段一：list-Fubini 组合学（bs_swap 消融的地基） ################
   出节机 AttnDoeblin.bs_list_sum 上的逐点同余 / 加法线性 / 双重和交换。 *)

Section P7DListSum.
Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {SS : StateSpace RI}.

(* 逐点 Id ⟹ 列表和 Id（bs_list_sum 的 sum_over_S_ext 对应物） *)
Theorem p7d_lsum_ext : forall (f g : S -> R) (l : list S),
  (forall x : S, Id (f x) (g x)) ->
  Id (AttnDoeblin.bs_list_sum f l) (AttnDoeblin.bs_list_sum g l).
Proof.
  intros f g l H. induction l as [| x t IH].
  - exact id_refl.
  - simpl. exact (id_cong2 plus (H x) IH).
Qed.

(* 列表和的加法线性（sum_over_S_add 的列表版） *)
Theorem p7d_lsum_add : forall (f g : S -> R) (l : list S),
  Id (AttnDoeblin.bs_list_sum (fun s : S => plus (f s) (g s)) l)
     (plus (AttnDoeblin.bs_list_sum f l) (AttnDoeblin.bs_list_sum g l)).
Proof.
  intros f g l. induction l as [| x t IH].
  - exact (id_sym (plus_zero zero)).
  - simpl.
    apply (id_trans (id_cong (fun w : R => plus (plus (f x) (g x)) w) IH)).
    exact (AttnDoeblin.plus_exchange (f x) (AttnDoeblin.bs_list_sum f t)
                                     (g x) (AttnDoeblin.bs_list_sum g t)).
Qed.

(* 零函数列表和为零（使用基座 bs_list_const_sum ＋ mult 零元） *)
Theorem p7d_lsum_zero : forall l : list S,
  Id zero (AttnDoeblin.bs_list_sum (fun _ : S => zero) l).
Proof.
  intro l.
  exact (id_sym (id_trans (AttnDoeblin.bs_list_const_sum zero l)
                  (mult_zero (AttnDoeblin.nat_to_R (length l))))).
Qed.

(* 双重列表和交换（一般形：内外列表分立；Fubini 组合学核心） *)
Theorem p7d_lsum_fubini_gen : forall (f : S -> S -> R) (l1 l2 : list S),
  Id (AttnDoeblin.bs_list_sum (fun s : S => AttnDoeblin.bs_list_sum (f s) l2) l1)
     (AttnDoeblin.bs_list_sum (fun s' : S => AttnDoeblin.bs_list_sum (fun s : S => f s s') l1) l2).
Proof.
  intros f l1. induction l1 as [| x t IH]; intro l2.
  - apply (id_trans (p7d_lsum_zero l2)).
    exact (p7d_lsum_ext (fun _ : S => zero)
                        (fun s' : S => AttnDoeblin.bs_list_sum (fun s : S => f s s') nil)
                        l2 (fun s' : S => id_refl)).
  - apply (id_trans (id_cong (fun w : R => plus (AttnDoeblin.bs_list_sum (f x) l2) w)
                             (IH l2))).
    apply (id_sym (p7d_lsum_add (fun s' : S => f x s')
              (fun s' : S => AttnDoeblin.bs_list_sum (fun s : S => f s s') t) l2)).
Qed.

End P7DListSum.

(* ################ 段二：bs_swap 消融主件 ################
   「诚实接口三件」之首 bs_swap 在 sum_eq_list（枚举求和规范化，
   CWE5/CYD7/CZB8 已证结论的已闭合槽）下可整体导出——它不是独立接口位。 *)

Section P7DSwap.
Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {SS : StateSpace RI}.
Context {SO : SumOver RI SS}.

Variable enum : list S.
Variable sum_eq_list : forall g : S -> R,
  Id (sum_over_S g) (AttnDoeblin.bs_list_sum g enum).

Theorem p7d_swap_of_sum_eq_list : forall f : S -> S -> R,
  Id (sum_over_S (fun s : S => sum_over_S (fun s' : S => f s s')))
     (sum_over_S (fun s' : S => sum_over_S (fun s : S => f s s'))).
Proof.
  intro f.
  apply (id_trans (sum_eq_list (fun s : S => sum_over_S (fun s' : S => f s s')))).
  apply (id_trans (p7d_lsum_ext
            (fun s : S => sum_over_S (fun s' : S => f s s'))
            (fun s : S => AttnDoeblin.bs_list_sum (fun s' : S => f s s') enum) enum
            (fun s : S => sum_eq_list (fun s' : S => f s s')))).
  apply (id_trans (p7d_lsum_fubini_gen f enum enum)).
  apply (id_trans (id_sym (p7d_lsum_ext
            (fun s' : S => sum_over_S (fun s : S => f s s'))
            (fun s' : S => AttnDoeblin.bs_list_sum (fun s : S => f s s') enum) enum
            (fun s' : S => sum_eq_list (fun s : S => f s s'))))).
  exact (id_sym (sum_eq_list (fun s' : S => sum_over_S (fun s : S => f s s')))).
Qed.

End P7DSwap.

(* ################ 段三：字段面 19→18——主定理双定理 no-swap 重述 ################ *)

Section P7DNoSwap.
Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {SS : StateSpace RI}.
Context {SO : SumOver RI SS}.

Variable enum : list S.
Variable enum_nonempty : Not (Id enum nil).
Variable temp : R.
Variable temp_pos : lt zero temp.
Variable Delta : R.
Variable Delta_pos : lt zero Delta.
Variable z : S -> S -> R.
Variable z_lb : forall s s' : S, le (opp Delta) (z s s').
Variable z_ub : forall s s' : S, le (z s s') Delta.
Variable expf : R -> R.
Variable expf_pos : forall x : R, lt zero (expf x).
Variable expf_zero : Id (expf zero) one.
Variable expf_plus : forall a b : R, Id (expf (plus a b)) (mult (expf a) (expf b)).
Variable expf_mono_lt : forall a b : R, lt a b -> lt (expf a) (expf b).
Variable expf_mono_le : forall a b : R, le a b -> le (expf a) (expf b).
Variable bs_abs : forall a : R, le zero a -> Id (abs a) a.
Variable bs_lpc : forall a b c d : R, lt a b -> le c d -> lt (plus a c) (plus b d).
Variable sum_eq_list : forall g : S -> R,
  Id (sum_over_S g) (AttnDoeblin.bs_list_sum g enum).
(* 注意：本 Section 不含 bs_swap —— 18 字段。 *)

(* 主定理定理 1（单步 TV 收缩）在无 bs_swap 字段面下成立：
   swap 槽由 p7d_swap_of_sum_eq_list 补位。 *)
Theorem p7d_tv_contraction_no_swap : forall mu nu : S -> R,
  Id (sum_over_S mu) one -> Id (sum_over_S nu) one ->
  le (tv_dist (@attention_step RI SS SO
                 (AttnDoeblin.bs_kernel enum enum_nonempty temp temp_pos Delta
                    z z_lb expf expf_pos expf_mono_le sum_eq_list) mu)
              (@attention_step RI SS SO
                 (AttnDoeblin.bs_kernel enum enum_nonempty temp temp_pos Delta
                    z z_lb expf expf_pos expf_mono_le sum_eq_list) nu))
     (mult (minus one
              (mult (expf (mult (inv_pos temp temp_pos) (opp Delta)))
                    (expf (mult (inv_pos temp temp_pos) (opp Delta)))))
           (tv_dist mu nu)).
Proof.
  intros mu nu Hmu Hnu.
  exact (@AttnDoeblin.bounded_softmax_tv_contraction
           RI SS SO enum enum_nonempty temp temp_pos Delta Delta_pos
           z z_lb z_ub expf expf_pos expf_zero expf_plus expf_mono_lt
           expf_mono_le (p7d_swap_of_sum_eq_list enum sum_eq_list)
           bs_abs bs_lpc sum_eq_list mu nu Hmu Hnu).
Qed.

(* 主定理定理 2（迭代几何率 (1−e^{−2Δ/T})ⁿ）同法 no-swap 重述。 *)
Theorem p7d_tv_iter_no_swap : forall (n : nat) (mu nu : S -> R),
  Id (sum_over_S mu) one -> Id (sum_over_S nu) one ->
  le (tv_dist (@u_titer RI SS SO
                 (AttnDoeblin.bs_kernel enum enum_nonempty temp temp_pos Delta
                    z z_lb expf expf_pos expf_mono_le sum_eq_list) n mu)
              (@u_titer RI SS SO
                 (AttnDoeblin.bs_kernel enum enum_nonempty temp temp_pos Delta
                    z z_lb expf expf_pos expf_mono_le sum_eq_list) n nu))
     (mult (@r_pow RI
              (minus one
                (mult (expf (mult (inv_pos temp temp_pos) (opp Delta)))
                      (expf (mult (inv_pos temp temp_pos) (opp Delta))))) n)
           (tv_dist mu nu)).
Proof.
  intros n mu nu Hmu Hnu.
  exact (@AttnDoeblin.bounded_softmax_tv_iter
           RI SS SO enum enum_nonempty temp temp_pos Delta Delta_pos
           z z_lb z_ub expf expf_pos expf_zero expf_plus expf_mono_lt
           expf_mono_le (p7d_swap_of_sum_eq_list enum sum_eq_list)
           bs_abs bs_lpc sum_eq_list n mu nu Hmu Hnu).
Qed.

End P7DNoSwap.

(* ################ 段四：enum_nonempty ⟷ nR>0（证书-产物等价） ################ *)

Section P7DEnum.
Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {SS : StateSpace RI}.
Context {SO : SumOver RI SS}.

(* 正向＝基座 bs_nR_pos 的使用包装（证书 ⟹ 产物） *)
Theorem p7d_enum_nonempty_gives_nR_pos :
  forall (enum : list S) (enum_nonempty : Not (Id enum nil))
         (sel : forall g : S -> R, Id (sum_over_S g) (AttnDoeblin.bs_list_sum g enum)),
  lt zero (AttnDoeblin.nat_to_R (length enum)).
Proof.
  intros enum enum_nonempty sel.
  exact (AttnDoeblin.bs_nR_pos enum enum_nonempty sel).
Qed.

(* 反向（新证）：产物 ⟹ 证书。enum_nonempty 的全部内容恰为 nR>0——
   接口可以改用解析形陈述而无损。 *)
Theorem p7d_nR_pos_gives_enum_nonempty :
  forall enum : list S,
  lt zero (AttnDoeblin.nat_to_R (length enum)) -> Not (Id enum nil).
Proof.
  intros enum HnR Heq.
  exact (lt_irrefl zero
           (lt_id_r zero (AttnDoeblin.nat_to_R (length enum))
              (AttnDoeblin.nat_to_R (length nil))
              (id_cong (fun l : list S => AttnDoeblin.nat_to_R (length l)) Heq)
              HnR)).
Qed.

End P7DEnum.

(* ################ 段五：温度/Δ 产物加深 ################
   P7A 已证 lo=e^{−Δ/T}<1（p7a_lo_lt_one）；本段补对偶 hi=e^{Δ/T}>1
   与展幅 1≤hi²，完成 softmax 刻度夹逼 lo<1<hi≤hi²。 *)

Section P7DScale.
Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.

(* 对偶补件：hi = e^{Δ/T} > 1（由 0<Δ/T 与 expf 严格单调＋expf_zero） *)
Theorem p7d_hi_gt_one :
  forall (temp : R) (temp_pos : lt zero temp) (Delta : R) (Delta_pos : lt zero Delta)
         (expf : R -> R) (expf_pos : forall x : R, lt zero (expf x))
         (expf_zero : Id (expf zero) one)
         (expf_mono_lt : forall a b : R, lt a b -> lt (expf a) (expf b)),
  lt one (expf (mult (inv_pos temp temp_pos) Delta)).
Proof.
  intros temp temp_pos Delta Delta_pos expf expf_pos expf_zero expf_mono_lt.
  exact (lt_id_r one (expf (mult Delta (inv_pos temp temp_pos)))
           (expf (mult (inv_pos temp temp_pos) Delta))
           (id_cong expf (mult_comm Delta (inv_pos temp temp_pos)))
           (lt_id_l one (expf zero)
              (expf (mult Delta (inv_pos temp temp_pos)))
              (id_sym expf_zero)
              (expf_mono_lt zero (mult Delta (inv_pos temp temp_pos))
                 (mult_positive Delta (inv_pos temp temp_pos) Delta_pos
                    (inv_pos_pos temp temp_pos))))).
Qed.

(* 展幅定理：1 ≤ hi² = e^{2Δ/T}（hi≥lo>0 与 hi·lo=1 的双重使用） *)
Theorem p7d_one_le_hi_sq :
  forall (temp : R) (temp_pos : lt zero temp) (Delta : R) (Delta_pos : lt zero Delta)
         (expf : R -> R) (expf_pos : forall x : R, lt zero (expf x))
         (expf_zero : Id (expf zero) one)
         (expf_plus : forall a b : R, Id (expf (plus a b)) (mult (expf a) (expf b)))
         (expf_mono_lt : forall a b : R, lt a b -> lt (expf a) (expf b)),
  le one (mult (expf (mult (inv_pos temp temp_pos) Delta))
               (expf (mult (inv_pos temp temp_pos) Delta))).
Proof.
  intros temp temp_pos Delta Delta_pos expf expf_pos expf_zero expf_plus expf_mono_lt.
  apply (le_trans _ (mult (expf (mult (inv_pos temp temp_pos) Delta))
                          (expf (mult (inv_pos temp temp_pos) (opp Delta))))).
  - apply (le_id_r one one
             (mult (expf (mult (inv_pos temp temp_pos) Delta))
                   (expf (mult (inv_pos temp temp_pos) (opp Delta))))
             (id_sym (id_trans (mult_comm (expf (mult (inv_pos temp temp_pos) Delta))
                                          (expf (mult (inv_pos temp temp_pos) (opp Delta))))
                               (AttnDoeblin.bs_lo_hi_eq temp temp_pos Delta expf
                                                        expf_zero expf_plus)))
             (le_refl one)).
  - exact (le_mult_compat_r (expf (mult (inv_pos temp temp_pos) Delta))
             (expf (mult (inv_pos temp temp_pos) (opp Delta)))
             (expf (mult (inv_pos temp temp_pos) Delta))
             (lt_le_iff _ _ (inl (expf_pos (mult (inv_pos temp temp_pos) Delta))))
             (lt_le_iff _ _ (inl (AttnDoeblin.bs_lo_lt_hi temp temp_pos Delta Delta_pos
                                    expf expf_mono_lt)))).
Qed.

End P7DScale.

(* ################ 段六：expf 字段产物——因子-倒数恒等式 ################ *)

Section P7DExpfShape.
Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.

(* 同温指数的乘积分裂：e^{k·a}·e^{k·b} = e^{k·(a+b)} *)
Theorem p7d_expf_plus_mult_l :
  forall (k a b : R) (expf : R -> R)
         (expf_plus : forall a b : R, Id (expf (plus a b)) (mult (expf a) (expf b))),
  Id (mult (expf (mult k a)) (expf (mult k b))) (expf (mult k (plus a b))).
Proof.
  intros k a b expf expf_plus.
  apply (id_trans (id_sym (expf_plus (mult k a) (mult k b)))).
  exact (id_cong expf (id_sym (distrib k a b))).
Qed.

(* 因子-倒数恒等式：e^{z/T}·(e^{Δ/T})⁻¹ = e^{(z−Δ)/T}
   ——expf 同态性把核值的比值结构还原为 logit 差。 *)
Theorem p7d_factor_over_hi :
  forall (temp : R) (temp_pos : lt zero temp) (Delta : R)
         (a b : R) (expf : R -> R)
         (expf_pos : forall x : R, lt zero (expf x))
         (expf_zero : Id (expf zero) one)
         (expf_plus : forall a b : R, Id (expf (plus a b)) (mult (expf a) (expf b))),
  Id (mult (expf (mult (inv_pos temp temp_pos) a))
           (inv_pos (expf (mult (inv_pos temp temp_pos) Delta))
                    (AttnDoeblin.bs_hi_pos temp temp_pos Delta expf expf_pos)))
     (expf (mult (inv_pos temp temp_pos) (plus a (opp Delta)))).
Proof.
  intros temp temp_pos Delta a b expf expf_pos expf_zero expf_plus.
  apply (id_trans (id_cong2 mult
            (id_refl : Id (expf (mult (inv_pos temp temp_pos) a))
                          (expf (mult (inv_pos temp temp_pos) a)))
            (AttnDoeblin.bs_inv_hi_lo temp temp_pos Delta expf
                                     expf_pos expf_zero expf_plus))).
  exact (p7d_expf_plus_mult_l (inv_pos temp temp_pos) a (opp Delta) expf expf_plus).
Qed.

End P7DExpfShape.

(* ################ 段七：z 界产物——核值独立上带定理 ################
   基座仅把下带 lo ≤ K ≤ … 内联在 bs_minorization 证明里；
   本段导出独立的上带 K(s,s') ≤ hi/(nR·lo)（Zrow 下界使用）。 *)

Section P7DKernelBand.
Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {SS : StateSpace RI}.
Context {SO : SumOver RI SS}.

Variable enum : list S.
Variable enum_nonempty : Not (Id enum nil).
Variable temp : R.
Variable temp_pos : lt zero temp.
Variable Delta : R.
Variable z : S -> S -> R.
Variable z_lb : forall s s' : S, le (opp Delta) (z s s').
Variable z_ub : forall s s' : S, le (z s s') Delta.
Variable expf : R -> R.
Variable expf_pos : forall x : R, lt zero (expf x).
Variable expf_mono_le : forall a b : R, le a b -> le (expf a) (expf b).
Variable sum_eq_list : forall g : S -> R,
  Id (sum_over_S g) (AttnDoeblin.bs_list_sum g enum).

Let invT := inv_pos temp temp_pos.
Let nR := AttnDoeblin.nat_to_R (length enum).
Let lo := expf (mult invT (opp Delta)).
Let hi := expf (mult invT Delta).

Lemma p7d_nR_pos : lt zero nR.
Proof. exact (AttnDoeblin.bs_nR_pos enum enum_nonempty sum_eq_list). Qed.

Lemma p7d_lo_pos : lt zero lo.
Proof. exact (expf_pos (mult invT (opp Delta))). Qed.

Lemma p7d_hi_pos : lt zero hi.
Proof. exact (expf_pos (mult invT Delta)). Qed.

Theorem p7d_kernel_le_hi_over_nRlo : forall (s s' : S) (HnRlo : lt zero (mult nR lo)),
  le (AttnDoeblin.bs_kernel enum enum_nonempty temp temp_pos Delta
        z z_lb expf expf_pos expf_mono_le sum_eq_list s s')
     (mult hi (inv_pos (mult nR lo) HnRlo)).
Proof.
  intros s s' HnRlo.
  assert (Hinvle : le (inv_pos (AttnDoeblin.Zrow temp temp_pos z expf s)
                        (AttnDoeblin.bs_Zrow_pos enum enum_nonempty temp temp_pos
                           Delta z z_lb expf expf_pos expf_mono_le sum_eq_list s))
                      (inv_pos (mult nR lo) HnRlo)).
  { exact (inv_pos_le_compat (mult nR lo) (AttnDoeblin.Zrow temp temp_pos z expf s)
             HnRlo
             (AttnDoeblin.bs_Zrow_pos enum enum_nonempty temp temp_pos
                Delta z z_lb expf expf_pos expf_mono_le sum_eq_list s)
             (AttnDoeblin.bs_Zrow_ge enum temp temp_pos Delta z z_lb
                expf expf_mono_le sum_eq_list s)). }
  apply (le_trans _ (mult hi
           (inv_pos (AttnDoeblin.Zrow temp temp_pos z expf s)
              (AttnDoeblin.bs_Zrow_pos enum enum_nonempty temp temp_pos
                 Delta z z_lb expf expf_pos expf_mono_le sum_eq_list s)))).
  - apply (le_id_l _
             (mult (expf (mult invT (z s s')))
                   (inv_pos (AttnDoeblin.Zrow temp temp_pos z expf s)
                      (AttnDoeblin.bs_Zrow_pos enum enum_nonempty temp temp_pos
                         Delta z z_lb expf expf_pos expf_mono_le sum_eq_list s)))
             _).
    + exact id_refl.
    + exact (le_mult_compat_weak
               (expf (mult invT (z s s'))) hi
               (inv_pos (AttnDoeblin.Zrow temp temp_pos z expf s)
                  (AttnDoeblin.bs_Zrow_pos enum enum_nonempty temp temp_pos
                     Delta z z_lb expf expf_pos expf_mono_le sum_eq_list s))
               (lt_le_iff _ _ (inl (inv_pos_pos (AttnDoeblin.Zrow temp temp_pos z expf s)
                  (AttnDoeblin.bs_Zrow_pos enum enum_nonempty temp temp_pos
                     Delta z z_lb expf expf_pos expf_mono_le sum_eq_list s))))
               (AttnDoeblin.bs_factor_le_hi temp temp_pos Delta z z_ub
                  expf expf_mono_le s s')).
  - exact (le_mult_compat_r hi
               (inv_pos (AttnDoeblin.Zrow temp temp_pos z expf s)
                  (AttnDoeblin.bs_Zrow_pos enum enum_nonempty temp temp_pos
                     Delta z z_lb expf expf_pos expf_mono_le sum_eq_list s))
               (inv_pos (mult nR lo) HnRlo)
               (lt_le_iff _ _ (inl p7d_hi_pos)) Hinvle).
Qed.

(* 实例化形：nR·lo > 0 由 mult_positive 闭式供给 *)
Theorem p7d_kernel_le_hi_over_nRlo_pos : forall s s' : S,
  le (AttnDoeblin.bs_kernel enum enum_nonempty temp temp_pos Delta
        z z_lb expf expf_pos expf_mono_le sum_eq_list s s')
     (mult hi (inv_pos (mult nR lo) (mult_positive nR lo p7d_nR_pos p7d_lo_pos))).
Proof.
  intros s s'.
  exact (p7d_kernel_le_hi_over_nRlo s s' (mult_positive nR lo p7d_nR_pos p7d_lo_pos)).
Qed.

End P7DKernelBand.

(* ################ Print Assumptions（G4 口径） ################ *)
Print Assumptions p7d_lsum_ext.
Print Assumptions p7d_lsum_add.
Print Assumptions p7d_lsum_fubini_gen.
Print Assumptions p7d_lsum_zero.
Print Assumptions p7d_swap_of_sum_eq_list.
Print Assumptions p7d_tv_contraction_no_swap.
Print Assumptions p7d_tv_iter_no_swap.
Print Assumptions p7d_enum_nonempty_gives_nR_pos.
Print Assumptions p7d_nR_pos_gives_enum_nonempty.
Print Assumptions p7d_hi_gt_one.
Print Assumptions p7d_one_le_hi_sq.
Print Assumptions p7d_expf_plus_mult_l.
Print Assumptions p7d_factor_over_hi.
Print Assumptions p7d_kernel_le_hi_over_nRlo.
Print Assumptions p7d_kernel_le_hi_over_nRlo_pos.

(* ################ 附：B 类 11 条逐条判定表 ################
   字段（AttnDoeblin.v:444–476，vorebuild 版行号）  | 深层判定 | 本件施工
   ------------------------------------------------+----------+---------
   enum(:444)            数据位：list 值由实例供给   | 设计面   | —（其组合学含于段一/段二）
   enum_nonempty(:445)   证书位                     | 可深挖   | 段四双定理（⟷ nR>0 等价）
   temp(:446)            数据位                     | 设计面   | —
   temp_pos(:447)        证书位                     | 可深挖   | 段五（invT 正性产物 hi>1、1≤hi²）
   Delta(:448)           数据位                     | 设计面   | —
   Delta_pos(:449)       证书位                     | 可深挖   | 段五（同上，Δ>0 进路）
   z(:450)               数据位                     | 设计面   | —
   z_lb(:451)            证书位                     | 可深挖   | 段七（下带 + 上带新证）
   z_ub(:452)            证书位                     | 可深挖   | 段七（上带主使用）
   expf(:464)            数据位（A 注：可满足性已实例化消解）| 可深挖  | 段六（因子-倒数恒等式）
   bs_swap(:472)         结构证书位                 | 可消融   | 段二+段三（sum_eq_list 槽导出，19→18）
   设计面合计 4：enum/temp/Delta/z（纯数据，须实例供给，非欠账）；
   可深挖/可消融 7：enum_nonempty、temp_pos、Delta_pos、z_lb、z_ub、expf、bs_swap。 *)
