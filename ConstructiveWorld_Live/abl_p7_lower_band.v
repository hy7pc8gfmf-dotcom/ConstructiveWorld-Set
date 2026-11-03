(* ===================================================================== *)
(*  abl_p7_lower_band.v —— P7 有界 softmax 核的核值下带定理（独立导出件）   *)
(*  使命: 有界 logits softmax 核逐点不低于 lo/(N·hi)，其中 lo := e^{−Δ/T}、  *)
(*        hi := e^{Δ/T}、N 为状态枚举规模。该下界链条原先埋存于 AttnDoeblin  *)
(*        均匀参考 Doeblin 下界主件的证明体内（行和上界 × 倒数反单调 ×       *)
(*        因子下界 三段装配），本件将其以具名语句独立重组导出：一般形保留    *)
(*        显式正性前提（不特化 lo·hi=1），实例化形由正性闭式自动供给。       *)
(*        与在册上带件 p7d_kernel_le_hi_over_nRlo 合成核值显式双带。         *)
(*  依赖: Stdlib List；S01_BaseRing（接口面：le/lt 传递与替换、inv_pos 保序  *)
(*        反单调与正性、mult_positive、le_mult_compat_r）；AttnDoeblin       *)
(*        （基座：bs_Zrow_le 行和上界／bs_Zrow_pos 行和正性／               *)
(*        bs_factor_ge_lo 因子下界／bs_kernel 核／Zrow 行和／nat_to_R）；    *)
(*        P7BoundedSoftmaxDeep（与在册上带件同构；其正性证书 p7d_nR_pos／    *)
(*        p7d_lo_pos／p7d_hi_pos 在本件复用）。                              *)
(*  对标: AttnDoeblin 主件体内下界组装链条的转写级导出；P7BoundedSoftmaxDeep *)
(*        段七上带定理的逐肢对应。                                           *)
(*  构造性: 纯构造性、零承认件；链式装配全 Qed 闭合；语句面零经典选择、      *)
(*        零弃证；文尾取证两件全 Closed（可提取面与在册上带件同标准）。      *)
(*  编译配方: rocq c -native-compiler no -Q <现役统一世界树> ""（独占沙箱）。 *)
(* ===================================================================== *)

From Stdlib Require Import List.
Require Import S01_BaseRing.
Require Import AttnDoeblin.
Require Import P7BoundedSoftmaxDeep.

(* ################ 核值下带：段七上带的对应独立件 ################ *)

Section P7DKernelLowerBand.
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

(* 正性三证书：nR 正性复用对应在册上带件同款证书；lo/hi 正性为指数正性直引 *)
Lemma p7d_lb_nR_pos : lt zero nR.
Proof. exact (p7d_nR_pos enum enum_nonempty sum_eq_list). Qed.

Lemma p7d_lb_lo_pos : lt zero lo.
Proof. exact (p7d_lo_pos temp temp_pos Delta expf expf_pos). Qed.

Lemma p7d_lb_hi_pos : lt zero hi.
Proof. exact (p7d_hi_pos temp temp_pos Delta expf expf_pos). Qed.

(* ===== 核值下带·一般形 =====
   链条：行和 ≤ N·hi（bs_Zrow_le） ⟹ 倒数反单调（inv_pos_le_compat）
   ⟹ lo 乘入（le_mult_compat_r）；另一肢 行和倒数作因子时核 ≥ lo·行和倒数
   （bs_factor_ge_lo 逐点下界）；两肢 le_trans 闭合。 *)
Theorem p7d_kernel_ge_lo_over_nRhi : forall (s s' : S) (HnRhi : lt zero (mult nR hi)),
  le (mult lo (inv_pos (mult nR hi) HnRhi))
     (AttnDoeblin.bs_kernel enum enum_nonempty temp temp_pos Delta
        z z_lb expf expf_pos expf_mono_le sum_eq_list s s').
Proof.
  intros s s' HnRhi.
  apply (le_trans _ (mult lo
           (inv_pos (AttnDoeblin.Zrow temp temp_pos z expf s)
              (AttnDoeblin.bs_Zrow_pos enum enum_nonempty temp temp_pos
                 Delta z z_lb expf expf_pos expf_mono_le sum_eq_list s)))).
  - apply (le_mult_compat_r lo (inv_pos (mult nR hi) HnRhi)
             (inv_pos (AttnDoeblin.Zrow temp temp_pos z expf s)
                (AttnDoeblin.bs_Zrow_pos enum enum_nonempty temp temp_pos
                   Delta z z_lb expf expf_pos expf_mono_le sum_eq_list s))
             (lt_le_iff _ _ (inl p7d_lb_lo_pos))).
    exact (inv_pos_le_compat (AttnDoeblin.Zrow temp temp_pos z expf s) (mult nR hi)
             (AttnDoeblin.bs_Zrow_pos enum enum_nonempty temp temp_pos
                Delta z z_lb expf expf_pos expf_mono_le sum_eq_list s)
             HnRhi
             (AttnDoeblin.bs_Zrow_le enum temp temp_pos Delta z z_ub
                expf expf_mono_le sum_eq_list s)).
  - exact (le_id_l _ _ _
             (mult_comm lo
                (inv_pos (AttnDoeblin.Zrow temp temp_pos z expf s)
                   (AttnDoeblin.bs_Zrow_pos enum enum_nonempty temp temp_pos
                      Delta z z_lb expf expf_pos expf_mono_le sum_eq_list s)))
             (le_id_r _ _ _
               (id_sym (mult_comm (expf (mult invT (z s s')))
                                  (inv_pos (AttnDoeblin.Zrow temp temp_pos z expf s)
                                     (AttnDoeblin.bs_Zrow_pos enum enum_nonempty temp temp_pos
                                        Delta z z_lb expf expf_pos expf_mono_le
                                        sum_eq_list s))))
               (le_mult_compat_r
                  (inv_pos (AttnDoeblin.Zrow temp temp_pos z expf s)
                     (AttnDoeblin.bs_Zrow_pos enum enum_nonempty temp temp_pos
                        Delta z z_lb expf expf_pos expf_mono_le sum_eq_list s))
                  lo (expf (mult invT (z s s')))
                  (lt_le_iff _ _ (inl (inv_pos_pos
                     (AttnDoeblin.Zrow temp temp_pos z expf s)
                     (AttnDoeblin.bs_Zrow_pos enum enum_nonempty temp temp_pos
                        Delta z z_lb expf expf_pos expf_mono_le sum_eq_list s))))
                  (AttnDoeblin.bs_factor_ge_lo temp temp_pos Delta z z_lb
                     expf expf_mono_le s s')))).
Qed.

(* 实例化形：N·hi > 0 由 mult_positive 闭式供给 *)
Theorem p7d_kernel_ge_lo_over_nRhi_pos : forall s s' : S,
  le (mult lo (inv_pos (mult nR hi)
         (mult_positive nR hi p7d_lb_nR_pos p7d_lb_hi_pos)))
     (AttnDoeblin.bs_kernel enum enum_nonempty temp temp_pos Delta
        z z_lb expf expf_pos expf_mono_le sum_eq_list s s').
Proof.
  intros s s'.
  exact (p7d_kernel_ge_lo_over_nRhi s s'
           (mult_positive nR hi p7d_lb_nR_pos p7d_lb_hi_pos)).
Qed.

End P7DKernelLowerBand.

(* ################ 取证（在册件同口径） ################ *)
Print Assumptions p7d_kernel_ge_lo_over_nRhi.
Print Assumptions p7d_kernel_ge_lo_over_nRhi_pos.
