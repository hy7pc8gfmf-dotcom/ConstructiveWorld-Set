(* ==========================================================================)
   UpAblAbsSumLeB.v — 列表绝对值和的 B 形上界族
   使命: uabS4_abs_diff_triangle_le_B/abs_sum_le_B_pair、uabS4_abs_list_sum_le_B/le_eps（加权列表绝对值和上界）、uabS4_lt_double_margin_le_half_contr/diff_double_kill（双倍余量收缩）。
   依赖: CW_ConstructiveWorld_219、UpRealLeB、S08_RealMainlineDPO；Stdlib List、QArith.Qring。
   对标: 有限和三角不等式 |Σf| ≤ Σ|f| 的 B 谓词形式（实分析）。
   构造性: 全件 Qed 闭合、零承认词面、无经典逻辑；语句面以 Set 层承载（序谓词与等词为 Set 值，零 Prop 泄露）。
   编译配方: Rocq 9.1 直调 coqc -Q . "" -native-compiler no（vo 影子树同世界重编），cpu_guard 包裹限载。
   ========================================================================== *)

From Stdlib Require Import List.
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

(* ============================================================ *)
(* §0 库内接口核对（Check 逐项对照真实签名）                            *)
(* ============================================================ *)

Check real_le_b.              (* Bishop 形 ≤（可达最强形谓词，见 UpRealLeB） *)
Check real_le_closure_b_one.  (* 逐 eps 完成为 B 形（单步闭包） *)
Check real_le_closure_b.      (* 带加权正性证书 D 的 B 形闭合 *)
Check real_abs_triangle_le_B. (* |a+b| ≤_B |a|+|b|（B 形三角不等式） *)
Check real_abs_triangle_le_eps. (* |a+b| ≤ (|a|+|b|)+eps 逐 eps（两点核三角不等式） *)
Check real_lt_zero_one.       (* 0 < 1（W(nil) 正性证书） *)
Check real_lt_plus_r_zero.    (* y < y+eps（见 UpRealLeB） *)
Check real_list_sum.          (* list 折叠（X 全称，见 S08_RealMainlineDPO） *)
Check RealSetoid.real_eq_abs_compat. (* abs 尊重 real_eq *)
Check real_abs_zero_req.      (* |0| ≡ 0 *)
Check real_lt_irrefl.         (* 实数 < 的反自反（归谬的共同落点） *)

(* ============================================================ *)
(* §1 基础引理：正余量右吸收 ＋ 差形两点三角不等式                     *)
(* ============================================================ *)

(* 基础引理：le a b ＋ 0 < c ⟹ le a (b+c)（正余量右吸收）。
   构造：Or 两支分别 lt 传递（b < b+c 经 (b+0) 换形平移）
   ／eq 支运输后同链；统一经 real_lt_le_iff_req 左注入收束。 *)
Lemma uabS4_le_add_r : forall a b c : Real,
  real_le a b -> real_lt real_zero c -> real_le a (real_plus b c).
Proof.
  intros a b c Hab Hc.
  apply (RealSetoid.real_lt_le_iff_req a (real_plus b c)). apply inl.
  destruct Hab as [Hab | Hab].
  - apply (real_lt_trans a b (real_plus b c)).
    + exact Hab.
    + apply (RealSetoid.real_lt_id_l b (real_plus b real_zero) (real_plus b c)).
      * apply real_eq_sym. apply real_plus_zero.
      * apply (real_lt_plus_translate b real_zero c). exact Hc.
  - apply (RealSetoid.real_lt_id_l a b (real_plus b c)).
    + exact Hab.
    + apply (RealSetoid.real_lt_id_l b (real_plus b real_zero) (real_plus b c)).
      * apply real_eq_sym. apply real_plus_zero.
      * apply (real_lt_plus_translate b real_zero c). exact Hc.
Qed.

(* A.1 两点核差形（逐 eps，Or-inl）：|a−c| ≤ (|a−b|+|b−c|)+eps。
   构造：差恒等式 eq 链 (a−b)+(b−c) ≡ a−c（assoc×2＋opp＋zero 五步，
   逐项经 real_eq_plus_compat 运输），abs 尊重 eq 后两点核三角直接应用。 *)
Lemma uabS4_abs_diff_triangle_le_eps : forall a b c e : Real,
  real_lt real_zero e ->
  real_le (real_abs (real_plus a (real_opp c)))
          (real_plus (real_plus (real_abs (real_plus a (real_opp b)))
                                (real_abs (real_plus b (real_opp c)))) e).
Proof.
  intros a b c e He.
  assert (Hdiff : real_eq (real_plus (real_plus a (real_opp b))
                                     (real_plus b (real_opp c)))
                          (real_plus a (real_opp c))).
  { eapply real_eq_trans.
    - apply real_eq_sym. apply real_plus_assoc.
    - apply (RealSetoid.real_eq_plus_compat a
               (real_plus (real_opp b) (real_plus b (real_opp c))) a
               (real_opp c)).
      + apply real_eq_refl.
      + eapply real_eq_trans.
        * apply real_plus_assoc.
        * eapply real_eq_trans.
          -- apply (RealSetoid.real_eq_plus_compat (real_plus (real_opp b) b)
                          (real_opp c) real_zero (real_opp c)).
             ++ apply (real_eq_trans _ _ _ (real_plus_comm (real_opp b) b)).
                apply real_plus_opp.
             ++ apply real_eq_refl.
          -- apply (real_eq_trans _ _ _ (real_plus_comm real_zero (real_opp c))).
             apply real_plus_zero. }
  apply (RealSetoid.real_le_id_l _ _ _
           (RealSetoid.real_eq_abs_compat _ _
              (real_eq_sym (real_plus (real_plus a (real_opp b))
                                      (real_plus b (real_opp c)))
                           (real_plus a (real_opp c)) Hdiff))).
  exact (real_abs_triangle_le_eps (real_plus a (real_opp b))
                                  (real_plus b (real_opp c)) e He).
Qed.

(* A.2 两点核差形（B 形，可达最强形）：|a−c| ≤_B |a−b|+|b−c|。 *)
Theorem uabS4_abs_diff_triangle_le_B : forall a b c : Real,
  real_le_b (real_abs (real_plus a (real_opp c)))
            (real_plus (real_abs (real_plus a (real_opp b)))
                       (real_abs (real_plus b (real_opp c)))).
Proof.
  intros a b c.
  exact (real_le_closure_b_one
    (real_abs (real_plus a (real_opp c)))
    (real_plus (real_abs (real_plus a (real_opp b)))
               (real_abs (real_plus b (real_opp c))))
    (fun e He => uabS4_abs_diff_triangle_le_eps a b c e He)).
Qed.


(* A.3 两点世界（S := bool）B 形实例：两点为 abs_sum_le 问题的最小
   非平凡世界，此处直接应用 real_abs_triangle_le_B。 *)
Theorem uabS4_abs_sum_le_B_pair : forall f : bool -> Real,
  real_le_b (real_abs (real_plus (f true) (f false)))
            (real_plus (real_abs (f true)) (real_abs (f false))).
Proof.
  intros f.
  exact (real_abs_triangle_le_B (f true) (f false)).
Qed.

(* ============================================================ *)
(* §2 list 折叠形：权函数加权归纳 ＋ B 形闭合                          *)
(* ============================================================ *)

(* 权函数：W(nil)=1，W(w::rest)=W(rest)+1（定义性尾权 +1）。
   误差分配：单点引入每步恰一整单位 e，尾段余量由 W(rest)·e 承担，
   合计 (W(rest)+1)·e ≡ W(cons)·e——该分配逐级精确成立。 *)
Fixpoint uabS4_wlen (X : Type) (l : list X) : Real :=
  match l with
  | nil => real_one
  | w :: rest => real_plus (uabS4_wlen X rest) real_one
  end.

(* 权正性证书：0 < W(l)（归纳：1 > 0；W(rest) > 0 平移至 W(rest)+1）。 *)
Lemma uabS4_wlen_pos : forall (X : Type) (l : list X),
  real_lt real_zero (uabS4_wlen X l).
Proof.
  intros X l. induction l as [| w rest IH].
  - exact real_lt_zero_one.
  - apply (real_lt_trans real_zero (uabS4_wlen X rest)
             (real_plus (uabS4_wlen X rest) real_one)).
    + exact IH.
    + apply real_lt_plus_r_zero. exact real_lt_zero_one.
Qed.

(* 归纳步引理（折叠归纳的 cons 一步）：
   两点核三角（单点引入，余量恰一整单位 e）＋尾段余量（w·e 加权承担）
   ⟹ 折叠目标余量 (w+1)·e。
   构造：经 real_le_plus_compat 合成，再以 assoc×3＋distrib/mult_one
   的 eq 链终运输（(w+1)·e ≡ w·e + e，经 comm/distrib 逐步重排）。 *)
Lemma uabS4_cons_glue : forall a s t w e : Real,
  real_lt real_zero e ->
  real_le (real_abs (real_plus a s))
          (real_plus (real_plus (real_abs a) (real_abs s)) e) ->
  real_le (real_abs s) (real_plus t (real_mult w e)) ->
  real_le (real_abs (real_plus a s))
          (real_plus (real_plus (real_abs a) t)
                     (real_mult (real_plus w real_one) e)).
Proof.
  intros a s t w e He Hpair Hih.
  assert (Hmid : real_le (real_plus (real_abs a) (real_abs s))
                         (real_plus (real_abs a) (real_plus t (real_mult w e)))).
  { apply (real_le_plus_compat (real_abs a) (real_abs a)
             (real_abs s) (real_plus t (real_mult w e))).
    - exact (RealSetoid.real_eq_le _ _ (real_eq_refl (real_abs a))).
    - exact Hih. }
  assert (Hstep : real_le (real_plus (real_plus (real_abs a) (real_abs s)) e)
                          (real_plus (real_plus (real_abs a)
                                     (real_plus t (real_mult w e))) e)).
  { apply (real_le_plus_compat _ _ e e).
    - exact Hmid.
    - exact (RealSetoid.real_eq_le _ _ (real_eq_refl e)). }
  assert (Hchain : real_le (real_abs (real_plus a s))
                           (real_plus (real_plus (real_abs a)
                                      (real_plus t (real_mult w e))) e)).
  { apply (real_le_trans _ _ _ Hpair Hstep). }
  apply (RealSetoid.real_le_id_r (real_abs (real_plus a s))
           (real_plus (real_plus (real_abs a) (real_plus t (real_mult w e))) e)
           (real_plus (real_plus (real_abs a) t)
                      (real_mult (real_plus w real_one) e))).
  - eapply real_eq_trans.
    + apply real_eq_sym. apply real_plus_assoc.
    + eapply real_eq_trans.
      * apply (RealSetoid.real_eq_plus_compat (real_abs a)
                   (real_plus (real_plus t (real_mult w e)) e) (real_abs a)
                   (real_plus t (real_plus (real_mult w e) e))).
        -- apply real_eq_refl.
        -- apply real_eq_sym. apply real_plus_assoc.
      * eapply real_eq_trans.
        -- apply real_plus_assoc.
        -- apply (RealSetoid.real_eq_plus_compat (real_plus (real_abs a) t)
                        (real_plus (real_mult w e) e)
                        (real_plus (real_abs a) t)
                        (real_mult (real_plus w real_one) e)).
           ++ apply real_eq_refl.
           ++ apply real_eq_sym.
              apply (real_eq_trans _ _ _
                       (real_mult_comm (real_plus w real_one) e)).
              apply (real_eq_trans _ _ _ (real_distrib e w real_one)).
              apply (RealSetoid.real_eq_plus_compat (real_mult e w)
                          (real_mult e real_one) (real_mult w e) e).
              ** apply real_mult_comm.
              ** apply real_mult_one.
  - exact Hchain.
Qed.

(* B.1 加权归纳主体（逐 eps 形，权函数 W）：|Σ_l f| ≤ Σ_l|f| + W(l)·e。
   情形 l=[]：|0| ≡ 0 ≤ 0 + 1·e（正余量右吸收）；
   归纳步 l 到 w::rest：两点核三角以整单位 e 引入，尾段由归纳假设同权承担，经 uabS4_cons_glue 合成。 *)
Lemma uabS4_abs_list_sum_le_wt : forall (X : Type) (f : X -> Real) (l : list X)
                                        (e : Real),
  real_lt real_zero e ->
  real_le (real_abs (real_list_sum X f l))
          (real_plus (real_list_sum X (fun x => real_abs (f x)) l)
                     (real_mult (uabS4_wlen X l) e)).
Proof.
  intros X f l. induction l as [| w rest IH]; intro e; intro He.
  - apply (uabS4_le_add_r (real_abs (real_list_sum X f nil)) real_zero
             (real_mult (uabS4_wlen X nil) e)).
    + apply (RealSetoid.real_le_id_l (real_abs real_zero) real_zero real_zero).
      * exact real_abs_zero_req.
      * exact (RealSetoid.real_eq_le real_zero real_zero (real_eq_refl real_zero)).
    + apply (RealSetoid.real_lt_id_r real_zero e (real_mult real_one e)).
      * apply real_eq_sym.
        apply (real_eq_trans _ _ _ (real_mult_comm real_one e)).
        apply real_mult_one.
      * exact He.
  - apply (uabS4_cons_glue (f w) (real_list_sum X f rest)
             (real_list_sum X (fun x => real_abs (f x)) rest)
             (uabS4_wlen X rest) e He).
    + exact (real_abs_triangle_le_eps (f w) (real_list_sum X f rest) e He).
    + exact (IH e He).
Qed.

(* B.2 B 形闭合（可达最强形）：|Σ_l f| ≤_B Σ_l|f|。
   real_le_closure_b 以 D := W(l) 显式正性证书闭合加权族。 *)
Theorem uabS4_abs_list_sum_le_B : forall (X : Type) (f : X -> Real) (l : list X),
  real_le_b (real_abs (real_list_sum X f l))
            (real_list_sum X (fun x => real_abs (f x)) l).
Proof.
  intros X f l.
  exact (real_le_closure_b
    (real_abs (real_list_sum X f l))
    (real_list_sum X (fun x => real_abs (f x)) l)
    (uabS4_wlen X l) (uabS4_wlen_pos X l)
    (fun e He => uabS4_abs_list_sum_le_wt X f l e He)).
Qed.


(* B.3 逐 eps 形推论：B 形 ⟹ |Σ_l f| ≤ Σ_l|f| + eps（Or-inl 注入）。
   对照结论：B 形严格强于逐 eps 形——real_le_closure_b_one 即单步反演。 *)
Theorem uabS4_abs_list_sum_le_eps : forall (X : Type) (f : X -> Real) (l : list X)
                                           (e : Real),
  real_lt real_zero e ->
  real_le (real_abs (real_list_sum X f l))
          (real_plus (real_list_sum X (fun x => real_abs (f x)) l) e).
Proof.
  intros X f l e He.
  apply (RealSetoid.real_lt_le_iff_req _ _).
  apply inl.
  exact (uabS4_abs_list_sum_le_B X f l e He).
Qed.

(* ============================================================ *)
(* §3 余量倍率 2 的不可共存引理                                        *)
(* ============================================================ *)

(* C.1 余量倍率 2 不可共存：0 < e ＋ real_lt (Y+2e) X ＋ real_le X (Y+e)
   不可能共存。构造：Or 两支都导出 real_lt (Y+2e) (Y+e)——
   lt 支经传递（Y+2e < X < Y+e）；eq 支经 RHS 运输（X ≡ Y+e）；
   另一侧 e < 2e 经平移给出 Y+e < Y+2e，与上式合取即与 real_lt_irrefl 矛盾。
   边界注记：余量恰为 e（倍率 1）时 eq 支与反向
   strict 可共存（xₙ−yₙ = e+1/n 型逼近例），倍率 2 方不可共存。 *)
Theorem uabS4_lt_double_margin_le_half_contr : forall X Y e : Real,
  real_lt real_zero e ->
  real_lt (real_plus Y (real_plus e e)) X ->
  real_le X (real_plus Y e) ->
  Empty_set.
Proof.
  intros X Y e He Hfar Hle.
  assert (Hboom : real_lt (real_plus Y (real_plus e e))
                          (real_plus Y e) -> Empty_set).
  { intro Hbad.
    assert (Hfwd : real_lt (real_plus Y e) (real_plus Y (real_plus e e))).
    { apply (real_lt_plus_translate Y e (real_plus e e)).
      apply (RealSetoid.real_lt_id_l e (real_plus e real_zero) (real_plus e e)).
      - apply real_eq_sym. apply real_plus_zero.
      - apply (real_lt_plus_translate e real_zero e). exact He. }
    exact (real_lt_irrefl _ (real_lt_trans _ _ _ Hbad Hfwd)). }
  unfold real_le in Hle. destruct Hle as [Hlt | Heq].
  - exact (Hboom (real_lt_trans _ _ _ Hfar Hlt)).
  - apply Hboom.
    exact (RealSetoid.real_lt_id_r (real_plus Y (real_plus e e)) X
             (real_plus Y e) Heq Hfar).
Qed.

(* C.2 倍率 2 矛盾的差形实例（两点核差形与 C.1 的对角组合）：以逐 eps
   差形两点核（uabS4_abs_diff_triangle_le_eps）为 le 来源：real_lt (b + 2e) a ＋ |a−c| ≤_B |a−b|+|b−c| 型
   余量约束下的矛盾实例——B 形在 eps := e 处给出 le a (|a−b|+|b−c|+e)，
   代入 C.1 即得。 *)
Theorem uabS4_diff_double_kill : forall a b c e : Real,
  real_lt real_zero e ->
  real_lt (real_plus (real_plus (real_abs (real_plus a (real_opp b)))
                                  (real_abs (real_plus b (real_opp c))))
                     (real_plus e e))
          (real_abs (real_plus a (real_opp c))) ->
  Empty_set.
Proof.
  intros a b c e He Hfar.
  apply (uabS4_lt_double_margin_le_half_contr           (real_abs (real_plus a (real_opp c)))           (real_plus (real_abs (real_plus a (real_opp b)))                      (real_abs (real_plus b (real_opp c)))) e He Hfar).
  exact (uabS4_abs_diff_triangle_le_eps a b c e He).
Qed.

(* ============================================================ *)
(* 审计注记：Print Assumptions 预期全 Closed（零外部未证假设）         *)
(* ============================================================ *)

Print Assumptions uabS4_le_add_r.
Print Assumptions uabS4_abs_diff_triangle_le_eps.
Print Assumptions uabS4_abs_diff_triangle_le_B.
Print Assumptions uabS4_abs_sum_le_B_pair.
Print Assumptions uabS4_wlen_pos.
Print Assumptions uabS4_cons_glue.
Print Assumptions uabS4_abs_list_sum_le_wt.
Print Assumptions uabS4_abs_list_sum_le_B.
Print Assumptions uabS4_abs_list_sum_le_eps.
Print Assumptions uabS4_lt_double_margin_le_half_contr.
Print Assumptions uabS4_diff_double_kill.
