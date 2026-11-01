(* ==========================================================================)
   UpReqEntropyDeficitTemp.v — 温度化 KL 分解与熵亏损
   使命: real_sum_neglog_boltzmann（负对数 Boltzmann 和恒等）、real_KL_temp、real_KL_temp_decomp（KL 分解为能量项与温度熵项）与 real_entropy_deficit_kl_temp（能量期望 == 自由能 − 温度·熵）。
   依赖: CW_ConstructiveWorld_219、UpReqTempDefs
   对标: 温度化相对熵分解（自由能 = 能量 − T·熵；熵亏损恒等式）。
   构造性: 全件 Qed 闭合、零承认词面；证体不引入额外公理前提。
   编译配方: Rocq 9.1 直调 coqc -native-compiler no -q -Q . ""（vo 树同世界重编），COQLIB/ROCQLIB 全字面环境前缀。
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
Require Import UpReqTempDefs.

(* ---------------------------------------------------------- *)

(*   去实例化副本，同配方：log_mult + log_wd + inv_pos_correct）        *)
(* ---------------------------------------------------------- *)
Lemma real_log_inv_pos_gen :
  forall (x : Real) (Hx : real_lt real_zero x),
    real_eq (real_log (real_inv_pos x Hx) (real_inv_pos_pos x Hx))
            (real_opp (real_log x Hx)).
Proof.
  intros x Hx.
  set (X := real_log (real_inv_pos x Hx) (real_inv_pos_pos x Hx)).
  set (L := real_log x Hx).
  assert (Hsum : real_eq (real_plus X L) real_zero).
  { apply (real_eq_trans (real_plus X L)
             (real_log (real_mult (real_inv_pos x Hx) x)
                       (real_mult_positive (real_inv_pos x Hx) x
                          (real_inv_pos_pos x Hx) Hx))
             real_zero).
    - apply real_eq_sym.
      exact (real_log_mult (real_inv_pos x Hx) x
              (real_inv_pos_pos x Hx) Hx).
    - apply (real_eq_trans
               (real_log (real_mult (real_inv_pos x Hx) x)
                         (real_mult_positive (real_inv_pos x Hx) x
                            (real_inv_pos_pos x Hx) Hx))
               (real_log real_one real_lt_zero_one)
               real_zero).
      + apply (real_log_wd
                 (real_mult (real_inv_pos x Hx) x)
                 real_one
                 (real_mult_positive (real_inv_pos x Hx) x
                    (real_inv_pos_pos x Hx) Hx)
                 real_lt_zero_one).
        apply (real_eq_trans
                 (real_mult (real_inv_pos x Hx) x)
                 (real_mult x (real_inv_pos x Hx))
                 real_one).
        -- exact (real_mult_comm (real_inv_pos x Hx) x).
        -- exact (real_inv_pos_correct x Hx).
      + exact (real_log_one real_lt_zero_one). }
  apply (real_eq_trans X (real_plus X real_zero) (real_opp L)).
  - apply real_eq_sym. exact (real_plus_zero X).
  - apply (real_eq_trans
             (real_plus X real_zero)
             (real_plus X (real_plus L (real_opp L)))
             (real_opp L)).
    + apply (RealSetoid.real_eq_plus_compat_adapt X X real_zero
               (real_plus L (real_opp L)) (real_eq_refl X)).
      apply real_eq_sym. exact (real_plus_opp L).
    + apply (real_eq_trans
               (real_plus X (real_plus L (real_opp L)))
               (real_plus (real_plus X L) (real_opp L))
               (real_opp L)).
      * exact (real_plus_assoc X L (real_opp L)).
      * apply (real_eq_trans
                 (real_plus (real_plus X L) (real_opp L))
                 (real_plus real_zero (real_opp L))
                 (real_opp L)).
        -- apply (RealSetoid.real_eq_plus_compat_adapt
                    (real_plus X L) real_zero (real_opp L) (real_opp L)
                    Hsum (real_eq_refl (real_opp L))).
        -- apply (real_eq_trans
                    (real_plus real_zero (real_opp L))
                    (real_plus (real_opp L) real_zero)
                    (real_opp L)).
           ++ exact (real_plus_comm real_zero (real_opp L)).
           ++ exact (real_plus_zero (real_opp L)).
Qed.

(* ---------------------------------------------------------- *)


(*   件 0a + opp_plus/双否定/交换（T6 卡坑 2：opp 肢显式走 trans）。    *)
(* ---------------------------------------------------------- *)
Lemma real_kl_term_point_bridge :
  forall (p q : Real) (Hp : real_lt real_zero p) (Hq : real_lt real_zero q),
    real_eq (real_mult p (real_plus (real_log p Hp) (real_opp (real_log q Hq))))
            (real_kl_term p q Hp Hq).
Proof.
  intros p q Hp Hq.
  unfold real_kl_term.
  assert (Hlogsum :
    real_eq (real_log (real_mult q (real_inv_pos p Hp))
                       (real_mult_positive q (real_inv_pos p Hp) Hq (real_inv_pos_pos p Hp)))
            (real_plus (real_log q Hq)
                       (real_log (real_inv_pos p Hp) (real_inv_pos_pos p Hp))))
    by exact (real_log_mult q (real_inv_pos p Hp) Hq (real_inv_pos_pos p Hp)).
  apply (RealSetoid.real_eq_mult_compat_adapt p p
           (real_plus (real_log p Hp) (real_opp (real_log q Hq)))
           (real_opp (real_log (real_mult q (real_inv_pos p Hp))
                               (real_mult_positive q (real_inv_pos p Hp)
                                  Hq (real_inv_pos_pos p Hp))))
           (real_eq_refl p)).
  apply (real_eq_trans
           (real_plus (real_log p Hp) (real_opp (real_log q Hq)))
           (real_opp (real_plus (real_log q Hq) (real_opp (real_log p Hp))))
           (real_opp (real_log (real_mult q (real_inv_pos p Hp))
                               (real_mult_positive q (real_inv_pos p Hp)
                                  Hq (real_inv_pos_pos p Hp))))).
  - 
    apply real_eq_sym.
    apply (real_eq_trans
             (real_opp (real_plus (real_log q Hq) (real_opp (real_log p Hp))))
             (real_plus (real_opp (real_log q Hq)) (real_opp (real_opp (real_log p Hp))))
             (real_plus (real_log p Hp) (real_opp (real_log q Hq)))).
    + exact (real_opp_plus (real_log q Hq) (real_opp (real_log p Hp))).
    + apply (real_eq_trans
               (real_plus (real_opp (real_log q Hq)) (real_opp (real_opp (real_log p Hp))))
               (real_plus (real_opp (real_log q Hq)) (real_log p Hp))
               (real_plus (real_log p Hp) (real_opp (real_log q Hq)))).
      * apply (RealSetoid.real_eq_plus_compat_adapt
                 (real_opp (real_log q Hq)) (real_opp (real_log q Hq))
                 (real_opp (real_opp (real_log p Hp))) (real_log p Hp)
                 (real_eq_refl (real_opp (real_log q Hq)))
                 (real_opp_opp (real_log p Hp))).
      * exact (real_plus_comm (real_opp (real_log q Hq)) (real_log p Hp)).
  - 
    apply (RealSetoid.real_eq_opp_compat
             (real_plus (real_log q Hq) (real_opp (real_log p Hp)))
             (real_log (real_mult q (real_inv_pos p Hp))
                       (real_mult_positive q (real_inv_pos p Hp) Hq (real_inv_pos_pos p Hp)))
             (real_eq_trans
                (real_plus (real_log q Hq) (real_opp (real_log p Hp)))
                (real_plus (real_log q Hq)
                           (real_log (real_inv_pos p Hp) (real_inv_pos_pos p Hp)))
                (real_log (real_mult q (real_inv_pos p Hp))
                          (real_mult_positive q (real_inv_pos p Hp) Hq (real_inv_pos_pos p Hp)))
                (RealSetoid.real_eq_plus_compat_adapt
                   (real_log q Hq) (real_log q Hq)
                   (real_opp (real_log p Hp))
                   (real_log (real_inv_pos p Hp) (real_inv_pos_pos p Hp))
                   (real_eq_refl (real_log q Hq))
                   (real_eq_sym _ _ (real_log_inv_pos_gen p Hp)))
                (real_eq_sym _ _ Hlogsum))).
Qed.

(* ============================================================ *)
(* Section RealEntropyDeficitTemp：求和面/温度/能量参数照               *)
(*   UpReqTempDefs Section 同名同序（供 T6 件全 arity 显式应用）。          *)
(* ============================================================ *)
Section RealEntropyDeficitTemp.

Variable S : Type.
Variable real_sum_over_S : (S -> Real) -> Real.
Variable real_sum_pos_preserved :
  forall (f : S -> Real),
    (forall s : S, real_lt real_zero (f s)) -> real_lt real_zero (real_sum_over_S f).
Variable real_sum_over_S_ext : forall (f g : S -> Real),
  (forall s : S, real_eq (f s) (g s)) -> real_eq (real_sum_over_S f) (real_sum_over_S g).
Variable real_sum_over_S_linear : forall (a : Real) (f : S -> Real),
  real_eq (real_sum_over_S (fun s : S => real_mult a (f s)))
          (real_mult a (real_sum_over_S f)).
Variable real_sum_over_S_add : forall (f g : S -> Real),
  real_eq (real_sum_over_S (fun s : S => real_plus (f s) (g s)))
          (real_plus (real_sum_over_S f) (real_sum_over_S g)).
Variable T : Real.
Variable T_pos : real_lt real_zero T.
Variable energy : S -> Real.

(* ---------------------------------------------------------- *)
(* 件 1：Σ(−f) ≡ −(Σ f)（opp_one 线性提取；对位 req 层 fsum_opp）      *)
(* ---------------------------------------------------------- *)
Lemma real_sum_over_S_opp :
  forall f : S -> Real,
    real_eq (real_sum_over_S (fun s : S => real_opp (f s)))
            (real_opp (real_sum_over_S f)).
Proof.
  intro f.
  apply (real_eq_trans
           (real_sum_over_S (fun s : S => real_opp (f s)))
           (real_mult (real_opp real_one) (real_sum_over_S f))
           (real_opp (real_sum_over_S f))).
  - apply (real_eq_trans
             (real_sum_over_S (fun s : S => real_opp (f s)))
             (real_sum_over_S (fun s : S => real_mult (real_opp real_one) (f s)))
             (real_mult (real_opp real_one) (real_sum_over_S f))).
    + apply real_sum_over_S_ext.
      intro s.
      apply real_eq_sym.
      apply (real_eq_trans
               (real_mult (real_opp real_one) (f s))
               (real_opp (real_mult real_one (f s)))
               (real_opp (f s))).
      * exact (real_eq_sym _ _ (real_opp_mult_r real_one (f s))).
      * apply (RealSetoid.real_eq_opp_compat (real_mult real_one (f s)) (f s)).
        apply (real_eq_trans
                 (real_mult real_one (f s))
                 (real_mult (f s) real_one)
                 (f s)).
        -- exact (real_mult_comm real_one (f s)).
        -- exact (real_mult_one (f s)).
    + apply real_sum_over_S_linear.
  - apply (real_eq_trans
             (real_mult (real_opp real_one) (real_sum_over_S f))
             (real_opp (real_mult real_one (real_sum_over_S f)))
             (real_opp (real_sum_over_S f))).
    + exact (real_eq_sym _ _ (real_opp_mult_r real_one (real_sum_over_S f))).
    + apply (RealSetoid.real_eq_opp_compat
               (real_mult real_one (real_sum_over_S f)) (real_sum_over_S f)).
      apply (real_eq_trans
               (real_mult real_one (real_sum_over_S f))
               (real_mult (real_sum_over_S f) real_one)
               (real_sum_over_S f)).
      -- exact (real_mult_comm real_one (real_sum_over_S f)).
      -- exact (real_mult_one (real_sum_over_S f)).
Qed.

(* ---------------------------------------------------------- *)

(*   req 先例 req_entropy_neg_sum 同构）                               *)
(* ---------------------------------------------------------- *)
Lemma real_entropy_neg_sum :
  forall (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s)),
    real_eq (real_sum_over_S (fun s : S => real_mult (p s) (real_log (p s) (Hp s))))
            (real_opp (real_entropy_dist S real_sum_over_S p Hp)).
Proof.
  intros p Hp.
  apply (real_eq_trans
           (real_sum_over_S (fun s : S => real_mult (p s) (real_log (p s) (Hp s))))
           (real_sum_over_S (fun s : S =>
              real_opp (real_mult (p s) (real_opp (real_log (p s) (Hp s))))))
           (real_opp (real_entropy_dist S real_sum_over_S p Hp))).
  - apply real_sum_over_S_ext.
    intro s.
    
    apply real_eq_sym.
    apply (real_eq_trans
             (real_opp (real_mult (p s) (real_opp (real_log (p s) (Hp s)))))
             (real_mult (p s) (real_opp (real_opp (real_log (p s) (Hp s)))))
             (real_mult (p s) (real_log (p s) (Hp s)))).
    + exact (real_opp_mult (p s) (real_opp (real_log (p s) (Hp s)))).
    + apply (RealSetoid.real_eq_mult_compat_adapt
               (p s) (p s)
               (real_opp (real_opp (real_log (p s) (Hp s))))
               (real_log (p s) (Hp s))
               (real_eq_refl (p s))
               (real_opp_opp (real_log (p s) (Hp s)))).
  - apply (real_eq_trans
             (real_sum_over_S (fun s : S =>
                real_opp (real_mult (p s) (real_opp (real_log (p s) (Hp s))))))
             (real_opp (real_sum_over_S (fun s : S =>
                real_mult (p s) (real_opp (real_log (p s) (Hp s))))))
             (real_opp (real_entropy_dist S real_sum_over_S p Hp))).
    + exact (real_sum_over_S_opp
               (fun s : S => real_mult (p s) (real_opp (real_log (p s) (Hp s))))).
    + apply real_eq_refl.
Qed.

(* ---------------------------------------------------------- *)

(*   T6 逐点件显式应用 + distrib/add/β 提取/logZ 提取，T6 explicit          *)
(*   步 2-4 同配方，归一化换 q）                                        *)
(* ---------------------------------------------------------- *)
Theorem real_sum_neglog_boltzmann :
  forall (q : S -> Real) (Hq : forall s : S, real_lt real_zero (q s)),
    real_eq (real_sum_over_S q) real_one ->
    real_eq (real_sum_over_S (fun s : S =>
               real_mult (q s)
                 (real_opp (real_log
                    (real_boltzmann_dist_temp S real_sum_over_S real_sum_pos_preserved T T_pos energy s)
                    (real_boltzmann_dist_temp_pos S real_sum_over_S real_sum_pos_preserved T T_pos energy s)))))
            (real_plus (real_mult (real_inv_pos T T_pos)
                                  (real_sum_over_S (fun s : S => real_mult (q s) (energy s))))
                       (real_log (real_Z_temp S real_sum_over_S T T_pos energy)
                                 (real_Z_temp_pos S real_sum_over_S real_sum_pos_preserved T T_pos energy))).
Proof.
  intros q Hq Hnormq.
  set (bta := real_inv_pos T T_pos).
  set (LZ := real_log (real_Z_temp S real_sum_over_S T T_pos energy)
                      (real_Z_temp_pos S real_sum_over_S real_sum_pos_preserved T T_pos energy)).
  set (B := real_boltzmann_dist_temp S real_sum_over_S real_sum_pos_preserved T T_pos energy).
  set (Bpos := real_boltzmann_dist_temp_pos S real_sum_over_S real_sum_pos_preserved T T_pos energy).
  apply (real_eq_trans
           (real_sum_over_S (fun s : S => real_mult (q s) (real_opp (real_log (B s) (Bpos s)))))
           (real_sum_over_S (fun s : S => real_mult (q s) (real_plus (real_mult bta (energy s)) LZ)))
           (real_plus (real_mult bta (real_sum_over_S (fun s : S => real_mult (q s) (energy s)))) LZ)).
  - 
    apply real_sum_over_S_ext.
    intro s.
    apply (RealSetoid.real_eq_mult_compat_adapt
             (q s) (q s)
             (real_opp (real_log (B s) (Bpos s)))
             (real_plus (real_mult bta (energy s)) LZ)
             (real_eq_refl (q s))
             (real_neg_log_boltzmann_point S real_sum_over_S real_sum_pos_preserved
                T T_pos energy s)).
  - (* 步 2-4：distrib 逐点拆和 → add 分和 → β 提取 + logZ 提取 *)
    apply (real_eq_trans
             (real_sum_over_S (fun s : S => real_mult (q s) (real_plus (real_mult bta (energy s)) LZ)))
             (real_plus (real_sum_over_S (fun s : S => real_mult (q s) (real_mult bta (energy s))))
                        (real_sum_over_S (fun s : S => real_mult (q s) LZ)))
             (real_plus (real_mult bta (real_sum_over_S (fun s : S => real_mult (q s) (energy s)))) LZ)).
    + apply (real_eq_trans
               (real_sum_over_S (fun s : S => real_mult (q s) (real_plus (real_mult bta (energy s)) LZ)))
               (real_sum_over_S (fun s : S =>
                  real_plus (real_mult (q s) (real_mult bta (energy s)))
                            (real_mult (q s) LZ)))
               (real_plus (real_sum_over_S (fun s : S => real_mult (q s) (real_mult bta (energy s))))
                          (real_sum_over_S (fun s : S => real_mult (q s) LZ)))).
      * apply real_sum_over_S_ext.
        intro s. apply real_distrib.
      * apply real_sum_over_S_add.
    + apply (RealSetoid.real_eq_plus_compat_adapt
               (real_sum_over_S (fun s : S => real_mult (q s) (real_mult bta (energy s))))
               (real_mult bta (real_sum_over_S (fun s : S => real_mult (q s) (energy s))))
               (real_sum_over_S (fun s : S => real_mult (q s) LZ))
               LZ).
      * (* β 支：Σ q·(β·e) ≡ β·Σ q·e（逐点重排 → 线性提取） *)
        apply (real_eq_trans
                 (real_sum_over_S (fun s : S => real_mult (q s) (real_mult bta (energy s))))
                 (real_mult bta (real_sum_over_S (fun s : S => real_mult (q s) (energy s))))
                 (real_mult bta (real_sum_over_S (fun s : S => real_mult (q s) (energy s))))).
        -- apply (real_eq_trans
                    (real_sum_over_S (fun s : S => real_mult (q s) (real_mult bta (energy s))))
                    (real_sum_over_S (fun s : S => real_mult bta (real_mult (q s) (energy s))))
                    (real_mult bta (real_sum_over_S (fun s : S => real_mult (q s) (energy s))))).
           ++ apply real_sum_over_S_ext.
              intro s.
              apply (real_eq_trans
                       (real_mult (q s) (real_mult bta (energy s)))
                       (real_mult (real_mult (q s) bta) (energy s))
                       (real_mult bta (real_mult (q s) (energy s)))).
              ** exact (real_mult_assoc (q s) bta (energy s)).
              ** apply (real_eq_trans
                          (real_mult (real_mult (q s) bta) (energy s))
                          (real_mult (real_mult bta (q s)) (energy s))
                          (real_mult bta (real_mult (q s) (energy s)))).
                 --- apply (RealSetoid.real_eq_mult_compat_adapt
                              (real_mult (q s) bta) (real_mult bta (q s))
                              (energy s) (energy s)
                              (real_mult_comm (q s) bta) (real_eq_refl (energy s))).
                 --- apply real_eq_sym.
                     exact (real_mult_assoc bta (q s) (energy s)).
           ++ apply real_sum_over_S_linear.
        -- apply real_eq_refl.
      * (* logZ 支：Σ q·LZ ≡ LZ·Σ q ≡ LZ·1 ≡ LZ *)
        apply (real_eq_trans
                 (real_sum_over_S (fun s : S => real_mult (q s) LZ))
                 (real_mult LZ (real_sum_over_S q))
                 LZ).
        -- apply (real_eq_trans
                    (real_sum_over_S (fun s : S => real_mult (q s) LZ))
                    (real_sum_over_S (fun s : S => real_mult LZ (q s)))
                    (real_mult LZ (real_sum_over_S q))).
           ++ apply real_sum_over_S_ext.
              intro s. apply real_mult_comm.
           ++ apply real_sum_over_S_linear.
        -- apply (real_eq_trans
                    (real_mult LZ (real_sum_over_S q))
                    (real_mult LZ real_one)
                    LZ).
           ++ apply (RealSetoid.real_eq_mult_compat_adapt LZ LZ
                       (real_sum_over_S q) real_one
                       (real_eq_refl LZ) Hnormq).
           ++ exact (real_mult_one LZ).
Qed.

(* ---------------------------------------------------------- *)
(* 定义件：real_KL_temp（温度族分布级 KL；Id relative_entropy          *)

(* ---------------------------------------------------------- *)
Definition real_KL_temp (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s)) : Real :=
  real_sum_over_S (fun s : S =>
    real_mult (p s)
      (real_plus (real_log (p s) (Hp s))
                 (real_opp (real_log
                    (real_boltzmann_dist_temp S real_sum_over_S real_sum_pos_preserved T T_pos energy s)
                    (real_boltzmann_dist_temp_pos S real_sum_over_S real_sum_pos_preserved T T_pos energy s))))).

(* ---------------------------------------------------------- *)
(* 件 4：KL 温度分解（Id relative_entropy_temp_decomp S04 L3568 对位）  *)

(*   add 分和 → 熵负和（件 2）+ 件 3 → 交换重排。                       *)
(* ---------------------------------------------------------- *)
Theorem real_KL_temp_decomp :
  forall (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s)),
    real_eq (real_sum_over_S p) real_one ->
    real_eq (real_KL_temp p Hp)
            (real_plus
               (real_plus (real_mult (real_inv_pos T T_pos)
                                     (real_sum_over_S (fun s : S => real_mult (p s) (energy s))))
                          (real_log (real_Z_temp S real_sum_over_S T T_pos energy)
                                    (real_Z_temp_pos S real_sum_over_S real_sum_pos_preserved T T_pos energy)))
               (real_opp (real_entropy_dist S real_sum_over_S p Hp))).
Proof.
  intros p Hp Hnp.
  set (bta := real_inv_pos T T_pos).
  set (LZ := real_log (real_Z_temp S real_sum_over_S T T_pos energy)
                      (real_Z_temp_pos S real_sum_over_S real_sum_pos_preserved T T_pos energy)).
  set (Sp := real_entropy_dist S real_sum_over_S p Hp).
  set (Ep := real_sum_over_S (fun s : S => real_mult (p s) (energy s))).
  set (B := real_boltzmann_dist_temp S real_sum_over_S real_sum_pos_preserved T T_pos energy).
  set (Bpos := real_boltzmann_dist_temp_pos S real_sum_over_S real_sum_pos_preserved T T_pos energy).
  apply (real_eq_trans
           (real_sum_over_S (fun s : S =>
              real_mult (p s)
                (real_plus (real_log (p s) (Hp s)) (real_opp (real_log (B s) (Bpos s))))))
           (real_plus (real_opp Sp) (real_plus (real_mult bta Ep) LZ))
           (real_plus (real_plus (real_mult bta Ep) LZ) (real_opp Sp))).
  - apply (real_eq_trans
             (real_sum_over_S (fun s : S =>
                real_mult (p s)
                  (real_plus (real_log (p s) (Hp s)) (real_opp (real_log (B s) (Bpos s))))))
             (real_plus (real_sum_over_S (fun s : S => real_mult (p s) (real_log (p s) (Hp s))))
                        (real_sum_over_S (fun s : S =>
                           real_mult (p s) (real_opp (real_log (B s) (Bpos s))))))
             (real_plus (real_opp Sp) (real_plus (real_mult bta Ep) LZ))).
    + apply (real_eq_trans
               (real_sum_over_S (fun s : S =>
                  real_mult (p s)
                    (real_plus (real_log (p s) (Hp s)) (real_opp (real_log (B s) (Bpos s))))))
               (real_sum_over_S (fun s : S =>
                  real_plus (real_mult (p s) (real_log (p s) (Hp s)))
                            (real_mult (p s) (real_opp (real_log (B s) (Bpos s))))))
               (real_plus (real_sum_over_S (fun s : S => real_mult (p s) (real_log (p s) (Hp s))))
                          (real_sum_over_S (fun s : S =>
                             real_mult (p s) (real_opp (real_log (B s) (Bpos s))))))).
      * apply real_sum_over_S_ext.
        intro s. apply real_distrib.
      * apply real_sum_over_S_add.
    + apply (RealSetoid.real_eq_plus_compat_adapt
               (real_sum_over_S (fun s : S => real_mult (p s) (real_log (p s) (Hp s))))
               (real_opp Sp)
               (real_sum_over_S (fun s : S =>
                  real_mult (p s) (real_opp (real_log (B s) (Bpos s)))))
               (real_plus (real_mult bta Ep) LZ)
               (real_entropy_neg_sum p Hp)
               (real_sum_neglog_boltzmann p Hp Hnp)).
  - exact (real_plus_comm (real_opp Sp) (real_plus (real_mult bta Ep) LZ)).
Qed.

(* ---------------------------------------------------------- *)
(* 件 5：real_kl_term 规范形桥（L41696 分布级完成）：             *)
(*   real_KL_temp ≡ Σ_s real_kl_term (p s) (p_T s)。                   *)
(* ---------------------------------------------------------- *)
Theorem real_KL_temp_kl_term_bridge :
  forall (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s)),
    real_eq (real_KL_temp p Hp)
            (real_sum_over_S (fun s : S =>
               real_kl_term (p s)
                 (real_boltzmann_dist_temp S real_sum_over_S real_sum_pos_preserved T T_pos energy s)
                 (Hp s)
                 (real_boltzmann_dist_temp_pos S real_sum_over_S real_sum_pos_preserved T T_pos energy s))).
Proof.
  intros p Hp.
  apply real_sum_over_S_ext.
  intro s.
  exact (real_kl_term_point_bridge (p s)           (real_boltzmann_dist_temp S real_sum_over_S real_sum_pos_preserved T T_pos energy s)           (Hp s)           (real_boltzmann_dist_temp_pos S real_sum_over_S real_sum_pos_preserved T T_pos energy s)).
Qed.

(* ============================================================ *)
(* 主件：real_entropy_deficit_kl_temp（Id S04 L3903 逐参数位对位）          *)
(*   同约束能量 E(p) == E_T ⟹ S[p_T] − S[p] == KL(p‖p_T)。             *)
(*   链：熵显式（T6）+ 同能量替换（β·E_T ↦ β·E(p)）+ 分解（件 4）反向。 *)
(* ============================================================ *)
Theorem real_entropy_deficit_kl_temp :
  forall (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s)),
    real_eq (real_sum_over_S p) real_one ->
    real_eq (real_sum_over_S (fun s : S => real_mult (p s) (energy s)))
            (real_energy_exp_temp S real_sum_over_S real_sum_pos_preserved T T_pos energy) ->
    real_eq (real_minus_r
               (real_entropy_dist S real_sum_over_S
                  (real_boltzmann_dist_temp S real_sum_over_S real_sum_pos_preserved T T_pos energy)
                  (real_boltzmann_dist_temp_pos S real_sum_over_S real_sum_pos_preserved T T_pos energy))
               (real_entropy_dist S real_sum_over_S p Hp))
            (real_KL_temp p Hp).
Proof.
  intros p Hp Hnp Henergy.
  set (bta := real_inv_pos T T_pos).
  set (LZ := real_log (real_Z_temp S real_sum_over_S T T_pos energy)
                      (real_Z_temp_pos S real_sum_over_S real_sum_pos_preserved T T_pos energy)).
  set (Sp := real_entropy_dist S real_sum_over_S p Hp).
  set (Spt := real_entropy_dist S real_sum_over_S
                (real_boltzmann_dist_temp S real_sum_over_S real_sum_pos_preserved T T_pos energy)
                (real_boltzmann_dist_temp_pos S real_sum_over_S real_sum_pos_preserved T T_pos energy)).
  set (Ep := real_sum_over_S (fun s : S => real_mult (p s) (energy s))).
  set (K := real_KL_temp p Hp).
  (* 目标：real_minus_r Spt Sp ≡ plus Spt (opp Sp) == K *)
  unfold real_minus_r.
  apply (real_eq_trans
           (real_plus Spt (real_opp Sp))
           (real_plus (real_plus (real_mult bta Ep) LZ) (real_opp Sp))
           K).
  - 
    apply (real_eq_trans
             (real_plus Spt (real_opp Sp))
             (real_plus (real_plus (real_mult bta
                                      (real_energy_exp_temp S real_sum_over_S real_sum_pos_preserved
                                         T T_pos energy))
                                   LZ)
                        (real_opp Sp))
             (real_plus (real_plus (real_mult bta Ep) LZ) (real_opp Sp))).
    + exact (RealSetoid.real_eq_plus_compat_adapt
               Spt (real_plus (real_mult bta
                                 (real_energy_exp_temp S real_sum_over_S real_sum_pos_preserved
                                    T T_pos energy))
                              LZ)
               (real_opp Sp) (real_opp Sp)
               (real_entropy_temp_explicit S real_sum_over_S real_sum_pos_preserved
                  real_sum_over_S_ext real_sum_over_S_linear real_sum_over_S_add
                  T T_pos energy)
               (real_eq_refl (real_opp Sp))).
    + (* 肢 1b：同能量替换 β·E_T ↦ β·E(p)（Henergy 换载 + 逐字余项） *)
      apply (RealSetoid.real_eq_plus_compat_adapt
               (real_plus (real_mult bta
                             (real_energy_exp_temp S real_sum_over_S real_sum_pos_preserved
                                T T_pos energy))
                          LZ)
               (real_plus (real_mult bta Ep) LZ)
               (real_opp Sp) (real_opp Sp)
               (RealSetoid.real_eq_plus_compat_adapt
                  (real_mult bta
                     (real_energy_exp_temp S real_sum_over_S real_sum_pos_preserved T T_pos energy))
                  (real_mult bta Ep)
                  LZ LZ
                  (RealSetoid.real_eq_mult_compat_adapt
                     bta bta
                     (real_energy_exp_temp S real_sum_over_S real_sum_pos_preserved T T_pos energy)
                     Ep
                     (real_eq_refl bta)
                     (real_eq_sym _ _ Henergy))
                  (real_eq_refl LZ))
               (real_eq_refl (real_opp Sp))).
  - (* 肢 2：分解（件 4）反向完成 *)
    exact (real_eq_sym _ _
             (real_KL_temp_decomp p Hp Hnp)).
Qed.

End RealEntropyDeficitTemp.

Print Assumptions real_KL_temp_kl_term_bridge.
