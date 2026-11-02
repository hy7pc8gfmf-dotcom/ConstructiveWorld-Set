(* Mission.  Set-lineage adaptation.  Dependencies.  S01-S15 trunk.  References.  Main UpSigMigrate.v.  Constructivity.  born-clean.  Build.  rocq c. *)
(* ========================================================================== *)
(*  UpSigMigrate.v -- Boltzmann distribution and free energy over the        *)
(*  setoid signature (req carrier).                                          *)
(*                                                                           *)
(*  Mission: sigm_boltzmann_dist / sigm_free_energy / sigm_softmax_temp      *)
(*  over the req carrier, with normalization and positivity as explicit      *)
(*  premises; main statements req_free_energy_kl_decomp (the free-energy     *)
(*  identity F[p] == F[p_b] + D*KL(p||p_b)) and req_attention_is_gibbs_temp. *)
(*                                                                           *)
(*  Ground: S-carrier wash of the Main-tree module of the same name (the     *)
(*  identity-based original): the equality/order carriers move from Id to    *)
(*  req (= real_eq), every statement is Set-carried with zero Prop atoms at  *)
(*  statement level, and each intermediate equation is a req_trans chain     *)
(*  over the interface compatibility fields (destruct-style elimination is   *)
(*  unavailable on the req carrier by design).                               *)
(*                                                                           *)
(*  Dependencies: S01_BaseRing, S02_CauchyComplete, S03_QExp,                *)
(*  S04_RealExpLogConv, S05_AlignmentGRPO, S06_DiffSamplingGibbs,            *)
(*  S07_RealSetoidExpLog, S08_RealMainlineDPO, S09_EntropyReal,              *)
(*  S10_KVQuantTrig, S11_TP3B5, S12_B5RecycleSF, S13_NLiveAudit,             *)
(*  S14_B5BatchBlock, S15_TailFEPUp; interface module                        *)
(*  RealInterfaceEnhancedMod (parameterless RealInterfaceEnhancedSetoid      *)
(*  with global instance RealEnhancedReal).                                  *)
(*                                                                           *)
(*  Constructivity: every proof closed by Qed, zero admission tokens, no     *)
(*  classical logic; statement face Set-carried.                             *)
(*                                                                           *)
(*  Build: rocq c -native-compiler no -Q . "" UpSigMigrate.v                 *)
(* ========================================================================== *)
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
Import RealInterfaceEnhancedMod.

(* Parameterless interface form (nw10cure re-anchor): the enhanced setoid
   interface is a parameterless class over the global carrier Real with the
   global instance RealEnhancedReal, so the section-level interface instance
   of the original is stripped; the order/equality tokens below are
   re-anchored to the corresponding global operations, the two readings
   convertible (the instance record reduces by projection). *)
Notation R := Real.
Notation req := real_eq.
Notation lt := real_lt.

(* ============================================================ *)
(* Part 1: the setoid signature for the free-energy development.  *)
(*   The summation interface is declared as three req-signed      *)
(*   section premises (the setoid counterpart of SumOver); the     *)
(*   two upstream facts about the Boltzmann law                   *)
(*   (energy_in_log_boltzmann / free_energy_boltzmann) are        *)
(*   likewise declared as req-signed premises.                  *)
(* ============================================================ *)
Section ReqFreeEnergyPilot.
Variable S : Set.

(* ---- The summation interface in req signature (setoid counterpart of SumOver) ---- *)
Variable sumf : (S -> R) -> R.
Hypothesis sum_ext :
  forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g).
Hypothesis sum_add :
  forall f g : S -> R,
    req (sumf (fun s => plus (f s) (g s))) (plus (sumf f) (sumf g)).
Hypothesis sum_linear :
  forall (a : R) (f : S -> R),
    req (sumf (fun s => mult a (f s))) (mult a (sumf f)).

(* ---- Section parameters ---- *)
Variable base_loss : S -> R.
Variable D : R.
Variable D_pos : lt zero D.
Variable Z : R.
Variable Z_pos : lt zero Z.
Hypothesis partition_condition :
  req Z (sumf (fun s => exp_neg (mult (inv_pos D D_pos) (base_loss s)))).

(* ---- 节内定义（setoid 惯例形态） ---- *)
Definition sigm_positive_dist (p : S -> R) : Set := forall s : S, lt zero (p s).
Definition sigm_boltzmann_dist : S -> R :=
  fun s => mult (inv_pos Z Z_pos) (exp_neg (mult (inv_pos D D_pos) (base_loss s))).
(* the log family carries positivity premises, so free_energy is taken over positive distributions only *)
Definition sigm_free_energy (p : S -> R) (Hp : sigm_positive_dist p) : R :=
  plus (sumf (fun s => mult (p s) (base_loss s)))
       (mult D (sumf (fun s => mult (p s) (log (p s) (Hp s))))).
Definition sigm_normalized (p : S -> R) : Set := req (sumf p) one.
Definition rminus (a b : R) : R := plus a (opp b).

(* ---- Boltzmann 分布正性（setoid log 前提所需；接口字段直接组装） ---- *)
Lemma req_boltzmann_positive : sigm_positive_dist sigm_boltzmann_dist.
Proof.
  intro s.
  apply mult_positive.
  - apply inv_pos_pos.
  - apply exp_neg_pos.
Qed.

(* ---- The two upstream Boltzmann facts, carried as req-signed premises ---- *)
Hypothesis energy_in_log_boltzmann_bridge :
  forall s : S,
    req (base_loss s)
        (opp (mult D (plus (log (sigm_boltzmann_dist s) (req_boltzmann_positive s))
                           (log Z Z_pos)))).
Hypothesis free_energy_boltzmann_bridge :
  req (sigm_free_energy sigm_boltzmann_dist req_boltzmann_positive)
      (mult (opp D) (log Z Z_pos)).

(* ============================================================ *)
(* A. 代数前奏：req 版 opp 代数（接口字段纯推导，零 destruct，   *)
(*    全 req_trans 链 + compat 桥） *)
(* ============================================================ *)

(* 加零右形式：plus_zero 字段只有左形式，右形式走 comm 桥 *)
Lemma req_plus_zero_r : forall a : R, req (plus zero a) a.
Proof.
  intro a.
  assert (Hc : req (plus zero a) (plus a zero)).
  { exact (plus_comm zero a). }
  assert (Hz : req (plus a zero) a).
  { exact (plus_zero a). }
  exact (req_trans (plus zero a) (plus a zero) a Hc Hz).
Qed.

(* 单位元左形式：mult_one 字段只有右形式 *)
Lemma req_mult_one_l : forall a : R, req (mult one a) a.
Proof.
  intro a.
  assert (Hc : req (mult one a) (mult a one)).
  { exact (mult_comm one a). }
  assert (Ho : req (mult a one) a).
  { exact (mult_one a). }
  exact (req_trans (mult one a) (mult a one) a Hc Ho).
Qed.

(* 左消去：opp 唯一性的引擎（七段传递链） *)
Lemma req_add_cancel_l : forall (u v w : R),
  req (plus u v) (plus w v) -> req u w.
Proof.
  intros u v w H.
  apply (req_trans u (plus u zero) w).
  - apply (req_sym (plus u zero) u). apply plus_zero.
  - apply (req_trans (plus u zero) (plus u (plus v (opp v))) w).
    + apply (req_plus_compat u u zero (plus v (opp v))).
      * apply req_refl.
      * apply (req_sym (plus v (opp v)) zero). apply plus_opp.
    + apply (req_trans (plus u (plus v (opp v))) (plus (plus u v) (opp v)) w).
      * apply plus_assoc.
      * apply (req_trans (plus (plus u v) (opp v)) (plus (plus w v) (opp v)) w).
        -- apply (req_plus_compat (plus u v) (plus w v) (opp v) (opp v) H).
           apply req_refl.
        -- apply (req_trans (plus (plus w v) (opp v)) (plus w (plus v (opp v))) w).
           ++ apply (req_sym (plus w (plus v (opp v))) (plus (plus w v) (opp v))).
              apply plus_assoc.
           ++ apply (req_trans (plus w (plus v (opp v))) (plus w zero) w).
              ** apply (req_plus_compat w w (plus v (opp v)) zero).
                 --- apply req_refl.
                 --- apply plus_opp.
              ** apply plus_zero.
Qed.

(* 双重负号：opp (opp a) == a（两次 plus_opp + 消去） *)
Lemma req_double_neg : forall a : R, req (opp (opp a)) a.
Proof.
  intro a.
  apply (req_add_cancel_l (opp (opp a)) (opp a) a).
  apply (req_trans (plus (opp (opp a)) (opp a)) zero (plus a (opp a))).
  - apply (req_trans (plus (opp (opp a)) (opp a)) (plus (opp a) (opp (opp a))) zero).
    + apply plus_comm.
    + apply plus_opp.
  - apply (req_sym (plus a (opp a)) zero). apply plus_opp.
Qed.

(* 负号分配：opp (a+b) == opp a + opp b *)
Lemma req_opp_plus : forall a b : R, req (opp (plus a b)) (plus (opp a) (opp b)).
Proof.
  intros a b.
  apply (req_add_cancel_l (opp (plus a b)) (plus a b) (plus (opp a) (opp b))).
  apply (req_trans (plus (opp (plus a b)) (plus a b)) zero (plus (plus (opp a) (opp b)) (plus a b))).
  - apply (req_trans (plus (opp (plus a b)) (plus a b)) (plus (plus a b) (opp (plus a b))) zero).
    + apply plus_comm.
    + apply plus_opp.
  - apply (req_sym (plus (plus (opp a) (opp b)) (plus a b)) zero).
    apply (req_trans (plus (plus (opp a) (opp b)) (plus a b))
                     (plus (opp a) (plus (opp b) (plus a b)))
                     zero).
    + apply (req_sym (plus (opp a) (plus (opp b) (plus a b)))
                     (plus (plus (opp a) (opp b)) (plus a b))).
      apply plus_assoc.
    + apply (req_trans (plus (opp a) (plus (opp b) (plus a b)))
                       (plus (opp a) (plus (plus (opp b) a) b))
                       zero).
      * apply (req_plus_compat (opp a) (opp a) (plus (opp b) (plus a b)) (plus (plus (opp b) a) b)).
        -- apply req_refl.
        -- apply plus_assoc.
      * apply (req_trans (plus (opp a) (plus (plus (opp b) a) b))
                         (plus (opp a) (plus (plus a (opp b)) b))
                         zero).
        -- apply (req_plus_compat (opp a) (opp a) (plus (plus (opp b) a) b) (plus (plus a (opp b)) b)).
           ++ apply req_refl.
           ++ apply (req_plus_compat (plus (opp b) a) (plus a (opp b)) b b).
              ** apply plus_comm.
              ** apply req_refl.
        -- apply (req_trans (plus (opp a) (plus (plus a (opp b)) b))
                            (plus (plus (opp a) a) (plus (opp b) b))
                            zero).
           ++ apply (req_trans (plus (opp a) (plus (plus a (opp b)) b))
                               (plus (opp a) (plus a (plus (opp b) b)))
                               (plus (plus (opp a) a) (plus (opp b) b))).
              ** apply (req_plus_compat (opp a) (opp a) (plus (plus a (opp b)) b) (plus a (plus (opp b) b))).
                 --- apply req_refl.
                 --- apply (req_sym (plus a (plus (opp b) b)) (plus (plus a (opp b)) b)). apply plus_assoc.
              ** apply plus_assoc.
           ++ apply (req_trans (plus (plus (opp a) a) (plus (opp b) b)) (plus zero zero) zero).
              ** apply (req_plus_compat (plus (opp a) a) zero (plus (opp b) b) zero).
                 --- apply (req_trans (plus (opp a) a) (plus a (opp a)) zero).
                     +++ apply plus_comm.
                     +++ apply plus_opp.
                 --- apply (req_trans (plus (opp b) b) (plus b (opp b)) zero).
                     +++ apply plus_comm.
                     +++ apply plus_opp.
              ** apply plus_zero.
Qed.

(* mult a (opp b) == opp (mult a b) *)
Lemma req_mult_opp_l : forall a b : R, req (mult a (opp b)) (opp (mult a b)).
Proof.
  intros a b.
  apply (req_add_cancel_l (mult a (opp b)) (mult a b) (opp (mult a b))).
  apply (req_trans (plus (mult a (opp b)) (mult a b)) zero (plus (opp (mult a b)) (mult a b))).
  - apply (req_trans (plus (mult a (opp b)) (mult a b)) (plus (mult a b) (mult a (opp b))) zero).
    + apply plus_comm.
    + apply (req_trans (plus (mult a b) (mult a (opp b))) (mult a (plus b (opp b))) zero).
      * apply (req_sym (mult a (plus b (opp b))) (plus (mult a b) (mult a (opp b)))).
        apply distrib.
      * apply (req_trans (mult a (plus b (opp b))) (mult a zero) zero).
        -- apply (req_mult_compat a a (plus b (opp b)) zero).
           ++ apply req_refl.
           ++ apply plus_opp.
        -- apply mult_zero.
  - apply (req_sym (plus (opp (mult a b)) (mult a b)) zero).
    apply (req_trans (plus (opp (mult a b)) (mult a b)) (plus (mult a b) (opp (mult a b))) zero).
    + apply plus_comm.
    + apply plus_opp.
Qed.

(* mult (opp a) b == opp (mult a b)（经 comm 桥） *)
Lemma req_opp_mult_l : forall a b : R, req (mult (opp a) b) (opp (mult a b)).
Proof.
  intros a b.
  apply (req_trans (mult (opp a) b) (mult b (opp a)) (opp (mult a b))).
  - apply mult_comm.
  - apply (req_trans (mult b (opp a)) (opp (mult b a)) (opp (mult a b))).
    + apply req_mult_opp_l.
    + apply (req_opp_compat (mult b a) (mult a b)). apply mult_comm.
  Qed.

(* ============================================================ *)
(* B. 求和层 req 引理（SumOver req 对接面之上的移植）            *)
(* ============================================================ *)

(* Σ opp f == opp Σ f *)
Lemma req_sum_opp :
  forall f : S -> R, req (sumf (fun s => opp (f s))) (opp (sumf f)).
Proof.
  intro f.
  apply (req_trans (sumf (fun s => opp (f s)))
                   (sumf (fun s => mult (opp one) (f s)))
                   (opp (sumf f))).
  - apply (sum_ext (fun s => opp (f s)) (fun s => mult (opp one) (f s))).
    intro s.
    apply (req_trans (opp (f s)) (opp (mult one (f s))) (mult (opp one) (f s))).
    + apply (req_opp_compat (f s) (mult one (f s))).
      apply (req_sym (mult one (f s)) (f s)). apply req_mult_one_l.
    + apply (req_sym (mult (opp one) (f s)) (opp (mult one (f s)))).
      apply req_opp_mult_l.
  - apply (req_trans (sumf (fun s => mult (opp one) (f s)))
                     (mult (opp one) (sumf f))
                     (opp (sumf f))).
    + apply (sum_linear (opp one) f).
    + apply (req_trans (mult (opp one) (sumf f)) (opp (mult one (sumf f))) (opp (sumf f))).
      * apply req_opp_mult_l.
      * apply (req_opp_compat (mult one (sumf f)) (sumf f)). apply req_mult_one_l.
Qed.

(* Boltzmann 分布归一化：分布和为一 *)
Lemma req_boltzmann_normalized : req (sumf sigm_boltzmann_dist) one.
Proof.
  apply (req_trans (sumf sigm_boltzmann_dist)
                   (mult (inv_pos Z Z_pos)
                         (sumf (fun s => exp_neg (mult (inv_pos D D_pos) (base_loss s)))))
                   one).
  - exact (sum_linear (inv_pos Z Z_pos)
                      (fun s => exp_neg (mult (inv_pos D D_pos) (base_loss s)))).
  - apply (req_trans (mult (inv_pos Z Z_pos)
                           (sumf (fun s => exp_neg (mult (inv_pos D D_pos) (base_loss s)))))
                     (mult (inv_pos Z Z_pos) Z)
                     one).
    + apply (req_mult_compat (inv_pos Z Z_pos) (inv_pos Z Z_pos)
                             (sumf (fun s => exp_neg (mult (inv_pos D D_pos) (base_loss s)))) Z).
      * apply req_refl.
      * apply (req_sym Z (sumf (fun s => exp_neg (mult (inv_pos D D_pos) (base_loss s))))).
        exact partition_condition.
    + apply (req_trans (mult (inv_pos Z Z_pos) Z) (mult Z (inv_pos Z Z_pos)) one).
      * apply mult_comm.
      * apply inv_pos_correct.
Qed.

(* ============================================================ *)
(* C. 逐点分解：p·E 的两点分解 *)
(* ============================================================ *)
Lemma req_p_times_energy_decomp :
  forall (p : S -> R) (s : S),
    req (mult (p s) (base_loss s)) (plus (opp (mult D (mult (p s) (log (sigm_boltzmann_dist s) (req_boltzmann_positive s))))) (opp (mult D (mult (p s) (log Z Z_pos))))).
Proof.
  intros p s.
  assert (HlegA : req (mult (p s) (base_loss s)) (opp (mult (p s) (mult D (plus (log (sigm_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos)))))).
  { apply (req_trans (mult (p s) (base_loss s)) (mult (p s) (opp (mult D (plus (log (sigm_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos))))) (opp (mult (p s) (mult D (plus (log (sigm_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos)))))).
    - apply (req_mult_compat (p s) (p s) (base_loss s) (opp (mult D (plus (log (sigm_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos))))).
      * apply req_refl.
      * apply (energy_in_log_boltzmann_bridge s).
    - apply (req_mult_opp_l (p s) (mult D (plus (log (sigm_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos)))). }
  assert (Hswap : req (mult (p s) (mult D (plus (log (sigm_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos)))) (mult D (mult (p s) (plus (log (sigm_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos))))).
  { apply (req_trans (mult (p s) (mult D (plus (log (sigm_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos)))) (mult (mult (p s) D) (plus (log (sigm_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos))) (mult D (mult (p s) (plus (log (sigm_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos))))).
    - apply mult_assoc.
      - apply (req_trans (mult (mult (p s) D) (plus (log (sigm_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos))) (mult (mult D (p s)) (plus (log (sigm_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos))) (mult D (mult (p s) (plus (log (sigm_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos))))).
        * apply (req_mult_compat (mult (p s) D) (mult D (p s)) (plus (log (sigm_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos)) (plus (log (sigm_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos))).
          { apply mult_comm. }
          { apply req_refl. }
        * apply (req_sym (mult D (mult (p s) (plus (log (sigm_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos)))) (mult (mult D (p s)) (plus (log (sigm_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos)))). apply mult_assoc.
  }
  assert (Hdist2 : req (mult D (mult (p s) (plus (log (sigm_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos)))) (plus (mult D (mult (p s) (log (sigm_boltzmann_dist s) (req_boltzmann_positive s)))) (mult D (mult (p s) (log Z Z_pos))))).
  { apply (req_trans (mult D (mult (p s) (plus (log (sigm_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos)))) (mult D (plus (mult (p s) (log (sigm_boltzmann_dist s) (req_boltzmann_positive s))) (mult (p s) (log Z Z_pos)))) (plus (mult D (mult (p s) (log (sigm_boltzmann_dist s) (req_boltzmann_positive s)))) (mult D (mult (p s) (log Z Z_pos))))).
    - apply (req_mult_compat D D (mult (p s) (plus (log (sigm_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos))) (plus (mult (p s) (log (sigm_boltzmann_dist s) (req_boltzmann_positive s))) (mult (p s) (log Z Z_pos)))).
      + apply req_refl.
      + apply distrib.
    - apply distrib. }
  apply (req_trans (mult (p s) (base_loss s)) (opp (mult (p s) (mult D (plus (log (sigm_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos))))) (plus (opp (mult D (mult (p s) (log (sigm_boltzmann_dist s) (req_boltzmann_positive s))))) (opp (mult D (mult (p s) (log Z Z_pos)))))).
  - exact HlegA.
  - apply (req_trans (opp (mult (p s) (mult D (plus (log (sigm_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos))))) (opp (mult D (mult (p s) (plus (log (sigm_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos))))) (plus (opp (mult D (mult (p s) (log (sigm_boltzmann_dist s) (req_boltzmann_positive s))))) (opp (mult D (mult (p s) (log Z Z_pos)))))).
    + apply (req_opp_compat (mult (p s) (mult D (plus (log (sigm_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos)))) (mult D (mult (p s) (plus (log (sigm_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos))))). exact Hswap.
    + apply (req_trans (opp (mult D (mult (p s) (plus (log (sigm_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos))))) (opp (plus (mult D (mult (p s) (log (sigm_boltzmann_dist s) (req_boltzmann_positive s)))) (mult D (mult (p s) (log Z Z_pos))))) (plus (opp (mult D (mult (p s) (log (sigm_boltzmann_dist s) (req_boltzmann_positive s))))) (opp (mult D (mult (p s) (log Z Z_pos)))))).
      * apply (req_opp_compat (mult D (mult (p s) (plus (log (sigm_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos)))) (plus (mult D (mult (p s) (log (sigm_boltzmann_dist s) (req_boltzmann_positive s)))) (mult D (mult (p s) (log Z Z_pos))))). exact Hdist2.
      * apply req_opp_plus.
Qed.
(* ============================================================ *)
(* D. 主定理：req_free_energy_kl_decomp                            *)
(*    F[p] == F[p_b] + D·KL(p‖p_b)                                *)
(*    KL := fun s => p s · (lgps s − lgpb s)；Fpb := sigm_free_energy p_b *)
(* ============================================================ *)
Theorem req_free_energy_kl_decomp :
  forall (p : S -> R) (Hp : sigm_normalized p) (p0 : sigm_positive_dist p),
    req (sigm_free_energy p p0)
        (plus (sigm_free_energy sigm_boltzmann_dist req_boltzmann_positive)
              (mult D (sumf (fun s =>
                mult (p s) (rminus (log (p s) (p0 s))
                                   (log (sigm_boltzmann_dist s) (req_boltzmann_positive s))))))).
Proof.
  intros p Hp p0.
  (* 桥：F[p_b] == mult (opp D) lgZ == opp (D·lgZ) *)
  assert (Hfb' : req (sigm_free_energy sigm_boltzmann_dist req_boltzmann_positive)
                     (opp (mult D (log Z Z_pos)))).
  { apply (req_trans (sigm_free_energy sigm_boltzmann_dist req_boltzmann_positive)
                     (mult (opp D) (log Z Z_pos))
                     (opp (mult D (log Z Z_pos)))).
    - exact free_energy_boltzmann_bridge.
    - apply req_opp_mult_l. }
  (* 步骤 1：Σ p·E == opp A + opp DlgZ *)
  assert (Hse : req (sumf (fun s => mult (p s) (base_loss s)))
                    (plus (opp (mult D (sumf (fun s => mult (p s) (log (sigm_boltzmann_dist s) (req_boltzmann_positive s))))))
                          (opp (mult D (log Z Z_pos))))).
  { apply (req_trans (sumf (fun s => mult (p s) (base_loss s)))
                     (sumf (fun s => plus (opp (mult D (mult (p s) (log (sigm_boltzmann_dist s) (req_boltzmann_positive s)))))
                                          (opp (mult D (mult (p s) (log Z Z_pos))))))
                     (plus (opp (mult D (sumf (fun s => mult (p s) (log (sigm_boltzmann_dist s) (req_boltzmann_positive s))))))
                           (opp (mult D (log Z Z_pos))))).
    - apply (sum_ext (fun s => mult (p s) (base_loss s))
                     (fun s => plus (opp (mult D (mult (p s) (log (sigm_boltzmann_dist s) (req_boltzmann_positive s)))))
                                    (opp (mult D (mult (p s) (log Z Z_pos)))))).
      { intro s. apply req_p_times_energy_decomp. }
    - apply (req_trans (sumf (fun s => plus (opp (mult D (mult (p s) (log (sigm_boltzmann_dist s) (req_boltzmann_positive s)))))
                                            (opp (mult D (mult (p s) (log Z Z_pos))))))
                       (plus (sumf (fun s => opp (mult D (mult (p s) (log (sigm_boltzmann_dist s) (req_boltzmann_positive s))))))
                             (sumf (fun s => opp (mult D (mult (p s) (log Z Z_pos))))))
                       (plus (opp (mult D (sumf (fun s => mult (p s) (log (sigm_boltzmann_dist s) (req_boltzmann_positive s))))))
                             (opp (mult D (log Z Z_pos))))).
      { apply sum_add. }
      { apply (req_plus_compat (sumf (fun s => opp (mult D (mult (p s) (log (sigm_boltzmann_dist s) (req_boltzmann_positive s))))))
                               (opp (mult D (sumf (fun s => mult (p s) (log (sigm_boltzmann_dist s) (req_boltzmann_positive s))))))
                               (sumf (fun s => opp (mult D (mult (p s) (log Z Z_pos)))))
                               (opp (mult D (log Z Z_pos)))).
        - (* Σ opp(D·p·lgpb) == opp(D·Σ p·lgpb)：sum_opp + D 线性提取 *)
          apply (req_trans (sumf (fun s => opp (mult D (mult (p s) (log (sigm_boltzmann_dist s) (req_boltzmann_positive s))))))
                           (opp (sumf (fun s => mult D (mult (p s) (log (sigm_boltzmann_dist s) (req_boltzmann_positive s))))))
                           (opp (mult D (sumf (fun s => mult (p s) (log (sigm_boltzmann_dist s) (req_boltzmann_positive s))))))).
          { apply req_sum_opp. }
          { apply (req_opp_compat (sumf (fun s => mult D (mult (p s) (log (sigm_boltzmann_dist s) (req_boltzmann_positive s)))))
                                  (mult D (sumf (fun s => mult (p s) (log (sigm_boltzmann_dist s) (req_boltzmann_positive s)))))).
            { apply (sum_linear D (fun s => mult (p s) (log (sigm_boltzmann_dist s) (req_boltzmann_positive s)))). } }
        - (* Σ opp(D·p·lgZ) == opp(D·lgZ)：sum_opp + D 线性 + Σ p·lgZ = lgZ·Σp = lgZ 归一化链 *)
          apply (req_trans (sumf (fun s => opp (mult D (mult (p s) (log Z Z_pos)))))
                           (opp (sumf (fun s => mult D (mult (p s) (log Z Z_pos)))))
                           (opp (mult D (log Z Z_pos)))).
          { apply req_sum_opp. }
          { apply (req_trans (opp (sumf (fun s => mult D (mult (p s) (log Z Z_pos)))))
                             (opp (mult D (sumf (fun s => mult (p s) (log Z Z_pos)))))
                             (opp (mult D (log Z Z_pos)))).
            { apply (req_opp_compat (sumf (fun s => mult D (mult (p s) (log Z Z_pos))))
                                    (mult D (sumf (fun s => mult (p s) (log Z Z_pos))))).
              { apply (sum_linear D (fun s => mult (p s) (log Z Z_pos))). } }
            { apply (req_opp_compat (mult D (sumf (fun s => mult (p s) (log Z Z_pos))))
                                    (mult D (log Z Z_pos))).
              { apply (req_mult_compat D D (sumf (fun s => mult (p s) (log Z Z_pos))) (log Z Z_pos)).
                { apply req_refl. }
                { apply (req_trans (sumf (fun s => mult (p s) (log Z Z_pos)))
                                   (sumf (fun s => mult (log Z Z_pos) (p s)))
                                   (log Z Z_pos)).
                  { apply (sum_ext (fun s => mult (p s) (log Z Z_pos)) (fun s => mult (log Z Z_pos) (p s))).
                    { intro s2. apply mult_comm. } }
                  { apply (req_trans (sumf (fun s => mult (log Z Z_pos) (p s)))
                                     (mult (log Z Z_pos) (sumf p))
                                     (log Z Z_pos)).
                    { apply (sum_linear (log Z Z_pos) p). }
                    { apply (req_trans (mult (log Z Z_pos) (sumf p))
                                       (mult (log Z Z_pos) one)
                                       (log Z Z_pos)).
                      { apply (req_mult_compat (log Z Z_pos) (log Z Z_pos) (sumf p) one).
                        { apply req_refl. }
                        { exact Hp. } }
                      { apply mult_one. } } } } } } }
  }
  }
  (* 步骤 3：D·KL == B + opp A *)
  assert (Hkl : req (mult D (sumf (fun s =>
                      mult (p s) (rminus (log (p s) (p0 s)) (log (sigm_boltzmann_dist s) (req_boltzmann_positive s))))))
                    (plus (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s)))))
                          (opp (mult D (sumf (fun s => mult (p s) (log (sigm_boltzmann_dist s) (req_boltzmann_positive s)))))))).
  { assert (Hpt2 : forall s : S,
        req (mult (p s) (rminus (log (p s) (p0 s)) (log (sigm_boltzmann_dist s) (req_boltzmann_positive s))))
            (plus (mult (p s) (log (p s) (p0 s)))
                  (opp (mult (p s) (log (sigm_boltzmann_dist s) (req_boltzmann_positive s)))))).
    { intro s. unfold rminus.
      apply (req_trans (mult (p s) (plus (log (p s) (p0 s)) (opp (log (sigm_boltzmann_dist s) (req_boltzmann_positive s)))))
                       (plus (mult (p s) (log (p s) (p0 s))) (mult (p s) (opp (log (sigm_boltzmann_dist s) (req_boltzmann_positive s)))))
                       (plus (mult (p s) (log (p s) (p0 s)))
                             (opp (mult (p s) (log (sigm_boltzmann_dist s) (req_boltzmann_positive s)))))).
      { apply distrib. }
      { apply (req_plus_compat (mult (p s) (log (p s) (p0 s))) (mult (p s) (log (p s) (p0 s)))
                               (mult (p s) (opp (log (sigm_boltzmann_dist s) (req_boltzmann_positive s))))
                               (opp (mult (p s) (log (sigm_boltzmann_dist s) (req_boltzmann_positive s))))).
        { apply req_refl. }
        { apply req_mult_opp_l. } } }
    assert (Hinner : req (sumf (fun s => mult (p s) (rminus (log (p s) (p0 s)) (log (sigm_boltzmann_dist s) (req_boltzmann_positive s)))))
                         (plus (sumf (fun s => mult (p s) (log (p s) (p0 s))))
                               (opp (sumf (fun s => mult (p s) (log (sigm_boltzmann_dist s) (req_boltzmann_positive s))))))).
    { apply (req_trans (sumf (fun s => mult (p s) (rminus (log (p s) (p0 s)) (log (sigm_boltzmann_dist s) (req_boltzmann_positive s)))))
                       (sumf (fun s => plus (mult (p s) (log (p s) (p0 s))) (opp (mult (p s) (log (sigm_boltzmann_dist s) (req_boltzmann_positive s))))))
                       (plus (sumf (fun s => mult (p s) (log (p s) (p0 s))))
                             (opp (sumf (fun s => mult (p s) (log (sigm_boltzmann_dist s) (req_boltzmann_positive s))))))).
      { apply (sum_ext (fun s => mult (p s) (rminus (log (p s) (p0 s)) (log (sigm_boltzmann_dist s) (req_boltzmann_positive s))))
                       (fun s => plus (mult (p s) (log (p s) (p0 s))) (opp (mult (p s) (log (sigm_boltzmann_dist s) (req_boltzmann_positive s)))))).
        { exact Hpt2. } }
      { apply (req_trans (sumf (fun s => plus (mult (p s) (log (p s) (p0 s))) (opp (mult (p s) (log (sigm_boltzmann_dist s) (req_boltzmann_positive s))))))
                         (plus (sumf (fun s => mult (p s) (log (p s) (p0 s)))) (sumf (fun s => opp (mult (p s) (log (sigm_boltzmann_dist s) (req_boltzmann_positive s))))))
                         (plus (sumf (fun s => mult (p s) (log (p s) (p0 s))))
                               (opp (sumf (fun s => mult (p s) (log (sigm_boltzmann_dist s) (req_boltzmann_positive s))))))).
        { apply sum_add. }
        { apply (req_plus_compat (sumf (fun s => mult (p s) (log (p s) (p0 s)))) (sumf (fun s => mult (p s) (log (p s) (p0 s))))
                                 (sumf (fun s => opp (mult (p s) (log (sigm_boltzmann_dist s) (req_boltzmann_positive s)))))
                                 (opp (sumf (fun s => mult (p s) (log (sigm_boltzmann_dist s) (req_boltzmann_positive s)))))).
          { apply req_refl. }
          { apply req_sum_opp. } } } }
    apply (req_trans (mult D (sumf (fun s => mult (p s) (rminus (log (p s) (p0 s)) (log (sigm_boltzmann_dist s) (req_boltzmann_positive s))))))
                     (mult D (plus (sumf (fun s => mult (p s) (log (p s) (p0 s))))
                                   (opp (sumf (fun s => mult (p s) (log (sigm_boltzmann_dist s) (req_boltzmann_positive s)))))))
                     (plus (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s)))))
                           (opp (mult D (sumf (fun s => mult (p s) (log (sigm_boltzmann_dist s) (req_boltzmann_positive s)))))))).
    { apply (req_mult_compat D D
                             (sumf (fun s => mult (p s) (rminus (log (p s) (p0 s)) (log (sigm_boltzmann_dist s) (req_boltzmann_positive s)))))
                             (plus (sumf (fun s => mult (p s) (log (p s) (p0 s))))
                                   (opp (sumf (fun s => mult (p s) (log (sigm_boltzmann_dist s) (req_boltzmann_positive s))))))).
      { apply req_refl. }
      { exact Hinner. } }
    apply (req_trans (mult D (plus (sumf (fun s => mult (p s) (log (p s) (p0 s))))
                                   (opp (sumf (fun s => mult (p s) (log (sigm_boltzmann_dist s) (req_boltzmann_positive s)))))))
                     (plus (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s)))))
                           (mult D (opp (sumf (fun s => mult (p s) (log (sigm_boltzmann_dist s) (req_boltzmann_positive s)))))))
                     (plus (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s)))))
                           (opp (mult D (sumf (fun s => mult (p s) (log (sigm_boltzmann_dist s) (req_boltzmann_positive s)))))))).
    { apply distrib. }
    apply (req_plus_compat (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s)))))
                           (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s)))))
                           (mult D (opp (sumf (fun s => mult (p s) (log (sigm_boltzmann_dist s) (req_boltzmann_positive s))))))
                           (opp (mult D (sumf (fun s => mult (p s) (log (sigm_boltzmann_dist s) (req_boltzmann_positive s))))))).
    { apply req_refl. }
    { apply req_mult_opp_l. } }

  (* 步骤 4：环代数坍缩：(opp A + opp DlgZ) + B → opp DlgZ + (B + opp A) *)
  assert (Hfin : req (plus (plus (opp (mult D (sumf (fun s => mult (p s) (log (sigm_boltzmann_dist s) (req_boltzmann_positive s)))))) (opp (mult D (log Z Z_pos)))) (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s))))))
                     (plus (opp (mult D (log Z Z_pos))) (plus (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s))))) (opp (mult D (sumf (fun s => mult (p s) (log (sigm_boltzmann_dist s) (req_boltzmann_positive s))))))))).
  { set (A := (mult D (sumf (fun s => mult (p s) (log (sigm_boltzmann_dist s) (req_boltzmann_positive s)))))).
    set (DlgZ := (mult D (log Z Z_pos))).
    set (B := (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s)))))).
    apply (req_trans (plus (plus (opp A) (opp DlgZ)) B)
                     (plus (opp A) (plus (opp DlgZ) B))
                     (plus (opp DlgZ) (plus B (opp A)))).
    { apply (req_sym (plus (opp A) (plus (opp DlgZ) B))
                     (plus (plus (opp A) (opp DlgZ)) B)).
      apply plus_assoc. }
    apply (req_trans (plus (opp A) (plus (opp DlgZ) B))
                     (plus (opp A) (plus B (opp DlgZ)))
                     (plus (opp DlgZ) (plus B (opp A)))).
    { apply (req_plus_compat (opp A) (opp A) (plus (opp DlgZ) B) (plus B (opp DlgZ))).
      { apply req_refl. }
      { apply plus_comm. } }
    apply (req_trans (plus (opp A) (plus B (opp DlgZ)))
                     (plus (plus (opp A) B) (opp DlgZ))
                     (plus (opp DlgZ) (plus B (opp A)))).
    { apply plus_assoc. }
    apply (req_trans (plus (plus (opp A) B) (opp DlgZ))
                     (plus (plus B (opp A)) (opp DlgZ))
                     (plus (opp DlgZ) (plus B (opp A)))).
    { apply (req_plus_compat (plus (opp A) B) (plus B (opp A)) (opp DlgZ) (opp DlgZ)).
      { apply plus_comm. }
      { apply req_refl. } }
    apply plus_comm. }
  (* 合成：Hleg1（sigm_free_energy p 定义展开 conversion + Hse 于 compat 槽）；Hleg2（Hfin + Hfb'/Hkl 反向收尾槽） *)
  assert (Hleg1 : req (sigm_free_energy p p0) (plus (plus (opp (mult D (sumf (fun s => mult (p s) (log (sigm_boltzmann_dist s) (req_boltzmann_positive s)))))) (opp (mult D (log Z Z_pos)))) (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s))))))).
  { unfold sigm_free_energy.
    apply (req_plus_compat (sumf (fun s => mult (p s) (base_loss s))) (plus (opp (mult D (sumf (fun s => mult (p s) (log (sigm_boltzmann_dist s) (req_boltzmann_positive s)))))) (opp (mult D (log Z Z_pos)))) (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s))))) (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s)))))).
    { exact Hse. }
    { apply req_refl. } }
  assert (Hleg2 : req (plus (plus (opp (mult D (sumf (fun s => mult (p s) (log (sigm_boltzmann_dist s) (req_boltzmann_positive s)))))) (opp (mult D (log Z Z_pos)))) (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s)))))) (plus (sigm_free_energy sigm_boltzmann_dist req_boltzmann_positive) (mult D (sumf (fun s => mult (p s) (rminus (log (p s) (p0 s)) (log (sigm_boltzmann_dist s) (req_boltzmann_positive s)))))))).
  { apply (req_trans (plus (plus (opp (mult D (sumf (fun s => mult (p s) (log (sigm_boltzmann_dist s) (req_boltzmann_positive s)))))) (opp (mult D (log Z Z_pos)))) (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s))))))
                      (plus (opp (mult D (log Z Z_pos))) (plus (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s))))) (opp (mult D (sumf (fun s => mult (p s) (log (sigm_boltzmann_dist s) (req_boltzmann_positive s))))))))
                      (plus (sigm_free_energy sigm_boltzmann_dist req_boltzmann_positive) (mult D (sumf (fun s => mult (p s) (rminus (log (p s) (p0 s)) (log (sigm_boltzmann_dist s) (req_boltzmann_positive s)))))))).
    { exact Hfin. }
    { apply (req_plus_compat (opp (mult D (log Z Z_pos))) (sigm_free_energy sigm_boltzmann_dist req_boltzmann_positive) (plus (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s))))) (opp (mult D (sumf (fun s => mult (p s) (log (sigm_boltzmann_dist s) (req_boltzmann_positive s))))))) (mult D (sumf (fun s => mult (p s) (rminus (log (p s) (p0 s)) (log (sigm_boltzmann_dist s) (req_boltzmann_positive s))))))).
      { apply (req_sym (sigm_free_energy sigm_boltzmann_dist req_boltzmann_positive) (opp (mult D (log Z Z_pos)))). exact Hfb'. }
      { apply (req_sym (mult D (sumf (fun s => mult (p s) (rminus (log (p s) (p0 s)) (log (sigm_boltzmann_dist s) (req_boltzmann_positive s)))))) (plus (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s))))) (opp (mult D (sumf (fun s => mult (p s) (log (sigm_boltzmann_dist s) (req_boltzmann_positive s)))))))). exact Hkl. } } }
  exact (req_trans _ _ _ Hleg1 Hleg2).
Qed.

End ReqFreeEnergyPilot.

(* ============================================================ *)
(* Part 2: req_attention_is_gibbs_temp.                           *)
(*   Three premises and a pointwise conclusion, all on the req     *)
(*   carrier; the section infrastructure (exp_pos_fn /             *)
(*   partition_function_temp / softmax_temp / boltzmann_factor /   *)
(*   Z_thermo / boltzmann_dist_attn) is rebuilt in the same shape. *)
(*   Interface note: the enhanced setoid interface carries no      *)
(*   exp_neg extensionality field; the gap is bridged by the       *)
(*   req-signed premise req_exp_neg_ext (realized on the Real   *)
(*   instance along the cauchy_real_exp_wd construction).          *)
(* ============================================================ *)
Section ReqGibbsPilot.
Variable S : Set.
Variable sumf : (S -> R) -> R.
Hypothesis sum_pos : forall f : S -> R, (forall s : S, lt zero (f s)) -> lt zero (sumf f).
(* 接口缺口桥：exp_neg 的 req 兼容（字段缺失，见上注） *)
Hypothesis req_exp_neg_ext : forall x y : R, req x y -> req (exp_neg x) (exp_neg y).

Variable T : R.
Variable T_pos : lt zero T.
Variable D : R.
Variable D_pos : lt zero D.
Variable energy : S -> R.
Variable z : S -> R.

Definition sigm_exp_pos_fn (x : R) : R := exp_neg (opp x).
Definition sigm_partition_function_temp : R :=
  sumf (fun s => sigm_exp_pos_fn (mult (inv_pos T T_pos) (z s))).
Hypothesis partition_function_temp_pos : lt zero sigm_partition_function_temp.
Definition sigm_softmax_temp (s : S) : R :=
  mult (sigm_exp_pos_fn (mult (inv_pos T T_pos) (z s)))
       (inv_pos sigm_partition_function_temp partition_function_temp_pos).
Definition sigm_boltzmann_factor (s : S) : R :=
  exp_neg (mult (inv_pos D D_pos) (energy s)).
Definition sigm_Z_thermo : R := sumf sigm_boltzmann_factor.
Variable Z_thermo_pos : lt zero sigm_Z_thermo.
Definition sigm_boltzmann_dist_attn (s : S) : R :=
  mult (inv_pos sigm_Z_thermo Z_thermo_pos) (sigm_boltzmann_factor s).

Theorem req_attention_is_gibbs_temp :
  (req (inv_pos T T_pos) (inv_pos D D_pos)) ->
  (forall s : S, req (energy s) (opp (z s))) ->
  (req sigm_Z_thermo sigm_partition_function_temp) ->
  forall s : S, req (sigm_softmax_temp s) (sigm_boltzmann_dist_attn s).
Proof.
  intros HD Henergy HZ s.
  assert (Hf : req (exp_neg (opp (mult (inv_pos T T_pos) (z s))))
                   (exp_neg (mult (inv_pos D D_pos) (energy s)))).
  { apply (req_exp_neg_ext (opp (mult (inv_pos T T_pos) (z s)))
                           (mult (inv_pos D D_pos) (energy s))).
    apply (req_trans (opp (mult (inv_pos T T_pos) (z s)))
                     (mult (inv_pos T T_pos) (opp (z s)))
                     (mult (inv_pos D D_pos) (energy s))).
    - exact (req_sym (mult (inv_pos T T_pos) (opp (z s)))
                     (opp (mult (inv_pos T T_pos) (z s)))
                     (req_mult_opp_l (inv_pos T T_pos) (z s))).
    - apply (req_mult_compat (inv_pos T T_pos) (inv_pos D D_pos) (opp (z s)) (energy s)).
      + exact HD.
      + apply (req_sym (energy s) (opp (z s))). apply Henergy. }
  assert (Hie : req (inv_pos sigm_Z_thermo Z_thermo_pos)
                    (inv_pos sigm_partition_function_temp partition_function_temp_pos)).
  { apply (inv_pos_ext sigm_Z_thermo sigm_partition_function_temp
                       Z_thermo_pos partition_function_temp_pos HZ). }
  unfold sigm_softmax_temp, sigm_boltzmann_dist_attn, sigm_boltzmann_factor, sigm_exp_pos_fn.
  apply (req_trans (mult (exp_neg (opp (mult (inv_pos T T_pos) (z s))))
                             (inv_pos sigm_partition_function_temp partition_function_temp_pos))
                       (mult (exp_neg (mult (inv_pos D D_pos) (energy s)))
                             (inv_pos sigm_Z_thermo Z_thermo_pos))
                       (mult (inv_pos sigm_Z_thermo Z_thermo_pos)
                             (exp_neg (mult (inv_pos D D_pos) (energy s))))).
    { apply (req_mult_compat (exp_neg (opp (mult (inv_pos T T_pos) (z s))))
                             (exp_neg (mult (inv_pos D D_pos) (energy s)))
                             (inv_pos sigm_partition_function_temp partition_function_temp_pos)
                             (inv_pos sigm_Z_thermo Z_thermo_pos)).
      { exact Hf. }
      { apply (req_sym (inv_pos sigm_Z_thermo Z_thermo_pos) (inv_pos sigm_partition_function_temp partition_function_temp_pos)). exact Hie. } }
    apply mult_comm.
Qed.

End ReqGibbsPilot.
