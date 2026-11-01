(* ===================================================================== *)
(*  UpAlignIdReq.v -- req-carried exact identity family on the alignment  *)
(*  objective: single-step exact gap decomposition and the backward-KL    *)
(*  re-axing identity.                                                    *)
(*  Mission.  Six pieces, all Set-valued (req/lt/le):                     *)
(*    1. minus_middle_t12: (a-b)-(c-b) == a-c (telescoping kernel).       *)
(*    2. minus_left_cancel_t12: (a-b)-(a-c) == c-b (left-cancel kernel).  *)
(*    3. policy_gap_next_exact: gap(pi_next) == gap(pi_t) - Delta.        *)
(*    4. policy_gap_decrement_exact: gap(pi_t) - gap(pi_next) == Delta.   *)
(*    5. dpo_loss_step_exact: loss(pi_t) - loss(pi_next) == Delta.        *)
(*    6. policy_gap_backward_kl_exact (conditional): the three-point KL   *)
(*       identity in req position is an explicit premise of the statement.*)
(*  Dependencies.  S01_BaseRing..S15_TailFEPUp, UpReqAlgebra, UpReqDist,  *)
(*    UpReqAlign, UpReqAlign2, UpReqAlign3.  Interface note: in this tree *)
(*    RealInterfaceEnhancedSetoid is the zero-argument Class at           *)
(*    S07_RealSetoidExpLog.v:8075 with global Instance RealEnhancedReal;  *)
(*    R is bound to the global Real by the file-top Notation and the      *)
(*    class fields resolve through that instance (UpReqAlign3.v form).    *)
(*  References.  mathlib relative-entropy policy-improvement bound; Coq   *)
(*    stdlib Reals.                                                       *)
(*  Constructivity.  Zero classical logic; every piece ends in Qed; no    *)
(*    magic values; statements carry Set-layer faces only (zero Prop      *)
(*    leakage).  Base pieces w_gap_base / w_subgap_base forward           *)
(*    r2_gap_diff and r2_rlhf_suboptimality_gap (UpReqAlign3) by full     *)
(*    explicit application, no re-proof.                                  *)
(*  Build.  rocq c -native-compiler no -Q <world> "" (Rocq 9.1;           *)
(*    cpu_guard wrapped; ulimit -s 65532).                                *)
(* ===================================================================== *)

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
Require Import UpReqAlgebra.
Require Import UpReqDist.
Require Import UpReqAlign.
Require Import UpReqAlign2.
Require Import UpReqAlign3.
Import RealInterfaceEnhancedMod.
(* A-face adaptation: the parameterized section binders
   Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}. are removed; the
   carrier R is bound to the global Real by the Notation below, and the class
   fields (req/lt/le/zero/one/plus/mult/opp/abs/log/log_inv/exp_neg/inv_pos)
   resolve through the global instance RealEnhancedReal, per the world's own
   UpReqAlign3.v precedent.  Zero magic values, zero Prop casts, statement
   names and proof bodies unchanged apart from the dropped binder arguments. *)
Notation R := Real.

(* ============================================================ *)
(* Part 1：差分代数两核（纯 req_minus 代数，仅依赖接口）           *)
(* ============================================================ *)
Section AlignDiffAlg.

(* ===== 件 1：望远镜核 (a−b)−(c−b) == a−c ===== *)
(* 装配：r2_minus_rearrange_four（(a−b)−(c−d) == (a−c)−(b−d)，d:=b）
   + req_minus_self_zero（b−b == 0）+ x−0 == x（reqd_minus_compat
   保形 + r2_opp_zero + req_plus_zero_r）。 *)
Lemma minus_middle_t12 : forall a b c : R,
  req (req_minus (req_minus a b) (req_minus c b)) (req_minus a c).
Proof.
  intros a b c.
  apply (req_trans (req_minus (req_minus a b) (req_minus c b))
                   (req_minus (req_minus a c) (req_minus b b))
                   (req_minus a c)).
  - exact (@r2_minus_rearrange_four a b c b).
  - apply (req_trans (req_minus (req_minus a c) (req_minus b b))
                     (req_minus (req_minus a c) zero)
                     (req_minus a c)).
    + exact (req_sym (req_minus (req_minus a c) zero)
                     (req_minus (req_minus a c) (req_minus b b))
                     (reqd_minus_compat (req_minus a c) (req_minus a c)
                                        zero (req_minus b b)
                                        (req_refl (req_minus a c))
                                        (req_sym (req_minus b b) zero
                                           (req_minus_self_zero b b (req_refl b))))).
    + exact (req_trans (req_minus (req_minus a c) zero)
                       (plus (req_minus a c) zero)
                       (req_minus a c)
                       (req_plus_compat (req_minus a c) (req_minus a c)
                                        (opp zero) zero
                                        (req_refl (req_minus a c))
                                        (r2_opp_zero))
                       (req_plus_zero_r (req_minus a c))).
Qed.

(* ===== 件 2：左消去核 (a−b)−(a−c) == c−b ===== *)
(* 装配：req_minus_plus_congr（(A+X)−(A+Y) == X−Y，X:=-b，Y:=-c）
   + req_double_neg + plus_comm 三步。 *)
Lemma minus_left_cancel_t12 : forall a b c : R,
  req (req_minus (req_minus a b) (req_minus a c)) (req_minus c b).
Proof.
  intros a b c.
  apply (req_trans (req_minus (req_minus a b) (req_minus a c))
                   (req_minus (opp b) (opp c))
                   (req_minus c b)).
  - exact (req_minus_plus_congr a (opp b) (opp c)).
  - apply (req_trans (req_minus (opp b) (opp c))
                     (plus (opp b) c)
                     (req_minus c b)).
    + exact (req_plus_compat (opp b) (opp b) (opp (opp c)) c
                             (req_refl (opp b)) (req_double_neg c)).
    + exact (plus_comm (opp b) c).
Qed.

End AlignDiffAlg.

(* ============================================================ *)
(* Part 2：RLHF gap 恒等式四件                                    *)
(*   （节参数与 UpReqAlign3 Req3AlignCore 逐位对齐）               *)
(* ============================================================ *)
Section AlignGapReq.

Variable S : Set.

Variable sumf : (S -> R) -> R.
Hypothesis sum_ext :
  forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g).
Hypothesis sum_add :
  forall f g : S -> R,
    req (sumf (fun s => plus (f s) (g s))) (plus (sumf f) (sumf g)).
Hypothesis sum_linear :
  forall (a : R) (f : S -> R),
    req (sumf (fun s => mult a (f s))) (mult a (sumf f)).
Hypothesis sum_pos :
  forall f : S -> R, (forall s : S, lt zero (f s)) -> lt zero (sumf f).
Hypothesis log_req_compat :
  forall (x y : R) (Hx : lt zero x) (Hy : lt zero y),
    req x y -> req (log x Hx) (log y Hy).
Hypothesis log_inv_exp_neg_req :
  forall x : R, req (log_inv (exp_neg x) (exp_neg_pos x)) x.

Variable reward : S -> R.
Variable beta : R.
Variable beta_pos : lt zero beta.
Variable pi_ref : S -> R.
Variable pi_ref_pos : forall s : S, lt zero (pi_ref s).
Variable eta : R.
Variable eta_pos : lt zero eta.

(* ---- 局部别名（上游 req2 定义的 δ 透明薄包装，与 UpReqAlign3 同式） ---- *)
Definition pos3 (p : S -> R) : Set := @req2_pos_dist S p.
Definition nrm (p : S -> R) : Set := @req2_norm_one S sumf p.
Definition KLE (p q : S -> R) (Hp : pos3 p) (Hq : pos3 q) : R :=
  @req2_rel_ent S sumf p q Hp Hq.
Definition JJ (p : S -> R) (Hp : pos3 p) : R :=
  @req2_J S sumf reward beta pi_ref pi_ref_pos p Hp.
Definition NPX (pi_t : S -> R) (Hpi_t : pos3 pi_t) (s : S) : R :=
  @req2_pi_next S sumf sum_pos reward beta beta_pos pi_ref pi_ref_pos
                eta pi_t Hpi_t s.
Definition npx_pos (pi_t : S -> R) (Hpi_t : pos3 pi_t) : pos3 (NPX pi_t Hpi_t) :=
  @req2_pi_next_pos S sumf sum_pos reward beta beta_pos pi_ref
                    pi_ref_pos eta pi_t Hpi_t.
Definition ZAL : R :=
  @req2_Z_align S sumf reward beta beta_pos pi_ref.
Variable ZAL_pos : lt zero ZAL.
Definition PSTR (s : S) : R :=
  @req2_pi_star S sumf reward beta beta_pos pi_ref ZAL_pos s.
Definition PSTR_pos : pos3 PSTR :=
  @req2_pi_star_pos S sumf reward beta beta_pos pi_ref pi_ref_pos ZAL_pos.
Definition AO (p : S -> R) (Hp : pos3 p) : R :=
  @req2_dpo_loss S sumf reward beta pi_ref pi_ref_pos p Hp.

(* ---- 基座件使用（@ 全参；零重证） ---- *)
Lemma w_gap_base : forall (pi_t : S -> R) (Hpi_t : pos3 pi_t) (Hn : nrm pi_t),
  req (req_minus (JJ (NPX pi_t Hpi_t) (npx_pos pi_t Hpi_t)) (JJ pi_t Hpi_t))
      (mult beta
            (plus (mult (req_minus (inv_pos eta eta_pos) one)
                        (KLE (NPX pi_t Hpi_t) pi_t (npx_pos pi_t Hpi_t) Hpi_t))
                  (mult (inv_pos eta eta_pos)
                        (KLE pi_t (NPX pi_t Hpi_t) Hpi_t (npx_pos pi_t Hpi_t))))).
Proof.
  intros pi_t Hpi_t Hn.
  exact (@r2_gap_diff S sumf sum_ext sum_add sum_linear sum_pos
                      log_req_compat log_inv_exp_neg_req
                      reward beta beta_pos pi_ref pi_ref_pos eta eta_pos
                      pi_t Hpi_t Hn).
Qed.

Lemma w_subgap_base : forall (p : S -> R) (Hp : pos3 p) (Hn : nrm p),
  req (req_minus (JJ PSTR PSTR_pos) (JJ p Hp))
      (mult beta (KLE p PSTR Hp PSTR_pos)).
Proof.
  intros p Hp Hn.
  exact (@r2_rlhf_suboptimality_gap S sumf sum_ext sum_add sum_linear
                                    log_req_compat log_inv_exp_neg_req
                                    reward beta beta_pos pi_ref pi_ref_pos
                                    ZAL_pos p Hp Hn).
Qed.

(* ===== 件 3（主定理）：gap 的单步精确分解 ===== *)
(* gap(pi_{t+1}) == gap(pi_t) − Δ
   装配：minus_middle_t12 的对称形 + reqd_minus_compat（Hgap/Hdiff 保形）。
   记 G := J(pi_star)，T := J(pi_t)，N := J(pi_{t+1})：
     G − N == (G − T) − (N − T) == (β·KL_t) − Δ。 *)
Theorem policy_gap_next_exact :
  forall (pi_t : S -> R) (Hpi_t : pos3 pi_t) (Hn : nrm pi_t),
    req (req_minus (JJ PSTR PSTR_pos)
                   (JJ (NPX pi_t Hpi_t) (npx_pos pi_t Hpi_t)))
        (req_minus (mult beta (KLE pi_t PSTR Hpi_t PSTR_pos))
                   (mult beta
                         (plus (mult (req_minus (inv_pos eta eta_pos) one)
                                     (KLE (NPX pi_t Hpi_t) pi_t
                                          (npx_pos pi_t Hpi_t) Hpi_t))
                               (mult (inv_pos eta eta_pos)
                                     (KLE pi_t (NPX pi_t Hpi_t)
                                          Hpi_t (npx_pos pi_t Hpi_t)))))).
Proof.
  intros pi_t Hpi_t Hn.
  exact (req_trans
          (req_minus (JJ PSTR PSTR_pos)
                     (JJ (NPX pi_t Hpi_t) (npx_pos pi_t Hpi_t)))
          (req_minus (req_minus (JJ PSTR PSTR_pos) (JJ pi_t Hpi_t))
                     (req_minus (JJ (NPX pi_t Hpi_t) (npx_pos pi_t Hpi_t))
                                (JJ pi_t Hpi_t)))
          (req_minus (mult beta (KLE pi_t PSTR Hpi_t PSTR_pos))
                     (mult beta
                           (plus (mult (req_minus (inv_pos eta eta_pos) one)
                                       (KLE (NPX pi_t Hpi_t) pi_t
                                            (npx_pos pi_t Hpi_t) Hpi_t))
                                 (mult (inv_pos eta eta_pos)
                                       (KLE pi_t (NPX pi_t Hpi_t)
                                            Hpi_t (npx_pos pi_t Hpi_t))))))
          (req_sym
              (req_minus (req_minus (JJ PSTR PSTR_pos) (JJ pi_t Hpi_t))
                         (req_minus (JJ (NPX pi_t Hpi_t) (npx_pos pi_t Hpi_t))
                                    (JJ pi_t Hpi_t)))
              (req_minus (JJ PSTR PSTR_pos)
                         (JJ (NPX pi_t Hpi_t) (npx_pos pi_t Hpi_t)))
              (minus_middle_t12 (JJ PSTR PSTR_pos) (JJ pi_t Hpi_t)
                                (JJ (NPX pi_t Hpi_t) (npx_pos pi_t Hpi_t))))
          (reqd_minus_compat
              (req_minus (JJ PSTR PSTR_pos) (JJ pi_t Hpi_t))
              (mult beta (KLE pi_t PSTR Hpi_t PSTR_pos))
              (req_minus (JJ (NPX pi_t Hpi_t) (npx_pos pi_t Hpi_t))
                         (JJ pi_t Hpi_t))
              (mult beta
                    (plus (mult (req_minus (inv_pos eta eta_pos) one)
                                (KLE (NPX pi_t Hpi_t) pi_t
                                     (npx_pos pi_t Hpi_t) Hpi_t))
                          (mult (inv_pos eta eta_pos)
                                (KLE pi_t (NPX pi_t Hpi_t)
                                     Hpi_t (npx_pos pi_t Hpi_t)))))
              (w_subgap_base pi_t Hpi_t Hn)
              (w_gap_base pi_t Hpi_t Hn))).
Qed.

(* ===== 件 4：gap 递减量的精确恒等式（单调 ≤ 的精确化） ===== *)
(* gap(pi_t) − gap(pi_{t+1}) == Δ（望远镜核 + Δ 精确值直代）。 *)
Corollary policy_gap_decrement_exact :
  forall (pi_t : S -> R) (Hpi_t : pos3 pi_t) (Hn : nrm pi_t),
    req (req_minus (req_minus (JJ PSTR PSTR_pos) (JJ pi_t Hpi_t))
                   (req_minus (JJ PSTR PSTR_pos)
                              (JJ (NPX pi_t Hpi_t) (npx_pos pi_t Hpi_t))))
        (mult beta
              (plus (mult (req_minus (inv_pos eta eta_pos) one)
                          (KLE (NPX pi_t Hpi_t) pi_t
                               (npx_pos pi_t Hpi_t) Hpi_t))
                    (mult (inv_pos eta eta_pos)
                          (KLE pi_t (NPX pi_t Hpi_t)
                               Hpi_t (npx_pos pi_t Hpi_t))))).
Proof.
  intros pi_t Hpi_t Hn.
  exact (req_trans
          (req_minus (req_minus (JJ PSTR PSTR_pos) (JJ pi_t Hpi_t))
                     (req_minus (JJ PSTR PSTR_pos)
                                (JJ (NPX pi_t Hpi_t) (npx_pos pi_t Hpi_t))))
          (req_minus (JJ (NPX pi_t Hpi_t) (npx_pos pi_t Hpi_t))
                     (JJ pi_t Hpi_t))
          (mult beta
                (plus (mult (req_minus (inv_pos eta eta_pos) one)
                            (KLE (NPX pi_t Hpi_t) pi_t
                                 (npx_pos pi_t Hpi_t) Hpi_t))
                      (mult (inv_pos eta eta_pos)
                            (KLE pi_t (NPX pi_t Hpi_t)
                                 Hpi_t (npx_pos pi_t Hpi_t)))))
          (minus_left_cancel_t12 (JJ PSTR PSTR_pos) (JJ pi_t Hpi_t)
                                 (JJ (NPX pi_t Hpi_t) (npx_pos pi_t Hpi_t)))
          (w_gap_base pi_t Hpi_t Hn)).
Qed.

(* ===== 件 5：dpo_loss 单步精确差（换轴并列形态） ===== *)
(* dpo_loss(p) := opp J(p)（req2_dpo_loss δ 透明）。
   loss(pi_t) − loss(pi_{t+1}) == (−J_t) − (−J_next) == J_next − J_t == Δ。 *)
Theorem dpo_loss_step_exact :
  forall (pi_t : S -> R) (Hpi_t : pos3 pi_t) (Hn : nrm pi_t),
    req (req_minus (AO pi_t Hpi_t)
                   (AO (NPX pi_t Hpi_t) (npx_pos pi_t Hpi_t)))
        (mult beta
              (plus (mult (req_minus (inv_pos eta eta_pos) one)
                          (KLE (NPX pi_t Hpi_t) pi_t
                               (npx_pos pi_t Hpi_t) Hpi_t))
                    (mult (inv_pos eta eta_pos)
                          (KLE pi_t (NPX pi_t Hpi_t)
                               Hpi_t (npx_pos pi_t Hpi_t))))).
Proof.
  intros pi_t Hpi_t Hn.
  apply (req_trans (req_minus (AO pi_t Hpi_t)
                              (AO (NPX pi_t Hpi_t) (npx_pos pi_t Hpi_t)))
                   (req_minus (JJ (NPX pi_t Hpi_t) (npx_pos pi_t Hpi_t))
                              (JJ pi_t Hpi_t))).
  - apply (req_trans (req_minus (opp (JJ pi_t Hpi_t))
                                (opp (JJ (NPX pi_t Hpi_t) (npx_pos pi_t Hpi_t))))
                     (plus (opp (JJ pi_t Hpi_t))
                           (JJ (NPX pi_t Hpi_t) (npx_pos pi_t Hpi_t)))
                     (req_minus (JJ (NPX pi_t Hpi_t) (npx_pos pi_t Hpi_t))
                                (JJ pi_t Hpi_t))).
    + exact (req_plus_compat (opp (JJ pi_t Hpi_t)) (opp (JJ pi_t Hpi_t))
                             (opp (opp (JJ (NPX pi_t Hpi_t) (npx_pos pi_t Hpi_t))))
                             (JJ (NPX pi_t Hpi_t) (npx_pos pi_t Hpi_t))
                             (req_refl (opp (JJ pi_t Hpi_t)))
                             (req_double_neg (JJ (NPX pi_t Hpi_t) (npx_pos pi_t Hpi_t)))).
    + exact (plus_comm (opp (JJ pi_t Hpi_t))
                       (JJ (NPX pi_t Hpi_t) (npx_pos pi_t Hpi_t))).
  - exact (w_gap_base pi_t Hpi_t Hn).
Qed.

(* ===== 件 6（主定理）：后向 KL 递推的换轴精确恒等式（条件形） ===== *)
(* β·KL(pi*‖pi_{t+1}) == (1−η)·β·KL(pi*‖pi_t) − η·gap(pi_t) + β·K2
   前提 = 三 KL 精确恒等的 req 同位形（显式前提位，语句层可见）；
   本件结果的构造性内容 = 整体 β 缩放链（mult_assoc/comm/反结合 +
   req_opp_mult_l + Hgap 精确代换 + distrib 两级分配组装）。 *)
Theorem policy_gap_backward_kl_exact :
  forall (pi_t : S -> R) (Hpi_t : pos3 pi_t) (Hn : nrm pi_t),
    req (KLE (NPX pi_t Hpi_t) PSTR (npx_pos pi_t Hpi_t) PSTR_pos)
        (plus (mult (req_minus one eta) (KLE PSTR pi_t PSTR_pos Hpi_t))
              (plus (opp (mult eta (KLE pi_t PSTR Hpi_t PSTR_pos)))
                    (KLE pi_t (NPX pi_t Hpi_t) Hpi_t (npx_pos pi_t Hpi_t)))) ->
    req (mult beta
              (KLE (NPX pi_t Hpi_t) PSTR (npx_pos pi_t Hpi_t) PSTR_pos))
        (plus (mult (req_minus one eta)
                    (mult beta (KLE PSTR pi_t PSTR_pos Hpi_t)))
              (plus (opp (mult eta
                              (req_minus (JJ PSTR PSTR_pos) (JJ pi_t Hpi_t))))
                    (mult beta
                          (KLE pi_t (NPX pi_t Hpi_t)
                               Hpi_t (npx_pos pi_t Hpi_t))))).
Proof.
  intros pi_t Hpi_t Hn Hbridge.
  assert (Hgap : req (req_minus (JJ PSTR PSTR_pos) (JJ pi_t Hpi_t))
                     (mult beta (KLE pi_t PSTR Hpi_t PSTR_pos)))
    by exact (w_subgap_base pi_t Hpi_t Hn).
  (* β 缩放核 1：β·(I·KSP) == I·(β·KSP)，I := 1−η *)
  assert (Hscale1 : req (mult beta (mult (req_minus one eta)
                                         (KLE PSTR pi_t PSTR_pos Hpi_t)))
                        (mult (req_minus one eta)
                              (mult beta (KLE PSTR pi_t PSTR_pos Hpi_t)))).
  { apply (req_trans
              (mult beta (mult (req_minus one eta)
                               (KLE PSTR pi_t PSTR_pos Hpi_t)))
              (mult (mult beta (req_minus one eta))
                    (KLE PSTR pi_t PSTR_pos Hpi_t))
              (mult (req_minus one eta)
                    (mult beta (KLE PSTR pi_t PSTR_pos Hpi_t)))).
    - exact (mult_assoc beta (req_minus one eta)
                        (KLE PSTR pi_t PSTR_pos Hpi_t)).
    - apply (req_trans
                (mult (mult beta (req_minus one eta))
                      (KLE PSTR pi_t PSTR_pos Hpi_t))
                (mult (mult (req_minus one eta) beta)
                      (KLE PSTR pi_t PSTR_pos Hpi_t))
                (mult (req_minus one eta)
                      (mult beta (KLE PSTR pi_t PSTR_pos Hpi_t)))).
      + exact (req_mult_compat (mult beta (req_minus one eta))
                               (mult (req_minus one eta) beta)
                               (KLE PSTR pi_t PSTR_pos Hpi_t)
                               (KLE PSTR pi_t PSTR_pos Hpi_t)
                               (mult_comm beta (req_minus one eta))
                               (req_refl (KLE PSTR pi_t PSTR_pos Hpi_t))).
      + exact (req_sym (mult (req_minus one eta)
                             (mult beta (KLE PSTR pi_t PSTR_pos Hpi_t)))
                       (mult (mult (req_minus one eta) beta)
                             (KLE PSTR pi_t PSTR_pos Hpi_t))
                       (mult_assoc (req_minus one eta) beta
                                   (KLE PSTR pi_t PSTR_pos Hpi_t))). }
  (* β 缩放核 2：β·(η·KTS) == η·(β·KTS) *)
  assert (Hswap2 : req (mult beta (mult eta (KLE pi_t PSTR Hpi_t PSTR_pos)))
                       (mult eta (mult beta (KLE pi_t PSTR Hpi_t PSTR_pos)))).
  { apply (req_trans
              (mult beta (mult eta (KLE pi_t PSTR Hpi_t PSTR_pos)))
              (mult (mult beta eta) (KLE pi_t PSTR Hpi_t PSTR_pos))
              (mult eta (mult beta (KLE pi_t PSTR Hpi_t PSTR_pos)))).
    - exact (mult_assoc beta eta (KLE pi_t PSTR Hpi_t PSTR_pos)).
    - apply (req_trans
                (mult (mult beta eta) (KLE pi_t PSTR Hpi_t PSTR_pos))
                (mult (mult eta beta) (KLE pi_t PSTR Hpi_t PSTR_pos))
                (mult eta (mult beta (KLE pi_t PSTR Hpi_t PSTR_pos)))).
      + exact (req_mult_compat (mult beta eta) (mult eta beta)
                               (KLE pi_t PSTR Hpi_t PSTR_pos)
                               (KLE pi_t PSTR Hpi_t PSTR_pos)
                               (mult_comm beta eta)
                               (req_refl (KLE pi_t PSTR Hpi_t PSTR_pos))).
      + exact (req_sym (mult eta (mult beta (KLE pi_t PSTR Hpi_t PSTR_pos)))
                       (mult (mult eta beta) (KLE pi_t PSTR Hpi_t PSTR_pos))
                       (mult_assoc eta beta (KLE pi_t PSTR Hpi_t PSTR_pos))). }
  (* β·(opp (η·KTS)) == opp (η·gap(pi_t))：req_opp_mult_l + 核 2 + Hgap 代换 *)
  assert (Hscale2 : req (mult beta (opp (mult eta (KLE pi_t PSTR Hpi_t PSTR_pos))))
                        (opp (mult eta
                                   (req_minus (JJ PSTR PSTR_pos)
                                              (JJ pi_t Hpi_t))))).
  { apply (req_trans
              (mult beta (opp (mult eta (KLE pi_t PSTR Hpi_t PSTR_pos))))
              (opp (mult beta (mult eta (KLE pi_t PSTR Hpi_t PSTR_pos))))
              (opp (mult eta (req_minus (JJ PSTR PSTR_pos) (JJ pi_t Hpi_t))))).
    - exact (req_opp_mult_l beta (mult eta (KLE pi_t PSTR Hpi_t PSTR_pos))).
    - apply (req_opp_compat
                (mult beta (mult eta (KLE pi_t PSTR Hpi_t PSTR_pos)))
                (mult eta (req_minus (JJ PSTR PSTR_pos) (JJ pi_t Hpi_t)))).
      exact (req_trans
                (mult beta (mult eta (KLE pi_t PSTR Hpi_t PSTR_pos)))
                (mult eta (mult beta (KLE pi_t PSTR Hpi_t PSTR_pos)))
                (mult eta (req_minus (JJ PSTR PSTR_pos) (JJ pi_t Hpi_t)))
                Hswap2
                (req_mult_compat eta eta
                   (mult beta (KLE pi_t PSTR Hpi_t PSTR_pos))
                   (req_minus (JJ PSTR PSTR_pos) (JJ pi_t Hpi_t))
                   (req_refl eta)
                   (req_sym (req_minus (JJ PSTR PSTR_pos) (JJ pi_t Hpi_t))
                            (mult beta (KLE pi_t PSTR Hpi_t PSTR_pos))
                            Hgap))). }
  (* β 分配到后半树：β·(B + C) == β·B + β·C，B 项换形 *)
  assert (Hscale3 : req (mult beta (plus (opp (mult eta (KLE pi_t PSTR Hpi_t PSTR_pos)))
                                         (KLE pi_t (NPX pi_t Hpi_t)
                                              Hpi_t (npx_pos pi_t Hpi_t))))
                        (plus (opp (mult eta
                                            (req_minus (JJ PSTR PSTR_pos)
                                                       (JJ pi_t Hpi_t))))
                              (mult beta (KLE pi_t (NPX pi_t Hpi_t)
                                               Hpi_t (npx_pos pi_t Hpi_t))))).
  { apply (req_trans
              (mult beta (plus (opp (mult eta (KLE pi_t PSTR Hpi_t PSTR_pos)))
                               (KLE pi_t (NPX pi_t Hpi_t)
                                    Hpi_t (npx_pos pi_t Hpi_t))))
              (plus (mult beta (opp (mult eta (KLE pi_t PSTR Hpi_t PSTR_pos))))
                    (mult beta (KLE pi_t (NPX pi_t Hpi_t)
                                     Hpi_t (npx_pos pi_t Hpi_t))))
              (plus (opp (mult eta
                                 (req_minus (JJ PSTR PSTR_pos)
                                            (JJ pi_t Hpi_t))))
                    (mult beta (KLE pi_t (NPX pi_t Hpi_t)
                                     Hpi_t (npx_pos pi_t Hpi_t))))).
    - exact (distrib beta
                     (opp (mult eta (KLE pi_t PSTR Hpi_t PSTR_pos)))
                     (KLE pi_t (NPX pi_t Hpi_t) Hpi_t (npx_pos pi_t Hpi_t))).
    - exact (req_plus_compat
                (mult beta (opp (mult eta (KLE pi_t PSTR Hpi_t PSTR_pos))))
                (opp (mult eta
                            (req_minus (JJ PSTR PSTR_pos) (JJ pi_t Hpi_t))))
                (mult beta (KLE pi_t (NPX pi_t Hpi_t)
                                 Hpi_t (npx_pos pi_t Hpi_t)))
                (mult beta (KLE pi_t (NPX pi_t Hpi_t)
                                 Hpi_t (npx_pos pi_t Hpi_t)))
                Hscale2 (req_refl (mult beta (KLE pi_t (NPX pi_t Hpi_t)
                                              Hpi_t (npx_pos pi_t Hpi_t))))). }
  (* 全树 β 分配组装 *)
  assert (Hscale : req
              (mult beta (plus (mult (req_minus one eta)
                                     (KLE PSTR pi_t PSTR_pos Hpi_t))
                               (plus (opp (mult eta
                                                  (KLE pi_t PSTR Hpi_t PSTR_pos)))
                                     (KLE pi_t (NPX pi_t Hpi_t)
                                          Hpi_t (npx_pos pi_t Hpi_t)))))
              (plus (mult (req_minus one eta)
                          (mult beta (KLE PSTR pi_t PSTR_pos Hpi_t)))
                    (plus (opp (mult eta
                                       (req_minus (JJ PSTR PSTR_pos)
                                                  (JJ pi_t Hpi_t))))
                          (mult beta (KLE pi_t (NPX pi_t Hpi_t)
                                           Hpi_t (npx_pos pi_t Hpi_t)))))).
  { apply (req_trans
              (mult beta (plus (mult (req_minus one eta)
                                     (KLE PSTR pi_t PSTR_pos Hpi_t))
                               (plus (opp (mult eta
                                                  (KLE pi_t PSTR Hpi_t PSTR_pos)))
                                     (KLE pi_t (NPX pi_t Hpi_t)
                                          Hpi_t (npx_pos pi_t Hpi_t)))))
              (plus (mult beta (mult (req_minus one eta)
                                     (KLE PSTR pi_t PSTR_pos Hpi_t)))
                    (mult beta (plus (opp (mult eta
                                                   (KLE pi_t PSTR Hpi_t PSTR_pos)))
                                     (KLE pi_t (NPX pi_t Hpi_t)
                                          Hpi_t (npx_pos pi_t Hpi_t)))))
              (plus (mult (req_minus one eta)
                          (mult beta (KLE PSTR pi_t PSTR_pos Hpi_t)))
                    (plus (opp (mult eta
                                       (req_minus (JJ PSTR PSTR_pos)
                                                  (JJ pi_t Hpi_t))))
                          (mult beta (KLE pi_t (NPX pi_t Hpi_t)
                                           Hpi_t (npx_pos pi_t Hpi_t)))))).
    - exact (distrib beta
                     (mult (req_minus one eta) (KLE PSTR pi_t PSTR_pos Hpi_t))
                     (plus (opp (mult eta (KLE pi_t PSTR Hpi_t PSTR_pos)))
                           (KLE pi_t (NPX pi_t Hpi_t)
                                Hpi_t (npx_pos pi_t Hpi_t)))).
    - exact (req_plus_compat
                (mult beta (mult (req_minus one eta)
                                 (KLE PSTR pi_t PSTR_pos Hpi_t)))
                (mult (req_minus one eta)
                      (mult beta (KLE PSTR pi_t PSTR_pos Hpi_t)))
                (mult beta (plus (opp (mult eta
                                               (KLE pi_t PSTR Hpi_t PSTR_pos)))
                                 (KLE pi_t (NPX pi_t Hpi_t)
                                      Hpi_t (npx_pos pi_t Hpi_t))))
                (plus (opp (mult eta
                                       (req_minus (JJ PSTR PSTR_pos)
                                                  (JJ pi_t Hpi_t))))
                      (mult beta (KLE pi_t (NPX pi_t Hpi_t)
                                           Hpi_t (npx_pos pi_t Hpi_t))))
                Hscale1 Hscale3). }
  exact (req_trans
          (mult beta (KLE (NPX pi_t Hpi_t) PSTR (npx_pos pi_t Hpi_t) PSTR_pos))
          (mult beta
                (plus (mult (req_minus one eta) (KLE PSTR pi_t PSTR_pos Hpi_t))
                      (plus (opp (mult eta (KLE pi_t PSTR Hpi_t PSTR_pos)))
                            (KLE pi_t (NPX pi_t Hpi_t)
                                 Hpi_t (npx_pos pi_t Hpi_t)))))
          (plus (mult (req_minus one eta)
                      (mult beta (KLE PSTR pi_t PSTR_pos Hpi_t)))
                (plus (opp (mult eta
                                   (req_minus (JJ PSTR PSTR_pos)
                                              (JJ pi_t Hpi_t))))
                      (mult beta (KLE pi_t (NPX pi_t Hpi_t)
                                           Hpi_t (npx_pos pi_t Hpi_t)))))
          (req_mult_compat beta beta
              (KLE (NPX pi_t Hpi_t) PSTR (npx_pos pi_t Hpi_t) PSTR_pos)
              (plus (mult (req_minus one eta) (KLE PSTR pi_t PSTR_pos Hpi_t))
                    (plus (opp (mult eta (KLE pi_t PSTR Hpi_t PSTR_pos)))
                          (KLE pi_t (NPX pi_t Hpi_t)
                               Hpi_t (npx_pos pi_t Hpi_t))))
              (req_refl beta) Hbridge)
          Hscale).
Qed.

End AlignGapReq.
