(* ConstructiveWorld-Set -- Q-layer dot products and kernel gap bounds. *)

(** * UpReqConcB2: Q-layer dot products and kernel gap bounds.

    Mission.  Formalizes the [cb2_dot] family on finite [list Real]
      vectors (sumd fold [cb2_dot_via_sumd], linearity [cb2_dot_map_mult_l],
      symmetry [cb2_dot_comm], cap bounds [cb2_dot_le_max],
      [cb2_dot_lt_max_eps]); the logit kernel bounds [cb2_z_lb],
      [cb2_z_ub], [cb2_z_lb_all], [cb2_z_ub_all] against [cb2_Delta]; and
      the all-zero certificates [cb2_smoke_complete], [cb2_smoke_ub_cert].

    Dependencies.  Stdlib [List], [QArith.QArith], [QArith.Qabs],
      [QArith.Qminmax], [Lia].  Requires [S01_BaseRing], [S02_CauchyComplete],
      [S03_QExp], [S04_RealExpLogConv], [S05_AlignmentGRPO],
      [S06_DiffSamplingGibbs], [S07_RealSetoidExpLog], [S08_RealMainlineDPO],
      [S09_EntropyReal], [S10_KVQuantTrig], [S11_TP3B5], [S12_B5RecycleSF],
      [S13_NLiveAudit], [S14_B5BatchBlock], [S15_TailFEPUp], [UpReqAlgebra],
      [UpReqSumD] of this development.

    References.  This development, UpReqConcB2.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" UpReqConcB2.v] compiles
      cleanly (exit 0); the artifact starts with [436f7121 00015ff4]. *)
From Stdlib Require Import List.
From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Lia QArith.Qminmax.
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
Require Import UpReqSumD.
Import RealInterfaceEnhancedMod.
Import ListNotations.

(* ============================================================ *)
(* Section 1. Pointwise Q-layer helpers, the arithmetic floor of the gap certificates. *)
(* ============================================================ *)

(* [x <= Qabs x]: the two branches of [Qabs_case]; [Qabs] is encoded via
   [Z.abs], not a [Qmax] shape, so the dual lemma does not apply here. *)
Lemma cb2_qabs_ge : forall x : Q, Qle x (Qabs x).
Proof.
  intro x. apply (Qabs_case x (fun w : Q => Qle x w)).
  - intro Hdummy. apply Qle_refl.
  - intro Hx0. apply (Qle_trans x 0 (Qopp x) Hx0).
    exact (Qopp_le_compat x 0 Hx0).
Qed.

(* [- x <= Qabs x]. *)
Lemma cb2_qabs_ge_opp : forall x : Q, Qle (Qopp x) (Qabs x).
Proof.
  intro x. apply (Qabs_case x (fun w : Q => Qle (Qopp x) w)).
  - intro Hx0. apply (Qle_trans (Qopp x) 0 x).
    + exact (Qopp_le_compat 0 x Hx0).
    + exact Hx0.
  - intro Hdummy. apply Qle_refl.
Qed.

(* [0 <= Qabs x]. *)
Lemma cb2_qabs_nonneg : forall x : Q, Qle 0 (Qabs x).
Proof.
  intro x. apply (Qabs_case x (fun w : Q => Qle 0 w)).
  - intro Hdummy. exact Hdummy.
  - intro Hx0. exact (Qopp_le_compat x 0 Hx0).
Qed.

(* [- Qabs x <= x]: in the branch [x <= 0] the chain [- x <= 0 <= x]
   applies; in the branch [0 <= x] the ring normalization [- - x == x]
   closes it. *)
Lemma cb2_qopp_abs_le : forall x : Q, Qle (Qopp (Qabs x)) x.
Proof.
  intro x. apply (Qabs_case x (fun w : Q => Qle (Qopp w) x)).
  - intro Hx0. apply (Qle_trans (Qopp x) 0 x).
    + exact (Qopp_le_compat 0 x Hx0).
    + exact Hx0.
  - intro Hdummy. apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
Qed.

(* The two [Qmax] membership bounds, from [max_l]/[max_r] of
   [GenericMinMax] with the [Qlt_le_dec] case split. *)
Lemma cb2_qmax_ge_l : forall x y : Q, Qle x (Qmax x y).
Proof.
  intros x y. destruct (Qlt_le_dec x y) as [Hxy | Hxy].
  - rewrite (Q.max_r x y (Qlt_le_weak x y Hxy)). exact (Qlt_le_weak x y Hxy).
  - rewrite (Q.max_l x y Hxy). apply Qle_refl.
Qed.

Lemma cb2_qmax_ge_r : forall x y : Q, Qle y (Qmax x y).
Proof.
  intros x y. destruct (Qlt_le_dec y x) as [Hyx | Hyx].
  - rewrite (Q.max_l x y (Qlt_le_weak y x Hyx)). exact (Qlt_le_weak y x Hyx).
  - rewrite (Q.max_r x y Hyx). apply Qle_refl.
Qed.

(* A product of nonnegative factors is nonnegative. *)
Lemma cb2_qmul_nonneg : forall a b : Q, Qle 0 a -> Qle 0 b -> Qle 0 (a * b).
Proof.
  intros a b Ha Hb.
  assert (H1 : Qle (0 * a) (b * a)) by (apply (Qmult_le_compat_r 0 b a); assumption).
  assert (E0 : Qeq 0 (0 * a)) by ring.
  assert (E2 : Qeq (b * a) (a * b)) by ring.
  exact (Qle_trans 0 (0 * a) (a * b)
           (QleT'_to_Qle _ _ (qeq_le 0 (0 * a) (qeq_imp_qeqT _ _ E0)))
           (Qle_trans (0 * a) (b * a) (a * b) H1
              (QleT'_to_Qle _ _
                 (qeq_le (b * a) (a * b) (qeq_imp_qeqT _ _ E2))))).
Qed.

(* Left multiplication by a nonnegative factor preserves [Qle]. *)
Lemma cb2_qmul_nonneg_r : forall a u v : Q, Qle 0 a -> Qle u v -> Qle (a * u) (a * v).
Proof.
  intros a u v Ha Huv.
  destruct (Qle_lt_or_eq 0 a Ha) as [Hapos | Haeq].
  - exact (Qle_trans (a * u) (u * a) (a * v)
             (QleT'_to_Qle _ _
                (qeq_le (a * u) (u * a) (qeq_imp_qeqT _ _ (Qmult_comm a u))))
             (Qle_trans (u * a) (v * a) (a * v)
                (proj2 (Qmult_le_r u v a Hapos) Huv)
                (QleT'_to_Qle _ _
                   (qeq_le (v * a) (a * v)
                      (qeq_imp_qeqT _ _ (Qmult_comm v a)))))).

  - rewrite <- Haeq.
    apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
    exact (Qeq_trans (0 * u) 0 (0 * v) (Qmult_0_l u)
                      (Qeq_sym (0 * v) 0 (Qmult_0_l v))).
Qed.

(* [x <= y] gives [0 <= y - x]: unpack one direction of the
   [Qplus_le_r] equivalence and normalize by ring. *)
Lemma cb2_qle_minus : forall x y : Q, Qle x y -> Qle 0 (Qminus y x).
Proof.
  intros x y H.
  assert (Hz : Qeq (Qplus x (Qminus y x)) y) by ring.
  apply (proj1 (Qplus_le_r 0 (Qminus y x) x)).
  rewrite Hz. rewrite Qplus_0_r. exact H.
Qed.

(* Gap piece one: [0 <= u] gives [1 <= u + 1]. *)
Lemma cb2_qplus_one_gap : forall u : Q, Qle 0 u -> Qle 1 (Qplus u 1).
Proof.
  intros u H.
  assert (H1 : Qle (Qplus 0 1) (Qplus u 1)) by (apply Qplus_le_compat; [exact H | apply Qle_refl]).
  rewrite Qplus_0_l in H1. exact H1.
Qed.

(* Gap piece two: [u <= v] gives [1 <= v + 1 - u], the arithmetic core
   of the unit slack in the cap. *)
Lemma cb2_qminus_gap : forall u v : Q, Qle u v -> Qle 1 (Qminus (Qplus v 1) u).
Proof.
  intros u v Huv.
  apply (proj1 (Qplus_le_r 1 (Qminus (Qplus v 1) u) u)).
  assert (Hz : Qeq (Qplus u (Qminus (Qplus v 1) u)) (Qplus v 1)) by ring.
  rewrite Hz.
  apply Qplus_le_compat.
  - exact Huv.
  - apply Qle_refl.
Qed.

(* The two certificate constants: the least strict margins used by the
   computed smoke checks. *)
Lemma cb2_qhalf_lt_one : Qlt (1#2) 1.
Proof. reflexivity. Qed.

Lemma cb2_qhalf_pos : QltT 0 (1#2).
Proof. apply Qlt_to_QltT. reflexivity. Qed.

(* Transport of [Qeq] on the right argument of [Qlt], a term-level safe
   channel for arithmetic reshaping of the goal: rewriting by arithmetic
   [Qeq] inside a [Qlt]-headed goal is unreliable in this environment,
   so every such step goes through this transport. *)
Lemma cb2_qlt_eq_r : forall e a b : Q, Qlt e a -> Qeq a b -> Qlt e b.
Proof.
  intros e a b H Hq.
  exact (Qlt_le_trans e a b H
           (QleT'_to_Qle _ _ (qeq_le a b (qeq_imp_qeqT _ _ Hq)))).
Qed.

(* ============================================================ *)
(* Section 2. The dot machine, pointwise multiply-accumulate over finite
   lists in the concrete [Real] layer. *)
(* ============================================================ *)

Fixpoint cb2_dot (x y : list Real) : Real :=
  match x, y with
  | a :: xt, b :: yt => real_plus (real_mult a b) (cb2_dot xt yt)
  | _, _ => real_zero
  end.

(* Bridge by [req]: [cb2_dot] agrees with the [sumd] fold, reusing the
   existing summation machine rather than rebuilding it -- the bridge
   for the linearity and summation helpers. *)
Lemma cb2_dot_via_sumd : forall x y : list Real,
  real_eq (cb2_dot x y)
      (@sumd_list_sum (Real * Real)
         (fun p : Real * Real => mult (fst p) (snd p)) (combine x y)).
Proof.
  intros x y. revert y. induction x as [| a xt IH]; intro y.
  - destruct y as [| b yt].
    + exact (req_refl real_zero).
    + exact (req_refl real_zero).
  - destruct y as [| b yt].
    + exact (req_refl real_zero).
    + exact (req_plus_compat (real_mult a b) (mult (fst (a, b)) (snd (a, b)))
                (cb2_dot xt yt)
                (@sumd_list_sum (Real * Real)
                   (fun p : Real * Real => mult (fst p) (snd p)) (combine xt yt))
                (req_refl (real_mult a b))
                (IH yt)).
Defined.

(* Linearity helper: [cb2_dot] over a list scaled pointwise by [a] is
   [a] times the original dot (a [req] chain through [mult_assoc] and
   [distrib]). *)
Lemma cb2_dot_map_mult_l : forall (a : Real) (x y : list Real),
  real_eq (cb2_dot (map (fun r : Real => real_mult a r) x) y)
      (real_mult a (cb2_dot x y)).
Proof.
  intros a x. induction x as [| c xt IH]; intro y.
  - destruct y as [| b yt].
    + exact (req_sym _ _ (mult_zero a)).
    + exact (req_sym _ _ (mult_zero a)).
  - destruct y as [| b yt].
    + exact (req_sym _ _ (mult_zero a)).
    + exact (req_trans _ _ _
               (req_trans _ _ _
                  (req_plus_compat (real_mult (real_mult a c) b)
                     (real_mult a (real_mult c b))
                     (cb2_dot (map (fun r : Real => real_mult a r) xt) yt)
                     (real_mult a (cb2_dot xt yt))
                     (req_sym _ _ (mult_assoc a c b))
                     (IH yt))
                  (req_plus_compat (real_mult a (real_mult c b))
                     (real_mult a (real_mult c b))
                     (real_mult a (cb2_dot xt yt))
                     (real_mult a (cb2_dot xt yt))
                     (req_refl (real_mult a (real_mult c b)))
                     (req_refl (real_mult a (cb2_dot xt yt)))))
               (req_sym _ _ (distrib a (real_mult c b) (cb2_dot xt yt)))).
Defined.

(* Symmetry helper: [cb2_dot] is commutative. *)
Lemma cb2_dot_comm : forall x y : list Real, real_eq (cb2_dot x y) (cb2_dot y x).
Proof.
  intros x. induction x as [| a xt IH]; intro y.
  - destruct y as [| b yt].
    + exact (req_refl real_zero).
    + exact (req_refl real_zero).
  - destruct y as [| b yt].
    + exact (req_refl real_zero).
    + exact (req_plus_compat (real_mult a b) (real_mult b a)
                (cb2_dot xt yt) (cb2_dot yt xt)
                (mult_comm a b) (IH yt)).
Defined.

(* ============================================================ *)
(* Section 3. The max-cap machine, a [real_max] fold over a list of
   pairs; the core lemma is pure Q-layer induction. *)
(* ============================================================ *)

(* The cap fold: a default base [d] (an honest empty-list branch) with
   [real_max] of the per-pair absolute dot folded in. *)
Fixpoint cb2_list_max_abs (d : Real) (l : list (list Real * list Real)) : Real :=
  match l with
  | nil => d
  | (a, b) :: t => real_max (real_abs (cb2_dot a b)) (cb2_list_max_abs d t)
  end.

(* Core lemma: the elementwise value of the absolute dot at each index
   [n] is bounded by the fold at [n], by genuine Q-layer induction over
   the finite list.  The statement takes the pointwise [Qle] shape: the
   plain [real_le] shape is the same family as the AT5 disjunction wall
   (neither summand is constructible under the mixed signatures), and
   the pointwise or epsilon shapes are the sound route (the same
   philosophy as [csm_abs_sum_le_eps]). *)
Lemma cb2_dot_le_max : forall (l : list (list Real * list Real)) (x y : list Real) (n : nat),
  In (x, y) l ->
  Qle (Qabs (projT1 (cb2_dot x y) n)) (projT1 (cb2_list_max_abs real_zero l) n).
Proof.
  intro l. induction l as [| p t IH]; intros x y n Hin.
  - destruct Hin.
  - destruct p as [a b]. simpl in Hin. destruct Hin as [Heq | Hin].
    + injection Heq; intros; subst.
      cbn [cb2_list_max_abs].
      rewrite (qeqT_imp_qeq _ _ (real_max_proj _ _ _)).
      rewrite (qeqT_imp_qeq _ _ (real_abs_proj _ _)).
      apply cb2_qmax_ge_l.
    + cbn [cb2_list_max_abs].
      rewrite (qeqT_imp_qeq _ _ (real_max_proj _ _ _)).
      rewrite (qeqT_imp_qeq _ _ (real_abs_proj _ _)).
      apply (Qle_trans (Qabs (projT1 (cb2_dot x y) n))
                       (projT1 (cb2_list_max_abs real_zero t) n)).
      * apply IH. exact Hin.
      * apply cb2_qmax_ge_r.
Qed.

(* The fold is nonnegative: the [real_zero] base branch supplies the
   lower bound [0]. *)
Lemma cb2_maxabs_nonneg : forall (l : list (list Real * list Real)) (n : nat),
  Qle 0 (projT1 (cb2_list_max_abs real_zero l) n).
Proof.
  intro l. induction l as [| p t IH]; intro n.
  - cbn [cb2_list_max_abs].
    assert (Hz : projT1 real_zero n == 0%Q) by reflexivity.
    rewrite Hz. apply Qle_refl.
  - destruct p as [a b]. cbn [cb2_list_max_abs].
    rewrite (qeqT_imp_qeq _ _ (real_max_proj _ _ _)).
    rewrite (qeqT_imp_qeq _ _ (real_abs_proj _ _)).
    apply (Qle_trans 0 (Qabs (projT1 (cb2_dot a b) n))).
    + apply cb2_qabs_nonneg.
    + apply cb2_qmax_ge_l.
Qed.

(* The AT5-style strict strengthening: the absolute dot value is below
   fold + eps for every [eps] with [0 < eps]; the gap is supplied by the
   eps certificate margin. *)
Lemma cb2_dot_lt_max_eps : forall (l : list (list Real * list Real)) (x y : list Real),
  In (x, y) l -> forall eps : Real, real_lt real_zero eps ->
  real_lt (real_abs (cb2_dot x y))
          (real_plus (cb2_list_max_abs real_zero l) eps).
Proof.
  intros l x y Hin eps Heps.
  destruct Heps as [e0 [He0 [Neps HNeps]]].
  unfold real_lt. exists e0. split.
  - exact He0.
  - exists Neps. intros n Hn.
    specialize (HNeps n Hn).
    apply QltT_to_Qlt in HNeps.
    assert (Hz0 : projT1 real_zero n == 0%Q) by reflexivity.
    rewrite Hz0 in HNeps.
    assert (Hze : Qeq (projT1 eps n - 0) (projT1 eps n)) by ring.
    rewrite Hze in HNeps.
    assert (Hbd : Qle (Qabs (projT1 (cb2_dot x y) n))
                      (projT1 (cb2_list_max_abs real_zero l) n))
      by exact (cb2_dot_le_max l x y n Hin).
    assert (Hm0 : Qle 0 (Qminus (projT1 (cb2_list_max_abs real_zero l) n)
                                (Qabs (projT1 (cb2_dot x y) n))))
      by (apply (cb2_qle_minus (Qabs (projT1 (cb2_dot x y) n))
                  (projT1 (cb2_list_max_abs real_zero l) n) Hbd)).
    apply Qlt_to_QltT.
    rewrite (qeqT_imp_qeq _ _ (real_plus_proj _ _ _)).
    rewrite (qeqT_imp_qeq _ _ (real_abs_proj _ _)).
    (* Certificate chain: e0 < eps(n) <= eps(n) + (M - |d|), ring-equal
       to M + eps(n) - |d(n)|. *)
    assert (Hstep : Qle (projT1 eps n)
                        (Qplus (projT1 eps n)
                               (Qminus (projT1 (cb2_list_max_abs real_zero l) n)
                                  (Qabs (projT1 (cb2_dot x y) n)))))
      by exact (Qle_trans (projT1 eps n) (Qplus (projT1 eps n) 0)
                  (Qplus (projT1 eps n)
                     (Qminus (projT1 (cb2_list_max_abs real_zero l) n)
                        (Qabs (projT1 (cb2_dot x y) n))))
                  (QleT'_to_Qle _ _
                     (qeq_le (projT1 eps n) (Qplus (projT1 eps n) 0)
                        (qeq_imp_qeqT _ _
                           (Qeq_sym (Qplus (projT1 eps n) 0) (projT1 eps n)
                              (Qplus_0_r (projT1 eps n))))))
                  (proj2 (Qplus_le_r 0
                            (Qminus (projT1 (cb2_list_max_abs real_zero l) n)
                               (Qabs (projT1 (cb2_dot x y) n)))
                            (projT1 eps n)) Hm0)).
    assert (Hzg : Qeq (Qplus (projT1 eps n)
                          (Qminus (projT1 (cb2_list_max_abs real_zero l) n)
                             (Qabs (projT1 (cb2_dot x y) n))))
                      (projT1 (cb2_list_max_abs real_zero l) n + projT1 eps n
                       - Qabs (projT1 (cb2_dot x y) n))) by ring.
    exact (cb2_qlt_eq_r e0
             (Qplus (projT1 eps n)
                (Qminus (projT1 (cb2_list_max_abs real_zero l) n)
                   (Qabs (projT1 (cb2_dot x y) n))))
             (projT1 (cb2_list_max_abs real_zero l) n + projT1 eps n
              - Qabs (projT1 (cb2_dot x y) n))
             (Qlt_le_trans e0 (projT1 eps n)
                (Qplus (projT1 eps n)
                   (Qminus (projT1 (cb2_list_max_abs real_zero l) n)
                      (Qabs (projT1 (cb2_dot x y) n))))
                HNeps Hstep)
             Hzg).
Qed.

(* ============================================================ *)
(* Section 4. The concrete logit kernel (Section Cb2Kernel): the q/k
   vector families, the temperature, and the cap list. *)
(* ============================================================ *)

Section Cb2Kernel.

Variable S : Set.
Variable q : S -> list Real.
Variable k : S -> list Real.
Variable temp : Real.
Variable temp_pos : real_lt real_zero temp.
Variable lmax : list (list Real * list Real).

(* Kernel value: the concrete logit kernel equals temp multiplied by
   dot (q s) (k s'). *)
Definition cb2_z (s s' : S) : Real :=
  real_mult temp (cb2_dot (q s) (k s')).

(* The cap core in the original literal shape, temp multiplied by the
   max absolute dot.  The literal shape does not assemble into the gap:
   under the all-zero degenerate input its positivity certificate does
   not exist. *)
Definition cb2_Delta_core : Real :=
  real_mult temp (cb2_list_max_abs real_zero lmax).

(* The assembled gap adds the cap core and one unit of slack: the slack
   keeps gap(n) >= 1 at every index, so the three certificate lemmas
   supply the strict half by [inl]. *)
Definition cb2_Delta : Real :=
  real_plus cb2_Delta_core real_one.

(* ---- Positivity of the assembled gap, unconditionally; the
   certificate eps is [1#2] and N is the [N0] of [temp_pos]. ---- *)

Lemma cb2_Delta_pos : real_lt real_zero cb2_Delta.
Proof.
  destruct temp_pos as [e0 [He0 [N0 HN0]]].
  unfold real_lt. exists (1#2)%Q. split.
  - exact cb2_qhalf_pos.
  - exists N0. intros n Hn.
    specialize (HN0 n Hn).
    apply QltT_to_Qlt in HN0.
    assert (Hz0 : projT1 real_zero n == 0%Q) by reflexivity.
    rewrite Hz0 in HN0.
    assert (Hzn : Qeq (projT1 temp n - 0) (projT1 temp n)) by ring.
    rewrite Hzn in HN0.
    assert (Htn0 : Qle 0 (projT1 temp n)).
    { apply (Qle_trans 0 e0 (projT1 temp n)).
      - apply Qlt_le_weak. exact (QltT_to_Qlt 0 e0 He0).
      - exact (Qlt_le_weak e0 (projT1 temp n) HN0). }
    assert (HM0 : Qle 0 (projT1 (cb2_list_max_abs real_zero lmax) n))
      by exact (cb2_maxabs_nonneg lmax n).
    assert (HX : Qle 0 (projT1 temp n * projT1 (cb2_list_max_abs real_zero lmax) n))
      by (apply cb2_qmul_nonneg; assumption).
    apply Qlt_to_QltT.
    unfold cb2_Delta, cb2_Delta_core.
    rewrite (qeqT_imp_qeq _ _ (real_plus_proj _ _ _)).
    rewrite !(qeqT_imp_qeq _ _ (real_mult_proj _ _ _)).
    assert (H1 : projT1 real_one n == 1%Q) by reflexivity.
    rewrite H1.
    change (projT1 real_zero n) with 0%Q.
    assert (Hzg : Qeq (projT1 temp n * projT1 (cb2_list_max_abs real_zero lmax) n + 1)
                      (projT1 temp n * projT1 (cb2_list_max_abs real_zero lmax) n
                       + 1 - 0)) by ring.
    exact (cb2_qlt_eq_r (1#2)%Q
             (projT1 temp n * projT1 (cb2_list_max_abs real_zero lmax) n + 1)
             (projT1 temp n * projT1 (cb2_list_max_abs real_zero lmax) n + 1 - 0)
             (Qlt_le_trans (1#2)%Q 1%Q
                (projT1 temp n * projT1 (cb2_list_max_abs real_zero lmax) n + 1)
                cb2_qhalf_lt_one
                (cb2_qplus_one_gap
                   (projT1 temp n * projT1 (cb2_list_max_abs real_zero lmax) n) HX))
             Hzg).
Qed.

(* ---- Lower bound on z: the negated gap is a lower bound of
   temp * dot, in the [In] form; the cap list must contain the pair. ---- *)

Lemma cb2_z_lb : forall s s' : S,
  In (q s, k s') lmax -> real_le (real_opp cb2_Delta) (cb2_z s s').
Proof.
  intros s s' Hin.
  destruct temp_pos as [e0 [He0 [N0 HN0]]].
  apply inl. unfold real_lt. exists (1#2)%Q. split.
  - exact cb2_qhalf_pos.
  - exists N0. intros n Hn.
    specialize (HN0 n Hn).
    apply QltT_to_Qlt in HN0.
    assert (Hz0 : projT1 real_zero n == 0%Q) by reflexivity.
    rewrite Hz0 in HN0.
    assert (Hzn : Qeq (projT1 temp n - 0) (projT1 temp n)) by ring.
    rewrite Hzn in HN0.
    assert (Htn0 : Qle 0 (projT1 temp n)).
    { apply (Qle_trans 0 e0 (projT1 temp n)).
      - apply Qlt_le_weak. exact (QltT_to_Qlt 0 e0 He0).
      - exact (Qlt_le_weak e0 (projT1 temp n) HN0). }
    assert (Hbd : Qle (Qabs (projT1 (cb2_dot (q s) (k s')) n))
                      (projT1 (cb2_list_max_abs real_zero lmax) n))
      by exact (cb2_dot_le_max lmax (q s) (k s') n Hin).
    assert (Hdn_ge : Qle (Qopp (Qabs (projT1 (cb2_dot (q s) (k s')) n)))
                         (projT1 (cb2_dot (q s) (k s')) n))
      by exact (cb2_qopp_abs_le (projT1 (cb2_dot (q s) (k s')) n)).
    assert (Hu : Qle (projT1 temp n
                        * Qopp (Qabs (projT1 (cb2_dot (q s) (k s')) n)))
                     (projT1 temp n * projT1 (cb2_dot (q s) (k s')) n))
      by (apply cb2_qmul_nonneg_r; [exact Htn0 | exact Hdn_ge]).
    assert (Hw : Qle 0 (projT1 temp n
                          * Qminus (projT1 (cb2_list_max_abs real_zero lmax) n)
                              (Qabs (projT1 (cb2_dot (q s) (k s')) n))))
      by (apply cb2_qmul_nonneg; [exact Htn0 | exact (cb2_qle_minus _ _ Hbd)]).
    apply Qlt_to_QltT.
    unfold cb2_z, cb2_Delta, cb2_Delta_core.
    rewrite (qeqT_imp_qeq _ _ (real_opp_proj _ _)).
    rewrite (qeqT_imp_qeq _ _ (real_plus_proj _ _ _)).
    rewrite !(qeqT_imp_qeq _ _ (real_mult_proj _ _ _)).
    assert (H1 : projT1 real_one n == 1%Q) by reflexivity.
    rewrite H1.
    (* Reshape [Hw] into the left summand of the goal:
       tn * (M - |d|) == tn * (- |d|) + tn * M. *)
    assert (Hzr : Qeq (projT1 temp n
                         * Qminus (projT1 (cb2_list_max_abs real_zero lmax) n)
                             (Qabs (projT1 (cb2_dot (q s) (k s')) n)))
                      (projT1 temp n * Qopp (Qabs (projT1 (cb2_dot (q s) (k s')) n))
                       + projT1 temp n * projT1 (cb2_list_max_abs real_zero lmax) n))
      by ring.
    assert (HX : Qle 0 (projT1 temp n
                          * Qopp (Qabs (projT1 (cb2_dot (q s) (k s')) n))
                        + projT1 temp n * projT1 (cb2_list_max_abs real_zero lmax) n)).
    { rewrite <- Hzr. exact Hw. }
    assert (HY : Qle (projT1 temp n * Qopp (Qabs (projT1 (cb2_dot (q s) (k s')) n))
                       + projT1 temp n * projT1 (cb2_list_max_abs real_zero lmax) n)
                     (projT1 temp n * projT1 (cb2_dot (q s) (k s')) n
                       + projT1 temp n * projT1 (cb2_list_max_abs real_zero lmax) n))
      by (apply Qplus_le_compat; [exact Hu | apply Qle_refl]).
    assert (Htot : Qle 0 (projT1 temp n * projT1 (cb2_dot (q s) (k s')) n
                           + projT1 temp n * projT1 (cb2_list_max_abs real_zero lmax) n))
      by exact (Qle_trans _ _ _ HX HY).
    (* gap = tn * dn - (-(tn * M + 1)) == tn * dn + tn * M + 1 >= 1
       > 1#2. *)
    assert (Hzg : Qeq (projT1 temp n * projT1 (cb2_dot (q s) (k s')) n
                       + projT1 temp n * projT1 (cb2_list_max_abs real_zero lmax) n + 1)
                      (projT1 temp n * projT1 (cb2_dot (q s) (k s')) n
                       - Qopp (projT1 temp n
                                 * projT1 (cb2_list_max_abs real_zero lmax) n + 1)))
      by ring.
    exact (cb2_qlt_eq_r (1#2)%Q
             (projT1 temp n * projT1 (cb2_dot (q s) (k s')) n
              + projT1 temp n * projT1 (cb2_list_max_abs real_zero lmax) n + 1)
             (projT1 temp n * projT1 (cb2_dot (q s) (k s')) n
              - Qopp (projT1 temp n
                        * projT1 (cb2_list_max_abs real_zero lmax) n + 1))
             (Qlt_le_trans (1#2)%Q 1%Q
                (projT1 temp n * projT1 (cb2_dot (q s) (k s')) n
                 + projT1 temp n * projT1 (cb2_list_max_abs real_zero lmax) n + 1)
                cb2_qhalf_lt_one (cb2_qplus_one_gap _ Htot))
             Hzg).
Qed.

(* ---- Upper bound on z: temp * dot is bounded by the gap, in the
   [In] form. ---- *)

Lemma cb2_z_ub : forall s s' : S,
  In (q s, k s') lmax -> real_le (cb2_z s s') cb2_Delta.
Proof.
  intros s s' Hin.
  destruct temp_pos as [e0 [He0 [N0 HN0]]].
  apply inl. unfold real_lt. exists (1#2)%Q. split.
  - exact cb2_qhalf_pos.
  - exists N0. intros n Hn.
    specialize (HN0 n Hn).
    apply QltT_to_Qlt in HN0.
    assert (Hz0 : projT1 real_zero n == 0%Q) by reflexivity.
    rewrite Hz0 in HN0.
    assert (Hzn : Qeq (projT1 temp n - 0) (projT1 temp n)) by ring.
    rewrite Hzn in HN0.
    assert (Htn0 : Qle 0 (projT1 temp n)).
    { apply (Qle_trans 0 e0 (projT1 temp n)).
      - apply Qlt_le_weak. exact (QltT_to_Qlt 0 e0 He0).
      - exact (Qlt_le_weak e0 (projT1 temp n) HN0). }
    assert (Hbd : Qle (Qabs (projT1 (cb2_dot (q s) (k s')) n))
                      (projT1 (cb2_list_max_abs real_zero lmax) n))
      by exact (cb2_dot_le_max lmax (q s) (k s') n Hin).
    assert (Huv : Qle (projT1 temp n * projT1 (cb2_dot (q s) (k s')) n)
                      (projT1 temp n * projT1 (cb2_list_max_abs real_zero lmax) n)).
    { apply cb2_qmul_nonneg_r.
      - exact Htn0.
      - apply (Qle_trans (projT1 (cb2_dot (q s) (k s')) n)
                         (Qabs (projT1 (cb2_dot (q s) (k s')) n))).
        + apply cb2_qabs_ge.
        + exact Hbd. }
    apply Qlt_to_QltT.
    unfold cb2_z, cb2_Delta, cb2_Delta_core.
    rewrite (qeqT_imp_qeq _ _ (real_plus_proj _ _ _)).
    rewrite !(qeqT_imp_qeq _ _ (real_mult_proj _ _ _)).
    assert (H1 : projT1 real_one n == 1%Q) by reflexivity.
    rewrite H1.
    (* gap = (tn * M + 1) - tn * dn >= 1, by [cb2_qminus_gap] with [Huv]
       as the cap premise. *)
    exact (Qlt_le_trans (1#2)%Q 1%Q
             (Qminus (Qplus (projT1 temp n * projT1 (cb2_list_max_abs real_zero lmax) n) 1)
                (projT1 temp n * projT1 (cb2_dot (q s) (k s')) n))
             cb2_qhalf_lt_one
             (cb2_qminus_gap (projT1 temp n * projT1 (cb2_dot (q s) (k s')) n)
                             (projT1 temp n * projT1 (cb2_list_max_abs real_zero lmax) n)
                             Huv)).
Qed.

(* ---- Direct substitution at the argument slots: the completeness
   certificate removes [In]; the statements transpose the closing chain
   of [cb2_z_lb] and [cb2_z_ub] verbatim. ---- *)

Variable lmax_complete : forall s s' : S, In (q s, k s') lmax.

Lemma cb2_z_lb_all : forall s s' : S, real_le (real_opp cb2_Delta) (cb2_z s s').
Proof. intros s s'. apply cb2_z_lb. apply lmax_complete. Qed.

Lemma cb2_z_ub_all : forall s s' : S, real_le (cb2_z s s') cb2_Delta.
Proof. intros s s'. apply cb2_z_ub. apply lmax_complete. Qed.

End Cb2Kernel.

(* ============================================================ *)
(* Section 5. Computed smoke checks on the degenerate all-zero input,
   closed by computation alone. *)
(* ============================================================ *)

Section Cb2Smoke.

Definition cb2_smoke_q : unit -> list Real := fun _ => real_zero :: nil.
Definition cb2_smoke_k : unit -> list Real := fun _ => real_zero :: nil.
Definition cb2_smoke_lmax : list (list Real * list Real) :=
  (real_zero :: nil, real_zero :: nil) :: nil.

(* Dot smoke check: the all-zero one-dimensional dot reduces to [0] at
   the probed index; [reflexivity] computes it. *)
Lemma cb2_smoke_dot : projT1 (cb2_dot (real_zero :: nil) (real_zero :: nil)) 5%nat == 0%Q.
Proof. reflexivity. Qed.

(* Kernel smoke check: z(5) = 1 * (0 * 0 + 0) = 0. *)
Lemma cb2_smoke_z : projT1 (cb2_z unit cb2_smoke_q cb2_smoke_k real_one tt tt) 5%nat == 0%Q.
Proof. reflexivity. Qed.

(* Cap fold smoke check: max|dot|(5) = Qmax |0| 0 = 0 and
   Delta(5) = 1 * 0 + 1 = 1. *)
Lemma cb2_smoke_max : projT1 (cb2_list_max_abs real_zero cb2_smoke_lmax) 5%nat == 0%Q.
Proof. reflexivity. Qed.

Lemma cb2_smoke_Delta : projT1 (cb2_Delta real_one cb2_smoke_lmax) 5%nat == 1%Q.
Proof. reflexivity. Qed.

(* Certificate smoke check: the gap of the z bound at index 5 is
   1 - 0 = 1, and its being strictly above [1#2] is decided by
   computation. *)
Lemma cb2_smoke_gap : QltT (1#2)%Q
   (projT1 (cb2_Delta real_one cb2_smoke_lmax) 5%nat
   - projT1 (cb2_z unit cb2_smoke_q cb2_smoke_k real_one tt tt) 5%nat).
Proof. reflexivity. Qed.

Lemma cb2_smoke_complete : forall s s' : unit,
  In (cb2_smoke_q s, cb2_smoke_k s') cb2_smoke_lmax.
Proof. intros s s'. apply in_eq. Qed.

(* The degenerate-branch certificate as one closed term: [cb2_z_ub_all]
   fully applied on the all-zero input. *)
Definition cb2_smoke_ub_cert :
  real_le (cb2_z unit cb2_smoke_q cb2_smoke_k real_one tt tt)
          (cb2_Delta real_one cb2_smoke_lmax) :=
  cb2_z_ub_all unit cb2_smoke_q cb2_smoke_k real_one one_pos
               cb2_smoke_lmax cb2_smoke_complete tt tt.

End Cb2Smoke.

(* ============ Evidence: the statements above rely on no unproved
   external assumption; all are closed under the global context, with
   premises carried as explicit arguments ============ *)
Print Assumptions cb2_dot_via_sumd.
Print Assumptions cb2_dot_map_mult_l.
Print Assumptions cb2_dot_comm.
Print Assumptions cb2_dot_le_max.
Print Assumptions cb2_maxabs_nonneg.
Print Assumptions cb2_dot_lt_max_eps.
Print Assumptions cb2_Delta_pos.
Print Assumptions cb2_z_lb.
Print Assumptions cb2_z_ub.
Print Assumptions cb2_z_lb_all.
Print Assumptions cb2_z_ub_all.
Print Assumptions cb2_smoke_ub_cert.

(* ======== Further evidence: assumption audit of the remaining
   Q-layer helpers and smoke checks ======== *)
Print Assumptions cb2_qmul_nonneg_r.
Print Assumptions cb2_qhalf_lt_one.
Print Assumptions cb2_qhalf_pos.
Print Assumptions cb2_qlt_eq_r.
Print Assumptions cb2_z_lb_all.
Print Assumptions cb2_z_ub_all.
Print Assumptions cb2_smoke_dot.
Print Assumptions cb2_smoke_z.
Print Assumptions cb2_smoke_max.
Print Assumptions cb2_smoke_Delta.
Print Assumptions cb2_smoke_gap.
Print Assumptions cb2_smoke_complete.
