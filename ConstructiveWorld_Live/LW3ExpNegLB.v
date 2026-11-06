(* ConstructiveWorld-Set -- explicit rational bounds for the constructive real exponential. *)

(** * LW3ExpNegLB: explicit positive rational lower bounds for e^(-node).

    Mission.  For every natural point [node] this file constructs an
      explicit positive rational lower bound of the real exponential
      value [cauchy_real_exp (real_const (- lw2_node node))]: with the
      uniform exp series bound [C] from [exp_series_arch] and the tail
      decay witness [m0] from [exp_partial_tail_small], the pointwise
      uniform bound 1/(2*C) yields [r := 1/(4*C)] with [QltT 0 r] and
      [real_lt (real_const r) e^(-node)] in data form.  Main statement:
      [tlw401_expneg_pos_lb], with bridges [tlw401_proj_const],
      [tlw401_proj_exp] and the even/odd split [tlw401_parity].

    Dependencies.  Stdlib [QArith], [Lia], [Arith], [ZArith], [List],
      [QArith_base], [QArith.Qabs].  Requires [S01_BaseRing],
      [S02_CauchyComplete], [S03_QExp], [LW0QPoly], [LW2Hermite] of
      this development.

    References.  This development, LW3ExpNegLB.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" LW3ExpNegLB.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 00015ff4]. *)

Require Import QArith Lia Arith ZArith List.
From Stdlib Require Import QArith_base.
From Stdlib Require Import QArith.Qabs.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import LW0QPoly.
Require Import LW2Hermite.

Local Open Scope Q_scope.

(* ============================================================ *)
(* Bridge 0.  Pointwise projections of constant reals and of the       *)
(* rational-point real exponential (both proved by reflexivity).       *)
(* ============================================================ *)

Lemma tlw401_proj_const : forall (c : Q) (n : nat),
  projT1 (real_const c) n == c.
Proof. intros c n. unfold real_const. reflexivity. Qed.

Lemma tlw401_proj_exp : forall (X : Q) (n : nat),
  projT1 (cauchy_real_exp (real_const X)) n == exp_partial n X.
Proof. intros X n. unfold cauchy_real_exp, real_const. reflexivity. Qed.

(* ============================================================ *)
(* Bridge 1.  Even/odd decomposition of a natural number (pure Set     *)
(* data form: a sum of sigT witnesses, no Prop on the statement face). *)
(* ============================================================ *)

Lemma tlw401_parity : forall n : nat,
  sigT (fun m : nat => (n = 2 * m)%nat) +
  sigT (fun m : nat => (n = Datatypes.S (2 * m))%nat).
Proof.
  induction n as [| n IH].
  - left. exists 0%nat. reflexivity.
  - destruct IH as [[m Hm] | [m Hm]].
    + right. exists m. rewrite Hm. lia.
    + left. exists (Datatypes.S m). rewrite Hm. lia.
Qed.

(* ============================================================ *)
(* Main statement: an explicit positive rational lower bound of        *)
(* e^(-node) (the eps-slot supply form).                               *)
(*   Construction: a := node (the transparent embedding lw2_node),     *)
(*   C := the uniform exp series bound (exp_series_arch), m0 := the    *)
(*   tail decay witness (exp_partial_tail_small); the pointwise        *)
(*   uniform lower bound 1/(2*C) (even branch 1/C <= S_{2*m}, odd      *)
(*   branch 1/(2*C) < S_{2*m+1}); with r := 1/(4*C), 0 < r and 2*r     *)
(*   below the pointwise truncation give real_lt (real_const r)        *)
(*   e^(-a).                                                           *)
(* ============================================================ *)

Theorem tlw401_expneg_pos_lb : forall (node : nat),
  sigT (fun r : Q =>
    And (QltT 0 r)
        (real_lt (real_const r)
           (cauchy_real_exp (real_const (- lw2_node node))))).
Proof.
  intros node.
  set (a := lw2_node node).
  (* (1) The node point is nonnegative: direct Z-level construction, via *)
  (*     Zmult_1_r and Zle_0_nat. *)
  assert (Ha0 : QleT' 0 a).
  { unfold a, lw2_node. apply Qle_to_QleT'.
    unfold Qle. cbn [Qnum Qden].
    rewrite !Zmult_1_r. apply Zle_0_nat. }
  (* (2) The uniform bound C and the tail decay witness m0, supplied     *)
  (*     directly by the two sigT statements of S03. *)
  destruct (exp_series_arch a Ha0) as [C [HC1 HCs]].
  destruct (exp_partial_tail_small a C Ha0 HC1) as [m0 Hm0].
  assert (HCpos : Qlt 0 C).
  { apply (Qlt_le_trans 0 1 C).
    - unfold Qlt. simpl. lia.
    - apply QleT'_to_Qle. exact HC1. }
  assert (Hz2C : Qlt 0 (2 * C)).
  { apply (Qmult_lt_0_compat 2 C).
    - unfold Qlt. simpl. lia.
    - exact HCpos. }
  assert (Hz4C : Qlt 0 (4 * C)).
  { apply (Qmult_lt_0_compat 4 C).
    - unfold Qlt. simpl. lia.
    - exact HCpos. }
  (* (3) The explicit bound r := 1/(4*C) and the half-step strict        *)
  (*     bridge (multiplying through by (2*C)/(4*C) on the field side). *)
  assert (Hrpos : QltT 0 (1 / (4 * C))).
  { apply Qlt_to_QltT. unfold Qdiv.
    apply (Qmult_lt_0_compat 1 (Qinv (4 * C))).
    - unfold Qlt. simpl. lia.
    - apply Qinv_lt_0_compat. exact Hz4C. }
  assert (Hhalf : Qlt (1 / (2 * C)) (1 / C)).
  { apply (Qlt_shift_div_r 1 (2 * C) (1 / C) Hz2C).
    assert (E2 : (1 / C) * (2 * C) == 2%Q).
    { unfold Qdiv. field. intro Hz0.
      destruct (q_neq_of_lt C (Qlt_to_QltT 0 C HCpos)
                  (qeq_imp_qeqT _ _ Hz0)). }
    rewrite E2. unfold Qlt. reflexivity. }
  assert (Hhalf2 : Qlt (1 / (4 * C)) (1 / (2 * C))).
  { apply (Qlt_shift_div_r 1 (4 * C) (1 / (2 * C)) Hz4C).
    assert (E2 : (1 / (2 * C)) * (4 * C) == 2%Q).
    { unfold Qdiv. field. intro Hz0.
      destruct (q_neq_of_lt C (Qlt_to_QltT 0 C HCpos)
                  (qeq_imp_qeqT _ _ Hz0)). }
    rewrite E2. unfold Qlt. reflexivity. }
  (* (4) The carrier slot for |(-a)| <= a: the two steps Qabs_opp and    *)
  (*     Qabs_pos. *)
  assert (Hy : QleT' (Qabs (- a)) a).
  { apply Qle_to_QleT'.
    apply (Qle_trans (Qabs (- a)) (Qabs a) a).
    - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
      apply Qabs_opp.
    - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
      apply Qabs_pos. apply QleT'_to_Qle. exact Ha0. }
  (* (5) The pointwise uniform lower bound: n >= 2*m0 implies            *)
  (*     1/(2*C) < S_n(-a), with the even and odd branches merged. *)
  assert (Hlow : forall n : nat, NatLe (2 * m0) n ->
            QltT (1 / (2 * C)) (exp_partial n (- a))).
  { intros n Hn. apply NatLe_drop in Hn.
    destruct (tlw401_parity n) as [[m Hm] | [m Hm]].
    - subst n. assert (Hge : (m0 <= m)%nat) by lia.
      apply Qlt_to_QltT.
      apply (Qlt_le_trans (1 / (2 * C)) (1 / C) (exp_partial (2 * m) (- a)) Hhalf).
      apply QleT'_to_Qle.
      exact (exp_partial_even_lower a C (- a) m Ha0 HC1 HCs Hy).
    - subst n. assert (Hge : (m0 <= m)%nat) by lia.
      replace (Datatypes.S (2 * m)) with (2 * m + 1)%nat by lia.
      exact (exp_partial_odd_lower a C m0 m (- a) Ha0 HC1 HCs Hm0 Hge Hy). }
  (* (6) Assembling the exit: unfold the real_lt definition; the exit    *)
  (*     difference is rewritten into the form e^(-a) - r through the    *)
  (*     Hdiff bridge and qltT_eq_compat_r; the strict half-step         *)
  (*     difference 2*r = 1/(2*C) closes the goal. *)
  exists (1 / (4 * C))%Q.
  split.
  - exact Hrpos.
  - exists (1 / (4 * C))%Q.
    split.
    + exact Hrpos.
    + exists (2 * m0)%nat. intros n Hn.
      assert (Hdiff : projT1 (cauchy_real_exp (real_const (- a))) n -
                      projT1 (real_const (1 / (4 * C))) n ==
                      exp_partial n (- a) - 1 / (4 * C)).
      { rewrite (tlw401_proj_exp (- a) n), (tlw401_proj_const (1 / (4 * C)) n).
        reflexivity. }
      apply (qltT_eq_compat_r
               (projT1 (cauchy_real_exp (real_const (- a))) n -
                projT1 (real_const (1 / (4 * C))) n)
               (exp_partial n (- a) - 1 / (4 * C)) (1 / (4 * C))
               (qeq_imp_qeqT _ _ Hdiff)).
      apply Qlt_to_QltT.
      apply (proj1 (Qplus_lt_r (1 / (4 * C))
                               (exp_partial n (- a) - 1 / (4 * C))
                               (1 / (4 * C)))).
      assert (Hback : 1 / (4 * C) + (exp_partial n (- a) - 1 / (4 * C))
                      == exp_partial n (- a)) by ring.
      rewrite Hback.
      assert (Hrr : 1 / (4 * C) + 1 / (4 * C) == 1 / (2 * C)).
      { field.
        all: try (intro Hz0;
             destruct (q_neq_of_lt (4 * C) (Qlt_to_QltT 0 (4 * C) Hz4C)
                         (qeq_imp_qeqT _ _ Hz0))).
        all: try (intro Hz0;
             destruct (q_neq_of_lt (2 * C) (Qlt_to_QltT 0 (2 * C) Hz2C)
                         (qeq_imp_qeqT _ _ Hz0))).
        all: try (intro Hz0;
             destruct (q_neq_of_lt C (Qlt_to_QltT 0 C HCpos)
                         (qeq_imp_qeqT _ _ Hz0))). }
      rewrite Hrr.
      apply QltT_to_Qlt. apply Hlow. exact Hn.
Qed.

Print Assumptions tlw401_expneg_pos_lb.
Print Assumptions tlw401_parity.

(* Extraction: Separate Extraction on [tlw401_parity] keeps only the   *)
(* numeric data: the nat witness [m] of each disjunct survives, and    *)
(* the equality components [n = 2*m] and [n = S (2*m)] are logical     *)
(* and are erased.  The extracted term is the structural parity        *)
(* recursion on [nat] with [Obj.magic] = 0; the output lands in        *)
(* LW3ExpNegLB.ml.                                                     *)
Separate Extraction tlw401_parity.
