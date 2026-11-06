(* ConstructiveWorld-Set -- E-slot family: rational truncations of e^X, uniform tail bounds, real_lt exits. *)

(** * LW3ESlot: tail bounds and the real_lt exit for the rational truncation of e^X.

    Mission.  First E-slot loading piece on the M3 Real half, the weighted
      and redesign segments untouched: the depth-[N] rational truncation
      [tlw383_EQ] of e^X by exponential partial sums, the uniform tail
      bound [tlw383_geom_bound] := (|X|^N / N!) * 2, the pointwise and
      geometric bounds [tlw383_eslot_pointwise] and [tlw383_eslot_geom],
      the [real_lt] exit [tlw383_eslot_real_lt], the explicit-premise
      assemblies [tlw383_eslot_carrier] and [tlw383_eslot_realcarrier],
      the scalar Lipschitz machine [tlw383_eslot_machine_lip], and the
      anchor pins [tlw383_eslot_anchor] and [tlw383_eslot_anchor_lt].

    Dependencies.  Stdlib [QArith], [Lia], [Arith], [ZArith], [List],
      [QArith_base], [QArith.Qabs]; of this development: [S01_BaseRing],
      [S02_CauchyComplete], [S03_QExp], [LW0QPoly], [LW1ZPoly],
      [LW0FactGrowth], [LW2Hermite], [LW2IntegMachine], [LW3ETranscendental].

    References.  This development, LW3ESlot.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" LW3ESlot.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 00015ff4]. *)
Require Import QArith Lia Arith ZArith List.
From Stdlib Require Import QArith_base.
From Stdlib Require Import QArith.Qabs.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import LW0QPoly.
Require Import LW1ZPoly.
Require Import LW0FactGrowth.
Require Import LW2Hermite.
Require Import LW2IntegMachine.
Require Import LW3ETranscendental.

(* ===== 1. absolute-value product identity at the Q layer, direct from Z.abs_mul ===== *)

Lemma tlw383_qabs_mult : forall x y : Q, Qabs (x * y) == Qabs x * Qabs y.
Proof.
  intros [xn xd] [yn yd].
  unfold Qabs, Qmult, Qeq. cbn [Qnum Qden].
  rewrite Z.abs_mul. reflexivity.
Qed.

(* ===== 2. the E_Q truncation supply form and the uniform tail bound form ===== *)

(* the depth-N rational truncation of e^X, the E_Q supply form of the E-slot: an exponential partial sum. *)
Definition tlw383_EQ (X : Q) (N : nat) : Q := exp_partial N X.

(* the depth-N uniform tail bound B_N := (|X|^N / N!) * 2, the geometric-series closure form. *)
Definition tlw383_geom_bound (X : Q) (N : nat) : Q :=
  (q_pow (Qabs X) N / q_fact N) * (1 + 1)%Q.

(* ===== 3. pointwise projection bridges: the computational face of the Defined-transparent constructions ===== *)

(* sequence projection of the constant real: projT1 (real_const c) n == c. *)
Lemma tlw383_realconst_proj : forall (c : Q) (n : nat),
  projT1 (real_const c) n == c.
Proof. intros c n. unfold real_const. reflexivity. Qed.

(* pointwise sequence of the real exponential at a rational point: exp_partial n X. *)
Lemma tlw383_realexp_const_proj : forall (X : Q) (n : nat),
  projT1 (cauchy_real_exp (real_const X)) n == exp_partial n X.
Proof. intros X n. unfold cauchy_real_exp, real_const. reflexivity. Qed.

(* ===== 4. pointwise tail bound of the E-slot ===== *)

(* at n >= N, |e_X(n) - E_Q| <= exp_tail_abs N n |X|: the difference
   identity (exp_partial_diff_tail) and the triangle bound (exp_tail_abs_le)
   apply directly; the assembly runs through an explicit lemma chain with
   one Qeq_trans conversion step and no Qeq rewriting. *)
Lemma tlw383_eslot_pointwise : forall (X : Q) (N n : nat), (N <= n)%nat ->
  QleT' (Qabs (projT1 (cauchy_real_exp (real_const X)) n - tlw383_EQ X N))
        (exp_tail_abs N n (Qabs X)).
Proof.
  intros X N n Hn.
  apply Qle_to_QleT'.
  apply (Qle_trans
           (Qabs (projT1 (cauchy_real_exp (real_const X)) n - tlw383_EQ X N))
           (Qabs (exp_tail N n X))
           (exp_tail_abs N n (Qabs X))).
  - apply QleT'_to_Qle. apply qeq_le.
    apply qeq_imp_qeqT. apply (Qabs_wd _ _).
    apply (Qeq_trans _ (exp_partial n X - exp_partial N X) _).
    + reflexivity.
    + exact (qeqT_imp_qeq _ _ (exp_partial_diff_tail N n X Hn)).
  - apply QleT'_to_Qle. apply exp_tail_abs_le.
Qed.

(* ===== 5. geometric composition ===== *)

(* for 2|X| <= N+1 the uniform bound B_N dominates the pointwise tail
   (exp_tail_abs_geom2 directly); the geometric premise travels
   monotonically along t >= N. *)
Lemma tlw383_eslot_geom : forall (X : Q) (N n : nat),
  QleT' (2 * Qabs X) (lw0_q_of_nat (N + 1)) ->
  (N <= n)%nat ->
  QleT' (Qabs (projT1 (cauchy_real_exp (real_const X)) n - tlw383_EQ X N))
        (tlw383_geom_bound X N).
Proof.
  intros X N n Hgeo Hn.
  apply (qleT'_trans
           (Qabs (projT1 (cauchy_real_exp (real_const X)) n - tlw383_EQ X N))
           (exp_tail_abs N n (Qabs X))
           (tlw383_geom_bound X N)).
  - apply tlw383_eslot_pointwise. exact Hn.
  - apply (exp_tail_abs_geom2 (Qabs X) N n).
    + exact (qabs_nonnegT X).
    + intros t Ht.
      apply NatLe_drop in Ht.
      apply (qleT'_trans (Qmult (1 + 1)%Q (Qabs X))
                       (lw0_q_of_nat (N + 1)) ((Z.of_nat (t + 1) # 1))).
      * exact Hgeo.
      * apply Qle_to_QleT'. unfold lw0_q_of_nat. unfold Qle. cbn [Qnum Qden].
        rewrite Z.mul_1_r. rewrite Z.mul_1_r. lia.
    + exact Hn.
Qed.

(* ===== 6. the real_lt face of the E-slot bridge: the face used at apartness exits ===== *)

(* given the slack B_N < eps, the real distance between the real
   exponential and the truncation constant is < eps.  the
   real_lt / real_metric / real_const pattern is the same exit shape as
   lw3_e_trans_exit; the inner precision piece is delta := (eps - B_N)/2
   and the half-strict closure runs through qltT_half_lt_selfT. *)
Theorem tlw383_eslot_real_lt : forall (X : Q) (N : nat) (eps : Q),
  QleT' (2 * Qabs X) (lw0_q_of_nat (N + 1)) ->
  QltT (tlw383_geom_bound X N) eps ->
  real_lt (real_metric (cauchy_real_exp (real_const X))
                        (real_const (tlw383_EQ X N)))
          (real_const eps).
Proof.
  intros X N eps Hgeo Hslack.
  assert (HBpos : QleT' 0 (tlw383_geom_bound X N)).
  { apply (qleT'_trans 0 (0 * (1 + 1)%Q) (tlw383_geom_bound X N)).
    - apply qeq_leT'. reflexivity.
    - apply (qleT'_trans (0 * (1 + 1)%Q)
               ((q_pow (Qabs X) N / q_fact N) * (1 + 1)%Q)
               (tlw383_geom_bound X N)).
      + apply qleT'_mult_compat_r.
        * unfold QleT'. vm_compute. reflexivity.
        * exact (q_pow_fact_nonneg (Qabs X) N (qabs_nonnegT X)).
      + apply qleT'_refl. }
  assert (HltB : Qlt (tlw383_geom_bound X N) eps)
    by (apply QltT_to_Qlt; exact Hslack).
  assert (Heps0 : Qlt 0 eps)
    by (apply (Qle_lt_trans 0 (tlw383_geom_bound X N) eps);
        [exact (QleT'_to_Qle _ _ HBpos) | exact HltB]).
  (* strict positivity of the difference QltT 0 (eps - B_N): plus-compatibility closed by a two-sided qeq step, all lemmas from the library. *)
  assert (HdB0T : QltT 0 (eps - tlw383_geom_bound X N)).
  { assert (H : QltT (tlw383_geom_bound X N + - (tlw383_geom_bound X N))
                     (eps + - (tlw383_geom_bound X N))).
    { apply (qltT_plus_leT'_ltT (tlw383_geom_bound X N) eps
               (- (tlw383_geom_bound X N)) (- (tlw383_geom_bound X N))).
      - exact Hslack.
      - apply qleT'_refl. }
    assert (H2 : QltT 0 (eps + - (tlw383_geom_bound X N))).
    { apply (qltT_eq_compat_l (tlw383_geom_bound X N + - (tlw383_geom_bound X N))
               0 (eps + - (tlw383_geom_bound X N))).
      - apply qeq_imp_qeqT. ring.
      - exact H. }
    apply (qltT_eq_compat_r (eps + - (tlw383_geom_bound X N))
             (eps - tlw383_geom_bound X N) 0).
    - apply qeq_imp_qeqT. ring.
    - exact H2. }
  exists (((eps - tlw383_geom_bound X N) / 2)%Q). split.
  - apply (qltT_div_pos (eps - tlw383_geom_bound X N) 2).
    + exact HdB0T.
    + exact qltT_0_2.
  - exists N. intros n HnN.
    (* the pointwise bound: the difference at n is at most B_N. *)
    assert (Hpd : QleT' (Qabs (exp_partial n X - tlw383_EQ X N))
                        (tlw383_geom_bound X N)).
    { exact (tlw383_eslot_geom X N n Hgeo (NatLe_drop N n HnN)). }
    (* convert the right side of the goal to the computational face: the projection bodies are Defined-transparent, one conversion step. *)
    apply (qltT_eq_compat_r
             (eps - Qabs (exp_partial n X - tlw383_EQ X N))
             (projT1 (real_const eps) n
              - projT1 (real_metric (cauchy_real_exp (real_const X))
                         (real_const (tlw383_EQ X N))) n)
             ((eps - tlw383_geom_bound X N) / 2)).
    + apply qeq_imp_qeqT. reflexivity.
    + apply (qltT_leT'_ltT ((eps - tlw383_geom_bound X N) / 2)
               (eps - tlw383_geom_bound X N)
               (eps - Qabs (exp_partial n X - tlw383_EQ X N))).
      * apply (qltT_half_lt_selfT (eps - tlw383_geom_bound X N)).
        exact HdB0T.
      * apply Qle_to_QleT'.
        assert (Hneg : Qle (- (tlw383_geom_bound X N))
                          (- Qabs (exp_partial n X - tlw383_EQ X N)))
          by (apply (Qopp_le_compat _ _ (QleT'_to_Qle _ _ Hpd))).
        apply (Qle_trans (eps - tlw383_geom_bound X N)
                           (eps + - (tlw383_geom_bound X N))
                           (eps + - Qabs (exp_partial n X - tlw383_EQ X N))).
        -- apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
        -- apply (Qle_trans (eps + - (tlw383_geom_bound X N))
                       (eps + - Qabs (exp_partial n X - tlw383_EQ X N))
                       (eps - Qabs (exp_partial n X - tlw383_EQ X N))).
           ++ apply (Qplus_le_compat eps eps (- (tlw383_geom_bound X N))
                        (- Qabs (exp_partial n X - tlw383_EQ X N)));
                [apply Qle_refl | exact Hneg].
           ++ apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
              apply (Qeq_sym _ _). ring.
Qed.

(* ===== 7. E-slot assembly: the gap premise carried explicitly ===== *)

(* the gap premise, verbatim the target shape left open by the E-slot:
   there is an M with 2|X| <= M+1 and B_M < eps, the eps-instantiation of
   the factorial suppression; once the later segments close it, this
   assembly drops that premise. *)
Theorem tlw383_eslot_carrier : forall (X : Q) (eps : Q),
  QltT 0 eps ->
  (sigT (fun M : nat =>
     And (QleT' (2 * Qabs X) (lw0_q_of_nat (M + 1)))
         (QltT (tlw383_geom_bound X M) eps))) ->
  sigT (fun M : nat =>
    real_lt (real_metric (cauchy_real_exp (real_const X))
                          (real_const (tlw383_EQ X M)))
            (real_const eps)).
Proof.
  intros X eps Heps0 Hkills.
  destruct Hkills as [M [Hgeo Hslack]].
  exists M. apply tlw383_eslot_real_lt; assumption.
Qed.

(* real-side assembly: the premise p(e) = 0 is carried verbatim (the
   applicability side-condition; used by the downstream redesign
   segments), at the node X = -node (S nodecount). *)
Theorem tlw383_eslot_realcarrier : forall (p : zpoly) (Nn : nat) (eps : Q),
  real_eq (lw3_evalr p lw3_e) real_zero ->
  QltT 0 eps ->
  (sigT (fun M : nat =>
     And (QleT' (2 * Qabs (- lw2_node (Datatypes.S (lw3_nodecount p Nn))))
                 (lw0_q_of_nat (M + 1)))
         (QltT (tlw383_geom_bound
                  (- lw2_node (Datatypes.S (lw3_nodecount p Nn))) M) eps))) ->
  sigT (fun M : nat =>
    real_lt (real_metric
               (cauchy_real_exp
                  (real_const (- lw2_node (Datatypes.S (lw3_nodecount p Nn)))))
               (real_const (tlw383_EQ
                  (- lw2_node (Datatypes.S (lw3_nodecount p Nn))) M)))
            (real_const eps)).
Proof.
  intros p Nn eps Hpzero Heps0 Hkills.
  exact (tlw383_eslot_carrier
          (- lw2_node (Datatypes.S (lw3_nodecount p Nn))) eps Heps0 Hkills).
Qed.

(* ===== 8. scalar Lipschitz bound for the endpoint functional ===== *)

(* from |E1 - E2| <= T and |eps_K f(X)| <= C to
   |exp_L(E1) - exp_L(E2)| <= T * C: the Lipschitz bound for a scalar E,
   the composition lemma that absorbs the deviation of replacing the
   exact scalar by its E-slot truncation. *)
Lemma tlw383_eslot_machine_lip : forall (E1 E2 : Q) (K : nat) (f : QPoly)
  (X T C : Q),
  QleT' (Qabs (E1 - E2)) T ->
  QleT' (Qabs (qpoly_eval (lw2_eps K f) X)) C ->
  QleT' (Qabs (lw2_exp_L E1 K f X - lw2_exp_L E2 K f X)) (T * C).
Proof.
  intros E1 E2 K f X T C HT HC.
  assert (HT0 : QleT' 0 T).
  { apply (qleT'_trans 0 (Qabs (E1 - E2)) T).
    - apply qabs_nonnegT.
    - exact HT. }
  assert (HT2 : QleT' (Qabs (E2 - E1)) T).
  { apply (qleT'_trans (Qabs (E2 - E1)) (Qabs (E1 - E2)) T).
    - apply qeq_leT'. exact (q_abs_minus_sym E2 E1).
    - exact HT. }
  assert (Hr : lw2_exp_L E1 K f X - lw2_exp_L E2 K f X
               == (E2 - E1) * qpoly_eval (lw2_eps K f) X).
  { unfold lw2_exp_L. ring. }
  apply (qleT'_trans (Qabs (lw2_exp_L E1 K f X - lw2_exp_L E2 K f X))
             (Qabs ((E2 - E1) * qpoly_eval (lw2_eps K f) X)) (T * C)).
  - apply qeq_leT'. apply qeq_imp_qeqT. apply (Qabs_wd _ _). exact Hr.
  - apply (qleT'_trans (Qabs ((E2 - E1) * qpoly_eval (lw2_eps K f) X))
             (Qabs (E2 - E1) * Qabs (qpoly_eval (lw2_eps K f) X)) (T * C)).
    + apply qeq_leT'.
      exact (qeq_imp_qeqT _ _
               (tlw383_qabs_mult (E2 - E1) (qpoly_eval (lw2_eps K f) X))).
    + apply (qleT'_trans (Qabs (E2 - E1) * Qabs (qpoly_eval (lw2_eps K f) X))
               (T * Qabs (qpoly_eval (lw2_eps K f) X)) (T * C)).
      * apply qleT'_mult_compat_r; [apply qabs_nonnegT | exact HT2].
      * apply qleT'_mult_compat_l; [exact HT0 | exact HC].
Qed.

(* ===== 9. anchor pins in both directions ===== *)

(* value-level pin of the anchor: at the node X = -node 2 (so |X| = 2)
   and depth N = 5, the uniform tail bound is B_5 = (2^5/5!) * 2 = 8/15 < 1,
   read off the transparent exp_partial value face. *)
Theorem tlw383_eslot_anchor :
  QltT (tlw383_geom_bound
          (- lw2_node (Datatypes.S (Datatypes.S O)))
          (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S O))))))
       (1 # 1)%Q.
Proof.
  unfold QltT, Qlt_bool, tlw383_geom_bound, lw2_node.
  vm_compute. reflexivity.
Qed.

(* real-side witness of the anchor: under the slack above, the real
   distance between e^{-2} and the depth-5 truncation is < 1, the same
   witness-production shape as tlw379_p2inst -- the real_lt face of the
   E-slot producing its witness. *)
Theorem tlw383_eslot_anchor_lt :
  real_lt (real_metric
             (cauchy_real_exp
                (real_const (- lw2_node (Datatypes.S (Datatypes.S O)))))
             (real_const (tlw383_EQ
                (- lw2_node (Datatypes.S (Datatypes.S O)))
                (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S O))))))))
          (real_const (1 # 1)%Q).
Proof.
  apply (tlw383_eslot_real_lt
          (- lw2_node (Datatypes.S (Datatypes.S O)))
          (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S O)))))
          (1 # 1)%Q).
  - unfold QleT', Qle_bool, lw2_node, lw0_q_of_nat, Qabs.
    cbn [Qnum Qden]. vm_compute. reflexivity.
  - apply tlw383_eslot_anchor.
Qed.

(* ===== 10. extraction audit of the data names ===== *)

From Stdlib Require Import Extraction.
Separate Extraction tlw383_EQ tlw383_geom_bound.

(* assumption audit for the named statements *)
Print Assumptions tlw383_eslot_pointwise.
Print Assumptions tlw383_eslot_geom.
Print Assumptions tlw383_eslot_real_lt.
Print Assumptions tlw383_eslot_carrier.
Print Assumptions tlw383_eslot_realcarrier.
Print Assumptions tlw383_eslot_machine_lip.
Print Assumptions tlw383_eslot_anchor.
Print Assumptions tlw383_eslot_anchor_lt.
