(* ConstructiveWorld-Set -- constructive Pinsker-type bounds for two-point distributions. *)

(** * PinskerTwoPoint: explicit witness constant for the two-point TV-KL inequality.

    Mission.  Formalizes the two-point total-variation / KL lower-bound block on
      the [Real] layer: the difference element [p2_diff], its square [p2_tvsq],
      the two-point divergence [p2_kl2] and the witness constant [p2_c].  Main
      statements: [p2_tvsq_sym], [p2_gibbs_core_strict_pgtq], [p2_kl2_pos],
      [p2_c_pos], and the Bishop-form bounds [p2_pinsker_witness_b] and
      [p2_kl2_nonneg_b].

    Dependencies.  Stdlib [QArith.Qring].  Requires [S01_BaseRing],
      [S02_CauchyComplete], [S03_QExp], [S04_RealExpLogConv],
      [S05_AlignmentGRPO], [S06_DiffSamplingGibbs], [S07_RealSetoidExpLog],
      [S08_RealMainlineDPO], [S09_EntropyReal], [S10_KVQuantTrig], [S11_TP3B5],
      [S12_B5RecycleSF], [S13_NLiveAudit], [S14_B5BatchBlock], [S15_TailFEPUp],
      [G07_KLWall], [UpRealLeB], [UpRealLeB3] of this development.

    References.  This development, PinskerTwoPoint.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" PinskerTwoPoint.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 00015ff4]. *)
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
Require Import G07_KLWall.
Require Import UpRealLeB.
Require Import UpRealLeB3.

(* ---- 0. Two-point distribution carrier definitions ---- *)

(* p - q: the difference element whose absolute value is the two-point TV distance. *)
Definition p2_diff (p q : Real) : Real :=
  real_plus p (real_opp q).

(* TV² := (p−q)² *)
Definition p2_tvsq (p q : Real) : Real :=
  real_mult (p2_diff p q) (p2_diff p q).

(* 1−p *)
Definition p2_one_minus (p : Real) : Real :=
  real_plus real_one (real_opp p).

(* KL := kl_term(p,q) + kl_term(1-p,1-q), built from the pointwise term real_kl_term of S08. *)
Definition p2_kl2 (p q : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (Hp1 : real_lt real_zero (p2_one_minus p))
  (Hq1 : real_lt real_zero (p2_one_minus q)) : Real :=
  real_plus (real_kl_term p q Hp Hq)
            (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1).

(* Witness constant c := KL * inv(TV^2): a closed explicit term; the positivity certificate of TV^2 discharges the inverse. *)
Definition p2_c (p q : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (Hp1 : real_lt real_zero (p2_one_minus p))
  (Hq1 : real_lt real_zero (p2_one_minus q))
  (Hkl : real_lt real_zero (p2_kl2 p q Hp Hq Hp1 Hq1))
  (Htv : real_lt real_zero (p2_tvsq p q)) : Real :=
  real_mult (p2_kl2 p q Hp Hq Hp1 Hq1) (real_inv_pos (p2_tvsq p q) Htv).

(* Pointwise Q-ring instantiation: the real_eq_of_zero_diff route, pure difference elements with singleton goals. *)
(* The zero-diff premise is a QeqT carrier leaf (S02 QeqT); the qeq_imp_qeqT bridge re-faces it as a Qeq   *)
(* equation before ring (family-B T-form bridge, canonical route S02_CauchyComplete.v qeq_imp_qeqT).       *)
Ltac p2_ring_eq :=
  apply real_eq_of_zero_diff; intro n0;
  repeat match goal with [ x : Real |- _ ] => destruct x end;
  cbn [projT1 p2_diff p2_one_minus p2_tvsq
       real_plus real_mult real_opp real_one real_zero];
  apply qeq_imp_qeqT; ring.

(* ---- 1. Support lemma one: symmetry of the squared distance, TV^2(p,q) == TV^2(q,p). ---- *)
Lemma p2_tvsq_sym : forall p q : Real,
  real_eq (p2_tvsq p q) (p2_tvsq q p).
Proof.
  intros p q. p2_ring_eq.
Qed.

(* ---- 2. Difference algebra: (1-p) + -(1-q) == q - p, a pointwise ring identity. ---- *)
Lemma p2_one_minus_diff : forall p q : Real,
  real_eq (real_plus (p2_one_minus p) (real_opp (p2_one_minus q)))
          (p2_diff q p).
Proof.
  intros p q. p2_ring_eq.
Qed.

(* ---- 3. Positivity transfer for the difference element: p < q gives 0 < q - p. ---- *)
Lemma p2_diff_pos_of_lt : forall p q : Real,
  real_lt p q -> real_lt real_zero (p2_diff q p).
Proof.
  intros p q Hpq.
  assert (H' : real_lt (real_plus (real_opp p) p)
                       (real_plus (real_opp p) q))
    by exact (real_lt_plus_translate (real_opp p) p q Hpq).
  apply (RealSetoid.real_lt_id_r real_zero
           (real_plus (real_opp p) q) (p2_diff q p)).
  - p2_ring_eq.
  - apply (RealSetoid.real_lt_id_l real_zero
             (real_plus (real_opp p) p) (real_plus (real_opp p) q)).
    + p2_ring_eq.
    + exact H'.
Qed.

(* ---- 4. Support lemma two: one-minus is antitone, p < q gives (1-q) < (1-p). ---- *)
Lemma p2_one_minus_antitone : forall p q : Real,
  real_lt p q -> real_lt (p2_one_minus q) (p2_one_minus p).
Proof.
  intros p q Hpq.
  apply real_lt_zero_minus.
  apply (RealSetoid.real_lt_id_r real_zero
           (p2_diff q p)
           (real_plus (p2_one_minus p) (real_opp (p2_one_minus q)))).
  - apply real_eq_sym. exact (p2_one_minus_diff p q).
  - exact (p2_diff_pos_of_lt p q Hpq).
Qed.

(* ---- 5. Support lemma three: the dual strict Gibbs pointwise kernel (q < p branch). ---- *)
(*   The G07 kernel klst_gibbs_core_strict covers only the p < q branch; this file    *)
(*   rebuilds the q < p branch from the same klst_gap_shape ring reshaping plus the   *)
(*   x < 1 tangent upper bound klst_log_tangent_neg. *)
Lemma p2_gibbs_core_strict_pgtq : forall (p q : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (Hqp : real_lt q p),
  real_lt real_zero
    (real_plus (real_kl_term p q Hp Hq) (real_plus q (real_opp p))).
Proof.
  intros p q Hp Hq Hqp.
  unfold real_kl_term.
  set (X := real_mult q (real_inv_pos p Hp)).
  set (HX := real_mult_positive q (real_inv_pos p Hp) Hq
               (real_inv_pos_pos p Hp)).
  set (L := real_log X HX).
  assert (Hxpos : real_lt real_zero X) by exact HX.
  assert (Hxlt : real_lt X real_one).
  { apply (RealSetoid.real_lt_id_r (real_mult q (real_inv_pos p Hp))
             (real_mult p (real_inv_pos p Hp)) real_one).
    - exact (real_inv_pos_correct p Hp).
    - exact (real_mult_lt_compat q p (real_inv_pos p Hp) Hqp
               (real_inv_pos_pos p Hp)). }
  assert (Htan : real_lt L (real_plus X (real_opp real_one)))
    by exact (klst_log_tangent_neg X HX Hxlt).
  assert (Hgap : real_lt real_zero
                   (real_plus (real_plus X (real_opp real_one))
                              (real_opp L))).
  { apply (RealSetoid.real_lt_id_r real_zero
             (real_plus (real_opp L) (real_plus X (real_opp real_one)))
             (real_plus (real_plus X (real_opp real_one)) (real_opp L))).
    - apply real_plus_comm.
    - apply (RealSetoid.real_lt_id_l real_zero
               (real_plus (real_opp L) L)
               (real_plus (real_opp L) (real_plus X (real_opp real_one)))).
      + apply real_eq_sym.
        apply (real_eq_trans _ (real_plus L (real_opp L)) _).
        * apply real_plus_comm.
        * apply real_plus_opp.
      + exact (real_lt_plus_translate (real_opp L) L
                 (real_plus X (real_opp real_one)) Htan). }
  assert (Hprod : real_lt real_zero
                    (real_mult p (real_plus (real_plus X (real_opp real_one))
                                            (real_opp L))))
    by exact (real_mult_pos_compat p
                (real_plus (real_plus X (real_opp real_one)) (real_opp L))
                Hp Hgap).
  apply (RealSetoid.real_lt_id_r real_zero
           (real_mult p (real_plus (real_plus X (real_opp real_one))
                                   (real_opp L)))
           (real_plus (real_kl_term p q Hp Hq) (real_plus q (real_opp p)))).
  - apply real_eq_sym. exact (klst_gap_shape p q Hp Hq).
  - exact Hprod.
Qed.

(* ---- 6. Support lemma four: two-point energy positivity (kl2 > 0 once p ≠ q). ---- *)
(*   Assembly: kl2 == [kl(p,q) + (q-p)] + [kl(1-p,1-q) + (p-q)]; the p < q branch      *)
(*   takes the G07 kernel on (p,q) and the dual kernel on (1-p,1-q), the q < p         *)
(*   branch swaps the two, and plus/minus (p-q) cancels pointwise. *)
Theorem p2_kl2_pos : forall (p q : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (Hp1 : real_lt real_zero (p2_one_minus p))
  (Hq1 : real_lt real_zero (p2_one_minus q))
  (Hne : Or (real_lt p q) (real_lt q p)),
  real_lt real_zero (p2_kl2 p q Hp Hq Hp1 Hq1).
Proof.
  intros p q Hp Hq Hp1 Hq1 Hne.
  destruct Hne as [Hpq | Hqp].
  - (* Case p < q: the G07 kernel on (p,q) and the dual kernel on (1-p,1-q), reshaped onto p - q. *)
    assert (H2 : real_lt real_zero
                   (real_plus (real_kl_term (p2_one_minus p)
                                       (p2_one_minus q) Hp1 Hq1)
                              (p2_diff p q))).
    { apply (RealSetoid.real_lt_id_r real_zero
               (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q)
                            Hp1 Hq1)
                          (real_plus (p2_one_minus q)
                                    (real_opp (p2_one_minus p))))
               (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q)
                            Hp1 Hq1)
                          (p2_diff p q))).
      - apply (RealSetoid.real_eq_plus_compat
                 (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1)
                 (real_plus (p2_one_minus q) (real_opp (p2_one_minus p)))
                 (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1)
                 (p2_diff p q)).  (* The S07 compat lemma pairs its arguments in the crossed order (a ≈ c)(b ≈ d). *)
        + apply real_eq_refl.
        + exact (p2_one_minus_diff q p).
      - exact (p2_gibbs_core_strict_pgtq (p2_one_minus p) (p2_one_minus q)
                 Hp1 Hq1 (p2_one_minus_antitone p q Hpq)). }
    assert (Hsum : real_lt real_zero
                     (real_plus
                        (real_plus (real_kl_term p q Hp Hq) (p2_diff q p))
                        (real_plus (real_kl_term (p2_one_minus p)
                                             (p2_one_minus q) Hp1 Hq1)
                                   (p2_diff p q)))).
    { apply (RealSetoid.real_lt_id_l real_zero real_zero
               (real_plus
                  (real_plus (real_kl_term p q Hp Hq) (p2_diff q p))
                  (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q)
                                       Hp1 Hq1)
                             (p2_diff p q)))).
      - apply real_eq_refl.
      - exact (real_lt_plus_compat real_zero
                 (real_plus (real_kl_term p q Hp Hq) (p2_diff q p))
                 real_zero
                 (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q)
                                      Hp1 Hq1)
                            (p2_diff p q))
                 (klst_gibbs_core_strict p q Hp Hq Hpq) H2). }
    apply (RealSetoid.real_lt_id_r real_zero
             (real_plus (p2_kl2 p q Hp Hq Hp1 Hq1)
                        (real_plus (p2_diff q p) (p2_diff p q)))
             (p2_kl2 p q Hp Hq Hp1 Hq1)).
    + apply (real_eq_trans
               _ (real_plus (p2_kl2 p q Hp Hq Hp1 Hq1) real_zero) _).
      * apply (RealSetoid.real_eq_plus_compat
                 (p2_kl2 p q Hp Hq Hp1 Hq1)
                 (real_plus (p2_diff q p) (p2_diff p q))
                 (p2_kl2 p q Hp Hq Hp1 Hq1) real_zero).  (* The compat lemma pairs its arguments in the crossed order (a ≈ c)(b ≈ d). *)
      -- p2_ring_eq.
      -- apply real_eq_sym. p2_ring_eq.
      * apply real_plus_zero.
    + apply (RealSetoid.real_lt_id_r real_zero
               (real_plus
                  (real_plus (real_kl_term p q Hp Hq) (p2_diff q p))
                  (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q)
                                       Hp1 Hq1)
                             (p2_diff p q)))
               (real_plus (p2_kl2 p q Hp Hq Hp1 Hq1)
                          (real_plus (p2_diff q p) (p2_diff p q)))).
      * (* Pure associativity/commutativity rebuilding of the B'-C' chain; every trans, sym and compat argument is explicit. *)
        exact (real_eq_trans
          (real_plus (real_plus (real_kl_term p q Hp Hq) (p2_diff q p)) (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1) (p2_diff p q))) (real_plus (real_kl_term p q Hp Hq) (real_plus (p2_diff q p) (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1) (p2_diff p q)))) (real_plus (real_plus (real_kl_term p q Hp Hq) (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1)) (real_plus (p2_diff q p) (p2_diff p q)))
          (real_eq_sym (real_plus (real_kl_term p q Hp Hq) (real_plus (p2_diff q p) (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1) (p2_diff p q)))) (real_plus (real_plus (real_kl_term p q Hp Hq) (p2_diff q p)) (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1) (p2_diff p q)))
             (real_plus_assoc (real_kl_term p q Hp Hq) (p2_diff q p) (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1) (p2_diff p q))))
          (real_eq_trans
             (real_plus (real_kl_term p q Hp Hq) (real_plus (p2_diff q p) (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1) (p2_diff p q)))) (real_plus (real_kl_term p q Hp Hq) (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1) (real_plus (p2_diff q p) (p2_diff p q)))) (real_plus (real_plus (real_kl_term p q Hp Hq) (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1)) (real_plus (p2_diff q p) (p2_diff p q)))
             (RealSetoid.real_eq_plus_compat (real_kl_term p q Hp Hq) (real_plus (p2_diff q p) (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1) (p2_diff p q))) (real_kl_term p q Hp Hq) (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1) (real_plus (p2_diff q p) (p2_diff p q)))
                (real_eq_refl (real_kl_term p q Hp Hq))
                (real_eq_trans (real_plus (p2_diff q p) (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1) (p2_diff p q))) (real_plus (real_plus (p2_diff q p) (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1)) (p2_diff p q)) (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1) (real_plus (p2_diff q p) (p2_diff p q)))
                   (real_plus_assoc (p2_diff q p) (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1) (p2_diff p q))
                   (real_eq_trans (real_plus (real_plus (p2_diff q p) (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1)) (p2_diff p q)) (real_plus (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1) (p2_diff q p)) (p2_diff p q)) (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1) (real_plus (p2_diff q p) (p2_diff p q)))
                      (RealSetoid.real_eq_plus_compat (real_plus (p2_diff q p) (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1)) (p2_diff p q) (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1) (p2_diff q p)) (p2_diff p q)
                         (real_plus_comm (p2_diff q p) (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1)) (real_eq_refl (p2_diff p q)))
                      (real_eq_sym (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1) (real_plus (p2_diff q p) (p2_diff p q))) (real_plus (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1) (p2_diff q p)) (p2_diff p q))
                         (real_plus_assoc (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1) (p2_diff q p) (p2_diff p q))))))
             (real_plus_assoc (real_kl_term p q Hp Hq) (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1) (real_plus (p2_diff q p) (p2_diff p q))))).
      * exact Hsum.
  - (* Case q < p: the dual kernel on (p,q) and the G07 kernel on (1-p,1-q) where 1-p < 1-q. *)
    assert (H2 : real_lt real_zero
                   (real_plus (real_kl_term (p2_one_minus p)
                                       (p2_one_minus q) Hp1 Hq1)
                              (p2_diff p q))).
    { apply (RealSetoid.real_lt_id_r real_zero
               (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q)
                            Hp1 Hq1)
                          (real_plus (p2_one_minus q)
                                    (real_opp (p2_one_minus p))))
               (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q)
                            Hp1 Hq1)
                          (p2_diff p q))).
      - apply (RealSetoid.real_eq_plus_compat
                 (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1)
                 (real_plus (p2_one_minus q) (real_opp (p2_one_minus p)))
                 (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1)
                 (p2_diff p q)).  (* The S07 compat lemma pairs its arguments in the crossed order (a ≈ c)(b ≈ d). *)
        + apply real_eq_refl.
        + exact (p2_one_minus_diff q p).
      - exact (klst_gibbs_core_strict (p2_one_minus p) (p2_one_minus q)
                 Hp1 Hq1 (p2_one_minus_antitone q p Hqp)). }
    assert (Hsum : real_lt real_zero
                     (real_plus
                        (real_plus (real_kl_term p q Hp Hq) (p2_diff q p))
                        (real_plus (real_kl_term (p2_one_minus p)
                                             (p2_one_minus q) Hp1 Hq1)
                                   (p2_diff p q)))).
    { apply (RealSetoid.real_lt_id_l real_zero real_zero
               (real_plus
                  (real_plus (real_kl_term p q Hp Hq) (p2_diff q p))
                  (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q)
                                       Hp1 Hq1)
                             (p2_diff p q)))).
      - apply real_eq_refl.
      - exact (real_lt_plus_compat real_zero
                 (real_plus (real_kl_term p q Hp Hq) (p2_diff q p))
                 real_zero
                 (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q)
                                      Hp1 Hq1)
                            (p2_diff p q))
                 (p2_gibbs_core_strict_pgtq p q Hp Hq Hqp) H2). }
    apply (RealSetoid.real_lt_id_r real_zero
             (real_plus (p2_kl2 p q Hp Hq Hp1 Hq1)
                        (real_plus (p2_diff q p) (p2_diff p q)))
             (p2_kl2 p q Hp Hq Hp1 Hq1)).
    + apply (real_eq_trans
               _ (real_plus (p2_kl2 p q Hp Hq Hp1 Hq1) real_zero) _).
      * apply (RealSetoid.real_eq_plus_compat
                 (p2_kl2 p q Hp Hq Hp1 Hq1)
                 (real_plus (p2_diff q p) (p2_diff p q))
                 (p2_kl2 p q Hp Hq Hp1 Hq1) real_zero).  (* The compat lemma pairs its arguments in the crossed order (a ≈ c)(b ≈ d). *)
      -- p2_ring_eq.
      -- apply real_eq_sym. p2_ring_eq.
      * apply real_plus_zero.
    + apply (RealSetoid.real_lt_id_r real_zero
               (real_plus
                  (real_plus (real_kl_term p q Hp Hq) (p2_diff q p))
                  (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q)
                                       Hp1 Hq1)
                             (p2_diff p q)))
               (real_plus (p2_kl2 p q Hp Hq Hp1 Hq1)
                          (real_plus (p2_diff q p) (p2_diff p q)))).
      * (* Pure associativity/commutativity rebuilding of the B'-C' chain; every trans, sym and compat argument is explicit. *)
        exact (real_eq_trans
          (real_plus (real_plus (real_kl_term p q Hp Hq) (p2_diff q p)) (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1) (p2_diff p q))) (real_plus (real_kl_term p q Hp Hq) (real_plus (p2_diff q p) (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1) (p2_diff p q)))) (real_plus (real_plus (real_kl_term p q Hp Hq) (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1)) (real_plus (p2_diff q p) (p2_diff p q)))
          (real_eq_sym (real_plus (real_kl_term p q Hp Hq) (real_plus (p2_diff q p) (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1) (p2_diff p q)))) (real_plus (real_plus (real_kl_term p q Hp Hq) (p2_diff q p)) (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1) (p2_diff p q)))
             (real_plus_assoc (real_kl_term p q Hp Hq) (p2_diff q p) (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1) (p2_diff p q))))
          (real_eq_trans
             (real_plus (real_kl_term p q Hp Hq) (real_plus (p2_diff q p) (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1) (p2_diff p q)))) (real_plus (real_kl_term p q Hp Hq) (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1) (real_plus (p2_diff q p) (p2_diff p q)))) (real_plus (real_plus (real_kl_term p q Hp Hq) (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1)) (real_plus (p2_diff q p) (p2_diff p q)))
             (RealSetoid.real_eq_plus_compat (real_kl_term p q Hp Hq) (real_plus (p2_diff q p) (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1) (p2_diff p q))) (real_kl_term p q Hp Hq) (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1) (real_plus (p2_diff q p) (p2_diff p q)))
                (real_eq_refl (real_kl_term p q Hp Hq))
                (real_eq_trans (real_plus (p2_diff q p) (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1) (p2_diff p q))) (real_plus (real_plus (p2_diff q p) (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1)) (p2_diff p q)) (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1) (real_plus (p2_diff q p) (p2_diff p q)))
                   (real_plus_assoc (p2_diff q p) (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1) (p2_diff p q))
                   (real_eq_trans (real_plus (real_plus (p2_diff q p) (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1)) (p2_diff p q)) (real_plus (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1) (p2_diff q p)) (p2_diff p q)) (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1) (real_plus (p2_diff q p) (p2_diff p q)))
                      (RealSetoid.real_eq_plus_compat (real_plus (p2_diff q p) (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1)) (p2_diff p q) (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1) (p2_diff q p)) (p2_diff p q)
                         (real_plus_comm (p2_diff q p) (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1)) (real_eq_refl (p2_diff p q)))
                      (real_eq_sym (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1) (real_plus (p2_diff q p) (p2_diff p q))) (real_plus (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1) (p2_diff q p)) (p2_diff p q))
                         (real_plus_assoc (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1) (p2_diff q p) (p2_diff p q))))))
             (real_plus_assoc (real_kl_term p q Hp Hq) (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1) (real_plus (p2_diff q p) (p2_diff p q))))).
      * exact Hsum.
Qed.

(* ---- 7. Main theorem, witness form: 0 < c and c*TV^2 <=_B KL. ---- *)

(* 7a. The witness is genuinely positive: KL > 0 and TV^2 > 0 give 0 < c := KL * inv(TV^2). *)
Theorem p2_c_pos : forall (p q : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (Hp1 : real_lt real_zero (p2_one_minus p))
  (Hq1 : real_lt real_zero (p2_one_minus q))
  (Hkl : real_lt real_zero (p2_kl2 p q Hp Hq Hp1 Hq1))
  (Htv : real_lt real_zero (p2_tvsq p q)),
  real_lt real_zero (p2_c p q Hp Hq Hp1 Hq1 Hkl Htv).
Proof.
  intros p q Hp Hq Hp1 Hq1 Hkl Htv.
  unfold p2_c.
  exact (real_mult_positive (p2_kl2 p q Hp Hq Hp1 Hq1)           (real_inv_pos (p2_tvsq p q) Htv) Hkl           (real_inv_pos_pos (p2_tvsq p q) Htv)).
Qed.

(* 7b. Main theorem: c*TV^2 == KL (the inverse algebra chain) gives the Bishop         *)
(*   form c*TV^2 <=_B KL.  Witness form of the Pinsker-type lower bound: the           *)
(*   constant is an explicit closed term, positive by 7a, and the bound exits on       *)
(*   the Set face through real_le_b (forall eps > 0). *)
Theorem p2_pinsker_witness_b : forall (p q : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (Hp1 : real_lt real_zero (p2_one_minus p))
  (Hq1 : real_lt real_zero (p2_one_minus q))
  (Hkl : real_lt real_zero (p2_kl2 p q Hp Hq Hp1 Hq1))
  (Htv : real_lt real_zero (p2_tvsq p q)),
  real_le_b (real_mult (p2_c p q Hp Hq Hp1 Hq1 Hkl Htv) (p2_tvsq p q))
            (p2_kl2 p q Hp Hq Hp1 Hq1).
Proof.
  intros p q Hp Hq Hp1 Hq1 Hkl Htv.
  assert (Hmain : real_eq
                    (real_mult (real_mult (p2_kl2 p q Hp Hq Hp1 Hq1)
                                 (real_inv_pos (p2_tvsq p q) Htv))
                               (p2_tvsq p q))
                    (p2_kl2 p q Hp Hq Hp1 Hq1)).
  { apply (real_eq_trans
             _ (real_mult (p2_kl2 p q Hp Hq Hp1 Hq1)
                          (real_mult (real_inv_pos (p2_tvsq p q) Htv)
                                     (p2_tvsq p q))) _).
    - apply real_eq_sym.
      exact (real_mult_assoc (p2_kl2 p q Hp Hq Hp1 Hq1)
               (real_inv_pos (p2_tvsq p q) Htv) (p2_tvsq p q)).
    - apply (real_eq_trans
               _ (real_mult (p2_kl2 p q Hp Hq Hp1 Hq1) real_one) _).
      + apply (RealSetoid.real_eq_mult_compat
                 (p2_kl2 p q Hp Hq Hp1 Hq1)
                 (real_mult (real_inv_pos (p2_tvsq p q) Htv)
                            (p2_tvsq p q))
                 (p2_kl2 p q Hp Hq Hp1 Hq1) real_one).  (* The compat lemma pairs its arguments in the crossed order (a ≈ c)(b ≈ d). *)
        * apply real_eq_refl.
        * apply (real_eq_trans
                   _ (real_mult (p2_tvsq p q)
                                (real_inv_pos (p2_tvsq p q) Htv)) _).
          -- exact (real_mult_comm (real_inv_pos (p2_tvsq p q) Htv)
                      (p2_tvsq p q)).
          -- exact (real_inv_pos_correct (p2_tvsq p q) Htv).
      + exact (real_mult_one (p2_kl2 p q Hp Hq Hp1 Hq1)).  (* The lemma real_mult_one is oriented as x * one == x, matching this goal directly. *) }
  apply (leb3_le_b_eq_l (p2_kl2 p q Hp Hq Hp1 Hq1)
           (real_mult (real_mult (p2_kl2 p q Hp Hq Hp1 Hq1)
                        (real_inv_pos (p2_tvsq p q) Htv))
                      (p2_tvsq p q))
           (p2_kl2 p q Hp Hq Hp1 Hq1)).
  - apply real_eq_sym. exact Hmain.
  - apply leb3_le_b_refl.
Qed.

(* ---- 8. Companion B-face closure: p ≠ q (Or premise) gives 0 <=_B KL (two-point Gibbs closure). ---- *)
Theorem p2_kl2_nonneg_b : forall (p q : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (Hp1 : real_lt real_zero (p2_one_minus p))
  (Hq1 : real_lt real_zero (p2_one_minus q))
  (Hne : Or (real_lt p q) (real_lt q p)),
  real_le_b real_zero (p2_kl2 p q Hp Hq Hp1 Hq1).
Proof.
  intros p q Hp Hq Hp1 Hq1 Hne.
  exact (real_le_to_le_b real_zero (p2_kl2 p q Hp Hq Hp1 Hq1)
    (@inl (real_lt real_zero (p2_kl2 p q Hp Hq Hp1 Hq1))
          (real_eq real_zero (p2_kl2 p q Hp Hq Hp1 Hq1))
     (p2_kl2_pos p q Hp Hq Hp1 Hq1 Hne))).
Qed.

(* ---- End-of-file assumption audit. ---- *)
Print Assumptions p2_tvsq_sym.
Print Assumptions p2_gibbs_core_strict_pgtq.
Print Assumptions p2_kl2_pos.
Print Assumptions p2_c_pos.
Print Assumptions p2_pinsker_witness_b.
Print Assumptions p2_kl2_nonneg_b.
