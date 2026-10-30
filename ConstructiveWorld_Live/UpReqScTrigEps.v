(* ========================================================================== *)
(*  UpReqScTrigEps.v - eps and Bishop remainder faces for the sc_cos/sc_sin   *)
(*                     family of S10_KVQuantTrig                              *)
(* ========================================================================== *)
(*   Mission. Per-eps remainder faces and Bishop faces completing the        *)
(*   sc_cos/sc_sin family (interpolation seam #4).  Part A: the family      *)
(*   mother bridge sce_real_le_eps_face turns the Or-encoded real_le into   *)
(*   the plain-eps face (forall eps > 0, real_le lhs (rhs + eps)) via the   *)
(*   one-way bridge real_le_to_le_b of UpRealLeB; the converse direction    *)
(*   is not claimed (constructively unprovable, UpRealLeB closing reg.).    *)
(*   Part B: the four S10 sandwich theorems on [0,1] (premises verbatim,    *)
(*   none new) lifted to four eps faces sce_real_*_eps and four Bishop      *)
(*   faces sce_real_*_B (via real_le_closure_b_one, D := real_one), so      *)
(*   the chain serves the three faces Or / eps / <=_B.  Part C: tail        *)
(*   bounds for the partial-sum truncation: Q-layer tails                   *)
(*   sce_cos/sin_partial_tail_le (from sc_cos/sin_diff_bound2 at            *)
(*   y := B := q, tail T_n(q) := q^(S(2n))/(S(2n))! shared) and the         *)
(*   Real Bishop tails sce_cos/sin_real_tail_B:                            *)
(*   |cauchy_real_cos/sin(real_const q) - S_n(q)| <=_B 3 * T_n(q),         *)
(*   delta := T_n/2; the q == 0 branch closes exactly by real_eq.           *)
(*   Dependencies. Stdlib QArith (Qring, Qabs), Lia; S01_BaseRing through   *)
(*   S15_TailFEPUp (Set-valued witnesses QltT/QleT'/QeqT/NatLe with         *)
(*   registered conversion lemmas); UpRealLeB.  No further Require.         *)
(*   References. Baseline module UpReqScTrigEps.v of ConstructiveWorld-Main *)
(*   / _Live (names verbatim; census 22=22 ordered identity).               *)
(*   Constructivity. All statements Set-valued; axiom-free, no classical    *)
(*   logic, extracts with Obj.magic = 0.                                    *)
(*   Build. rocq c -native-compiler no -q -Q . "" UpReqScTrigEps.v          *)
(*   (Rocq 9.1 toolchain; single -Q root with an empty logical prefix).     *)

From Stdlib Require Import QArith.Qring.
From Stdlib Require Import QArith.Qabs.
From Stdlib Require Import Lia.
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
(* Part A: base face - the Or-encoded real_le implies the       *)
(* plain-eps remainder face (family mother bridge).             *)
(* ============================================================ *)

(* Mother bridge: Or-encoded real_le lhs rhs implies
   forall eps > 0, real_le lhs (rhs + eps).
   Construction: the one-way bridge real_le_to_le_b (UpRealLeB) yields the
   Bishop face real_le_b lhs rhs, which by definition is exactly the
   plain-eps family; the target real_le face is recovered on the inl
   branch of real_lt_le_iff_req, after taking the eps premise.
   Meaning: the constructive multi-branch decision burden of the Or-exact
   form is dissolved by the one-way shift - downstream assembly needs no
   case split; the reverse direction (eps face implies Or face) is not
   claimed (constructively unprovable; closing register of UpRealLeB). *)
Lemma sce_real_le_eps_face : forall lhs rhs : Real,
  real_le lhs rhs ->
  forall eps : Real, real_lt real_zero eps ->
  real_le lhs (real_plus rhs eps).
Proof.
  intros lhs rhs Hle eps Heps.
  apply RealSetoid.real_lt_le_iff_req. apply inl.
  apply (real_le_to_le_b lhs rhs Hle). exact Heps.
Qed.

(* ============================================================ *)
(* Part B: first-section four faces - the eps/Bishop lifting of  *)
(*   the S10 Real-layer sandwich theorems.  Domains and premise  *)
(*   positions carried over verbatim (double real_le on          *)
(*   0 <= X <= 1), no new premises.                              *)
(* ============================================================ *)

(* B.1 sin X <=_eps X (source theorem real_sin_le_x) *)
Lemma sce_real_sin_le_x_eps : forall X : Real,
  real_le real_zero X -> real_le X (real_const 1) ->
  forall eps : Real, real_lt real_zero eps ->
  real_le (cauchy_real_sin X) (real_plus X eps).
Proof.
  intros X H0 H1 eps Heps.
  exact (sce_real_le_eps_face (cauchy_real_sin X) X (real_sin_le_x X H0 H1)
           eps Heps).
Qed.

(* B.2 X - X^3/6 <=_eps sin X (source theorem real_x_minus_cube_le_sin) *)
Lemma sce_real_x_minus_cube_le_sin_eps : forall X : Real,
  real_le real_zero X -> real_le X (real_const 1) ->
  forall eps : Real, real_lt real_zero eps ->
  real_le (real_plus X (real_opp (real_mult (real_mult X (real_mult X X))
                                            (real_const (1 / 6)))))
          (real_plus (cauchy_real_sin X) eps).
Proof.
  intros X H0 H1 eps Heps.
  exact (sce_real_le_eps_face
           (real_plus X (real_opp (real_mult (real_mult X (real_mult X X))
                                             (real_const (1 / 6)))))
           (cauchy_real_sin X)
           (real_x_minus_cube_le_sin X H0 H1) eps Heps).
Qed.

(* B.3 cos X <=_eps 1 (source theorem real_cos_le_one) *)
Lemma sce_real_cos_le_one_eps : forall X : Real,
  real_le real_zero X -> real_le X (real_const 1) ->
  forall eps : Real, real_lt real_zero eps ->
  real_le (cauchy_real_cos X) (real_plus (real_const 1) eps).
Proof.
  intros X H0 H1 eps Heps.
  exact (sce_real_le_eps_face (cauchy_real_cos X) (real_const 1)
           (real_cos_le_one X H0 H1) eps Heps).
Qed.

(* B.4 1 - X^2/2 <=_eps cos X (source theorem real_one_minus_half_le_cos) *)
Lemma sce_real_one_minus_half_le_cos_eps : forall X : Real,
  real_le real_zero X -> real_le X (real_const 1) ->
  forall eps : Real, real_lt real_zero eps ->
  real_le (real_plus (real_const 1)
                     (real_opp (real_mult (real_mult X X) (real_const (1 / 2)))))
          (real_plus (cauchy_real_cos X) eps).
Proof.
  intros X H0 H1 eps Heps.
  exact (sce_real_le_eps_face
           (real_plus (real_const 1)
                      (real_opp (real_mult (real_mult X X) (real_const (1 / 2)))))
           (cauchy_real_cos X)
           (real_one_minus_half_le_cos X H0 H1) eps Heps).
Qed.

(* B.5 to B.8: Bishop completions of the four (the real_le_closure_b_one
   completer plus B.1 to B.4 direct; certificate D := real_one, and
   real_lt_zero_one already in the library). *)
Lemma sce_real_sin_le_x_B : forall X : Real,
  real_le real_zero X -> real_le X (real_const 1) ->
  real_le_b (cauchy_real_sin X) X.
Proof.
  intros X H0 H1. apply real_le_closure_b_one. intros eps Heps.
  exact (sce_real_sin_le_x_eps X H0 H1 eps Heps).
Qed.

Lemma sce_real_x_minus_cube_le_sin_B : forall X : Real,
  real_le real_zero X -> real_le X (real_const 1) ->
  real_le_b (real_plus X (real_opp (real_mult (real_mult X (real_mult X X))
                                              (real_const (1 / 6)))))
            (cauchy_real_sin X).
Proof.
  intros X H0 H1. apply real_le_closure_b_one. intros eps Heps.
  exact (sce_real_x_minus_cube_le_sin_eps X H0 H1 eps Heps).
Qed.

Lemma sce_real_cos_le_one_B : forall X : Real,
  real_le real_zero X -> real_le X (real_const 1) ->
  real_le_b (cauchy_real_cos X) (real_const 1).
Proof.
  intros X H0 H1. apply real_le_closure_b_one. intros eps Heps.
  exact (sce_real_cos_le_one_eps X H0 H1 eps Heps).
Qed.

Lemma sce_real_one_minus_half_le_cos_B : forall X : Real,
  real_le real_zero X -> real_le X (real_const 1) ->
  real_le_b (real_plus (real_const 1)
                       (real_opp (real_mult (real_mult X X)
                                            (real_const (1 / 2)))))
            (cauchy_real_cos X).
Proof.
  intros X H0 H1. apply real_le_closure_b_one. intros eps Heps.
  exact (sce_real_one_minus_half_le_cos_eps X H0 H1 eps Heps).
Qed.

(* ============================================================ *)
(* Part C: tail-remainder eps faces - the constructive            *)
(* quantification of the partial-sum truncation tails.            *)
(* ============================================================ *)

(* C.0 Tail quantity: T_n(q) := q^(S(2n))/(S(2n))! (absolute value of the
   first discarded term; the bound exponent of sc_sin/sc_cos_diff_bound2
   is S(2n) alike, shared by sin and cos). *)
Definition sce_cos_tail (q : Q) (n : nat) : Q :=
  q_pow q (Datatypes.S (2 * n)) / q_fact (Datatypes.S (2 * n)).

(* C.0a Helper: 0 < 1/2 (closed Q literal). *)
Lemma sce_half_pos : QltT 0 (1 # 2).
Proof. vm_compute. reflexivity. Qed.

(* C.1 Helper: 2 <= (t+1)#1 (t >= 1; the B-side geometric premise of
   sc_*_diff_bound2 evaluated at B := 1). *)
Lemma sce_two_le_nat_q : forall t : nat, NatLe 1 t ->
  QleT' (1 + 1)%Q (Z.of_nat (t + 1) # 1).
Proof.
  intros t Ht.
  assert (HtQ : (1 <= t)%nat) by (apply NatLe_drop; exact Ht).
  apply Qle_to_QleT'.
  assert (H1 : (1 + 1)%Q == 2) by reflexivity.
  rewrite H1.
  unfold Qle. simpl. lia.
Qed.

(* C.2 Helper: 0 < q implies 0 < q^k (q_pow strictly positive;
   induction + Qmult_lt_compat_r). *)
Lemma sce_q_pow_pos : forall (q : Q) (k : nat), QltT 0 q -> QltT 0 (q_pow q k).
Proof.
  intros q k Hq. induction k as [| k IH].
  - exact qltT_0_1.
  - apply Qlt_to_QltT.
    rewrite (qeqT_imp_qeq _ _ (q_pow_succ q k)).
    assert (HqQ : Qlt 0 q) by (apply QltT_to_Qlt; exact Hq).
    assert (HIHQ : Qlt 0 (q_pow q k)) by (apply QltT_to_Qlt; exact IH).
    assert (Hpre : Qlt (0 * q_pow q k) (q * q_pow q k))
      by (apply (Qmult_lt_compat_r 0 q (q_pow q k)); assumption).
    rewrite Qmult_0_l in Hpre. exact Hpre.
Qed.

(* C.3 Helper: 0 < q implies 0 < T_n(q) (q^... > 0 times 1/(2n+2)! > 0,
   multiplicative closure). *)
Lemma sce_cos_tail_pos : forall (q : Q) (n : nat), QltT 0 q ->
  QltT 0 (sce_cos_tail q n).
Proof.
  intros q n Hq. apply Qlt_to_QltT. unfold sce_cos_tail. unfold Qdiv.
  assert (HqQ : Qlt 0 q) by (apply QltT_to_Qlt; exact Hq).
  assert (Hpow : Qlt 0 (q_pow q (Datatypes.S (2 * n))))
    by (apply QltT_to_Qlt; apply (sce_q_pow_pos q); exact Hq).
  assert (Hinv : Qlt 0 (Qinv (q_fact (Datatypes.S (2 * n)))))
    by (apply Qinv_lt_0_compat; apply (QltT_to_Qlt _ _); apply q_fact_pos).
  assert (Hpre : Qlt (0 * Qinv (q_fact (Datatypes.S (2 * n))))
                     (q_pow q (Datatypes.S (2 * n))
                      * Qinv (q_fact (Datatypes.S (2 * n)))))
    by (apply (Qmult_lt_compat_r 0 (q_pow q (Datatypes.S (2 * n)))
                                  (Qinv (q_fact (Datatypes.S (2 * n)))));
        assumption).
  rewrite Qmult_0_l in Hpre. exact Hpre.
Qed.

(* C.3a Zero-evaluation trio: the partial sums and the tail at q == 0.
   q sits in a non-morphic position inside q_pow/cos_partial/sin_partial,
   so Qeq rewriting cannot reach it; closed uniformly by the q_pow_wd
   supply form plus computable evaluation inside each lemma. *)
Lemma sce_cos_tail_at_zero : forall (q : Q) (n : nat), QeqT q 0 ->
  QeqT (sce_cos_tail q n) 0.
Proof.
  intros q n Hz. apply qeq_imp_qeqT. unfold sce_cos_tail, Qdiv.
  assert (Hqp : q_pow q (Datatypes.S (2 * n)) == q_pow 0 (Datatypes.S (2 * n)))
    by exact (qeqT_imp_qeq _ _ (q_pow_wd q 0 (Datatypes.S (2 * n)) Hz)).
  rewrite Hqp.
  assert (Hq0 : q_pow 0 (Datatypes.S (2 * n)) == 0) by reflexivity.
  rewrite Hq0. apply Qmult_0_l.
Qed.

Lemma sce_cos_partial_at_zero : forall (q : Q) (n : nat), QeqT q 0 ->
  QeqT (cos_partial n q) 1.
Proof.
  intros q n Hz. apply qeq_imp_qeqT.
  induction n as [| n IH].
  - reflexivity.
  - change (cos_partial (Datatypes.S n) q)
      with (cos_partial n q + cos_term (Datatypes.S n) q)%Q.
    rewrite IH.
    assert (Hterm : cos_term (Datatypes.S n) q == 0).
    { unfold cos_term, Qdiv.
      assert (Hqp : q_pow q (2 * Datatypes.S n) == q_pow 0 (2 * Datatypes.S n))
        by exact (qeqT_imp_qeq _ _ (q_pow_wd q 0 (2 * Datatypes.S n) Hz)).
      rewrite Hqp.
      assert (Hq0 : q_pow 0 (2 * Datatypes.S n) == 0) by reflexivity.
      rewrite Hq0. rewrite Qmult_0_l. apply Qmult_0_r. }
    rewrite Hterm. reflexivity.
Qed.

Lemma sce_sin_partial_at_zero : forall (q : Q) (n : nat), QeqT q 0 ->
  QeqT (sin_partial n q) 0.
Proof.
  intros q n Hz. apply qeq_imp_qeqT.
  induction n as [| n IH].
  - simpl. unfold sin_term, Qdiv.
    assert (Hqp : q_pow q 1 == q_pow 0 1)
      by exact (qeqT_imp_qeq _ _ (q_pow_wd q 0 1 Hz)).
    rewrite Hqp.
    assert (Hq0 : q_pow 0 1 == 0) by reflexivity.
    rewrite Hq0. rewrite Qmult_0_l. apply Qmult_0_r.
  - change (sin_partial (Datatypes.S n) q)
      with (sin_partial n q + sin_term (Datatypes.S n) q)%Q.
    rewrite IH.
    assert (Hterm : sin_term (Datatypes.S n) q == 0).
    { unfold sin_term, Qdiv.
      assert (Hqp : q_pow q (Datatypes.S (2 * Datatypes.S n)) == q_pow 0 (Datatypes.S (2 * Datatypes.S n)))
        by exact (qeqT_imp_qeq _ _ (q_pow_wd q 0 (Datatypes.S (2 * Datatypes.S n)) Hz)).
      rewrite Hqp.
      assert (Hq0 : q_pow 0 (Datatypes.S (2 * Datatypes.S n)) == 0) by reflexivity.
      rewrite Hq0. rewrite Qmult_0_l. apply Qmult_0_r. }
    rewrite Hterm. reflexivity.
Qed.

(* C.4 Q-layer cos tail bound: 0 <= q <= 1, n <= k implies
   |cos_partial k q - cos_partial n q| <= 2 * T_n(q)
   (direct from sc_cos_diff_bound2 at y := B := q; the geometric premise
   2q <= 2 <= t+1 closes by q <= 1 and t >= S(2n) >= 1). *)
Lemma sce_cos_partial_tail_le : forall (q : Q) (n k : nat),
  QleT' 0 q -> QleT' q 1 -> NatLe n k ->
  QleT' (Qabs (cos_partial k q - cos_partial n q))
        (sce_cos_tail q n * (1 + 1)%Q).
Proof.
  intros q n k Hq0 Hq1 Hnk.
  assert (Hq0Q : Qle 0 q) by (apply QleT'_to_Qle; exact Hq0).
  assert (Hq1Q : Qle q 1) by (apply QleT'_to_Qle; exact Hq1).
  assert (HnkQ : (n <= k)%nat) by (apply NatLe_drop; exact Hnk).
  apply (sc_cos_diff_bound2 q q n k).
  - exact Hq0Q.
  - rewrite (Qabs_pos q Hq0Q). apply Qle_refl.
  - intros t Ht.
    assert (Hz : Qle 0 ((1 + 1)%Q)) by (unfold Qle; simpl; lia).
    apply (Qle_trans _ (q * (1 + 1))).
    + rewrite (Qmult_comm (1 + 1) q). apply Qle_refl.
    + apply (Qle_trans _ ((1 + 1) * 1)%Q).
      * assert (Hr : (1 + 1) * 1 == 1 * (1 + 1)) by ring.
        rewrite Hr.
        apply (Qmult_le_compat_r q 1 (1 + 1)).
        -- exact Hq1Q.
        -- exact Hz.
      * assert (Heq : (1 + 1) * 1 == 1 + 1) by ring.
        rewrite Heq. apply QleT'_to_Qle. apply (sce_two_le_nat_q t).
        apply NatLe_lift. lia.
  - exact HnkQ.
Qed.

(* C.5 Q-layer sin tail bound (direct from sc_sin_diff_bound2 at
   y := B := q; the bound exponent equals the cos one, S(2n), which is
   the shape the source module already has). *)
Lemma sce_sin_partial_tail_le : forall (q : Q) (n k : nat),
  QleT' 0 q -> QleT' q 1 -> NatLe n k ->
  QleT' (Qabs (sin_partial k q - sin_partial n q))
        (sce_cos_tail q n * (1 + 1)%Q).
Proof.
  intros q n k Hq0 Hq1 Hnk.
  assert (Hq0Q : Qle 0 q) by (apply QleT'_to_Qle; exact Hq0).
  assert (Hq1Q : Qle q 1) by (apply QleT'_to_Qle; exact Hq1).
  assert (HnkQ : (n <= k)%nat) by (apply NatLe_drop; exact Hnk).
  apply (sc_sin_diff_bound2 q q n k).
  - exact Hq0Q.
  - rewrite (Qabs_pos q Hq0Q). apply Qle_refl.
  - intros t Ht.
    assert (Hz : Qle 0 ((1 + 1)%Q)) by (unfold Qle; simpl; lia).
    apply (Qle_trans _ (q * (1 + 1))).
    + rewrite (Qmult_comm (1 + 1) q). apply Qle_refl.
    + apply (Qle_trans _ ((1 + 1) * 1)%Q).
      * assert (Hr : (1 + 1) * 1 == 1 * (1 + 1)) by ring.
        rewrite Hr.
        apply (Qmult_le_compat_r q 1 (1 + 1)).
        -- exact Hq1Q.
        -- exact Hz.
      * assert (Heq : (1 + 1) * 1 == 1 + 1) by ring.
        rewrite Heq. apply QleT'_to_Qle. apply (sce_two_le_nat_q t).
        apply NatLe_lift. lia.
  - exact HnkQ.
Qed.

(* C.6 Core arithmetic: |diff| <= 2T and 0 < T imply T/2 < 3T - |diff|
   (the QltT certificate supplying the separating quantity delta := T/2
   of real_lt). *)
Lemma sce_gap_arith : forall (T diff : Q),
  QltT 0 T -> QleT' (Qabs diff) (T * (1 + 1)%Q) ->
  QltT (T * (1 # 2)) (3 * T - Qabs diff).
Proof.
  intros T diff HT Hb.
  apply Qlt_to_QltT.
  assert (HTQ : Qlt 0 T) by (apply QltT_to_Qlt; exact HT).
  assert (HbQ : Qle (Qabs diff) (T * (1 + 1))) by (apply QleT'_to_Qle; exact Hb).
  assert (Hb2 : T * (1 + 1) == 2 * T) by ring.
  rewrite Hb2 in HbQ.
  (* half quantity positive: T/2 > 0 *)
  assert (Hhalf : Qlt 0 (T * (1 # 2))).
  { assert (Hpre : Qlt (0 * (1 # 2)) (T * (1 # 2)))
      by (apply (Qmult_lt_compat_r 0 T (1 # 2));
          [apply QltT_to_Qlt; exact sce_half_pos | exact HTQ]).
    rewrite Qmult_0_l in Hpre. exact Hpre. }
  (* T/2 < T: T/2 + 0 < T/2 + T/2 == T *)
  assert (Hsplit : T * (1 # 2) + T * (1 # 2) == T) by ring.
  assert (Hlt : Qlt (T * (1 # 2)) T).
  { assert (Hstep : T * (1 # 2) + 0 < T * (1 # 2) + T * (1 # 2))
      by exact (proj2 (Qplus_lt_r 0 (T * (1 # 2)) (T * (1 # 2))) Hhalf).
    rewrite Hsplit in Hstep. rewrite Qplus_0_r in Hstep. exact Hstep. }
  (* T <= 3T - |diff|: |diff| <= 2T gives T + |diff| <= T + 2T == 3T;
   rewrite the left end as T == (T + |diff|) - |diff| and transfer. *)
  assert (Hle2 : Qle (T + Qabs diff) (T + 2 * T))
    by exact (proj2 (Qplus_le_r (Qabs diff) (2 * T) T) HbQ).
  assert (Hle3 : Qle (T + Qabs diff) (3 * T)).
  { assert (Heq : T + 2 * T == 3 * T) by ring.
    apply (Qle_trans _ (T + 2 * T)).
    - exact Hle2.
    - rewrite Heq. apply Qle_refl. }
  apply (Qlt_le_trans (T * (1 # 2)) T (3 * T - Qabs diff)).
  - exact Hlt.
  - assert (Hid : T == T + Qabs diff - Qabs diff) by ring.
    rewrite Hid at 1.
    exact (proj2 (Qplus_le_l (T + Qabs diff) (3 * T) (- Qabs diff)) Hle3).
Qed.

(* C.7 G2 main face: the cos Real tail in Bishop form -
   |cauchy_real_cos(real_const q) - S_n(q)| <=_B 3 * T_n(q), q in [0,1].
   Construction: the q == 0 branch closes exactly through real_eq (the
   cos_partial k 0 == 1 identity); the 0 < q branch carries the real_lt
   certificate delta := T_n/2 (C.6) with final index N := n and the
   pointwise bound from C.4; the right end + eps shifts by
   real_lt_plus_r_zero. *)
Theorem sce_cos_real_tail_B : forall (q : Q) (n : nat),
  QleT' 0 q -> QleT' q 1 ->
  real_le_b (real_abs (real_plus (cauchy_real_cos (real_const q))
                                 (real_opp (real_const (cos_partial n q)))))
            (real_const (3 * sce_cos_tail q n)).
Proof.
  intros q n Hq0 Hq1. apply real_le_closure_b_one. intros eps Heps.
  assert (Hq0Q : Qle 0 q) by (apply QleT'_to_Qle; exact Hq0).
  destruct (Qlt_bool 0 q) eqn:Hb.
  - (* Qlt_bool 0 q = true gives 0 < q: real_lt certificate delta := T_n/2 (inl branch) *)
    assert (Hpz : Qlt 0 q).
    { unfold Qlt_bool in Hb.
      destruct (Qcompare 0 q) eqn:E; try discriminate Hb.
      apply Qlt_alt. exact E. }
    assert (HT : QltT 0 (sce_cos_tail q n)).
    { apply (sce_cos_tail_pos q). apply Qlt_to_QltT. exact Hpz. }
    assert (HTQ : Qlt 0 (sce_cos_tail q n)) by (apply QltT_to_Qlt; exact HT).
    assert (Hhalf : Qlt 0 (sce_cos_tail q n * (1 # 2))).
    { assert (Hpre : Qlt (0 * (1 # 2)) (sce_cos_tail q n * (1 # 2)))
        by (apply (Qmult_lt_compat_r 0 (sce_cos_tail q n) (1 # 2));
            [apply QltT_to_Qlt; exact sce_half_pos | exact HTQ]).
      rewrite Qmult_0_l in Hpre. exact Hpre. }
    apply RealSetoid.real_lt_le_iff_req. apply inl.
    apply (real_lt_trans
             (real_abs (real_plus (cauchy_real_cos (real_const q))
                                  (real_opp (real_const (cos_partial n q)))))
             (real_const (3 * sce_cos_tail q n))
             (real_plus (real_const (3 * sce_cos_tail q n)) eps)).
    + unfold real_lt.
      exists (sce_cos_tail q n * (1 # 2)). split.
      * apply Qlt_to_QltT. exact Hhalf.
      * exists n. intros k Hk.
        apply Qlt_to_QltT.
        rewrite (qeqT_imp_qeq _ _ (real_const_proj
                   (3 * sce_cos_tail q n) k)).
        rewrite (qeqT_imp_qeq _ _ (real_abs_proj _ k)).
        rewrite (qeqT_imp_qeq _ _ (real_plus_proj _ _ k)).
        rewrite (qeqT_imp_qeq _ _ (real_opp_proj _ k)).
        rewrite (qeqT_imp_qeq _ _ (real_cos_proj (real_const q) k)).
        rewrite (qeqT_imp_qeq _ _ (real_const_proj q k)).
        rewrite (qeqT_imp_qeq _ _ (real_const_proj (cos_partial n q) k)).
        apply QltT_to_Qlt.
        apply (sce_gap_arith (sce_cos_tail q n)
                             (cos_partial k q - cos_partial n q)).
        -- exact HT.
        -- apply (sce_cos_partial_tail_le q n k Hq0 Hq1). exact Hk.
    + apply real_lt_plus_r_zero. exact Heps.
  - (* Qlt_bool 0 q = false: with 0 <= q this gives q == 0; the projected
       difference is identically 0 and real_eq closes the branch exactly. *)
    assert (Hz : q == 0).
    { destruct (Qle_lt_or_eq 0 q Hq0Q) as [Hlt0 | Hc].
      - exfalso.
        unfold Qlt_bool, Qcompare in Hb.
        rewrite (proj2 (Qlt_alt 0 q) Hlt0) in Hb.
        simpl in Hb. discriminate Hb.
      - exact (Qeq_sym 0 q Hc). }
    assert (HzT : QeqT q 0) by (apply qeq_imp_qeqT; exact Hz).
    apply RealSetoid.real_lt_le_iff_req. apply inl.
    apply (RealSetoid.real_lt_id_l
             (real_abs (real_plus (cauchy_real_cos (real_const q))
                                  (real_opp (real_const (cos_partial n q)))))
             real_zero (real_plus (real_const (3 * sce_cos_tail q n)) eps)).
    + (* |difference| == 0 == real_zero (q == 0 identity closure) *)
      apply real_eq_of_zero_diff. intro k.
      apply qeq_imp_qeqT.
      rewrite (qeqT_imp_qeq _ _ (real_abs_proj _ k)).
      rewrite (qeqT_imp_qeq _ _ (real_plus_proj _ _ k)).
      rewrite (qeqT_imp_qeq _ _ (real_opp_proj _ k)).
      rewrite (qeqT_imp_qeq _ _ (real_cos_proj (real_const q) k)).
      rewrite (qeqT_imp_qeq _ _ (real_const_proj q k)).
      rewrite (qeqT_imp_qeq _ _ (real_const_proj (cos_partial n q) k)).
      rewrite (qeqT_imp_qeq _ _ (sce_cos_partial_at_zero q k HzT)).
      rewrite (qeqT_imp_qeq _ _ (sce_cos_partial_at_zero q n HzT)).
      assert (Hrz : projT1 real_zero k == 0) by reflexivity.
      rewrite Hrz. simpl. reflexivity.
    + (* real_lt real_zero (real_const c + eps): right-end transfer plus
         real_lt_plus_r_zero *)
      apply (RealSetoid.real_lt_id_r real_zero
               (real_plus real_zero eps)
               (real_plus (real_const (3 * sce_cos_tail q n)) eps)).
      * apply (RealSetoid.real_eq_plus_compat real_zero eps
                 (real_const (3 * sce_cos_tail q n)) eps).
        -- apply real_eq_of_zero_diff. intro k.
           apply qeq_imp_qeqT.
           rewrite (qeqT_imp_qeq _ _
                      (real_const_proj (3 * sce_cos_tail q n) k)).
           assert (Hrz : projT1 real_zero k == 0) by reflexivity.
           rewrite Hrz.
           rewrite (qeqT_imp_qeq _ _ (sce_cos_tail_at_zero q n HzT)).
           reflexivity.
        -- apply real_eq_refl.
      * exact (real_lt_plus_r_zero real_zero eps Heps).
Qed.

(* C.8 G2 twin: the sin Real tail in Bishop form (same shape as C.7,
   swapping real_sin_proj / sc_sin_diff_bound2 / sce_sin_partial_at_zero). *)
Theorem sce_sin_real_tail_B : forall (q : Q) (n : nat),
  QleT' 0 q -> QleT' q 1 ->
  real_le_b (real_abs (real_plus (cauchy_real_sin (real_const q))
                                 (real_opp (real_const (sin_partial n q)))))
            (real_const (3 * sce_cos_tail q n)).
Proof.
  intros q n Hq0 Hq1. apply real_le_closure_b_one. intros eps Heps.
  assert (Hq0Q : Qle 0 q) by (apply QleT'_to_Qle; exact Hq0).
  destruct (Qlt_bool 0 q) eqn:Hb.
  - (* Qlt_bool 0 q = true gives 0 < q: real_lt certificate delta := T_n/2 (inl branch) *)
    assert (Hpz : Qlt 0 q).
    { unfold Qlt_bool in Hb.
      destruct (Qcompare 0 q) eqn:E; try discriminate Hb.
      apply Qlt_alt. exact E. }
    assert (HT : QltT 0 (sce_cos_tail q n)).
    { apply (sce_cos_tail_pos q). apply Qlt_to_QltT. exact Hpz. }
    assert (HTQ : Qlt 0 (sce_cos_tail q n)) by (apply QltT_to_Qlt; exact HT).
    assert (Hhalf : Qlt 0 (sce_cos_tail q n * (1 # 2))).
    { assert (Hpre : Qlt (0 * (1 # 2)) (sce_cos_tail q n * (1 # 2)))
        by (apply (Qmult_lt_compat_r 0 (sce_cos_tail q n) (1 # 2));
            [apply QltT_to_Qlt; exact sce_half_pos | exact HTQ]).
      rewrite Qmult_0_l in Hpre. exact Hpre. }
    apply RealSetoid.real_lt_le_iff_req. apply inl.
    apply (real_lt_trans
             (real_abs (real_plus (cauchy_real_sin (real_const q))
                                  (real_opp (real_const (sin_partial n q)))))
             (real_const (3 * sce_cos_tail q n))
             (real_plus (real_const (3 * sce_cos_tail q n)) eps)).
    + unfold real_lt.
      exists (sce_cos_tail q n * (1 # 2)). split.
      * apply Qlt_to_QltT. exact Hhalf.
      * exists n. intros k Hk.
        apply Qlt_to_QltT.
        rewrite (qeqT_imp_qeq _ _ (real_const_proj
                   (3 * sce_cos_tail q n) k)).
        rewrite (qeqT_imp_qeq _ _ (real_abs_proj _ k)).
        rewrite (qeqT_imp_qeq _ _ (real_plus_proj _ _ k)).
        rewrite (qeqT_imp_qeq _ _ (real_opp_proj _ k)).
        rewrite (qeqT_imp_qeq _ _ (real_sin_proj (real_const q) k)).
        rewrite (qeqT_imp_qeq _ _ (real_const_proj q k)).
        rewrite (qeqT_imp_qeq _ _ (real_const_proj (sin_partial n q) k)).
        apply QltT_to_Qlt.
        apply (sce_gap_arith (sce_cos_tail q n)
                             (sin_partial k q - sin_partial n q)).
        -- exact HT.
        -- apply (sce_sin_partial_tail_le q n k Hq0 Hq1). exact Hk.
    + apply real_lt_plus_r_zero. exact Heps.
  - (* Qlt_bool 0 q = false: with 0 <= q this gives q == 0; the projected
       difference is identically 0 and real_eq closes the branch exactly. *)
    assert (Hz : q == 0).
    { destruct (Qle_lt_or_eq 0 q Hq0Q) as [Hlt0 | Hc].
      - exfalso.
        unfold Qlt_bool, Qcompare in Hb.
        rewrite (proj2 (Qlt_alt 0 q) Hlt0) in Hb.
        simpl in Hb. discriminate Hb.
      - exact (Qeq_sym 0 q Hc). }
    assert (HzT : QeqT q 0) by (apply qeq_imp_qeqT; exact Hz).
    apply RealSetoid.real_lt_le_iff_req. apply inl.
    apply (RealSetoid.real_lt_id_l
             (real_abs (real_plus (cauchy_real_sin (real_const q))
                                  (real_opp (real_const (sin_partial n q)))))
             real_zero (real_plus (real_const (3 * sce_cos_tail q n)) eps)).
    + (* |difference| == 0 == real_zero (q == 0 identity closure) *)
      apply real_eq_of_zero_diff. intro k.
      apply qeq_imp_qeqT.
      rewrite (qeqT_imp_qeq _ _ (real_abs_proj _ k)).
      rewrite (qeqT_imp_qeq _ _ (real_plus_proj _ _ k)).
      rewrite (qeqT_imp_qeq _ _ (real_opp_proj _ k)).
      rewrite (qeqT_imp_qeq _ _ (real_sin_proj (real_const q) k)).
      rewrite (qeqT_imp_qeq _ _ (real_const_proj q k)).
      rewrite (qeqT_imp_qeq _ _ (real_const_proj (sin_partial n q) k)).
      rewrite (qeqT_imp_qeq _ _ (sce_sin_partial_at_zero q k HzT)).
      rewrite (qeqT_imp_qeq _ _ (sce_sin_partial_at_zero q n HzT)).
      assert (Hrz : projT1 real_zero k == 0) by reflexivity.
      rewrite Hrz. simpl. reflexivity.
    + (* real_lt real_zero (real_const c + eps): right-end transfer plus
         real_lt_plus_r_zero *)
      apply (RealSetoid.real_lt_id_r real_zero
               (real_plus real_zero eps)
               (real_plus (real_const (3 * sce_cos_tail q n)) eps)).
      * apply (RealSetoid.real_eq_plus_compat real_zero eps
                 (real_const (3 * sce_cos_tail q n)) eps).
        -- apply real_eq_of_zero_diff. intro k.
           apply qeq_imp_qeqT.
           rewrite (qeqT_imp_qeq _ _
                      (real_const_proj (3 * sce_cos_tail q n) k)).
           assert (Hrz : projT1 real_zero k == 0) by reflexivity.
           rewrite Hrz.
           rewrite (qeqT_imp_qeq _ _ (sce_cos_tail_at_zero q n HzT)).
           reflexivity.
        -- apply real_eq_refl.
      * exact (real_lt_plus_r_zero real_zero eps Heps).
Qed.

(* ============================================================ *)
(* Assumption audit: Print Assumptions on the main faces         *)
(* (expected all Closed - the module adds none).                 *)
(* ============================================================ *)
Print Assumptions sce_real_le_eps_face.
Print Assumptions sce_real_sin_le_x_eps.
Print Assumptions sce_real_cos_le_one_eps.
Print Assumptions sce_real_x_minus_cube_le_sin_eps.
Print Assumptions sce_real_one_minus_half_le_cos_eps.
Print Assumptions sce_real_sin_le_x_B.
Print Assumptions sce_real_cos_le_one_B.
Print Assumptions sce_real_x_minus_cube_le_sin_B.
Print Assumptions sce_real_one_minus_half_le_cos_B.
Print Assumptions sce_cos_partial_tail_le.
Print Assumptions sce_sin_partial_tail_le.
Print Assumptions sce_cos_real_tail_B.
Print Assumptions sce_sin_real_tail_B.
