(* ============================================================
   UpReqPadeTransport.v -- the Q-to-Real transport bridge family:
   carries the Q-layer Pade bounds into the Real-layer cauchy_real_exp
   eps/Bishop form, giving Real-layer exp bounds with Pade precision.
   Mission. G1 qtr_embed_mono / qtr_embed_le -- the Q-to-Real embedding
   order bridges (QltT a b implies real_const a < real_const b;
   witnesses eps := (b-a)/2, N := 0). G1 qtr_exp_gt_partial /
   qtr_exp_ge_partial -- the series bridge: the eps/Bishop order between
   the Real-layer e^y and the embedding of the n-th partial sum
   (witnesses eps := (y^(n+1)/(n+1)!)/2, N := n+1). G2
   qtr_mult_eq_compat_l plus qtr_pade_lower_real -- the transport engine
   and the first Real-layer Pade-precision lower bound (the check value
   is an arbitrary w congruent to e^y; the multiplied-out division-free
   form consumes cpl_lower_even). G2b qtr_pade_lower_extract -- the
   certificate reflection: the real_lt witness of cpl is unpacked into
   an explicit N/eps pointwise QltT form.
   Dependencies. UpReqPadeExp (pade_num/pade_den), UpReqQExpTail
   (the qtail family), UpReqPadeLower (cpl_lower_even family), DTPT_Bridge,
   S01_BaseRing, S02_CauchyComplete, S03_QExp, S07_RealSetoidExpLog;
   read-only Requires, no source changes.
   Constructivity. Every piece is expected Closed under Print
   Assumptions; purely constructive, zero LPO, zero classical
   limit/integral properties; Set-layer assumption positions all go
   through QltT/QleT (the S01 Set order), no Prop positions.
   Proof style. Division avoidance = multiplied-out form plus the
   Qmult_inv_r certificate (the in-library cpl precedent); Qeq transfer
   chains always use named asserts with apply-with, no proof-slot
   placeholders (not inferable at elaboration).
   Build. coqc -q -Q <Live tree> "" UpReqPadeTransport.v
   ============================================================ *)

Require Import UpReqPadeExp.
Require Import UpReqQExpTail.
Require Import UpReqPadeLower.
From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith Lia Setoid.
Require Import DTPT_Bridge.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S01_BaseRing.
Require Import S07_RealSetoidExpLog.

(* ============================================================ *)
(* B0 bridge pieces: small Q-layer combinators (self-contained, zero external dependencies) *)
(* ============================================================ *)

(* a < b implies 0 < b - a (QltT face).
   Proof route: Qplus_lt_r (z+x < z+y iff x < y with z := -a) plus
   Qplus_opp_r / Qplus_comm setoid recasts; Qminus b a is definitionally
   b + (-a). (destruct-lia is not viable: the denominator positivity is
   outside lia's reachable face.) *)
Lemma qtr_qlt_sub : forall a b : Q, QltT a b -> QltT 0 (b - a).
Proof.
  intros a b H.
  assert (Hlt : Qlt a b) by (apply QltT_to_Qlt; exact H).
  assert (H1 : Qlt (- a + a) (- a + b)).
  { exact (proj2 (Qplus_lt_r a b (- a)) Hlt). }
  apply Qlt_to_QltT.
  setoid_rewrite (Qplus_comm (- a) a) in H1.
  setoid_rewrite (Qplus_opp_r a) in H1.
  setoid_rewrite (Qplus_comm (- a) b) in H1.
  exact H1.
Qed.

(* 0 < x implies x/2 < x (strict halving contraction).
   destruct-lia: H has the polynomial form 0 < nx*dx and the goal is
   -(nx*dx) < 2*(nx*dx), linear in P := nx*dx (micromega ring
   normalization; same family as cpl_qlt_le). *)
Lemma qtr_div2_lt : forall x : Q, Qlt 0 x -> Qlt (x / 2) x.
Proof.
  intro x. unfold Qlt in *.
  destruct x as [nx dx]. simpl in *. lia.
Qed.

Lemma qtr_div2_ltT : forall x : Q, QltT 0 x -> QltT (x / 2) x.
Proof.
  intros x H. apply Qlt_to_QltT. apply qtr_div2_lt.
  apply QltT_to_Qlt. exact H.
Qed.

(* Cancellation certificate: m != 0 implies (a/m)*m == a (Qmult_inv_r, zero division-goal face) *)
Lemma qtr_div_cancel : forall a m : Q, ~ (m == 0) -> a / m * m == a.
Proof.
  intros a m Hm. unfold Qdiv.
  rewrite <- (Qmult_assoc a (/ m) m).
  rewrite (Qmult_comm (/ m) m).
  rewrite (Qmult_inv_r m Hm).
  apply Qmult_1_r.
Qed.

(* ============================================================ *)
(* G1(1) embedding order bridge: Q-layer order implies Real-layer embedding order *)
(* ============================================================ *)

(* Strict form: a < b implies real_const a < real_const b.
   Witness eps := (b-a)/2 > 0 and N := 0 (pointwise congruence of the constant sequence). *)
Theorem qtr_embed_mono : forall a b : Q, QltT a b ->
  real_lt (real_const a) (real_const b).
Proof.
  intros a b Hab.
  assert (Hsub : QltT 0 (b - a)) by (apply qtr_qlt_sub; exact Hab).
  assert (Hhalf : QltT ((b - a) / 2) (b - a)) by (apply qtr_div2_ltT; exact Hsub).
  unfold real_lt.
  exists ((b - a) / 2)%Q. split.
  - apply qltT_div_pos.
    + exact Hsub.
    + exact qltT_0_2.
  - exists 0%nat. intros n _.
    assert (Hraw : projT1 (real_const b) n - projT1 (real_const a) n
                   == b - a).
    { apply Qminus_comp; apply qeqT_imp_qeq; apply real_const_proj. }
    apply qltT_eq_compat_r with (a' := (b - a)%Q).
    + exact (qeq_imp_qeqT _ _ Hraw).
    + exact Hhalf.
Qed.

(* Weak form: a <= b implies real_const a <= real_const b (the real_le three-form:
   the strict branch goes through the embedding bridge; the Id-equality branch goes through the Qabs zero congruence). *)
Theorem qtr_embed_le : forall a b : Q, QleT a b ->
  real_le (real_const a) (real_const b).
Proof.
  intros a b Hab. destruct Hab as [Hlt | H0].
  - left. apply qtr_embed_mono. exact Hlt.
  - right. intros eps Heps. exists 0%nat. intros n _.
    assert (Hab0 : a - b == 0).
    { destruct H0. ring. }
    assert (Habs0 : Qabs (projT1 (real_const a) n
                          - projT1 (real_const b) n) == 0).
    { apply Qeq_trans with (y := Qabs (a - b)).
      - apply Qabs_wd. apply Qminus_comp; apply qeqT_imp_qeq; apply real_const_proj.
      - apply Qeq_trans with (y := Qabs 0).
        + apply Qabs_wd. exact Hab0.
        + apply Qeq_refl. }
    apply qltT_eq_compat_l with (a := 0%Q).
    + exact (qeq_imp_qeqT _ _ (Qeq_sym _ _ Habs0)).
    + exact Heps.
Qed.

(* ============================================================ *)
(* G1(2) series pier: the Q-layer partial-sum tail-difference lower bound (the Q kernel of e^y >= partial sum) *)
(* ============================================================ *)

(* Tail first-term lower bound: 0 <= y and d >= 0 imply
   y^{n+1}/(n+1)! ≤ E_{n+1+d}(y) − E_n(y)。
   Induction invariant: each step appends the nonnegative term y^k/k! (q_pow_fact_nonneg). *)
Lemma qtr_partial_gap : forall (y : Q) (n d : nat), QleT 0 y ->
  Qle (q_pow y (Datatypes.S n) / q_fact (Datatypes.S n))
      (exp_partial (Datatypes.S n + d) y - exp_partial n y).
Proof.
  intros y n d Hy. revert d.
  assert (Hy0 : Qle 0 y) by (apply qtail_QleT_to_Qle; exact Hy).
  induction d as [| d IH].
  - replace (Datatypes.S n + 0)%nat with (Datatypes.S n)%nat by lia.
    change (exp_partial (Datatypes.S n) y) with
      (exp_partial n y + q_pow y (Datatypes.S n) / q_fact (Datatypes.S n)).
    (* Division atomization: ring does not consume Qdiv atoms (the in-library pitfall) *)
    set (T := q_pow y (Datatypes.S n) / q_fact (Datatypes.S n)).
    apply QleT'_to_Qle. apply qeq_leT'. apply qeq_imp_qeqT. ring.
  - replace (Datatypes.S n + Datatypes.S d)%nat
      with (Datatypes.S (Datatypes.S n + d))%nat by lia.
    change (exp_partial (Datatypes.S (Datatypes.S n + d)) y) with
      (exp_partial (Datatypes.S n + d) y
       + q_pow y (Datatypes.S (Datatypes.S n + d))
         / q_fact (Datatypes.S (Datatypes.S n + d))).
    set (T2 := q_pow y (Datatypes.S (Datatypes.S n + d))
                 / q_fact (Datatypes.S (Datatypes.S n + d))).
    apply (Qle_trans _
             ((exp_partial (Datatypes.S n + d) y - exp_partial n y) + T2)%Q _).
    + (* first term <= old tail difference <= old tail difference + the nonneg new term *)
      apply (Qle_trans _ (exp_partial (Datatypes.S n + d) y - exp_partial n y) _).
      * exact IH.
      * apply QleT'_to_Qle. apply qtail_le_plus_r.
        unfold T2. apply QleT'_to_Qle. apply q_pow_fact_nonneg. apply Qle_to_QleT'. exact Hy0.
    + (* recast: (E - F) + T2 == E + T2 - F (ring, division atomized) *)
      apply QleT'_to_Qle. apply qeq_leT'. apply qeq_imp_qeqT. ring.
Qed.

(* ============================================================ *)
(* G1(2) series bridge: Real-layer e^y >= the n-th partial sum (eps/Bishop form) *)
(* ============================================================ *)

(* Strict form: y > 0 implies real_const(E_n(y)) < e^y.
   Witness eps := (y^(n+1)/(n+1)!)/2 > 0 and N := n+1; the pointwise
   difference E_m(y) - E_n(y) >= y^(n+1)/(n+1)! > eps (m >= n+1, tail
   difference increasing). *)
Theorem qtr_exp_gt_partial : forall (y : Q) (n : nat), QltT 0 y ->
  real_lt (real_const (exp_partial n y)) (cauchy_real_exp (real_const y)).
Proof.
  intros y n Hy.
  assert (Hterm : QltT 0 (q_pow y (Datatypes.S n) / q_fact (Datatypes.S n))).
  { apply qltT_div_pos.
    - exact (cpl_qpow_pos y (Datatypes.S n) (QltT_to_Qlt _ _ Hy)).
    - apply q_fact_pos. }
  unfold real_lt.
  exists (q_pow y (Datatypes.S n) / q_fact (Datatypes.S n) / 2)%Q.
  split.
  - apply qltT_div_pos.
    + exact Hterm.
    + exact qltT_0_2.
  - exists (Datatypes.S n). intros m Hm.
    assert (Hle : (Datatypes.S n <= m)%nat) by (apply NatLe_drop; exact Hm).
    assert (Hraw : projT1 (cauchy_real_exp (real_const y)) m
                   - projT1 (real_const (exp_partial n y)) m
                   == exp_partial m y - exp_partial n y).
    { apply Qminus_comp.
      - apply qeqT_imp_qeq; apply exp_const_proj.
      - apply qeqT_imp_qeq; apply real_const_proj. }
    assert (Hgap : Qle (q_pow y (Datatypes.S n) / q_fact (Datatypes.S n))
                       (exp_partial m y - exp_partial n y)).
    { replace m with (Datatypes.S n + (m - Datatypes.S n))%nat by lia.
      apply qtr_partial_gap.
      left. exact Hy. }
    assert (HgapT : QltT (q_pow y (Datatypes.S n) / q_fact (Datatypes.S n) / 2)
                         (exp_partial m y - exp_partial n y)).
    { apply Qlt_to_QltT.
      apply (Qlt_le_trans _ (q_pow y (Datatypes.S n) / q_fact (Datatypes.S n))).
      - apply qtr_div2_lt. apply QltT_to_Qlt. exact Hterm.
      - exact Hgap. }
    apply qltT_eq_compat_r with (a' := (exp_partial m y - exp_partial n y)%Q).
    + exact (qeq_imp_qeqT _ _ Hraw).
    + exact HgapT.
Qed.

(* Weak form: y >= 0 implies real_const(E_n(y)) <= e^y (the real_le three-form:
   the strict branch goes through the series bridge; the y == 0 branch
   goes through the real_eq congruence of the all-ones partial sum, with
   the Id branch discharged by destruct). *)
Theorem qtr_exp_ge_partial : forall (y : Q) (n : nat), QleT 0 y ->
  real_le (real_const (exp_partial n y)) (cauchy_real_exp (real_const y)).
Proof.
  intros y n Hy. destruct Hy as [Hlt | H0].
  - left. apply qtr_exp_gt_partial. exact Hlt.
  - assert (H0q : 0 == y) by (destruct H0; apply Qeq_refl).
    assert (Hn1 : exp_partial n y == 1%Q).
    { apply Qeq_trans with (y := exp_partial n 0).
      - apply Qeq_sym. apply qeqT_imp_qeq. apply (cpl_ep_ext n 0 y H0q).
      - apply qeqT_imp_qeq. apply exp_partial_zero. }
    assert (Hk1 : forall k : nat, exp_partial k y == 1%Q).
    { intro k. apply Qeq_trans with (y := exp_partial k 0).
      - apply Qeq_sym. apply qeqT_imp_qeq. apply (cpl_ep_ext k 0 y H0q).
      - apply qeqT_imp_qeq. apply exp_partial_zero. }
    right. intros eps Heps. exists 0%nat. intros k _.
    assert (Habs0 : Qabs (projT1 (real_const (exp_partial n y)) k
                          - projT1 (cauchy_real_exp (real_const y)) k) == 0).
    { apply Qeq_trans with (y := Qabs (1%Q - 1%Q)).
      - apply Qabs_wd.
        apply Qminus_comp.
        + apply Qeq_trans with (y := exp_partial n y).
          * apply qeqT_imp_qeq; apply real_const_proj.
          * exact Hn1.
        + apply Qeq_trans with (y := exp_partial k y).
          * apply qeqT_imp_qeq; apply exp_const_proj.
          * apply Hk1.
      - apply Qeq_trans with (y := Qabs 0).
        + apply Qabs_wd. ring.
        + apply Qeq_refl. }
    apply qltT_eq_compat_l with (a := 0%Q).
    + exact (qeq_imp_qeqT _ _ (Qeq_sym _ _ Habs0)).
    + exact Heps.
Qed.

(* ============================================================ *)
(* G2 core: left congruence of real_mult over real_eq (the transport engine) *)
(* ============================================================ *)

(* Cancellation certificate ready (qtr_div_cancel).
   Left congruence: x congruent z implies x*v congruent z*v (real_eq face).
   Proof route: real_norm_bounded takes |v| <= Mv with the halved slack eps/2:
   |u_n−z_n|·|w_n| ≤ (eps/2/Mv')·Mv' == eps/2 < eps
   (Qmult_le_compat_nonneg plus the Qmult_inv_r certificate; zero division-goal face). *)
Lemma qtr_mult_eq_compat_l : forall x z v : Real,
  real_eq x z -> real_eq (real_mult x v) (real_mult z v).
Proof.
  intros [u Hu] [z Hz] [w Hw] Heq eps Heps.
  destruct (real_norm_bounded (existT (fun s : Qseq => cauchy s) w Hw))
    as [Mv [HMvT HMv]].
  set (Mv' := (Qabs Mv + 1)%Q).
  assert (HMv'0 : Qlt 0 Mv').
  { unfold Mv'. setoid_rewrite <- (Qplus_comm 1%Q (Qabs Mv)).
    apply (Qlt_le_trans 0%Q 1%Q).
    - reflexivity.
    - apply Qle_plus_nonneg_r. apply Qabs_nonneg. }
  assert (HMv'posT : QltT 0 Mv') by (apply Qlt_to_QltT; exact HMv'0).
  (* Halving amplification: feed eps/2 into Heq; the tail eps/2 < eps restores strictness *)
  destruct (Heq (eps / 2 / Mv')
    (qltT_div_pos (eps / 2) Mv'
       (qltT_div_pos eps 2%Q Heps qltT_0_2) HMv'posT)) as [N HN].
  exists N. intros n Hn.
  specialize (HN n Hn).
  (* HN : QltT |u_n − z_n| (eps/2/Mv') *)
  assert (Hwn : Qle (Qabs (w n)) Mv').
  { apply (Qle_trans _ Mv _).
    - apply (QleT'_to_Qle _ _ (HMv n)).
    - apply (Qle_trans _ (Qabs Mv) _).
      + apply Qle_Qabs.
      + apply Qle_plus_nonneg_r.
        (* 0 <= 1: unfold Qle then lia (trivial at the Z layer) *)
        unfold Qle. simpl. lia. }
  assert (Hle2 : Qle (Qabs (u n - z n) * Qabs (w n))
                     ((eps / 2 / Mv') * Mv')).
  { apply (Qmult_le_compat_nonneg (Qabs (u n - z n))
             (eps / 2 / Mv')%Q (Qabs (w n)) Mv').
    - split.
      + apply Qabs_nonneg.
      + apply Qlt_le_weak. apply QltT_to_Qlt. exact HN.
    - split.
      + apply Qabs_nonneg.
      + exact Hwn. }
  assert (Hab : Qabs (u n * w n - z n * w n)
                == Qabs (u n - z n) * Qabs (w n)).
  { apply Qeq_trans with (y := Qabs ((u n - z n) * w n)).
    - apply Qabs_wd. ring.
    - apply Qabs_Qmult. }
  assert (Hchain : QltT (Qabs (u n - z n) * Qabs (w n)) eps).
  { apply Qlt_to_QltT.
    apply (Qle_lt_trans _ (eps / 2) eps).
    - apply (Qle_trans _ ((eps / 2 / Mv') * Mv')).
      + exact Hle2.
      + apply QleT'_to_Qle. apply qeq_leT'. apply qeq_imp_qeqT.
        apply qtr_div_cancel. intro Hmz.
        exact (match qtail_neq0 Mv' HMv'0 (qeq_imp_qeqT _ _ Hmz) with end).
    - apply qtr_div2_lt.
      apply QltT_to_Qlt. exact Heps. }
  apply qltT_eq_compat_l with (a := Qabs (u n - z n) * Qabs (w n)).
  - exact (S02_CauchyComplete.qeq_imp_qeqT _ _ (Qeq_sym _ _ Hab)).
  - exact Hchain.
Qed.

(* ============================================================ *)
(* G2 main piece: the first Real-layer Pade-precision lower bound (arbitrary check value) *)
(* ============================================================ *)

(* y > 0 and w congruent to e^y (an arbitrary Real check value in the real_eq sense) imply
   P2(y) < w*Q2(y) (the multiplied-out division-free form).
   Transport path: cpl_lower_even (the specific diagonal witness), then real_lt_eq_lt plus
   the real_mult left congruence (qtr_mult_eq_compat_l), then the arbitrary check value. *)
Theorem qtr_pade_lower_real : forall (y : Q) (w : Real), QltT 0 y ->
  real_eq w (cauchy_real_exp (real_const y)) ->
  real_lt (real_const (pade_num 2%nat y))
          (real_mult w (real_const (pade_den 2%nat y))).
Proof.
  intros y w Hy Hw.
  apply (real_lt_eq_lt _ _ _ (cpl_lower_even y Hy)).
  apply qtr_mult_eq_compat_l.
  apply real_eq_sym. exact Hw.
Qed.

(* ============================================================ *)
(* G2b reverse bridge: the real_lt certificate unpacked into the explicit N/eps pointwise QltT form *)
(*   the eps/Bishop witness reflection: the Real-layer statement implies the pointwise Q-layer precision ledger; *)
(*   N/eps are carried through verbatim from the cpl sigT witness: y^5/720, N := 6) *)
(* ============================================================ *)

Theorem qtr_pade_lower_extract : forall y : Q, QltT 0 y ->
  sigT (fun N : nat => sigT (fun eps : Q => And (QltT 0 eps)
    (forall m : nat, NatLe N m ->
      QltT eps (exp_partial m y * pade_den 2%nat y
                - pade_num 2%nat y)%Q))).
Proof.
  intros y Hy.
  destruct (cpl_lower_even y Hy) as [eps [Heps [N HN]]].
  exists N. exists eps. split.
  - exact Heps.
  - intros m Hm.
    specialize (HN m Hm).
    assert (Hmult : projT1 (real_mult (cauchy_real_exp (real_const y))
                                      (real_const (pade_den 2%nat y))) m
                    == exp_partial m y * pade_den 2%nat y).
    { apply Qeq_trans with
        (y := projT1 (cauchy_real_exp (real_const y)) m
              * projT1 (real_const (pade_den 2%nat y)) m).
      - apply qeqT_imp_qeq; apply real_mult_proj.
      - apply Qmult_comp.
        + apply qeqT_imp_qeq; apply exp_const_proj.
        + apply qeqT_imp_qeq; apply real_const_proj. }
    assert (Hconst : projT1 (real_const (pade_num 2%nat y)) m
                     == pade_num 2%nat y).
    { apply qeqT_imp_qeq; apply real_const_proj. }
    assert (Hraw : projT1 (real_mult (cauchy_real_exp (real_const y))
                                     (real_const (pade_den 2%nat y))) m
                   - projT1 (real_const (pade_num 2%nat y)) m
                   == exp_partial m y * pade_den 2%nat y
                      - pade_num 2%nat y).
    { apply Qminus_comp.
      - exact Hmult.
      - exact Hconst. }
    exact (qltT_eq_compat_r _ _ _ (qeq_imp_qeqT _ _ (Qeq_sym _ _ Hraw)) HN).
Qed.

(* Weak-form completion (the real_le three-form): y > 0 and w congruent to e^y imply P2(y) <= w*Q2(y). *)
Theorem qtr_pade_lower_real_le : forall (y : Q) (w : Real), QltT 0 y ->
  real_eq w (cauchy_real_exp (real_const y)) ->
  real_le (real_const (pade_num 2%nat y))
          (real_mult w (real_const (pade_den 2%nat y))).
Proof.
  intros y w Hy Hw. left.
  apply (qtr_pade_lower_real y w Hy Hw).
Qed.

(* ============================================================ *)
(* Certification face (assumption face: all pieces expected Closed) *)
(* ============================================================ *)

Print Assumptions qtr_embed_mono.
Print Assumptions qtr_embed_le.
Print Assumptions qtr_partial_gap.
Print Assumptions qtr_exp_gt_partial.
Print Assumptions qtr_exp_ge_partial.
Print Assumptions qtr_mult_eq_compat_l.
Print Assumptions qtr_pade_lower_real.
Print Assumptions qtr_pade_lower_extract.
Print Assumptions qtr_pade_lower_real_le.
