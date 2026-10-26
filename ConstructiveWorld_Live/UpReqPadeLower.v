(* ConstructiveWorld-Set — division-free positive lower bound for the Pade [2/2] exponential error remainder. *)

(** * UpReqPadeLower: division-free lower bound for the Pade [2/2] tail.

    Mission.  For [y > 0] the module proves
      [real_lt (real_const (pade_num 2 y))
                (real_mult (cauchy_real_exp (real_const y))
                           (real_const (pade_den 2 y)))]
      in the sigT witness form of [real_lt] with witness
      [eps := y^5/720] and index bound [N := 6]; the Q-layer kernel is
      the identity [exp_partial 6 y * pade_den 2 y - pade_num 2 y =
      y^5/720 + y^6/1440 + y^8/8640] with every term nonnegative.
      Main statements: [cpl_g6_identity], [cpl_den2_pos],
      [cpl_ep_mono], [cpl_lower_even].

    Dependencies.  Stdlib [QArith], [Arith], [Lia], [Setoid].  Requires
      [S01_BaseRing]-[S15_TailFEPUp] and [UpReqPadeExp],
      [UpReqQExpTail], [UpReqPadeQLeg].

    References.  This development, the ConstructiveWorld-Main baseline
      module of the same name whose statement names are carried over
      verbatim.

    Constructivity.  All named statements are carried by [Set]
      ([QltT]/[QleT']/[QeqT] and the sigT witness form of [real_lt]);
      positivity is witnessed pointwise with no excluded middle;
      [coqchk] reports [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" UpReqPadeLower.v]
      compiles cleanly; artifact magic [436f7121 00015ff4]. *)

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
Require Import UpReqPadeExp.
Require Import UpReqQExpTail.
Require Import UpReqPadeQLeg.
From Stdlib Require Import QArith.QArith Arith.Arith Lia Setoid.

Section PadeLower.

(* ===== B0 bridging lemmas (Qeq to Qlt transfer bridges; the monotone Q
   lemmas are rebuilt in place with one-step proofs, statements unchanged) ===== *)

(* Right-transfer under equality: [a == b] turns [Qlt 0 a] into [QltT 0 b] (self-contained). *)
Lemma cpl_qlt0_eq_r : forall a b : Q, a == b -> Qlt 0 a -> QltT 0 b.
Proof.
  intros a b Hab Ha.
  exact (pql_qlt0_eq_r a b Hab Ha).
Qed.

(* Left-transfer under equality: [x == a] turns [Qlt x b] into [QltT a b] (rewrites the strict term of the main theorem). *)
Lemma cpl_qlt_eq_l : forall x a b : Q, x == a -> Qlt x b -> QltT a b.
Proof.
  intros x a b Hxa Hlt.
  exact (pql_qlt_eq_l x a b Hxa Hlt).
Qed.

(* Qeq combinators for plus/minus/mult: the stdlib [QArith_base] Proper
   instances are applied directly as functions ([Qplus_comp]/[Qminus_comp]/
   [Qmult_comp]); no nonlinear arithmetic. *)
Lemma cpl_qplus_comp : forall w x y z : Q, w == x -> y == z -> QeqT (w + y) (x + z).
Proof. intros w x y z H1 H2. apply qeq_imp_qeqT. apply Qplus_comp; assumption. Qed.

Lemma cpl_qminus_comp : forall w x y z : Q, w == x -> y == z -> QeqT (w - y) (x - z).
Proof. intros w x y z H1 H2. apply qeq_imp_qeqT. apply Qminus_comp; assumption. Qed.

Lemma cpl_qmult_comp : forall w x y z : Q, w == x -> y == z -> QeqT (w * y) (x * z).
Proof. intros w x y z H1 H2. apply qeq_imp_qeqT. apply Qmult_comp; assumption. Qed.

(* Strict right-transfer: [a == b] implies [Qlt x a -> QltT x b]
   (a one-step bridge to the strict-transfer lemma of the predecessor file). *)
Lemma cpl_qlt_eq_sr : forall (x a b : Q), a == b -> Qlt x a -> QltT x b.
Proof.
  intros x a b Hab Ha.
  exact (pql_qlt_eq_r a b x Hab Ha).
Qed.

(* Powers are nonnegative: [0 <= y] implies [0 <= y^k] (base module of the pointwise monotonicity chain). *)
Lemma cpl_qpow_nonneg : forall (y : Q) (k : nat), Qle 0 y -> QleT' 0 (q_pow y k).
Proof.
  intros y k Hy. apply Qle_to_QleT'. induction k as [| k IH].
  - change (q_pow y 0%nat) with 1%Q. apply QleT'_to_Qle. apply Qle_0_1.
  - change (q_pow y (Datatypes.S k)) with (y * q_pow y k).
    apply Qmult_le_0_compat.
    + exact Hy.
    + exact IH.
Qed.

(* Powers are strictly positive: [0 < y] implies [0 < y^k] (the source of witness strictness). *)
Lemma cpl_qpow_pos : forall (y : Q) (k : nat), Qlt 0 y -> QltT 0 (q_pow y k).
Proof.
  intros y k Hy. apply Qlt_to_QltT. induction k as [| k IH].
  - change (q_pow y 0%nat) with 1%Q. unfold Qlt. simpl. lia.
  - change (q_pow y (Datatypes.S k)) with (y * q_pow y k).
    apply Qmult_lt_0_compat.
    + exact Hy.
    + exact IH.
Qed.

(* Strict implies weak: [Qlt x y -> QleT' x y] (self-contained; [Qlt] and [Qle] share the Z-level unfolding). *)
Lemma cpl_qlt_le : forall x y : Q, Qlt x y -> QleT' x y.
Proof.
  intros x y H. apply Qle_to_QleT'. unfold Qlt, Qle in *.
  destruct x as [nx dx]. destruct y as [ny dy]. simpl in *. lia.
Qed.

(* Squares are nonnegative: decided pointwise by [Qlt_le_dec] (no excluded middle); the negative branch uses the [-t * -t] dual. *)
Lemma cpl_sq_nonneg : forall t : Q, QleT' 0 (t * t).
Proof.
  intro t. apply Qle_to_QleT'.
  destruct t as [tn td].
  destruct (Qlt_le_dec 0 (tn#td)) as [Hlt | Hle].
  - apply QleT'_to_Qle. apply cpl_qlt_le. apply Qmult_lt_0_compat; exact Hlt.
  - assert (Hnn : Qle 0 (- (tn#td))).
    { unfold Qle, Qopp in *. simpl in Hle |- *. lia. }
    apply (Qle_trans 0 ((- (tn#td)) * (- (tn#td))) ((tn#td) * (tn#td))).
    + apply Qmult_le_0_compat; exact Hnn.
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
Qed.

(* ===== B1 numeric anchors (closed literal positions close by [vm_compute]) ===== *)

(* The coefficient formula, bounded sum and alternating sign, end to end. *)
Lemma cpl_sent_s_b1 : QeqT (pade_num 1%nat (1#2)) (5#4).
Proof. exact pade_num_1_half. Qed.

Lemma cpl_sent_s_b2 : QeqT (pade_den 1%nat (1#2)) (3#4).
Proof. exact pade_den_1_half. Qed.

(* Numeric cross-checks of the identity (exact fraction values). *)
Lemma cpl_sent_g6_half : QeqT
 (exp_partial 6%nat (1#2) * pade_den 2%nat (1#2)                          - pade_num 2%nat (1#2)) (121#2211840).
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Lemma cpl_sent_g6_one : QeqT
 (exp_partial 6%nat (1#1) * pade_den 2%nat (1#1)                         - pade_num 2%nat (1#1)) (19#8640).
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

(* Witness value: [beta_0 * y^5 = (1#720) * (1#2)^5 = 1#23040]. *)
Lemma cpl_sent_witness_half : QeqT (q_pow (1#2) 5%nat / 720) (1#23040).
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

(* Degenerate case [n = 0]: [E_0 == 1] (with [P_0 = Q_0 = 1] this is the
   [e^y - 1 >= y] face; a numeric anchor for the partial-sum base case). *)
Lemma cpl_sent_exp0 : forall y : Q, QeqT (exp_partial 0%nat y) (1%Q).
Proof. intro y. exact (qeq_imp_qeqT _ _ (Qeq_refl 1%Q)). Qed.

(* ===== B2 the Q-layer main algebra ===== *)

(* Closed form of the denominator at [n = 2]: the positivity lemma of the
   predecessor file covers [0,1] only; this instance covers all [y > 0]
   through [Q2(y) = 1 - y/2 + y^2/12 = ((y-3)^2 + 3)/12 > 0]. *)
Lemma cpl_den2_expl : forall y : Q,  
 QeqT (pade_den 2%nat y) (1%Q + (- (1#2)%Q) * y + (1#12)%Q * (y * y)).
Proof.
  intro y. apply qeq_imp_qeqT.
  unfold pade_den, pade_coeff.
  cbn [sum_upto q_pow q_fact Z.of_nat Nat.sub Nat.mul Nat.add]. cbv beta.
  field.
Qed.

Lemma cpl_den2_pos : forall y : Q, Qlt 0 y -> QltT 0 (pade_den 2%nat y).
Proof.
  intros y Hy. apply Qlt_to_QltT.
  assert (Hexpl : pade_den 2%nat y == 1%Q + (- (1#2)%Q) * y + (1#12)%Q * (y * y))
    by (apply qeqT_imp_qeq; apply cpl_den2_expl).
(* 12 * explicit form == (y-3)^2 + 3 > 0 *)
  assert (H12 : Qlt 0 (12 * (1%Q + - (1#2)%Q * y + (1#12)%Q * (y * y)))).
  { apply QltT_to_Qlt. apply (cpl_qlt0_eq_r ((y + -3) * (y + -3) + 3)
                         (12 * (1 + - (1#2) * y + (1#12) * (y * y)))).
    - field.
    - assert (Hsq : Qle 0 ((y + -3) * (y + -3))) by (apply QleT'_to_Qle; apply cpl_sq_nonneg).
      assert (H3 : Qlt 0 3%Q) by (unfold Qlt; simpl; lia).
      apply QltT_to_Qlt. apply (cpl_qlt0_eq_r (3 + (y + -3) * (y + -3))%Q
                           ((y + -3) * (y + -3) + 3)%Q).
      + ring.
      + apply (Qlt_le_trans 0 3%Q (3 + (y + -3) * (y + -3))%Q).
        * exact H3.
        * apply QleT'_to_Qle. apply (qtail_le_plus_r 3%Q ((y + -3) * (y + -3))). exact Hsq. }
(* From [Qlt 0 ((12 * E) * (1/12))] to [Qlt 0 pade_den] along the right-transfer bridge chain. *)
  apply QltT_to_Qlt.
  apply (cpl_qlt0_eq_r ((12 * (1 + - (1#2) * y + (1#12) * (y * y))) * (1#12))
                       (pade_den 2%nat y)).
  - transitivity (1%Q + - (1#2)%Q * y + (1#12)%Q * (y * y)).
    + unfold Qdiv. field.
    + apply Qeq_sym. exact Hexpl.
  - apply (Qmult_lt_0_compat _ (1#12)).
    + exact H12.
    + unfold Qlt. simpl. lia.
Qed.

(* Partial sums are nondecreasing: [0 <= y] implies [E_m <= E_(m+1)] (the Q-layer half of the main theorem). *)
Lemma cpl_ep_step_le : forall (y : Q) (m : nat), 
  Qle 0 y -> QleT' (exp_partial m y) (exp_partial (Datatypes.S m) y).
Proof.
  intros y m Hy.
  change (exp_partial (Datatypes.S m) y)
    with (exp_partial m y + q_pow y (Datatypes.S m) / q_fact (Datatypes.S m)).
  apply Qle_to_QleT'.
  apply QleT'_to_Qle. apply (qtail_le_plus_r (exp_partial m y) (q_pow y (Datatypes.S m) / q_fact (Datatypes.S m))).
  unfold Qdiv. apply Qmult_le_0_compat.
  - apply QleT'_to_Qle. apply (cpl_qpow_nonneg y (Datatypes.S m) Hy).
  - apply QleT'_to_Qle. apply cpl_qlt_le.
    apply (Qinv_lt_0_compat (q_fact (Datatypes.S m))).
    apply QltT_to_Qlt. apply q_fact_pos.
Qed.

(* Partial sums are monotone: [0 <= y] and [a <= b] imply [E_a <= E_b] (the Q-layer kernel of the [N := 6] slot). *)
Lemma cpl_ep_mono : forall (y : Q) (a b : nat), 
  Qle 0 y -> (a <= b)%nat -> QleT' (exp_partial a y) (exp_partial b y).
Proof.
  intros y a b Hy Hab.
  revert a Hab. induction b as [| b' IH].
  - intros a Hab. assert (Ha0 : a = 0%nat) by lia. subst a.
    apply Qle_to_QleT'. apply Qle_refl.
  - intros a Hab. destruct (Nat.eq_dec a (Datatypes.S b')) as [Heq | Hne].
    + rewrite Heq. apply Qle_to_QleT'. apply Qle_refl.
    + assert (Hab' : (a <= b')%nat) by lia.
      apply (qleT'_trans _ (exp_partial b' y)).
      * apply IH. exact Hab'.
      * apply (cpl_ep_step_le y b' Hy).
Qed.

(* Core identity: [E_6 * Q_2 - P_2] equals the division-free positive
   polynomial [y^5/720 + y^6/1440 + y^8/8640]. *)
Lemma cpl_g6_identity : forall y : Q, 
  QeqT (exp_partial 6%nat y * pade_den 2%nat y - pade_num 2%nat y)
 (q_pow y 5%nat / 720 + q_pow y 6%nat / 1440 + q_pow y 8%nat / 8640).
Proof.
  intro y. apply qeq_imp_qeqT.
  unfold pade_den, pade_num, pade_coeff.
  cbn [exp_partial sum_upto q_pow q_fact Z.of_nat Nat.sub Nat.mul Nat.add]. cbv beta.
  field.
Qed.

(* Powers respect equality: [a == b] implies [QeqT (q_pow a k) (q_pow b k)] (layerwise via [Qmult_comp]). *)
Lemma cpl_qpow_ext : forall (k : nat) (a b : Q), a == b -> QeqT (q_pow a k) (q_pow b k).
Proof.
  intros k a b Hab. apply qeq_imp_qeqT. induction k as [| k IH].
  - reflexivity.
  - apply Qmult_comp.
    + exact Hab.
    + exact IH.
Qed.

(* Partial sums respect equality: [a == b] implies [E_m(a) == E_m(b)] (lifts equality hypotheses into [exp_partial]). *)
Lemma cpl_ep_ext : forall (m : nat) (a b : Q), a == b -> QeqT (exp_partial m a) (exp_partial m b).
Proof.
  intros m a b Hab. apply qeq_imp_qeqT. induction m as [| m IH].
  - reflexivity.
  - apply Qplus_comp.
    + exact IH.
    + unfold Qdiv. apply qeqT_imp_qeq. apply cpl_qmult_comp.
      * change (q_pow a (Datatypes.S m)) with (a * q_pow a m).
        change (q_pow b (Datatypes.S m)) with (b * q_pow b m).
        apply qeqT_imp_qeq. apply cpl_qmult_comp.
        -- exact Hab.
        -- exact (qeqT_imp_qeq _ _ (cpl_qpow_ext m a b Hab)).
      * apply Qeq_refl.
Qed.

(* ===== C the Real-layer main theorem (division-free [real_lt] sigT witness form) ===== *)

(* Statement: [e^y * Q2(y) - P2(y) > beta_0 * y^5] with [beta_0 = 1/720];
   the sigT witness is [eps := y^5/720] with index [N := 6], both explicitly
   computable; the internal Q subtraction of [real_lt] needs no division
   face.  Reading: [P2 > 0] and [Q2 > 0] give [0 < e^y] and [e^y > P2/Q2]. *)
Theorem cpl_lower_even : forall y : Q,
  QltT 0 y ->
  real_lt (real_const (pade_num 2%nat y))
          (real_mult (cauchy_real_exp (real_const y)) (real_const (pade_den 2%nat y))).
Proof.
  intros y Hy.
  assert (Hylt : Qlt 0 y) by (apply QltT_to_Qlt; exact Hy).
  assert (Hy0 : Qle 0 y) by (apply QleT'_to_Qle; apply cpl_qlt_le; exact Hylt).
(* Pointwise construction over eps: open [real_const] and reduce projections pointwise. *)
  assert (Hc : forall k, projT1 (real_const y) k == y) by (intro k; apply qeqT_imp_qeq; apply real_const_proj).
  destruct (real_const y) as [u Hu] eqn:Eu.
(* The destruct above already rewrote [real_const y] inside [Hc]; reduce projections directly. *)
  cbn [projT1] in Hc.
  unfold real_lt.
  exists (q_pow y 5%nat / 720)%Q.
  split.
  - (* Witness positivity: [0 < y^5/720]. *)
    apply Qlt_to_QltT.
    apply (Qmult_lt_0_compat (q_pow y 5%nat) (1#720)).
    + apply QltT_to_Qlt. apply (cpl_qpow_pos y 5%nat Hylt).
    + apply (Qinv_lt_0_compat (720#1)). unfold Qlt. simpl. lia.
  - exists 6%nat.
    intros m Hm.
    assert (Hle : (6 <= m)%nat) by (apply NatLe_drop; exact Hm).
(* The projection assembly goes through qeq bridges: the [QltT] face admits
   no rewrite and has no setoid instance, so self-contained Qeq combinators
   with explicit [Qeq_trans] are used. *)
    assert (Hexp : projT1 (cauchy_real_exp (existT (fun s : Qseq => cauchy s) u Hu)) m
                   == exp_partial m (u m)).
    { unfold cauchy_real_exp. reflexivity. }
    assert (Hexp2 : projT1 (cauchy_real_exp (existT (fun s : Qseq => cauchy s) u Hu)) m
                    == exp_partial m y)
      by (apply (Qeq_trans _ (exp_partial m (u m)) _ Hexp (qeqT_imp_qeq _ _ (cpl_ep_ext m (u m) y (Hc m))))).
    assert (HDe : projT1 (real_mult (cauchy_real_exp (existT (fun s : Qseq => cauchy s) u Hu))
                                    (real_const (pade_den 2%nat y))) m
                    - projT1 (real_const (pade_num 2%nat y)) m
                  == exp_partial m y * pade_den 2%nat y - pade_num 2%nat y).
    { apply (Qeq_trans _
              (projT1 (cauchy_real_exp (existT (fun s : Qseq => cauchy s) u Hu)) m
                 * projT1 (real_const (pade_den 2%nat y)) m
                 - projT1 (real_const (pade_num 2%nat y)) m) _).
      - apply qeqT_imp_qeq. apply (cpl_qminus_comp
                 (projT1 (real_mult (cauchy_real_exp (existT (fun s : Qseq => cauchy s) u Hu))
                                    (real_const (pade_den 2%nat y))) m)
                 (projT1 (cauchy_real_exp (existT (fun s : Qseq => cauchy s) u Hu)) m
                    * projT1 (real_const (pade_den 2%nat y)) m)).
        + apply qeqT_imp_qeq. apply (real_mult_proj (cauchy_real_exp (existT (fun s : Qseq => cauchy s) u Hu))
                                (real_const (pade_den 2%nat y)) m).
        + apply Qeq_refl.
      - apply qeqT_imp_qeq. apply (cpl_qminus_comp
                 (projT1 (cauchy_real_exp (existT (fun s : Qseq => cauchy s) u Hu)) m
                    * projT1 (real_const (pade_den 2%nat y)) m)
                 (exp_partial m y * pade_den 2%nat y)).
        + apply qeqT_imp_qeq. apply (cpl_qmult_comp
                   (projT1 (cauchy_real_exp (existT (fun s : Qseq => cauchy s) u Hu)) m)
                   (exp_partial m y)
                   (projT1 (real_const (pade_den 2%nat y)) m) (pade_den 2%nat y)).
          * exact Hexp2.
          * apply qeqT_imp_qeq. apply (real_const_proj (pade_den 2%nat y) m).
        + apply qeqT_imp_qeq. apply (real_const_proj (pade_num 2%nat y) m). }
    assert (Hchain : Qlt (q_pow y 5%nat / 720)
                       (exp_partial m y * pade_den 2%nat y - pade_num 2%nat y)).
    { (* The Q-layer closing chain (a Prop derivation inside the proof). *)
    assert (Hident : exp_partial 6%nat y * pade_den 2%nat y - pade_num 2%nat y ==
                     q_pow y 5%nat / 720 + q_pow y 6%nat / 1440 + q_pow y 8%nat / 8640)
      by (apply qeqT_imp_qeq; apply cpl_g6_identity).
    assert (Hmono : Qle (exp_partial 6%nat y) (exp_partial m y))
      by (apply QleT'_to_Qle; apply (cpl_ep_mono y 6%nat m Hy0 Hle)).
    assert (Hden : Qle 0 (pade_den 2%nat y))
      by (apply QleT'_to_Qle; apply cpl_qlt_le; apply QltT_to_Qlt; apply cpl_den2_pos; exact Hylt).
    assert (Hstep1 : Qle (exp_partial 6%nat y * pade_den 2%nat y)
                         (exp_partial m y * pade_den 2%nat y))
      by (apply (Qmult_le_compat_r _ _ (pade_den 2%nat y)); assumption).
    assert (Hstep2 : Qle (exp_partial 6%nat y * pade_den 2%nat y - pade_num 2%nat y)
                         (exp_partial m y * pade_den 2%nat y - pade_num 2%nat y))
      by (apply (proj2 (Qplus_le_l _ _ (- pade_num 2%nat y))); exact Hstep1).
    assert (Hstep3 : Qle (q_pow y 5%nat / 720 + q_pow y 6%nat / 1440 + q_pow y 8%nat / 8640)
                         (exp_partial m y * pade_den 2%nat y - pade_num 2%nat y))
      by (apply (Qle_trans _ (exp_partial 6%nat y * pade_den 2%nat y - pade_num 2%nat y));
          [apply QleT'_to_Qle; apply qeq_le; apply qeq_imp_qeqT; apply Qeq_sym; exact Hident
          | exact Hstep2]).
(* Strict term: [0 < y^6/1440] implies [A < A + y^6/1440]. *)
    assert (Hb : Qlt 0 (q_pow y 6%nat / 1440)).
    { unfold Qdiv. apply Qmult_lt_0_compat.
      - apply QltT_to_Qlt. apply (cpl_qpow_pos y 6%nat Hylt).
      - apply (Qinv_lt_0_compat (1440#1)). unfold Qlt. simpl. lia. }
    assert (Hc1 : Qlt (q_pow y 5%nat / 720)
                      (q_pow y 6%nat / 1440 + q_pow y 5%nat / 720)).
    { apply QltT_to_Qlt. apply (cpl_qlt_eq_l (0 + q_pow y 5%nat / 720)%Q).
      - ring.
      - apply (proj2 (Qplus_lt_l 0%Q (q_pow y 6%nat / 1440) (q_pow y 5%nat / 720))).
        exact Hb. }
    assert (Hswap : Qle (q_pow y 6%nat / 1440 + q_pow y 5%nat / 720)
                        (q_pow y 5%nat / 720 + q_pow y 6%nat / 1440))
      by (apply QleT'_to_Qle; apply qeq_le; apply qeq_imp_qeqT; ring).
    apply (Qlt_le_trans _ (q_pow y 5%nat / 720 + q_pow y 6%nat / 1440)).
    - exact (Qlt_le_trans _ (q_pow y 6%nat / 1440 + q_pow y 5%nat / 720) _ Hc1 Hswap).
    - apply (Qle_trans _ (q_pow y 5%nat / 720 + q_pow y 6%nat / 1440 + q_pow y 8%nat / 8640)).
      + apply QleT'_to_Qle. apply (qtail_le_plus_r _ (q_pow y 8%nat / 8640)).
        unfold Qdiv. apply Qmult_le_0_compat.
        * apply QleT'_to_Qle. apply (cpl_qpow_nonneg y 8%nat Hy0).
        * apply QleT'_to_Qle. apply cpl_qlt_le. apply (Qinv_lt_0_compat (8640#1)). unfold Qlt. simpl. lia.
      + exact Hstep3.
    }
    assert (Hpt : Qlt (q_pow y 5%nat / 720)
                      (projT1 (real_mult (cauchy_real_exp (existT (fun s : Qseq => cauchy s) u Hu))
                                          (real_const (pade_den 2%nat y))) m
                        - projT1 (real_const (pade_num 2%nat y)) m)).
    { apply QltT_to_Qlt. apply (cpl_qlt_eq_sr (q_pow y 5%nat / 720)
              (exp_partial m y * pade_den 2%nat y - pade_num 2%nat y)).
      - exact (Qeq_sym _ _ HDe).
      - exact Hchain. }
    apply Qlt_to_QltT. exact Hpt.
Qed.

End PadeLower.
