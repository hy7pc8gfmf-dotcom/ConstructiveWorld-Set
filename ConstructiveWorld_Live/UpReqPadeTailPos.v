(* ConstructiveWorld-Set — closed-form positivity of the Pade tail
   coefficients, sign transfer, and denominator positivity on (1,2). *)

(** * UpReqPadeTailPos: the positive tail of the Pade error expansion and
      the denominator sign on the window [x in (1,2)].

    Mission.  (1) The closed-form beta coefficients [ptp_beta n m =
      n! * (n+m)! / (2n+m+1)!]: strict positivity with the witness
      [1/(2n+m+1)!], the sigT witness form, factorial monotonicity, and
      the denominator well-definedness and nonzero faces.  (2) The truncated-tail series identity for
      [exp_partial (3+k) y * Q1(y) - P1(y)] with numeric anchors.
      (3) Denominator positivity of the Pade approximant on [x in (1,2)]
      and the Q-to-Real embedding bridges for the accuracy statement.

    Dependencies.  Stdlib [QArith], [Arith], [Lia], [Setoid],
      [Morphisms], [Extraction]; requires [S01_BaseRing] through
      [S15_TailFEPUp] plus the Pade family of this development.

    References.  ConstructiveWorld-Main, module [UpReqPadeTailPos].

    Constructivity.  All statements are carried by [Set]
      ([QltT]/[QleT']/[QeqT]/[sigT]); positivity is carried by explicit
      witnesses; closed numeric anchors close by [vm_compute].  The
      extraction audit reports [Obj.magic] = 0; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" UpReqPadeTailPos.v];
      artifact magic [436f7121 00015ff4]. *)

(* ============================ Part 1. Closed-form positivity of the beta coefficients and sign transfer ============================ *)
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqPadeQLeg.
From Stdlib Require Import QArith.QArith Arith.Arith Lia Setoid.
From Stdlib Require Import Setoid Morphisms.

(* ===== The factorial face ===== *)

(* Every factorial is at least one (at concrete nat level: induction on the index, with a two-sided successor step). *)
Lemma pbp_qfact_ge1 : forall k : nat, QleT' 1%Q (q_fact k).
Proof.
  induction k as [| j IH].
  - change (QleT' 1%Q 1%Q). apply qleT'_refl.
  - apply Qle_to_QleT'.
    assert (H1 : Qle 1%Q ((Z.of_nat (Datatypes.S j) # 1)))
      by (unfold Qle; cbn [Qnum Qden]; lia).
    change (Qle (1%Q * 1%Q) ((Z.of_nat (Datatypes.S j) # 1) * q_fact j)).
    apply (Qmult_le_compat_nonneg 1%Q ((Z.of_nat (Datatypes.S j) # 1)) 1%Q (q_fact j)).
    + split.
      * unfold Qle. cbn [Qnum Qden]. lia.
      * exact H1.
    + split.
      * unfold Qle. cbn [Qnum Qden]. lia.
      * apply (QleT'_to_Qle 1%Q (q_fact j)). exact IH.
Qed.

(* Factorial monotonicity (the Set-level [<=] face): [a <= b] implies
   [a! <= b!].  Route: a nat-level lia bridge, the successor expansion of
   the factorial, and two right-factor multiplications reordered and
   normalized. *)
Lemma pbp_qfact_mono : forall a b : nat, (a <= b)%nat -> QleT' (q_fact a) (q_fact b).
Proof.
  intros a b. revert a.
  induction b as [| j IH]; intros a H.
  - assert (Ha : a = 0%nat) by lia. subst a. apply qleT'_refl.
  - destruct a as [| i].
    + exact (pbp_qfact_ge1 (Datatypes.S j)).
    + assert (Hij : (i <= j)%nat) by lia.
      specialize (IH i Hij).
      assert (Hprod : Qle ((Z.of_nat (Datatypes.S i) # 1) * q_fact i)
                          ((Z.of_nat (Datatypes.S j) # 1) * q_fact j)).
      { apply (Qle_trans _ (q_fact i * (Z.of_nat (Datatypes.S i) # 1))).
        - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
        - apply (Qle_trans _ ((Z.of_nat (Datatypes.S i) # 1) * q_fact j)).
          + apply (Qle_trans _ (q_fact j * (Z.of_nat (Datatypes.S i) # 1))).
            * apply Qmult_le_compat_r.
              -- apply (QleT'_to_Qle (q_fact i) (q_fact j)). exact IH.
              -- assert (Hsi : Qle 0%Q ((Z.of_nat (Datatypes.S i) # 1)))
                   by (unfold Qle; cbn [Qnum Qden]; lia).
                 exact Hsi.
            * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
          + apply Qmult_le_compat_r.
            * assert (HSij : Qle (Z.of_nat (Datatypes.S i) # 1)
                                 (Z.of_nat (Datatypes.S j) # 1))
                by (unfold Qle; cbn [Qnum Qden]; lia).
              exact HSij.
            * apply (Qlt_le_weak 0%Q (q_fact j)). apply QltT_to_Qlt. apply q_fact_pos. }
      apply Qle_to_QleT'. exact Hprod.
Qed.

(* ===== Main: the beta coefficients in closed form and their positivity ===== *)

(* The beta coefficient: the closed-form coefficient of the positive Pade remainder series. *)
Definition pbp_beta (n m : nat) : Q :=
  (q_fact n * q_fact (n + m)) / q_fact (2 * n + m + 1).

(* The concrete lower-bound witness [1/(2n+m+1)!]: positivity is carried by a genuinely constructive, computable positive number. *)
Definition pbp_beta_lb (n m : nat) : Q := 1%Q / q_fact (2 * n + m + 1).

(* The lower bound is positive (strict-inverse face plus a product of positives). *)
Lemma pbp_beta_lb_pos : forall n m : nat, QltT 0 (pbp_beta_lb n m).
Proof.
  intros n m. apply Qlt_to_QltT. unfold pbp_beta_lb.
  change (Qlt 0%Q (1%Q * / q_fact (2 * n + m + 1))).
  apply Qmult_lt_0_compat.
  - unfold Qlt. cbn [Qnum Qden]. lia.
  - apply Qinv_lt_0_compat. apply QltT_to_Qlt. apply q_fact_pos.
Qed.

(* The lower bound is attained: the numerator is at least [1*1] (both
   factorials are at least one), both sides divided by the same positive
   denominator. *)
Lemma pbp_beta_ge_lb : forall n m : nat, QleT' (pbp_beta_lb n m) (pbp_beta n m).
Proof.
  intros n m.
  assert (Hn : Qle 1%Q (q_fact n))
    by (apply (QleT'_to_Qle 1%Q (q_fact n)); apply pbp_qfact_ge1).
  assert (Hm : Qle 1%Q (q_fact (n + m)))
    by (apply (QleT'_to_Qle 1%Q (q_fact (n + m))); apply pbp_qfact_ge1).
  assert (Hnum : Qle 1%Q (q_fact n * q_fact (n + m))).
  { apply (Qmult_le_compat_nonneg 1%Q (q_fact n) 1%Q (q_fact (n + m))).
    - split.
      + unfold Qle. cbn [Qnum Qden]. lia.
      + exact Hn.
    - split.
      + unfold Qle. cbn [Qnum Qden]. lia.
      + exact Hm. }
  unfold pbp_beta, pbp_beta_lb.
  apply (q_le_div_le 1%Q (q_fact (2 * n + m + 1))
                     (q_fact n * q_fact (n + m)) (q_fact (2 * n + m + 1))).
  - apply q_fact_pos.
  - apply q_fact_pos.
  - apply Qle_to_QleT'.
    apply (Qmult_le_compat_r 1%Q (q_fact n * q_fact (n + m))
                              (q_fact (2 * n + m + 1)) Hnum).
    apply (Qlt_le_weak 0%Q (q_fact (2 * n + m + 1))). apply QltT_to_Qlt.
    apply q_fact_pos.
Qed.

(* Main: the beta coefficient is strictly positive (in [QltT] witness form; the proof is the positive lower bound plus its transfer). *)
Lemma pbp_beta_pos : forall n m : nat, QltT 0 (pbp_beta n m).
Proof.
  intros n m.
  apply Qlt_to_QltT.
  apply (Qlt_le_trans 0%Q (pbp_beta_lb n m) (pbp_beta n m)).
  - apply QltT_to_Qlt. apply pbp_beta_lb_pos.
  - apply (QleT'_to_Qle (pbp_beta_lb n m) (pbp_beta n m)). apply pbp_beta_ge_lb.
Qed.

(* The sigT witness form (positivity lifted into the witness, for bitwise
   downstream use): the witness is the beta value itself (pinned by [Id])
   together with its [QltT] positivity certificate. *)
Definition pbp_beta_pos_sigT (n m : nat) :
  sigT (fun b : Q => sigT (fun _ : Id b (pbp_beta n m) => QltT 0 b)) :=
  existT (fun b : Q => sigT (fun _ : Id b (pbp_beta n m) => QltT 0 b))
         (pbp_beta n m)
         (existT (fun _ : Id (pbp_beta n m) (pbp_beta n m)
                    => QltT 0 (pbp_beta n m))
                 (@id_refl Q (pbp_beta n m))
                 (pbp_beta_pos n m)).

(* ===== Companion 1: well-definedness and the denominator-nonzero face ===== *)

(* The denominator index nat bridge: [2n+m+1 >= 1] (one lia step; witnessed at the successor expansion). *)
Lemma pbp_den_index_ge1 : forall n m : nat, NatLe (1) (2 * n + m + 1).
Proof. intros n m. apply NatLe_lift. lia. Qed.

(* Well-definedness of the denominator factorial ratio: the factorial at
   index [2n+m+1] equals [(2n+m+1) * (2n+m)!], with the first factor at
   least one through the nat bridge — a concrete natural-number witness of
   denominator nonzeroness. *)
Lemma pbp_beta_closed : forall n m : nat,  
 QeqT (q_fact (2 * n + m + 1))
 ((Z.of_nat (Datatypes.S (2 * n + m)) # 1) * q_fact (2 * n + m)).
Proof.
  intros n m.
  replace (2 * n + m + 1)%nat with (Datatypes.S (2 * n + m)) by lia.
  apply q_fact_succ.
Qed.

(* The denominator is positive (on the Set face). *)
Lemma pbp_den_posT : forall n m : nat, QltT 0 (q_fact (2 * n + m + 1)).
Proof. intros n m. apply q_fact_pos. Qed.

(* The denominator is nonzero (a Prop-face bridge lemma of the familiar q_neq_of_lt shape, for domain arguments). *)
Lemma pbp_den_neq0 : forall n m : nat, Not (QeqT (q_fact (2 * n + m + 1)) 0%Q).
Proof.
  intros n m Hz.
  exact (q_neq_of_lt (q_fact (2 * n + m + 1)) (q_fact_pos (2 * n + m + 1))
         Hz).
Qed.

(* ===== Companion 2: preparation for sign transfer (the interface is left explicit; no forced connection) ===== *)

(* A right-transport bridge under Qeq (the smallest transfer lemma of this
   module): [a == b] turns [0 < a] into [0 < b] (a one-step reuse of the
   predecessor lemma, so the closed axiom environment of the original
   statement is not reintroduced). *)
Lemma pbp_qlt0_eq_r : forall a b : Q, a == b -> Qlt 0 a -> QltT 0 b.
Proof.
  intros a b Hab Ha.
  exact (pql_qlt0_eq_r a b Hab Ha).
Qed.

(* Sign transfer: when the leading remainder coefficient factors as
   [lead == pbp_beta n m * posf] with the factor [posf] positive, then
   [0 < lead].  The positive factor is supplied downstream (this lemma only
   transfers the sign; it does not pin the factor's shape). *)
Lemma pbp_sign_transfer : forall (lead posf : Q) (n m : nat),
  lead == pbp_beta n m * posf ->
  QltT 0 posf ->
  QltT 0 lead.
Proof.
  intros lead posf n m Heq Hf.
  apply (pbp_qlt0_eq_r (pbp_beta n m * posf) lead).
  - apply Qeq_sym. exact Heq.
  - apply Qmult_lt_0_compat.
    + apply QltT_to_Qlt. apply pbp_beta_pos.
    + apply QltT_to_Qlt. exact Hf.
Qed.

(* Additional face: [ptp_beta n m <= n!] (a real use of factorial
   monotonicity: [(2n+m+1)! >= (n+m)!] forces
   [beta = n! * (n+m)! / (2n+m+1)! <= n!]); the downstream tail bound reads
   this as a concrete constant for fixed [n]. *)
Lemma pbp_beta_le_nfact : forall n m : nat, QleT' (pbp_beta n m) (q_fact n).
Proof.
  intros n m.
  assert (Hmono : Qle (q_fact (n + m)) (q_fact (2 * n + m + 1))).
  { apply (QleT'_to_Qle (q_fact (n + m)) (q_fact (2 * n + m + 1))).
    apply pbp_qfact_mono. lia. }
  assert (Hneq : ~ (q_fact (n + m) == 0))
    by (intro Hz; exact (match q_neq_of_lt (q_fact (n + m))
                             (q_fact_pos (n + m)) (qeq_imp_qeqT _ _ Hz)
                         with end)).
  assert (Hleg : Qle ((q_fact n * q_fact (n + m)) * q_fact (n + m))
                     ((q_fact n * q_fact (n + m)) * q_fact (2 * n + m + 1))).
  { apply (Qle_trans _ ((q_fact (n + m)) * (q_fact n * q_fact (n + m)))).
    - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
    - apply (Qle_trans _ ((q_fact (2 * n + m + 1)) * (q_fact n * q_fact (n + m)))).
      + apply Qmult_le_compat_r.
        * exact Hmono.
        * apply Qmult_le_0_compat.
          -- apply (Qlt_le_weak 0%Q (q_fact n)). apply QltT_to_Qlt.
             apply q_fact_pos.
          -- apply (Qlt_le_weak 0%Q (q_fact (n + m))). apply QltT_to_Qlt.
             apply q_fact_pos.
      + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
  apply Qle_to_QleT'.
  unfold pbp_beta.
  apply (Qle_trans ((q_fact n * q_fact (n + m)) / q_fact (2 * n + m + 1))
                   ((q_fact n * q_fact (n + m)) / q_fact (n + m))
                   (q_fact n)).
  - apply QleT'_to_Qle.
    apply (q_le_div_le (q_fact n * q_fact (n + m)) (q_fact (2 * n + m + 1))
                       (q_fact n * q_fact (n + m)) (q_fact (n + m))).
    + apply q_fact_pos.
    + apply q_fact_pos.
    + apply Qle_to_QleT'. exact Hleg.
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
    apply (Qdiv_mult_l (q_fact n) (q_fact (n + m)) Hneq).
Qed.

(* ===== Numeric anchors (checked: at n = 1 the values are 1/6, 1/12, 1/20, 1/30, 1/42) ===== *)
Lemma pbp_beta_1_0 : QeqT (pbp_beta 1%nat 0%nat) ((1#6)%Q).
Proof. vm_compute. reflexivity. Qed.

Lemma pbp_beta_1_1 : QeqT (pbp_beta 1%nat 1%nat) ((1#12)%Q).
Proof. vm_compute. reflexivity. Qed.

Lemma pbp_beta_1_2 : QeqT (pbp_beta 1%nat 2%nat) ((1#20)%Q).
Proof. vm_compute. reflexivity. Qed.


From Stdlib Require Import Extraction.
Separate Extraction pbp_beta pbp_beta_lb pbp_qfact_ge1 pbp_qfact_mono
  pbp_beta_lb_pos pbp_beta_ge_lb pbp_beta_pos pbp_beta_pos_sigT
  pbp_den_index_ge1 pbp_beta_closed pbp_den_posT pbp_den_neq0
  pbp_qlt0_eq_r pbp_sign_transfer pbp_beta_le_nfact.
Print Assumptions pbp_beta.
Print Assumptions pbp_beta_lb.
Print Assumptions pbp_qfact_ge1.
Print Assumptions pbp_qfact_mono.
Print Assumptions pbp_beta_lb_pos.
Print Assumptions pbp_beta_ge_lb.
Print Assumptions pbp_beta_pos.
Print Assumptions pbp_beta_pos_sigT.
Print Assumptions pbp_den_index_ge1.
Print Assumptions pbp_beta_closed.
Print Assumptions pbp_den_posT.
Print Assumptions pbp_den_neq0.
Print Assumptions pbp_qlt0_eq_r.
Print Assumptions pbp_sign_transfer.
Print Assumptions pbp_beta_le_nfact.

Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqPadeExp.
From Stdlib Require Import QArith.QArith Arith.Arith Lia Setoid.

(* ===== Definitions ===== *)

(* The beta coefficient = n! * (n+m)! / (2n+m+1)! — the same closed form as the predecessor beta term, positive throughout. *)
Definition ptp_beta (n m : nat) : Q :=
  q_fact n * q_fact (n + m) / q_fact (2 * n + m + 1).

(* The signed positive-tail prefix: the sum over m <= M of beta_m * y^(2n+1+m)/m! (the power inside each term). *)
Definition ptp_beta_prefix (n M : nat) (y : Q) : Q :=
  sum_upto (Datatypes.S M)
    (fun m => ptp_beta n m / q_fact m * q_pow y (2 * n + 1 + m)).

(* ===== Small engines ===== *)

(* Tail expansion of the bounded sum: definitional (the successor step adds the last term). *)
Lemma ptp_sum_S : forall (K : nat) (f : nat -> Q),  
 QeqT (sum_upto (Datatypes.S K) f) (sum_upto K f + f K).
Proof. intro K. intro f. exact (qeq_imp_qeqT _ _ (Qeq_refl (sum_upto (Datatypes.S K) f))). Qed.

(* Prefix stepping: the successor prefix adds the last term. *)
Lemma ptp_prefix_S : forall (n M : nat) (y : Q),  
 QeqT (ptp_beta_prefix n (Datatypes.S M) y)


 (ptp_beta_prefix n M y +   (ptp_beta n (Datatypes.S M) / q_fact (Datatypes.S M)      * q_pow y (2 * n + 1 + Datatypes.S M))).
Proof.
  intros n M y. unfold ptp_beta_prefix.
  apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (ptp_sum_S (Datatypes.S M)
             (fun m => ptp_beta n m / q_fact m * q_pow y (2 * n + 1 + m)))).
  reflexivity.
Qed.

(* The linear denominator and numerator in closed form (coefficient expansion). *)
Lemma ptp_den1 : forall y : Q, QeqT (pade_den 1 y) (1 + - (1#2) * y).
Proof.
  intro y. apply qeq_imp_qeqT. unfold pade_den, pade_coeff. cbn. field.
Qed.

Lemma ptp_num1 : forall y : Q, QeqT (pade_num 1 y) (1 + (1#2) * y).
Proof.
  intro y. apply qeq_imp_qeqT. unfold pade_num, pade_coeff. cbn. field.
Qed.

(* ===== Positivity statements (for all n, m; Set-level [QltT] exits) ===== *)

Theorem ptp_beta_pos : forall (n m : nat), QltT 0 (ptp_beta n m).
Proof.
  intros n m. apply Qlt_to_QltT.
  unfold ptp_beta. unfold Qdiv.
  apply Qmult_lt_0_compat.
  - apply Qmult_lt_0_compat;
      [apply QltT_to_Qlt; apply q_fact_pos | apply QltT_to_Qlt; apply q_fact_pos].
  - apply Qinv_lt_0_compat. apply QltT_to_Qlt. apply q_fact_pos.
Qed.

(* ===== Beta anchor family (exact fraction cross-checks) ===== *)

Lemma ptp_beta_n1_0 : QeqT (ptp_beta 1 0%nat) (1#6).
Proof. apply qeq_imp_qeqT. vm_compute. unfold Qeq. simpl. lia. Qed.

Lemma ptp_beta_n1_1 : QeqT (ptp_beta 1 1%nat) (1#12).
Proof. apply qeq_imp_qeqT. vm_compute. unfold Qeq. simpl. lia. Qed.

Lemma ptp_beta_n1_2 : QeqT (ptp_beta 1 2%nat) (1#20).
Proof. apply qeq_imp_qeqT. vm_compute. unfold Qeq. simpl. lia. Qed.

Lemma ptp_beta_n1_3 : QeqT (ptp_beta 1 3%nat) (1#30).
Proof. apply qeq_imp_qeqT. vm_compute. unfold Qeq. simpl. lia. Qed.

Lemma ptp_beta_n1_4 : QeqT (ptp_beta 1 4%nat) (1#42).
Proof. apply qeq_imp_qeqT. vm_compute. unfold Qeq. simpl. lia. Qed.

Lemma ptp_beta_n2_0 : QeqT (ptp_beta 2 0%nat) (1#30).
Proof. apply qeq_imp_qeqT. vm_compute. unfold Qeq. simpl. lia. Qed.

Lemma ptp_beta_n2_1 : QeqT (ptp_beta 2 1%nat) (1#60).
Proof. apply qeq_imp_qeqT. vm_compute. unfold Qeq. simpl. lia. Qed.

Lemma ptp_beta_n2_2 : QeqT (ptp_beta 2 2%nat) (1#105).
Proof. apply qeq_imp_qeqT. vm_compute. unfold Qeq. simpl. lia. Qed.

(* Closed-form leading instances: [(n!)^2 / ((2n)! (2n+1)!)] gives [1/12]
   at [n = 1] (the leading coefficient of the [y^3] position, with the odd
   sign) and [1/720] at [n = 2] (the leading coefficient of the [y^5]
   position, positive). *)
Lemma ptp_beta_n1_first : QeqT (ptp_beta 1 0%nat / q_fact 2) (1#12).
Proof. apply qeq_imp_qeqT. vm_compute. unfold Qeq. simpl. lia. Qed.

Lemma ptp_beta_n2_first : QeqT (ptp_beta 2 0%nat / q_fact 4) (1#720).
Proof. apply qeq_imp_qeqT. vm_compute. unfold Qeq. simpl. lia. Qed.

(* Base piece 1: the truncated polynomial identity at [n = 1] (for all [y]).
   The coefficients match the full-series coefficients exactly at [m = 0,1];
   the [y^5] term is the truncation sliver of the fourth partial sum. *)
Lemma ptp_n1_poly : forall y : Q, 
  QeqT (exp_partial 4 y * pade_den 1 y - pade_num 1 y)
 (- ((1#12)*q_pow y 3 + (1#24)*q_pow y 4 + (1#48)*q_pow y 5)).
Proof.
  intro y. apply qeq_imp_qeqT.
  unfold exp_partial, pade_den, pade_num, pade_coeff.
  cbn. field.
Qed.

(* ===== Base piece 2: the even-sign positive-tail instance at n = 2 (for all y) =====
   The ten Pade matching conditions (all coefficients of y^0..y^4 vanish)
   are read off from the absence of low-order terms on the right; the y^7
   coefficient vanishes exactly, and the leading term is y^5/720 =
   (2!)^2/(4! * 5!). *)
Lemma ptp_n2_poly : forall y : Q, 
  QeqT (exp_partial 6 y * pade_den 2 y - pade_num 2 y)
 ((1#720)*q_pow y 5 + (1#1440)*q_pow y 6 + (1#8640)*q_pow y 8).
Proof.
  intro y. apply qeq_imp_qeqT.
  unfold exp_partial, pade_den, pade_num, pade_coeff.
  cbn. field.
Qed.

(* ===== Numeric anchors (checked at y = 1/2; vm_compute with cross-multiplied integer comparison) ===== *)

Lemma ptp_sentinel_n1_half :  
 QeqT (exp_partial 4 (1#2) * pade_den 1 (1#2) - pade_num 1 (1#2)) (- (7#512)).
Proof. apply qeq_imp_qeqT. vm_compute. unfold Qeq. simpl. lia. Qed.

Lemma ptp_sentinel_n2_half : 
  QeqT (exp_partial 6 (1#2) * pade_den 2 (1#2) - pade_num 2 (1#2))
 ((1#720)*(1#32) + (1#1440)*(1#64) + (1#8640)*(1#256)).
Proof. apply qeq_imp_qeqT. vm_compute. unfold Qeq. simpl. lia. Qed.

(* ===== Audit and extraction ===== *)

Print Assumptions ptp_beta_pos.
Print Assumptions ptp_n1_poly.
Print Assumptions ptp_n2_poly.

From Stdlib Require Import Extraction.
Separate Extraction ptp_beta_pos ptp_beta ptp_beta_prefix
  ptp_n1_poly ptp_n2_poly.

(* ============================================================ *)
(* The tail series identity.  Induction invariant:                *)
(*     exp_partial (3+k) y * Q1(y) - P1(y)                        *)
(*       == -((1#2) * prefix_1 k y) - ((1#2) * y^(S(3+k)) / (3+k)!) *)
(*   The two (−1#2) factors make the odd sign explicit (odd n has *)
(*   a negative tail); the even-n dual is carried by the positive *)
(*   n=2 instance.  The closed forms at N = 3 and N = 4 are       *)
(*   compared coefficient by coefficient with the n=1 polynomial, *)
(*   with rechecks and a numeric check at y = 1/2.                *)
(*   Method: a multiplication-form merge over free variables (a   *)
(*   field over atoms), then cross-multiplication to clear the    *)
(*   denominators, then field again.                              *)
(* ============================================================ *)

(* -- 0. A free-variable engine (ring/field only sees free variables and literal constants) -- *)

Lemma ptp_AC_swap_m : forall a b c : Q, QeqT (a + b - c) (a - c + b).
Proof. intros a b c. apply qeq_imp_qeqT. unfold Qminus. ring. Qed.

Lemma ptp_opp_plus : forall a b : Q, QeqT (- (a + b)) (- a + - b).
Proof. intros a b. apply qeq_imp_qeqT. unfold Qminus. ring. Qed.

Lemma ptp_opp_mul_move : forall a b : Q, QeqT ((- a) * b) (- (a * b)).
Proof. intros a b. apply qeq_imp_qeqT. ring. Qed.

Lemma ptp_G_alg : forall a b c p : Q, QeqT ((a + b) + c) ((a + (- p)) + ((b + p) + c)).
Proof. intros a b c p. apply qeq_imp_qeqT. ring. Qed.

Lemma ptp_Qmake_plus : forall a b : Z, QeqT ((a + b) # 1) ((a # 1) + (b # 1)).
Proof. intros a b. apply qeq_imp_qeqT. unfold Qeq. simpl. lia. Qed.

(* -- 1. Denominator clearing (cross-multiplication via multiplication injectivity, with positivity present) -- *)

Lemma ptp_div_clear_r : forall x d D E : Q,   ~
 (d == 0) -> D == E * d -> QeqT (x / d * D) (x * E).
Proof.
  intros x d D E Hd HDE. apply qeq_imp_qeqT. unfold Qdiv. rewrite HDE.
  rewrite (Qmult_comm E d).
  rewrite <- (Qmult_assoc x (Qinv d) (d * E)).
  rewrite (Qmult_assoc (Qinv d) d E).
  rewrite (Qmult_comm (Qinv d) d). rewrite (Qmult_inv_r d Hd).
  rewrite Qmult_1_l. reflexivity.
Qed.

(* -- 2. The multiplication-form merge (skeleton reused verbatim; the factorial chain normalized by lia) -- *)

Lemma ptp_n1_merge : forall m : nat, 
  QeqT (q_fact 1 * q_fact (Datatypes.S m) * q_fact (Datatypes.S (Datatypes.S m)))

 ((q_fact (Datatypes.S (Datatypes.S (Datatypes.S m)))       - (1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S m))) * q_fact m).
Proof.
  intro m. apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (q_fact_succ (Datatypes.S (Datatypes.S m)))).
  rewrite (qeqT_imp_qeq _ _ (q_fact_succ (Datatypes.S m))).
  rewrite (qeqT_imp_qeq _ _ (q_fact_succ m)).
  rewrite (qeqT_imp_qeq _ _ (q_fact_succ 0%nat)).
  cbn [q_fact].
  replace (Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S m))))
    with (Z.of_nat m + 3)%Z by lia.
  replace (Z.of_nat (Datatypes.S (Datatypes.S m)))
    with (Z.of_nat m + 2)%Z by lia.
  replace (Z.of_nat (Datatypes.S m)) with (Z.of_nat m + 1)%Z by lia.
  replace (Z.of_nat 1) with 1%Z by lia.
  rewrite (qeqT_imp_qeq _ _ (ptp_Qmake_plus (Z.of_nat m) 3%Z)).
  rewrite (qeqT_imp_qeq _ _ (ptp_Qmake_plus (Z.of_nat m) 2%Z)).
  rewrite (qeqT_imp_qeq _ _ (ptp_Qmake_plus (Z.of_nat m) 1%Z)).
  field.
Qed.

(* -- 3. Two-sided step expansions (rewrites only; the atomic denominators are untouched) -- *)

Definition ptp_F (k : nat) (y : Q) : Q :=
  exp_partial (3 + k) y * pade_den 1 y - pade_num 1 y.

Definition ptp_G (k : nat) (y : Q) : Q :=
  - ((1#2) * ptp_beta_prefix 1 k y)
    - (1#2) * (q_pow y (4 + k) / q_fact (3 + k)).

Lemma ptp_exp_S : forall (n : nat) (y : Q),  
 QeqT (exp_partial (Datatypes.S n) y)
 (exp_partial n y + q_pow y (Datatypes.S n) / q_fact (Datatypes.S n)).
Proof. intros n y. exact (qeq_imp_qeqT _ _ (Qeq_refl (exp_partial (Datatypes.S n) y))). Qed.

Lemma ptp_G_eq : forall k y, 
  QeqT (ptp_G k y)

 (- ((1#2) * ptp_beta_prefix 1 k y)      + - ((1#2) * (q_pow y (Datatypes.S (3 + k)) / q_fact (3 + k)))).
Proof.
  intros k y. apply qeq_imp_qeqT. unfold ptp_G, Qminus.
  replace (4%nat + k)%nat with (Datatypes.S (3 + k)%nat) by lia.
  reflexivity.
Qed.

Lemma ptp_F_step : forall k y, 
  QeqT (ptp_F (Datatypes.S k) y)


 (ptp_F k y      + ((q_pow y (Datatypes.S (3 + k)) / q_fact (Datatypes.S (3 + k)))         * (1 + - (1#2) * y))).
Proof.
  intros k y. apply qeq_imp_qeqT. unfold ptp_F.
  replace (3%nat + Datatypes.S k)%nat with (Datatypes.S (3 + k)%nat) by lia.
  rewrite (qeqT_imp_qeq _ _ (ptp_exp_S _ _)).
  rewrite (qeqT_imp_qeq _ _ (ptp_den1 _)).
  rewrite (qeqT_imp_qeq _ _ (ptp_num1 _)).
  rewrite (Qmult_plus_distr_l (exp_partial (3 + k) y)
             (q_pow y (Datatypes.S (3 + k)) / q_fact (Datatypes.S (3 + k)))
             (1 + - (1#2) * y)).
  rewrite (qeqT_imp_qeq _ _ (ptp_AC_swap_m
             (exp_partial (3 + k) y * (1 + - (1#2) * y))
             ((q_pow y (Datatypes.S (3 + k)) / q_fact (Datatypes.S (3 + k)))
              * (1 + - (1#2) * y))
             (1 + (1#2) * y))).
  reflexivity.
Qed.

Lemma ptp_G_step : forall k y, 
  QeqT (ptp_G (Datatypes.S k) y)






 (- ((1#2) * ptp_beta_prefix 1 k y)      + - ((1#2) * (q_pow y (Datatypes.S (3 + k)) / q_fact (3 + k)))      + (- ((1#2) * (ptp_beta 1 (Datatypes.S k) / q_fact (Datatypes.S k)                     * q_pow y (Datatypes.S (3 + k))))         + (1#2) * (q_pow y (Datatypes.S (3 + k)) / q_fact (3 + k))         + - ((1#2) * (y * q_pow y (Datatypes.S (3 + k))                       / q_fact (Datatypes.S (3 + k)))))).
Proof.
  intros k y. apply qeq_imp_qeqT. unfold ptp_G.
  replace (4%nat + Datatypes.S k)%nat
    with (Datatypes.S (Datatypes.S (3%nat + k)%nat)) by lia.
  replace (3%nat + Datatypes.S k)%nat with (Datatypes.S (3 + k)%nat) by lia.
  rewrite (qeqT_imp_qeq _ _ (ptp_prefix_S _ _ _)).
  replace (2%nat * 1%nat + 1%nat + Datatypes.S k)%nat with (Datatypes.S (3%nat + k)%nat) by lia.
  rewrite (qeqT_imp_qeq _ _ (q_pow_succ y (Datatypes.S (3 + k)))).
  rewrite (Qmult_plus_distr_r (1#2) (ptp_beta_prefix 1 k y)
             (ptp_beta 1 (Datatypes.S k) / q_fact (Datatypes.S k)
              * q_pow y (Datatypes.S (3 + k)))).
  rewrite (qeqT_imp_qeq _ _ (ptp_opp_plus ((1#2) * ptp_beta_prefix 1 k y)
             ((1#2) * (ptp_beta 1 (Datatypes.S k) / q_fact (Datatypes.S k)
                       * q_pow y (Datatypes.S (3 + k)))))).
  rewrite (qeqT_imp_qeq _ _ (ptp_G_alg (- ((1#2) * ptp_beta_prefix 1 k y))
             (- ((1#2) * (ptp_beta 1 (Datatypes.S k) / q_fact (Datatypes.S k)
                          * q_pow y (Datatypes.S (3 + k)))))
             (- ((1#2) * (y * q_pow y (Datatypes.S (3 + k))
                          / q_fact (Datatypes.S (3 + k)))))
             ((1#2) * (q_pow y (Datatypes.S (3 + k)) / q_fact (3 + k))))).
  reflexivity.
Qed.

(* Clearing the denominator: the induction-step difference identity (both
   sides multiplied by the positive product of the four factors). *)

Lemma ptp_step_core : forall k y, 
  QeqT ((q_pow y (Datatypes.S (3 + k)) / q_fact (Datatypes.S (3 + k)))     * (1 + - (1#2) * y))





 (- ((1#2) * (ptp_beta 1 (Datatypes.S k) / q_fact (Datatypes.S k)                  * q_pow y (Datatypes.S (3 + k))))      + (1#2) * (q_pow y (Datatypes.S (3 + k)) / q_fact (3 + k))      + - ((1#2) * (y * q_pow y (Datatypes.S (3 + k))                    / q_fact (Datatypes.S (3 + k))))).
Proof.
  intros k y. apply qeq_imp_qeqT.
  unfold ptp_beta. cbn [Nat.add Nat.mul].
  replace (k%nat + 1%nat)%nat with (Datatypes.S k) by lia.
  remember (q_pow y (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S k)))))
    as Aeq eqn:HA.
  assert (Hw0 : ~ (q_fact (Datatypes.S k) == 0))
    by (intro Hz; exact (match q_neq_of_lt (q_fact (Datatypes.S k))
                             (q_fact_pos (Datatypes.S k))
                             (qeq_imp_qeqT _ _ Hz) with end)).
  assert (Hu0 : ~ (q_fact (Datatypes.S (Datatypes.S (Datatypes.S k))) == 0))
    by (intro Hz; exact (match q_neq_of_lt (q_fact (Datatypes.S (Datatypes.S
                                   (Datatypes.S k))))
                             (q_fact_pos (Datatypes.S (Datatypes.S
                                (Datatypes.S k))))
                             (qeq_imp_qeqT _ _ Hz) with end)).
  assert (Hv0 : ~ (q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                   (Datatypes.S k)))) == 0))
    by (intro Hz; exact (match q_neq_of_lt (q_fact (Datatypes.S (Datatypes.S
                                   (Datatypes.S (Datatypes.S k)))))
                             (q_fact_pos (Datatypes.S (Datatypes.S
                                (Datatypes.S (Datatypes.S k)))))
                             (qeq_imp_qeqT _ _ Hz) with end)).
  assert (HDBIG : QltT 0 (((1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S
                    (Datatypes.S k)))
                   * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                       (Datatypes.S k)))))
                  * q_fact (Datatypes.S k))).
  { apply Qlt_to_QltT. apply Qmult_lt_0_compat.
    - apply Qmult_lt_0_compat.
      + apply Qmult_lt_0_compat;
          [apply QltT_to_Qlt; exact Q2_pos | apply QltT_to_Qlt; apply q_fact_pos].
      + apply QltT_to_Qlt. apply q_fact_pos.
    - apply QltT_to_Qlt. apply q_fact_pos. }
  assert (HD : ~ (((1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S
                    (Datatypes.S k)))
                   * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                       (Datatypes.S k)))))
                  * q_fact (Datatypes.S k) == 0)).
  { intro Hz. exact (match q_neq_of_lt (((1 + 1)%Q * q_fact (Datatypes.S
                            (Datatypes.S (Datatypes.S k)))
                           * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                               (Datatypes.S k)))))
                          * q_fact (Datatypes.S k)) HDBIG
                        (qeq_imp_qeqT _ _ Hz) with end). }
  apply (proj1 (Qmult_inj_r _ _ _ HD)).
  (* Cancelling on the left-hand side. *)
  rewrite <- (Qmult_assoc (Aeq / q_fact (Datatypes.S (Datatypes.S
              (Datatypes.S (Datatypes.S k)))))
              (1 + - (1#2) * y)
              (((1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S (Datatypes.S k)))
                * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                    (Datatypes.S k)))))
               * q_fact (Datatypes.S k))).
  assert (HcL : (Aeq / q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                  (Datatypes.S k)))))
                * ((1 + - (1#2) * y)
                   * (((1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S
                        (Datatypes.S k)))
                       * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                           (Datatypes.S k)))))
                      * q_fact (Datatypes.S k)))
                == Aeq * ((1 + - (1#2) * y)
                          * ((1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S
                              (Datatypes.S k)))
                             * q_fact (Datatypes.S k)))).
  { apply qeqT_imp_qeq. apply (ptp_div_clear_r Aeq
             (q_fact (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S k)))))
             ((1 + - (1#2) * y)
              * (((1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S
                    (Datatypes.S k)))
                  * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                      (Datatypes.S k)))))
                 * q_fact (Datatypes.S k)))
             ((1 + - (1#2) * y)
              * ((1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S
                    (Datatypes.S k)))
                 * q_fact (Datatypes.S k))));
    [ exact Hv0 | ring ]. }
  rewrite HcL.
  (* Right-hand side: distribute D block by block, then cancel (explicit instances prevent accidental distribution on the left). *)
  rewrite (Qmult_plus_distr_l
             (- ((1#2) * (q_fact 1 * q_fact (Datatypes.S (Datatypes.S k))
                          / q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                              (Datatypes.S k))))
                          / q_fact (Datatypes.S k) * Aeq))
              + (1#2) * (Aeq / q_fact (Datatypes.S (Datatypes.S
                    (Datatypes.S k)))))
             (- ((1#2) * (y * Aeq
                          / q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                              (Datatypes.S k))))))
              )
             (((1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S (Datatypes.S k)))
               * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                   (Datatypes.S k)))))
              * q_fact (Datatypes.S k))).
  rewrite (Qmult_plus_distr_l
             (- ((1#2) * (q_fact 1 * q_fact (Datatypes.S (Datatypes.S k))
                          / q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                              (Datatypes.S k))))
                          / q_fact (Datatypes.S k) * Aeq)))
             ((1#2) * (Aeq / q_fact (Datatypes.S (Datatypes.S
                    (Datatypes.S k)))))
             (((1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S (Datatypes.S k)))
               * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                   (Datatypes.S k)))))
              * q_fact (Datatypes.S k))).
  (* Block B: the beta/w * A * D term. *)
  rewrite (qeqT_imp_qeq _ _ (ptp_opp_mul_move ((1#2) * (q_fact 1 * q_fact (Datatypes.S
             (Datatypes.S k))
             / q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                 (Datatypes.S k))))
             / q_fact (Datatypes.S k) * Aeq))
             (((1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S (Datatypes.S k)))
               * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                   (Datatypes.S k)))))
              * q_fact (Datatypes.S k)))).
  rewrite <- (Qmult_assoc (1#2)
             (q_fact 1 * q_fact (Datatypes.S (Datatypes.S k))
              / q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                  (Datatypes.S k))))
              / q_fact (Datatypes.S k) * Aeq)
             (((1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S (Datatypes.S k)))
               * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                   (Datatypes.S k)))))
              * q_fact (Datatypes.S k))).
  rewrite <- (Qmult_assoc (q_fact 1 * q_fact (Datatypes.S (Datatypes.S k))
              / q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                  (Datatypes.S k))))
              / q_fact (Datatypes.S k))
             Aeq
             (((1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S (Datatypes.S k)))
               * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                   (Datatypes.S k)))))
              * q_fact (Datatypes.S k))).
  assert (HcB1 : (q_fact 1 * q_fact (Datatypes.S (Datatypes.S k))
                  / q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                      (Datatypes.S k))))
                  / q_fact (Datatypes.S k))
                 * (Aeq * (((1 + 1)%Q
                            * q_fact (Datatypes.S (Datatypes.S
                                (Datatypes.S k)))
                            * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                                (Datatypes.S k)))))
                           * q_fact (Datatypes.S k)))
                 == (q_fact 1 * q_fact (Datatypes.S (Datatypes.S k))
                     / q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                         (Datatypes.S k)))))
                    * (Aeq * ((1 + 1)%Q
                              * q_fact (Datatypes.S (Datatypes.S
                                  (Datatypes.S k)))
                              * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                                  (Datatypes.S k))))))).
  { apply qeqT_imp_qeq. apply (ptp_div_clear_r
             (q_fact 1 * q_fact (Datatypes.S (Datatypes.S k))
              / q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                  (Datatypes.S k)))))
             (q_fact (Datatypes.S k))
             (Aeq * (((1 + 1)%Q
                      * q_fact (Datatypes.S (Datatypes.S (Datatypes.S k)))
                      * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                          (Datatypes.S k)))))
                     * q_fact (Datatypes.S k)))
             (Aeq * ((1 + 1)%Q
                     * q_fact (Datatypes.S (Datatypes.S (Datatypes.S k)))
                     * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                         (Datatypes.S k)))))));
    [ exact Hw0 | ring ]. }
  rewrite HcB1.
  assert (HcB2 : (q_fact 1 * q_fact (Datatypes.S (Datatypes.S k))
                  / q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                      (Datatypes.S k)))))
                 * (Aeq * ((1 + 1)%Q
                           * q_fact (Datatypes.S (Datatypes.S
                               (Datatypes.S k)))
                           * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                               (Datatypes.S k))))))
                 == (q_fact 1 * q_fact (Datatypes.S (Datatypes.S k)))
                    * (Aeq * ((1 + 1)%Q
                              * q_fact (Datatypes.S (Datatypes.S
                                  (Datatypes.S k)))))).
  { apply qeqT_imp_qeq. apply (ptp_div_clear_r
             (q_fact 1 * q_fact (Datatypes.S (Datatypes.S k)))
             (q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                 (Datatypes.S k)))))
             (Aeq * ((1 + 1)%Q
                     * q_fact (Datatypes.S (Datatypes.S (Datatypes.S k)))
                     * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                         (Datatypes.S k))))))
             (Aeq * ((1 + 1)%Q
                     * q_fact (Datatypes.S (Datatypes.S (Datatypes.S k))))));
    [ exact Hv0 | ring ]. }
  rewrite HcB2.
  (* Block C: the A/u3 * D term. *)
  rewrite <- (Qmult_assoc (1#2)
             (Aeq / q_fact (Datatypes.S (Datatypes.S (Datatypes.S k))))
             (((1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S (Datatypes.S k)))
               * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                   (Datatypes.S k)))))
              * q_fact (Datatypes.S k))).
  assert (HcC : (Aeq / q_fact (Datatypes.S (Datatypes.S (Datatypes.S k))))
                * (((1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S
                      (Datatypes.S k)))
                    * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                        (Datatypes.S k)))))
                   * q_fact (Datatypes.S k))
                == Aeq * ((1 + 1)%Q
                          * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                              (Datatypes.S k))))
                          * q_fact (Datatypes.S k))).
  { apply qeqT_imp_qeq. apply (ptp_div_clear_r Aeq
             (q_fact (Datatypes.S (Datatypes.S (Datatypes.S k))))
             (((1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S (Datatypes.S k)))
               * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                   (Datatypes.S k)))))
              * q_fact (Datatypes.S k))
             (((1 + 1)%Q
               * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                   (Datatypes.S k))))
               * q_fact (Datatypes.S k))));
    [ exact Hu0 | ring ]. }
  rewrite HcC.
  (* Block D: the y*A/v4 * D term. *)
  rewrite (qeqT_imp_qeq _ _ (ptp_opp_mul_move ((1#2) * (y * Aeq
             / q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                 (Datatypes.S k))))))
             (((1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S (Datatypes.S k)))
               * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                   (Datatypes.S k)))))
              * q_fact (Datatypes.S k)))).
  rewrite <- (Qmult_assoc (1#2)
             (y * Aeq / q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                 (Datatypes.S k)))))
             (((1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S (Datatypes.S k)))
               * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                   (Datatypes.S k)))))
              * q_fact (Datatypes.S k))).
  assert (HcD : ((y * Aeq) / q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                  (Datatypes.S k)))))
                * (((1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S
                      (Datatypes.S k)))
                    * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                        (Datatypes.S k)))))
                   * q_fact (Datatypes.S k))
                == (y * Aeq) * ((1 + 1)%Q
                                * q_fact (Datatypes.S (Datatypes.S
                                    (Datatypes.S k)))
                                * q_fact (Datatypes.S k))).
  { apply qeqT_imp_qeq. apply (ptp_div_clear_r (y * Aeq)
             (q_fact (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S k)))))
             (((1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S (Datatypes.S k)))
               * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                   (Datatypes.S k)))))
              * q_fact (Datatypes.S k))
             ((1 + 1)%Q
              * q_fact (Datatypes.S (Datatypes.S
                  (Datatypes.S k)))
               * q_fact (Datatypes.S k)));
    [ exact Hv0 | ring ]. }
  rewrite HcD.
  (* Substituting the merged form back (multiplication form, brackets aligned). *)
  rewrite (Qmult_comm Aeq
             ((1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S (Datatypes.S k))))).
  rewrite (Qmult_assoc (q_fact 1 * q_fact (Datatypes.S (Datatypes.S k)))
             ((1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S (Datatypes.S k))))
             Aeq).
  rewrite (Qmult_comm (1 + 1)%Q
             (q_fact (Datatypes.S (Datatypes.S (Datatypes.S k))))).
  rewrite (Qmult_assoc (q_fact 1 * q_fact (Datatypes.S (Datatypes.S k)))
             (q_fact (Datatypes.S (Datatypes.S (Datatypes.S k))))
             (1 + 1)%Q).
  rewrite (qeqT_imp_qeq _ _ (ptp_n1_merge (Datatypes.S k))).
  field.
Qed.

(* -- 5. Main statement: the identity in universally quantified N form (induction complete) -- *)

Lemma ptp_main_fg : forall k : nat, forall y : Q, QeqT (ptp_F k y) (ptp_G k y).
Proof.
  induction k as [| k IH].
  - intro y. apply qeq_imp_qeqT. unfold ptp_F, ptp_G.
    unfold ptp_beta_prefix, ptp_beta, pade_den, pade_num, pade_coeff.
    cbn. field.
  - intro y. apply qeq_imp_qeqT.
    rewrite (qeqT_imp_qeq _ _ (ptp_F_step _ _)).
    rewrite (qeqT_imp_qeq _ _ (ptp_G_step _ _)).
    rewrite <- (qeqT_imp_qeq _ _ (ptp_G_eq _ _)).
    rewrite (qeqT_imp_qeq _ _ (IH y)).
    rewrite (qeqT_imp_qeq _ _ (ptp_step_core k y)).
    reflexivity.
Qed.

Theorem ptp_tail_series_k : forall (k : nat) (y : Q),  
 QeqT (exp_partial (3 + k) y * pade_den 1 y - pade_num 1 y)

 (- ((1#2) * ptp_beta_prefix 1 k y)      - (1#2) * (q_pow y (Datatypes.S (3 + k)) / q_fact (3 + k))).
Proof.
  intros k y. exact (ptp_main_fg k y).
Qed.

Theorem ptp_tail_series : forall (N : nat) (y : Q), (3 <= N)%nat ->  
 QeqT (exp_partial N y * pade_den 1 y - pade_num 1 y)

 (- ((1#2) * ptp_beta_prefix 1 (N - 3) y)      - (1#2) * (q_pow y (Datatypes.S N) / q_fact N)).
Proof.
  intros N y HN.
  replace N with (3%nat + (N - 3)%nat)%nat by lia.
  replace (3%nat + (N - 3)%nat - 3%nat)%nat with (N - 3)%nat by lia.
  apply (ptp_tail_series_k (N - 3) y).
Qed.

(* Cross-checks: the closed forms at N = 3 and N = 4 match the n=1
   polynomial coefficient by coefficient, and at y = 1/2 both sides take the
   same value. *)

Lemma ptp_series_n1_N3 : forall y : Q,  
 QeqT
 (- ((1#2) * ptp_beta_prefix 1 0 y)     + - ((1#2) * (q_pow y (4 + 0) / q_fact (3 + 0))))
 (- ((1#12) * q_pow y 3 + (1#12) * q_pow y 4)).
Proof. intro y. apply qeq_imp_qeqT. unfold ptp_beta_prefix, ptp_beta. cbn. field. Qed.

Lemma ptp_series_n1_N4 : forall y : Q, 
  QeqT
 (- ((1#2) * ptp_beta_prefix 1 1 y)     + - ((1#2) * (q_pow y (4 + 1) / q_fact (3 + 1))))
 (- ((1#12) * q_pow y 3 + (1#24) * q_pow y 4 + (1#48) * q_pow y 5)).
Proof. intro y. apply qeq_imp_qeqT. unfold ptp_beta_prefix, ptp_beta. cbn. field. Qed.

(* The N = 4 special case is statement-identical to the fixed-value polynomial. *)
Lemma ptp_n1_poly_recheck : forall y : Q,  
 QeqT (exp_partial 4 y * pade_den 1 y - pade_num 1 y)
 (- ((1#12) * q_pow y 3 + (1#24) * q_pow y 4 + (1#48) * q_pow y 5)).
Proof.
  intro y. apply qeq_imp_qeqT.
  change (ptp_F 1 y
          == - ((1#12) * q_pow y 3 + (1#24) * q_pow y 4
                + (1#48) * q_pow y 5)).
  transitivity (ptp_G 1 y).
  - apply qeqT_imp_qeq. apply ptp_main_fg.
  - unfold ptp_G. apply qeqT_imp_qeq. apply ptp_series_n1_N4.
Qed.

(* Numeric check of the general instance against the fixed-value piece: both sides take the same value at y = 1/2. *)
Lemma ptp_tail_sentinel_F_half : QeqT (ptp_F 1 (1#2)) (-(7#512)).
Proof. apply qeq_imp_qeqT. vm_compute. unfold Qeq. simpl. lia. Qed.

Lemma ptp_tail_sentinel_G_half : QeqT (ptp_G 1 (1#2)) (-(7#512)).
Proof. apply qeq_imp_qeqT. vm_compute. unfold Qeq. simpl. lia. Qed.

Lemma ptp_tail_FG_agree_half : QeqT (ptp_F 1 (1#2)) (ptp_G 1 (1#2)).
Proof. apply ptp_main_fg. Qed.

(* -- Audit and extraction -- *)

Print Assumptions ptp_tail_series.
Print Assumptions ptp_tail_series_k.
Print Assumptions ptp_main_fg.
Print Assumptions ptp_step_core.
Print Assumptions ptp_n1_merge.
Print Assumptions ptp_n1_poly_recheck.

Separate Extraction ptp_tail_series ptp_step_core ptp_n1_merge.

(* ============================ Part 2. Denominator positivity of the Pade approximant on (1,2) ============================ *)
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
Require Import UpReqPadeExp UpReqPadeDenPos UpReqPadeSign UpReqAltSumPos.
Require Import UpReqPadeQLeg.
From Stdlib Require Import QArith.QArith Arith.Arith Lia Setoid.

Local Open Scope Q_scope.

(* Piece 1: the ratio lower bound (for [k < n]) — the new mathematical core
   of this section.  The skeleton mirrors the ratio-geq-one lemma:
   [2 = inv(a) * (2a) <= inv(a) * (b c) = the ratio], where [2a <= b c] is
   carried by a Z-level arithmetic helper (the expanded product is
   nonnegative). *)
Lemma pdq_R_ge_2 : forall n k : nat, (k < n)%nat -> QleT' 2%Q (pdp_R n k).
Proof.
  intros n k Hk.
  assert (Hlit : QleT' ((2 # 1) *
                          (Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1))%Q
                       (((Z.of_nat (Datatypes.S (2 * n - Datatypes.S k)) # 1) *
                         (Z.of_nat (Datatypes.S k) # 1))%Q)).
  { apply Qle_to_QleT'. unfold Qle. cbn [Qnum Qden Qmult Pos.mul].
    pose proof (pql_nat_ratio_mono2 n k Hk) as Hp.
    rewrite !Z.mul_1_r, ?Z.mul_1_l. exact (ZLeT_drop _ _ Hp). }
  assert (Hinvpos : QleT' 0%Q
    (Qinv ((Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1)%Q))).
  { apply qltT_leT'. apply Qlt_to_QltT. apply Qinv_lt_0_compat.
    unfold Qlt, Qcompare. cbn [Qnum Qden]. apply Z.compare_lt_iff.
    rewrite Z.mul_0_l, !Z.mul_1_r, Znat.Nat2Z.inj_succ.
    exact (proj2 (Z.lt_succ_r 0%Z (Z.of_nat (n - Datatypes.S k)))
             (Znat.Nat2Z.is_nonneg (n - Datatypes.S k))). }
  assert (Ez : Qinv ((Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1)) *
               (Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1) == 1%Q).
  { apply (Qeq_trans
      (Qinv ((Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1)) *
       (Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1))
      ((Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1) *
       Qinv ((Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1)))
      1%Q).
    - ring.
    - apply Qmult_inv_r. intro Hc. exact (match pdp_ZS1_nz (n - Datatypes.S k) (qeq_imp_qeqT _ _ Hc) with end). }
  apply (qleT'_trans 2%Q
    (Qinv ((Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1)) *
     (((2 # 1) * (Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1)))%Q)
    (pdp_R n k)).
  - apply qeq_leT'. apply qeq_imp_qeqT. apply Qeq_sym.
    apply (Qeq_trans
      (Qinv ((Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1)) *
       ((2 # 1) * (Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1)))
      (((2 # 1) *
        (Qinv ((Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1)) *
         (Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1))))
      2%Q).
    + ring.
    + rewrite Ez. ring.
  - apply (qleT'_trans
      (Qinv ((Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1)) *
       (((2 # 1) * (Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1)))%Q)
      (Qinv ((Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1)) *
       (((Z.of_nat (Datatypes.S (2 * n - Datatypes.S k)) # 1) *
         (Z.of_nat (Datatypes.S k) # 1)))%Q)
      (pdp_R n k)).
    + apply pdp_qmult_le_compat_l; assumption.
    + apply qeq_leT'. apply qeq_imp_qeqT. unfold pdp_R. ring.
Qed.

(* Piece 2: upgrading the decay face — with [x <= 2] the terms decay
   term by term (mirroring the predecessor decay lemma, with the
   "x <= 1 multiplication-monotonicity step" replaced by the
   "x <= 2 <= ratio" step). *)
Lemma pdq_term_decay_2 : forall (n k : nat) (x : Q),
  (k < n)%nat -> QleT' 0%Q x -> QleT' x 2%Q ->
  QleT' (pdp_g n x (Datatypes.S k)) (pdp_g n x k).
Proof.
  intros n k x Hk Hx0 Hx2.
  assert (E1 : (Datatypes.S k <=? n)%nat = true)
    by (apply Nat.leb_le; exact Hk).
  assert (E2 : (k <=? n)%nat = true)
    by (apply Nat.leb_le; exact (Nat.le_trans _ _ _ (Nat.le_succ_diag_r k) Hk)).
  unfold pdp_g. rewrite E1, E2.
  change (q_pow x (Datatypes.S k)) with (x * q_pow x k).
  assert (HstepT : QleT' (pade_coeff n (Datatypes.S k) * x) (pade_coeff n k)).
  { apply (qleT'_trans (pade_coeff n (Datatypes.S k) * x)
                       (pade_coeff n (Datatypes.S k) * pdp_R n k)
                       (pade_coeff n k)).
    - apply pdp_qmult_le_compat_l.
      + apply (qleT'_trans x 2%Q (pdp_R n k)).
        * exact Hx2.
        * apply pdq_R_ge_2. exact Hk.
      + apply qltT_leT'. apply pdp_coeff_pos_any.
    - apply qeq_leT'. apply qeq_imp_qeqT. apply Qeq_sym. apply qeqT_imp_qeq.
      apply pdp_coeff_ratio. exact Hk. }
  apply (qleT'_trans
           (pade_coeff n (Datatypes.S k) * (x * q_pow x k))
           ((pade_coeff n (Datatypes.S k) * x) * q_pow x k)
           (pade_coeff n k * q_pow x k)).
  - apply qeq_leT'. apply qeq_imp_qeqT. ring.
  - apply pdp_qmult_le_compat_r.
    + exact HstepT.
    + apply q_pow_nonneg. exact Hx0.
Qed.

(* Piece 3 (main, non-strict): [1 < x < 2] implies [0 <= Q_n(x)].
   The statement face matches the predecessor positivity lemma (conclusion
   on the [QleT'] face); the skeleton is the same, with only the decay
   premise replaced by the upgraded one. *)
Theorem pdq_den_pos_12 : forall (n : nat) (x : Q),
  QltT 1%Q x -> QltT x 2%Q -> QleT' 0%Q (pade_den n x).
Proof.
  intros n x Hlo Hhi.
  assert (Hx0 : QleT 0%Q x).
  { left. apply Qlt_to_QltT. apply (Qlt_trans 0%Q 1%Q x).
    - unfold Qlt. reflexivity.
    - apply QltT_to_Qlt. exact Hlo. }
  assert (Hxa : QleT' 0%Q x) by (apply altsum_QleT_to_QleT'; exact Hx0).
  assert (Hx2 : QleT' x 2%Q)
    by (apply Qle_to_QleT'; apply Qlt_le_weak; apply QltT_to_Qlt; exact Hhi).
  assert (Hb : pade_den n x == altsum (pdp_g n x) (Datatypes.S n))
    by (apply qeqT_imp_qeq; apply pdp_den_altsum).
  apply (qleT'_trans 0%Q (altsum (pdp_g n x) (Datatypes.S n)) (pade_den n x)).
  - apply altsum_nonneg_leT.
    + intro k. apply pdp_g_nonneg. exact Hxa.
    + intro k. destruct (Nat.leb (Datatypes.S k) n) eqn:E.
      * apply pdq_term_decay_2;
          [apply Nat.leb_le in E; exact E | exact Hxa | exact Hx2].
      * apply pdp_g_decay_hi; [exact Hxa | apply Nat.leb_gt in E; exact E].
  - apply qeq_leT'. apply qeq_imp_qeqT. apply Qeq_sym. exact Hb.
Qed.

(* ============================================================ *)
(* Piece 4: support for the strict version (a strict first pair, supplied directly by the alternating-sum strict engine). *)
(* ============================================================ *)

(* Piece 4a: [g(0) = 1] (the constant coefficient is one and [x^0 = 1], for every n). *)
Lemma pdq_g0_one : forall (n : nat) (x : Q), QeqT (pdp_g n x 0%nat) (1%Q).
Proof.
  intros n x. apply qeq_imp_qeqT. unfold pdp_g.
  assert (E0 : (0 <=? n)%nat = true)
    by (apply Nat.leb_le; exact (Nat.le_0_l n)).
  rewrite E0. cbn [q_pow].
  rewrite (qeqT_imp_qeq _ _ (pade_coeff_0_one n)). ring.
Qed.

(* Piece 4b: the first pair is strict, [g(1) < g(0)] — without computing
   the first coefficient explicitly, via the ratio identity
   [c_0 == c_1 * R_0], [x < 2 <= R_0] and [c_1 > 0]. *)
Lemma pdq_g1_lt_g0 : forall (n : nat) (x : Q),
  (1 <= n)%nat -> QltT 1%Q x -> QltT x 2%Q ->
  QltT (pdp_g n x 1%nat) (pdp_g n x 0%nat).
Proof.
  intros n x Hn Hlo Hhi.
  assert (Hk : (0 < n)%nat) by exact Hn.
  assert (E0 : (0 <=? n)%nat = true)
    by (apply Nat.leb_le; exact (Nat.le_trans _ _ _ (Nat.le_0_l 1) Hn)).
  assert (E1 : (1 <=? n)%nat = true) by (apply Nat.leb_le; exact Hn).
  unfold pdp_g. rewrite E1, E0. cbn [q_pow].
  apply Qlt_to_QltT.
  repeat rewrite Qmult_1_r.
  rewrite (qeqT_imp_qeq _ _ (pdp_coeff_ratio n 0%nat Hk)).
  assert (Hc : x * pade_coeff n (Datatypes.S 0)
               < pdp_R n 0 * pade_coeff n (Datatypes.S 0)).
  { apply (Qmult_lt_compat_r x (pdp_R n 0) (pade_coeff n (Datatypes.S 0))).
    - apply QltT_to_Qlt. apply pdp_coeff_pos_any.
    - apply (Qlt_le_trans x 2%Q (pdp_R n 0)).
      + apply QltT_to_Qlt. exact Hhi.
      + apply QleT'_to_Qle. apply pdq_R_ge_2. exact Hk. }
  rewrite (Qmult_comm (pade_coeff n (Datatypes.S 0)) x).
  rewrite (Qmult_comm (pade_coeff n (Datatypes.S 0)) (pdp_R n 0)).
  exact Hc.
Qed.

(* Piece 4c: the closed form at n = 1, [den_1(x) == 1 - x/2] (with the numeric anchor coefficient explicit). *)
Lemma pdq_den1_form : forall x : Q,  
 QeqT (pade_den 1%nat x) (1%Q + Qopp ((1#2)%Q * x)).
Proof.
  intros x. apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (pdp_den_altsum 1%nat x)).
  unfold altsum.
  rewrite (qeqT_imp_qeq _ _ (altsum_acc_T (pdp_g 1%nat x) 0%nat 1%nat)).
  rewrite (qeqT_imp_qeq _ _ (altsum_acc_F (pdp_g 1%nat x) 1%nat 0%nat)).
  rewrite (qeqT_imp_qeq _ _ (altsum_acc_0_eq true (pdp_g 1%nat x) 2%nat)).
  assert (E0 : (0 <=? 1)%nat = true)
    by (apply Nat.leb_le; exact (Nat.le_0_l 1)).
  assert (E1 : (1 <=? 1)%nat = true)
    by (apply Nat.leb_le; exact (Nat.le_refl 1)).
  unfold pdp_g. rewrite E0, E1. cbn [q_pow].
  rewrite (qeqT_imp_qeq _ _ (pade_coeff_0_one 1%nat)).
  rewrite (qeqT_imp_qeq _ _ pds_c11). ring.
Qed.

(* Piece 4c': the closed form at n = 0, [den_0(x) == 1] (independent of the argument). *)
Lemma pdq_den0_one : forall x : Q, QeqT (pade_den 0%nat x) (1%Q).
Proof.
  intros x. apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (pdp_den_altsum 0%nat x)).
  unfold altsum.
  rewrite (qeqT_imp_qeq _ _ (altsum_acc_T (pdp_g 0%nat x) 0%nat 0%nat)).
  rewrite (qeqT_imp_qeq _ _ (altsum_acc_0_eq false (pdp_g 0%nat x) 1%nat)).
  rewrite (qeqT_imp_qeq _ _ (pdq_g0_one 0%nat x)). ring.
Qed.

(* Piece 4d: the half-linearity fact is inlined into the n = 1 branch of
   piece 5 (the Prop-order derivation lives only inside the proof; no
   separate Prop statement is created). *)

(* ============================================================ *)
(* Piece 5 (main, strict): [1 < x < 2] implies [0 < Q_n(x)] for every n.  For n >= 2 the strict alternating-sum engine applies (a strict first pair plus a nonnegative tail); n = 0 is constantly one and n = 1 has the closed form [1 - x/2 > 0]. *)
(*   For n >= 2 the strict alternating-sum engine applies (a strict first pair plus a nonnegative tail); n = 0 is constantly one and *)
(*   n = 1 has the closed form 1 - x/2 > 0. *)
(* ============================================================ *)
Theorem pdq_den_pos_12_strict : forall (n : nat) (x : Q),
  QltT 1%Q x -> QltT x 2%Q -> QltT 0%Q (pade_den n x).
Proof.
  intros n x Hlo Hhi.
  assert (Hx2 : QleT' x 2%Q)
    by (apply Qle_to_QleT'; apply Qlt_le_weak; apply QltT_to_Qlt; exact Hhi).
  destruct n as [|[|m]].
  - apply Qlt_to_QltT. rewrite (qeqT_imp_qeq _ _ (pdq_den0_one x)). unfold Qlt. reflexivity.
  - apply Qlt_to_QltT. rewrite (qeqT_imp_qeq _ _ (pdq_den1_form x)).
    apply QltT_to_Qlt in Hhi.
    assert (Hp : 0%Q < (1#2)%Q).
    { apply (Qinv_lt_0_compat 2%Q). unfold Qlt. reflexivity. }
    assert (Hs : x * (1#2)%Q < 2 * (1#2)%Q).
    { apply Qmult_lt_compat_r.
      - exact Hp.
      - exact Hhi. }
    pose proof Hs as Hs2.
    rewrite (Qmult_comm x (1#2)%Q), (Qmult_comm 2%Q (1#2)%Q) in Hs2.
    assert (E21 : (1#2)%Q * 2%Q == 1%Q) by ring.
    rewrite E21 in Hs2.
    apply (proj1 (Qlt_minus_iff ((1#2)%Q * x) 1%Q)).
    exact Hs2.
  - assert (Hxa : QleT' 0%Q x).
    { apply altsum_QleT_to_QleT'.
      left. apply Qlt_to_QltT. apply (Qlt_trans 0%Q 1%Q x).
      - unfold Qlt. reflexivity.
      - apply QltT_to_Qlt. exact Hlo. }
    assert (Hdec : forall k : nat,
              QleT' (pdp_g (Datatypes.S (Datatypes.S m)) x (Datatypes.S k))
                    (pdp_g (Datatypes.S (Datatypes.S m)) x k)).
    { intro k.
      destruct (Nat.leb (Datatypes.S k) (Datatypes.S (Datatypes.S m))) eqn:E.
      - apply pdq_term_decay_2;
          [apply Nat.leb_le in E; exact E | exact Hxa | exact Hx2].
      - apply pdp_g_decay_hi; [exact Hxa | apply Nat.leb_gt in E; exact E]. }
    apply (qeq_ltT
             (altsum (pdp_g (Datatypes.S (Datatypes.S m)) x)
                     (Datatypes.S (Datatypes.S (Datatypes.S m))))
             (pade_den (Datatypes.S (Datatypes.S m)) x)).
    + apply qeq_imp_qeqT. apply Qeq_sym. apply qeqT_imp_qeq.
      apply pdp_den_altsum.
    + apply altsum_pos_strict.
      * intro k. apply pdp_g_nonneg. exact Hxa.
      * exact Hdec.
      * apply pdq_g1_lt_g0;
          [exact (Nat.le_le_succ_r 1 (Datatypes.S m)
                    (proj1 (Nat.succ_le_mono 0 m) (Nat.le_0_l m)))
          | exact Hlo | exact Hhi].
      * exact (Nat.le_le_succ_r 2 (Datatypes.S (Datatypes.S m))
                 (proj1 (Nat.succ_le_mono 1 (Datatypes.S m))
                        (proj1 (Nat.succ_le_mono 0 m) (Nat.le_0_l m)))).
Qed.

Print Assumptions pdq_den_pos_12.
Print Assumptions pdq_den_pos_12_strict.

(* ============================ Part 3. The small-transfer lemma statements ============================ *)
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
Require Import UpReqPadeLower.
From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith Lia Setoid.

(* ============================================================ *)
(* Bridging lemmas: small Q-layer combinators (self-contained, no external dependencies). *)
(* ============================================================ *)

(* [a < b] implies [0 < b - a] (on the [QltT] face).
   Route: the successor-difference lemma at z := -a plus the opposite and
   commutativity reshapes; the subtraction is definitionally the sum with
   the opposite.  (A destruct-lia route is unavailable: the positivity of
   denominators is out of its reach.) *)
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

(* [0 < x] implies [x/2 < x] (strict contraction of the half).
   By destruct-lia on the polynomial form: the premise is 0 < nx*dx and
   the goal is linear in P := nx*dx (the same family as the strict-implies-
   weak lemma). *)
Lemma qtr_div2_lt : forall x : Q, Qlt 0 x -> QltT (x / 2) x.
Proof.
  intros x H. apply Qlt_to_QltT. unfold Qlt in *.
  destruct x as [nx dx]. simpl in *. lia.
Qed.

Lemma qtr_div2_ltT : forall x : Q, QltT 0 x -> QltT (x / 2) x.
Proof.
  intros x H. apply qtr_div2_lt.
  apply QltT_to_Qlt. exact H.
Qed.

(* Cancellation certificate: [m <> 0] implies [(a/m) * m == a] (via the inverse-multiplication law; no division goals). *)
Lemma qtr_div_cancel : forall a m : Q, ~ (m == 0) -> QeqT (a / m * m) (a).
Proof.
  intros a m Hm. apply qeq_imp_qeqT. unfold Qdiv.
  rewrite <- (Qmult_assoc a (/ m) m).
  rewrite (Qmult_comm (/ m) m).
  rewrite (Qmult_inv_r m Hm).
  apply Qmult_1_r.
Qed.

(* ============================================================ *)
(* The order-preserving embedding bridge: a Q-layer order gives the embedded Real-layer order. *)
(* ============================================================ *)

(* Strict form: [a < b] implies the embedded constants compare strictly.
   Witness eps := (b-a)/2 > 0 with index N := 0 (the constant sequences
   agree pointwise). *)
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
    + apply qeq_imp_qeqT. exact Hraw.
    + exact Hhalf.
Qed.

(* Weak form: [a <= b] implies the embedded constants compare weakly (a
   three-form Real-order face: the strict branch goes through the embedding
   bridge; the equal branch goes through the absolute-value-zero
   congruence). *)
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
      - apply Qabs_wd. apply Qminus_comp; apply qeqT_imp_qeq;
        apply real_const_proj.
      - apply Qeq_trans with (y := Qabs 0).
        + apply Qabs_wd. exact Hab0.
        + apply Qeq_refl. }
    apply qltT_eq_compat_l with (a := 0%Q).
    + apply qeq_imp_qeqT. apply Qeq_sym. exact Habs0.
    + exact Heps.
Qed.

(* ============================================================ *)
(* The series bridge pier: the Q-layer lower bound for the partial-sum tail difference (the exponential dominates its partial sums). *)
(* ============================================================ *)

(* First-term lower bound on the tail difference: for [0 <= y] and [d >= 0],
   [y^(n+1)/(n+1)! <= E_(n+1+d)(y) - E_n(y)].
   Induction invariant: each step appends the nonnegative term [y^k/k!]. *)
Lemma qtr_partial_gap : forall (y : Q) (n d : nat), QleT 0 y -> 
  QleT' (q_pow y (Datatypes.S n) / q_fact (Datatypes.S n))
       (exp_partial (Datatypes.S n + d) y - exp_partial n y).
Proof.
  intros y n d Hy. revert d.
  assert (Hy0 : Qle 0 y) by (apply qtail_QleT_to_Qle; exact Hy).
  induction d as [| d IH].
  - replace (Datatypes.S n + 0)%nat with (Datatypes.S n)%nat by lia.
    change (exp_partial (Datatypes.S n) y) with
      (exp_partial n y + q_pow y (Datatypes.S n) / q_fact (Datatypes.S n)).
    (* Atomizing the divisions: the ring tactic does not act on division atoms (a known pitfall). *)
    set (T := q_pow y (Datatypes.S n) / q_fact (Datatypes.S n)).
    apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
  - replace (Datatypes.S n + Datatypes.S d)%nat
      with (Datatypes.S (Datatypes.S n + d))%nat by lia.
    change (exp_partial (Datatypes.S (Datatypes.S n + d)) y) with
      (exp_partial (Datatypes.S n + d) y
       + q_pow y (Datatypes.S (Datatypes.S n + d))
         / q_fact (Datatypes.S (Datatypes.S n + d))).
    set (T2 := q_pow y (Datatypes.S (Datatypes.S n + d))
                 / q_fact (Datatypes.S (Datatypes.S n + d))).
    apply (qleT'_trans _
             ((exp_partial (Datatypes.S n + d) y - exp_partial n y) + T2)%Q _).
    + (* The first term is at most the old tail, which is at most the old tail plus the new nonnegative term. *)
      apply (qleT'_trans _ (exp_partial (Datatypes.S n + d) y - exp_partial n y) _).
      * exact IH.
      * apply qtail_le_plus_r.
        unfold T2. apply QleT'_to_Qle. apply q_pow_fact_nonneg.
        apply Qle_to_QleT'. exact Hy0.
    + (* Reshaping: the difference-plus-tail reassociates (by ring; divisions already atomized). *)
      apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
Qed.

(* ============================================================ *)
(* The series bridge: the Real-layer exponential dominates the n-th partial sum (eps-witness form). *)
(* ============================================================ *)

(* Strict form: for [y > 0] the embedded partial sum is strictly below the
   exponential.  Witness eps := (y^(n+1)/(n+1)!)/2 > 0 with N := n+1: the
   pointwise difference of partial sums is at least y^(n+1)/(n+1)! > eps
   for every m >= n+1 (the tail grows). *)
Theorem qtr_exp_gt_partial : forall (y : Q) (n : nat), QltT 0 y ->
  real_lt (real_const (exp_partial n y)) (cauchy_real_exp (real_const y)).
Proof.
  intros y n Hy.
  assert (Hterm : QltT 0 (q_pow y (Datatypes.S n) / q_fact (Datatypes.S n))).
  { apply qltT_div_pos.
    - apply (cpl_qpow_pos y (Datatypes.S n)).
      apply QltT_to_Qlt. exact Hy.
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
      - apply qeqT_imp_qeq. apply exp_const_proj.
      - apply qeqT_imp_qeq. apply real_const_proj. }
    assert (Hgap : Qle (q_pow y (Datatypes.S n) / q_fact (Datatypes.S n))
                       (exp_partial m y - exp_partial n y)).
    { replace m with (Datatypes.S n + (m - Datatypes.S n))%nat by lia.
      apply QleT'_to_Qle. apply qtr_partial_gap.
      left. exact Hy. }
    assert (HgapT : QltT (q_pow y (Datatypes.S n) / q_fact (Datatypes.S n) / 2)
                         (exp_partial m y - exp_partial n y)).
    { apply Qlt_to_QltT.
      apply (Qlt_le_trans _ (q_pow y (Datatypes.S n) / q_fact (Datatypes.S n))).
      - apply QltT_to_Qlt. apply qtr_div2_lt. apply QltT_to_Qlt. exact Hterm.
      - exact Hgap. }
    apply qltT_eq_compat_r with (a' := (exp_partial m y - exp_partial n y)%Q).
    + apply qeq_imp_qeqT. exact Hraw.
    + exact HgapT.
Qed.

(* Weak form: for [y >= 0] the embedded partial sum is below the exponential
   (a three-form Real-order face: the strict branch goes through the series
   bridge; the y == 0 branch goes through the congruence of the all-ones
   partial sum, with the Id branch resolved by a case split into Qeq). *)
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
          * apply qeqT_imp_qeq. apply real_const_proj.
          * exact Hn1.
        + apply Qeq_trans with (y := exp_partial k y).
          * apply qeqT_imp_qeq. apply exp_const_proj.
          * apply Hk1.
      - apply Qeq_trans with (y := Qabs 0).
        + apply Qabs_wd. ring.
        + apply Qeq_refl. }
    apply qltT_eq_compat_l with (a := 0%Q).
    + apply qeq_imp_qeqT. apply Qeq_sym. exact Habs0.
    + exact Heps.
Qed.

(* ============================================================ *)
(* The core: left congruence of the Real product under Real equality (the transport engine). *)
(* ============================================================ *)

(* The cancellation certificate is available.
   Left congruence: [x == z] implies [x*v == z*v] (on the Real-equality
   face).  Route: bound the norm of the second factor by its modulus, slack
   the eps by half, and conclude
   [the difference norm times the factor norm <= (eps/2/M) * M == eps/2 < eps]
   (via the nonnegative-multiplication monotonicity and the inverse
   certificate; no division goals). *)
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
  (* Half-amount scaling: feed eps/2 into the equality transport; the final eps/2 < eps step restores strictness. *)
  destruct (Heq (eps / 2 / Mv')
    (qltT_div_pos (eps / 2) Mv'
       (qltT_div_pos eps 2%Q Heps qltT_0_2) HMv'posT)) as [N HN].
  exists N. intros n Hn.
  specialize (HN n Hn).
  (* The difference premise: the norm of the difference is below eps/2 scaled. *)
  assert (Hwn : Qle (Qabs (w n)) Mv').
  { apply (Qle_trans _ Mv _).
    - apply (QleT'_to_Qle _ _ (HMv n)).
    - apply (Qle_trans _ (Qabs Mv) _).
      + apply Qle_Qabs.
      + apply Qle_plus_nonneg_r.
        (* [0 <= 1]: after unfolding the Q-order, a Z-level lia step. *)
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
      + apply QleT'_to_Qle. apply qeq_imp_qle.
        apply qtr_div_cancel. intro Hmz.
        exact (match qtail_neq0 Mv' HMv'0 (qeq_imp_qeqT _ _ Hmz) with end).
    - apply QltT_to_Qlt. apply qtr_div2_lt.
      apply QltT_to_Qlt. exact Heps. }
  apply qltT_eq_compat_l with (a := Qabs (u n - z n) * Qabs (w n)).
  - apply qeq_imp_qeqT. apply Qeq_sym. exact Hab.
  - exact Hchain.
Qed.

(* ============================================================ *)
(* The main statement: the first Real-layer lower bound for the Pade accuracy (over an arbitrary carrier). *)
(* ============================================================ *)

(* For [y > 0] and [w] any Real representative of the exponential (equal in
   the Real sense), the product dominates: the numerator times the
   denominator is below w times the denominator (in the multiplication-
   expanded, division-free form).
   Transport route: from the lower-bound module's statement on its
   distinguished diagonal carrier, through the strict-order transfer and
   the left congruence of the Real product, to an arbitrary carrier. *)
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
(* The converse bridge: unpacking a strict Real certificate into an explicit pointwise index/eps account. *)
(* (Witness reflection: the Real-layer statement gives the pointwise
   Q-layer accuracy account; the index and eps are passed through verbatim
   from the sigT witness of the lower-bound module: y^5/720 with N := 6.) *)
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
      - apply qeqT_imp_qeq. apply real_mult_proj.
      - apply Qmult_comp.
        + apply qeqT_imp_qeq. apply exp_const_proj.
        + apply qeqT_imp_qeq. apply real_const_proj. }
    assert (Hconst : projT1 (real_const (pade_num 2%nat y)) m
                     == pade_num 2%nat y).
    { apply qeqT_imp_qeq. apply real_const_proj. }
    assert (Hraw : projT1 (real_mult (cauchy_real_exp (real_const y))
                                     (real_const (pade_den 2%nat y))) m
                   - projT1 (real_const (pade_num 2%nat y)) m
                   == exp_partial m y * pade_den 2%nat y
                      - pade_num 2%nat y).
    { apply Qminus_comp.
      - exact Hmult.
      - exact Hconst. }
    exact (qltT_eq_compat_r _ _ _
              (qeq_imp_qeqT _ _ (Qeq_sym _ _ Hraw)) HN).
Qed.

(* The weak-form companion (three-form Real order): for [y > 0] and [w] representing the exponential, the numerator is dominated by the product. *)
Theorem qtr_pade_lower_real_le : forall (y : Q) (w : Real), QltT 0 y ->
  real_eq w (cauchy_real_exp (real_const y)) ->
  real_le (real_const (pade_num 2%nat y))
          (real_mult w (real_const (pade_den 2%nat y))).
Proof.
  intros y w Hy Hw. left.
  apply (qtr_pade_lower_real y w Hy Hw).
Qed.

(* ============================================================ *)
(* Certification face (assumption audit: every statement should print Closed). *)
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
