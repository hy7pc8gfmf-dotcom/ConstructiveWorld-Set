(* ConstructiveWorld-Set -- RealIdentity: the Real-layer statement face and assembly of the ln2 approximation identity. *)

(** * RealIdentity: statement face and assembly over the Real layer for the ln2 approximation identity.

    Mission.  The Real-carrier input interface ri_Iface (nat -> Real) for I_n = 2^{n+1} * q~_n * ln2 - r_n,
      the pointwise exact core algebra c_n * |X_k - x'_n| == |c_n * X_k - r_n| (ri_core_pt), the
      conditional assembly ri_identity_assembly of the target identity
      real_metric X (real_const x'_n) == I_n/c_n, the upper-bound transfer ri_upper_transfer, and
      the four-piece numerical anchor group.

    Dependencies.  QArith, QArith.Qabs, Arith, ZArith, Lia, Setoid, Morphisms; S01_BaseRing,
      S02_CauchyComplete, S03_QExp; UpReqIrrationalCriterion, UpReqLn2Irrational; BeukersLists,
      BeukersVariant, TrueNumerator.

    References.  Apéry-type convergence acceleration and the Real-layer identity behind the
      irrationality proofs of ln2 (rational approximation theory); interface-generation
      alignment per UpReqMisc5B precedent (NatLe_drop bridge).

    Constructivity.  Every proof closes in Qed with zero admission lexicon; the statement face is
      all Set (QeqT / real_eq / real_le / sigT); extractable; the Print Assumptions audit at the
      file end re-checks zero dependencies.

    Build.  coqc 9.1 direct invocation (no -Q), wrapped in cpu_guard, -o into a scratch output
      directory, in-tree .vo untouched; the artifact starts with [436f7121 000160bc]. *)
From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith ZArith.ZArith Lia.
From Stdlib Require Import Setoid Morphisms.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp.
Require Import UpReqIrrationalCriterion UpReqLn2Irrational.
Require Import BeukersLists BeukersVariant TrueNumerator.

Open Scope nat_scope.

(* ============================================================ *)
(* §A the Real carrier and the statement face of x'_n (real embedding of Q constants)                             *)
(* ============================================================ *)

(* the Real carrier of ln2: the Cauchy limit of ln2i_x (its tail-control and vanishing
   certificates are supplied by the source module; same defining face as Ln2Bridge.ln2b_X,
   named independently to avoid cross-file name clashes) *)
Definition ri_real : Real :=
  existT (fun u : Qseq => cauchy u) ln2i_x
    (lic_seq_cauchy ln2i_x ln2i_e ln2i_tail ln2i_vanish).

Lemma ri_real_proj : forall k : nat, projT1 ri_real k == ln2i_x k.
Proof. intro k. exact (Qeq_refl (ln2i_x k)). Qed.

(* ri_x: x'_n := p_n/q~_n (that is, bv_x; a Q constant, embedded into the Real layer via real_const) *)
Definition ri_x (n : nat) : Q := bv_x n.

(* ri_x_eq_pn_qn: ri_x n == bv_p n / q~_n *)
Lemma ri_x_eq_pn_qn : forall n : nat,
  QeqT (ri_x n) (bv_p n / (Z.of_nat (bk_Qn_qtilde n) # 1)%Q).
Proof.
  intro n.
  unfold ri_x, bv_x.
  apply qeq_imp_qeqT.
  exact (Qeq_refl (bv_p n / (Z.of_nat (bk_Qn_qtilde n) # 1)%Q)).
Qed.

(* ri_x_eq_tn: ri_x n == tn_x n (read backwards from tn_x_eq_bv_x across the Qeq bridge) *)
Lemma ri_x_eq_tn : forall n : nat, QeqT (ri_x n) (tn_x n).
Proof.
  intro n. unfold ri_x. apply qeq_imp_qeqT. symmetry.
  apply qeqT_imp_qeq. apply tn_x_eq_bv_x.
Qed.

(* ============================================================ *)
(* §B the normalization-factor face: c_n := 2^{n+1} * q~_n                                     *)
(* ============================================================ *)

Definition ri_qnorm (n : nat) : Q :=
  (q_pow (2 # 1)%Q (Datatypes.S n) * (Z.of_nat (bk_Qn_qtilde n) # 1)%Q)%Q.

Lemma ri_pow3_ge1 : forall n : nat, (1 <= 3 ^ n)%nat.
Proof.
  induction n as [| n IH].
  - cbn. lia.
  - rewrite Nat.pow_succ_r'. lia.
Qed.

Lemma ri_qtilde_ge1 : forall n : nat, (1 <= bk_Qn_qtilde n)%nat.
Proof.
  intro n. pose proof (NatLe_drop (3 ^ n) (bk_Qn_qtilde n) (bk_Qn_ge_3pow_nat n)) as H3.
  pose proof (ri_pow3_ge1 n) as H1. lia.
Qed.

Lemma ri_qtilde_pos : forall n : nat, Qlt 0 ((Z.of_nat (bk_Qn_qtilde n) # 1)%Q).
Proof.
  intro n. unfold Qlt. cbn [Qnum Qden].
  pose proof (proj1 (Nat2Z.inj_le 1 (bk_Qn_qtilde n)) (ri_qtilde_ge1 n)) as Hz.
  lia.
Qed.

Lemma ri_qtilde_ne0 : forall n : nat,
  ~ ((Z.of_nat (bk_Qn_qtilde n) # 1)%Q == 0%Q).
Proof.
  intros n Hc. unfold Qeq in Hc. cbn [Qnum Qden] in Hc.
  pose proof (proj1 (Nat2Z.inj_le 1 (bk_Qn_qtilde n)) (ri_qtilde_ge1 n)) as Hz.
  lia.
Qed.

Lemma ri_qpow2_pos : forall k : nat, Qlt 0 (q_pow (2 # 1)%Q k).
Proof.
  induction k as [| k IH].
  - unfold Qlt. cbn [q_pow Qnum Qden]. lia.
  - cbn [q_pow]. apply Qmult_lt_0_compat.
    + unfold Qlt. cbn [Qnum Qden]. lia.
    + exact IH.
Qed.

Lemma ri_qnorm_pos : forall n : nat, Qlt 0 (ri_qnorm n).
Proof.
  intro n. unfold ri_qnorm. apply Qmult_lt_0_compat.
  - apply ri_qpow2_pos.
  - apply ri_qtilde_pos.
Qed.

Lemma ri_qnorm_ne0 : forall n : nat, ~ (ri_qnorm n == 0%Q).
Proof.
  intros n Hc. unfold ri_qnorm in Hc.
  apply (Qmult_integral _ _) in Hc. destruct Hc as [H1 | H2].
  - exact (match (tn_qpow2_ne (Datatypes.S n) (qeq_imp_qeqT _ _ H1)) with end).
  - exact (ri_qtilde_ne0 n H2).
Qed.

(* ============================================================ *)
(* §C the metric face (projection via lic_metric_proj), the line face, and the pointwise exact algebra core                  *)
(* ============================================================ *)

(* ri_metric: the projection object of real_metric ri_real (real_const x'_n) *)
Definition ri_metric (n : nat) : Real :=
  real_metric ri_real (real_const (ri_x n)).

Lemma ri_metric_proj : forall (n k : nat),
  projT1 (ri_metric n) k == Qabs ((ln2i_x k - ri_x n)%Q).
Proof.
  intros n k. unfold ri_metric.
  rewrite lic_metric_proj. rewrite ri_real_proj. reflexivity.
Qed.

(* ri_lineabs: the line face |c_n * X - r_n| (the pointwise Real-layer reading of I_n;
   the rational-constant form -- the p_n/q~_n-normalized counterpart of the integer-coefficient
   line face consumed by the supply side, see §E) *)
Definition ri_lineabs (n : nat) : Real :=
  real_abs (real_plus (real_mult (real_const (ri_qnorm n)) ri_real)
                      (real_opp (real_const (tn_r n)))).

Lemma ri_lineabs_proj : forall (n k : nat),
  projT1 (ri_lineabs n) k == Qabs ((ri_qnorm n * ln2i_x k - tn_r n)%Q).
Proof.
  intros n k. unfold ri_lineabs.
  rewrite (qeqT_imp_qeq _ _ (real_abs_proj _ _)), (qeqT_imp_qeq _ _ (real_plus_proj _ _ _)),
          (qeqT_imp_qeq _ _ (real_mult_const_proj _ _ _)), (qeqT_imp_qeq _ _ (real_opp_proj _ _)),
          (qeqT_imp_qeq _ _ (real_const_proj _ _)), ri_real_proj.
  reflexivity.
Qed.

(* closure under the normalized product: c_n * x'_n == r_n (the Q-layer form of x'_n = r_n/c_n) *)
Lemma ri_cx_eq_r : forall n : nat, (ri_qnorm n * ri_x n)%Q == tn_r n.
Proof.
  intro n. unfold ri_qnorm, ri_x, bv_x, Qdiv.
  transitivity (q_pow (2 # 1)%Q (Datatypes.S n)
                * (bv_p n * ((Z.of_nat (bk_Qn_qtilde n) # 1)%Q
                             * Qinv ((Z.of_nat (bk_Qn_qtilde n) # 1)%Q))))%Q.
  - ring.
  - rewrite (Qmult_inv_r (Z.of_nat (bk_Qn_qtilde n) # 1)%Q (ri_qtilde_ne0 n)).
    rewrite Qmult_1_r. reflexivity.
Qed.

(* ri_core_pt (purely Q-layer, pointwise exact): c_n * |X_k - x'_n| == |c_n * X_k - r_n|
   -- the algebraic body of the corrected identity at the Real layer (the core of the equality face) *)
Lemma ri_core_pt : forall (n k : nat),
  (ri_qnorm n * Qabs ((ln2i_x k - ri_x n)%Q))%Q
  == Qabs ((ri_qnorm n * ln2i_x k - tn_r n)%Q).
Proof.
  intros n k.
  assert (Hsplit : Qabs ((ri_qnorm n * ln2i_x k - tn_r n)%Q)
                   == Qabs ((ri_qnorm n * (ln2i_x k - ri_x n))%Q)).
  { rewrite <- (ri_cx_eq_r n). apply Qabs_wd. unfold Qminus. ring. }
  rewrite Hsplit.
  rewrite (Qabs_Qmult (ri_qnorm n) (ln2i_x k - ri_x n)%Q).
  rewrite (Qabs_pos (ri_qnorm n) (Qlt_le_weak 0%Q (ri_qnorm n) (ri_qnorm_pos n))).
  reflexivity.
Qed.

(* ri_metric_line_scale: the line face == c_n * the metric face (pointwise; the input form consumed by the supply side) *)
Lemma ri_metric_line_scale : forall (n k : nat),
  projT1 (ri_lineabs n) k == (ri_qnorm n * projT1 (ri_metric n) k)%Q.
Proof.
  intros n k. rewrite ri_lineabs_proj. rewrite ri_metric_proj.
  symmetry. apply ri_core_pt.
Qed.

(* ============================================================ *)
(* §D the Real-layer statement (conditional form) of the target identity and its assembly: ri_identity_assembly         *)
(* ============================================================ *)

(* ri_Iface: the Real-layer input face on the I_n side (nat -> Real);
   the volume face of I_n itself (the partial-fraction decomposition) still lies outside the
   library, see the scope note in the file header *)
Definition ri_Iface : Set := nat -> Real.

(* ri_identity_leg (the input face): Ireal_n == |c_n * X - r_n| == I_n (Real layer) *)
Definition ri_identity_leg (Ireal : ri_Iface) : Set :=
  forall n : nat, real_eq (Ireal n) (ri_lineabs n).

(* ri_identity_spec (the target identity):
   real_metric X (real_const x'_n) == I_n/(2^{n+1} * q~_n) (Real layer) *)
Definition ri_identity_spec (Ireal : ri_Iface) : Set :=
  forall n : nat,
    real_eq (ri_metric n)
            (real_mult (Ireal n) (real_const (Qinv (ri_qnorm n)))).

(* ri_eps_core (purely Q-layer support): c * m == L, 0 < c, |I - L| < c * eps
   imply |m - I * c^-1| < eps (all the remaining algebra of the identity assembly) *)
Lemma ri_eps_core : forall c m I L eps : Q,
  (c * m == L)%Q -> Qlt 0 c -> Qlt (Qabs (I - L)) (c * eps)%Q ->
  Qlt (Qabs (m - I * Qinv c)%Q) eps.
Proof.
  intros c m I L eps Hcm Hc Hlt.
  assert (Hc0 : ~ (c == 0%Q)).
  { intro Hz. apply (Qlt_not_eq 0%Q c Hc).
    apply Qeq_sym. exact Hz. }
  assert (Hinv : (c * Qinv c)%Q == 1%Q) by (apply Qmult_inv_r; exact Hc0).
  assert (Hic0 : Qlt 0 (Qinv c)) by (apply Qinv_lt_0_compat; exact Hc).
  assert (Hs : (m - I * Qinv c)%Q == ((L - I) * Qinv c)%Q).
  { assert (HmL : (L * Qinv c)%Q == m%Q).
    { rewrite <- Hcm. transitivity (m * (c * Qinv c))%Q.
      - ring.
      - rewrite Hinv. apply Qmult_1_r. }
    unfold Qminus. rewrite <- HmL. ring. }
  rewrite Hs. rewrite Qabs_Qmult. rewrite (Qabs_Qminus L I).
  assert (Habs : Qabs (Qinv c) == Qinv c)
    by (apply Qabs_pos; apply Qlt_le_weak; exact Hic0).
  rewrite Habs.
  assert (Hstep : (c * eps * Qinv c)%Q == eps%Q).
  { transitivity (eps * (c * Qinv c))%Q.
    - ring.
    - rewrite Hinv. apply Qmult_1_r. }
  rewrite <- Hstep.
  apply (Qmult_lt_compat_r (Qabs (I - L)) (c * eps)%Q (Qinv c) Hic0).
  exact Hlt.
Qed.

(* ri_identity_assembly: once the Ireal input face is supplied, the Real-layer instance of the
   target identity dissolves.  route: the pointwise core (exact, via ri_core_pt) plus reading
   the eps witness off the input face and dividing by c_n.
   (a QltT goal is first lowered to the Qlt reasoning face and then rewritten, in the style of
   lic_tail_e) *)
Theorem ri_identity_assembly : forall Ireal : ri_Iface,
  ri_identity_leg Ireal -> ri_identity_spec Ireal.
Proof.
  intros Ireal Hleg n eps Heps.
  assert (Hce : QltT 0 ((ri_qnorm n * eps)%Q)).
  { apply Qlt_to_QltT. apply Qmult_lt_0_compat.
    - apply ri_qnorm_pos.
    - apply QltT_to_Qlt. exact Heps. }
  destruct (Hleg n ((ri_qnorm n * eps)%Q) Hce) as [N HN].
  exists N. intros k Hk.
  pose proof (QltT_to_Qlt _ _ (HN k Hk)) as HNk.
  apply Qlt_to_QltT.
  rewrite ri_metric_proj.
  rewrite (qeqT_imp_qeq _ _ (real_mult_proj _ _ _)), (qeqT_imp_qeq _ _ (real_const_proj _ _)).
  apply (ri_eps_core (ri_qnorm n) (Qabs ((ln2i_x k - ri_x n)%Q))
                     (projT1 (Ireal n) k) (projT1 (ri_lineabs n) k) eps).
  - transitivity (Qabs ((ri_qnorm n * ln2i_x k - tn_r n)%Q)).
    + apply ri_core_pt.
    + symmetry. apply ri_lineabs_proj.
  - apply ri_qnorm_pos.
  - exact HNk.
Qed.

(* ============================================================ *)
(* §E alignment with the supply interface (interface registration)                                         *)
(* ============================================================ *)
(* interface fact: the real_metric face of ln2b_delta_of_supply consumes the form *)
(*   |A_n * X - B_n| (ln2b_line with A B : nat -> Z integer coefficients).  the output *)
(*   of the assembly (the metric face ri_metric + the normalization factor ri_qnorm + *)
(*   the rational-constant line face ri_lineabs) is, via ri_metric_line_scale, exactly *)
(*   its pointwise scaled image: *)
(*     lineabs_n == c_n * metric_n (pointwise exact), *)
(* so the input form of the supply-side clo/theta criteria (clo_n <= |A_n X - B_n| <= theta^n) *)
(* reads off pointwise directly from the assembly output.  future work: for the x' family *)
(*   the B_n := p_n cease to be integral from n = 3 on (the integrality fact is recorded in *)
(*   the TrueNumerator file header); integer-coefficient renormalization is the prerequisite *)
(* of the supply instantiation; the A/B integrality and the supply assembly are separate work. *)

(* ri_upper_transfer (upper-bound face transfer): Ireal_n/c_n <= theta^n implies |X - x'_n| <= theta^n
   (real_eq enters real_le through the right branch, then real_le transitivity -- the input form of
   the supply-side upper-bound criteria) *)
Theorem ri_upper_transfer : forall (Ireal : ri_Iface) (th : Q),
  ri_identity_spec Ireal ->
  (forall n : nat, real_le (real_mult (Ireal n) (real_const (Qinv (ri_qnorm n))))
                           (real_const (q_pow th n))) ->
  forall n : nat, real_le (ri_metric n) (real_const (q_pow th n)).
Proof.
  intros Ireal th Hspec Hup n.
  apply (real_le_trans (ri_metric n)
          (real_mult (Ireal n) (real_const (Qinv (ri_qnorm n))))
          (real_const (q_pow th n))).
  - right. exact (Hspec n).
  - exact (Hup n).
Qed.

(* ============================================================ *)
(* §F the numerical anchor group (each anchor decided exactly by vm_compute through the projection lemmas)                       *)
(* ============================================================ *)

(* normalization-factor anchor: c_1 = 2^2 * q~_1 = 4 * 3 = 12 *)
Theorem ri_qnorm1_anchor : QeqT (ri_qnorm 1) (12 # 1)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

(* r-family anchor: c_2 * x'_2 == r_2 = 72 *)
Theorem ri_cx2_anchor : QeqT ((ri_qnorm 2 * ri_x 2)%Q) (72 # 1)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

(* metric-face anchor: |X_5 - x'_1| == |661/960 - 2/3| == 7/320 (X_k := ln2i_x k) *)
Theorem ri_metric15_anchor : QeqT (projT1 (ri_metric 1) 5) (7 # 320)%Q.
Proof.
  apply qeq_imp_qeqT. rewrite ri_metric_proj. vm_compute. reflexivity.
Qed.

(* line-face anchor: |c_1 * X_5 - r_1| == |12 * (661/960) - 8| == 21/80 = 12 * (7/320)
   -- together with the metric-face anchor this forms the proportional pair of anchors for
   ri_core_pt (c_1 = 12) *)
Theorem ri_lineabs15_anchor : QeqT (projT1 (ri_lineabs 1) 5) (21 # 80)%Q.
Proof.
  apply qeq_imp_qeqT. rewrite ri_lineabs_proj. vm_compute. reflexivity.
Qed.

(* ============================================================ *)
(* assumption audit: the Print Assumptions output below should report zero dependencies (the zero-admission re-check).          *)
(* ============================================================ *)

Print Assumptions ri_x_eq_tn.
Print Assumptions ri_core_pt.
Print Assumptions ri_identity_assembly.
Print Assumptions ri_upper_transfer.
Print Assumptions ri_metric15_anchor.
