(* ConstructiveWorld-Set — Q-layer Archimedean stepping-stone modules. *)

(** * abl_Hqarch_bridge_06: the Hqarch site closed from the Bernoulli
    lower bound.

    Mission.  The constructive closure of the Hqarch contraction-power
      premise: the Archimedean nat witness core ([abl_q_arch_sig],
      [abl_arch_nat]), the final-premise witness production
      ([abl_bridge_ratio], [abl_bridge_step], [abl_hqarch_witness_site],
      with the closed term [abl_hqarch_nat]), and the closure theorem
      [abl_hqarch_site_closed] in the site shape.

    Dependencies.  Stdlib [QArith.QArith], [ZArith],
      [ZArith.ZArith_dec], [Lia], [Extraction]; requires
      [S02_CauchyComplete] (order carriers, bridges) and
      [abl_Hqarch_bernoulli_04].

    References.  The baseline module abl_Hqarch_bridge_06.v in
      ConstructiveWorld-Main, whose statement names are carried over
      here verbatim; the closed site is the premise shape of the
      baseline source module R2BishopLogSel.v.

    Constructivity.  All statements close by [Qed]; the witness is a
      closed computational term over [sigT]; statement faces use
      [QleT']/[QltT]; extraction has [Obj.magic] = 0; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . ""
      abl_Hqarch_bridge_06.v] compiles cleanly (exit 0); the artifact
      begins [436f7121 00015ff4]. *)


From Stdlib Require Import QArith.QArith.
From Stdlib Require Import ZArith.
From Stdlib Require Import ZArith.ZArith_dec.
From Stdlib Require Import Lia.
From Stdlib Require Import Extraction.
Require Import S02_CauchyComplete (QleT', Qle_to_QleT', QleT'_to_Qle).

Require Import abl_Hqarch_bernoulli_04.

Open Scope Q_scope.

(* ================= Part A. The Archimedean nat witness core ================= *)
(*   n := Z.to_nat (Qnum q) satisfies q <= n (nat scale).  Proof: expand the
     order to a Z inequality and split on the sign of Qnum q; the
     nonnegative branch normalizes the witness to the numerator with the
     denominator at least one preserving the order, the negative branch
     caps the witness at zero by nonnegativity of the coercion. *)
(* ============================================================ *)

Definition abl_arch_nat (q : Q) : nat := Z.to_nat (Qnum q).

Lemma abl_arch : forall q : Q, QleT' q (abl_qofnat (abl_arch_nat q)).
Proof.
  intro q.
  apply Qle_to_QleT'.
  destruct q as [m e].
  assert (He : (0 < Z.pos e)%Z) by exact (Pos2Z.is_pos e).
  assert (H1e : (1 <= Z.pos e)%Z) by lia.
  unfold Qle, abl_qofnat, abl_arch_nat. cbn [Qnum Qden].
  destruct (Z_lt_le_dec m 0) as [Hm | Hm].
  - (* Negative numerator: the witness is capped at zero. *)
    assert (H0 : (0 <= Z.of_nat (Z.to_nat m))%Z)
      by exact (Nat2Z.is_nonneg (Z.to_nat m)).
    assert (Hx : (1 * Z.of_nat (Z.to_nat m) <= Z.pos e * Z.of_nat (Z.to_nat m))%Z)
      by (apply Zmult_le_compat_r; assumption).
    rewrite Zmult_1_l in Hx.
    rewrite (Zmult_comm (Z.pos e) (Z.of_nat (Z.to_nat m))) in Hx.
    rewrite Zmult_1_r. lia.
  - (* Nonnegative numerator: witness normalizes to the numerator,
       denominator at least one preserves the order. *)
    rewrite (Z2Nat.id m Hm). rewrite Zmult_1_r.
    assert (Hx : (1 * m <= Z.pos e * m)%Z)
      by (apply Zmult_le_compat_r; assumption).
    rewrite Zmult_1_l in Hx.
    rewrite (Zmult_comm (Z.pos e) m) in Hx.
    exact Hx.
Qed.

(* The sigT form of the Archimedean witness (informative carrier). *)
Lemma abl_q_arch_sig : forall q : Q, sigT (fun n : nat => QleT' q (abl_qofnat n)).
Proof.
  intro q. exists (abl_arch_nat q). exact (abl_arch q).
Qed.

(* ================= Part B. Final-premise witness production ================= *)
(*   t := (v-b) * /(b*w): t <= n (Arch), right-multiply by b*w > 0 to get
     v - b <= n*(b*w), add b and normalize to v <= b*(1+n*w); the case
     v <= b is covered by n = 0. *)
(* ============================================================ *)

Definition abl_bridge_ratio (v b w : Q) : Q := (v - b) * / (b * w).

Definition abl_hqarch_nat (p v b : Q) : nat :=
  abl_arch_nat (abl_bridge_ratio v b (/ p - 1)).

Lemma abl_bridge_step : forall (v b w : Q) (n : nat),
  Qlt 0 b -> Qlt 0 w ->
  Qle (abl_bridge_ratio v b w) (abl_qofnat n) ->
  QleT' v (b * (1 + abl_qofnat n * w)).
Proof.
  intros v b w n Hb0 Hw0 Hratio.
  apply Qle_to_QleT'.
  assert (Hr0 : Qlt 0 (b * w)) by exact (Qmult_lt_0_compat b w Hb0 Hw0).
  assert (Hrle : Qle 0 (b * w)) by exact (Qlt_le_weak 0 (b * w) Hr0).
  assert (Hrne : ~ ((b * w) == 0))
    by exact (fun Hne : b * w == 0 =>
              (fun e : Empty_set => match e with end)
                (abl_qlt_neq0 (b * w) Hr0
                  (S02_CauchyComplete.qeq_imp_qeqT _ _ Hne))).
(* Right-multiplying the ratio into shape: t*(b*w) == v - b. *)
  assert (Htr : Qeq ((abl_bridge_ratio v b w) * (b * w)) (v - b)).
  { unfold abl_bridge_ratio.
    rewrite <- Qmult_assoc.
    rewrite (Qmult_comm (/ (b * w)) (b * w)).
    rewrite (Qmult_inv_r (b * w) Hrne).
    apply Qmult_1_r. }
  assert (Hsc : Qle ((abl_bridge_ratio v b w) * (b * w))
                    (abl_qofnat n * (b * w))).
  { exact (Qmult_le_compat_r (abl_bridge_ratio v b w) (abl_qofnat n) (b * w)
             Hratio Hrle). }
  assert (H1 : Qle (v - b) (abl_qofnat n * (b * w))).
    { exact (QleT'_to_Qle _ _
             (abl_qle_eq_l (v - b) ((abl_bridge_ratio v b w) * (b * w))
             (abl_qofnat n * (b * w)) (Qeq_sym _ _ Htr) Hsc)). }
  assert (H2 : Qle v (abl_qofnat n * (b * w) + b)).
  { apply QleT'_to_Qle.
    apply (abl_qle_eq_l v (v - b + b) (abl_qofnat n * (b * w) + b)).
    - ring.
    - exact (Qplus_le_compat (v - b) (abl_qofnat n * (b * w)) b b H1
               (Qle_refl b)). }
  apply QleT'_to_Qle.
  apply (abl_qle_eq_r v (abl_qofnat n * (b * w) + b)
           (b * (1 + abl_qofnat n * w))).
  - exact H2.
  - ring.
Qed.

(* The final-premise witness lemma: the four premises give the sigT witness
   over n with v <= b*(1+n*w), n produced by the closed term. *)
Lemma abl_hqarch_witness_site : forall (p v b : Q),
  Qlt 0 p -> Qlt p 1 -> Qlt 0 v -> Qlt 0 b ->
  sigT (fun n : nat => QleT' v (b * (1 + abl_qofnat n * (/ p - 1)))).
Proof.
  intros p v b Hp0 Hp1 Hvt0 Hb0.
  exists (abl_hqarch_nat p v b).
  exact (abl_bridge_step v b (/ p - 1) (abl_hqarch_nat p v b) Hb0
             (S02_CauchyComplete.QltT_to_Qlt _ _ (abl_canon_w_pos p Hp0 Hp1))
             (QleT'_to_Qle _ _ (abl_arch (abl_bridge_ratio v b (/ p - 1))))).
Qed.

(* ================= Part C. The full-site closure theorem ================= *)
(*   The premise shape (four positivity premises plus the sigT body, the
     power body renamed as in the header) closes in one step from the
     Bernoulli-based interface lemma. *)
(* ============================================================ *)

Theorem abl_hqarch_site_closed : forall (p v b : Q),
  Qlt 0 p -> Qlt p 1 -> Qlt 0 v -> Qlt 0 b ->
  sigT (fun j : nat => QleT' (abl_qpow p j * v) b).
Proof.
  intros p v b Hp0 Hp1 Hvt0 Hb0.
  destruct (abl_hqarch_witness_site p v b Hp0 Hp1 Hvt0 Hb0) as [n Hn].
  destruct (abl_hqarch_via_bern p v b n Hp0 Hp1 Hvt0 Hb0
             (QleT'_to_Qle _ _ Hn)) as [j Hj].
  exists j. exact Hj.
Qed.

(* ================= Verification: extraction and assumption closure ================= *)

Extraction "abl_hqarch_bridge_06_G3.ml" abl_q_arch_sig abl_hqarch_witness_site
  abl_hqarch_site_closed.

Print Assumptions abl_arch.
Print Assumptions abl_q_arch_sig.
Print Assumptions abl_bridge_step.
Print Assumptions abl_hqarch_witness_site.
Print Assumptions abl_hqarch_site_closed.
Print Assumptions abl_hqarch_via_bern.
Print Assumptions abl_canon_w_pos.
