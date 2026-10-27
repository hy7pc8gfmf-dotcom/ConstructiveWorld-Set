(* ConstructiveWorld-Set — Q-layer Archimedean stepping-stone modules. *)

(** * abl_Hqarch_bernoulli_04: the Q-layer Bernoulli lower bound and the
    Hqarch site-shape interface.

    Mission.  Two deliveries toward the constructive closure of the
      [Hqarch] contraction-power premise: the Bernoulli inequality in Q
      ([abl_bern_lower], 1 + n*q <= (1+q)^n for q >= 0, with the
      companion [abl_qpow_ge1]) over the locally defined power
      [abl_qpow]; and the site-shape interface ([abl_hqarch_bern_step],
      [abl_hqarch_via_bern]) closing in the premise's [sigT] shape.

    Dependencies.  Stdlib [QArith.QArith], [ZArith], [Lia],
      [Extraction]; requires [S01_BaseRing] ([Not]) and a selective
      import of [S02_CauchyComplete] (carriers and two-way bridges).

    References.  The baseline module abl_Hqarch_bernoulli_04.v in
      ConstructiveWorld-Main, whose statement names are carried over
      here verbatim; the power [abl_qpow] is the baseline's [mixe_qpow]
      Fixpoint body under a different name, so this file carries its
      own copy instead of requiring the unwashed source.

    Constructivity.  All statements close by [Qed] with no admissions
      and no classical logic; witnesses are carried by [sigT]; statement
      faces use [QleT']/[QltT]; [coqchk] reports [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . ""
      abl_Hqarch_bernoulli_04.v] compiles cleanly (exit 0); its artifact
      begins [436f7121 00015ff4]. *)


From Stdlib Require Import QArith.QArith.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Extraction.
Require Import S01_BaseRing (Not).
Require Import S02_CauchyComplete
  (QeqT, QleT', QltT, Qle_to_QleT', QleT'_to_Qle, Qlt_to_QltT, QltT_to_Qlt,
   qeq_imp_qeqT, qeqT_imp_qeq).

Open Scope Q_scope.

(* ================= Part A. Q-layer transport helpers ================= *)

Lemma abl_qlt_01 : QltT 0 1.
Proof. apply Qlt_to_QltT. unfold Qlt. cbn. lia. Qed.

Lemma abl_qeq_le : forall a b : Q, Qeq a b -> QleT' a b.
Proof.
  intros a b Hab. apply Qle_to_QleT'. unfold Qle, Qeq in *. rewrite Hab.
  apply Z.le_refl.
Qed.

Lemma abl_qle_eq_l : forall a b c : Q, Qeq a b -> Qle b c -> QleT' a c.
Proof.
  intros a b c Hab Hbc. apply Qle_to_QleT'.
  apply (Qle_trans a b c).
  - exact (QleT'_to_Qle _ _ (abl_qeq_le a b Hab)).
  - exact Hbc.
Qed.

Lemma abl_qle_eq_r : forall a b c : Q, Qle a b -> Qeq b c -> QleT' a c.
Proof.
  intros a b c Hab Hbc. apply Qle_to_QleT'.
  apply (Qle_trans a b c).
  - exact Hab.
  - exact (QleT'_to_Qle _ _ (abl_qeq_le b c Hbc)).
Qed.

Lemma abl_qlt_eq_l : forall a b c : Q, Qeq a b -> Qlt b c -> QltT a c.
Proof.
  intros a b c Hab Hbc. apply Qlt_to_QltT.
  apply (Qle_lt_trans a b c).
  - exact (QleT'_to_Qle _ _ (abl_qeq_le a b Hab)).
  - exact Hbc.
Qed.

Lemma abl_qlt_eq_r : forall a b c : Q, Qlt a b -> Qeq b c -> QltT a c.
Proof.
  intros a b c Hab Hbc. apply Qlt_to_QltT.
  apply (Qlt_le_trans a b c).
  - exact Hab.
  - exact (QleT'_to_Qle _ _ (abl_qeq_le b c Hbc)).
Qed.

Lemma abl_qmult_eq_l : forall a b c : Q, Qeq a b -> QeqT (a * c) (b * c).
Proof.
  intros a b c Hab. apply qeq_imp_qeqT. rewrite Hab. apply Qeq_refl.
Qed.

(* ================= Part B. nat-scaled rationalization and powers ================= *)

Definition abl_qofnat (k : nat) : Q := (Z.of_nat k # 1)%Q.

Lemma abl_qofnat_nonneg : forall n : nat, QleT' 0 (abl_qofnat n).
Proof.
  intro n. apply Qle_to_QleT'. unfold Qle, abl_qofnat. cbn [Qnum Qden]. lia.
Qed.

Lemma abl_qofnat_S : forall n : nat, QeqT (abl_qofnat (S n)) ((1 + abl_qofnat n)%Q).
Proof.
  intro n. apply qeq_imp_qeqT. unfold Qeq, Qplus, abl_qofnat. cbn [Qnum Qden]. lia.
Qed.

Fixpoint abl_qpow (x : Q) (n : nat) : Q :=
  match n with
  | Datatypes.O => 1%Q
  | Datatypes.S m => x * abl_qpow x m
  end.

Lemma abl_boost : forall (n : nat) (q : Q), Qle 0 q -> QleT' 1 (1 + abl_qofnat n * q).
Proof.
  intros n q Hq0. apply Qle_to_QleT'.
  assert (Hhq_qlt_01 : Qlt 0 1) by exact (QltT_to_Qlt _ _ abl_qlt_01).
  assert (Hhq_qeq_le : forall ka kb : Q, Qeq ka kb -> Qle ka kb)
    by (intros ka kb kHab; exact (QleT'_to_Qle _ _ (abl_qeq_le ka kb kHab))).
  assert (Hhq_qle_eq_l : forall ka kb kc : Q, Qeq ka kb -> Qle kb kc -> Qle ka kc)
    by (intros ka kb kc kHab kHbc; exact (QleT'_to_Qle _ _ (abl_qle_eq_l ka kb kc kHab kHbc))).
  assert (Hhq_qle_eq_r : forall ka kb kc : Q, Qle ka kb -> Qeq kb kc -> Qle ka kc)
    by (intros ka kb kc kHab kHbc; exact (QleT'_to_Qle _ _ (abl_qle_eq_r ka kb kc kHab kHbc))).
  assert (Hhq_qlt_eq_l : forall ka kb kc : Q, Qeq ka kb -> Qlt kb kc -> Qlt ka kc)
    by (intros ka kb kc kHab kHbc; exact (QltT_to_Qlt _ _ (abl_qlt_eq_l ka kb kc kHab kHbc))).
  assert (Hhq_qlt_eq_r : forall ka kb kc : Q, Qlt ka kb -> Qeq kb kc -> Qlt ka kc)
    by (intros ka kb kc kHab kHbc; exact (QltT_to_Qlt _ _ (abl_qlt_eq_r ka kb kc kHab kHbc))).
  assert (Hhq_qmult_eq_l : forall ka kb kc : Q, Qeq ka kb -> Qeq (ka * kc) (kb * kc))
    by (intros ka kb kc kHab; exact (qeqT_imp_qeq _ _ (abl_qmult_eq_l ka kb kc kHab))).
  assert (Hhq_qofnat_nonneg : forall kn : nat, Qle 0 (abl_qofnat kn))
    by (intro kn; exact (QleT'_to_Qle _ _ (abl_qofnat_nonneg kn))).
  assert (Hhq_qofnat_S : forall kn : nat, abl_qofnat (S kn) == (1 + abl_qofnat kn)%Q)
    by (intro kn; exact (qeqT_imp_qeq _ _ (abl_qofnat_S kn))).
  assert (Hnq0 : Qle (0 * q) (abl_qofnat n * q)).
  { exact (Qmult_le_compat_r 0 (abl_qofnat n) q (Hhq_qofnat_nonneg n) Hq0). }
  assert (Hnq0' : Qle 0 (abl_qofnat n * q)).
  { apply (Hhq_qle_eq_l 0 (0 * q) (abl_qofnat n * q)).
    - ring.
    - exact Hnq0. }
  apply (Hhq_qle_eq_l 1 (1 + 0) (1 + abl_qofnat n * q)).
  - ring.
  - exact (Qplus_le_compat 1 1 0 (abl_qofnat n * q) (Qle_refl 1) Hnq0').
Qed.

Lemma abl_qpow_pos : forall (u : Q) (n : nat), Qlt 0 u -> QltT 0 (abl_qpow u n).
Proof.
  intros u n Hu. apply Qlt_to_QltT.
  induction n as [| n IH].
  - cbn [abl_qpow]. exact (QltT_to_Qlt _ _ abl_qlt_01).
  - cbn [abl_qpow]. exact (Qmult_lt_0_compat u (abl_qpow u n) Hu IH).
Qed.

Lemma abl_qlt_neq0 : forall x : Q, Qlt 0 x -> Not (QeqT x 0).
Proof.
  intros x Hx Hc. apply qeqT_imp_qeq in Hc.
  exact (False_rect Empty_set (Qlt_irrefl 0
    (QltT_to_Qlt _ _ (abl_qlt_eq_r 0 x 0 Hx Hc)))).
Qed.

(* ============================================================ *)
(* ================= Part C. The Bernoulli lower bound ================= *)
(*   (1+q)^n >= 1 + n*q for q >= 0, by induction over the iterated power:
     the step chains 1+nq+q <= (1+q)^n+q (shifting the induction
     claim) and (1+q)^n+q <= (1+q)^n+q*(1+q)^n (right-multiplying
     q <= q*(1+q)^n by the at-least-one face), reassembling to
     (1+q)*(1+q)^n with the n*q^2 term absorbed by rewriting. *)
(* ============================================================ *)

Lemma abl_bern_lower : forall (q : Q) (n : nat),
  Qle 0 q -> QleT' (1 + abl_qofnat n * q) (abl_qpow (1 + q) n).
Proof.
  intros q n Hq0. apply Qle_to_QleT'.
  assert (Hhq_qlt_01 : Qlt 0 1) by exact (QltT_to_Qlt _ _ abl_qlt_01).
  assert (Hhq_qeq_le : forall ka kb : Q, Qeq ka kb -> Qle ka kb)
    by (intros ka kb kHab; exact (QleT'_to_Qle _ _ (abl_qeq_le ka kb kHab))).
  assert (Hhq_qle_eq_l : forall ka kb kc : Q, Qeq ka kb -> Qle kb kc -> Qle ka kc)
    by (intros ka kb kc kHab kHbc; exact (QleT'_to_Qle _ _ (abl_qle_eq_l ka kb kc kHab kHbc))).
  assert (Hhq_qle_eq_r : forall ka kb kc : Q, Qle ka kb -> Qeq kb kc -> Qle ka kc)
    by (intros ka kb kc kHab kHbc; exact (QleT'_to_Qle _ _ (abl_qle_eq_r ka kb kc kHab kHbc))).
  assert (Hhq_qlt_eq_l : forall ka kb kc : Q, Qeq ka kb -> Qlt kb kc -> Qlt ka kc)
    by (intros ka kb kc kHab kHbc; exact (QltT_to_Qlt _ _ (abl_qlt_eq_l ka kb kc kHab kHbc))).
  assert (Hhq_qlt_eq_r : forall ka kb kc : Q, Qlt ka kb -> Qeq kb kc -> Qlt ka kc)
    by (intros ka kb kc kHab kHbc; exact (QltT_to_Qlt _ _ (abl_qlt_eq_r ka kb kc kHab kHbc))).
  assert (Hhq_qmult_eq_l : forall ka kb kc : Q, Qeq ka kb -> Qeq (ka * kc) (kb * kc))
    by (intros ka kb kc kHab; exact (qeqT_imp_qeq _ _ (abl_qmult_eq_l ka kb kc kHab))).
  assert (Hhq_qofnat_nonneg : forall kn : nat, Qle 0 (abl_qofnat kn))
    by (intro kn; exact (QleT'_to_Qle _ _ (abl_qofnat_nonneg kn))).
  assert (Hhq_qofnat_S : forall kn : nat, abl_qofnat (S kn) == (1 + abl_qofnat kn)%Q)
    by (intro kn; exact (qeqT_imp_qeq _ _ (abl_qofnat_S kn))).
  assert (Hhq_boost : forall (kn : nat) (kq : Q), Qle 0 kq -> Qle 1 (1 + abl_qofnat kn * kq))
    by (intros kn kq kHq0; exact (QleT'_to_Qle _ _ (abl_boost kn kq kHq0))).
  assert (Hhq_qpow_pos : forall (ku : Q) (kn : nat), Qlt 0 ku -> Qlt 0 (abl_qpow ku kn))
    by (intros ku kn kHu; exact (QltT_to_Qlt _ _ (abl_qpow_pos ku kn kHu))).
  assert (Hhq_qlt_neq0 : forall kx : Q, Qlt 0 kx -> ~ (kx == 0))
    by (intros kx kHx kHc;
        exact (Qlt_irrefl 0 (QltT_to_Qlt _ _ (abl_qlt_eq_r 0 kx 0 kHx kHc)))).
  induction n as [| n IH].
  - cbn [abl_qpow].
    apply (Hhq_qle_eq_l (1 + abl_qofnat 0 * q) 1 1).
    + change (abl_qofnat 0) with 0%Q. ring.
    + apply Qle_refl.
  - cbn [abl_qpow].
    assert (Hge1 : Qle 1 (1 + abl_qofnat n * q)) by (apply (Hhq_boost n q Hq0)).
    assert (Hge1' : Qle 1 (abl_qpow (1 + q) n))
      by (apply (Qle_trans 1 (1 + abl_qofnat n * q) (abl_qpow (1 + q) n) Hge1 IH)).
    assert (Hqle : Qle q (q * abl_qpow (1 + q) n)).
    { apply (Hhq_qle_eq_l q (1 * q) (q * abl_qpow (1 + q) n)).
      - ring.
      - apply (Hhq_qle_eq_r (1 * q) (abl_qpow (1 + q) n * q)
                 (q * abl_qpow (1 + q) n)).
        + exact (Qmult_le_compat_r 1 (abl_qpow (1 + q) n) q Hge1' Hq0).
        + ring. }
    apply (Hhq_qle_eq_l (1 + abl_qofnat (S n) * q)
                        (1 + abl_qofnat n * q + q)
                        ((1 + q) * abl_qpow (1 + q) n)).
    + rewrite (Hhq_qofnat_S n). ring.
    + apply (Hhq_qle_eq_r (1 + abl_qofnat n * q + q)
               (abl_qpow (1 + q) n + q * abl_qpow (1 + q) n)
               ((1 + q) * abl_qpow (1 + q) n)).
      * apply (Qle_trans (1 + abl_qofnat n * q + q)
                 (abl_qpow (1 + q) n + q)
                 (abl_qpow (1 + q) n + q * abl_qpow (1 + q) n)).
        -- apply (Qplus_le_compat (1 + abl_qofnat n * q) (abl_qpow (1 + q) n)
                    q q IH (Qle_refl q)).
        -- apply (Qplus_le_compat (abl_qpow (1 + q) n) (abl_qpow (1 + q) n)
                    q (q * abl_qpow (1 + q) n)
                    (Qle_refl (abl_qpow (1 + q) n)) Hqle).
      * ring.
Qed.

(* The at-least-one face of Bernoulli: (1+q)^n >= 1. *)
Lemma abl_qpow_ge1 : forall (q : Q) (n : nat), Qle 0 q -> QleT' 1 (abl_qpow (1 + q) n).
Proof.
  intros q n Hq0. apply Qle_to_QleT'.
  apply (Qle_trans 1 (1 + abl_qofnat n * q) (abl_qpow (1 + q) n)).
  - exact (QleT'_to_Qle _ _ (abl_boost n q Hq0)).
  - exact (QleT'_to_Qle _ _ (abl_bern_lower q n Hq0)).
Qed.

(* ============================================================ *)
(* ================= Part D. The Hqarch site-shape interface ================= *)
(*   Reciprocal monotonicity (on positives, <= reverses under the
     reciprocal); reciprocal rewriting of powers; the Bernoulli lower
     bound turned into the contraction-power upper bound; closed in the
     [sigT] shape of the premise (power body renamed as in the header). *)

Lemma abl_qmult_cancel_r : forall (a x y : Q),
  ~ (a == 0) -> Qeq (x * a) (y * a) -> QeqT x y.
Proof.
  intros a x y Ha Hc. apply qeq_imp_qeqT.
  assert (Hs1 : Qeq x (x * (a * / a))).
  { rewrite (Qmult_inv_r a Ha). symmetry. apply Qmult_1_r. }
  assert (Hs2 : Qeq (x * (a * / a)) (x * a * / a)) by (apply Qmult_assoc).
  assert (Hs3 : Qeq (x * a * / a) (y * a * / a)) by (rewrite Hc; apply Qeq_refl).
  assert (Hs4 : Qeq (y * a * / a) (y * (a * / a))).
  { exact (Qeq_sym _ _ (Qmult_assoc y a (/ a))). }
  assert (Hs5 : Qeq (y * (a * / a)) y).
  { rewrite (Qmult_inv_r a Ha). apply Qmult_1_r. }
  exact (Qeq_trans _ _ _ Hs1 (Qeq_trans _ _ _ Hs2 (Qeq_trans _ _ _ Hs3 (Qeq_trans _ _ _ Hs4 Hs5)))).
Qed.

Lemma abl_qinv_eq_compat_nz : forall a b : Q,
  ~ (a == 0) -> Qeq a b -> QeqT (/ a) (/ b).
Proof.
  intros a b Ha Hab.
  assert (Hb0 : ~ (b == 0)).
  { intro Hc. apply Ha. rewrite <- Hc. exact Hab. }
  apply qeq_imp_qeqT.
  apply (qeqT_imp_qeq _ _).
  apply (abl_qmult_cancel_r a (/ a) (/ b) Ha).
  apply (Qeq_trans (/ a * a) 1 ((/ b) * a)).
  - rewrite (Qmult_comm (/ a) a). apply (Qmult_inv_r a Ha).
  - rewrite Hab. rewrite (Qmult_comm (/ b) b).
    symmetry. apply (Qmult_inv_r b Hb0).
Qed.

Lemma abl_qinv_le_contravar : forall a b : Q,
  Qlt 0 a -> Qlt 0 b -> Qle a b -> QleT' (/ b) (/ a).
Proof.
  intros a b Ha Hb Hab. apply Qle_to_QleT'.
  assert (Hhq_qlt_01 : Qlt 0 1) by exact (QltT_to_Qlt _ _ abl_qlt_01).
  assert (Hhq_qeq_le : forall ka kb : Q, Qeq ka kb -> Qle ka kb)
    by (intros ka kb kHab; exact (QleT'_to_Qle _ _ (abl_qeq_le ka kb kHab))).
  assert (Hhq_qle_eq_l : forall ka kb kc : Q, Qeq ka kb -> Qle kb kc -> Qle ka kc)
    by (intros ka kb kc kHab kHbc; exact (QleT'_to_Qle _ _ (abl_qle_eq_l ka kb kc kHab kHbc))).
  assert (Hhq_qle_eq_r : forall ka kb kc : Q, Qle ka kb -> Qeq kb kc -> Qle ka kc)
    by (intros ka kb kc kHab kHbc; exact (QleT'_to_Qle _ _ (abl_qle_eq_r ka kb kc kHab kHbc))).
  assert (Hhq_qlt_eq_l : forall ka kb kc : Q, Qeq ka kb -> Qlt kb kc -> Qlt ka kc)
    by (intros ka kb kc kHab kHbc; exact (QltT_to_Qlt _ _ (abl_qlt_eq_l ka kb kc kHab kHbc))).
  assert (Hhq_qlt_eq_r : forall ka kb kc : Q, Qlt ka kb -> Qeq kb kc -> Qlt ka kc)
    by (intros ka kb kc kHab kHbc; exact (QltT_to_Qlt _ _ (abl_qlt_eq_r ka kb kc kHab kHbc))).
  assert (Hhq_qmult_eq_l : forall ka kb kc : Q, Qeq ka kb -> Qeq (ka * kc) (kb * kc))
    by (intros ka kb kc kHab; exact (qeqT_imp_qeq _ _ (abl_qmult_eq_l ka kb kc kHab))).
  assert (Hhq_qofnat_nonneg : forall kn : nat, Qle 0 (abl_qofnat kn))
    by (intro kn; exact (QleT'_to_Qle _ _ (abl_qofnat_nonneg kn))).
  assert (Hhq_qofnat_S : forall kn : nat, abl_qofnat (S kn) == (1 + abl_qofnat kn)%Q)
    by (intro kn; exact (qeqT_imp_qeq _ _ (abl_qofnat_S kn))).
  assert (Hhq_boost : forall (kn : nat) (kq : Q), Qle 0 kq -> Qle 1 (1 + abl_qofnat kn * kq))
    by (intros kn kq kHq0; exact (QleT'_to_Qle _ _ (abl_boost kn kq kHq0))).
  assert (Hhq_qpow_pos : forall (ku : Q) (kn : nat), Qlt 0 ku -> Qlt 0 (abl_qpow ku kn))
    by (intros ku kn kHu; exact (QltT_to_Qlt _ _ (abl_qpow_pos ku kn kHu))).
  assert (Hhq_qlt_neq0 : forall kx : Q, Qlt 0 kx -> ~ (kx == 0))
    by (intros kx kHx kHc;
        exact (Qlt_irrefl 0 (QltT_to_Qlt _ _ (abl_qlt_eq_r 0 kx 0 kHx kHc)))).
  assert (Hhq_bern_lower : forall (kq : Q) (kn : nat),
      Qle 0 kq -> Qle (1 + abl_qofnat kn * kq) (abl_qpow (1 + kq) kn))
    by (intros kq kn kHq0; exact (QleT'_to_Qle _ _ (abl_bern_lower kq kn kHq0))).
  assert (Hhq_qpow_ge1 : forall (kq : Q) (kn : nat), Qle 0 kq -> Qle 1 (abl_qpow (1 + kq) kn))
    by (intros kq kn kHq0; exact (QleT'_to_Qle _ _ (abl_qpow_ge1 kq kn kHq0))).
  assert (Hhq_qmult_cancel_r : forall (ka kx ky : Q),
      ~ (ka == 0) -> Qeq (kx * ka) (ky * ka) -> Qeq kx ky)
    by (intros ka kx ky kHa kHc; exact (qeqT_imp_qeq _ _ (abl_qmult_cancel_r ka kx ky kHa kHc))).
  assert (Hhq_qinv_eq_compat_nz : forall ka kb : Q, ~ (ka == 0) -> Qeq ka kb -> Qeq (/ ka) (/ kb))
    by (intros ka kb kHa kHab; exact (qeqT_imp_qeq _ _ (abl_qinv_eq_compat_nz ka kb kHa kHab))).
  destruct (Qlt_le_dec a b) as [Hlt | Hge].
  - apply (Qlt_le_weak (/ b) (/ a)).
    exact (proj1 (Qinv_lt_contravar a b Ha Hb) Hlt).
  - apply Hhq_qeq_le.
    exact (Hhq_qinv_eq_compat_nz b a (Hhq_qlt_neq0 b Hb)
             (Qeq_sym _ _ (Qle_antisym a b Hab Hge))).
Qed.

Lemma abl_qpow_ext : forall (u v : Q) (n : nat),
  Qeq u v -> QeqT (abl_qpow u n) (abl_qpow v n).
Proof.
  intros u v n H. apply qeq_imp_qeqT.
  induction n as [| n IH].
  - apply Qeq_refl.
  - cbn [abl_qpow].
    apply (Qeq_trans _ (v * abl_qpow u n) _).
    + exact (qeqT_imp_qeq _ _ (abl_qmult_eq_l u v (abl_qpow u n) H)).
    + rewrite IH. apply Qeq_refl.
Qed.

Lemma abl_qpow_inv : forall (u : Q) (n : nat),
  QeqT (abl_qpow (/ u) n) (/ (abl_qpow u n)).
Proof.
  intros u n. apply qeq_imp_qeqT.
  induction n as [| n IH].
  - cbn [abl_qpow]. apply Qeq_refl.
  - cbn [abl_qpow]. rewrite IH.
    exact (Qeq_sym _ _ (Qinv_mult_distr u (abl_qpow u n))).
Qed.

(* Bernoulli to the contraction step: p == 1/(1+w), 0 < v, and
   v <= b*(1+n*w) give p^n*v <= b.
   Chain: p^n == 1/(1+w)^n (reciprocal rewriting of powers) at most
   1/(1+n*w) (the Bernoulli lower bound recast on reciprocals, which
   reverse order on positives); multiply by v and normalize by the
   reciprocal of (1+n*w).  The four positivity premises align with the
   Hqarch site convention. *)
Lemma abl_hqarch_bern_step : forall (p w v b : Q) (n : nat),
  Qeq p (/ (1 + w)) -> Qle 0 w -> Qlt 0 v -> Qlt 0 b ->
  Qle v (b * (1 + abl_qofnat n * w)) ->
  QleT' (abl_qpow p n * v) b.
Proof.
  intros p w v b n Hp Hw0 Hvt0 Hb0 Hv. apply Qle_to_QleT'.
  assert (Hhq_qlt_01 : Qlt 0 1) by exact (QltT_to_Qlt _ _ abl_qlt_01).
  assert (Hhq_qeq_le : forall ka kb : Q, Qeq ka kb -> Qle ka kb)
    by (intros ka kb kHab; exact (QleT'_to_Qle _ _ (abl_qeq_le ka kb kHab))).
  assert (Hhq_qle_eq_l : forall ka kb kc : Q, Qeq ka kb -> Qle kb kc -> Qle ka kc)
    by (intros ka kb kc kHab kHbc; exact (QleT'_to_Qle _ _ (abl_qle_eq_l ka kb kc kHab kHbc))).
  assert (Hhq_qle_eq_r : forall ka kb kc : Q, Qle ka kb -> Qeq kb kc -> Qle ka kc)
    by (intros ka kb kc kHab kHbc; exact (QleT'_to_Qle _ _ (abl_qle_eq_r ka kb kc kHab kHbc))).
  assert (Hhq_qlt_eq_l : forall ka kb kc : Q, Qeq ka kb -> Qlt kb kc -> Qlt ka kc)
    by (intros ka kb kc kHab kHbc; exact (QltT_to_Qlt _ _ (abl_qlt_eq_l ka kb kc kHab kHbc))).
  assert (Hhq_qlt_eq_r : forall ka kb kc : Q, Qlt ka kb -> Qeq kb kc -> Qlt ka kc)
    by (intros ka kb kc kHab kHbc; exact (QltT_to_Qlt _ _ (abl_qlt_eq_r ka kb kc kHab kHbc))).
  assert (Hhq_qmult_eq_l : forall ka kb kc : Q, Qeq ka kb -> Qeq (ka * kc) (kb * kc))
    by (intros ka kb kc kHab; exact (qeqT_imp_qeq _ _ (abl_qmult_eq_l ka kb kc kHab))).
  assert (Hhq_qofnat_nonneg : forall kn : nat, Qle 0 (abl_qofnat kn))
    by (intro kn; exact (QleT'_to_Qle _ _ (abl_qofnat_nonneg kn))).
  assert (Hhq_qofnat_S : forall kn : nat, abl_qofnat (S kn) == (1 + abl_qofnat kn)%Q)
    by (intro kn; exact (qeqT_imp_qeq _ _ (abl_qofnat_S kn))).
  assert (Hhq_boost : forall (kn : nat) (kq : Q), Qle 0 kq -> Qle 1 (1 + abl_qofnat kn * kq))
    by (intros kn kq kHq0; exact (QleT'_to_Qle _ _ (abl_boost kn kq kHq0))).
  assert (Hhq_qpow_pos : forall (ku : Q) (kn : nat), Qlt 0 ku -> Qlt 0 (abl_qpow ku kn))
    by (intros ku kn kHu; exact (QltT_to_Qlt _ _ (abl_qpow_pos ku kn kHu))).
  assert (Hhq_qlt_neq0 : forall kx : Q, Qlt 0 kx -> ~ (kx == 0))
    by (intros kx kHx kHc;
        exact (Qlt_irrefl 0 (QltT_to_Qlt _ _ (abl_qlt_eq_r 0 kx 0 kHx kHc)))).
  assert (Hhq_bern_lower : forall (kq : Q) (kn : nat),
      Qle 0 kq -> Qle (1 + abl_qofnat kn * kq) (abl_qpow (1 + kq) kn))
    by (intros kq kn kHq0; exact (QleT'_to_Qle _ _ (abl_bern_lower kq kn kHq0))).
  assert (Hhq_qpow_ge1 : forall (kq : Q) (kn : nat), Qle 0 kq -> Qle 1 (abl_qpow (1 + kq) kn))
    by (intros kq kn kHq0; exact (QleT'_to_Qle _ _ (abl_qpow_ge1 kq kn kHq0))).
  assert (Hhq_qmult_cancel_r : forall (ka kx ky : Q),
      ~ (ka == 0) -> Qeq (kx * ka) (ky * ka) -> Qeq kx ky)
    by (intros ka kx ky kHa kHc; exact (qeqT_imp_qeq _ _ (abl_qmult_cancel_r ka kx ky kHa kHc))).
  assert (Hhq_qinv_eq_compat_nz : forall ka kb : Q, ~ (ka == 0) -> Qeq ka kb -> Qeq (/ ka) (/ kb))
    by (intros ka kb kHa kHab; exact (qeqT_imp_qeq _ _ (abl_qinv_eq_compat_nz ka kb kHa kHab))).
  assert (Hhq_qinv_le_contravar : forall ka kb : Q,
      Qlt 0 ka -> Qlt 0 kb -> Qle ka kb -> Qle (/ kb) (/ ka))
    by (intros ka kb kHa kHb kHab; exact (QleT'_to_Qle _ _ (abl_qinv_le_contravar ka kb kHa kHb kHab))).
  assert (Hhq_qpow_ext : forall (ku kv : Q) (kn : nat), Qeq ku kv -> Qeq (abl_qpow ku kn) (abl_qpow kv kn))
    by (intros ku kv kn kH; exact (qeqT_imp_qeq _ _ (abl_qpow_ext ku kv kn kH))).
  assert (Hhq_qpow_inv : forall (ku : Q) (kn : nat), Qeq (abl_qpow (/ ku) kn) (/ (abl_qpow ku kn)))
    by (intros ku kn; exact (qeqT_imp_qeq _ _ (abl_qpow_inv ku kn))).
  assert (Hv0 : Qle 0 v) by (apply (Qlt_le_weak 0 v); exact Hvt0).
  assert (Hge : Qle 1 (1 + w)).
  { apply (Hhq_qle_eq_l 1 (1 + 0) (1 + w)).
    - ring.
    - exact (Qplus_le_compat 1 1 0 w (Qle_refl 1) Hw0). }
  assert (Hp1 : Qlt 0 (1 + w)) by (apply (Qlt_le_trans 0 1 (1 + w) Hhq_qlt_01 Hge)).
  assert (Hpowpos : Qlt 0 (abl_qpow (1 + w) n)) by (apply (Hhq_qpow_pos (1 + w) n Hp1)).
  assert (Hpowne : ~ (abl_qpow (1 + w) n == 0)) by (apply (Hhq_qlt_neq0 _ Hpowpos)).
  assert (HYpos : Qlt 0 (1 + abl_qofnat n * w))
    by (apply (Qlt_le_trans 0 1 (1 + abl_qofnat n * w) Hhq_qlt_01 (Hhq_boost n w Hw0))).
  assert (HYne : ~ (1 + abl_qofnat n * w == 0)) by (apply (Hhq_qlt_neq0 _ HYpos)).
  assert (HYinvpos : Qlt 0 (/ (1 + abl_qofnat n * w))) by (apply (Qinv_lt_0_compat _ HYpos)).
  assert (Hmp : Qeq (abl_qpow p n) (/ (abl_qpow (1 + w) n))).
  { apply (Qeq_trans _ (abl_qpow (/ (1 + w)) n) _).
    - exact (Hhq_qpow_ext p (/ (1 + w)) n Hp).
    - exact (Hhq_qpow_inv (1 + w) n). }
  assert (Hmono : Qle (/ (abl_qpow (1 + w) n)) (/ (1 + abl_qofnat n * w))).
  { apply (Hhq_qinv_le_contravar (1 + abl_qofnat n * w) (abl_qpow (1 + w) n)
             HYpos Hpowpos).
    exact (Hhq_bern_lower w n Hw0). }
  assert (Hstep1 : Qle (abl_qpow p n * v) (v * / (1 + abl_qofnat n * w))).
  { apply (Hhq_qle_eq_r (abl_qpow p n * v) (/ (1 + abl_qofnat n * w) * v)
             (v * / (1 + abl_qofnat n * w))).
    - apply (Hhq_qle_eq_l (abl_qpow p n * v) (/ (abl_qpow (1 + w) n) * v)
               (/ (1 + abl_qofnat n * w) * v)).
      + exact (Hhq_qmult_eq_l _ _ v Hmp).
      + exact (Qmult_le_compat_r (/ (abl_qpow (1 + w) n))
                   (/ (1 + abl_qofnat n * w)) v Hmono Hv0).
    - ring. }
  assert (Hcancel : Qeq ((b * (1 + abl_qofnat n * w)) * / (1 + abl_qofnat n * w)) b).
  { rewrite <- Qmult_assoc.
    rewrite (Qmult_inv_r (1 + abl_qofnat n * w) HYne).
    apply Qmult_1_r. }
  assert (Hstep2 : Qle (v * / (1 + abl_qofnat n * w)) b).
  { apply (Hhq_qle_eq_r (v * / (1 + abl_qofnat n * w))
             ((b * (1 + abl_qofnat n * w)) * / (1 + abl_qofnat n * w)) b).
    - exact (Qmult_le_compat_r v (b * (1 + abl_qofnat n * w))
                 (/ (1 + abl_qofnat n * w)) Hv
                 (Qlt_le_weak 0 (/ (1 + abl_qofnat n * w)) HYinvpos)).
    - exact Hcancel. }
  exact (Qle_trans _ _ _ Hstep1 Hstep2).
Qed.

(* Canonical coupling: w := /p - 1 (= (1-p)/p) satisfies 1 + w == 1/p,
   i.e. p == 1/(1+w). *)
Lemma abl_canon_w_inv : forall p : Q, QeqT p (/ (1 + (/ p - 1))).
Proof.
  intros p. apply qeq_imp_qeqT.
  assert (Hs : (1 + (/ p - 1))%Q == (/ p)%Q) by ring.
  rewrite Hs. symmetry. apply Qinv_involutive.
Qed.

Lemma abl_canon_w_pos : forall p : Q, Qlt 0 p -> Qlt p 1 -> QltT 0 (/ p - 1).
Proof.
  intros p Hp0 Hp1. apply Qlt_to_QltT.
  assert (Hhq_qlt_01 : Qlt 0 1) by exact (QltT_to_Qlt _ _ abl_qlt_01).
  assert (Hhq_qeq_le : forall ka kb : Q, Qeq ka kb -> Qle ka kb)
    by (intros ka kb kHab; exact (QleT'_to_Qle _ _ (abl_qeq_le ka kb kHab))).
  assert (Hhq_qle_eq_l : forall ka kb kc : Q, Qeq ka kb -> Qle kb kc -> Qle ka kc)
    by (intros ka kb kc kHab kHbc; exact (QleT'_to_Qle _ _ (abl_qle_eq_l ka kb kc kHab kHbc))).
  assert (Hhq_qle_eq_r : forall ka kb kc : Q, Qle ka kb -> Qeq kb kc -> Qle ka kc)
    by (intros ka kb kc kHab kHbc; exact (QleT'_to_Qle _ _ (abl_qle_eq_r ka kb kc kHab kHbc))).
  assert (Hhq_qlt_eq_l : forall ka kb kc : Q, Qeq ka kb -> Qlt kb kc -> Qlt ka kc)
    by (intros ka kb kc kHab kHbc; exact (QltT_to_Qlt _ _ (abl_qlt_eq_l ka kb kc kHab kHbc))).
  assert (Hhq_qlt_eq_r : forall ka kb kc : Q, Qlt ka kb -> Qeq kb kc -> Qlt ka kc)
    by (intros ka kb kc kHab kHbc; exact (QltT_to_Qlt _ _ (abl_qlt_eq_r ka kb kc kHab kHbc))).
  assert (Hhq_qmult_eq_l : forall ka kb kc : Q, Qeq ka kb -> Qeq (ka * kc) (kb * kc))
    by (intros ka kb kc kHab; exact (qeqT_imp_qeq _ _ (abl_qmult_eq_l ka kb kc kHab))).
  assert (Hhq_qofnat_nonneg : forall kn : nat, Qle 0 (abl_qofnat kn))
    by (intro kn; exact (QleT'_to_Qle _ _ (abl_qofnat_nonneg kn))).
  assert (Hhq_qofnat_S : forall kn : nat, abl_qofnat (S kn) == (1 + abl_qofnat kn)%Q)
    by (intro kn; exact (qeqT_imp_qeq _ _ (abl_qofnat_S kn))).
  assert (Hhq_boost : forall (kn : nat) (kq : Q), Qle 0 kq -> Qle 1 (1 + abl_qofnat kn * kq))
    by (intros kn kq kHq0; exact (QleT'_to_Qle _ _ (abl_boost kn kq kHq0))).
  assert (Hhq_qpow_pos : forall (ku : Q) (kn : nat), Qlt 0 ku -> Qlt 0 (abl_qpow ku kn))
    by (intros ku kn kHu; exact (QltT_to_Qlt _ _ (abl_qpow_pos ku kn kHu))).
  assert (Hhq_qlt_neq0 : forall kx : Q, Qlt 0 kx -> ~ (kx == 0))
    by (intros kx kHx kHc;
        exact (Qlt_irrefl 0 (QltT_to_Qlt _ _ (abl_qlt_eq_r 0 kx 0 kHx kHc)))).
  assert (Hhq_bern_lower : forall (kq : Q) (kn : nat),
      Qle 0 kq -> Qle (1 + abl_qofnat kn * kq) (abl_qpow (1 + kq) kn))
    by (intros kq kn kHq0; exact (QleT'_to_Qle _ _ (abl_bern_lower kq kn kHq0))).
  assert (Hhq_qpow_ge1 : forall (kq : Q) (kn : nat), Qle 0 kq -> Qle 1 (abl_qpow (1 + kq) kn))
    by (intros kq kn kHq0; exact (QleT'_to_Qle _ _ (abl_qpow_ge1 kq kn kHq0))).
  assert (Hhq_qmult_cancel_r : forall (ka kx ky : Q),
      ~ (ka == 0) -> Qeq (kx * ka) (ky * ka) -> Qeq kx ky)
    by (intros ka kx ky kHa kHc; exact (qeqT_imp_qeq _ _ (abl_qmult_cancel_r ka kx ky kHa kHc))).
  assert (Hhq_qinv_eq_compat_nz : forall ka kb : Q, ~ (ka == 0) -> Qeq ka kb -> Qeq (/ ka) (/ kb))
    by (intros ka kb kHa kHab; exact (qeqT_imp_qeq _ _ (abl_qinv_eq_compat_nz ka kb kHa kHab))).
  assert (Hhq_qinv_le_contravar : forall ka kb : Q,
      Qlt 0 ka -> Qlt 0 kb -> Qle ka kb -> Qle (/ kb) (/ ka))
    by (intros ka kb kHa kHb kHab; exact (QleT'_to_Qle _ _ (abl_qinv_le_contravar ka kb kHa kHb kHab))).
  assert (Hhq_qpow_ext : forall (ku kv : Q) (kn : nat), Qeq ku kv -> Qeq (abl_qpow ku kn) (abl_qpow kv kn))
    by (intros ku kv kn kH; exact (qeqT_imp_qeq _ _ (abl_qpow_ext ku kv kn kH))).
  assert (Hhq_qpow_inv : forall (ku : Q) (kn : nat), Qeq (abl_qpow (/ ku) kn) (/ (abl_qpow ku kn)))
    by (intros ku kn; exact (qeqT_imp_qeq _ _ (abl_qpow_inv ku kn))).
  assert (Hhq_bern_step : forall (kp kw kv kb : Q) (kn : nat),
      Qeq kp (/ (1 + kw)) -> Qle 0 kw -> Qlt 0 kv -> Qlt 0 kb ->
      Qle kv (kb * (1 + abl_qofnat kn * kw)) -> Qle (abl_qpow kp kn * kv) kb)
    by (intros kp kw kv kb kn kHp kHw0 kHvt0 kHb0 kHv;
        exact (QleT'_to_Qle _ _ (abl_hqarch_bern_step kp kw kv kb kn kHp kHw0 kHvt0 kHb0 kHv))).
  assert (Hhq_canon_w_inv : forall kp : Q, Qeq kp (/ (1 + (/ kp - 1))))
    by (intro kp; exact (qeqT_imp_qeq _ _ (abl_canon_w_inv kp))).
  apply (proj1 (Qlt_minus_iff 1 (/ p))).
  apply (Hhq_qlt_eq_l 1 (/ 1) (/ p)).
  - apply Qeq_refl.
  - exact (proj1 (Qinv_lt_contravar p 1 Hp0 Hhq_qlt_01) Hp1).
Qed.

(* Closure in the Hqarch site shape: the four positivity premises in the
   premise's exact form (Qlt 0 p -> Qlt p 1 -> Qlt 0 v -> Qlt 0 b) plus
   the Bernoulli bridge step give the [sigT] witness.  The only textual
   difference from the site is the renamed power body; a companion piece
   can produce the final premise's nat witness by a Q-layer Archimedean
   argument. *)
Lemma abl_hqarch_via_bern : forall (p v b : Q) (n : nat),
  Qlt 0 p -> Qlt p 1 -> Qlt 0 v -> Qlt 0 b ->
  Qle v (b * (1 + abl_qofnat n * (/ p - 1))) ->
  sigT (fun j : nat => QleT' (abl_qpow p j * v) b).
Proof.
  intros p v b n Hp0 Hp1 Hvt0 Hb0 Hv.
  exists n.
  exact (abl_hqarch_bern_step p (/ p - 1) v b n
           (qeqT_imp_qeq _ _ (abl_canon_w_inv p))
           (Qlt_le_weak 0 (/ p - 1) (QltT_to_Qlt _ _ (abl_canon_w_pos p Hp0 Hp1)))
           Hvt0 Hb0 Hv).
Qed.

(* ================= Verification: extraction and assumption closure ================= *)

Extraction "abl_hqarch_bern_04_G3.ml" abl_bern_lower abl_qpow_ge1
  abl_hqarch_bern_step abl_hqarch_via_bern.

Print Assumptions abl_qlt_01.
Print Assumptions abl_qeq_le.
Print Assumptions abl_qle_eq_l.
Print Assumptions abl_qle_eq_r.
Print Assumptions abl_qlt_eq_l.
Print Assumptions abl_qlt_eq_r.
Print Assumptions abl_qmult_eq_l.
Print Assumptions abl_qofnat_nonneg.
Print Assumptions abl_qofnat_S.
Print Assumptions abl_boost.
Print Assumptions abl_qpow_pos.
Print Assumptions abl_bern_lower.
Print Assumptions abl_qpow_ge1.
Print Assumptions abl_qlt_neq0.
Print Assumptions abl_qmult_cancel_r.
Print Assumptions abl_qinv_eq_compat_nz.
Print Assumptions abl_qinv_le_contravar.
Print Assumptions abl_qpow_ext.
Print Assumptions abl_qpow_inv.
Print Assumptions abl_hqarch_bern_step.
Print Assumptions abl_canon_w_inv.
Print Assumptions abl_canon_w_pos.
Print Assumptions abl_hqarch_via_bern.
