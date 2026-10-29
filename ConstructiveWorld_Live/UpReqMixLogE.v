(* ==========================================================================)
   UpReqMixLogE.v - Closed-form selector and capping theorems
   Mission. mixe_cf_accept/accept_sharp (acceptance predicates),
   mixe_cf_sound_affine/sharp (soundness), mixe_cf_cap/cap_gen/cap_div
   (capping), mixe_cf_select and select_cert (selection carrying a
   certificate); the Bernoulli sharpened family and the smoke examples.
   Dependencies. Stdlib QArith, QArith.Qround, ZArith, Lia (zero in-library
   dependencies); S01_BaseRing (Id, id_refl) and S02_CauchyComplete (QltT, QleT',
   order/equality bridge lemmas).
   References. Baseline module UpReqMixLogE.v of ConstructiveWorld-Main
   ConstructiveWorld_Live (statement names carried over verbatim; census
   54=54 ordered identity; 34 wash stations).
   Constructivity. Whole file Qed-closed, no classical logic; statement faces
   carried on the Set layer (order predicates and the equality are Set-valued,
   zero Prop leakage). Prop premise slots are EXEMPT lawful keeps; every
   [Print Assumptions] audit reads Closed under the global context.
   Build. Rocq 9.1 direct: coqc -Q . "" -native-compiler no (same-world vo
   shadow tree recompile), wrapped by cpu_guard for load throttling.
   ========================================================================== *)

From Stdlib Require Import QArith.QArith.
From Stdlib Require Import QArith.Qround.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.

Require Import S01_BaseRing ( Id, id_refl ).
Require Import S02_CauchyComplete
  ( QltT, QleT', Qlt_to_QltT, QltT_to_Qlt, Qle_to_QleT', QleT'_to_Qle ).

Local Open Scope Q_scope.

(* ============================================================ *)
(* Part 0: basic utilities (mixe_ prefix; zero name clashes by whole-tree grep)  *)
(* ============================================================ *)

(* nat-scaled rational: stdlib Q.of_nat missing, self-built (vm_compute direct; zero extraction deps) *)
Definition mixe_qofnat (k : nat) : Q := (Z.of_nat k # 1)%Q.

(* Q strict-comparison bool decider (stdlib Qlt_bool missing; self-built via a    *)
(* Set-valued sumbool; Defined body with zero Prop elimination) *)
Definition mixe_qlt_bool (x y : Q) : bool :=
  if Qlt_le_dec x y then true else false.

(* ---- Qeq transport kit (rewrite stable inside Qeq goals; rewrite forbidden in *)
(*      Qlt/Qle goals: always transport by terms; AT8 card section-1 discipline) ---- *)

(* Qeq->Qle term bridge (stdlib qeq_le missing in 9.1, self-built; AT8 card same trick) *)
Lemma mixe_qeq_le : forall a b : Q, Qeq a b -> QleT' a b.
Proof.
  intros a b Hab. apply Qle_to_QleT'.
  unfold Qle, Qeq in *. rewrite Hab. apply Z.le_refl.
Qed.

Lemma mixe_qle_eq_l : forall a b c : Q, Qeq a b -> Qle b c -> QleT' a c.
Proof.
  intros a b c Hab Hbc. apply Qle_to_QleT'.
  apply (Qle_trans a b c).
  - exact (QleT'_to_Qle _ _ (mixe_qeq_le _ _ Hab)).
  - exact Hbc.
Qed.

Lemma mixe_qle_eq_r : forall a b c : Q, Qle a b -> Qeq b c -> QleT' a c.
Proof.
  intros a b c Hab Hbc. apply Qle_to_QleT'.
  apply (Qle_trans a b c).
  - exact Hab.
  - exact (QleT'_to_Qle _ _ (mixe_qeq_le _ _ Hbc)).
Qed.

Lemma mixe_qlt_eq_l : forall a b c : Q, Qeq a b -> Qlt b c -> QltT a c.
Proof.
  intros a b c Hab Hbc. apply Qlt_to_QltT.
  apply (Qle_lt_trans a b c).
  - exact (QleT'_to_Qle _ _ (mixe_qeq_le _ _ Hab)).
  - exact Hbc.
Qed.

Lemma mixe_qlt_eq_r : forall a b c : Q, Qeq a b -> Qlt c a -> QltT c b.
Proof.
  intros a b c Hab Hca. apply Qlt_to_QltT.
  apply (Qlt_le_trans c a b).
  - exact Hca.
  - exact (QleT'_to_Qle _ _ (mixe_qeq_le _ _ Hab)).
Qed.

(* ---- constant order and bool bridges ---- *)

Lemma mixe_qle_01 : QleT' 0 1.
Proof. apply Qle_to_QleT'. unfold Qle. cbn [Qnum Qden Z.mul Pos.mul]. lia. Qed.

Lemma mixe_qlt_01 : QltT 0 1.
Proof. apply Qlt_to_QltT. unfold Qlt. cbn [Qnum Qden Z.mul Pos.mul]. lia. Qed.

Lemma mixe_qlt_bool_true : forall x y : Q, Qlt x y -> Id (mixe_qlt_bool x y) true.
Proof.
  intros x y H. unfold mixe_qlt_bool.
  destruct (Qlt_le_dec x y) as [Hd | Hd].
  - apply id_refl.
  - destruct (Qlt_not_le x y H Hd).
Qed.

Lemma mixe_qlt_bool_of_true : forall x y : Q, mixe_qlt_bool x y = true -> QltT x y.
Proof.
  intros x y H. apply Qlt_to_QltT. unfold mixe_qlt_bool in H.
  destruct (Qlt_le_dec x y) as [Hd | Hd].
  - exact Hd.
  - discriminate.
Qed.

(* ---- multiplication order ledger (stdlib mult lemmas hang on the right only; left side via comm-Qeq term transport; IR3 card pitfall b) *)

Lemma mixe_qmult_nonneg : forall x y : Q, Qle 0 x -> Qle 0 y -> QleT' 0 (x * y).
Proof.
  intros x y Hx Hy. apply Qle_to_QleT'.
  apply QleT'_to_Qle.
  apply (mixe_qle_eq_l 0 (0 * y) (x * y)).
  - ring.
  - exact (Qmult_le_compat_r 0 x y Hx Hy).
Qed.

Lemma mixe_qmult_le_l : forall z x y : Q,
  Qle 0 z -> Qle x y -> QleT' (z * x) (z * y).
Proof.
  intros z x y Hz Hxy. apply Qle_to_QleT'.
  apply QleT'_to_Qle.
  apply (mixe_qle_eq_l (z * x) (x * z) (z * y)).
  - ring.
  - apply QleT'_to_Qle.
    apply (mixe_qle_eq_r (x * z) (y * z) (z * y)).
    + exact (Qmult_le_compat_r x y z Hxy Hz).
    + ring.
Qed.

Lemma mixe_qmult_pos : forall x y : Q, Qlt 0 x -> Qlt 0 y -> QltT 0 (x * y).
Proof.
  intros x y Hx Hy. apply Qlt_to_QltT.
  apply QltT_to_Qlt.
  apply (mixe_qlt_eq_l 0 (0 * y) (x * y)).
  - ring.
  - exact (Qmult_lt_compat_r 0 x y Hy Hx).
Qed.

(* "x - c <= x" (c >= 0): helper lemma for capping and Bernoulli stepping; no elimination, no division *)
Lemma mixe_le_sub : forall x c : Q, Qle 0 c -> QleT' (x - c) x.
Proof.
  intros x c Hc. apply Qle_to_QleT'. unfold Qminus.
  apply QleT'_to_Qle.
  apply (mixe_qle_eq_l (x + Qopp c) (0 + (x + Qopp c)) x).
  - ring.
  - apply QleT'_to_Qle.
    apply (mixe_qle_eq_r (0 + (x + Qopp c)) (c + (x + Qopp c)) x).
    + apply (Qplus_le_compat 0 c (x + Qopp c) (x + Qopp c)).
      * exact Hc.
      * apply Qle_refl.
    + ring.
Qed.

(* "1 - w >= 0" (w <= 1): Bernoulli power base nonnegative *)
Lemma mixe_sub_nonneg : forall w : Q, Qle w 1 -> QleT' 0 (1 - w).
Proof.
  intros w Hw1. apply Qle_to_QleT'. unfold Qminus.
  apply QleT'_to_Qle.
  apply (mixe_qle_eq_l 0 (Qopp 1 + 1) (1 + Qopp w)).
  - ring.
  - apply QleT'_to_Qle.
    apply (mixe_qle_eq_r (Qopp 1 + 1) (Qopp w + 1) (1 + Qopp w)).
    + apply (Qplus_le_compat (Qopp 1) (Qopp w) 1 1).
      * exact (Qopp_le_compat w 1 Hw1).
      * apply Qle_refl.
    + ring.
Qed.

(* "1 + q >= 0" (q >= 0) *)
Lemma mixe_one_plus_nonneg : forall q : Q, Qle 0 q -> QleT' 0 (1 + q).
Proof.
  intros q Hq. apply Qle_to_QleT'.
  apply (Qle_trans 0 1).
  - exact (QleT'_to_Qle _ _ mixe_qle_01).
  - apply QleT'_to_Qle.
    apply (mixe_qle_eq_l 1 (1 + 0) (1 + q)).
    + ring.
    + apply (Qplus_le_compat 1 1 0 q).
      * apply Qle_refl.
      * exact Hq.
Qed.

(* positivity of the Q inverse *)
Lemma mixe_qinv_pos : forall x : Q, Qlt 0 x -> QltT 0 (Qinv x).
Proof.
  intros x Hx. apply Qlt_to_QltT.
  destruct (Qlt_le_dec 0 (Qinv x)) as [Hd | Hd].
  - exact Hd.
  - exfalso.
    assert (Hle : Qle (Qinv x * x) 0).
    { apply QleT'_to_Qle.
      apply (mixe_qle_eq_r (Qinv x * x) (0 * x) 0).
      - exact (Qmult_le_compat_r (Qinv x) 0 x Hd (Qlt_le_weak 0 x Hx)).
      - ring. }
    assert (Hone : Qinv x * x == 1).
    { apply (Qeq_trans (Qinv x * x) (x * Qinv x) 1).
      - ring.
      - apply (Qmult_inv_r x).
        intro Heq.
      exact (Qlt_irrefl 0 (QltT_to_Qlt _ _ (mixe_qlt_eq_r x 0 0 Heq Hx))). }
    exact (Qlt_irrefl 0
             (Qlt_le_trans 0 1 0 (QltT_to_Qlt _ _ mixe_qlt_01)
                (QleT'_to_Qle _ _
                   (mixe_qle_eq_l 1 (Qinv x * x) 0
                      (Qeq_sym (Qinv x * x) 1 Hone) Hle)))).
Qed.

(* ---- nat-scaling ledger ---- *)

Lemma mixe_qofnat_S : forall k : nat,
  Qeq (mixe_qofnat (Datatypes.S k)) (1 + mixe_qofnat k)%Q.
Proof.
  intro k.
  unfold mixe_qofnat, Qeq, Qplus.
  cbn [Qnum Qden Z.mul Pos.mul].
  replace (Z.of_nat (Datatypes.S k)) with (Z.of_nat k + 1)%Z by lia.
  lia.
Qed.

Lemma mixe_qofnat_nonneg : forall k : nat, QleT' 0 (mixe_qofnat k).
Proof.
  intro k. apply Qle_to_QleT'. induction k as [| k IH].
  - unfold mixe_qofnat, Qle.
    cbn [Qnum Qden Z.of_nat Z.mul Pos.mul]. lia.
  - apply QleT'_to_Qle.
    apply (mixe_qle_eq_r 0 (1 + mixe_qofnat k)
             (mixe_qofnat (Datatypes.S k))).
    + apply QleT'_to_Qle. apply mixe_one_plus_nonneg. exact IH.
    + exact (Qeq_sym _ _ (mixe_qofnat_S k)).
Qed.

Lemma mixe_qofnat_succ_pos : forall k : nat, QleT' 0 (1 + mixe_qofnat k).
Proof.
  intro k. apply Qle_to_QleT'.
  apply (Qle_trans 0 (mixe_qofnat (Datatypes.S k))).
  - apply QleT'_to_Qle. apply mixe_qofnat_nonneg.
  - exact (QleT'_to_Qle _ _ (mixe_qeq_le _ _ (mixe_qofnat_S k))).
Qed.

(* ---- Z->Q order preservation (select capping chain) ---- *)

Lemma mixe_qofZ_le : forall z1 z2 : Z, (z1 <= z2)%Z -> QleT' (z1 # 1) (z2 # 1).
Proof.
  intros z1 z2 Hz. apply Qle_to_QleT'.
  unfold Qle. cbn [Qnum Qden Z.mul Pos.mul]. lia.
Qed.

(* one-sided strict shift on Q (Z-layer replace+ring normalization, closed by    *)
(* Zplus_lt_compat_r; the load-bearing converse piece of selector soundness) *)
Lemma mixe_qlt_plus_r : forall x y z : Q, Qlt x y -> QltT (x + z) (y + z).
Proof.
  intros [a da] [b db] [c dc] Hxy. apply Qlt_to_QltT.
  unfold Qlt in *.
  cbn [Qnum Qden Qplus] in *.
  replace (Z.pos (db * dc)%positive)%Z
    with (Z.pos db * Z.pos dc)%Z by reflexivity.
  replace (Z.pos (da * dc)%positive)%Z
    with (Z.pos da * Z.pos dc)%Z by reflexivity.
  replace ((a * Z.pos dc + c * Z.pos da) * (Z.pos db * Z.pos dc))%Z
    with ((a * Z.pos db) * (Z.pos dc * Z.pos dc)
          + (c * Z.pos db) * (Z.pos da * Z.pos dc))%Z by ring.
  replace ((b * Z.pos dc + c * Z.pos db) * (Z.pos da * Z.pos dc))%Z
    with ((b * Z.pos da) * (Z.pos dc * Z.pos dc)
          + (c * Z.pos db) * (Z.pos da * Z.pos dc))%Z by ring.
  apply (Zplus_lt_compat_r _ _ ((c * Z.pos db) * (Z.pos da * Z.pos dc))).
  assert (Hdc2 : (0 < Z.pos dc * Z.pos dc)%Z) by nia.
  apply Z.mul_lt_mono_pos_r.
  - exact Hdc2.
  - exact Hxy.
Qed.

(* ---- Qfloor upper-bound bridge (ceil behavior of the closed-form k formula) ---- *)

Lemma mixe_qfloor_lt : forall r : Q,
  QltT r (mixe_qofnat (Datatypes.S (Z.to_nat (Qfloor r)))).
Proof.
  intro r. apply Qlt_to_QltT.
  destruct (Z_le_gt_dec 0 (Qfloor r)) as [Hz | Hz].
  - assert (Hshift : Qeq (inject_Z (Qfloor r + 1))
                         (1 + mixe_qofnat (Z.to_nat (Qfloor r)))).
    { unfold mixe_qofnat, Qeq, Qplus, inject_Z.
      cbn [Qnum Qden Z.mul Pos.mul]. rewrite (Z2Nat.id (Qfloor r) Hz). lia. }
    apply QltT_to_Qlt.
    apply (mixe_qlt_eq_r (inject_Z (Qfloor r + 1))
             (mixe_qofnat (Datatypes.S (Z.to_nat (Qfloor r)))) r).
    + exact (Qeq_trans (inject_Z (Qfloor r + 1))
               (1 + mixe_qofnat (Z.to_nat (Qfloor r)))
               (mixe_qofnat (Datatypes.S (Z.to_nat (Qfloor r))))
               Hshift (Qeq_sym _ _ (mixe_qofnat_S (Z.to_nat (Qfloor r))))).
    + exact (Qlt_floor r).
  - assert (Hz1 : (Qfloor r + 1 <= 0)%Z) by lia.
    assert (Hstep_a : Qle (inject_Z (Qfloor r + 1)) 1%Q).
    { apply QleT'_to_Qle.
      apply (mixe_qle_eq_l (inject_Z (Qfloor r + 1))
               ((Qfloor r + 1) # 1)%Q 1%Q).
      - reflexivity.
      - assert (Hz1b : (Qfloor r + 1 <= 1)%Z) by lia.
        exact (QleT'_to_Qle _ _ (mixe_qofZ_le (Qfloor r + 1) 1 Hz1b)).
      }
    assert (Hstep_b : Qle 1%Q
               (mixe_qofnat (Datatypes.S (Z.to_nat (Qfloor r))))).
    { apply QleT'_to_Qle.
      apply (mixe_qle_eq_l 1%Q (1 + 0)%Q).
      - ring.
      - apply QleT'_to_Qle.
        apply (mixe_qle_eq_r (1 + 0)%Q
                 (1 + mixe_qofnat (Z.to_nat (Qfloor r)))
                 (mixe_qofnat (Datatypes.S (Z.to_nat (Qfloor r))))).
        + apply (Qplus_le_compat 1 1 0 (mixe_qofnat (Z.to_nat (Qfloor r)))).
          * apply Qle_refl.
          * apply QleT'_to_Qle. apply mixe_qofnat_nonneg.
        + exact (Qeq_sym _ _ (mixe_qofnat_S (Z.to_nat (Qfloor r)))). }
    apply (Qlt_le_trans r (inject_Z (Qfloor r + 1))).
    + exact (Qlt_floor r).
    + exact (Qle_trans _ _ _ Hstep_a Hstep_b).
Qed.

(* ============================================================ *)
(* Part 1: sharpened closed-form family (Q-layer cross-mult exact form list)     *)
(*   F1 mixe_bern_sharp  : (1-w)^k * (1+k*w) <= 1                          *)
(*        = "(1-w)^k <= 1/(1+kw)" cross-mult decidable exact form         *)
(*   F2 mixe_bern_lower  : 1 + k*w <= (1+w)^k                              *)
(*        = Bernoulli lower form, i.e. "(1+w)^(-k) <= (1+kw)^(-1)";         *)
(*        (in-family contrast term proving (1+w)^k membership sharper:      *)
(*   F3 mixe_sharp_pair  : (1-w)^k * (1+w)^k <= 1                          *)
(*        = "(1-w)^k <= (1+w)^(-k)" optimal-constant variant cross-mult form *)
(* ============================================================ *)

Fixpoint mixe_qpow (w : Q) (k : nat) : Q :=
  match k with
  | Datatypes.O => 1%Q
  | Datatypes.S m => w * mixe_qpow w m
  end.

Lemma mixe_qpow_nonneg : forall (x : Q) (k : nat),
  Qle 0 x -> QleT' 0 (mixe_qpow x k).
Proof.
  intros x k Hx. apply Qle_to_QleT'. induction k as [| k IH].
  - exact (QleT'_to_Qle _ _ mixe_qle_01).
  - cbn [mixe_qpow].
    exact (QleT'_to_Qle _ _ (mixe_qmult_nonneg x (mixe_qpow x k) Hx IH)).
Qed.

Lemma mixe_qpow_le_one : forall (x : Q) (k : nat),
  Qle 0 x -> Qle x 1 -> QleT' (mixe_qpow x k) 1.
Proof.
  intros x k Hx0 Hx1. apply Qle_to_QleT'. induction k as [| k IH].
  - exact (Qle_refl 1).
  - cbn [mixe_qpow].
    apply (Qle_trans _ x).
    + apply QleT'_to_Qle.
      apply (mixe_qle_eq_r (x * mixe_qpow x k) (x * 1) x).
      * exact (QleT'_to_Qle _ _ (mixe_qmult_le_l x (mixe_qpow x k) 1 Hx0 IH)).
      * ring.
    + exact Hx1.
Qed.

Lemma mixe_qpow_mul : forall (a b : Q) (k : nat),
  Qeq (mixe_qpow a k * mixe_qpow b k) (mixe_qpow (a * b) k).
Proof.
  intros a b k. induction k as [| k IH].
  - reflexivity.
  - cbn [mixe_qpow].
    apply (Qeq_trans
             (a * mixe_qpow a k * (b * mixe_qpow b k))
             (a * b * (mixe_qpow a k * mixe_qpow b k))).
    + ring.
    + rewrite IH. apply Qeq_refl.
Qed.

(* F1: sharpened Bernoulli upper form (needs only 0 <= w <= 1, weaker than  *)
(* the 0<w<1 premise of the incumbent mix_bernoulli_upper; sharpened) *)
Lemma mixe_bern_sharp : forall (w : Q) (k : nat),
  Qle 0 w -> Qle w 1 ->
  QleT' (mixe_qpow (1 - w) k * (1 + mixe_qofnat k * w)) 1.
Proof.
  intros w k Hw0 Hw1. apply Qle_to_QleT'. induction k as [| k IH].
  - cbn [mixe_qpow].
    apply QleT'_to_Qle.
    apply (mixe_qle_eq_l (1 + mixe_qofnat 0 * w) 1 1).
    + change (mixe_qofnat 0) with 0%Q. ring.
    + apply Qle_refl.
  - cbn [mixe_qpow].
    assert (HeqAB : Qeq
              ((1 - w) * mixe_qpow (1 - w) k
                 * (1 + mixe_qofnat (Datatypes.S k) * w))
              ((1 - w) * mixe_qpow (1 - w) k
                 * (1 + (1 + mixe_qofnat k) * w))).
    { rewrite (mixe_qofnat_S k). apply Qeq_refl. }
    assert (Hpw : Qle 0 (mixe_qpow (1 - w) k))
      by exact (QleT'_to_Qle _ _
             (mixe_qpow_nonneg (1 - w) k
                (QleT'_to_Qle _ _ (mixe_sub_nonneg w Hw1)))).
    assert (HC : Qle 0 ((1 + mixe_qofnat k) * w * w)).
    { apply QleT'_to_Qle.
      apply (mixe_qmult_nonneg ((1 + mixe_qofnat k) * w) w).
      - exact (QleT'_to_Qle _ _
             (mixe_qmult_nonneg (1 + mixe_qofnat k) w
                (QleT'_to_Qle _ _ (mixe_qofnat_succ_pos k)) Hw0)).
      - exact Hw0. }
    assert (Haux : Qle ((1 - w) * (1 + (1 + mixe_qofnat k) * w))
                            (1 + mixe_qofnat k * w)).
    { apply QleT'_to_Qle.
      apply (mixe_qle_eq_l
               ((1 - w) * (1 + (1 + mixe_qofnat k) * w))
               ((1 + mixe_qofnat k * w) - (1 + mixe_qofnat k) * w * w)
               (1 + mixe_qofnat k * w)).
      - ring.
      - exact (QleT'_to_Qle _ _ (mixe_le_sub _ _ HC)). }
    assert (Hmul : Qle ((1 - w) * mixe_qpow (1 - w) k
                          * (1 + (1 + mixe_qofnat k) * w))
                            (mixe_qpow (1 - w) k * (1 + mixe_qofnat k * w))).
    { apply QleT'_to_Qle.
      apply (mixe_qle_eq_l _ (mixe_qpow (1 - w) k
               * ((1 - w) * (1 + (1 + mixe_qofnat k) * w)))).
      - ring.
      - exact (QleT'_to_Qle _ _ (mixe_qmult_le_l _ _ _ Hpw Haux)). }
    exact (QleT'_to_Qle _ _
             (mixe_qle_eq_l _ _ _ HeqAB
                (Qle_trans _ _ _ Hmul IH))).
Qed.

(* F2: Bernoulli lower form (in-family contrast: 1+kw <= (1+w)^k implies 1/(1+w)^k <= 1/(1+kw)) *)
Lemma mixe_bern_lower : forall (w : Q) (k : nat),
  Qle 0 w -> QleT' (1 + mixe_qofnat k * w) (mixe_qpow (1 + w) k).
Proof.
  intros w k Hw0. apply Qle_to_QleT'. induction k as [| k IH].
  - cbn [mixe_qpow].
    apply QleT'_to_Qle.
    apply (mixe_qle_eq_l (1 + mixe_qofnat 0 * w) 1 1).
    + change (mixe_qofnat 0) with 0%Q. ring.
    + apply Qle_refl.
  - cbn [mixe_qpow].
    assert (Hp1 : Qle 0 (1 + w))
      by exact (QleT'_to_Qle _ _ (mixe_one_plus_nonneg w Hw0)).
    assert (Haux0 : Qeq (1 + (1 + mixe_qofnat k) * w)
                         ((1 + (1 + mixe_qofnat k) * w) + 0)) by ring.
    assert (Hq2 : Qle 0 (mixe_qofnat k * w * w)).
    { exact (QleT'_to_Qle _ _
               (mixe_qmult_nonneg (mixe_qofnat k * w) w
                  (QleT'_to_Qle _ _
                     (mixe_qmult_nonneg (mixe_qofnat k) w
                        (QleT'_to_Qle _ _ (mixe_qofnat_nonneg k)) Hw0)) Hw0)). }
    assert (Haux1 : Qle ((1 + (1 + mixe_qofnat k) * w) + 0)
                         ((1 + (1 + mixe_qofnat k) * w) + mixe_qofnat k * w * w))
      by exact (Qplus_le_compat (1 + (1 + mixe_qofnat k) * w)
                  (1 + (1 + mixe_qofnat k) * w) 0 (mixe_qofnat k * w * w)
                  (Qle_refl (1 + (1 + mixe_qofnat k) * w)) Hq2).
    assert (Haux2 : Qeq ((1 + (1 + mixe_qofnat k) * w) + mixe_qofnat k * w * w)
                         ((1 + w) * (1 + mixe_qofnat k * w))) by ring.
    assert (Haux : Qle (1 + (1 + mixe_qofnat k) * w)
                            ((1 + w) * (1 + mixe_qofnat k * w))).
    { exact (QleT'_to_Qle _ _
               (mixe_qle_eq_r
                  (1 + (1 + mixe_qofnat k) * w)
                  ((1 + (1 + mixe_qofnat k) * w) + mixe_qofnat k * w * w)
                  ((1 + w) * (1 + mixe_qofnat k * w))
                  (QleT'_to_Qle _ _
                     (mixe_qle_eq_l (1 + (1 + mixe_qofnat k) * w)
                        ((1 + (1 + mixe_qofnat k) * w) + 0)
                        ((1 + (1 + mixe_qofnat k) * w) + mixe_qofnat k * w * w)
                        Haux0 Haux1))
                  Haux2)). }
    assert (Hshift : Qeq (1 + mixe_qofnat (Datatypes.S k) * w)
                         (1 + (1 + mixe_qofnat k) * w)).
    { rewrite (mixe_qofnat_S k). apply Qeq_refl. }
    exact (QleT'_to_Qle _ _
             (mixe_qle_eq_l _ _ _ Hshift
                (Qle_trans _ _ _ Haux
                   (QleT'_to_Qle _ _
                      (mixe_qmult_le_l (1 + w) _ _ Hp1 IH))))).
Qed.

(* F3: optimal-constant variant: (1-w)^k (1+w)^k == (1-w^2)^k <= 1 *)
Lemma mixe_sharp_pair : forall (w : Q) (k : nat),
  Qle 0 w -> Qle w 1 ->
  QleT' (mixe_qpow (1 - w) k * mixe_qpow (1 + w) k) 1.
Proof.
  intros w k Hw0 Hw1. apply Qle_to_QleT'.
  assert (Hx0 : Qle 0 ((1 - w) * (1 + w))).
  { apply QleT'_to_Qle.
    apply (mixe_qmult_nonneg (1 - w) (1 + w)).
    - exact (QleT'_to_Qle _ _ (mixe_sub_nonneg w Hw1)).
    - exact (QleT'_to_Qle _ _ (mixe_one_plus_nonneg w Hw0)). }
  assert (Hx1 : Qle ((1 - w) * (1 + w)) 1).
  { apply QleT'_to_Qle.
    apply (mixe_qle_eq_l ((1 - w) * (1 + w)) (1 - w * w) 1).
    - ring.
    - exact (QleT'_to_Qle _ _
               (mixe_le_sub 1 (w * w)
                  (QleT'_to_Qle _ _ (mixe_qmult_nonneg w w Hw0 Hw0)))). }
  apply QleT'_to_Qle.
  apply (mixe_qle_eq_l
           (mixe_qpow (1 - w) k * mixe_qpow (1 + w) k)
           (mixe_qpow ((1 - w) * (1 + w)) k) 1).
  - exact (mixe_qpow_mul (1 - w) (1 + w) k).
  - exact (QleT'_to_Qle _ _ (mixe_qpow_le_one ((1 - w) * (1 + w)) k Hx0 Hx1)).
Qed.

(* ============================================================ *)
(* Part 2: closed-form selector (Defined, extractable), soundness, capping theorems (core pieces)  *)
(* ============================================================ *)

(* closed-form acceptance predicate of the affine member: tv0 < b0*(1+k*w)   *)
(*   = the cross-mult decidable closed form of "1/(1+kw) * TV0' < b0"       *)
Definition mixe_cf_accept (w b0 tv0 : Q) (k : nat) : bool :=
  mixe_qlt_bool tv0 (b0 * (1 + mixe_qofnat k * w)).

(* acceptance predicate of the optimal-constant member: tv0 < b0*(1+w)^k (same-family sharpened certificate) *)
Definition mixe_cf_accept_sharp (w b0 tv0 : Q) (k : nat) : bool :=
  mixe_qlt_bool tv0 (b0 * mixe_qpow (1 + w) k).

(* ---- soundness: family acceptance implies the truth certificate (1-w)^k * tv0 < b0 ---- *)

Lemma mixe_cf_sound_affine : forall (w b0 tv0 : Q) (k : nat),
  Qle 0 w -> Qle w 1 -> Qle 0 tv0 ->
  mixe_cf_accept w b0 tv0 k = true ->
  QltT (mixe_qpow (1 - w) k * tv0) b0.
Proof.
  intros w b0 tv0 k Hw0 Hw1 Htv0 Hacc. apply Qlt_to_QltT.
  destruct (Qlt_le_dec (mixe_qpow (1 - w) k * tv0) b0) as [Hd | Hbad].
  - exact Hd.
  - exfalso.
    assert (Hlt : Qlt tv0 (b0 * (1 + mixe_qofnat k * w)))
      by exact (QltT_to_Qlt _ _ (mixe_qlt_bool_of_true _ _ Hacc)).
    assert (HB : Qle (mixe_qpow (1 - w) k * (1 + mixe_qofnat k * w)) 1)
      by exact (QleT'_to_Qle _ _ (mixe_bern_sharp w k Hw0 Hw1)).
    assert (Hzle : Qle 0 (1 + mixe_qofnat k * w)).
    { apply QleT'_to_Qle.
      apply mixe_one_plus_nonneg.
      exact (QleT'_to_Qle _ _
               (mixe_qmult_nonneg (mixe_qofnat k) w
                  (QleT'_to_Qle _ _ (mixe_qofnat_nonneg k)) Hw0)). }
    assert (Hs1 : Qle (b0 * (1 + mixe_qofnat k * w))
                       ((mixe_qpow (1 - w) k * tv0) * (1 + mixe_qofnat k * w)))
      by exact (Qmult_le_compat_r b0 (mixe_qpow (1 - w) k * tv0)
                  (1 + mixe_qofnat k * w) Hbad Hzle).
    assert (Hs2a : Qeq ((mixe_qpow (1 - w) k * tv0) * (1 + mixe_qofnat k * w))
                       ((mixe_qpow (1 - w) k * (1 + mixe_qofnat k * w)) * tv0))
      by ring.
    assert (Hs2b : Qle ((mixe_qpow (1 - w) k * (1 + mixe_qofnat k * w)) * tv0)
                       (1 * tv0))
      by exact (Qmult_le_compat_r
                  (mixe_qpow (1 - w) k * (1 + mixe_qofnat k * w)) 1 tv0
                  HB Htv0).
    assert (Hs2c : Qeq (1 * tv0) tv0) by ring.
    assert (Hs2 : Qle ((mixe_qpow (1 - w) k * tv0) * (1 + mixe_qofnat k * w)) tv0).
    { exact (Qle_trans _ _ _
               (Qle_trans _ _ _ (QleT'_to_Qle _ _ (mixe_qeq_le _ _ Hs2a)) Hs2b)
               (QleT'_to_Qle _ _ (mixe_qeq_le _ _ Hs2c))). }
    exact (Qlt_irrefl tv0
             (Qlt_le_trans tv0 (b0 * (1 + mixe_qofnat k * w)) tv0 Hlt
                (Qle_trans _ _ _ Hs1 Hs2))).
Qed.

Lemma mixe_cf_sound_sharp : forall (w b0 tv0 : Q) (k : nat),
  Qle 0 w -> Qle w 1 -> Qle 0 tv0 ->
  mixe_cf_accept_sharp w b0 tv0 k = true ->
  QltT (mixe_qpow (1 - w) k * tv0) b0.
Proof.
  intros w b0 tv0 k Hw0 Hw1 Htv0 Hacc. apply Qlt_to_QltT.
  destruct (Qlt_le_dec (mixe_qpow (1 - w) k * tv0) b0) as [Hd | Hbad].
  - exact Hd.
  - exfalso.
    assert (Hlt : Qlt tv0 (b0 * mixe_qpow (1 + w) k))
      by exact (QltT_to_Qlt _ _ (mixe_qlt_bool_of_true _ _ Hacc)).
    assert (HB : Qle (mixe_qpow (1 - w) k * mixe_qpow (1 + w) k) 1)
      by exact (QleT'_to_Qle _ _ (mixe_sharp_pair w k Hw0 Hw1)).
    assert (Hzle : Qle 0 (mixe_qpow (1 + w) k))
      by exact (QleT'_to_Qle _ _
             (mixe_qpow_nonneg (1 + w) k
                (QleT'_to_Qle _ _ (mixe_one_plus_nonneg w Hw0)))).
    assert (Hs1 : Qle (b0 * mixe_qpow (1 + w) k)
                       ((mixe_qpow (1 - w) k * tv0) * mixe_qpow (1 + w) k))
      by exact (Qmult_le_compat_r b0 (mixe_qpow (1 - w) k * tv0)
                  (mixe_qpow (1 + w) k) Hbad Hzle).
    assert (Hs2a : Qeq ((mixe_qpow (1 - w) k * tv0) * mixe_qpow (1 + w) k)
                       ((mixe_qpow (1 - w) k * mixe_qpow (1 + w) k) * tv0))
      by ring.
    assert (Hs2b : Qle ((mixe_qpow (1 - w) k * mixe_qpow (1 + w) k) * tv0)
                       (1 * tv0))
      by exact (Qmult_le_compat_r
                  (mixe_qpow (1 - w) k * mixe_qpow (1 + w) k) 1 tv0
                  HB Htv0).
    assert (Hs2c : Qeq (1 * tv0) tv0) by ring.
    assert (Hs2 : Qle ((mixe_qpow (1 - w) k * tv0) * mixe_qpow (1 + w) k) tv0).
    { exact (Qle_trans _ _ _
               (Qle_trans _ _ _ (QleT'_to_Qle _ _ (mixe_qeq_le _ _ Hs2a)) Hs2b)
               (QleT'_to_Qle _ _ (mixe_qeq_le _ _ Hs2c))). }
    exact (Qlt_irrefl tv0
             (Qlt_le_trans tv0 (b0 * mixe_qpow (1 + w) k) tv0 Hlt
                (Qle_trans _ _ _ Hs1 Hs2))).
Qed.

(* ---- capping theorems (core pieces) ---- *)

(* generic slope form: any family member/constant that keeps the algebra     *)
(* invertible (affine form b0 + k*c) caps on acceptance; constant improvements only rescale the slope c, the order of magnitude stays linear *)
Theorem mixe_cf_cap_gen : forall (b0 c tv0 : Q) (k : nat),
  Qlt tv0 (b0 + mixe_qofnat k * c) ->
  QltT (Qminus tv0 b0) (mixe_qofnat k * c).
Proof.
  intros b0 c tv0 k Hlt. apply Qlt_to_QltT.
  unfold Qminus.
  assert (Hle : Qle (tv0 + Qopp b0) (mixe_qofnat k * c)).
  { apply QleT'_to_Qle.
    apply (mixe_qle_eq_r (tv0 + Qopp b0)
             ((b0 + mixe_qofnat k * c) + Qopp b0) (mixe_qofnat k * c)).
    - apply (Qplus_le_compat tv0 (b0 + mixe_qofnat k * c) (Qopp b0) (Qopp b0)).
      + exact (Qlt_le_weak tv0 (b0 + mixe_qofnat k * c) Hlt).
      + apply Qle_refl.
    - ring. }
  destruct (Qlt_le_dec (tv0 + Qopp b0) (mixe_qofnat k * c)) as [Hd | Hb].
  - exact Hd.
  - exfalso.
    assert (Hle2 : Qle (b0 + mixe_qofnat k * c) (b0 + (tv0 + Qopp b0))).
    { apply (Qplus_le_compat b0 b0 (mixe_qofnat k * c) (tv0 + Qopp b0)).
      - apply Qle_refl.
      - exact Hb. }
    apply (Qlt_irrefl tv0).
    apply QltT_to_Qlt.
    apply (mixe_qlt_eq_r (b0 + (tv0 + Qopp b0)) tv0 tv0).
    + ring.
    + exact (Qlt_le_trans tv0 (b0 + mixe_qofnat k * c)
               (b0 + (tv0 + Qopp b0)) Hlt Hle2).
Qed.

(* main capping theorem: affine-member closed-form acceptance implies tv0-b0 < k*(w*b0) *)
Theorem mixe_cf_cap : forall (w b0 tv0 : Q) (k : nat),
  Qlt 0 w -> Qlt 0 b0 ->
  mixe_cf_accept w b0 tv0 k = true ->
  QltT (Qminus tv0 b0) (mixe_qofnat k * (w * b0)).
Proof.
  intros w b0 tv0 k Hw Hb0 Hacc. apply Qlt_to_QltT.
  apply QltT_to_Qlt.
  apply (mixe_cf_cap_gen b0 (w * b0) tv0 k).
  apply QltT_to_Qlt.
  apply (mixe_qlt_eq_r
           (b0 * (1 + mixe_qofnat k * w))
           (b0 + mixe_qofnat k * (w * b0)) tv0).
  - ring.
  - exact (QltT_to_Qlt _ _ (mixe_qlt_bool_of_true _ _ Hacc)).
Qed.

(* exact division form: k > (TV0'/b0 - 1)/w, i.e. (tv0-b0)/(w*b0) < k *)
Theorem mixe_cf_cap_div : forall (w b0 tv0 : Q) (k : nat),
  Qlt 0 w -> Qlt 0 b0 ->
  mixe_cf_accept w b0 tv0 k = true ->
  QltT ((Qminus tv0 b0) * Qinv (w * b0)) (mixe_qofnat k).
Proof.
  intros w b0 tv0 k Hw Hb0 Hacc. apply Qlt_to_QltT.
  assert (Hzwb : Qlt 0 (w * b0))
    by exact (QltT_to_Qlt _ _ (mixe_qmult_pos w b0 Hw Hb0)).
  assert (Hinv : Qlt 0 (Qinv (w * b0)))
    by exact (QltT_to_Qlt _ _ (mixe_qinv_pos _ Hzwb)).
  apply QltT_to_Qlt.
  apply (mixe_qlt_eq_r
           (mixe_qofnat k * (w * b0) * Qinv (w * b0))
           (mixe_qofnat k)
           ((Qminus tv0 b0) * Qinv (w * b0))).
  - apply (Qeq_trans (mixe_qofnat k * (w * b0) * Qinv (w * b0))
             (mixe_qofnat k * ((w * b0) * Qinv (w * b0)))).
    + ring.
    + assert (Hone2 : (w * b0) * Qinv (w * b0) == 1).
      { apply (Qmult_inv_r (w * b0)).
        intro Heq.
        exact (Qlt_irrefl 0
                 (QltT_to_Qlt _ _ (mixe_qlt_eq_r (w * b0) 0 0 Heq Hzwb))). }
      rewrite Hone2.
      apply (Qmult_1_r _).
  - exact (Qmult_lt_compat_r (Qminus tv0 b0) (mixe_qofnat k * (w * b0))
             (Qinv (w * b0)) Hinv
             (QltT_to_Qlt _ _ (mixe_cf_cap w b0 tv0 k Hw Hb0 Hacc))).
Qed.

(* ============================================================ *)
(* Part 3: closed-form k-formula selector (no search, Defined extractable; the capping target itself)   *)
(*   k := 1 + floor( (TV0'-b0)/(w*b0) ): solved by pure algebra, zero predicate iteration *)
(* ============================================================ *)

Definition mixe_cf_select (w b0 tv0 : Q) : nat :=
  Datatypes.S (Z.to_nat (Qfloor (Qminus tv0 b0 * Qinv (w * b0)))).

(* capped at the selector's return: k > (TV0'-b0)/(w*b0) = (TV0'/b0 - 1)/w (lower bound sealed) *)
Theorem mixe_cf_select_cap : forall (w b0 tv0 : Q),
  QltT ((Qminus tv0 b0) * Qinv (w * b0)) (mixe_qofnat (mixe_cf_select w b0 tv0)).
Proof.
  intros w b0 tv0.
  unfold mixe_cf_select.
  exact (mixe_qfloor_lt (Qminus tv0 b0 * Qinv (w * b0))).
Qed.

(* selector self-witness: the returned k closes affine acceptance (the formula is the solution) *)
Theorem mixe_cf_select_accept : forall (w b0 tv0 : Q),
  Qlt 0 w -> Qlt 0 b0 ->
  Id (mixe_cf_accept w b0 tv0 (mixe_cf_select w b0 tv0)) true.
Proof.
  intros w b0 tv0 Hw Hb0.
  assert (Hzwb : Qlt 0 (w * b0))
    by exact (QltT_to_Qlt _ _ (mixe_qmult_pos w b0 Hw Hb0)).
  assert (Hrk : Qlt ((Qminus tv0 b0) * Qinv (w * b0))
                    (mixe_qofnat (mixe_cf_select w b0 tv0)))
    by exact (QltT_to_Qlt _ _ (mixe_cf_select_cap w b0 tv0)).
  assert (Hmult : Qlt ((Qminus tv0 b0 * Qinv (w * b0)) * (w * b0))
                      (mixe_qofnat (mixe_cf_select w b0 tv0) * (w * b0)))
    by exact (Qmult_lt_compat_r _ _ _ Hzwb Hrk).
  assert (HeqL : Qeq ((Qminus tv0 b0 * Qinv (w * b0)) * (w * b0))
                     (Qminus tv0 b0)).
  { apply (Qeq_trans ((Qminus tv0 b0 * Qinv (w * b0)) * (w * b0))
             (Qminus tv0 b0 * ((w * b0) * Qinv (w * b0)))).
    - ring.
    - assert (Hone2 : (w * b0) * Qinv (w * b0) == 1).
      { apply (Qmult_inv_r (w * b0)).
        intro Heq.
        exact (Qlt_irrefl 0
                 (QltT_to_Qlt _ _ (mixe_qlt_eq_r (w * b0) 0 0 Heq Hzwb))). }
      rewrite Hone2.
      apply (Qmult_1_r _). }
  assert (Hlt2 : Qlt (Qminus tv0 b0)
                     (mixe_qofnat (mixe_cf_select w b0 tv0) * (w * b0))).
  { apply QltT_to_Qlt.
    apply (mixe_qlt_eq_l (Qminus tv0 b0)
             ((Qminus tv0 b0) * Qinv (w * b0) * (w * b0))
             (mixe_qofnat (mixe_cf_select w b0 tv0) * (w * b0))).
    - exact (Qeq_sym _ _ HeqL).
    - exact Hmult. }
  assert (Hplus : Qlt (b0 + Qminus tv0 b0)
                      (b0 + mixe_qofnat (mixe_cf_select w b0 tv0) * (w * b0))).
  { apply QltT_to_Qlt.
    apply (mixe_qlt_eq_r
             (mixe_qofnat (mixe_cf_select w b0 tv0) * (w * b0) + b0)
             (b0 + mixe_qofnat (mixe_cf_select w b0 tv0) * (w * b0))
             (b0 + Qminus tv0 b0)).
    - ring.
    - apply QltT_to_Qlt.
      apply (mixe_qlt_eq_l (b0 + Qminus tv0 b0)
               (Qminus tv0 b0 + b0)
               (mixe_qofnat (mixe_cf_select w b0 tv0) * (w * b0) + b0)).
      + ring.
      + exact (QltT_to_Qlt _ _
                 (mixe_qlt_plus_r (Qminus tv0 b0)
                    (mixe_qofnat (mixe_cf_select w b0 tv0) * (w * b0)) b0 Hlt2)). }
  unfold mixe_cf_accept.
  apply mixe_qlt_bool_true.
  apply QltT_to_Qlt.
  apply (mixe_qlt_eq_r
           (b0 + mixe_qofnat (mixe_cf_select w b0 tv0) * (w * b0))
           (b0 * (1 + mixe_qofnat (mixe_cf_select w b0 tv0) * w))
           tv0).
  - ring.
  - apply QltT_to_Qlt.
    apply (mixe_qlt_eq_l tv0 (b0 + Qminus tv0 b0)
             (b0 + mixe_qofnat (mixe_cf_select w b0 tv0) * (w * b0))).
    + ring.
    + exact Hplus.
Qed.

(* full closed-route soundness: the returned k carries the truth certificate (1-w)^k * tv0 < b0 *)
Theorem mixe_cf_select_cert : forall (w b0 tv0 : Q),
  Qlt 0 w -> Qle w 1 -> Qle 0 tv0 -> Qlt 0 b0 ->
  QltT (mixe_qpow (1 - w) (mixe_cf_select w b0 tv0) * tv0) b0.
Proof.
  intros w b0 tv0 Hw Hw1 Htv0 Hb0.
  apply (mixe_cf_sound_affine w b0 tv0 (mixe_cf_select w b0 tv0)).
  - exact (Qlt_le_weak 0 w Hw).
  - exact Hw1.
  - exact Htv0.
  - assert (HaccE : mixe_cf_accept w b0 tv0 (mixe_cf_select w b0 tv0) = true).
    { pose proof (mixe_cf_select_accept w b0 tv0 Hw Hb0) as HID.
      destruct HID. reflexivity. }
    exact HaccE.
Qed.

(* ============================================================ *)
(* Part 4: self-check anchors (vm_compute direct checks, w = 1#10; the Qle/Qlt sides computed directly on the bool face) *)
(*   (1) family both sides k=9 vs k=10: acceptance around the 39/20 bound     *)
(*   (2) capping both sides: cap instance violated on the 9 side / holds on the 10 side  *)
(*   (3) linear vs logarithmic contrast: closed-form k=91 (TV0'=1, b0=1/10); *)
(*      true minimal station k=22 (decidable search domain), sharpened-member station k=25 *)
(* ============================================================ *)

Example mixe_smoke_bern_sharp_9 :
  Qle_bool (mixe_qpow (9 # 10) 9 * (1 + mixe_qofnat 9 * (1 # 10))) 1 = true.
Proof. vm_compute. reflexivity. Qed.

Example mixe_smoke_bern_sharp_10 :
  Qle_bool (mixe_qpow (9 # 10) 10 * (1 + mixe_qofnat 10 * (1 # 10))) 1 = true.
Proof. vm_compute. reflexivity. Qed.

Example mixe_smoke_accept_9_false :
  mixe_cf_accept (1 # 10) 1 (39 # 20) 9%nat = false.
Proof. vm_compute. reflexivity. Qed.

Example mixe_smoke_accept_10_true :
  mixe_cf_accept (1 # 10) 1 (39 # 20) 10%nat = true.
Proof. vm_compute. reflexivity. Qed.

Example mixe_smoke_cap_9_side :
  mixe_qlt_bool ((39 # 20) - 1) (mixe_qofnat 9 * ((1 # 10) * 1)) = false.
Proof. vm_compute. reflexivity. Qed.

Example mixe_smoke_cap_10_side :
  mixe_qlt_bool ((39 # 20) - 1) (mixe_qofnat 10 * ((1 # 10) * 1)) = true.
Proof. vm_compute. reflexivity. Qed.

(* the closed k-formula returns 91: k = 1 + floor((1 - 1/10)/(1/10 * 1)) = 1 + 90 *)
Example mixe_smoke_select_91 :
  mixe_cf_select (1 # 10) (1 # 10) 1 = 91%nat.
Proof. vm_compute. reflexivity. Qed.

Example mixe_smoke_select_cert_91 :
  mixe_qlt_bool (mixe_qpow (9 # 10) 91 * 1) (1 # 10) = true.
Proof. vm_compute. reflexivity. Qed.

(* contrast: true minimal station k=22 ((9/10)^22 < 1/10); affine closed-form acceptance *)
(* not yet closed at k=22: the linear-91 vs true-minimal-22 methodology gap is a computable witness *)
Example mixe_smoke_true_min_22 :
  mixe_qlt_bool (mixe_qpow (9 # 10) 22 * 1) (1 # 10) = true.
Proof. vm_compute. reflexivity. Qed.

Example mixe_smoke_affine_not_22 :
  mixe_cf_accept (1 # 10) (1 # 10) 1 22%nat = false.
Proof. vm_compute. reflexivity. Qed.

(* sharpened-member acceptance station: 1 < (1/10)(11/10)^25 (k=24 false / k=25 true); *)
(* the minimal passing station of a monotone decidable predicate is where the logarithmic order of decidable search comes from *)
Example mixe_smoke_sharp_24_false :
  mixe_cf_accept_sharp (1 # 10) (1 # 10) 1 24%nat = false.
Proof. vm_compute. reflexivity. Qed.

Example mixe_smoke_sharp_25_true :
  mixe_cf_accept_sharp (1 # 10) (1 # 10) 1 25%nat = true.
Proof. vm_compute. reflexivity. Qed.

(* ============================================================ *)
(* G4 audit block (expect every audit to read Closed: no new assumptions) *)
(* ============================================================ *)

Print Assumptions mixe_bern_sharp.
Print Assumptions mixe_bern_lower.
Print Assumptions mixe_sharp_pair.
Print Assumptions mixe_cf_sound_affine.
Print Assumptions mixe_cf_sound_sharp.
Print Assumptions mixe_cf_cap_gen.
Print Assumptions mixe_cf_cap.
Print Assumptions mixe_cf_cap_div.
Print Assumptions mixe_cf_select_cap.
Print Assumptions mixe_cf_select_accept.
Print Assumptions mixe_cf_select_cert.
Print Assumptions mixe_cf_select.
