(* ===================================================================== *)
(* sl3_d3_gf_carrier.v                                                   *)
(*                                                                       *)
(* Mission. Integer convolution carrier for the generating-function      *)
(*   decomposition of the multiple-sum coefficients: Z tables (index 0 = *)
(*   constant term) with entrywise addition [add_tbl], Cauchy convolution*)
(*   [conv], powers [gf_pow] and coefficient sums [gf_sum]; the Pascal   *)
(*   binomial [binomP] with its order facts; nonnegativity of tables as  *)
(*   a decidable per-entry scan; and the length law for [add_tbl].       *)
(* Dependencies. Stdlib ZArith, Arith.Arith, Lia, List only; no          *)
(*   development-internal requires.                                      *)
(* References. The rational form of the ZZ coefficient extraction line   *)
(*   (numerator side of the pole-kernel coefficient); the generating-    *)
(*   function decomposition item of the SL3 series.                      *)
(* Constructivity. Every statement is carried at the Set layer:          *)
(*   equations as the single-constructor identity [gfc_id], order facts  *)
(*   as the decidable boolean-identity carriers [gfc_zlt]/[gfc_zle]/     *)
(*   [gfc_natlt]/[gfc_natle] over [Z.ltb]/[Z.leb]/[Nat.ltb]/[Nat.leb],   *)
(*   and table nonnegativity as the boolean scan identity [tbl_nonneg f  *)
(*   := gfc_id (tbl_all_leb f) true].  Prop-face equations occur only as *)
(*   in-body scaffolding discharged by the kernel, never as statements.  *)
(*   Definitions and lemmas close transparently ([Defined]).             *)
(* Build. Rocq 9.3: coqc -Q <world root> "" sl3_d3_gf_carrier.v; single  *)
(*   all-names Separate Extraction driver, ocamlc compiled, sample run.  *)
(* ===================================================================== *)

From Stdlib Require Import ZArith.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
Import ListNotations.
Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(* Set-level identity carrier: statements relate their two sides by    *)
(* [gfc_id], the Set-sorted Leibniz equality with a single reflective  *)
(* constructor; Prop-face [eq] serves only inside proof bodies.        *)
(* ------------------------------------------------------------------ *)

Inductive gfc_id {A : Set} (x : A) : A -> Set :=
  gfc_idrefl : gfc_id x x.

Arguments gfc_idrefl {A} {x}.

Definition gfc_idsym {A : Set} {x y : A} (p : gfc_id x y) : gfc_id y x :=
  match p with gfc_idrefl => gfc_idrefl end.

(* Decidable order facts as boolean-identity carriers: the nat-lt and   *)
(* Z-lt families are carried as a matched pair, each over its boolean   *)
(* comparison.                                                          *)
Definition gfc_zlt (a b : Z) : Set := gfc_id (Z.ltb a b) true.
Definition gfc_zle (a b : Z) : Set := gfc_id (Z.leb a b) true.
Definition gfc_natlt (n m : nat) : Set := gfc_id (Nat.ltb n m) true.
Definition gfc_natle (n m : nat) : Set := gfc_id (Nat.leb n m) true.

(* ------------------------------------------------------------------ *)
(* Power helpers (nat-shaped exponents over Z)                          *)
(* ------------------------------------------------------------------ *)

Lemma pow9_S : forall k : nat, gfc_id (9 ^ Z.of_nat (S k)) (9 * 9 ^ Z.of_nat k)%Z.
Proof.
  assert (Hc : forall k : nat, (9 ^ Z.of_nat (S k))%Z = (9 * 9 ^ Z.of_nat k)%Z).
  { intros k. rewrite Nat2Z.inj_succ. rewrite Z.pow_succ_r by lia. reflexivity. }
  intros k. rewrite (Hc k). apply gfc_idrefl.
Defined.

Lemma pow10_S : forall k : nat, gfc_id (10 ^ Z.of_nat (S k)) (10 * 10 ^ Z.of_nat k)%Z.
Proof.
  assert (Hc : forall k : nat, (10 ^ Z.of_nat (S k))%Z = (10 * 10 ^ Z.of_nat k)%Z).
  { intros k. rewrite Nat2Z.inj_succ. rewrite Z.pow_succ_r by lia. reflexivity. }
  intros k. rewrite (Hc k). apply gfc_idrefl.
Defined.

Lemma pow_two_mul : forall (a : Z) (n : nat),
  gfc_id (a ^ Z.of_nat (2 * n)) ((a * a) ^ Z.of_nat n)%Z.
Proof.
  assert (Hc : forall (a : Z) (n : nat), (a ^ Z.of_nat (2 * n))%Z = ((a * a) ^ Z.of_nat n)%Z).
  { intros a n. replace (2 * n)%nat with (n + n)%nat by lia.
    rewrite Nat2Z.inj_add. rewrite Z.pow_add_r by lia. rewrite Z.pow_mul_l. reflexivity. }
  intros a n. rewrite (Hc a n). apply gfc_idrefl.
Defined.

Lemma zpow9_pos : forall k : nat, gfc_zlt 0 (9 ^ Z.of_nat k).
Proof.
  induction k as [| k IH].
  - unfold gfc_zlt. cbn [Z.of_nat Z.pow]. apply gfc_idrefl.
  - assert (Hb0 : (0 <? 9 ^ Z.of_nat k)%Z = true).
    { unfold gfc_zlt in IH. destruct (Z.ltb 0 (9 ^ Z.of_nat k)) eqn:E.
      - reflexivity.
      - inversion IH. }
    pose proof (proj1 (Z.ltb_lt 0 (9 ^ Z.of_nat k)) Hb0) as Hpos.
    assert (Hb1 : (0 <? 9 * 9 ^ Z.of_nat k)%Z = true).
    { apply (proj2 (Z.ltb_lt 0 (9 * 9 ^ Z.of_nat k))).
      pose proof (Z.mul_pos_pos 9 (9 ^ Z.of_nat k) (ltac:(lia)) Hpos) as HP.
      exact HP. }
    unfold gfc_zlt. rewrite Nat2Z.inj_succ. rewrite Z.pow_succ_r by lia.
    rewrite Hb1. apply gfc_idrefl.
Defined.

Lemma zpow10_pos : forall k : nat, gfc_zlt 0 (10 ^ Z.of_nat k).
Proof.
  induction k as [| k IH].
  - unfold gfc_zlt. cbn [Z.of_nat Z.pow]. apply gfc_idrefl.
  - assert (Hb0 : (0 <? 10 ^ Z.of_nat k)%Z = true).
    { unfold gfc_zlt in IH. destruct (Z.ltb 0 (10 ^ Z.of_nat k)) eqn:E.
      - reflexivity.
      - inversion IH. }
    pose proof (proj1 (Z.ltb_lt 0 (10 ^ Z.of_nat k)) Hb0) as Hpos.
    assert (Hb1 : (0 <? 10 * 10 ^ Z.of_nat k)%Z = true).
    { apply (proj2 (Z.ltb_lt 0 (10 * 10 ^ Z.of_nat k))).
      pose proof (Z.mul_pos_pos 10 (10 ^ Z.of_nat k) (ltac:(lia)) Hpos) as HP.
      exact HP. }
    unfold gfc_zlt. rewrite Nat2Z.inj_succ. rewrite Z.pow_succ_r by lia.
    rewrite Hb1. apply gfc_idrefl.
Defined.

(* ------------------------------------------------------------------ *)
(* Pascal binomials (nat-valued, recursive on the upper index)          *)
(* ------------------------------------------------------------------ *)

Fixpoint binomP (n k : nat) {struct n} : nat :=
  match k with
  | O => 1%nat
  | S k' =>
      match n with
      | O => 0%nat
      | S n' => (binomP n' k' + binomP n' (S k'))%nat
      end
  end.

Lemma binomP_zero : forall n k, gfc_natlt n k -> gfc_id (binomP n k) 0%nat.
Proof.
  intros n k H.
  assert (Hlt : (n < k)%nat).
  { unfold gfc_natlt in H. destruct (Nat.ltb n k) eqn:E.
    - apply (proj1 (Nat.ltb_lt n k)). exact E.
    - inversion H. }
  assert (Hc : forall m j, (m < j)%nat -> (binomP m j = 0)%nat).
  { intros m. induction m as [| m IH]; intros j Hj.
    - destruct j as [| j']; cbn [binomP]; lia.
    - destruct j as [| j']; cbn [binomP].
      + lia.
      + rewrite (IH (S j')) by lia. rewrite (IH j') by lia. lia. }
  rewrite (Hc n k Hlt). apply gfc_idrefl.
Defined.

Lemma binomP_step0 : forall m, gfc_id (binomP (S m) 0) 1%nat.
Proof. intros m. cbn [binomP]. apply gfc_idrefl. Defined.

Lemma binomP_stepS : forall m t,
  gfc_id (binomP (S m) (S t)) (binomP m t + binomP m (S t))%nat.
Proof. intros m t. cbn [binomP]. apply gfc_idrefl. Defined.

Lemma binomP_diag : forall n, gfc_id (binomP n n) 1%nat.
Proof.
  assert (Hc : forall n, (binomP n n = 1)%nat).
  { induction n as [| n IH].
    - reflexivity.
    - cbn [binomP]. rewrite IH.
      assert (Hprem : gfc_natlt n (S n)).
      { unfold gfc_natlt.
        assert (Hb : (n <? S n)%nat = true) by (apply (proj2 (Nat.ltb_lt n (S n))); lia).
        rewrite Hb. apply gfc_idrefl. }
      destruct (gfc_idsym (binomP_zero n (S n) Hprem)). reflexivity. }
  intros n. rewrite (Hc n). apply gfc_idrefl.
Defined.

Lemma binomP_k0 : forall n, gfc_id (binomP n 0) 1%nat.
Proof.
  assert (Hc : forall n, (binomP n 0 = 1)%nat).
  { induction n as [| n]; cbn [binomP]; reflexivity. }
  intros n. rewrite (Hc n). apply gfc_idrefl.
Defined.

Lemma binomP_ge1 : forall n k, gfc_natle k n -> gfc_natle 1 (binomP n k).
Proof.
  intros n k H.
  assert (Hk : (k <= n)%nat).
  { unfold gfc_natle in H. destruct (Nat.leb k n) eqn:E.
    - apply (proj1 (Nat.leb_le k n)). exact E.
    - inversion H. }
  assert (Hc : forall m j, (j <= m)%nat -> (1 <= binomP m j)%nat).
  { intros m. induction m as [| m IH]; intros j Hj.
    - assert (Hj0 : (j = 0)%nat) by lia. subst j. cbn [binomP]. lia.
    - destruct j as [| j'].
      + cbn [binomP]. lia.
      + cbn [binomP]. pose proof (IH j' (ltac:(lia))). lia. }
  unfold gfc_natle. assert (Hb : (1 <=? binomP n k)%nat = true).
  { apply (proj2 (Nat.leb_le 1 (binomP n k))). apply Hc. exact Hk. }
  rewrite Hb. apply gfc_idrefl.
Defined.

Lemma binomP_l1 : forall n, gfc_id (binomP n 1) n%nat.
Proof.
  assert (Hc : forall n, (binomP n 1 = n)%nat).
  { induction n as [| n IH].
    - reflexivity.
    - cbn [binomP].
      assert (H0 : (binomP n 0 = 1)%nat) by (destruct n; reflexivity).
      rewrite H0. rewrite IH. lia. }
  intros n. rewrite (Hc n). apply gfc_idrefl.
Defined.

Lemma binomP_diag_succ : forall n, gfc_id (binomP (S n) n) (S n)%nat.
Proof.
  assert (Hc : forall n, (binomP (S n) n = S n)%nat).
  { induction n as [| n IH].
    - reflexivity.
    - destruct (gfc_idsym (binomP_stepS (S n) n)).
      rewrite IH.
      destruct (gfc_idsym (binomP_diag (S n))). lia. }
  intros n. rewrite (Hc n). apply gfc_idrefl.
Defined.

Lemma binomP_sym : forall n k, gfc_natle k n -> gfc_id (binomP n k) (binomP n (n - k))%nat.
Proof.
  intros n k H.
  assert (Hk : (k <= n)%nat).
  { unfold gfc_natle in H. destruct (Nat.leb k n) eqn:E.
    - apply (proj1 (Nat.leb_le k n)). exact E.
    - inversion H. }
  assert (Hc : forall m j, (j <= m)%nat -> (binomP m j = binomP m (m - j))%nat).
  { intros m. induction m as [| m IH]; intros j Hj.
    - destruct j as [| j']; [ reflexivity | lia ].
    - destruct j as [| j'].
      + replace (S m - 0)%nat with (S m)%nat by lia.
        destruct (gfc_idsym (binomP_step0 m)).
        destruct (gfc_idsym (binomP_diag (S m))).
        reflexivity.
      + destruct (Nat.eq_dec j' m) as [Heq | Hne].
        * subst j'. replace (S m - S m)%nat with 0%nat by lia.
          destruct (gfc_idsym (binomP_step0 m)).
          destruct (gfc_idsym (binomP_diag (S m))).
          reflexivity.
        * assert (Hk'n : (S j' <= m)%nat) by lia.
          assert (Hidx : (S (m - S j') <= m)%nat) by lia.
          pose proof (IH (S j') Hk'n) as E2.
          pose proof (IH (S (m - S j')) Hidx) as E3.
          replace (m - S (m - S j'))%nat with j'%nat in E3 by lia.
          replace (S m - S j')%nat with (S (m - S j'))%nat by lia.
          cbn [binomP]. rewrite E3. rewrite E2. lia. }
  rewrite (Hc n k Hk). apply gfc_idrefl.
Defined.

Lemma binomP_Z_nonneg : forall n k, gfc_zle 0 (Z.of_nat (binomP n k)).
Proof.
  intros n k. unfold gfc_zle.
  assert (Hb : (0 <=? Z.of_nat (binomP n k))%Z = true).
  { apply (proj2 (Z.leb_le 0 (Z.of_nat (binomP n k)))). apply Nat2Z.is_nonneg. }
  rewrite Hb. apply gfc_idrefl.
Defined.

Lemma binomP_pos_in : forall p j, gfc_natle j p -> gfc_zlt 0 (Z.of_nat (binomP (p + j) j)).
Proof.
  intros p j H.
  assert (Hj : (j <= p)%nat).
  { unfold gfc_natle in H. destruct (Nat.leb j p) eqn:E.
    - apply (proj1 (Nat.leb_le j p)). exact E.
    - inversion H. }
  assert (Hc : forall q r, (r <= q)%nat -> (0 < Z.of_nat (binomP (q + r) r))%Z).
  { intros q r Hr.
    assert (Hprem : gfc_natle r (q + r)).
    { unfold gfc_natle.
      assert (Hb : (r <=? q + r)%nat = true) by (apply (proj2 (Nat.leb_le r (q + r))); lia).
      rewrite Hb. apply gfc_idrefl. }
    assert (Hs : (binomP (q + r) r = binomP (q + r) q)%nat).
    { destruct (gfc_idsym (binomP_sym (q + r) r Hprem)).
      replace ((q + r) - r)%nat with q%nat by lia. reflexivity. }
    rewrite Hs.
    assert (Hg : (1 <= binomP (q + r) q)%nat).
    { assert (Hprem2 : gfc_natle q (q + r)).
      { unfold gfc_natle.
        assert (Hb : (q <=? q + r)%nat = true) by (apply (proj2 (Nat.leb_le q (q + r))); lia).
        rewrite Hb. apply gfc_idrefl. }
      pose proof (binomP_ge1 (q + r) q Hprem2) as HG.
      assert (E2 : (1 <=? binomP (q + r) q)%nat = true).
      { unfold gfc_natle in HG. destruct (Nat.leb 1 (binomP (q + r) q)) eqn:Ex.
        - reflexivity.
        - inversion HG. }
      exact (proj1 (Nat.leb_le 1 (binomP (q + r) q)) E2). }
    lia. }
  unfold gfc_zlt.
  assert (Hb : (0 <? Z.of_nat (binomP (p + j) j))%Z = true).
  { apply (proj2 (Z.ltb_lt 0 (Z.of_nat (binomP (p + j) j)))). apply Hc. exact Hj. }
  rewrite Hb. apply gfc_idrefl.
Defined.

(* ------------------------------------------------------------------ *)
(* Z-coefficient tables (index 0 = constant coefficient)                *)
(* ------------------------------------------------------------------ *)

Definition tbl := list Z.

Fixpoint add_tbl (f g : tbl) : tbl :=
  match f, g with
  | [], _ => g
  | _, [] => f
  | a :: f', b :: g' => (a + b)%Z :: add_tbl f' g'
  end.

Fixpoint conv (f g : tbl) : tbl :=
  match f with
  | [] => []
  | a :: f' => add_tbl (map (Z.mul a) g) (0%Z :: conv f' g)
  end.

Fixpoint gf_pow (f : tbl) (k : nat) : tbl :=
  match k with
  | O => [1]%Z
  | S k' => conv f (gf_pow f k')
  end.

Definition gf_sum (f : tbl) : Z := fold_right Z.add 0 f.

Lemma gf_sum_nil : gfc_id (gf_sum []) 0%Z.
Proof. cbn [gf_sum]. apply gfc_idrefl. Defined.

Lemma gf_sum_cons : forall x f, gfc_id (gf_sum (x :: f)) (x + gf_sum f)%Z.
Proof. intros x f. cbn [gf_sum]. apply gfc_idrefl. Defined.

Lemma gf_sum_add : forall f g, gfc_id (gf_sum (add_tbl f g)) (gf_sum f + gf_sum g)%Z.
Proof.
  assert (Hc : forall f g, (gf_sum (add_tbl f g) = gf_sum f + gf_sum g)%Z).
  { intros f. induction f as [| a f IH]; intros g.
    - destruct g as [| b g]; cbn [add_tbl gf_sum fold_right].
      + ring.
      + ring.
    - destruct g as [| b g]; cbn [add_tbl].
      + cbn [gf_sum fold_right]. ring.
      + destruct (gfc_idsym (gf_sum_cons (a + b) (add_tbl f g))).
        rewrite IH.
        destruct (gfc_idsym (gf_sum_cons a f)).
        destruct (gfc_idsym (gf_sum_cons b g)).
        ring. }
  intros f g. rewrite (Hc f g). apply gfc_idrefl.
Defined.

Lemma fold_map_mul : forall (a : Z) f,
  gfc_id (fold_right Z.add 0 (map (Z.mul a) f)) (a * fold_right Z.add 0 f)%Z.
Proof.
  assert (Hc : forall (a : Z) f,
    (fold_right Z.add 0 (map (Z.mul a) f) = a * fold_right Z.add 0 f)%Z).
  { intros a f. induction f as [| b f IH].
    - cbn [map fold_right]. ring.
    - cbn [map fold_right]. rewrite IH. ring. }
  intros a f. rewrite (Hc a f). apply gfc_idrefl.
Defined.

Lemma gf_sum_map_mul : forall (a : Z) f, gfc_id (gf_sum (map (Z.mul a) f)) (a * gf_sum f)%Z.
Proof.
  assert (Hc : forall (a : Z) f, (gf_sum (map (Z.mul a) f) = a * gf_sum f)%Z).
  { intros a f. unfold gf_sum. induction f as [| b f IH].
    - cbn [map fold_right]. ring.
    - cbn [map fold_right]. rewrite IH. ring. }
  intros a f. rewrite (Hc a f). apply gfc_idrefl.
Defined.

Lemma gf_sum_conv : forall f g, gfc_id (gf_sum (conv f g)) (gf_sum f * gf_sum g)%Z.
Proof.
  assert (Hc : forall f g, (gf_sum (conv f g) = gf_sum f * gf_sum g)%Z).
  { intros f. induction f as [| a f IH]; intros g; cbn [conv].
    - destruct (gfc_idsym gf_sum_nil). ring.
    - destruct (gfc_idsym (gf_sum_add (map (Z.mul a) g) (0 :: conv f g))).
      destruct (gfc_idsym (gf_sum_map_mul a g)).
      destruct (gfc_idsym (gf_sum_cons 0 (conv f g))).
      destruct (gfc_idsym (gf_sum_cons a f)).
      rewrite IH. ring. }
  intros f g. rewrite (Hc f g). apply gfc_idrefl.
Defined.

Lemma gf_sum_pow : forall f k, gfc_id (gf_sum (gf_pow f k)) (gf_sum f ^ Z.of_nat k)%Z.
Proof.
  assert (Hc : forall f k, (gf_sum (gf_pow f k) = gf_sum f ^ Z.of_nat k)%Z).
  { intros f k. induction k as [| k IH].
    - cbn [gf_pow gf_sum fold_right Z.of_nat Z.pow]. reflexivity.
    - cbn [gf_pow].
      destruct (gfc_idsym (gf_sum_conv f (gf_pow f k))).
      rewrite IH. rewrite Nat2Z.inj_succ. rewrite Z.pow_succ_r by lia. reflexivity. }
  intros f k. rewrite (Hc f k). apply gfc_idrefl.
Defined.

(* ------------------------------------------------------------------ *)
(* Nonnegativity as a decidable boolean scan: [tbl_all_leb] folds the   *)
(* per-entry test (0 <= a) over the table, and the statement carrier is *)
(* the boolean identity [tbl_nonneg f := gfc_id (tbl_all_leb f) true],  *)
(* the same decidable-carrier shape as the order facts above.           *)
(* ------------------------------------------------------------------ *)

Fixpoint tbl_all_leb (f : tbl) : bool :=
  match f with
  | [] => true
  | a :: f' => andb (Z.leb 0 a) (tbl_all_leb f')
  end.

Definition tbl_nonneg (f : tbl) : Set := gfc_id (tbl_all_leb f) true.

Lemma add_tbl_nonneg : forall f g,
  tbl_nonneg f -> tbl_nonneg g -> tbl_nonneg (add_tbl f g).
Proof.
  assert (Hgen : forall u v, tbl_nonneg u -> tbl_nonneg v -> tbl_all_leb (add_tbl u v) = true).
  { intros u. induction u as [| a u IH]; intros v Hu Hv.
    - cbn [add_tbl].
      destruct (tbl_all_leb v) eqn:E.
      + reflexivity.
      + unfold tbl_nonneg in Hv. rewrite E in Hv. inversion Hv.
    - destruct v as [| b v]; cbn [add_tbl].
      + destruct (tbl_all_leb (a :: u)) eqn:E.
        * reflexivity.
        * unfold tbl_nonneg in Hu. rewrite E in Hu. inversion Hu.
      + cbn [tbl_all_leb].
        assert (Hb1 : tbl_all_leb (a :: u) = true).
        { destruct (tbl_all_leb (a :: u)) eqn:E. reflexivity.
          unfold tbl_nonneg in Hu. rewrite E in Hu. inversion Hu. }
        cbn [tbl_all_leb] in Hb1.
        assert (E1 : (Z.leb 0 a)%Z = true).
        { destruct (Z.leb 0 a) eqn:Ex. reflexivity.
          cbn [andb] in Hb1. discriminate Hb1. }
        rewrite E1 in Hb1. cbn [andb] in Hb1.
        assert (Hb2 : tbl_all_leb (b :: v) = true).
        { destruct (tbl_all_leb (b :: v)) eqn:E. reflexivity.
          unfold tbl_nonneg in Hv. rewrite E in Hv. inversion Hv. }
        cbn [tbl_all_leb] in Hb2.
        assert (E3 : (Z.leb 0 b)%Z = true).
        { destruct (Z.leb 0 b) eqn:Ex. reflexivity.
          cbn [andb] in Hb2. discriminate Hb2. }
        rewrite E3 in Hb2. cbn [andb] in Hb2.
        assert (Hx : (Z.leb 0 (a + b))%Z = true).
        { apply (proj2 (Z.leb_le 0 (a + b))).
          assert (Hpa : (0 <= a)%Z) by (apply (proj1 (Z.leb_le 0 a)); exact E1).
          assert (Hpb : (0 <= b)%Z) by (apply (proj1 (Z.leb_le 0 b)); exact E3).
          lia. }
        assert (Hy : tbl_all_leb (add_tbl u v) = true).
        { assert (HuC : tbl_nonneg u) by (unfold tbl_nonneg; rewrite Hb1; apply gfc_idrefl).
          assert (HvC : tbl_nonneg v) by (unfold tbl_nonneg; rewrite Hb2; apply gfc_idrefl).
          exact (IH v HuC HvC). }
        rewrite Hx, Hy. reflexivity. }
  intros f g Hf Hg.
  pose proof (Hgen f g Hf Hg) as Hdone.
  unfold tbl_nonneg. rewrite Hdone. apply gfc_idrefl.
Defined.

Lemma map_mul_nonneg : forall (a : Z) f,
  gfc_zle 0 a -> tbl_nonneg f -> tbl_nonneg (map (Z.mul a) f).
Proof.
  intros a f Ha Hf.
  assert (Ha0 : (0 <= a)%Z).
  { unfold gfc_zle in Ha. destruct (Z.leb 0 a) eqn:E.
    - apply (proj1 (Z.leb_le 0 a)). exact E.
    - inversion Ha. }
  assert (Hb : tbl_all_leb (map (Z.mul a) f) = true).
  { revert Hf. induction f as [| b f IH]; intros Hf.
    - cbn [map tbl_all_leb]. reflexivity.
    - cbn [map tbl_all_leb].
      assert (Hb1 : tbl_all_leb (b :: f) = true).
      { destruct (tbl_all_leb (b :: f)) eqn:E. reflexivity.
        unfold tbl_nonneg in Hf. rewrite E in Hf. inversion Hf. }
      cbn [tbl_all_leb] in Hb1.
      assert (E1 : (Z.leb 0 b)%Z = true).
      { destruct (Z.leb 0 b) eqn:Ex. reflexivity.
        cbn [andb] in Hb1. discriminate Hb1. }
      rewrite E1 in Hb1. cbn [andb] in Hb1.
      assert (Hpb : (0 <= b)%Z) by (apply (proj1 (Z.leb_le 0 b)); exact E1).
      assert (Hx : (Z.leb 0 (a * b))%Z = true).
      { apply (proj2 (Z.leb_le 0 (a * b))). nia. }
      assert (Hy : tbl_all_leb (map (Z.mul a) f) = true).
      { assert (Hf2 : tbl_nonneg f) by (unfold tbl_nonneg; rewrite Hb1; apply gfc_idrefl).
        exact (IH Hf2). }
      rewrite Hx, Hy. reflexivity. }
  unfold tbl_nonneg. rewrite Hb. apply gfc_idrefl.
Defined.

Lemma conv_nonneg : forall f g,
  tbl_nonneg f -> tbl_nonneg g -> tbl_nonneg (conv f g).
Proof.
  intros f g Hf Hg.
  assert (Hb : tbl_all_leb (conv f g) = true).
  { revert Hf. induction f as [| a f IH]; intros Hf.
    - cbn [conv tbl_all_leb]. reflexivity.
    - cbn [conv].
      assert (Hb1 : tbl_all_leb (a :: f) = true).
      { destruct (tbl_all_leb (a :: f)) eqn:E. reflexivity.
        unfold tbl_nonneg in Hf. rewrite E in Hf. inversion Hf. }
      cbn [tbl_all_leb] in Hb1.
      assert (E1 : (Z.leb 0 a)%Z = true).
      { destruct (Z.leb 0 a) eqn:Ex. reflexivity.
        cbn [andb] in Hb1. discriminate Hb1. }
      rewrite E1 in Hb1. cbn [andb] in Hb1.
      assert (Hpa : (0 <= a)%Z) by (apply (proj1 (Z.leb_le 0 a)); exact E1).
      assert (Hza : gfc_zle 0 a) by (unfold gfc_zle; rewrite E1; apply gfc_idrefl).
      assert (Hf2 : tbl_nonneg f) by (unfold tbl_nonneg; rewrite Hb1; apply gfc_idrefl).
      pose proof (map_mul_nonneg a g Hza Hg) as Hmap.
      pose proof (IH Hf2) as Hconv.
      assert (Hzero : tbl_nonneg (0 :: conv f g)).
      { unfold tbl_nonneg. cbn [tbl_all_leb].
        assert (H0 : (0 <=? 0)%Z = true) by reflexivity.
        rewrite H0, Hconv. cbn [andb]. apply gfc_idrefl. }
      pose proof (add_tbl_nonneg (map (Z.mul a) g) (0 :: conv f g) Hmap Hzero) as Hres.
      destruct (tbl_all_leb (add_tbl (map (Z.mul a) g) (0 :: conv f g))) eqn:E.
      + reflexivity.
      + unfold tbl_nonneg in Hres. rewrite E in Hres. inversion Hres. }
  unfold tbl_nonneg. rewrite Hb. apply gfc_idrefl.
Defined.

Lemma gf_pow_nonneg : forall f k, tbl_nonneg f -> tbl_nonneg (gf_pow f k).
Proof.
  intros f k Hf.
  assert (Hb : tbl_all_leb (gf_pow f k) = true).
  { induction k as [| k IH].
    - cbn [gf_pow tbl_all_leb]. reflexivity.
    - cbn [gf_pow].
      assert (HpowC : tbl_nonneg (gf_pow f k))
        by (unfold tbl_nonneg; rewrite IH; apply gfc_idrefl).
      pose proof (conv_nonneg f (gf_pow f k) Hf HpowC) as Hc.
      destruct (tbl_all_leb (conv f (gf_pow f k))) eqn:E.
      + reflexivity.
      + unfold tbl_nonneg in Hc. rewrite E in Hc. inversion Hc. }
  unfold tbl_nonneg. rewrite Hb. apply gfc_idrefl.
Defined.

Lemma nth_nonneg : forall f i,
  tbl_nonneg f -> gfc_natlt i (length f) -> gfc_zle 0 (nth i f 0).
Proof.
  intros f i Hf Hi.
  assert (Hi' : (i < length f)%nat).
  { unfold gfc_natlt in Hi. destruct (Nat.ltb i (length f)) eqn:E.
    - apply (proj1 (Nat.ltb_lt i (length f))). exact E.
    - inversion Hi. }
  assert (Hb0 : tbl_all_leb f = true).
  { destruct (tbl_all_leb f) eqn:E. reflexivity.
    unfold tbl_nonneg in Hf. rewrite E in Hf. inversion Hf. }
  assert (Hc : forall l j, tbl_all_leb l = true -> (j < length l)%nat -> (0 <= nth j l 0)%Z).
  { intros l. induction l as [| c l IH]; intros j Hl Hj.
    - destruct j as [| j']; cbn [nth]; lia.
    - destruct j as [| j']; cbn [nth length] in Hj; cbn [nth].
      + cbn [tbl_all_leb] in Hl.
        assert (E1 : (Z.leb 0 c)%Z = true).
        { destruct (Z.leb 0 c) eqn:Ex. reflexivity.
          cbn [andb] in Hl. discriminate Hl. }
        apply (proj1 (Z.leb_le 0 c)). exact E1.
      + cbn [tbl_all_leb] in Hl.
        assert (E1 : (Z.leb 0 c)%Z = true).
        { destruct (Z.leb 0 c) eqn:Ex. reflexivity.
          cbn [andb] in Hl. discriminate Hl. }
        rewrite E1 in Hl. cbn [andb] in Hl.
        exact (IH j' Hl (ltac:(lia))). }
  unfold gfc_zle. assert (Hb : (0 <=? nth i f 0)%Z = true).
  { apply (proj2 (Z.leb_le 0 (nth i f 0))). exact (Hc f i Hb0 Hi'). }
  rewrite Hb. apply gfc_idrefl.
Defined.

Lemma gf_sum_nonneg : forall f, tbl_nonneg f -> gfc_zle 0 (gf_sum f).
Proof.
  intros f Hf.
  assert (Hb0 : tbl_all_leb f = true).
  { destruct (tbl_all_leb f) eqn:E. reflexivity.
    unfold tbl_nonneg in Hf. rewrite E in Hf. inversion Hf. }
  assert (Hc : forall l, tbl_all_leb l = true -> (0 <= gf_sum l)%Z).
  { intros l. induction l as [| a l IH]; intros Hl.
    - cbn [gf_sum fold_right]. lia.
    - cbn [tbl_all_leb] in Hl.
      assert (E1 : (Z.leb 0 a)%Z = true).
      { destruct (Z.leb 0 a) eqn:Ex. reflexivity.
        cbn [andb] in Hl. discriminate Hl. }
      rewrite E1 in Hl. cbn [andb] in Hl.
      assert (Ha' : (0 <= a)%Z) by (apply (proj1 (Z.leb_le 0 a)); exact E1).
      pose proof (IH Hl) as HP.
      destruct (gfc_idsym (gf_sum_cons a l)). lia. }
  unfold gfc_zle. assert (Hb : (0 <=? gf_sum f)%Z = true).
  { apply (proj2 (Z.leb_le 0 (gf_sum f))). exact (Hc f Hb0). }
  rewrite Hb. apply gfc_idrefl.
Defined.

Lemma nth_le_sum : forall f i,
  tbl_nonneg f -> gfc_natlt i (length f) -> gfc_zle (nth i f 0) (gf_sum f).
Proof.
  intros f i Hf Hi.
  assert (Hi' : (i < length f)%nat).
  { unfold gfc_natlt in Hi. destruct (Nat.ltb i (length f)) eqn:E.
    - apply (proj1 (Nat.ltb_lt i (length f))). exact E.
    - inversion Hi. }
  assert (Hb0 : tbl_all_leb f = true).
  { destruct (tbl_all_leb f) eqn:E. reflexivity.
    unfold tbl_nonneg in Hf. rewrite E in Hf. inversion Hf. }
  assert (Hc : forall l j, tbl_all_leb l = true -> (j < length l)%nat -> (nth j l 0 <= gf_sum l)%Z).
  { intros l. induction l as [| a l IH]; intros j Hl Hj.
    - destruct j as [| j']; cbn [nth gf_sum fold_right]; lia.
    - destruct j as [| j']; cbn [nth length] in Hj; cbn [nth].
      + cbn [tbl_all_leb] in Hl.
        assert (E1 : (Z.leb 0 a)%Z = true).
        { destruct (Z.leb 0 a) eqn:Ex. reflexivity.
          cbn [andb] in Hl. discriminate Hl. }
        rewrite E1 in Hl. cbn [andb] in Hl.
        assert (Ha' : (0 <= a)%Z) by (apply (proj1 (Z.leb_le 0 a)); exact E1).
        assert (HtlC : tbl_nonneg l) by (unfold tbl_nonneg; rewrite Hl; apply gfc_idrefl).
        pose proof (gf_sum_nonneg l HtlC) as HP.
        assert (HP' : (0 <= gf_sum l)%Z).
        { unfold gfc_zle in HP. destruct (Z.leb 0 (gf_sum l)) eqn:Ex.
          - apply (proj1 (Z.leb_le 0 (gf_sum l))). exact Ex.
          - inversion HP. }
        destruct (gfc_idsym (gf_sum_cons a l)). lia.
      + cbn [tbl_all_leb] in Hl.
        assert (E1 : (Z.leb 0 a)%Z = true).
        { destruct (Z.leb 0 a) eqn:Ex. reflexivity.
          cbn [andb] in Hl. discriminate Hl. }
        rewrite E1 in Hl. cbn [andb] in Hl.
        assert (Ha' : (0 <= a)%Z) by (apply (proj1 (Z.leb_le 0 a)); exact E1).
        assert (HtlC : tbl_nonneg l) by (unfold tbl_nonneg; rewrite Hl; apply gfc_idrefl).
        pose proof (gf_sum_nonneg l HtlC) as HP.
        assert (HP' : (0 <= gf_sum l)%Z).
        { unfold gfc_zle in HP. destruct (Z.leb 0 (gf_sum l)) eqn:Ex.
          - apply (proj1 (Z.leb_le 0 (gf_sum l))). exact Ex.
          - inversion HP. }
        pose proof (IH j' Hl (ltac:(lia))) as H0.
        destruct (gfc_idsym (gf_sum_cons a l)). lia. }
  unfold gfc_zle. assert (Hb : (nth i f 0 <=? gf_sum f)%Z = true).
  { apply (proj2 (Z.leb_le (nth i f 0) (gf_sum f))). exact (Hc f i Hb0 Hi'). }
  rewrite Hb. apply gfc_idrefl.
Defined.

(* ------------------------------------------------------------------ *)
(* Lengths                                                              *)
(* ------------------------------------------------------------------ *)

Lemma length_add_tbl : forall f g,
  gfc_id (length (add_tbl f g)) (Nat.max (length f) (length g)).
Proof.
  assert (Hc : forall f g, (length (add_tbl f g) = Nat.max (length f) (length g))%nat).
  { intros f. induction f as [| a f IH]; intros g.
    - destruct g; reflexivity.
    - destruct g as [| b g]; cbn [add_tbl length].
      + rewrite Nat.max_0_r. lia.
      + rewrite IH. lia. }
  intros f g. rewrite (Hc f g). apply gfc_idrefl.
Defined.

(* ------------------------------------------------------------------ *)
(* Known exclusions (future work; the draft statements are preserved in *)
(* the development working notes):                                      *)
(*   1. length_conv_nonnil: length (conv f g) = length f + length g - 1 *)
(*      for nonempty positive tables (the general statement needs a     *)
(*      case analysis on the tail emptiness that is not yet settled).   *)
(*   2. gf_pow_length: length (gf_pow f k) = k * (length f - 1) + 1.    *)
(*   3. ptable_length: length (ptable n) = 10 * n + 1.                  *)
(*   4. poleZ_dom: |poleZ n k| <= 2^(17n) * 10^(6n+1) for k <= 3n,      *)
(*      together with its supporting lemmas (absum_le, pole_sumR_abs,   *)
(*      kpart_rescale, kpart_ksumF, the partial sums Fsum and Gsum, and *)
(*      the kernel identity chain).                                     *)
(* Items 1-3 follow by list-length inductions over the fold             *)
(* definitions; item 4 assembles them into the domination estimate via  *)
(* the kernel partial-sum identity.  No axioms, admissions or           *)
(* solver-closed main statements are introduced by this file.           *)
(* ------------------------------------------------------------------ *)
