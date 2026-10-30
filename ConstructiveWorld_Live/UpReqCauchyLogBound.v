(* Five-field pointer.  Mission. Formalization of the statement-surface properties of every theorem/lemma in this file.  Dependencies. The modules listed in the Require face below.  References. The reference table in the banner below.  Constructivity. Assumption-free statements (machine-checked).  Build. coqc -native-compiler no -q -Q . "".  ============================================================ *)
(* ====================================================================== *)
(* UpReqCauchyLogBound.v -- R2-RCL: explicit logarithmic return bound, Cauchy side *)
(* (making explicit the log bound carried by the fuel-structured bisection itself) *)
(* ====================================================================== *)
(* Established (Bishop route): rb_log_return_bound: S j0 <= 2^(log2 j0 + 2).        *)
(*   The Cauchy-side design kept the logarithmicity inside a bisection Fixpoint;      *)
(*   this file closes the gap with a self-contained cl_bsearch (Q interval [lo,hi],   *)
(*   Qle_bool-driven fuel-structured recursion: the interval halves each step, fuel   *)
(*   decreases each step, termination is structural). The main theorem                *)
(*   cl_bsearch_log_bound binds the logarithmicity back onto the search body:         *)
(*   a search with fuel = log2 j0 + 2 over [0,j0] yields the dual ledger              *)
(*   (pass+minimal, or an honest no-solution report) and S j0 <= 2^(log2 j0 + 2).     *)
(*                                                                                  *)
(* Reference table (vs R2BishopLogSel.v / UpReqMixLogA.v):                            *)
(*   mixa_bsearch         ~ cl_bsearch        (bisection core in-file, no Requires)  *)
(*   rb_bishop_search     ~ cl_bsearch_log    (fuel log2 j0 + 2 over [0,j0])         *)
(*   rb_cond/rb_cond_mono ~ cl_cond/cl_cond_mono (Qle_bool-driven + monotone)        *)
(*   rb_fuel_ge           ~ cl_fuel_ge_pos    (fuel sufficiency for 0<j0)            *)
(*   rb_log_return_bound  ~ cl_log_return_bound (same shape, verbatim parallel)     *)
(*   rb_bishop_search_ok  ~ cl_bsearch_ok   (pass+minimal ledger)                    *)
(*   (Bishop side: none)  ~ cl_bsearch_dual (new: pass+minimal or honest no-solution) *)
(*                                                                                  *)
(* Dependencies: Stdlib (PeanoNat/QArith/Qring/Lia/Extraction) plus S01_BaseRing /    *)
(*   S02_CauchyComplete (Set base Id/NatLe/QltT/QleT'/QeqT + bridges); core in-file. *)
(*                                                                                  *)
(* Red-line self-check: zero assumption-style words file-wide; no classical logic     *)
(*   introduced; all search decisions stay at the Q layer (Qle_bool); the fuel        *)
(*   recursion is structural; extraction check Obj.magic = 0 (measured).             *)
(* ====================================================================== *)

From Stdlib Require Import PeanoNat.
From Stdlib Require Import QArith.QArith.
From Stdlib Require Import QArith.Qring.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Extraction.

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.

(* nat scope first (QArith leaks Q_scope; Q-side arithmetic is type-driven or %Q-annotated) *)
Open Scope nat_scope.

(* ====================================================================== *)
(* §0 Q-layer search predicate kernel: power + Qle_bool bridge + monotonicity *)
(* ====================================================================== *)

(* Q power (nat exponent, transparently computable -- the computational kernel of the search predicate; in-file) *)
Fixpoint cl_qpow (a : Q) (k : nat) {struct k} : Q :=
  match k with
  | Datatypes.O => (1#1)
  | Datatypes.S m => a * cl_qpow a m
  end.

Lemma cl_qpow_nonneg : forall (q : Q), QleT' 0 q ->
  forall m : nat, QleT' 0 (cl_qpow q m).
Proof.
  intros q Hq0 m. induction m as [| m IH].
  - cbn [cl_qpow]. apply Qle_to_QleT'. unfold Qle. cbn. lia.
  - cbn [cl_qpow]. apply Qle_to_QleT'.
    assert (Hq0p : Qle 0 q) by (apply QleT'_to_Qle; exact Hq0).
    assert (Hs : Qle (0 * cl_qpow q m)%Q (q * cl_qpow q m)%Q)
      by (apply (Qmult_le_compat_r 0 q (cl_qpow q m) Hq0p
                  (QleT'_to_Qle _ _ IH))).
    assert (E0 : (0 * cl_qpow q m)%Q == 0%Q) by ring.
    rewrite <- E0. exact Hs.
Qed.

(* Qeq -> Qle (stdlib shape-shift, base-free name; statement face washed to QeqT/QleT') *)
Lemma cl_qeq_le : forall x y : Q, QeqT x y -> QleT' x y.
Proof.
  intros x y H. apply Qle_to_QleT'.
  pose proof (qeqT_imp_qeq x y H) as HQ. rewrite HQ. apply Qle_refl.
Qed.

(* Left-multiplication preserves order (assembled via commutation shapes around Qmult_le_compat_r, explicit args) *)
Lemma cl_qmult_le_l : forall x y z : Q,
  QleT' x y -> QleT' 0 z -> QleT' (z * x) (z * y).
Proof.
  intros x y z HT H0T.
  assert (H : Qle x y) by (apply QleT'_to_Qle; exact HT).
  assert (H0 : Qle 0 z) by (apply QleT'_to_Qle; exact H0T).
  assert (Hcomm1 : QleT' (z * x) (x * z)).
  { apply cl_qeq_le. apply qeq_imp_qeqT. apply Qmult_comm. }
  assert (Hcomm2 : QleT' (y * z) (z * y)).
  { apply cl_qeq_le. apply qeq_imp_qeqT. apply Qmult_comm. }
  exact (Qle_to_QleT' _ _
           (Qle_trans (z * x) (x * z) (z * y)
              (QleT'_to_Qle _ _ Hcomm1)
              (Qle_trans (x * z) (y * z) (z * y)
                 (Qmult_le_compat_r x y z H H0)
                 (QleT'_to_Qle _ _ Hcomm2)))).
Qed.

(* Qle_bool twin bridges (Qle_bool here = Z-level Qnum/QDen <=?; measured verdict;
   Z.leb_le / Z.leb_gt direct bridges; statement face: bool= -> Id form) *)
Lemma cl_qle_bool_true : forall x y : Q, Id (Qle_bool x y) true -> QleT' x y.
Proof. intros x y H. exact H. Qed.

Lemma cl_qle_bool_false : forall x y : Q, Id (Qle_bool x y) false -> QltT y x.
Proof.
  intros x y H. apply Qlt_to_QltT. unfold Qlt. apply Z.leb_gt.
  destruct (Qle_bool x y) eqn:E.
  - inversion H.
  - unfold Qle_bool in E. simpl in E. exact E.
Qed.

(* Forward bridge: QleT' -> Qle_bool true (statement face shares the same Id form as the QleT' body) *)
Lemma cl_qle_bool_of_qle : forall x y : Q, QleT' x y -> Id (Qle_bool x y) true.
Proof. intros x y H. exact H. Qed.

(* Power-column exponent decrease: m <= m' implies q^m' <= q^m (0<=q<=1; induction along le) *)
Lemma cl_qpow_decr : forall (q : Q), QleT' 0 q -> QleT' q 1 ->
  forall m m' : nat, NatLe m m' -> QleT' (cl_qpow q m') (cl_qpow q m).
Proof.
  intros q Hq0 Hq1 m m' Hle.
  assert (Hq0p : Qle 0 q) by (apply QleT'_to_Qle; exact Hq0).
  assert (Hq1p : Qle q 1) by (apply QleT'_to_Qle; exact Hq1).
  apply Qle_to_QleT'.
  assert (Hle' : Nat.le m m') by (apply NatLe_drop; exact Hle).
  clear Hle.
  induction Hle' as [| m' Hle'i IH].
  - apply Qle_refl.
  - cbn [cl_qpow].
    apply (Qle_trans (q * cl_qpow q m') (q * cl_qpow q m) (cl_qpow q m)).
    + exact (QleT'_to_Qle _ _
               (cl_qmult_le_l (cl_qpow q m') (cl_qpow q m) q
                  (Qle_to_QleT' _ _ IH) Hq0)).
    + apply (Qle_trans (q * cl_qpow q m) (1 * cl_qpow q m) (cl_qpow q m)).
      * exact (Qmult_le_compat_r q 1 (cl_qpow q m) Hq1p
                 (QleT'_to_Qle _ _ (cl_qpow_nonneg q Hq0 m))).
      * rewrite Qmult_1_l. apply Qle_refl.
Qed.

(* Cauchy-shaped search predicate: station j passes iff q1^j * M <= T. All decisions at the Q layer. *)
Definition cl_cond (q1 M T : Q) (j : nat) : bool :=
  Qle_bool (cl_qpow q1 j * M) T.

(* Proxy predicate monotone (passing stations upward closed) *)
Lemma cl_cond_mono : forall (q1 M T : Q),
  QleT' 0 q1 -> QleT' q1 1 -> QleT' 0 M ->
  forall j j' : nat, NatLe j j' ->
  Id (cl_cond q1 M T j) true -> Id (cl_cond q1 M T j') true.
Proof.
  intros q1 M T Hq0 Hq1 HM0 j j' Hjj Hj.
  assert (Hq0p : Qle 0 q1) by (apply QleT'_to_Qle; exact Hq0).
  assert (Hq1p : Qle q1 1) by (apply QleT'_to_Qle; exact Hq1).
  assert (HM0p : Qle 0 M) by (apply QleT'_to_Qle; exact HM0).
  assert (Hj' : Qle (cl_qpow q1 j * M) T).
  { unfold cl_cond in Hj. apply QleT'_to_Qle.
    exact (cl_qle_bool_true _ _ Hj). }
  unfold cl_cond.
  apply (cl_qle_bool_of_qle).
  apply Qle_to_QleT'.
  apply (Qle_trans (cl_qpow q1 j' * M) (cl_qpow q1 j * M) T).
  - apply (Qmult_le_compat_r (cl_qpow q1 j') (cl_qpow q1 j) M).
    + exact (QleT'_to_Qle _ _ (cl_qpow_decr q1 Hq0 Hq1 j j' Hjj)).
    + exact HM0p.
  - exact Hj'.
Qed.

(* ====================================================================== *)
(* §1 Bisection core (in-file): fuel-structured recursion + interval halving + dual-account spec *)
(* ====================================================================== *)

(* Bisection core: fuel decreases each step (structural termination), the interval halves
   each step (mid = midpoint). f=0 or lo=hi returns lo directly; otherwise tests mid:
   a pass narrows left [lo,mid], a failure narrows right [S mid,hi]. The cond predicate
   is instantiated at the Q layer (§0/§3). *)
Fixpoint cl_bsearch (cond : nat -> bool) (f lo hi : nat) {struct f} : nat :=
  match f with
  | Datatypes.O => lo
  | Datatypes.S f' =>
      if Nat.eqb lo hi then lo
      else if cond (Nat.div2 (Nat.add lo hi))
        then cl_bsearch cond f' lo (Nat.div2 (Nat.add lo hi))
        else cl_bsearch cond f' (Datatypes.S (Nat.div2 (Nat.add lo hi))) hi
  end.

(* Dual-account spec (Cauchy shape made explicit: find the minimal passing station, or
   honestly report no solution in the interval). *)
(* Fuel invariant S (hi - lo) <= 2^f: the interval halves each step; 2^f steps always suffice. *)
(* Statement face Set-form: nat<= -> NatLe, bool= -> Id, connectives -> And/Or (S01 base). *)
Theorem cl_bsearch_dual : forall (cond : nat -> bool) (f : nat),
  (forall a b : nat, NatLe a b -> Id (cond a) true -> Id (cond b) true) ->
  forall lo hi : nat,
  NatLe lo hi ->
  NatLe (Datatypes.S (Nat.sub hi lo)) (Nat.pow 2 f) ->
  Or
    (And (Id (cond hi) true)
         (And (Id (cond (cl_bsearch cond f lo hi)) true)
              (forall j : nat, NatLe lo j ->
                 Nat.lt j (cl_bsearch cond f lo hi) -> Id (cond j) false)))
    (And (Id (cond hi) false)
         (And (Id (cond (cl_bsearch cond f lo hi)) false)
              (forall j : nat, NatLe lo j -> NatLe j hi ->
                 Id (cond j) false))).
Proof.
  intros cond f Hmono.
  induction f as [| f IH]; intros lo hi Hlo Hfuel.
  - (* f = 0: the fuel bound forces hi = lo; return lo directly *)
    apply NatLe_drop in Hlo. apply NatLe_drop in Hfuel.
    simpl in Hfuel. assert (Elo : lo = hi) by lia.
    rewrite Elo. cbn [cl_bsearch].
    destruct (cond hi) eqn:Hc.
    + apply inl. split; [exact id_refl | split; [exact id_refl |]].
      intros j Hjl Hjlt. apply NatLe_drop in Hjl.
      assert (Hcon : False) by lia. exact (False_rect _ Hcon).
    + apply inr. split; [exact id_refl | split; [exact id_refl |]].
      intros j Hjl Hjh. apply NatLe_drop in Hjl. apply NatLe_drop in Hjh.
      assert (Hjeq : j = hi) by lia. rewrite Hjeq, Hc. apply id_refl.
  - apply NatLe_drop in Hlo. apply NatLe_drop in Hfuel.
    cbn [cl_bsearch]. destruct (Nat.eqb lo hi) eqn:Eeq.
    + (* lo = hi: single-point interval; the dual account branches on the truth of that point *)
      apply Nat.eqb_eq in Eeq. rewrite Eeq.
      destruct (cond hi) eqn:Hc.
      * apply inl. split; [exact id_refl | split; [exact id_refl |]].
        intros j Hjl Hjlt. apply NatLe_drop in Hjl.
        assert (Hcon : False) by lia. exact (False_rect _ Hcon).
      * apply inr. split; [exact id_refl | split; [exact id_refl |]].
        intros j Hjl Hjh. apply NatLe_drop in Hjl. apply NatLe_drop in Hjh.
        assert (Hjeq : j = hi) by lia. rewrite Hjeq, Hc. apply id_refl.
    + (* lo < hi: take the midpoint and halve *)
      apply Nat.eqb_neq in Eeq.
      assert (Hlt : Nat.lt lo hi) by lia.
      assert (Hd2 : Nat.div2 (Nat.add lo hi) = Nat.div (Nat.add lo hi) 2)
        by apply Nat.div2_div.
      rewrite Hd2.
      pose proof (Nat.mod_upper_bound (Nat.add lo hi) 2 ltac:(lia)) as Hmod.
      pose proof (Nat.div_mod (Nat.add lo hi) 2 ltac:(lia)) as Hdm.
      assert (Hmod0 : Nat.le 0 (Nat.modulo (Nat.add lo hi) 2))
        by (apply Nat.le_0_l).
      assert (Hmlo : Nat.le lo (Nat.div (Nat.add lo hi) 2)) by lia.
      assert (Hmhi : Nat.lt (Nat.div (Nat.add lo hi) 2) hi) by lia.
      rewrite Nat.pow_succ_r' in Hfuel.
      destruct (cond (Nat.div (Nat.add lo hi) 2)) eqn:Ht.
      * (* mid passes: monotonicity lifts hi; narrow left; dual account lands on the left branch *)
        assert (HtI : Id (cond (Nat.div (Nat.add lo hi) 2)) true)
          by (rewrite Ht; apply id_refl).
        assert (Hhit : Id (cond hi) true).
        { exact (Hmono (Nat.div (Nat.add lo hi) 2) hi
                   (NatLe_lift _ _ (Nat.lt_le_incl _ _ Hmhi)) HtI). }
        assert (Hf1 : Nat.le (Datatypes.S
                          (Nat.sub (Nat.div (Nat.add lo hi) 2) lo))
                        (Nat.pow 2 f)) by lia.
        destruct (IH lo (Nat.div (Nat.add lo hi) 2)
                    (NatLe_lift _ _ Hmlo) (NatLe_lift _ _ Hf1))
          as [[Htop [Hok Hmin]] | [Hf1' [Hf2' Hf3']]];
          [| rewrite Ht in Hf1'; inversion Hf1'].
        apply inl. split; [exact Hhit | split; [exact Hok | exact Hmin]].
      * (* mid fails: narrow right; below-mid all-fail ledger first *)
        assert (Hbl : forall j : nat, NatLe lo j ->
                   Nat.lt j (Datatypes.S (Nat.div (Nat.add lo hi) 2)) ->
                   Id (cond j) false).
        { intros j Hjl Hjlt. apply NatLe_drop in Hjl.
          destruct (Nat.leb j (Nat.div (Nat.add lo hi) 2)) eqn:E.
          - destruct (cond j) eqn:Htj.
            + assert (Hjd : j <= Nat.div (Nat.add lo hi) 2)
                by (apply (proj1 (Nat.leb_le j (Nat.div (Nat.add lo hi) 2)));
                    exact E).
              assert (HtjI : Id (cond j) true)
                by (rewrite Htj; apply id_refl).
              assert (Htm2 : Id (cond (Nat.div (Nat.add lo hi) 2)) true)
                by (exact (Hmono j (Nat.div (Nat.add lo hi) 2)
                             (NatLe_lift _ _ Hjd) HtjI)).
              rewrite Ht in Htm2. inversion Htm2.
            + exact id_refl.
          - assert (Hgt : Nat.div (Nat.add lo hi) 2 < j)
              by (apply (proj1 (Nat.leb_gt j (Nat.div (Nat.add lo hi) 2)));
                  exact E).
            assert (Heq : j = Nat.div (Nat.add lo hi) 2) by lia.
            rewrite Heq, Ht. apply id_refl. }
        assert (Hf2 : Nat.le (Datatypes.S (Nat.sub hi
                          (Datatypes.S (Nat.div (Nat.add lo hi) 2))))
                        (Nat.pow 2 f)) by lia.
        destruct (cond hi) eqn:Hc.
        -- (* hi passes: the right interval recurs into the left branch; below ledger splices with the IH minimal ledger *)
           destruct (IH (Datatypes.S (Nat.div (Nat.add lo hi) 2)) hi
                       ltac:(apply NatLe_lift; lia) (NatLe_lift _ _ Hf2))
             as [[Htop [Hok Hmin]] | [Hg1 [Hg2 Hg3]]];
             [| rewrite Hc in Hg1; inversion Hg1].
           apply inl. split; [exact id_refl | split; [exact Hok |]].
           intros j Hjl Hjlt.
           destruct (Nat.leb j (Nat.div (Nat.add lo hi) 2)) eqn:E.
           ++ assert (Hjd : j <= Nat.div (Nat.add lo hi) 2)
                by (apply (proj1 (Nat.leb_le j (Nat.div (Nat.add lo hi) 2)));
                    exact E).
              apply Hbl; [exact Hjl | lia].
           ++ assert (Hgt : Nat.div (Nat.add lo hi) 2 < j)
                by (apply (proj1 (Nat.leb_gt j (Nat.div (Nat.add lo hi) 2)));
                    exact E).
              apply Hmin; [apply NatLe_lift; exact Hgt | exact Hjlt].
        -- (* hi fails: honest no-solution ledger (no passing station in the interval) *)
           destruct (IH (Datatypes.S (Nat.div (Nat.add lo hi) 2)) hi
                       ltac:(apply NatLe_lift; lia) (NatLe_lift _ _ Hf2))
             as [[Hh1 [Hh2 Hh3]] | [Hh1 [Hh2 Hh3]]].
           ++ rewrite Hc in Hh1. inversion Hh1.
           ++ apply inr. split; [exact id_refl | split; [exact Hh2 |]].
              intros j Hjl Hjh.
              destruct (Nat.leb j (Nat.div (Nat.add lo hi) 2)) eqn:E.
              ** assert (Hjd : j <= Nat.div (Nat.add lo hi) 2)
                   by (apply (proj1 (Nat.leb_le j (Nat.div (Nat.add lo hi) 2)));
                       exact E).
                 apply Hbl; [exact Hjl | lia].
              ** assert (Hgt : Nat.div (Nat.add lo hi) 2 < j)
                   by (apply (proj1 (Nat.leb_gt j (Nat.div (Nat.add lo hi) 2)));
                       exact E).
                 apply Hh3; [apply NatLe_lift; exact Hgt | exact Hjh].
Qed.

(* ====================================================================== *)
(* §2 Explicit logarithmic return bound (parallels rb_fuel_ge / rb_log_return_bound) *)
(* ====================================================================== *)

(* Fuel sufficiency (0 < j0): S j0 <= 2^(log2 j0 + 2); pure nat arithmetic chain
   (isomorphic to rb_fuel_ge: log2_spec two-sided squeeze + pow_add_r flattening) *)
Lemma cl_fuel_ge_pos : forall j0 : nat,
  0 < j0 -> NatLe (Datatypes.S j0) (Nat.pow 2 (Nat.log2 j0 + 2)).
Proof.
  intros j0 Hj0. apply NatLe_lift.
  destruct (Nat.log2_spec j0 Hj0) as [Hlo Hhi].
  replace (Nat.log2 j0 + 2) with (Nat.log2 j0 + 1 + 1) by lia.
  rewrite Nat.pow_add_r. rewrite Nat.pow_add_r.
  cbn [Nat.pow].
  replace (Datatypes.S (Nat.log2 j0)) with (Nat.log2 j0 + 1) in Hhi by lia.
  rewrite Nat.pow_add_r in Hhi. cbn [Nat.pow] in Hhi.
  lia.
Qed.

(* Parallels rb_log_return_bound (signature verbatim-same shape, j0=0 included) *)
Theorem cl_log_return_bound : forall j0 : nat,
  NatLe (Datatypes.S j0) (Nat.pow 2 (Nat.log2 j0 + 2)).
Proof.
  intros j0. destruct j0 as [| j0'].
  - apply NatLe_lift. replace (Nat.log2 0 + 2) with 2 by (cbn; lia).
    cbn [Nat.pow]. lia.
  - apply (cl_fuel_ge_pos (Datatypes.S j0') (Nat.lt_0_succ j0')).
Qed.

(* Fuel-condition reshaping for the [0, j0] interval (sub 0 elimination) *)
Lemma cl_fuel_sub : forall j0 : nat,
  NatLe (Datatypes.S (Nat.sub j0 0)) (Nat.pow 2 (Nat.log2 j0 + 2)).
Proof. intros j0. rewrite Nat.sub_0_r. apply cl_log_return_bound. Qed.

(* Search over [0, j0] with fuel = log2 j0 + 2 (assembly site paralleling rb_bishop_search) *)
Definition cl_bsearch_log (cond : nat -> bool) (j0 : nat) : nat :=
  cl_bsearch cond (Nat.log2 j0 + 2) 0 j0.

(* Pass + minimal ledger (parallels rb_bishop_search_ok: when the top station is true
   the search yields the minimal passing station) *)
Theorem cl_bsearch_ok : forall (cond : nat -> bool) (j0 : nat),
  (forall a b : nat, NatLe a b -> Id (cond a) true -> Id (cond b) true) ->
  Id (cond j0) true ->
  And (Id (cond (cl_bsearch cond (Nat.log2 j0 + 2) 0 j0)) true)
      (forall j : nat, Nat.lt j (cl_bsearch cond (Nat.log2 j0 + 2) 0 j0) ->
         Id (cond j) false).
Proof.
  intros cond j0 Hmono Hhi.
  destruct (cl_bsearch_dual cond (Nat.log2 j0 + 2) Hmono 0 j0
              (NatLe_lift _ _ (Nat.le_0_l j0)) (cl_fuel_sub j0))
    as [[H1 [H2 H3]] | [H1 [H2 H3]]].
  - split; [exact H2 |].
    intros j Hj. apply (H3 j (NatLe_lift _ _ (Nat.le_0_l j)) Hj).
  - destruct (cond j0) eqn:E.
    + inversion H1.
    + inversion Hhi.
Qed.

(* ====================================================================== *)
(* Main theorem: logarithmicity registered explicitly in the search body *)
(*   First account = the dual-account spec (pass+minimal or honest no-solution, Cauchy shape); *)
(*   Second account = the explicit log return bound S j0 <= 2^(log2 j0 + 2) (parallels Bishop). *)
(* ====================================================================== *)
Theorem cl_bsearch_log_bound : forall (cond : nat -> bool) (j0 : nat),
  (forall a b : nat, NatLe a b -> Id (cond a) true -> Id (cond b) true) ->
  And
    (Or
       (And (Id (cond j0) true)
            (And (Id (cond (cl_bsearch_log cond j0)) true)
                 (forall j : nat, Nat.lt j (cl_bsearch_log cond j0) ->
                    Id (cond j) false)))
       (And (Id (cond j0) false)
            (And (Id (cond (cl_bsearch_log cond j0)) false)
                 (forall j : nat, NatLe j j0 -> Id (cond j) false))))
    (NatLe (Datatypes.S j0) (Nat.pow 2 (Nat.log2 j0 + 2))).
Proof.
  intros cond j0 Hmono. split.
  - unfold cl_bsearch_log.
    destruct (cl_bsearch_dual cond (Nat.log2 j0 + 2) Hmono 0 j0
                (NatLe_lift _ _ (Nat.le_0_l j0)) (cl_fuel_sub j0))
      as [[H1 [H2 H3]] | [H1 [H2 H3]]].
    + apply inl. split; [exact H1 | split; [exact H2 |]].
      intros j Hj. apply (H3 j (NatLe_lift _ _ (Nat.le_0_l j)) Hj).
    + apply inr. split; [exact H1 | split; [exact H2 |]].
      intros j Hj. apply (H3 j (NatLe_lift _ _ (Nat.le_0_l j)) Hj).
  - apply cl_log_return_bound.
Qed.

(* ====================================================================== *)
(* §3 Cauchy-shaped instance: assembling the Qle_bool power-slack predicate *)
(* ====================================================================== *)

Definition cl_find_qpow (q1 M T : Q) (j0 : nat) : nat :=
  cl_bsearch_log (cl_cond q1 M T) j0.

Theorem cl_find_qpow_spec : forall (q1 M T : Q) (j0 : nat),
  QleT' 0 q1 -> QleT' q1 1 -> QleT' 0 M ->
  And
    (Or
       (And (Id (cl_cond q1 M T j0) true)
            (And (Id (cl_cond q1 M T (cl_find_qpow q1 M T j0)) true)
                 (forall j : nat, Nat.lt j (cl_find_qpow q1 M T j0) ->
                    Id (cl_cond q1 M T j) false)))
       (And (Id (cl_cond q1 M T j0) false)
            (And (Id (cl_cond q1 M T (cl_find_qpow q1 M T j0)) false)
                 (forall j : nat, NatLe j j0 -> Id (cl_cond q1 M T j) false))))
    (NatLe (Datatypes.S j0) (Nat.pow 2 (Nat.log2 j0 + 2))).
Proof.
  intros q1 M T j0 Hq0 Hq1 HM0.
  exact (cl_bsearch_log_bound (cl_cond q1 M T) j0
           (cl_cond_mono q1 M T Hq0 Hq1 HM0)).
Qed.

(* ====================================================================== *)
(* Audit: extraction Obj.magic count must be 0 + statement assumption closure *)
(* ====================================================================== *)

Separate Extraction cl_qpow cl_cond cl_bsearch cl_bsearch_log cl_find_qpow.

Print Assumptions cl_bsearch_dual.
Print Assumptions cl_bsearch_ok.
Print Assumptions cl_bsearch_log_bound.
Print Assumptions cl_find_qpow_spec.
Print Assumptions cl_log_return_bound.
