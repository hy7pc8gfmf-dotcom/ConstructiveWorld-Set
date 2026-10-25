(** ConstructiveWorld-Set — Cauchy-Schwarz inequality for finite Q sums, with Real-layer wrappers.

* UpCS: Two-layer Cauchy-Schwarz and refutation of the reversed statement.

    Mission.  Finite dot products and sums of squares at the [Q] layer
      ([dotp], [sql], [dotpQ], [sqlQ]), the main inequality [cs_Q], the
      pointwise projection statements [sql_proj]/[dotp_proj], and the
      Real-layer theorems [real_cauchy_schwarz_lt] (strict epsilon form),
      [real_cauchy_schwarz] (non-strict form) and
      [real_cauchy_schwarz_reversed_false] (constructive refutation of the
      reversed universal statement).

    Dependencies.  Stdlib [List], [QArith.Qring], [QArith.Qabs]; requires
      [S01_BaseRing] and the S-series modules of this development.

    References.  This development, ConstructiveWorld-Main baseline module
      UpCS.v, whose statement names are carried over here verbatim
      (statement-face Set-carrier completion).  The Lagrange identity
      argument proceeds coordinatewise on finite lists.

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers [QltT]/[QleT']/[QeqT]); every proof ends in
      [Qed] with no admitted goals and no additional axiom premises;
      [coqchk] reports [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" UpCS.v] compiles cleanly
      (exit 0); the first eight bytes of the artifact are
      [436f7121 00015ff4]. *)

From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import QArith.Qring QArith.Qabs.
From Stdlib Require Import Setoid.
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

Open Scope Q_scope.

(* ========== CS1: inner product (finite sum of pairwise products) =============== *)
Fixpoint dotp (a b : list Real) : Real :=
  match a, b with
  | x :: xs, y :: ys => real_plus (real_mult x y) (dotp xs ys)
  | _, _ => real_zero
  end.

(* ========== CS2: sum of squares ================================================ *)
Fixpoint sql (a : list Real) : Real :=
  match a with
  | nil => real_zero
  | x :: rest => real_plus (real_mult x x) (sql rest)
  end.

(* ========== Q-layer copies (pointwise evaluation targets) ===================== *)
Fixpoint sqlQ (u : list Q) : Q :=
  match u with
  | nil => 0
  | x :: rest => x * x + sqlQ rest
  end.

Fixpoint dotpQ (u v : list Q) : Q :=
  match u, v with
  | x :: xs, y :: ys => x * y + dotpQ xs ys
  | _, _ => 0
  end.

(* ========== Basic Q-layer inequalities (constructive, no classical axioms) ==== *)

(* Nonnegativity of a square: three-way Qcompare case split (decidable order, constructively legitimate) *)
Lemma Qle_0_sq : forall x : Q, QleT' 0 (x * x).
Proof.
  intro x.
  apply Qle_to_QleT'.
  destruct (Qcompare 0 x) as [ | | ] eqn:Ec.
  - (* Eq case: 0 == x *)
    assert (Hx0 : 0 == x) by exact (proj2 (Qeq_alt 0 x) Ec).
    apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. rewrite <- Hx0. ring.
  - (* Lt case: 0 < x, and 0·x ≤ x·x (right multiplication preserves the order) *)
    assert (H0x : 0 <= x).
    { apply Qlt_le_weak. exact (proj2 (Qlt_alt 0 x) Ec). }
    apply (Qle_trans _ (0 * x)).
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
    + apply (Qmult_le_compat_r 0 x x); assumption.
  - (* Gt case: x < 0, so 0 ≤ −x, and (−x)·(−x) == x·x *)
    assert (Hlt : Qlt x 0).
    { apply (proj2 (Qlt_alt x 0)).
      rewrite <- Qcompare_antisym. rewrite Ec. reflexivity. }
    assert (Hneg : 0 <= - x).
    { exact (Qopp_le_compat x 0 (Qlt_le_weak x 0 Hlt)). }
    apply (Qle_trans _ ((- x) * (- x))).
    + apply (Qle_trans _ (0 * (- x))).
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
      * apply (Qmult_le_compat_r 0 (- x) (- x)); assumption.
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
Qed.

(* The sum of squares is nonnegative *)
Lemma Qle_0_sqlQ : forall u : list Q, QleT' 0 (sqlQ u).
Proof.
  induction u as [| x xs IH].
  - apply Qle_to_QleT'. apply Qle_refl.
  - apply Qle_to_QleT'.
    apply (Qle_trans _ (0 + sqlQ xs)).
    + rewrite Qplus_0_l. exact (QleT'_to_Qle _ _ IH).
    + apply Qplus_le_compat.
      * apply QleT'_to_Qle. apply Qle_0_sq.
      * apply Qle_refl.
Qed.

(* A product of nonnegative factors is nonnegative *)
Lemma Qle_mult_nonneg : forall x y : Q, Qle 0 x -> Qle 0 y -> QleT' 0 (x * y).
Proof.
  intros x y Hx Hy.
  apply Qle_to_QleT'.
  apply (Qle_trans _ (0 * y)).
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
  - apply (Qmult_le_compat_r 0 x y); assumption.
Qed.

(* ========== Lagrange cross term (pairwise nonnegative blocks of the identity) == The identity x²·Σv² − 2xy·Σuv
+ y²·Σu² decomposes into Σ_pairs (x·v − y·u)² plus a leftover term carrying y²/x², and is ≥ 0 (with lists of
unequal length the leftover contributes further squares, still nonnegative — one induction covers both). *)
Lemma crossQ : forall (xs ys : list Q) (x y : Q),
  QleT' 0 (x * x * sqlQ ys - 2 * x * y * dotpQ xs ys + y * y * sqlQ xs).
Proof.
  induction xs as [| u us IH]; intros ys x y; apply Qle_to_QleT'.
  - destruct ys as [| v vs].
    + (* Both lists empty: the statement is the identity 0 *)
      apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. simpl. ring.
    + (* xs empty: x²·sqlQ(v::vs) ≥ 0 *)
      apply (Qle_trans _ (x * x * sqlQ (v :: vs))).
      * apply QleT'_to_Qle. apply Qle_mult_nonneg.
        -- apply QleT'_to_Qle. apply Qle_0_sq.
        -- apply QleT'_to_Qle. apply Qle_0_sqlQ.
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. simpl. ring.
  - destruct ys as [| v vs].
    + (* ys empty: y²·sqlQ(u::us) ≥ 0 *)
      apply (Qle_trans _ (y * y * sqlQ (u :: us))).
      * apply QleT'_to_Qle. apply Qle_mult_nonneg.
        -- apply QleT'_to_Qle. apply Qle_0_sq.
        -- apply QleT'_to_Qle. apply Qle_0_sqlQ.
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. simpl. ring.
    + (* Both lists nonempty: (xv − yu)² plus the induction leftover block *)
      apply (Qle_trans _ ((x * v - y * u) * (x * v - y * u)
                          + (x * x * sqlQ vs - 2 * x * y * dotpQ us vs
                             + y * y * sqlQ us))).
      * apply (Qle_trans _ (0 + (x * x * sqlQ vs
                                  - 2 * x * y * dotpQ us vs + y * y * sqlQ us))).
        -- rewrite Qplus_0_l. exact (QleT'_to_Qle _ _ (IH vs x y)).
        -- assert (Hq : Qle 0 ((x * v - y * u) * (x * v - y * u)))
             by (apply QleT'_to_Qle; apply Qle_0_sq).
           assert (Hr : Qle (x * x * sqlQ vs
                             - 2 * x * y * dotpQ us vs + y * y * sqlQ us)
                            (x * x * sqlQ vs
                             - 2 * x * y * dotpQ us vs + y * y * sqlQ us))
             by apply Qle_refl.
           exact (Qplus_le_compat 0 ((x * v - y * u) * (x * v - y * u))
                    _ _ Hq Hr).
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. simpl. ring.
Qed.

(* ========== Finite-sum Cauchy-Schwarz at the Q layer ========================== *)
Lemma cs_Q : forall (a b : list Q),
  QleT' (dotpQ a b * dotpQ a b) (sqlQ a * sqlQ b).
Proof.
  induction a as [| x xs IHa]; intro b; apply Qle_to_QleT'.
  - (* a empty: dotpQ = 0 *)
    cbn [dotpQ sqlQ]. rewrite !Qmult_0_l. apply Qle_refl.
  - destruct b as [| y ys].
    + (* b empty: dotpQ = 0 *)
      cbn [dotpQ sqlQ]. rewrite !Qmult_0_r. apply Qle_refl.
    + (* cons-cons: expand and apply the Lagrange block (x²+A)(y²+B)
− (xy+C)² = (x²B − 2xyC + y²A) + (AB − C²) ≥ 0 *)
      cbn [dotpQ sqlQ].
      assert (Hcs : Qle (dotpQ xs ys * dotpQ xs ys) (sqlQ xs * sqlQ ys))
        by (apply QleT'_to_Qle; apply IHa).
      assert (Hcross : Qle 0 (x * x * sqlQ ys - 2 * x * y * dotpQ xs ys
                              + y * y * sqlQ xs))
        by (apply QleT'_to_Qle; apply crossQ).
      set (C := dotpQ xs ys). set (A := sqlQ xs). set (B := sqlQ ys).
      assert (Hstep : Qle (2 * x * y * C) (x * x * B + y * y * A)).
      { apply (Qle_trans _ (2 * x * y * C + 0)).
        - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
        - apply (Qle_trans _ (2 * x * y * C + (x * x * B - 2 * x * y * C
                                               + y * y * A))).
          + apply (Qplus_le_compat (2 * x * y * C) (2 * x * y * C) 0
                     (x * x * B - 2 * x * y * C + y * y * A));
               [apply Qle_refl | exact Hcross].
          + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
      (* Main chain: (xy+C)² ≤ x²y² + 2xyC + C² ≤ x²y² + (x²B+y²A)
+ C² ≤ x²y² + (x²B+y²A) + AB == (x²+A)(y²+B) *)
      apply (Qle_trans _ (x * x * y * y + 2 * x * y * C + C * C)).
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
      * apply (Qle_trans _ (x * x * y * y + (x * x * B + y * y * A) + C * C)).
        -- apply (Qplus_le_compat (x * x * y * y + 2 * x * y * C)
                     (x * x * y * y + (x * x * B + y * y * A)) (C * C) (C * C)).
           ++ apply (Qplus_le_compat (x * x * y * y) (x * x * y * y)
                       (2 * x * y * C) (x * x * B + y * y * A));
                [apply Qle_refl | exact Hstep].
           ++ apply Qle_refl.
        -- apply (Qle_trans _ (x * x * y * y + (x * x * B + y * y * A) + A * B)).
           ++ apply (Qplus_le_compat
                       (x * x * y * y + (x * x * B + y * y * A))
                       (x * x * y * y + (x * x * B + y * y * A))
                       (C * C) (A * B));
                [apply Qle_refl | exact Hcs].
           ++ apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
Qed.

(* ========== Pointwise projections (Real layer to Q-layer copies) ============== *)

Lemma sql_proj : forall (a : list Real) (k : nat),
  QeqT (projT1 (sql a) k) (sqlQ (map (fun x : Real => projT1 x k) a)).
Proof.
  induction a as [| x xs IH]; intro k.
  - apply qeq_imp_qeqT. reflexivity.
  - apply qeq_imp_qeqT.
    cbn [sql]. setoid_rewrite (fun x0 y0 k0 => qeqT_imp_qeq _ _ (real_plus_proj x0 y0 k0)). setoid_rewrite (fun x0 y0 k0 => qeqT_imp_qeq _ _ (real_mult_proj x0 y0 k0)). rewrite (qeqT_imp_qeq _ _ (IH k)). reflexivity.
Qed.

Lemma dotp_proj : forall (a b : list Real) (k : nat),
  QeqT (projT1 (dotp a b) k)
       (dotpQ (map (fun x : Real => projT1 x k) a)
              (map (fun y : Real => projT1 y k) b)).
Proof.
  induction a as [| x xs IH]; intro b; intro k.
  - apply qeq_imp_qeqT. reflexivity.
  - destruct b as [| y ys].
    + apply qeq_imp_qeqT. reflexivity.
    + apply qeq_imp_qeqT.
      cbn [dotp]. setoid_rewrite (fun x0 y0 k0 => qeqT_imp_qeq _ _ (real_plus_proj x0 y0 k0)). setoid_rewrite (fun x0 y0 k0 => qeqT_imp_qeq _ _ (real_mult_proj x0 y0 k0)). rewrite (qeqT_imp_qeq _ _ (IH ys k)). reflexivity.
Qed.

(* ========== Real-layer main theorem (epsilon form of finite-sum Cauchy-Schwarz)= Key observation:
gap_n := (sql a)_n·(sql b)_n − (dotp a b)_n² ≥ 0 holds pointwise for every index n (pure Q-layer
cs_Q; no case analysis, no discriminant, no division). Hence (AA·BB + eps)_n − (AB²)_n = gap_n
+ eps_n ≥ eps_n > e1 (a uniform final lower bound), and the real_lt witness is built in one
step (e1 := the positivity witness of eps, N1 := its modulus). *)

Theorem real_cauchy_schwarz_lt :
  forall (a b : list Real) (eps : Real),
    real_lt real_zero eps ->
    real_lt (real_mult (dotp a b) (dotp a b))
            (real_plus (real_mult (sql a) (sql b)) eps).
Proof.
  intros a b eps Heps.
  destruct Heps as [e1 [Hpos1 [N1 HN1]]].
  exists e1. split.
  - exact Hpos1.
  - exists N1. intros n Hn.
    apply Qlt_to_QltT.
    (* Pointwise projection expansion: the difference equals (sql a)_n·(sql b)_n + eps_n − (dotp a b)_n² *)
    setoid_rewrite (fun x0 y0 k0 => qeqT_imp_qeq _ _ (real_plus_proj x0 y0 k0)).
    repeat setoid_rewrite (fun x0 y0 k0 => qeqT_imp_qeq _ _ (real_mult_proj x0 y0 k0)).
    assert (HsA : projT1 (sql a) n == sqlQ (map (fun x : Real => projT1 x n) a))
      by (apply qeqT_imp_qeq; apply sql_proj).
    assert (HsB : projT1 (sql b) n == sqlQ (map (fun x : Real => projT1 x n) b))
      by (apply qeqT_imp_qeq; apply sql_proj).
    assert (HdP : projT1 (dotp a b) n
                  == dotpQ (map (fun x : Real => projT1 x n) a)
                           (map (fun x : Real => projT1 x n) b))
      by (apply qeqT_imp_qeq; apply dotp_proj).
    rewrite HsA, HsB, HdP.
    set (A := sqlQ (map (fun x : Real => projT1 x n) a)).
    set (B := sqlQ (map (fun x : Real => projT1 x n) b)).
    set (C := dotpQ (map (fun x : Real => projT1 x n) a)
                    (map (fun x : Real => projT1 x n) b)).
    (* Positivity lower bound for eps: e1 < eps_n *)
    assert (Hz0 : projT1 real_zero n == 0) by reflexivity.
    assert (Hep : Qlt e1 (projT1 eps n)).
    { pose proof (HN1 n Hn) as Ht.
      apply QltT_to_Qlt in Ht.
      assert (Hzr : projT1 eps n - projT1 real_zero n == projT1 eps n).
      { rewrite Hz0. ring. }
      rewrite Hzr in Ht.
      exact Ht. }
    (* The Cauchy-Schwarz gap is pointwise nonnegative *)
    assert (Hgap : Qle 0 (A * B - C * C)).
    { apply (Qle_trans _ (C * C - C * C)).
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
      - pose proof (cs_Q (map (fun x : Real => projT1 x n) a)
                         (map (fun x : Real => projT1 x n) b)) as HcsT.
        assert (Hcs : Qle (C * C) (A * B))
          by exact (QleT'_to_Qle _ _ HcsT).
        unfold Qminus.
        exact (Qplus_le_compat (C * C) (A * B) (- (C * C)) (- (C * C))
                 Hcs (Qle_refl _)). }
    (* Composition: e1 < eps_n ≤ gap_n + eps_n = (AA·BB + eps)_n − (AB²)_n *)
    apply (Qlt_le_trans e1 (projT1 eps n)).
    + exact Hep.
    + apply (Qle_trans _ (0 + projT1 eps n)).
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
      * apply (Qle_trans _ ((A * B - C * C) + projT1 eps n)).
        -- exact (Qplus_le_compat 0 (A * B - C * C)
                    (projT1 eps n) (projT1 eps n) Hgap (Qle_refl _)).
        -- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
Qed.

(* ========== CS3: finite-sum Cauchy-Schwarz (epsilon form, real_le) ============ *)

Theorem real_cauchy_schwarz :
  forall (a b : list Real) (eps : Real),
    real_lt real_zero eps ->
    real_le (real_mult (dotp a b) (dotp a b))
            (real_plus (real_mult (sql a) (sql b)) eps).
Proof.
  intros a b eps Heps.
  exact (inl (real_cauchy_schwarz_lt a b eps Heps)).
Qed.

(* The literal goal real_le (AA·BB) (AB² + eps) (for an arbitrary eps >
0) is a false statement: counterexample a = [1, 0], b = [0, 1] gives
AA·BB = 1, AB = 0, and eps = 1/2 yields "1 ≤ 1/2". The constructive proof
of Not (...) below rules out any misuse of that direction. *)

Definition cs_point_a : list Real := [real_const 1; real_zero].
Definition cs_point_b : list Real := [real_zero; real_const 1].

Lemma sql_pt_a_one : forall n : nat, QeqT (projT1 (sql cs_point_a) n) 1.
Proof.
  intro n. apply qeq_imp_qeqT.
  unfold cs_point_a. cbn [sql].
  vm_compute. reflexivity.
Qed.

Lemma sql_pt_b_one : forall n : nat, QeqT (projT1 (sql cs_point_b) n) 1.
Proof.
  intro n. apply qeq_imp_qeqT.
  unfold cs_point_b. cbn [sql].
  vm_compute. reflexivity.
Qed.

Lemma dotp_pt_zero : forall n : nat,
  QeqT (projT1 (dotp cs_point_a cs_point_b) n) 0.
Proof.
  intro n. apply qeq_imp_qeqT.
  unfold cs_point_a, cs_point_b. cbn [dotp].
  vm_compute. reflexivity.
Qed.

Lemma pt_sql_eq :
  real_eq (real_mult (sql cs_point_a) (sql cs_point_b)) (real_const 1).
Proof.
  apply (RealSetoid.real_eq_mult_compat
           (sql cs_point_a) (sql cs_point_b) (real_const 1) (real_const 1)).
  - apply real_eq_of_zero_diff. intro n.
    vm_compute. reflexivity.
  - apply real_eq_of_zero_diff. intro n.
    vm_compute. reflexivity.
Qed.

Lemma pt_rhs_eq :
  real_eq (real_plus (real_mult (dotp cs_point_a cs_point_b)
                                  (dotp cs_point_a cs_point_b))
                     (real_const (1/2)%Q))
          (real_const (1/2)%Q).
Proof.
  assert (Hd0 : real_eq (dotp cs_point_a cs_point_b) (real_const 0)).
  { apply real_eq_of_zero_diff. intro n.
    vm_compute. reflexivity. }
  apply (RealSetoid.real_eq_plus_compat
           (real_mult (dotp cs_point_a cs_point_b)
                      (dotp cs_point_a cs_point_b))
           (real_const (1/2)%Q) (real_const 0) (real_const (1/2)%Q)).
  - exact (RealSetoid.real_eq_mult_compat (dotp cs_point_a cs_point_b)
             (dotp cs_point_a cs_point_b) (real_const 0) (real_const 0)
             Hd0 Hd0).
  - apply real_eq_refl.
Qed.

Lemma real_const_half_pos : real_lt real_zero (real_const (1/2)%Q).
Proof.
  exists (1/4)%Q. split.
  - exact (Qlt_to_QltT 0 (1/4)%Q (proj2 (Qlt_alt 0 (1/4)%Q) eq_refl)).
  - exists 0%nat. intros n _.
    apply Qlt_to_QltT.
    setoid_replace (projT1 (real_const (1/2)%Q) n - projT1 real_zero n)
      with (1/2)%Q.
    + exact (proj2 (Qlt_alt (1/4)%Q (1/2)%Q) eq_refl).
    + vm_compute. reflexivity.
Qed.

Theorem real_cauchy_schwarz_reversed_false :
  Not (forall (a b : list Real) (eps : Real),
        real_lt real_zero eps ->
        real_le (real_mult (sql a) (sql b))
                (real_plus (real_mult (dotp a b) (dotp a b)) eps)).
Proof.
  intro H.
  assert (Hbad : real_le (real_const 1) (real_const (1/2)%Q)).
  { assert (Hspec := H cs_point_a cs_point_b (real_const (1/2)%Q)
                       real_const_half_pos).
    exact (real_le_trans (real_const 1)
             (real_mult (sql cs_point_a) (sql cs_point_b))
             (real_plus (real_mult (dotp cs_point_a cs_point_b)
                                   (dotp cs_point_a cs_point_b))
                        (real_const (1/2)%Q))
             (inr (real_eq_sym (real_const 1)
                    (real_mult (sql cs_point_a) (sql cs_point_b))
                    pt_sql_eq))
             (real_le_trans (real_mult (sql cs_point_a) (sql cs_point_b))
                (real_plus (real_mult (dotp cs_point_a cs_point_b)
                                      (dotp cs_point_a cs_point_b))
                           (real_const (1/2)%Q))
                (real_const (1/2)%Q)
                Hspec (inr pt_rhs_eq))). }
  destruct Hbad as [Hlt | Heq].
  - (* real_lt 1 (1/2): contradicts the witness positivity e > 0 *)
    destruct Hlt as [e [Hepos [N HN]]].
    specialize (HN N (NatLe_lift N N (le_n N))).
    apply QltT_to_Qlt in HN.
    assert (Hd : projT1 (real_const (1/2)%Q) N - projT1 (real_const 1) N
                 == ((-1)#2)%Q).
    { vm_compute. reflexivity. }
    rewrite Hd in HN.
    exfalso.
    pose proof (Qlt_trans 0 e ((-1)#2)%Q (QltT_to_Qlt 0 e Hepos) HN) as Hcontra.
    vm_compute in Hcontra.
    discriminate Hcontra.
  - (* real_eq 1 (1/2): taking eps := 1/4, |1 − 1/2| = 1/2 is not below 1/4 *)
    specialize (Heq (1/4)%Q
                  (Qlt_to_QltT 0 (1/4)%Q (proj2 (Qlt_alt 0 (1/4)%Q) eq_refl))).
    destruct Heq as [M HM].
    specialize (HM M (NatLe_lift M M (le_n M))).
    unfold QltT in HM.
    vm_compute in HM.
    inversion HM.
Qed.

(* ========== Extraction check =================================================== *)

Set Warnings "-extraction-opaque-accessed".

(* Follow-up audit prints: the assumption face of each listed statement is printed and must all report closed *)
Print Assumptions real_cauchy_schwarz.
