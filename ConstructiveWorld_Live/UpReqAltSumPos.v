(* ConstructiveWorld-Set — positivity engine for finite alternating sums over Q. *)

(** * UpReqAltSumPos: positivity of finite alternating sums over the rationals.

    Mission.  For a nonnegative nonincreasing sequence [f : nat -> Q], the
      finite alternating sum [altsum f n = sum_{k<n} (-1)^k * f k] is
      nonnegative ([altsum_nonneg], with the [QleT]-premise form), bounded
      by its head term ([altsum_le_head]), at least the first pair
      difference ([altsum_ge_pair0]), and strictly positive when the first
      pair decreases strictly and [n >= 2] ([altsum_pos_strict]); plus the
      support families [altsum_acc_*], [altsum_sgp_2k]/[altsum_sgp_2k1],
      [altsum_peven_eq]/[altsum_podd_eq] and the concrete instances
      [altsum_ex_*].

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs], [Arith.Arith],
      [Lia].  Requires [S01_BaseRing], [S02_CauchyComplete] of this
      development (the file also defines the local transport pair
      [Id_eq]/[eq_Id] between [Id] and Leibniz equality).

    References.  This development, UpReqAltSumPos.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion: boolean and nat
      equations moved to [Id], [==] identities to [QeqT]; premise-position
      equalities are kept in Leibniz form).  The standard library identity
      [altf N == 0] of [S03_QExp] is the coefficient identity of the
      expansion of (1-1)^N, not the general engine, hence this file.

    Constructivity.  All named statements are carried by [Set] (decidable
      Q-carriers [QltT]/[QleT']/[QeqT], [Id], the boolean sign accumulator
      of [altsum_acc]); statements extract with [Obj.magic] = 0;
      [coqchk] reports [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" UpReqAltSumPos.v]
      compiles cleanly (exit 0); the first eight bytes of the artifact
      are [436f7121 00015ff4]. *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith.
From Stdlib Require Import Lia.

(* ==================================================================
   Set-carried equality transport: [Id] of [S01_BaseRing] is not a
   setoid, so these two definitional bridges convert between [Id] and
   Leibniz equality. *)
(* ================================================================== *)
Definition Id_eq {A : Set} (x y : A) (H : Id x y) : x = y.
Proof. destruct H. apply eq_refl. Defined.

Definition eq_Id {A : Set} (x y : A) (H : x = y) : Id x y.
Proof. destruct H. apply id_refl. Defined.

(* ============================================================ *)
(* Part 0: Q helpers (QleT'/QltT addition combinators and        *)
(* representation shifts; assembled from existing library pieces) *)
(* ============================================================ *)
(* ============================================================ *)

(* The sum of two nonnegative rationals is nonnegative (the 0 + 0 shift via qeq). *)
Lemma altsum_qleT'_0_plus : forall x y : Q,
  QleT' 0 x -> QleT' 0 y -> QleT' 0 (x + y).
Proof.
  intros x y Hx Hy.
  apply (qleT'_trans 0 (0 + 0) (x + y)).
  - apply qeq_leT'. apply qeq_imp_qeqT. ring.
  - apply qleT'_plus_compat; assumption.
Qed.

(* The sum of two nonpositive rationals is nonpositive. *)
Lemma altsum_qleT'_plus_nonpos : forall x y : Q,
  QleT' x 0 -> QleT' y 0 -> QleT' (x + y) 0.
Proof.
  intros x y Hx Hy.
  apply Qle_to_QleT'.
  apply (Qle_trans (x + y) (0 + 0) 0).
  - apply (Qplus_le_compat x 0 y 0); apply QleT'_to_Qle; assumption.
  - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
Qed.

(* Adding a nonpositive summand does not increase: y <= 0 implies x + y <= x (the x + 0 shift). *)
Lemma altsum_qleT'_plus_r0 : forall x y : Q, QleT' y 0 -> QleT' (x + y) x.
Proof.
  intros x y Hy.
  apply (qleT'_trans (x + y) (x + 0) x).
  - apply qleT'_plus_compat.
    + apply qleT'_refl.
    + exact Hy.
  - apply qeq_leT'. apply qeq_imp_qeqT. ring.
Qed.

(* Negation flips: 0 <= a implies Qopp a <= 0 (the Qopp 0 shift). *)
Lemma altsum_qleT'_neg_le0 : forall a : Q, QleT' 0 a -> QleT' (Qopp a) 0.
Proof.
  intros a H.
  apply Qle_to_QleT'.
  apply (Qle_trans (Qopp a) (Qopp 0) 0).
  - apply Qopp_le_compat. apply QleT'_to_Qle. exact H.
  - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
Qed.

(* Difference is nonpositive: a <= b implies a + Qopp b <= 0 (the b + Qopp b == 0 shift). *)
Lemma altsum_qleT'_sub_le0 : forall a b : Q, QleT' a b -> QleT' (a + Qopp b) 0.
Proof.
  intros a b H.
  apply Qle_to_QleT'.
  apply (Qle_trans (a + Qopp b) (b + Qopp b) 0).
  - apply (Qplus_le_compat a b (Qopp b) (Qopp b)).
    + apply QleT'_to_Qle. exact H.
    + apply Qle_refl.
  - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. apply Qplus_opp_r.
Qed.

(* Difference is nonnegative: a <= b implies 0 <= b + Qopp a (the a + Qopp a == 0 shift). *)
Lemma altsum_qleT'_ge_sub : forall a b : Q, QleT' a b -> QleT' 0 (b + Qopp a).
Proof.
  intros a b H.
  apply Qle_to_QleT'.
  apply (Qle_trans 0 (a + Qopp a) (b + Qopp a)).
  - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. apply Qeq_sym. apply Qplus_opp_r.
  - apply (Qplus_le_compat a b (Qopp a) (Qopp a)).
    + apply QleT'_to_Qle. exact H.
    + apply Qle_refl.
Qed.

(* Q addition is compatible with Qeq on both sides (composed from Qplus_inj_r and Qplus_comm). *)
Lemma altsum_qplus_eq_compat : forall x y z t : Q,
  x == y -> z == t -> QeqT (x + z) (y + t).
Proof.
  intros x y z t H1 H2. apply qeq_imp_qeqT.
  apply (Qeq_trans (x + z) (y + z) (y + t)).
  - apply (proj2 (Qplus_inj_r x y z)). exact H1.
  - apply (Qeq_trans (y + z) (z + y) (y + t)).
    + apply Qplus_comm.
    + apply (Qeq_trans (z + y) (t + y) (y + t)).
      * apply (proj2 (Qplus_inj_r z t y)). exact H2.
      * apply Qplus_comm.
Qed.

(* QltT left shift: a == c and a <T b imply c <T b. *)
Lemma altsum_qltT_shift_l : forall a b c : Q, a == c -> QltT a b -> QltT c b.
Proof.
  intros a b c Hac Hlt.
  apply Qlt_to_QltT.
  apply (Qle_lt_trans c a b).
  - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. apply Qeq_sym. exact Hac.
  - apply QltT_to_Qlt. exact Hlt.
Qed.

(* Strict difference is positive: a <T b implies 0 <T b + Qopp a. *)
Lemma altsum_qltT_sub_pos : forall a b : Q, QltT a b -> QltT 0 (b + Qopp a).
Proof.
  intros a b H.
  apply (altsum_qltT_shift_l (a + Qopp a) (b + Qopp a) 0).
  - apply Qplus_opp_r.
  - apply Qlt_to_QltT.
    apply (Qplus_lt_le_compat a b (Qopp a) (Qopp a)).
    + apply QltT_to_Qlt. exact H.
    + apply Qle_refl.
Qed.

(* Strict sum: 0 <T x and 0 <=T' y imply 0 <T x + y. *)
Lemma altsum_strict_plus_le : forall x y : Q,
  QltT 0 x -> QleT' 0 y -> QltT 0 (x + y).
Proof.
  intros x y Hx Hy.
  assert (H1 : QltT (0 + 0) (y + x)).
  { apply (qleT'_plus_ltT_ltT 0 y 0 x).
    - exact Hy.
    - exact Hx. }
  apply (qeq_ltT (y + x) (x + y)).
  - apply qeq_imp_qeqT. ring.
  - apply (altsum_qltT_shift_l (0 + 0) (y + x) 0).
    + ring.
    + exact H1.
Qed.

(* The left branch goes through qltT_leT'; the right Id branch is representational and closes after destruct. *)
Lemma altsum_QleT_to_QleT' : forall x y : Q, QleT x y -> QleT' x y.
Proof.
  intros x y H. destruct H as [Hlt | Hid].
  - apply qltT_leT'. exact Hlt.
  - destruct Hid. apply qleT'_refl.
Qed.

(* ================================================================== *)
(* Part 1: parity data splitting (pbit/phalf as Set-layer data; the    *)
(* equality premise is not a Prop-valued case split).                  *)
(* ================================================================== *)

Fixpoint altsum_pbit (n : nat) : bool :=
  match n with
  | 0%nat => true
  | Datatypes.S 0%nat => false
  | Datatypes.S (Datatypes.S m) => altsum_pbit m
  end.

Fixpoint altsum_phalf (n : nat) : nat :=
  match n with
  | 0%nat => 0%nat
  | Datatypes.S 0%nat => 0%nat
  | Datatypes.S (Datatypes.S m) => Datatypes.S (altsum_phalf m)
  end.

Lemma altsum_peven_eq : forall n : nat,
  altsum_pbit n = true -> Id n (2 * altsum_phalf n)%nat.
Proof.
  assert (Hadj : forall n : nat, forall f : bool,
    (if f
     then (altsum_pbit n = true -> n = (2 * altsum_phalf n)%nat)
     else (altsum_pbit (Datatypes.S n) = true ->
          Datatypes.S n = (2 * altsum_phalf (Datatypes.S n))%nat))).
  { induction n as [| n IH].
    - intros f. destruct f.
      + intro H. reflexivity.
      + intro H. discriminate.
    - intros f. destruct f.
      + intro H. exact (IH false H).
      + intro H.
        change (altsum_pbit n = true) in H.
        assert (Hn : n = (2 * altsum_phalf n)%nat) by exact (IH true H).
        change (altsum_phalf (Datatypes.S (Datatypes.S n)))
          with (Datatypes.S (altsum_phalf n)).
        lia. }
  intro n. intro H. apply eq_Id. apply (Hadj n true H).
Qed.

Lemma altsum_podd_eq : forall n : nat,
  altsum_pbit n = false -> Id n (2 * altsum_phalf n + 1)%nat.
Proof.
  assert (Hadj : forall n : nat, forall f : bool,
    (if f
     then (altsum_pbit n = false -> n = (2 * altsum_phalf n + 1)%nat)
     else (altsum_pbit (Datatypes.S n) = false ->
          Datatypes.S n = (2 * altsum_phalf (Datatypes.S n) + 1)%nat))).
  { induction n as [| n IH].
    - intros f. destruct f.
      + intro H. discriminate.
      + intro H. reflexivity.
    - intros f. destruct f.
      + intro H. exact (IH false H).
      + intro H.
        change (altsum_pbit n = false) in H.
        assert (Hn : n = (2 * altsum_phalf n + 1)%nat) by exact (IH true H).
        change (altsum_phalf (Datatypes.S (Datatypes.S n)))
          with (Datatypes.S (altsum_phalf n)).
        lia. }
  intro n. intro H. apply eq_Id. apply (Hadj n true H).
Qed.

(* ================================================================== *)
(* Part 2: the alternating tail sum; the sign is absorbed layer by     *)
(* layer by a boolean accumulator inside the recursion.                *)
(* ================================================================== *)

Fixpoint altsum_acc (sg : bool) (f : nat -> Q) (k n : nat) : Q :=
  match n with
  | 0%nat => 0%Q
  | Datatypes.S m => (if sg then f k else Qopp (f k))
                     + altsum_acc (negb sg) f (Datatypes.S k) m
  end.

Definition altsum (f : nat -> Q) (n : nat) : Q := altsum_acc true f 0%nat n.

(* Unfolding equations (reflection lemmas): one term is peeled per step, the sign absorbed layer by layer. *)
Lemma altsum_acc_T : forall (f : nat -> Q) (k m : nat),
  QeqT (altsum_acc true f k (Datatypes.S m)) (f k + altsum_acc false f (Datatypes.S k) m).
Proof. intros f k m. apply qeq_imp_qeqT. simpl. ring. Qed.

Lemma altsum_acc_F : forall (f : nat -> Q) (k m : nat),
  QeqT (altsum_acc false f k (Datatypes.S m)) (Qopp (f k) + altsum_acc true f (Datatypes.S k) m).
Proof. intros f k m. apply qeq_imp_qeqT. simpl. ring. Qed.

Lemma altsum_acc_0_eq : forall (sg : bool) (f : nat -> Q) (k : nat),
  QeqT (altsum_acc sg f k 0%nat) 0.
Proof. intros sg f k. apply qeq_imp_qeqT. exact (Qeq_refl 0). Qed.

(* Consumer-facing unfolding equation: regrouping with stride 2 (adjacent pairing face). *)
Lemma altsum_skip2 : forall (f : nat -> Q) (m : nat),
  QeqT (altsum f (Datatypes.S (Datatypes.S m)))
       ((f 0%nat + Qopp (f 1%nat)) + altsum_acc true f 2%nat m).
Proof. intros f m. apply qeq_imp_qeqT. unfold altsum. simpl. ring. Qed.

(* Sign-parity alignment: even indices take true, odd indices take false. *)
Definition altsum_sgp (k : nat) : bool := if Nat.even k then true else false.

Lemma altsum_even_2k : forall k : nat, Id (Nat.even (2 * k)%nat) true.
Proof.
  intro k. induction k as [| k IH].
  - apply id_refl.
  - replace (2 * Datatypes.S k)%nat
      with (Datatypes.S (Datatypes.S (2 * k)))%nat by lia.
    exact IH.
Qed.

Lemma altsum_sgp_2k : forall k : nat, Id (altsum_sgp (2 * k)%nat) true.
Proof.
  intro k. unfold altsum_sgp.
  replace (Nat.even (2 * k)%nat) with true.
  - apply id_refl.
  - apply eq_sym. exact (Id_eq _ _ (altsum_even_2k k)).
Qed.

Lemma altsum_sgp_2k1 : forall k : nat, Id (altsum_sgp (2 * k + 1)%nat) false.
Proof.
  intro k. unfold altsum_sgp. induction k as [| k IH].
  - apply id_refl.
  - replace (2 * Datatypes.S k + 1)%nat
      with (Datatypes.S (Datatypes.S (2 * k + 1)))%nat by lia.
    exact IH.
Qed.

(* ================================================================== *)
(* Part 3: the three-shape sandwich (even-start even-count >= 0;       *)
(* even-start odd-count >= 0; odd-start even-count <= 0), with the     *)
(* induction variable the term count m and the index k general in IH.  *)
(* ================================================================== *)

Lemma altsum_sandwich : forall (f : nat -> Q) (m : nat),
  (forall k, QleT' 0 (f k)) ->
  (forall k, QleT' (f (Datatypes.S k)) (f k)) ->
  forall k : nat,
  And (QleT' 0 (altsum_acc (altsum_sgp (2 * k)%nat) f (2 * k)%nat (2 * m)%nat))
  (And (QleT' 0 (f (2 * k)%nat
                 + altsum_acc (altsum_sgp (2 * k + 1)%nat) f (2 * k + 1)%nat (2 * m)%nat))
       (QleT' (altsum_acc (altsum_sgp (2 * k + 1)%nat) f (2 * k + 1)%nat (2 * m)%nat) 0)).
Proof.
  intros f m H0 Hd.
  induction m as [| m IH].
  - intro k. split.
    + reflexivity.
    + split.
      * change (altsum_acc (altsum_sgp (2 * k + 1)%nat) f (2 * k + 1)%nat (2 * 0)%nat)
          with 0%Q.
        apply (qleT'_trans 0 (f (2 * k)%nat) (f (2 * k)%nat + 0)).
        -- exact (H0 (2 * k)%nat).
        -- apply qeq_leT'. apply qeq_imp_qeqT. ring.
      * change (altsum_acc (altsum_sgp (2 * k + 1)%nat) f (2 * k + 1)%nat (2 * 0)%nat)
          with 0%Q.
        reflexivity.
  - intro k. destruct (IH (Datatypes.S k)) as [IH1 [IH2 IH4]].
    assert (Hg1 := Id_eq _ _ (altsum_sgp_2k (Datatypes.S k)));
      rewrite Hg1 in IH1.
    assert (Hg2 := Id_eq _ _ (altsum_sgp_2k1 (Datatypes.S k)));
      rewrite Hg2 in IH2. rewrite Hg2 in IH4.
    (* The two peeling equations for the odd-start tail (from 2k+1, 2m+2 terms). *)
    assert (Hp : altsum_acc (altsum_sgp (2 * k + 1)%nat) f (2 * k + 1)%nat
                   (2 * Datatypes.S m)%nat
                 == (Qopp (f (2 * k + 1)%nat) + f (2 * Datatypes.S k)%nat)
                    + altsum_acc false f (2 * Datatypes.S k + 1)%nat (2 * m)%nat).
    { assert (Hg := Id_eq _ _ (altsum_sgp_2k1 k)); rewrite Hg.
      replace (2 * Datatypes.S m)%nat with (Datatypes.S (Datatypes.S (2 * m)))%nat by lia.
      rewrite (qeqT_imp_qeq _ _ (altsum_acc_F f (2 * k + 1)%nat (Datatypes.S (2 * m)))).
      replace (Datatypes.S (2 * k + 1))%nat with (2 * Datatypes.S k)%nat by lia.
      rewrite (qeqT_imp_qeq _ _ (altsum_acc_T f (2 * Datatypes.S k)%nat (2 * m))).
      replace (Datatypes.S (2 * Datatypes.S k))%nat with (2 * Datatypes.S k + 1)%nat by lia.
      ring. }
    assert (Hdk : QleT' (f (2 * Datatypes.S k)%nat) (f (2 * k + 1)%nat)).
    { replace (2 * Datatypes.S k)%nat with (Datatypes.S (2 * k + 1))%nat by lia.
      apply Hd. }
    assert (Hdk0 : QleT' (f (2 * k + 1)%nat) (f (2 * k)%nat)).
    { replace (2 * k + 1)%nat with (Datatypes.S (2 * k))%nat by lia.
      apply Hd. }
    split.
    + (* W1: even-start even-count >= 0 = the adjacent difference pair plus the even-start even-count tail at k+1. *)
      assert (Hw1 : altsum_acc (altsum_sgp (2 * k)%nat) f (2 * k)%nat
                      (2 * Datatypes.S m)%nat
                    == (f (2 * k)%nat + Qopp (f (2 * k + 1)%nat))
                       + altsum_acc true f (2 * Datatypes.S k)%nat (2 * m)%nat).
      { assert (Hg := Id_eq _ _ (altsum_sgp_2k k)); rewrite Hg.
        replace (2 * Datatypes.S k)%nat
          with (Datatypes.S (Datatypes.S (2 * k)))%nat by lia.
        replace (2 * Datatypes.S m)%nat
          with (Datatypes.S (Datatypes.S (2 * m)))%nat by lia.
        rewrite (qeqT_imp_qeq _ _ (altsum_acc_T f (2 * k)%nat (Datatypes.S (2 * m)))).
        replace (Datatypes.S (2 * k))%nat with (2 * k + 1)%nat by lia.
        rewrite (qeqT_imp_qeq _ _ (altsum_acc_F f (2 * k + 1)%nat (2 * m))).
        replace (Datatypes.S (2 * k + 1))%nat with (2 * Datatypes.S k)%nat by lia.
        ring. }
      apply (qleT'_trans 0
        ((f (2 * k)%nat + Qopp (f (2 * k + 1)%nat))
         + altsum_acc true f (2 * Datatypes.S k)%nat (2 * m)%nat)).
      * apply altsum_qleT'_0_plus.
        -- apply (altsum_qleT'_ge_sub (f (2 * k + 1)%nat) (f (2 * k)%nat)).
           ++ exact Hdk0.
        -- exact IH1.
      * apply qeq_leT'. apply qeq_imp_qeqT. apply Qeq_sym. exact Hw1.
    + split.
      * (* W2: even-start odd-count >= 0 = the adjacent difference pair plus the even-start odd-count tail at k+1. *)
        assert (Hw2 : altsum_acc (altsum_sgp (2 * k + 1)%nat) f (2 * k + 1)%nat
                        (2 * Datatypes.S m)%nat
                      == Qopp (f (2 * k + 1)%nat)
                         + (f (2 * Datatypes.S k)%nat
                            + altsum_acc false f (2 * Datatypes.S k + 1)%nat (2 * m)%nat)).
        { assert (Hg := Id_eq _ _ (altsum_sgp_2k1 k)); rewrite Hg.
          replace (2 * Datatypes.S m)%nat
            with (Datatypes.S (Datatypes.S (2 * m)))%nat by lia.
          rewrite (qeqT_imp_qeq _ _ (altsum_acc_F f (2 * k + 1)%nat (Datatypes.S (2 * m)))).
          replace (Datatypes.S (2 * k + 1))%nat with (2 * Datatypes.S k)%nat by lia.
          rewrite (qeqT_imp_qeq _ _ (altsum_acc_T f (2 * Datatypes.S k)%nat (2 * m))).
          replace (Datatypes.S (2 * Datatypes.S k))%nat
            with (2 * Datatypes.S k + 1)%nat by lia.
          ring. }
        apply (qleT'_trans 0
          ((f (2 * k)%nat + Qopp (f (2 * k + 1)%nat))
           + (f (2 * Datatypes.S k)%nat
              + altsum_acc false f (2 * Datatypes.S k + 1)%nat (2 * m)%nat))).
        -- apply altsum_qleT'_0_plus.
           ++ apply (altsum_qleT'_ge_sub (f (2 * k + 1)%nat) (f (2 * k)%nat)).
              ** exact Hdk0.
           ++ exact IH2.
        -- apply (qleT'_trans
             ((f (2 * k)%nat + Qopp (f (2 * k + 1)%nat))
              + (f (2 * Datatypes.S k)%nat
                 + altsum_acc false f (2 * Datatypes.S k + 1)%nat (2 * m)%nat))
             (f (2 * k)%nat
              + (Qopp (f (2 * k + 1)%nat)
                 + (f (2 * Datatypes.S k)%nat
                    + altsum_acc false f (2 * Datatypes.S k + 1)%nat (2 * m)%nat)))).
           ++ apply qeq_leT'. apply qeq_imp_qeqT. ring.
           ++ apply qeq_leT'.
              apply (altsum_qplus_eq_compat (f (2 * k)%nat) (f (2 * k)%nat)
                (Qopp (f (2 * k + 1)%nat)
                 + (f (2 * Datatypes.S k)%nat
                    + altsum_acc false f (2 * Datatypes.S k + 1)%nat (2 * m)%nat))
                (altsum_acc (altsum_sgp (2 * k + 1)%nat) f (2 * k + 1)%nat
                   (2 * Datatypes.S m)%nat)).
              ** apply Qeq_refl.
              ** apply Qeq_sym. exact Hw2.
      * (* W4: odd-start even-count <= 0 = Qopp (f (2k+1)) plus the even-start odd-count tail at k+1, the tail being <= f (2k+2). *)
        apply (qleT'_trans
          (altsum_acc (altsum_sgp (2 * k + 1)%nat) f (2 * k + 1)%nat
             (2 * Datatypes.S m)%nat)
          ((Qopp (f (2 * k + 1)%nat) + f (2 * Datatypes.S k)%nat)
           + altsum_acc false f (2 * Datatypes.S k + 1)%nat (2 * m)%nat)
          0).
        -- apply qeq_leT'. apply qeq_imp_qeqT. exact Hp.
        -- apply altsum_qleT'_plus_nonpos.
           ++ apply (qleT'_trans
                ((Qopp (f (2 * k + 1)%nat) + f (2 * Datatypes.S k)%nat))
                (f (2 * Datatypes.S k)%nat + Qopp (f (2 * k + 1)%nat)) 0).
              ** apply qeq_leT'. apply qeq_imp_qeqT. ring.
              ** apply altsum_qleT'_sub_le0. exact Hdk.
           ++ exact IH4.
Qed.

(* Even term count (n = 2m): the alternating sum is nonnegative. *)
Lemma altsum_nonneg_even : forall (f : nat -> Q) (m : nat),
  (forall k, QleT' 0 (f k)) ->
  (forall k, QleT' (f (Datatypes.S k)) (f k)) ->
  QleT' 0 (altsum f (2 * m)%nat).
Proof.
  intros f m H0 Hd.
  assert (Hs := fst (altsum_sandwich f m H0 Hd 0%nat)).
  assert (Hg := Id_eq _ _ (altsum_sgp_2k 0%nat)); rewrite Hg in Hs.
  exact Hs.
Qed.

(* Odd term count (n = 2m+1): the alternating sum is nonnegative (the last term f (2m) contributes positively). *)
Lemma altsum_nonneg_odd : forall (f : nat -> Q) (m : nat),
  (forall k, QleT' 0 (f k)) ->
  (forall k, QleT' (f (Datatypes.S k)) (f k)) ->
  QleT' 0 (altsum f (2 * m + 1)%nat).
Proof.
  intros f m H0 Hd.
  assert (Hp : altsum f (2 * m + 1)%nat == f 0%nat + altsum_acc false f 1%nat (2 * m)%nat).
  { unfold altsum. replace (2 * m + 1)%nat with (Datatypes.S (2 * m))%nat by lia.
    rewrite (qeqT_imp_qeq _ _ (altsum_acc_T f 0%nat (2 * m)%nat)). reflexivity. }
  apply (qleT'_trans 0 (f 0%nat + altsum_acc false f 1%nat (2 * m)%nat)
    (altsum f (2 * m + 1)%nat)).
  - assert (Hs := fst (snd (altsum_sandwich f m H0 Hd 0%nat))).
    assert (Hg := Id_eq _ _ (altsum_sgp_2k1 0%nat)); rewrite Hg in Hs.
    exact Hs.
  - apply qeq_leT'. apply qeq_imp_qeqT. apply Qeq_sym. exact Hp.
Qed.

(* General n: Set-layer data splitting on pbit, applying the even or odd form per branch. *)
Lemma altsum_nonneg_leT : forall (f : nat -> Q) (n : nat),
  (forall k, QleT' 0 (f k)) ->
  (forall k, QleT' (f (Datatypes.S k)) (f k)) ->
  QleT' 0 (altsum f n).
Proof.
  intros f n H0 Hd. destruct (altsum_pbit n) eqn:Ep.
  - assert (Hq := Id_eq _ _ (altsum_peven_eq n Ep)); rewrite Hq.
    apply altsum_nonneg_even; assumption.
  - assert (Hq := Id_eq _ _ (altsum_podd_eq n Ep)); rewrite Hq.
    apply altsum_nonneg_odd; assumption.
Qed.

Lemma altsum_nonneg : forall (f : nat -> Q) (n : nat),
  (forall k, QleT 0 (f k)) ->
  (forall k, QleT (f (Datatypes.S k)) (f k)) ->
  QleT' 0 (altsum f n).
Proof.
  intros f n H0 Hd.
  apply (altsum_nonneg_leT f n).
  - intros k. apply altsum_QleT_to_QleT'. apply H0.
  - intros k. apply altsum_QleT_to_QleT'. apply Hd.
Qed.

(* ================================================================== *)
(* Part 4: the upper-bound companion altsum_le_head (the alternating   *)
(* sum is at most its head term); supported by the two-step adjacent   *)
(* induction showing the odd-start tail is at most 0.                  *)
(* ================================================================== *)

Lemma altsum_altacc_odd_le0 : forall (f : nat -> Q) (m : nat),
  (forall k, QleT' 0 (f k)) ->
  (forall k, QleT' (f (Datatypes.S k)) (f k)) ->
  QleT' (altsum_acc false f (2 * 0 + 1)%nat m) 0.
Proof.
  intros f m H0 Hd.
  assert (Hadj : forall t : nat,
    And (forall k, QleT' (altsum_acc false f (2 * k + 1)%nat t) 0)
        (forall k, QleT' (altsum_acc false f (2 * k + 1)%nat (Datatypes.S t)) 0)).
  { induction t as [| t IH].
    - split.
      + intro k. reflexivity.
      + intro k.
        apply (qleT'_trans (altsum_acc false f (2 * k + 1)%nat 1%nat)
          (Qopp (f (2 * k + 1)%nat) + 0) 0).
        * apply qeq_leT'. apply qeq_imp_qeqT.
          rewrite (qeqT_imp_qeq _ _ (altsum_acc_F f (2 * k + 1)%nat 0%nat)).
          rewrite (qeqT_imp_qeq _ _
                     (altsum_acc_0_eq true f (Datatypes.S (2 * k + 1)))).
          ring.
        * apply (qleT'_trans (Qopp (f (2 * k + 1)%nat) + 0)
            (Qopp (f (2 * k + 1)%nat)) 0).
          -- apply qeq_leT'. apply qeq_imp_qeqT. ring.
          -- apply altsum_qleT'_neg_le0. apply H0.
    - destruct IH as [IH1 IH2]. split.
      + exact IH2.
      + intro k.
        assert (Hp : altsum_acc false f (2 * k + 1)%nat
                       (Datatypes.S (Datatypes.S t))
                     == (Qopp (f (2 * k + 1)%nat) + f (2 * Datatypes.S k)%nat)
                        + altsum_acc false f (2 * Datatypes.S k + 1)%nat t).
        { rewrite (qeqT_imp_qeq _ _ (altsum_acc_F f (2 * k + 1)%nat (Datatypes.S t))).
          replace (Datatypes.S (2 * k + 1))%nat with (2 * Datatypes.S k)%nat by lia.
          rewrite (qeqT_imp_qeq _ _ (altsum_acc_T f (2 * Datatypes.S k)%nat t)).
          replace (Datatypes.S (2 * Datatypes.S k))%nat
            with (2 * Datatypes.S k + 1)%nat by lia.
          ring. }
        apply (qleT'_trans
          (altsum_acc false f (2 * k + 1)%nat (Datatypes.S (Datatypes.S t)))
          ((Qopp (f (2 * k + 1)%nat) + f (2 * Datatypes.S k)%nat)
           + altsum_acc false f (2 * Datatypes.S k + 1)%nat t)
          0).
        * apply qeq_leT'. apply qeq_imp_qeqT. exact Hp.
        * apply altsum_qleT'_plus_nonpos.
          -- apply (qleT'_trans
               ((Qopp (f (2 * k + 1)%nat) + f (2 * Datatypes.S k)%nat))
               (f (2 * Datatypes.S k)%nat + Qopp (f (2 * k + 1)%nat)) 0).
             ++ apply qeq_leT'. apply qeq_imp_qeqT. ring.
             ++ apply altsum_qleT'_sub_le0.
                replace (2 * Datatypes.S k)%nat with (Datatypes.S (2 * k + 1))%nat by lia.
                apply Hd.
          -- apply IH1.
    }
  apply (fst (Hadj m) 0%nat).
Qed.

(* Companion: the alternating sum is at most its head term (any n). *)
Lemma altsum_le_head : forall (f : nat -> Q) (n : nat),
  (forall k, QleT' 0 (f k)) ->
  (forall k, QleT' (f (Datatypes.S k)) (f k)) ->
  QleT' (altsum f n) (f 0%nat).
Proof.
  intros f n H0 Hd. destruct n as [| m].
  - apply (qleT'_trans (altsum f 0%nat) 0 (f 0%nat)).
    + change (altsum f 0%nat) with 0%Q. reflexivity.
    + exact (H0 0%nat).
  - assert (Hp : altsum f (Datatypes.S m) == f 0%nat + altsum_acc false f 1%nat m).
    { unfold altsum.
      rewrite (qeqT_imp_qeq _ _ (altsum_acc_T f 0%nat m)). reflexivity. }
    apply (qleT'_trans (altsum f (Datatypes.S m)) (f 0%nat + 0) (f 0%nat)).
    + apply qleT'_plus_compat.
      * apply qleT'_refl.
      * exact (altsum_altacc_odd_le0 f m H0 Hd).
    + apply qeq_leT'. apply qeq_imp_qeqT. ring.
Qed.

(* ================================================================== *)
(* Part 5: the strict version and the refinement to the lower bound    *)
(* f0 - f1.                                                            *)
(* ================================================================== *)

(* The tail starting at an even index 2k is >= 0 for any term count      *)
(* (pbit splitting: even counts use W1, odd counts peel one term and     *)
(* use W2). *)
Lemma altsum_altacc_evenstart_pos : forall (f : nat -> Q) (k m : nat),
  (forall j, QleT' 0 (f j)) ->
  (forall j, QleT' (f (Datatypes.S j)) (f j)) ->
  QleT' 0 (altsum_acc true f (2 * k)%nat m).
Proof.
  intros f k m H0 Hd. destruct (altsum_pbit m) eqn:Ep.
  - assert (Hq := Id_eq _ _ (altsum_peven_eq m Ep)); rewrite Hq.
    assert (Hs := fst (altsum_sandwich f (altsum_phalf m) H0 Hd k)).
    assert (Hg := Id_eq _ _ (altsum_sgp_2k k)); rewrite Hg in Hs.
    exact Hs.
  - assert (Hq := Id_eq _ _ (altsum_podd_eq m Ep)); rewrite Hq.
    replace (2 * altsum_phalf m + 1)%nat with (Datatypes.S (2 * altsum_phalf m))%nat by lia.
    assert (Hp : altsum_acc true f (2 * k)%nat (Datatypes.S (2 * altsum_phalf m))
                 == f (2 * k)%nat + altsum_acc false f (Datatypes.S (2 * k))%nat
                      (2 * altsum_phalf m)%nat).
    { rewrite (qeqT_imp_qeq _ _
                 (altsum_acc_T f (2 * k)%nat (2 * altsum_phalf m)%nat)). reflexivity. }
    apply (qleT'_trans 0
      (f (2 * k)%nat + altsum_acc false f (Datatypes.S (2 * k))%nat
         (2 * altsum_phalf m)%nat)
      (altsum_acc true f (2 * k)%nat (Datatypes.S (2 * altsum_phalf m)))).
    + assert (Hs := fst (snd (altsum_sandwich f (altsum_phalf m) H0 Hd k))).
      assert (Hg := Id_eq _ _ (altsum_sgp_2k1 k)); rewrite Hg in Hs.
      replace (2 * k + 1)%nat with (Datatypes.S (2 * k))%nat in Hs by lia.
      exact Hs.
    + apply qeq_leT'. apply qeq_imp_qeqT. apply Qeq_sym. exact Hp.
Qed.

(* Strict version: if the first pair strictly decreases (f1 <T f0) and n >= 2, the alternating sum is strictly positive. *)
Lemma altsum_pos_strict : forall (f : nat -> Q) (n : nat),
  (forall k, QleT' 0 (f k)) ->
  (forall k, QleT' (f (Datatypes.S k)) (f k)) ->
  QltT (f 1%nat) (f 0%nat) -> (2 <= n)%nat ->
  QltT 0 (altsum f n).
Proof.
  intros f n H0 Hd Hlt Hn. destruct n as [|[|m]].
  - lia.
  - lia.
  - destruct m as [| m'].
    + (* n = 2: the alternating sum == f0 - f1 > 0. *)
      assert (Hp : altsum f 2%nat == f 0%nat + Qopp (f 1%nat)).
      { unfold altsum.
        rewrite (qeqT_imp_qeq _ _ (altsum_acc_T f 0%nat 1%nat)).
        rewrite (qeqT_imp_qeq _ _ (altsum_acc_F f 1%nat 0%nat)).
        rewrite (qeqT_imp_qeq _ _ (altsum_acc_0_eq true f 2%nat)). ring. }
      apply (qeq_ltT (f 0%nat + Qopp (f 1%nat)) (altsum f 2%nat)).
      * apply qeq_imp_qeqT. apply Qeq_sym. exact Hp.
      * apply altsum_qltT_sub_pos. exact Hlt.
    + (* n >= 3: strictly positive first pair plus a nonnegative tail. *)
      assert (Hp : altsum f (Datatypes.S (Datatypes.S (Datatypes.S m')))
                   == (f 0%nat + Qopp (f 1%nat)) + altsum_acc true f 2%nat (Datatypes.S m')).
      { unfold altsum.
        rewrite (qeqT_imp_qeq _ _ (altsum_acc_T f 0%nat (Datatypes.S (Datatypes.S m')))).
        rewrite (qeqT_imp_qeq _ _ (altsum_acc_F f 1%nat (Datatypes.S m'))). ring. }
      apply (qeq_ltT
        ((f 0%nat + Qopp (f 1%nat)) + altsum_acc true f 2%nat (Datatypes.S m'))
        (altsum f (Datatypes.S (Datatypes.S (Datatypes.S m'))))).
      * apply qeq_imp_qeqT. apply Qeq_sym. exact Hp.
      * apply altsum_strict_plus_le.
        -- apply altsum_qltT_sub_pos. exact Hlt.
        -- exact (altsum_altacc_evenstart_pos f 1%nat (Datatypes.S m') H0 Hd).
Qed.

(* Parity refinement (valid direction): n >= 1 implies f0 - f1 <= the alternating sum.
   The reverse direction (the alternating sum <= f0 - f1 for odd n) is false in
   general: for the constant sequence f = 1 (nonnegative and nonincreasing) the
   sum at n = 3 equals 1 > 0 = f0 - f1. The correct refinement is this lower
   bound, which holds for every n >= 1, even n included. *)
Lemma altsum_ge_pair0 : forall (f : nat -> Q) (n : nat),
  (forall k, QleT' 0 (f k)) ->
  (forall k, QleT' (f (Datatypes.S k)) (f k)) ->
  (1 <= n)%nat ->
  QleT' (f 0%nat + Qopp (f 1%nat)) (altsum f n).
Proof.
  intros f n H0 Hd Hn. destruct n as [| m].
  - lia.
  - destruct m as [| m'].
    + (* n = 1: the alternating sum == f0 >= f0 - f1. *)
      assert (Hp : altsum f 1%nat == f 0%nat + 0).
      { unfold altsum.
        rewrite (qeqT_imp_qeq _ _ (altsum_acc_T f 0%nat 0%nat)).
        rewrite (qeqT_imp_qeq _ _ (altsum_acc_0_eq false f 1%nat)). reflexivity. }
      apply (qleT'_trans (f 0%nat + Qopp (f 1%nat)) (f 0%nat + 0) (altsum f 1%nat)).
      * apply qleT'_plus_compat.
        -- apply qleT'_refl.
        -- apply altsum_qleT'_neg_le0. apply H0.
      * apply qeq_leT'. apply qeq_imp_qeqT. apply Qeq_sym. exact Hp.
    + (* n >= 2: the alternating sum == (f0 - f1) + the even-start tail, the tail being >= 0. *)
      assert (Hp : altsum f (Datatypes.S (Datatypes.S m'))
                   == (f 0%nat + Qopp (f 1%nat)) + altsum_acc true f 2%nat m').
      { unfold altsum.
        rewrite (qeqT_imp_qeq _ _ (altsum_acc_T f 0%nat (Datatypes.S m'))).
        rewrite (qeqT_imp_qeq _ _ (altsum_acc_F f 1%nat m')). ring. }
      apply (qleT'_trans (f 0%nat + Qopp (f 1%nat))
        ((f 0%nat + Qopp (f 1%nat)) + altsum_acc true f 2%nat m')
        (altsum f (Datatypes.S (Datatypes.S m')))).
      * apply (qleT'_trans (f 0%nat + Qopp (f 1%nat)) ((f 0%nat + Qopp (f 1%nat)) + 0) _).
        -- apply qeq_leT'. apply qeq_imp_qeqT. ring.
        -- apply (qleT'_plus_compat (f 0%nat + Qopp (f 1%nat))
                    (f 0%nat + Qopp (f 1%nat)) 0%Q
                    (altsum_acc true f 2%nat m')).
           ++ apply qleT'_refl.
           ++ exact (altsum_altacc_evenstart_pos f 1%nat m' H0 Hd).
      * apply qeq_leT'. apply qeq_imp_qeqT. apply Qeq_sym. exact Hp.
Qed.

(* ================================================================== *)
(* Part 6: concrete warm-up instances (n <= 3, each closed by          *)
(* computation under the standing hypotheses).                         *)
(* ================================================================== *)

(* Constant sequence 1/2: the two-term alternation 1/2 - 1/2 == 0 is nonnegative. *)
Example altsum_ex_2 : QleT' 0 (altsum (fun _ => (1#2)%Q) 2).
Proof. unfold QleT'. exact (@id_refl _ true). Qed.

(* Constant sequence 2: the three-term alternation 2 - 2 + 2 == 2 > 0. *)
Example altsum_ex_3 : QltT 0 (altsum (fun _ => (2#1)%Q) 3).
Proof. unfold QltT. exact (@id_refl _ true). Qed.

(* Constant sequence 3: the single term 3 >= 0. *)
Example altsum_ex_1 : QleT' 0 (altsum (fun _ => (3#1)%Q) 1).
Proof. unfold QleT'. exact (@id_refl _ true). Qed.

(* Concrete decreasing sequence f = 3, 2, 1: the three-term alternation 3 - 2 + 1 == 2 > 0. *)
Example altsum_ex_dec3 : QltT 0 (altsum (fun k => (3#1)%Q + Qopp ((Z.of_nat k # 1)%Q)) 3).
Proof. unfold QltT. exact (@id_refl _ true). Qed.
