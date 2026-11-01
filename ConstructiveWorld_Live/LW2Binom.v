(* ==================================================================== *)
(* LW2Binom.v - nat binomial coefficients with a Z bridge, Set-carried. *)
(* Mission.  The nat binomial lw2_binom (Pascal recursion on the first  *)
(*   argument) with companions: boolean nonnegativity lw2_binom_nonneg; *)
(*   zero tail lw2_binom_above; diagonal lw2_binom_diag; factorial      *)
(*   lw2_fact with successor witness lw2_fact_pos (a sigT dependent     *)
(*   pair); factorial characterization lw2_binom_fact (counting lemma   *)
(*   behind the symmetry law C(n,k) = C(n,n-k)); local multiplication   *)
(*   left-commutation lw2_mul_left_comm; the Z sign equations           *)
(*   lw2_zsign_even / lw2_zsign_odd (odd-even split of (-1) powers      *)
(*   feeding the z_lo sign factor of the S07 lo formula); and the Z     *)
(*   bridge lw2_binom_Z expanding Z.of_nat (lw2_binom n k) branchwise,  *)
(*   so Z-domain consumers unfold the Pascal structure in place.  The   *)
(*   three defining equations (lw2_binom n 0 = 1; lw2_binom 0 (S k)=0;  *)
(*   lw2_binom (S n) (S k) = lw2_binom n (S k) + lw2_binom n k) are     *)
(*   reflexivity-checkable, and Pascal is the third of them.            *)
(* Dependencies.  Stdlib Arith, ZArith, Lia; tree S01_BaseRing for the  *)
(*   Set equality Id (constructor id_refl, symmetry id_sym); sigT from  *)
(*   Coq.Init.Specif.                                                   *)
(* References.  Statement faces follow LW2ZInt.v (LW2 wave); recursion  *)
(*   follows the Pascal addition shape (UpReqBanachAdd bpa_binom is the *)
(*   Q-valued form; the factorial pair joins the LW0Integrality2        *)
(*   lw0_ratio domain through lw2_binom_fact and the two Z entries.     *)
(* Constructivity.  All statements are Set-carried (equations as Id,    *)
(*   witness as sigT; no premises, no Prop on the statement face);      *)
(*   definitions are Fixpoint algorithms; proofs are constructive       *)
(*   (structural induction, rewriting, ring, lia); in-proof arithmetic  *)
(*   uses the classic equation form, closed into id_refl shape.         *)
(* Build.  rocq c -native-compiler no -q -Q . "" LW2Binom.v             *)
(* ==================================================================== *)

From Stdlib Require Import Arith.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
Require Import S01_BaseRing.

(* nat binomial coefficient, Pascal recursion (the recursion variable is
   the first argument n). *)
Fixpoint lw2_binom (n k : nat) : nat :=
  match n with
  | 0 => match k with 0 => 1 | Datatypes.S _ => 0 end
  | Datatypes.S n' =>
      match k with
      | 0 => 1
      | Datatypes.S k' => lw2_binom n' (Datatypes.S k') + lw2_binom n' k'
      end
  end.

(* nat factorial (the counting basis of the Z bridge). *)
Fixpoint lw2_fact (n : nat) : nat :=
  match n with 0 => 1 | Datatypes.S m => Datatypes.S m * lw2_fact m end.

(* Non-negativity (boolean form, trivial but explicit). *)
Lemma lw2_binom_nonneg : forall n k : nat, Id (Nat.leb 0 (lw2_binom n k)) true.
Proof. intros n k. apply id_refl. Qed.

(* Factorial strictly positive (successor witness form, consumed by the
   division elimination of the symmetry law). *)
Lemma lw2_fact_pos : forall n : nat,
  sigT (fun p : nat => Id (lw2_fact n) (Datatypes.S p)).
Proof.
  induction n as [|n IH].
  - exists 0%nat. apply id_refl.
  - destruct IH as [p Hp].
    assert (Hp' : lw2_fact n = Datatypes.S p)
      by (destruct (id_sym Hp); reflexivity).
    exists (p + n * Datatypes.S p). simpl. rewrite Hp'. apply id_refl.
Qed.

(* Zero tail: the coefficient vanishes once k exceeds n. *)
Lemma lw2_binom_above : forall n k : nat, Id (lw2_binom n (n + Datatypes.S k)) 0.
Proof.
  induction n as [|n IH]; intro k; simpl.
  - apply id_refl.
  - replace (Datatypes.S (n + Datatypes.S k))
      with (n + Datatypes.S (Datatypes.S k)) by lia.
    assert (HA : lw2_binom n (n + Datatypes.S (Datatypes.S k)) = 0)
      by (destruct (id_sym (IH (Datatypes.S k))); reflexivity).
    assert (HB : lw2_binom n (n + Datatypes.S k) = 0)
      by (destruct (id_sym (IH k)); reflexivity).
    rewrite HA, HB. apply id_refl.
Qed.

(* Diagonal: C(n,n) = 1. *)
Lemma lw2_binom_diag : forall n : nat, Id (lw2_binom n n) 1.
Proof.
  induction n as [|n IH].
  - apply id_refl.
  - simpl. pose proof (lw2_binom_above n 0) as HA.
    replace (Datatypes.S n) with (n + Datatypes.S 0) by lia.
    assert (HAe : lw2_binom n (n + Datatypes.S 0) = 0)
      by (destruct (id_sym HA); reflexivity).
    assert (HDe : lw2_binom n n = 1)
      by (destruct (id_sym IH); reflexivity).
    rewrite HAe, HDe. apply id_refl.
Qed.

(* Multiplication left-commutation (Nat.mul_left_comm is absent from the
   environment; restated locally). *)
Lemma lw2_mul_left_comm : forall a b c : nat, Id (a * (b * c)) (b * (a * c)).
Proof.
  intros a b c.
  rewrite (Nat.mul_assoc a b c), (Nat.mul_comm a b), <- (Nat.mul_assoc b a c).
  apply id_refl.
Qed.

(* Factorial characterization (the counting main lemma of the symmetry
   law).  The induction runs on the classic equation form, and the Id
   goal is closed by destructing the resulting equation. *)
Lemma lw2_binom_fact : forall n k : nat,
  Id (lw2_fact (n + k)) (lw2_binom (n + k) k * (lw2_fact n * lw2_fact k)).
Proof.
  intro n. induction n as [|n IH].
  - intro k.
    assert (HD : lw2_binom k k = 1)
      by (destruct (id_sym (lw2_binom_diag k)); reflexivity).
    assert (Heq : lw2_fact (0 + k)
                  = lw2_binom (0 + k) k * (lw2_fact 0 * lw2_fact k)).
    { simpl. rewrite HD, ?Nat.mul_1_l. lia. }
    rewrite Heq. apply id_refl.
  - intro k.
    assert (IHe : forall j : nat,
              lw2_fact (n + j) = lw2_binom (n + j) j * (lw2_fact n * lw2_fact j))
      by (intro j; destruct (id_sym (IH j)); reflexivity).
    assert (Heq : lw2_fact (Datatypes.S n + k)
                  = lw2_binom (Datatypes.S n + k) k
                    * (lw2_fact (Datatypes.S n) * lw2_fact k)).
    { induction k as [|c IHc].
      + simpl. rewrite ?Nat.add_0_r, ?Nat.mul_1_r, ?Nat.mul_1_l. reflexivity.
      + assert (HB : lw2_binom (Datatypes.S n + Datatypes.S c) (Datatypes.S c)
                     = lw2_binom (n + Datatypes.S c) (Datatypes.S c)
                       + lw2_binom (n + Datatypes.S c) c)
          by reflexivity.
        assert (HF : lw2_fact (Datatypes.S n + Datatypes.S c)
                     = Datatypes.S (n + Datatypes.S c)
                       * lw2_fact (n + Datatypes.S c))
          by reflexivity.
        assert (H1 : lw2_fact (Datatypes.S n) = Datatypes.S n * lw2_fact n)
          by reflexivity.
        assert (H2 : lw2_fact (Datatypes.S c) = Datatypes.S c * lw2_fact c)
          by reflexivity.
        rewrite HB, HF, H1, H2.
        remember (lw2_fact n) as fn eqn:Ef.
        remember (lw2_fact c) as fc eqn:Ec.
        remember (lw2_binom (n + Datatypes.S c) (Datatypes.S c)) as B1 eqn:E1.
        remember (lw2_binom (n + Datatypes.S c) c) as B2 eqn:E2.
        remember (lw2_binom (n + c) c) as B0 eqn:E0.
        assert (A1 : lw2_fact (n + Datatypes.S c)
                     = lw2_binom (n + Datatypes.S c) (Datatypes.S c)
                       * (fn * lw2_fact (Datatypes.S c)))
          by (apply IHe).
        rewrite <- E1, H2 in A1.
        assert (A2 : lw2_fact (n + c) = lw2_binom (n + c) c * (fn * lw2_fact c))
          by (apply IHe).
        rewrite <- E0, <- Ec in A2.
        assert (A3 : lw2_fact (Datatypes.S n + c)
                     = lw2_binom (Datatypes.S n + c) c
                       * (lw2_fact (Datatypes.S n) * fc))
          by (apply IHc).
        assert (H4 : lw2_fact (Datatypes.S n + c)
                     = Datatypes.S (n + c) * lw2_fact (n + c))
          by reflexivity.
        assert (H5 : lw2_binom (Datatypes.S n + c) c = B2)
          by (rewrite E2;
              replace (n + Datatypes.S c) with (Datatypes.S n + c) by lia;
              reflexivity).
        rewrite H4, H5, H1, A2 in A3.
        rewrite <- (Nat.mul_assoc (Datatypes.S n) fn fc) in A3.
        assert (EQ1 : B1 * (fn * (Datatypes.S c * fc))
                      = Datatypes.S (n + c) * (B0 * (fn * fc))).
        { rewrite <- A1, Nat.add_succ_r.
          assert (H7 : lw2_fact (Datatypes.S (n + c))
                       = Datatypes.S (n + c) * lw2_fact (n + c))
            by reflexivity.
          rewrite H7, A2. reflexivity. }
        assert (EQ2 : B2 * (Datatypes.S n * (fn * fc))
                      = Datatypes.S (n + c) * (B0 * (fn * fc))).
        { symmetry. exact A3. }
        rewrite A1, EQ1, Nat.mul_add_distr_r.
        assert (HMLC : forall a b d : nat, a * (b * d) = b * (a * d)).
        { intros; destruct (id_sym (lw2_mul_left_comm a b d)); reflexivity. }
        assert (R1 : B1 * (Datatypes.S n * fn * (Datatypes.S c * fc))
                     = Datatypes.S n * (Datatypes.S (n + c) * (B0 * (fn * fc)))).
        { rewrite <- Nat.mul_assoc, <- EQ1. apply HMLC. }
        assert (R2 : B2 * (Datatypes.S n * fn * (Datatypes.S c * fc))
                     = Datatypes.S c * (Datatypes.S (n + c) * (B0 * (fn * fc)))).
        { rewrite <- Nat.mul_assoc, (HMLC fn (Datatypes.S c) fc),
                   (HMLC (Datatypes.S n) (Datatypes.S c) (fn * fc)), <- EQ2.
          apply HMLC. }
        rewrite R1, R2, <- Nat.mul_add_distr_r. f_equal. }
    rewrite Heq. apply id_refl.
Qed.

(* Z sign factor equations: the odd-even split of (-1) powers. *)
Lemma lw2_zsign_even : forall e : nat, Id (Z.pow (-1)%Z (Z.of_nat (2 * e))) 1%Z.
Proof.
  intro e. assert (Heq : Z.pow (-1)%Z (Z.of_nat (2 * e)) = 1%Z).
  { induction e as [|e IH].
    - reflexivity.
    - replace (2 * Datatypes.S e)
        with (Datatypes.S (Datatypes.S (2 * e))) by lia.
      rewrite !Nat2Z.inj_succ, !Z.pow_succ_r by lia.
      rewrite IH. ring. }
  rewrite Heq. apply id_refl.
Qed.

Lemma lw2_zsign_odd : forall e : nat,
  Id (Z.pow (-1)%Z (Z.of_nat (2 * e + 1))) (-1)%Z.
Proof.
  intro e. assert (Heq : Z.pow (-1)%Z (Z.of_nat (2 * e + 1)) = (-1)%Z).
  { induction e as [|e IH].
    - reflexivity.
    - replace (2 * Datatypes.S e + 1)
        with (Datatypes.S (Datatypes.S (2 * e + 1))) by lia.
      rewrite !Nat2Z.inj_succ, !Z.pow_succ_r by lia.
      rewrite IH. ring. }
  rewrite Heq. apply id_refl.
Qed.

(* Z bridge: the three-branch access equation for Z.of_nat (lw2_binom n k)
   (the Z-domain Pascal form). *)
Lemma lw2_binom_Z : forall n k : nat,
  Id (Z.of_nat (lw2_binom n k))
     (match n with
      | 0 => match k with 0 => 1%Z | Datatypes.S _ => 0%Z end
      | Datatypes.S n' =>
          match k with
          | 0 => 1%Z
          | Datatypes.S k' =>
              (Z.of_nat (lw2_binom n' (Datatypes.S k'))
               + Z.of_nat (lw2_binom n' k'))%Z
          end
      end).
Proof.
  intros n k. destruct n as [|n]; destruct k as [|k]; simpl; try apply id_refl.
  rewrite Nat2Z.inj_add. apply id_refl.
Qed.

(* Every statement closes under the global context. *)
Print Assumptions lw2_binom_nonneg.
Print Assumptions lw2_fact_pos.
Print Assumptions lw2_binom_above.
Print Assumptions lw2_binom_diag.
Print Assumptions lw2_mul_left_comm.
Print Assumptions lw2_binom_fact.
Print Assumptions lw2_zsign_even.
Print Assumptions lw2_zsign_odd.
Print Assumptions lw2_binom_Z.
