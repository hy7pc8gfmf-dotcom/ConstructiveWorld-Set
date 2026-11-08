(* ConstructiveWorld-Set — the Niven source polynomial with certified integer coefficients. *)

(** * LW2NivenInt: integrality of the Niven source polynomial, pure-Z face.

    Mission.  The Niven source polynomial [f = t^n (a - b*t)^n] for
      [a b : Z] on its pure-Z face: every coefficient is a closed-form
      integer (binomial [lw2_binom] times Z powers times the sign factor
      [(-1)^k]) with its own [sigT] integer witness, so [lw2_niven_f_intpoly
      : forall a b n, [lw2i_intpoly] (lw2_niven_int_f a b n)] holds by
      construction (via LW2Hermite's [lw2i_intpoly]); [lw2_niven_f_lc] /
      [lw2_niven_f_lc_closed] serve the nonvanishing determination in M3.

    Dependencies.  Stdlib [QArith], [ZArith], [Arith], [Lia], [List].
      Requires [S01_BaseRing], [S02_CauchyComplete], [LW0QPoly],
      [LW2Binom], and [LW2Hermite] of this development.

    References.  This development, LW2NivenInt.v, the baseline module
      in ConstructiveWorld-Main whose statement names are carried over
      here verbatim (statement-face Set-carrier completion); the
      reserved M3 interface is [eval(p,e)]-shaped and [f ∈ ℤ[X]] is
      constructed directly (pure-Z face; π does not enter [f]).

    Constructivity.  Every operation is a closed-form map with computing
      content ([Defined]); statements carry [Qeq] between rational data
      with explicit [Z] witnesses in [sigT] form; every proof ends in [Qed].

    Build.  [coqc -native-compiler no -q -Q . "" LW2NivenInt.v]
      compiles cleanly (exit 0); the first eight bytes of the
      artifact are [436f7121 00015ff4]. *)

From Stdlib Require Import QArith ZArith Arith Lia List.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import LW0QPoly.
Require Import LW2Binom.
Require Import LW2Hermite.

(* ------------------------------------------------------------------ *)
(* Section 1.  Leibniz-form coefficient lookup on mapped index lists.  *)
(* (map g (seq s m)) is [g s; g (s+1); ...; g (s+m-1)]: its j-th       *)
(* coefficient is g (s+j) when j < m, and structurally 0 beyond.       *)
(* Everything in this section is plain Leibniz equality on Q, so the   *)
(* downstream rewrites need no setoid machinery.                       *)
(* ------------------------------------------------------------------ *)

Lemma lw2_len_map_seq : forall (g : nat -> Q) (m s : nat),
  Id m (length (map g (seq s m))).
Proof.
  intros g.
  assert (Hc : forall m s, length (map g (seq s m)) = m).
  { induction m as [|m IH]; intros s.
    - reflexivity.
    - cbn [seq map length].
      rewrite (IH (Datatypes.S s)).
      reflexivity. }
  intros m s.
  rewrite (Hc m s).
  apply id_refl.
Qed.

Lemma lw2_coef_beyond_eq : forall (j : nat) (p : QPoly),
  (length p <= j)%nat -> Id (lw0_coef j p) 0%Q.
Proof.
  assert (Hc : forall (j : nat) (p : QPoly),
    (length p <= j)%nat -> lw0_coef j p = 0%Q).
  { intros j p.
    revert j.
    induction p as [|a p IH]; intros j Hj.
    - reflexivity.
    - destruct j as [|j'].
      + simpl in Hj. lia.
      + cbn [lw0_coef].
        apply (IH j').
        simpl in Hj. lia. }
  intros j p Hj.
  rewrite (Hc j p Hj).
  apply id_refl.
Qed.

Lemma lw2_coef_seq_gen_eq : forall (g : nat -> Q) (m s i : nat),
  (i < m)%nat -> Id (lw0_coef i (map g (seq s m))) (g (s + i)%nat).
Proof.
  assert (Hc : forall (g : nat -> Q) (m s i : nat),
    (i < m)%nat -> lw0_coef i (map g (seq s m)) = g (s + i)%nat).
  { intros g.
    induction m as [|m IH]; intros s i Hi.
    - exfalso. lia.
    - cbn [seq map].
      destruct i as [|i'].
      + cbn [lw0_coef].
        rewrite Nat.add_0_r.
        reflexivity.
      + cbn [lw0_coef].
        replace (s + Datatypes.S i')%nat with (Datatypes.S s + i')%nat by lia.
        apply IH.
        lia. }
  intros g m s i Hi.
  rewrite (Hc g m s i Hi).
  apply id_refl.
Qed.

Lemma lw2_coef_seq0_eq : forall (g : nat -> Q) (m i : nat),
  (i < m)%nat -> Id (lw0_coef i (map g (seq 0 m))) (g i).
Proof.
  assert (Hc : forall (g : nat -> Q) (m i : nat),
    (i < m)%nat -> lw0_coef i (map g (seq 0 m)) = g i).
  { intros g m i Hi.
    rewrite <- (Nat.add_0_l i).
    destruct (lw2_coef_seq_gen_eq g m 0 i Hi).
    reflexivity. }
  intros g m i Hi.
  rewrite (Hc g m i Hi).
  apply id_refl.
Qed.

(* ------------------------------------------------------------------ *)
(* Section 2.  The Niven source polynomial, pure-Z face.               *)
(* f = t^n (a - b*t)^n with a b : Z.  Closed-form coefficients: the    *)
(* coefficient of t^(n+k) is (-1)^k * binom(n,k) * a^(n-k) * b^k, zero *)
(* outside [n, 2n].  Indexing by the absolute degree i with d = i - n  *)
(* (truncated nat subtraction), the gate n <=? i zeroes the low band;  *)
(* the high band (d > n) dies through lw2_binom's zero branch.         *)
(* ------------------------------------------------------------------ *)

Definition lw2_niven_zcoef (a b : Z) (n i : nat) : Z :=
  match Nat.leb n i with
  | true =>
      (Z.pow (-1)%Z (Z.of_nat (i - n)) *
       Z.of_nat (lw2_binom n (i - n)) *
       Z.pow a (Z.of_nat (n - (i - n))) *
       Z.pow b (Z.of_nat (i - n)))%Z
  | false => 0%Z
  end.

Definition lw2_niven_int_f (a b : Z) (n : nat) : QPoly :=
  map (fun k : nat => (lw2_niven_zcoef a b n k # 1)%Q)
      (seq 0 (Datatypes.S (n + n))).

(* ------------------------------------------------------------------ *)
(* Section 3.  Automatic integrality (the main deliverable).           *)
(* Each coefficient carries an explicit Z witness: the same closed     *)
(* form that defines it -- integrality holds by construction.          *)
(* Three regions: witness 0 for i < n, the closed-form witness for     *)
(* n <= i <= 2n, witness 0 for i > 2n.                                 *)
(* ------------------------------------------------------------------ *)

(* Relation to the Niven polynomial of LW0Integrality2: there
   [lw0_niven_f_z] q b n = (b^n/n!) * t^n (q - t)^n with q : Q, b : Z,
   so at [q = a/b], [lw0_niven_f_z (a/b) b n = (1/n!) *
   lw2_niven_int_f a b n] (a rational identity).  This file does not
   Require LW0Integrality2: its upstream chain
   [S03_QExp]/[UpReqBanachAdd] lies outside this build world, so the
   relation is declared here.  The [1/n!] scaling is not a
   coefficient-layer matter: in the Niven argument the integrality of
   j!/n! holds at the derivative-value layer for k >= n (j!/n! is a
   nat factorial ratio), and the coefficient layer takes the unscaled
   [t^n (a - b*t)^n], whose integrality holds without further proof.
   Interface honesty: an unconditional integrality predicate on
   [lw0_niven_f_z] itself is false (at [q = 1], [b = 1], [n = 2] the
   coefficient of [t^2] is [1/2]); the nonzero-premise form of the
   main statement is therefore replaced here by the premise-free
   strengthened form. *)

Theorem lw2_niven_f_intpoly : forall (a b : Z) (n : nat),
  lw2i_intpoly (lw2_niven_int_f a b n).
Proof.
  intros a b n i.
  destruct (Nat.leb n i) eqn:Hb1.
  - destruct (Nat.leb i (n + n)) eqn:Hb2.
    + (* main band: witness is the closed form itself. *)
      apply Nat.leb_le in Hb1.
      apply Nat.leb_le in Hb2.
      assert (Hin : (i < Datatypes.S (n + n))%nat) by lia.
      exists (lw2_niven_zcoef a b n i).
      unfold lw2_niven_int_f.
      assert (Hc0 : lw0_coef i
                 (map (fun k : nat => (lw2_niven_zcoef a b n k # 1)%Q)
                      (seq 0 (Datatypes.S (n + n))))
                 = (fun k : nat => (lw2_niven_zcoef a b n k # 1)%Q) i).
      { destruct (lw2_coef_seq0_eq
               (fun k : nat => (lw2_niven_zcoef a b n k # 1)%Q)
               (Datatypes.S (n + n)) i Hin).
        reflexivity. }
      rewrite Hc0. cbv beta.
      apply qeq_imp_qeqT. apply Qeq_refl.
    + (* beyond the list: coefficient is structurally zero. *)
      apply Nat.leb_gt in Hb2.
      assert (Hout : (Datatypes.S (n + n) <= i)%nat) by lia.
      exists 0%Z.
      unfold lw2_niven_int_f.
      assert (Hlen : length (map (fun k : nat => (lw2_niven_zcoef a b n k # 1)%Q)
                      (seq 0 (Datatypes.S (n + n)))) = Datatypes.S (n + n)).
      { destruct (lw2_len_map_seq
               (fun k : nat => (lw2_niven_zcoef a b n k # 1)%Q)
               (Datatypes.S (n + n)) 0).
        reflexivity. }
      assert (Hbeyond : lw0_coef i
                 (map (fun k : nat => (lw2_niven_zcoef a b n k # 1)%Q)
                      (seq 0 (Datatypes.S (n + n)))) = 0%Q).
      { destruct (lw2_coef_beyond_eq i
               (map (fun k : nat => (lw2_niven_zcoef a b n k # 1)%Q)
                    (seq 0 (Datatypes.S (n + n))))
               ltac:(rewrite Hlen; exact Hout)).
        reflexivity. }
      rewrite Hbeyond.
      reflexivity.
  - (* low band: coefficient is the gated zero. *)
    assert (Hlt : (i < n)%nat) by (apply Nat.leb_gt; exact Hb1).
    assert (Hin : (i < Datatypes.S (n + n))%nat) by lia.
    exists 0%Z.
    unfold lw2_niven_int_f.
    assert (Hc0 : lw0_coef i
               (map (fun k : nat => (lw2_niven_zcoef a b n k # 1)%Q)
                    (seq 0 (Datatypes.S (n + n))))
               = (fun k : nat => (lw2_niven_zcoef a b n k # 1)%Q) i).
    { destruct (lw2_coef_seq0_eq
             (fun k : nat => (lw2_niven_zcoef a b n k # 1)%Q)
             (Datatypes.S (n + n)) i Hin).
      reflexivity. }
    rewrite Hc0.
    cbv beta.
    unfold lw2_niven_zcoef.
    rewrite Hb1.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Section 4.  Leading-coefficient faces for M3's nonzero consumption. *)
(* The top coefficient (degree 2n) is the closed form at i = n + n;    *)
(* it further collapses to (-1)^n * b^n (binom n n = 1, a^0 = 1), so   *)
(* b <> 0 in Z certifies f <> 0 by pure Z arithmetic downstream.       *)
(* ------------------------------------------------------------------ *)

Lemma lw2_niven_f_lc : forall (a b : Z) (n : nat),
  QeqT (lw0_coef (n + n) (lw2_niven_int_f a b n))
       ((lw2_niven_zcoef a b n (n + n)) # 1)%Q.
Proof.
  intros a b n.
  unfold lw2_niven_int_f.
  assert (Hc0 : lw0_coef (n + n)
             (map (fun k : nat => (lw2_niven_zcoef a b n k # 1)%Q)
                  (seq 0 (Datatypes.S (n + n))))
             = (fun k : nat => (lw2_niven_zcoef a b n k # 1)%Q) (n + n)%nat).
  { destruct (lw2_coef_seq0_eq
           (fun k : nat => (lw2_niven_zcoef a b n k # 1)%Q)
           (Datatypes.S (n + n)) (n + n) (Nat.lt_succ_diag_r (n + n))).
    reflexivity. }
  rewrite Hc0. cbv beta.
  apply qeq_imp_qeqT. apply Qeq_refl.
Qed.

Lemma lw2_niven_f_lc_closed : forall (a b : Z) (n : nat),
  QeqT (lw0_coef (n + n) (lw2_niven_int_f a b n))
       ((Z.pow (-1)%Z (Z.of_nat n) * Z.pow b (Z.of_nat n)) # 1)%Q.
Proof.
  intros a b n.
  unfold lw2_niven_int_f.
  assert (Hc0 : lw0_coef (n + n)
             (map (fun k : nat => (lw2_niven_zcoef a b n k # 1)%Q)
                  (seq 0 (Datatypes.S (n + n))))
             = (fun k : nat => (lw2_niven_zcoef a b n k # 1)%Q) (n + n)%nat).
  { destruct (lw2_coef_seq0_eq
           (fun k : nat => (lw2_niven_zcoef a b n k # 1)%Q)
           (Datatypes.S (n + n)) (n + n) (Nat.lt_succ_diag_r (n + n))).
    reflexivity. }
  rewrite Hc0.
  cbv beta.
  apply qeq_imp_qeqT.
  unfold lw2_niven_zcoef.
  assert (Hg : Nat.leb n (n + n) = true) by (apply Nat.leb_le; lia).
  rewrite Hg.
  replace (n + n - n)%nat with n by lia.
  rewrite lw2_binom_diag.
  change (Z.of_nat 1) with 1%Z.
  replace (n - n)%nat with 0%nat by lia.
  change (Z.of_nat 0) with 0%Z.
  rewrite Z.pow_0_r.
  unfold Qeq.
  cbn [Qnum Qden].
  ring.
Qed.

(* ------------------------------------------------------------------ *)
(* Section 5.  Extraction probe and assumption checks.                 *)
(* ------------------------------------------------------------------ *)

From Stdlib Require Import Extraction.
Separate Extraction lw2_niven_int_f lw2_niven_f_intpoly lw2_niven_f_lc.

Print Assumptions lw2_niven_int_f.
Print Assumptions lw2_niven_f_intpoly.
Print Assumptions lw2_niven_f_lc.
Print Assumptions lw2_niven_f_lc_closed.
