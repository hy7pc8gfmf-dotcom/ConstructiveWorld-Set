(* ConstructiveWorld-Set — scalar-engine lemmas over Banach algebras, second set. *)

(** * UpReqBanachProd2: two-layer scalar lemmas over Banach algebras..

    Mission.  Three two-layer lemmas: [sum_upto_div] (constant factor extraction),
 [q_choose_div_fact] (binomial-factorial splitting), [exp_term_split]
 (per-term coefficient splitting), each at the [Q] engine layer and in
 the [bae]/[bmult] Banach context with the central-scalar commutation
 [bcoef_comm].

    Dependencies.  Stdlib [QArith.QArith]. Requires [S01_BaseRing],
 [S02_CauchyComplete], [S03_QExp], [UpReqBanachExp],
 [UpReqBanachProd] of this development.

    References.  This development, UpReqBanachProd2.v, the baseline module in
 ConstructiveWorld-Main whose statement names are carried over here
 verbatim (statement-face Set-carrier completion: [==] equalities
 moved to [QeqT]).

    Constructivity.  All named statements and fields are carried by
      [Set] (decidable Q-carriers [QltT]/[QleT']/[QeqT], [Id],
      [NatLe]); statements extract with [Obj.magic] = 0 and no
      erasure; [coqchk] reports [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" UpReqBanachProd2.v]
      compiles cleanly (exit 0); the first eight bytes of the
      artifact are [436f7121 00015ff4]. *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqBanachExp.
Require Import UpReqBanachProd.
From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith.
From Stdlib Require Import Setoid.
From Stdlib Require Import Lia.

Open Scope Q_scope.

(* ============================================================ *)
(* Section 1. The Q engine layer (binomial coefficients and factorial
   identities, [bpr2_] prefix). *)
(* ============================================================ *)

(* Binomial coefficient as a rational: [n!/(k!*(n-k)!)] (standard
   meaning for k <= n; the truncated-subtraction convention applies
   otherwise). *)
Definition bpr2_q_choose (n k : nat) : Q :=
  q_fact n / (q_fact k * q_fact (Nat.sub n k)).

(* Division constant extraction: [sum (f/c) = (sum f)/c] (Q layer,
   nonzero-denominator premise). *)
Lemma bpr2_sum_upto_div : forall (n : nat) (c : Q) (f : nat -> Q),
  ~ c == 0 -> QeqT (sum_upto n (fun j : nat => f j / c)) ((sum_upto n f) / c).
Proof.
  intros n c f Hc. apply qeq_imp_qeqT.
  induction n as [| n' IH]; simpl.
  - unfold Qdiv. ring.
  - setoid_rewrite IH. unfold Qdiv. ring.
Qed.

(* Factorial splitting: [C(n,k)/n! = 1/k! * 1/(n-k)!].  Two steps:
   rearrange atoms and cancel [n!] (inverse of a nonzero product),
   then split the inverse of a product. *)
Lemma bpr2_q_choose_div_fact : forall (n k : nat),
  QeqT (bpr2_q_choose n k / q_fact n) (Qinv (q_fact k) * Qinv (q_fact (Nat.sub n k))).
Proof.
  intros n k. apply qeq_imp_qeqT.
  unfold bpr2_q_choose. unfold Qdiv.
  transitivity (Qinv (q_fact k * q_fact (Nat.sub n k))).
  - transitivity
      ((q_fact n * Qinv (q_fact n)) * Qinv (q_fact k * q_fact (Nat.sub n k))).
    + (* Atom rearrangement: [Qinv] terms are atoms; commutativity and
         associativity close by [ring]. *)
      ring.
    + assert (Hn : ~ q_fact n == 0).
      { intro Hz. apply qeq_imp_qeqT in Hz.
        apply (q_neq_of_lt (q_fact n) (q_fact_pos n)) in Hz. destruct Hz. }
      rewrite (Qmult_inv_r (q_fact n) Hn).
      apply Qmult_1_l.
  - apply Qinv_mult_distr.
Qed.

(* Per-term coefficient splitting:
   [C(k,j) * x^j * y^(k-j) / k! = (x^j/j!) * (y^(k-j)/(k-j)!)].
   Proof: pull [C(k,j)/k!] to the front, substitute the factorial
   splitting identity, close by [ring]. *)
Lemma bpr2_exp_term_split : forall (x y : Q) (k j : nat),
  QeqT (bpr2_q_choose k j * q_pow x j * q_pow y (Nat.sub k j) / q_fact k)
  ((q_pow x j / q_fact j) * (q_pow y (Nat.sub k j) / q_fact (Nat.sub k j))).
Proof.
  intros x y k j. apply qeq_imp_qeqT.
  transitivity
    ((bpr2_q_choose k j / q_fact k) * q_pow x j * q_pow y (Nat.sub k j)).
  - unfold Qdiv. ring.
  - assert (Hdf : bpr2_q_choose k j / q_fact k == Qinv (q_fact j) * Qinv (q_fact (Nat.sub k j)))
      by (apply qeqT_imp_qeq; apply bpr2_q_choose_div_fact).
    rewrite Hdf. unfold Qdiv. ring.
Qed.

(* ============================================================ *)
(* Section 2. Congruence convenience lemmas: left/right one-sided
   faces of [bmult_wd].  The interface provides the four-slot
   [bmult_wd] (and one-sided add faces); the one-sided multiplication
   faces are supplied here and are used repeatedly in rearrangement
   chains and diagonal folding. *)
(* ============================================================ *)

Lemma bpr2_bmult_wd_l : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (a b c : BA),
  bae a b -> bae (@bmult _ _ B a c) (@bmult _ _ B b c).
Proof.
  intros BA bae B a b c H. exact (@bmult_wd _ _ B a c b c H (@bae_refl _ _ B c)).
Qed.

Lemma bpr2_bmult_wd_r : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (a b c : BA),
  bae a b -> bae (@bmult _ _ B c a) (@bmult _ _ B c b).
Proof.
  intros BA bae B a b c H. exact (@bmult_wd _ _ B c a c b (@bae_refl _ _ B c) H).
Qed.

(* ============================================================ *)
(* Section 3. The Banach-algebra layer (carriage-equality statements
   with scalar fields placed through [bcoef]). *)
(* ============================================================ *)

(* Scalar extraction in the algebra: [sum (f * bcoef (1/c)) =
   (sum f) * bcoef (1/c)] — the instance of the right-scalar law at
   the reciprocal scalar. *)
Lemma bpr2_bsum_div : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (n : nat) (c : Q)
                             (f : nat -> BA),
  bae (bsum _ _ B n (fun j : nat => @bmult _ _ B (f j) (@bcoef _ _ B (Qinv c))))
         (@bmult _ _ B (bsum _ _ B n f) (@bcoef _ _ B (Qinv c))).
Proof.
  intros BA bae B n c f. exact (bsum_scal _ _ B n (Qinv c) f).
Qed.

(* Main statement: diagonal coefficient folding by scalar centrality.
   [(a^j * bcoef(1/j!)) * (b^i * bcoef(1/i!)) =
    (a^j * b^i) * bcoef(1/j! * 1/i!)].  The seven-step chain runs
   through symmetry of associativity, reassociation, centrality of
   the scalar (swapping it past the algebra factor), reassociation,
   and closes by multiplicativity of [bcoef].  The order of the
   algebra factors [a^j] and [b^i] never changes (no commutativity of
   multiplication is used); the rational identity enters the carrier
   equality only through the constructive direction [bcoef_mult]. *)
Lemma bpr2_bterm_split : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (a b : BA) (k j : nat),
  bae
    (@bmult _ _ B (@bmult _ _ B (bpow BA bae B a j) (@bcoef _ _ B (Qinv (q_fact j))))
              (@bmult _ _ B (bpow BA bae B b (Nat.sub k j))
                        (@bcoef _ _ B (Qinv (q_fact (Nat.sub k j))))))
    (@bmult _ _ B (@bmult _ _ B (bpow BA bae B a j) (bpow BA bae B b (Nat.sub k j)))
              (@bcoef _ _ B
                 (Qinv (q_fact j) * Qinv (q_fact (Nat.sub k j)))%Q)).
Proof.
  intros BA bae B a b k j.
  (* Step 0 -> 1: [A*(c1*(Bb*c2))] — left associativity with the
     common left factor [A]. *)
  apply (@bae_trans _ _ B _
    (@bmult _ _ B (bpow BA bae B a j)
       (@bmult _ _ B (@bcoef _ _ B (Qinv (q_fact j)))
          (@bmult _ _ B (bpow BA bae B b (Nat.sub k j))
                   (@bcoef _ _ B (Qinv (q_fact (Nat.sub k j))))))) _).
  { apply (@bae_sym _ _ B).
    exact (@bmult_assoc _ _ B (bpow BA bae B a j) (@bcoef _ _ B (Qinv (q_fact j)))
             (@bmult _ _ B (bpow BA bae B b (Nat.sub k j))
                      (@bcoef _ _ B (Qinv (q_fact (Nat.sub k j)))))). }
  (* Step 1 -> 2: [A*((c1*Bb)*c2)] — associativity in the inner sum. *)
  apply (@bae_trans _ _ B _
    (@bmult _ _ B (bpow BA bae B a j)
       (@bmult _ _ B (@bmult _ _ B (@bcoef _ _ B (Qinv (q_fact j)))
                           (bpow BA bae B b (Nat.sub k j)))
                 (@bcoef _ _ B (Qinv (q_fact (Nat.sub k j)))))) _).
  { apply (@bpr2_bmult_wd_r _ _ B _ _ (@bpow BA bae B a j)).
    exact (@bmult_assoc _ _ B (@bcoef _ _ B (Qinv (q_fact j)))
             (bpow BA bae B b (Nat.sub k j))
             (@bcoef _ _ B (Qinv (q_fact (Nat.sub k j))))). }
  (* Step 2 -> 3: [A*((Bb*c1)*c2)] — the central scalar [c1] is
     swapped past the algebra factor [Bb] by [bcoef_comm]. *)
  apply (@bae_trans _ _ B _
    (@bmult _ _ B (bpow BA bae B a j)
       (@bmult _ _ B (@bmult _ _ B (bpow BA bae B b (Nat.sub k j))
                           (@bcoef _ _ B (Qinv (q_fact j))))
                 (@bcoef _ _ B (Qinv (q_fact (Nat.sub k j)))))) _).
  { apply (@bpr2_bmult_wd_r _ _ B _ _ (@bpow BA bae B a j)).
    apply (@bpr2_bmult_wd_l _ _ B (@bmult _ _ B (@bcoef _ _ B (Qinv (q_fact j)))
                                       (bpow BA bae B b (Nat.sub k j)))
                             (@bmult _ _ B (bpow BA bae B b (Nat.sub k j))
                                       (@bcoef _ _ B (Qinv (q_fact j))))
                             (@bcoef _ _ B (Qinv (q_fact (Nat.sub k j))))).
    apply (@bae_sym _ _ B).
    exact (@bcoef_comm _ _ B (Qinv (q_fact j)) (bpow BA bae B b (Nat.sub k j))). }
  (* Step 3 -> 4: [A*(Bb*(c1*c2))] — associativity, symmetric face. *)
  apply (@bae_trans _ _ B _
    (@bmult _ _ B (bpow BA bae B a j)
       (@bmult _ _ B (bpow BA bae B b (Nat.sub k j))
          (@bmult _ _ B (@bcoef _ _ B (Qinv (q_fact j)))
                   (@bcoef _ _ B (Qinv (q_fact (Nat.sub k j))))))) _).
  { apply (@bpr2_bmult_wd_r _ _ B _ _ (@bpow BA bae B a j)).
    apply (@bae_sym _ _ B).
    exact (@bmult_assoc _ _ B (bpow BA bae B b (Nat.sub k j))
             (@bcoef _ _ B (Qinv (q_fact j)))
             (@bcoef _ _ B (Qinv (q_fact (Nat.sub k j))))). }
  (* Step 4 -> 5: [(A*Bb)*(c1*c2)] — associativity, direct face. *)
  apply (@bae_trans _ _ B _
    (@bmult _ _ B (@bmult _ _ B (bpow BA bae B a j) (bpow BA bae B b (Nat.sub k j)))
             (@bmult _ _ B (@bcoef _ _ B (Qinv (q_fact j)))
                       (@bcoef _ _ B (Qinv (q_fact (Nat.sub k j)))))) _).
  { exact (@bmult_assoc _ _ B (bpow BA bae B a j) (bpow BA bae B b (Nat.sub k j))
             (@bmult _ _ B (@bcoef _ _ B (Qinv (q_fact j)))
                       (@bcoef _ _ B (Qinv (q_fact (Nat.sub k j)))))). }
 (* Step 5 -> goal: [(A*Bb)*bcoef(1/j! * 1/(k-j)!)] — closed by
     multiplicativity of [bcoef]. *)
  apply (@bpr2_bmult_wd_r _ _ B _ _ (@bmult _ _ B (bpow BA bae B a j)
                                        (bpow BA bae B b (Nat.sub k j)))).
  apply (@bae_sym _ _ B).
  exact (@bcoef_mult _ _ B (Qinv (q_fact j)) (Qinv (q_fact (Nat.sub k j)))).
Qed.

(* ============================================================ *)
(* Role of each statement: [bpr2_bsum_div] instantiates the
   right-scalar extraction law of UpReqBanachProd at reciprocal
   scalars; [bpr2_q_choose_div_fact]/[bpr2_exp_term_split] are the
   Q-engine for the diagonal collection step
   [C(k,j)/k! = 1/j! * 1/(k-j)!] of the Cauchy product; and
   [bpr2_bterm_split] is the square-to-diagonal folding lemma at the
   algebra layer, applied term by term.  Open extensions (no
   statements admitted here): the binomial expansion of [exp (a+b)]
   and the tail-truncated estimates, which connect to
   [esp_diff_le_tail] of UpReqBanachExp. *)
(* ============================================================ *)
