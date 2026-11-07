(* ConstructiveWorld-Set — Poincaré root-limit engine for a Salikhov-type pi recurrence. *)

(** * piu_zz_poincare_engine: Poincaré root-limit engine, part 1.

    Mission.  For the third-order recurrence with polynomial coefficients
      [p0..p3] (verbatim from oSALIKHOVpi3.txt:86-93): (i) the Set-carried
      Q-valued recurrence predicate [piu_zz_seq] with non-vanishing shift
      coefficient [p3]; (ii) the limit characteristic polynomial
      ([Ainf]/[Binf]/[Cinf]) with integer form [piu_zz_charpoly_int]
      (indicial polynomial of oSALIKHOVpi3.txt:138-147 up to sign), the
      commensuration quadruple, and Vieta readings mechanizing [|N1|^2 = 512/(27*N3)];
      (iii) the epsilon power-cage predicate [piu_zz_power_cage] and the
      [piu_zz_poincare_rootlimit] statement, frozen as a comment (its proof core belongs to later parts).

    Dependencies.  Stdlib [QArith], [Qring], [QArith.Qabs], [Lia],
      [Extraction]; the module is compiled closed (see [Print Assumptions]).

    References.  oSALIKHOVpi3.txt; D. Zeilberger, "A sequence of
      Diophantine approximations to Pi that implies its irrationality";
      H. Poincaré, Amer. J. Math. 7 (1885) 203-258; S. Elaydi, An
      Introduction to Difference Equations, 3rd ed.; the same-name
      ConstructiveWorld-Main baseline module of this development.

    Constructivity.  Statements carried in [Set]
      ([QeqT]/[QleT']/[QltT]/[QneqT]/[sigT]/[prod]); the frozen theorem
      is a comment, so the compiled module carries no unproved claim.

    Build.  [coqc -native-compiler no -q -Q ConstructiveWorld_Live ""
      piu_zz_poincare_engine.v] compiles cleanly (exit 0); the first
      eight bytes of the artifact are [436f7121 00015ff4]. *)

From Stdlib Require Import QArith Qring Lia.
From Stdlib Require Import QArith.Qabs.
From Stdlib Require Import Extraction.

(* ------------------------------------------------------------------ *)
(* Set-carried rational order / (in)equality carriers                  *)
(* ------------------------------------------------------------------ *)

Inductive QeqT (a b : Q) : Set :=
| qeqT_intro : a == b -> QeqT a b.

Inductive QleT' (a b : Q) : Set :=
| qleT_intro : a <= b -> QleT' a b.

Inductive QneqT (a b : Q) : Set :=
| qneqT_intro : a <> b -> QneqT a b.

Inductive QltT (a b : Q) : Set :=
| qltT_intro : a < b -> QltT a b.

Inductive BoolTrueT (b : bool) : Set :=
| boolTrueT_intro : b = true -> BoolTrueT b.

(* ------------------------------------------------------------------ *)
(* Recurrence coefficients p0..p3, transcribed verbatim from           *)
(* oSALIKHOVpi3.txt:86-93 (Maple format, integer polynomials,          *)
(* all of degree 9 in n).                                              *)
(* ------------------------------------------------------------------ *)

Definition pzz0 (n : nat) : Z :=
  (-1024 * (2 * Z.of_nat n + 5) * (2 * Z.of_nat n + 3) * (2 * Z.of_nat n + 1)
           * (Z.of_nat n + 2) * (Z.of_nat n + 1)
           * (559455 * Z.of_nat n ^ 4 + 5637736 * Z.of_nat n ^ 3
              + 21207869 * Z.of_nat n ^ 2 + 35294652 * Z.of_nat n + 21926016))%Z.

Definition pzz1 (n : nat) : Z :=
  (64 * (2 * Z.of_nat n + 5) * (2 * Z.of_nat n + 3) * (Z.of_nat n + 2)
       * (1208982255 * Z.of_nat n ^ 6 + 14601112006 * Z.of_nat n ^ 5
          + 71554462078 * Z.of_nat n ^ 4 + 181444545414 * Z.of_nat n ^ 3
          + 250049018747 * Z.of_nat n ^ 2 + 176898555884 * Z.of_nat n
          + 50159702880))%Z.

Definition pzz2 (n : nat) : Z :=
  (-6 * (2 * Z.of_nat n + 5)
        * (440102548665 * Z.of_nat n ^ 8 + 7075613606958 * Z.of_nat n ^ 7
           + 49182254436312 * Z.of_nat n ^ 6 + 192978557313766 * Z.of_nat n ^ 5
           + 467319046780891 * Z.of_nat n ^ 4 + 714892923466956 * Z.of_nat n ^ 3
           + 674376299494052 * Z.of_nat n ^ 2 + 358497976451216 * Z.of_nat n
           + 82191375084672))%Z.

Definition pzz3 (n : nat) : Z :=
  (3 * (4 * Z.of_nat n + 11) * (3 * Z.of_nat n + 8) * (3 * Z.of_nat n + 7)
       * (4 * Z.of_nat n + 9) * (Z.of_nat n + 3)
       * (559455 * Z.of_nat n ^ 4 + 3399916 * Z.of_nat n ^ 3
          + 7651391 * Z.of_nat n ^ 2 + 7554302 * Z.of_nat n + 2760952))%Z.

(* Sub-lemma L0a: the shift coefficient never vanishes. The five linear
   factors and the quartic (all coefficients positive) are positive for all
   n : nat. Mechanical integer sign arithmetic. *)
Lemma piu_zz_p3_pos : forall n : nat, BoolTrueT (Z.ltb 0 (pzz3 n))%Z.
Proof.
  intros n. apply boolTrueT_intro. apply Z.ltb_lt. unfold pzz3.
  assert (Hm : (0 <= Z.of_nat n)%Z) by lia.
  assert (H2 : (0 <= Z.of_nat n ^ 2)%Z) by (apply Z.pow_nonneg; lia).
  assert (H3 : (0 <= Z.of_nat n ^ 3)%Z) by (apply Z.pow_nonneg; lia).
  assert (H4 : (0 <= Z.of_nat n ^ 4)%Z) by (apply Z.pow_nonneg; lia).
  assert (Hp : (0 < 559455 * Z.of_nat n ^ 4 + 3399916 * Z.of_nat n ^ 3
                     + 7651391 * Z.of_nat n ^ 2 + 7554302 * Z.of_nat n
                     + 2760952)%Z) by lia.
  assert (Ha : (0 < 4 * Z.of_nat n + 11)%Z) by lia.
  assert (Hb : (0 < 3 * Z.of_nat n + 8)%Z) by lia.
  assert (Hc : (0 < 3 * Z.of_nat n + 7)%Z) by lia.
  assert (Hd : (0 < 4 * Z.of_nat n + 9)%Z) by lia.
  assert (He : (0 < Z.of_nat n + 3)%Z) by lia.
  assert (Hlit : (0 < 3)%Z) by lia.
  nia.
Qed.

(* ------------------------------------------------------------------ *)
(* Recurrence carrier: Q-valued sequences satisfying the recurrence     *)
(*   p0(n) u(n) + p1(n) u(n+1) + p2(n) u(n+2) + p3(n) u(n+3) = 0,      *)
(* with p3 nonzero everywhere and the initial values of the rational    *)
(* part C of E(n) = C(n) + D(n)*pi:                                     *)
(*   C(0) = 0, C(1) = 11272/15, C(2) = 6156093056/525                   *)
(* (oSALIKHOVpi3.txt:100-111; the D sequence carries the pi coefficients *)
(* D(0) = -1/20, D(1) = -1196/5, D(2) = -18662336/5).                   *)
(* ------------------------------------------------------------------ *)

Definition zq (z : Z) : Q := (z # 1)%Q.

Definition piu_zz_seq : Set :=
  { u : nat -> Q &
      (forall n : nat,
         QeqT (zq (pzz0 n) * u n + zq (pzz1 n) * u (S n)
               + zq (pzz2 n) * u (S (S n)) + zq (pzz3 n) * u (S (S (S n))))
              0%Q)
    * (forall n : nat, QneqT (zq (pzz3 n)) 0%Q)
    * (QeqT (u 0%nat) (0 # 1)%Q
       * QeqT (u 1%nat) (11272 # 15)%Q
       * QeqT (u 2%nat) (6156093056 # 525)%Q) }.

(* ------------------------------------------------------------------ *)
(* Rational power for the cage predicate: transparent Fixpoint.         *)
(* ------------------------------------------------------------------ *)

Fixpoint piu_zz_qpow (q : Q) (n : nat) : Q :=
  match n with
  | 0%nat => 1%Q
  | S k => q * piu_zz_qpow q k
  end.

(* Sub-lemma L0c: positivity is preserved by rational powers. *)
Lemma piu_zz_qpow_pos : forall (n : nat) (q : Q), (0 < q)%Q ->
  QltT 0%Q (piu_zz_qpow q n).
Proof.
  intros n q Hq. induction n as [|k IH].
  - apply qltT_intro. simpl. unfold Qlt. reflexivity.
  - apply qltT_intro. simpl. destruct IH as [IH].
    apply Qmult_lt_0_compat; assumption.
Qed.

(* ------------------------------------------------------------------ *)
(* Characteristic polynomial and root objects.                          *)
(*                                                                      *)
(* The four coefficient polynomials share the common degree 9, so the   *)
(* constant-coefficient limit recurrence is governed by the ratios of   *)
(* leading coefficients. The normalized characteristic polynomial is    *)
(*   lambda^3 + Ainf*lambda^2 + Binf*lambda + Cinf with                 *)
(*   Ainf = -2359989/108, Binf = 138304/108, Cinf = -2048/108,          *)
(* and its integer-coefficient commuted form is exactly the negative of *)
(* the indicial polynomial of oSALIKHOVpi3.txt:138-147                  *)
(*   108*lambda^3 - 2359989*lambda^2 + 138304*lambda - 2048.            *)
(* ------------------------------------------------------------------ *)

Definition piu_zz_Ainf : Q := ((-2359989) # 108)%Q.
Definition piu_zz_Binf : Q := (138304 # 108)%Q.
Definition piu_zz_Cinf : Q := ((-2048) # 108)%Q.

Definition piu_zz_charpoly (lam : Q) : Q :=
  (piu_zz_qpow lam 3 + piu_zz_Ainf * piu_zz_qpow lam 2
   + piu_zz_Binf * lam + piu_zz_Cinf)%Q.

Definition piu_zz_charpoly_int (lam : Q) : Q :=
  (108 * (lam * lam * lam) - 2359989 * (lam * lam)
   + 138304 * lam - 2048)%Q.

(* Sub-lemma L0d (commutation): the normalized and integer forms agree up
   to the nonzero integral scale 108. *)
Lemma piu_zz_charpoly_commuted : forall lam : Q,
  QeqT (108 * piu_zz_charpoly lam)%Q (piu_zz_charpoly_int lam).
Proof.
  intros lam. apply qeqT_intro.
  unfold piu_zz_charpoly, piu_zz_Ainf, piu_zz_Binf, piu_zz_Cinf,
    piu_zz_charpoly_int.
  cbn [piu_zz_qpow]. ring.
Qed.

(* Sub-lemma L0d (leading-coefficient commensuration quadruple): the scale
   2237820 sends the four coefficients of the indicial polynomial to the
   leading coefficients of p3, p2, p1, p0 in exact integer arithmetic
   (2237820 = p3*/108 with p3* = 241684560 = 3*4*3^3*4*559455). Literal
   kernel-level identities; the reading of the leading coefficients out of
   the factorized forms of pzz0..pzz3 is sub-lemma L1a, reserved. *)
Lemma piu_zz_lead_coeff_commensuration :
  BoolTrueT ((Z.eqb (2237820 * 108) 241684560)%Z
   && (Z.eqb (2237820 * 2359989) 5281230583980)%Z
   && (Z.eqb (2237820 * 138304) 309499457280)%Z
   && (Z.eqb (2237820 * 2048) 4583055360)%Z).
Proof. apply boolTrueT_intro. reflexivity. Qed.

Lemma piu_zz_scale_nonzero :
  BoolTrueT (negb (Z.eqb 108 0)%Z && negb (Z.eqb 241684560 0)%Z).
Proof. apply boolTrueT_intro. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Vieta readings in purely rational decidable form.                    *)
(*                                                                      *)
(* Given one root z of the characteristic polynomial, the remaining     *)
(* quadratic factor is lambda^2 + s(z)*lambda + t(z) with               *)
(*   s(z) = (-108*z + 2359989)/108   (sum of the two remaining roots),  *)
(*   t(z) = (108*z^2 - 2359989*z + 138304)/108 (their product).         *)
(* For the actual root pattern — one large real root N3 and a conjugate *)
(* pair of modulus |N1| — the pair product equals |N1|^2, so the root   *)
(* product identity below mechanizes |N1|*|N1|*N3 = 512/27, i.e.        *)
(* |N1|^2 = 512/(27*N3), exactly and over Q alone (no complex analysis  *)
(* and no floating constants).                                          *)
(* ------------------------------------------------------------------ *)

Definition piu_zz_vieta_small_sum (z : Q) : Q :=
  ((-108 * z + 2359989) * (1 # 108))%Q.

Definition piu_zz_vieta_small_prod (z : Q) : Q :=
  ((108 * (z * z) - 2359989 * z + 138304) * (1 # 108))%Q.

(* Sub-lemma L0b (Vieta readings, structural identities; no premises). *)
Lemma piu_zz_vieta_root_sum : forall z : Q,
  QeqT ((z + piu_zz_vieta_small_sum z)%Q) ((2359989 # 108)%Q).
Proof. intros z. apply qeqT_intro. unfold piu_zz_vieta_small_sum. ring. Qed.

Lemma piu_zz_vieta_root_pair : forall z : Q,
  QeqT ((piu_zz_vieta_small_prod z + z * piu_zz_vieta_small_sum z)%Q)
       ((138304 # 108)%Q).
Proof. intros z. apply qeqT_intro.
  unfold piu_zz_vieta_small_prod, piu_zz_vieta_small_sum. ring. Qed.

(* Sub-lemma L0b (root product identity): if z is a root then
   z * t(z) = 512/27; this is the exact rational content of the identity
   N1*N2*N3 = -Cinf = 2048/108 = 512/27. *)
Lemma piu_zz_vieta_root_prod : forall z : Q,
  piu_zz_charpoly_int z == 0%Q ->
  QeqT ((z * piu_zz_vieta_small_prod z)%Q) ((512 # 27)%Q).
Proof.
  intros z H. apply qeqT_intro.
  unfold piu_zz_charpoly_int in H.
  unfold piu_zz_vieta_small_prod.
  transitivity ((108 * (z * z * z) - 2359989 * (z * z) + 138304 * z)
                * (1 # 108))%Q.
  - ring.
  - transitivity ((108 * (z * z * z) - 2359989 * (z * z) + 138304 * z
                   - 2048 + 2048) * (1 # 108))%Q.
    + ring.
    + rewrite H. ring.
Qed.

(* Numerical anchor of the same identity: 2048/108 = 512/27 over Q. *)
Lemma piu_zz_prod_value : QeqT ((2048 * (1 # 108))%Q) ((512 # 27)%Q).
Proof. apply qeqT_intro. ring. Qed.

(* ------------------------------------------------------------------ *)
(* Two-sided epsilon power cage: the compiled conclusion predicate of   *)
(* the engine theorem (statement-level freeze; see the outline below).  *)
(* ------------------------------------------------------------------ *)

Definition piu_zz_power_cage (rho : Q) (u : nat -> Q) : Set :=
  forall eps : Q, (0 < eps)%Q -> (eps < rho)%Q ->
    { N : nat & forall n : nat, (N <= n)%nat ->
        QleT' (Qabs (piu_zz_qpow (rho - eps) n)) (Qabs (u n))
        * QleT' (Qabs (u n)) (Qabs (piu_zz_qpow (rho + eps) n)) }.

(* ================================================================== *)
(* FROZEN STATEMENT — piu_zz_poincare_rootlimit                        *)
(* (proof core reserved for later parts; frozen here as a comment so   *)
(* that this compiled module carries no unproved claim; the            *)
(* conclusion predicate is compiled above)                             *)
(*                                                                     *)
(*   Theorem piu_zz_poincare_rootlimit :                               *)
(*     forall u : nat -> Q, piu_zz_seq u ->                            *)
(*     exists rho : Q, (0 < rho)%Q /\ piu_zz_power_cage rho u.         *)
(*                                                                     *)
(* Interpretation: rho is the maximal root modulus of the              *)
(* characteristic polynomial among the roots that carry the given      *)
(* solution — rho = N3 = 21851.69... for the growing sequences C, D    *)
(* unconditionally, and rho = |N1| = 0.0294... for the decaying        *)
(* sequence E under the bounded-input premise |E(n)| <= 1; in both     *)
(* cases the limit of |u(n)|^(1/n) exists and equals rho (Poincaré     *)
(* 1885; Elaydi 3rd ed., Poincaré-type theorem).                       *)
(*                                                                     *)
(* Proof outline (annotated; each step anchored to a sub-lemma):       *)
(*  1. Normalization. Write the recurrence as                          *)
(*     u(n+3) + A(n)u(n+2) + B(n)u(n+1) + C(n)u(n) = 0 with            *)
(*     A = p2/p3, B = p1/p3, C = p0/p3 (well-defined by L0a).          *)
(*  2. Coefficient convergence (L1a + L1b). A(n) -> Ainf, B(n) ->      *)
(*     Binf, C(n) -> Cinf with effective rational rates, since the     *)
(*     four coefficient polynomials share degree 9 and the limits are  *)
(*     ratios of leading coefficients; the rational values are pinned  *)
(*     to the indicial polynomial by the commensuration L0d.           *)
(*  3. Root geometry over Q (L0b + L2b). The three roots are one real  *)
(*     root N3 with N3 > 2000 (sign certificate + Sturm-type count     *)
(*     over Q) and a conjugate pair of modulus |N1| with               *)
(*     |N1|^2 = 512/(27*N3) < 1/100, whence |N1| < 1/10. Both sides    *)
(*     are separated from modulus 1, so the Poincaré premise holds.    *)
(*  4. Stability window (L2a + L2b). For eps > 0 small, scale          *)
(*     x(n) := u(n)/(rho+eps)^n; the scaled companion matrix tends to  *)
(*     the companion matrix of the scaled characteristic polynomial,   *)
(*     which is Schur-stable; the three-term Jury inequalities hold    *)
(*     with an explicit rational margin at r = rho ± eps.              *)
(*  5. Upper cage (L3a). A weighted maximum-norm induction from a      *)
(*     sufficiently large index gives |u(n)| <= (rho+eps)^n up to a    *)
(*     constant, the polynomial correction being absorbed by the       *)
(*     (1+eps)^n slack.                                                *)
(*  6. Lower cage (L3b). If a root of modulus rho carries a nonzero    *)
(*     component of the solution, the reversed recurrence (lambda      *)
(*     mapped to 1/lambda, same Jury machinery) gives                  *)
(*     |u(n)| >= (rho-eps)^n eventually; which modulus rho is          *)
(*     realized is decided by the bounded-input premise for the        *)
(*     decaying sequence (rho = |N1|) or fails to arise for the        *)
(*     growing sequences (rho = N3).                                   *)
(*  7. Assembly (L4). Steps 2-6 give exists rho, piu_zz_power_cage     *)
(*     rho u.                                                          *)
(*                                                                     *)
(* Sub-lemma checklist (statement shape / difficulty / proof outlook): *)
(*  L0a piu_zz_p3_pos — mechanical — Proved above.                       *)
(*  L0b piu_zz_vieta_root_prod/_sum/_pair + piu_zz_prod_value —        *)
(*      mechanical (Q ring) — Proved above.                              *)
(*  L0c piu_zz_qpow_pos — mechanical — Proved above.                     *)
(*  L0d piu_zz_charpoly_commuted + leading-coefficient commensuration  *)
(*      quadruple — mechanical (literal identities) — Proved above.      *)
(*  L1a leading-coefficient extraction: expand pzz0..pzz3 to power-sum *)
(*      form and read off the degree-9 coefficients (p3* = 241684560,  *)
(*      |p1*| = 309499457280, |p0*| = 4583055360, |p2*| =              *)
(*      5281230583980) — mechanical but verbose (integer ring          *)
(*      expansion, 13-15 digit coefficients) — provable next part.    *)
(*  L1b coefficient convergence: forall delta > 0, exists N0, forall   *)
(*      n >= N0, |A(n) - Ainf|, |B(n) - Binf|, |C(n) - Cinf| < delta   *)
(*      — medium (rational-function bounds from L1a) — provable.      *)
(*  L2a three-term Schur-Jury criterion over Q: necessary and          *)
(*      sufficient rational inequalities on (a, b, c, r) for all      *)
(*      roots of lambda^3 + a*lambda^2 + b*lambda + c to have modulus  *)
(*      < r — hard (stability core; constructive proof via the Jury    *)
(*      table) — provable but long.                                   *)
(*  L2b instantiation of L2a at r = rho ± eps with rational interval   *)
(*      certificates for (Ainf, Binf, Cinf), the location N3 > 2000    *)
(*      by a Sturm-type sign certificate, and the pair bound           *)
(*      |N1|^2 = 512/(27*N3) < 1/100 — mechanical given L2a.           *)
(*  L3a upper-cage induction (limsup half) — hard (companion-matrix    *)
(*      perturbation against L1b + L2b) — provable, research core.    *)
(*  L3b lower-cage half (liminf) via the reversed recurrence — hard,   *)
(*      same machinery as L3a — provable, research core.              *)
(*  L4 assembly into piu_zz_power_cage — medium bookkeeping —          *)
(*      provable.                                                     *)
(*  L5 instance debt: the concrete C and D sequences satisfy           *)
(*      piu_zz_seq (Fixpoint on the three base values; the C/D split   *)
(*      of E = C + D*pi uses the irrationality of pi, available in the  *)
(*      main tree) — medium — provable after joining the main tree.   *)
(* ================================================================== *)

(* ------------------------------------------------------------------ *)
(* Audit: assumption accounting and data-level extraction probe.        *)
(* ------------------------------------------------------------------ *)

Print Assumptions piu_zz_p3_pos.
Print Assumptions piu_zz_qpow_pos.
Print Assumptions piu_zz_charpoly_commuted.
Print Assumptions piu_zz_lead_coeff_commensuration.
Print Assumptions piu_zz_scale_nonzero.
Print Assumptions piu_zz_vieta_root_prod.
Print Assumptions piu_zz_vieta_root_sum.
Print Assumptions piu_zz_vieta_root_pair.
Print Assumptions piu_zz_prod_value.
Print Assumptions piu_zz_seq.

Extraction "piu_zz_engine_data.ml" pzz0 pzz1 pzz2 pzz3 piu_zz_qpow
  piu_zz_vieta_small_prod piu_zz_vieta_small_sum
  piu_zz_Ainf piu_zz_Binf piu_zz_Cinf.
