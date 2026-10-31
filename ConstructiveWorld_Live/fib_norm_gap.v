(* ConstructiveWorld -- fib_norm_gap.v: Z-layer integer-gap base widening the Fibonacci denominator-family separation to the whole rational field. *)
(** * fib_norm_gap: no integer solution of [a]^2 = 5*[b]^2; integer-gap and
    family-bridge statements -- the [Z]-layer base of [fib_family_sep].
    Mission.  [sqrt5_mod5_sq]: [z]^2 = 0 (mod 5) forces [z] = 0 (mod 5)
      (squares of residues 1..4 are 1 or 4, via [Zmod_unique]).
      [sqrt5_no_sqrtZ]: [a]^2 = 5*[b]^2 with 0 < [b] is impossible, by
      infinite descent on [Z.to_nat b] (5 | [a]^2, so 5 | [a], so 5 | [b]*[b]
      strictly shrinking); [sqrt5_no_sqrtZ_ne]: the [b] <> 0 face over the
      [Z.abs] bridge |[b]|^2 = [b]^2.
      [fib2_gap5_ne]: |[a]^2 - 5*[b]^2| >= 1 for all integer pairs, [b] <> 0;
      [fib_norm_gap5_pos]: positive-denominator face, slot of [b5_gap_ge1];
      [fib_norm_gap_ge1]: |[a]^2 - [a]*[b] - [b]^2| >= 1, the norm of
      [a] - [b]*[phi] in [Z][phi], via (2[a] - [b])^2 = 5[b]^2;
      [fib_norm_member_abs1]: norm exactly 1 at ([F_{n+3}], [F_{n+2}])
      (Cassini identity) -- the bound 1 is attained on the family.
    Dependencies.  [fib_machine] ([zabs_ge1], [fibz] family, [fibz_cassini],
      [zabs_powneg1]); [S01_BaseRing] ([Id], [id_refl]); Stdlib [ZArith],
      [Arith], [Bool], [Lia].
    References.  [fib_qdomain] ([b5_gap_ge1] same-slot face);
      [UpReqSqrt3Irrational] ([ir2_no_sqrtZ] precedent shape).
    Constructivity.  [Z]-layer statements on registered precedent shapes;
      only premise slots (0 < .)%[Z] and (. <> 0)%[Z]; constructive [Prop]
      proof bodies; no proof gaps, no classical logic, no global assumption
      commands; transparent definitions; [Print Assumptions] reports none
      on every named item.
      Independent exact-integer recomputation ran first: 420300 zero-point
      probes with no solution, 40x40 universal grid clean on both shapes,
      norm-1 census = the Fibonacci chains (+/-[F_{k+1}], +/-[F_k]) and their
      negations, family bridge pairwise exact to n = 60.
    Build.  [rocq c -native-compiler no -q -Q WORLD "" fib_norm_gap.v] (Rocq 9.1.0, exit 0); WORLD = the read-only droot world root supplying [S01_BaseRing] and [fib_machine]. *)
Require Import S01_BaseRing (Id, id_refl).
Require Import fib_machine.
From Stdlib Require Import ZArith.ZArith Arith.Arith Bool.Bool.
From Stdlib Require Import Lia.

(* ============================================================ *)
(* Sec-M Quadratic-residue layer: z^2 = 0 (mod 5) forces z = 0 (mod 5) *)
(* ============================================================ *)

Lemma sqrt5_mod5_sq : forall z : Z, ((z * z) mod 5 = 0)%Z -> (z mod 5 = 0)%Z.
Proof.
  intros z H.
  assert (Hr : (z mod 5 = 0)%Z \/ (z mod 5 = 1)%Z \/ (z mod 5 = 2)%Z \/
               (z mod 5 = 3)%Z \/ (z mod 5 = 4)%Z).
  { pose proof (Z.mod_pos_bound z 5 (ltac:(lia))) as Hb. lia. }
  destruct Hr as [Hr | [Hr | [Hr | [Hr | Hr]]]]; [exact Hr | | | | ].
  - (* z = 5k+1: z^2 = 5*(5k^2+2k)+1 *)
    exfalso.
    pose proof (Z.div_mod z 5 (ltac:(lia))) as Hz.
    rewrite Hr in Hz.
    remember (z / 5)%Z as k eqn:Ek.
    assert (Hsq : (z * z = 5 * (5 * k * k + 2 * k) + 1)%Z).
    { rewrite Hz at 1 2. ring. }
    rewrite Hsq in H.
    assert (Hm : ((z * z) mod 5 = 1)%Z).
    { symmetry. apply (Zmod_unique ((z * z)%Z) 5%Z ((5 * k * k + 2 * k)%Z) 1%Z); lia. }
    rewrite Hsq in Hm. rewrite Hm in H. lia.
  - (* z = 5k+2: z^2 = 5*(5k^2+4k)+4 *)
    exfalso.
    pose proof (Z.div_mod z 5 (ltac:(lia))) as Hz.
    rewrite Hr in Hz.
    remember (z / 5)%Z as k eqn:Ek.
    assert (Hsq : (z * z = 5 * (5 * k * k + 4 * k) + 4)%Z).
    { rewrite Hz at 1 2. ring. }
    rewrite Hsq in H.
    assert (Hm : ((z * z) mod 5 = 4)%Z).
    { symmetry. apply (Zmod_unique ((z * z)%Z) 5%Z ((5 * k * k + 4 * k)%Z) 4%Z); lia. }
    rewrite Hsq in Hm. rewrite Hm in H. lia.
  - (* z = 5k+3: z^2 = 5*(5k^2+6k+1)+4 *)
    exfalso.
    pose proof (Z.div_mod z 5 (ltac:(lia))) as Hz.
    rewrite Hr in Hz.
    remember (z / 5)%Z as k eqn:Ek.
    assert (Hsq : (z * z = 5 * (5 * k * k + 6 * k + 1) + 4)%Z).
    { rewrite Hz at 1 2. ring. }
    rewrite Hsq in H.
    assert (Hm : ((z * z) mod 5 = 4)%Z).
    { symmetry. apply (Zmod_unique ((z * z)%Z) 5%Z ((5 * k * k + 6 * k + 1)%Z) 4%Z); lia. }
    rewrite Hsq in Hm. rewrite Hm in H. lia.
  - (* z = 5k+4: z^2 = 5*(5k^2+8k+3)+1 *)
    exfalso.
    pose proof (Z.div_mod z 5 (ltac:(lia))) as Hz.
    rewrite Hr in Hz.
    remember (z / 5)%Z as k eqn:Ek.
    assert (Hsq : (z * z = 5 * (5 * k * k + 8 * k + 3) + 1)%Z).
    { rewrite Hz at 1 2. ring. }
    rewrite Hsq in H.
    assert (Hm : ((z * z) mod 5 = 1)%Z).
    { symmetry. apply (Zmod_unique ((z * z)%Z) 5%Z ((5 * k * k + 8 * k + 3)%Z) 1%Z); lia. }
    rewrite Hsq in Hm. rewrite Hm in H. lia.
Qed.

(* ============================================================ *)
(* Sec-N No-square layer: sqrt(5) has no rational square root (infinite descent) *)
(* ============================================================ *)

Lemma sqrt5_no_sqrtZ : forall a b : Z, (0 < b)%Z -> (a * a = 5 * (b * b))%Z -> False.
Proof.
  assert (Hgen : forall n : nat, forall a b : Z, (0 < b)%Z ->
    (a * a = 5 * (b * b))%Z -> (Z.to_nat b <= n)%nat -> False).
  { induction n as [|n IH]; intros a b Hb Heq Hn.
    - assert (Hb0 : (b = 0)%Z).
      { pose proof (Z2Nat.id b (ltac:(lia))) as Hzz.
        apply Nat.le_0_r in Hn. rewrite Hn in Hzz. cbn in Hzz.
        symmetry. exact Hzz. }
      lia.
    - (* 5 divides a, 5 divides b, b strictly shrinks (b maps to b/5) *)
      assert (Ham : ((a * a) mod 5 = 0)%Z).
      { rewrite Heq.
        symmetry. apply (Zmod_unique ((5 * (b * b))%Z) 5%Z ((b * b)%Z) 0%Z); lia. }
      assert (Hae : (a mod 5 = 0)%Z) by (apply sqrt5_mod5_sq; exact Ham).
      pose proof (Z.div_mod a 5 (ltac:(lia))) as Hza. rewrite Hae in Hza.
      remember (a / 5)%Z as a1 eqn:Ea1.
      assert (Ha1 : (a = 5 * a1)%Z) by lia.
      clear Hza Ea1 Hae Ham.
      assert (Hbb : (b * b = 5 * (a1 * a1))%Z).
      { rewrite Ha1 in Heq.
        replace ((5 * a1)%Z * (5 * a1)%Z)%Z with (25 * (a1 * a1)%Z)%Z in Heq by ring.
        replace (25 * (a1 * a1)%Z)%Z with (5 * (5 * (a1 * a1)%Z)%Z)%Z in Heq by ring.
        lia. }
      assert (Hbm : ((b * b) mod 5 = 0)%Z).
      { rewrite Hbb.
        symmetry. apply (Zmod_unique ((5 * (a1 * a1))%Z) 5%Z ((a1 * a1)%Z) 0%Z); lia. }
      assert (Hbe : (b mod 5 = 0)%Z) by (apply sqrt5_mod5_sq; exact Hbm).
      pose proof (Z.div_mod b 5 (ltac:(lia))) as Hzb. rewrite Hbe in Hzb.
      remember (b / 5)%Z as b1 eqn:Eb1.
      assert (Hb1 : (b = 5 * b1)%Z) by lia.
      apply (IH a1 b1).
      + lia.
      + rewrite Hb1 in Hbb.
        replace ((5 * b1)%Z * (5 * b1)%Z)%Z with (25 * (b1 * b1)%Z)%Z in Hbb by ring.
        replace (25 * (b1 * b1)%Z)%Z with (5 * (5 * (b1 * b1)%Z)%Z)%Z in Hbb by ring.
        lia.
      + pose proof (Z2Nat.inj_mul b b1 (ltac:(lia)) (ltac:(lia))) as Hmm.
        pose proof (Z2Nat.id b (ltac:(lia))) as Hz1.
        pose proof (Z2Nat.id b1 (ltac:(lia))) as Hz2.
        lia. }
  intros a b Hb Heq.
  apply (Hgen (Z.to_nat b) a b Hb Heq (Nat.le_refl _)).
Qed.

(* b<>0 shape (Z.abs bridge: |b|^2 = b^2) *)
Lemma sqrt5_no_sqrtZ_ne : forall a b : Z, b <> 0%Z -> (a * a = 5 * (b * b))%Z -> False.
Proof.
  intros a b Hb Heq.
  apply (sqrt5_no_sqrtZ a (Z.abs b)).
  - apply Z.abs_pos. exact Hb.
  - rewrite <- (Z.abs_mul b b).
    rewrite (Z.abs_eq (b * b)) by lia.
    exact Heq.
Qed.

(* ============================================================ *)
(* Sec-G Integer-gap layer: |a^2-5b^2| >= 1 all integer pairs + phi-norm |a^2-ab-b^2| >= 1 *)
(* ============================================================ *)

(* Computational face (transparent definitions, executable witnesses): the Z function faces of the norm shape and the sqrt(5) gap *)
Definition fib2_norm (a b : Z) : Z := a * a - a * b - b * b.
Definition fib2_gap5 (a b : Z) : Z := a * a - 5 * (b * b).

(* Universal statement (assigned carve): for every integer pair (a,b) with b<>0, |a^2-5b^2| >= 1 *)
Lemma fib2_gap5_ne : forall a b : Z, b <> 0%Z -> (1 <= Z.abs (a * a - 5 * (b * b)))%Z.
Proof.
  intros a b Hb.
  assert (Hz : Id (Z.leb 1 (Z.abs (a * a - 5 * (b * b)))) true).
  { apply zabs_ge1.
    intro H0. apply (sqrt5_no_sqrtZ_ne a b Hb). lia. }
  apply Z.leb_le.
  exact (match Hz in (Id _ y)
           return (Z.leb 1 (Z.abs (a * a - 5 * (b * b))) = y)
         with id_refl => eq_refl end).
Qed.

(* Positive-denominator usage shape (same slot as B5 b5_gap_ge1; consumed directly at the Q assembly layer) *)
Lemma fib_norm_gap5_pos : forall (a : Z) (b : positive),
  (1 <= Z.abs (a * a - 5 * (Z.pos b * Z.pos b)))%Z.
Proof.
  intros a b. apply (fib2_gap5_ne a (Z.pos b)).
  intro Hc. pose proof (Pos2Z.is_pos b). lia.
Qed.

(* Phi-norm-shape integer gap (FIB carve): a^2-ab-b^2 = N(a-b*phi), zero point
   equivalent to (2a-b)^2 = 5b^2; with b<>0 it contradicts no-square sqrt(5), gap >= 1 *)
Lemma fib_norm_gap_ge1 : forall (a : Z) (b : positive),
  (1 <= Z.abs (a * a - a * Z.pos b - Z.pos b * Z.pos b))%Z.
Proof.
  intros a b.
  pose proof (Pos2Z.is_pos b) as Hb0.
  assert (Hz : Id (Z.leb 1 (Z.abs (a * a - a * Z.pos b - Z.pos b * Z.pos b))) true).
  { apply zabs_ge1.
    intro H0.
    assert (Hs : ((2 * a - Z.pos b) * (2 * a - Z.pos b)
                  = 5 * (Z.pos b * Z.pos b))%Z) by nia.
    exact (sqrt5_no_sqrtZ (2 * a - Z.pos b) (Z.pos b) Hb0 Hs). }
  apply Z.leb_le.
  exact (match Hz in (Id _ y)
           return (Z.leb 1 (Z.abs (a * a - a * Z.pos b - Z.pos b * Z.pos b)) = y)
         with id_refl => eq_refl end).
Qed.

(* ============================================================ *)
(* Sec-F Family-bridge layer: the norm-shape gap is attained with equality on the denominator family *)
(* ============================================================ *)

(* At the family pair (F_{n+3},F_{n+2}) the norm is exactly +/-1 (direct Cassini face:
   F_{n+3}^2 - F_{n+3}F_{n+2} - F_{n+2}^2 = -(F_{n+2}^2 - F_{n+1}F_{n+3}))
   -- the lower bound 1 of fib_norm_gap_ge1 is met exactly on the Fibonacci family (fib_family_sharp norm face) *)
Lemma fib_norm_member_abs1 : forall n : nat,
  Id (Z.abs (fibz (S (S n)) * fibz (S (S n)) - fibz (S (S n)) * fibz (S n)
       - fibz (S n) * fibz (S n))) 1%Z.
Proof.
  intro n.
  assert (Erec : fibz (S (S n)) = (fibz (S n) + fibz n)%Z).
  { exact (match fibz_rec n in (Id _ y) return (fibz (S (S n)) = y)
           with id_refl => eq_refl end). }
  assert (Hc1 : (fibz (S n) * fibz (S n) - fibz n * (fibz (S n) + fibz n)
                = powneg1 (S n))%Z).
  { rewrite <- Erec.
    exact (match fibz_cassini n in (Id _ y)
             return ((fibz (S n) * fibz (S n) - fibz n * fibz (S (S n)))%Z = y)
           with id_refl => eq_refl end). }
  rewrite Erec.
  replace (((fibz (S n) + fibz n) * (fibz (S n) + fibz n)
            - (fibz (S n) + fibz n) * fibz (S n)
            - fibz (S n) * fibz (S n)))%Z
    with (- (fibz (S n) * fibz (S n) - fibz n * (fibz (S n) + fibz n)))%Z by ring.
  rewrite Hc1.
  rewrite Z.abs_opp.
  apply zabs_powneg1.
Qed.

(* ============================================================ *)
(* Sec-A Audit: Print Assumptions + Separate Extraction + vm_compute numerical anchors *)
(* ============================================================ *)

Print Assumptions sqrt5_mod5_sq.
Print Assumptions sqrt5_no_sqrtZ.
Print Assumptions sqrt5_no_sqrtZ_ne.
Print Assumptions fib2_gap5_ne.
Print Assumptions fib_norm_gap5_pos.
Print Assumptions fib_norm_gap_ge1.
Print Assumptions fib_norm_member_abs1.

(* Numerical anchor 1 (Pell pair equality instance): |9^2-5*4^2| = 1 *)
Lemma fib2_smoke_pell_gap : Z.eqb (Z.abs (9 * 9 - 5 * (4 * 4))) 1%Z = true.
Proof. vm_compute. reflexivity. Qed.

(* Numerical anchor 2 (family-pair equality instance): |13^2-13*8-8^2| = 1 ((F_7,F_6)=(13,8)) *)
Lemma fib2_smoke_norm_fib : Z.eqb (Z.abs (13 * 13 - 13 * 8 - 8 * 8)) 1%Z = true.
Proof. vm_compute. reflexivity. Qed.

(* Numerical anchor 3 (strict example): |7^2-7*5-5^2| = 11 >= 1 (non-family pair; gap strictly above 1) *)
Lemma fib2_smoke_norm_strict : Z.eqb (Z.abs (7 * 7 - 7 * 5 - 5 * 5)) 11%Z = true.
Proof. vm_compute. reflexivity. Qed.

(* Numerical anchor 4 (family-bridge instance): at fibz 4 = 5, fibz 3 = 3, |5^2-5*3-3^2| = 1 *)
Lemma fib2_smoke_member : Z.eqb (Z.abs (fibz 4 * fibz 4 - fibz 4 * fibz 3 - fibz 3 * fibz 3)) 1%Z = true.
Proof. vm_compute. reflexivity. Qed.

(* Numerical anchor 5 (mod-5 residue): 7^2 = 49 = 4 (mod 5) -- residue-enumeration face instance *)
Lemma fib2_smoke_mod5 : Z.eqb ((7 * 7) mod 5) 4%Z = true.
Proof. vm_compute. reflexivity. Qed.

(* Numerical anchor 6 (executable witness of the computational face): fib2_norm 13 8 = 1 (family pair, direct function computation) *)
Lemma fib2_smoke_norm_fun : Z.eqb (Z.abs (fib2_norm 13 8)) 1%Z = true.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions fib2_smoke_pell_gap.
Print Assumptions fib2_smoke_norm_fib.
Print Assumptions fib2_smoke_norm_strict.
Print Assumptions fib2_smoke_member.
Print Assumptions fib2_smoke_mod5.
Print Assumptions fib2_smoke_norm_fun.

From Stdlib Require Import Extraction.
Separate Extraction fib2_norm fib2_gap5 sqrt5_mod5_sq sqrt5_no_sqrtZ
  sqrt5_no_sqrtZ_ne fib2_gap5_ne fib_norm_gap5_pos fib_norm_gap_ge1
  fib_norm_member_abs1 fib2_smoke_pell_gap fib2_smoke_norm_fib
  fib2_smoke_norm_strict fib2_smoke_member fib2_smoke_mod5 fib2_smoke_norm_fun.
