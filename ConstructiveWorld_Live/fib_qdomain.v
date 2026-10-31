(* fib_qdomain.v -- rational-field gap assembly: |a^2 - D*b^2| >= 1     *)
(* (2 <= D, D a non-square, b <> 0), zero premises, by the              *)
(* Hardy-Wright one-step contradiction (lowest terms + gcd + Gauss +    *)
(* floor bound), D=2 / D=5 generalized; plus |(a/b)^2 - D| >= 1/b^2     *)
(* on the QleT' Set carrier, never naming a square root of D.           *)
(* Mission.  Sec F floor bound sqrtD_floor (m := Z.sqrt D).  Sec Z      *)
(* genD_no_sqrtZ / _ne: a^2 = D*b^2 with b <> 0 has no solution.        *)
(* Sec M sqrt2_nonsquare, sqrt3_nonsquare (even/odd case split),        *)
(* sqrt5_nonsquare.  Sec G gap layer genD_gap, genD_gapQ,               *)
(* gen_gapD_ne / _pos / _2 / _3 / _5.  Sec Q q_square_cross,            *)
(* q_square_gap.  Sec A audit block.                                    *)
(* Dependencies.  S02_CauchyComplete (QleT'), fib_machine (zabs_ge1,    *)
(* fib_qabs_congr, fib_qle_abs_ge, fib_qleT_congr_r), fib_norm_gap      *)
(* (sqrt5_no_sqrtZ), S01_BaseRing (Id, id_refl, And); Stdlib ZArith,    *)
(* Arith, Bool, Lia, QArith, Qabs -- the in-file Require list.          *)
(* References.  genD_no_sqrtZ engine: Z.abs normalization; lowest       *)
(* terms (Z.gcd_divide_l/r, Z.div_unique, Z.gcd_div_gcd); floor         *)
(* bound m*k2 < k1 < (m+1)*k2; supply k2 | k1*(k1 + m*k2); then         *)
(* Z.gauss: k2 | k1 with 0 < k1 - m*k2 < k2, impossible.                *)
(* Audit: Print Assumptions x21, Separate Extraction, vm_compute        *)
(* anchors.  Machine parallels: b5_machine, fib_machine, fib_norm_gap.  *)
(* Constructivity.  Statements carry Id / QleT' (Set); Prop occurs      *)
(* in proofs only.  The -> False conclusions generalize registered      *)
(* same-shape precedents ir2_no_sqrtZ / sqrt5_no_sqrtZ; the slots       *)
(* (2 <= D), (forall c, D <> c^2), (b <> 0) reuse them.  No             *)
(* admission-style statements, no global premises, no classical         *)
(* logic, definitions transparent; Print Assumptions at file end        *)
(* reports all results Closed.                                          *)
(* Build.  rocq c -native-compiler no -q -Q <world root> ""             *)
(* fib_qdomain.v (Rocq 9.1.0), same-world dependency .vo chain.         *)

Require Import S02_CauchyComplete.
Require Import fib_machine.
Require Import fib_norm_gap.
Require Import S01_BaseRing (Id, id_refl, And).
From Stdlib Require Import ZArith.ZArith Arith.Arith Bool.Bool.
From Stdlib Require Import Lia QArith.QArith QArith.Qabs.

(* ============================================================ *)
(* Sec F. Floor-bound piece: strict two-sided Z.sqrt bounds for a non-square D. *)
(* ============================================================ *)

Lemma sqrtD_floor : forall D : Z, (2 <= D)%Z -> (forall c : Z, (D <> c * c)%Z) ->
  And (Id (Z.ltb (Z.sqrt D * Z.sqrt D) D) true)
      (Id (Z.ltb D (Z.succ (Z.sqrt D) * Z.succ (Z.sqrt D))) true).
Proof.
  intros D HD Hns.
  assert (HD0 : (0 <= D)%Z) by lia.
  pose proof (Z.sqrt_spec D HD0) as H. cbv zeta in H.
  pose proof (Hns (Z.sqrt D)) as Hne.
  split.
  - assert (Hlt : (Z.sqrt D * Z.sqrt D < D)%Z) by lia.
    pose proof (proj2 (Z.ltb_lt (Z.sqrt D * Z.sqrt D) D) Hlt) as Hltb.
    rewrite Hltb. apply id_refl.
  - pose proof (proj2 (Z.ltb_lt D
        (Z.succ (Z.sqrt D) * Z.succ (Z.sqrt D))) (proj2 H)) as Hltb.
    rewrite Hltb. apply id_refl.
Qed.

(* ============================================================ *)
(* Sec Z. General no-square-root layer: a non-square D has no
   integer square root (lowest terms + one-step Gauss). *)
(* ============================================================ *)

Lemma genD_no_sqrtZ : forall (D a b : Z), (2 <= D)%Z ->
  (forall c : Z, (D <> c * c)%Z) -> (0 < b)%Z -> (a * a = D * (b * b))%Z -> False.
Proof.
  intros D a b HD Hns Hb Heq.
  assert (Hfl := sqrtD_floor D HD Hns).
  assert (HflP : (Z.sqrt D * Z.sqrt D < D
                  < Z.succ (Z.sqrt D) * Z.succ (Z.sqrt D))%Z).
  { destruct Hfl as [Hf1 Hf2]. split.
    - apply (proj1 (Z.ltb_lt (Z.sqrt D * Z.sqrt D) D)).
      exact (match Hf1 in (Id _ y)
               return (Z.ltb (Z.sqrt D * Z.sqrt D) D = y)
             with id_refl => eq_refl end).
    - apply (proj1 (Z.ltb_lt D (Z.succ (Z.sqrt D) * Z.succ (Z.sqrt D)))).
      exact (match Hf2 in (Id _ y)
               return (Z.ltb D (Z.succ (Z.sqrt D) * Z.succ (Z.sqrt D)) = y)
             with id_refl => eq_refl end). }
  pose proof (Z.abs_square a) as Habs.
  assert (Ha0 : (Z.abs a * Z.abs a = D * (b * b))%Z) by (rewrite Habs; exact Heq).
  assert (Ha0p : (0 <= Z.abs a)%Z) by apply Z.abs_nonneg.
  (* Lowest terms: g := gcd(|a|, b), divisibility witnesses k1/k2 *)
  assert (Hg0 : (0 < Z.gcd (Z.abs a) b)%Z).
  { pose proof (Z.gcd_nonneg (Z.abs a) b) as H1.
    assert (H2 : Z.gcd (Z.abs a) b <> 0%Z).
    { intro Hc. apply (Z.gcd_eq_0 (Z.abs a) b) in Hc. lia. }
    lia. }
  pose proof (Z.gcd_div_gcd (Z.abs a) b (Z.gcd (Z.abs a) b)
              (ltac:(lia)) eq_refl) as Hcop0.
  pose proof (Z.gcd_divide_l (Z.abs a) b) as Hda.
  pose proof (Z.gcd_divide_r (Z.abs a) b) as Hdb.
  unfold Z.divide in Hda, Hdb.
  destruct Hda as [k1 Hk1]. destruct Hdb as [k2 Hk2].
  remember (Z.gcd (Z.abs a) b) as g eqn:Eg.
  (* Quotient recovery: |a| / g = k1 and b / g = k2 *)
  assert (Hq1 : (Z.abs a / g = k1)%Z).
  { symmetry. apply Z.div_unique with (r := 0%Z).
    - left. lia.
    - lia. }
  assert (Hq2 : (b / g = k2)%Z).
  { symmetry. apply Z.div_unique with (r := 0%Z).
    - left. lia.
    - lia. }
  rewrite Hq1, Hq2 in Hcop0.
  (* Equation transfer and positivity *)
  assert (Heq1 : (k1 * k1 = D * (k2 * k2))%Z).
  { rewrite Hk1, Hk2 in Ha0. nia. }
  assert (Hk2p : (0 < k2)%Z) by nia.
  assert (Hk1p : (0 < k1)%Z) by nia.
  (* Floor bound: m*k2 < k1 < (m+1)*k2 *)
  assert (Hfl2 : (Z.sqrt D * Z.sqrt D < D)%Z) by lia.
  assert (Hfl3 : (D < (Z.sqrt D + 1) * (Z.sqrt D + 1))%Z) by lia.
  remember (Z.sqrt D) as m eqn:Em.
  assert (Hm0 : (0 <= m)%Z) by (rewrite Em; apply Z.sqrt_nonneg).
  assert (Hfb : (m * k2 < k1 < (m + 1) * k2)%Z).
  { split; nia. }
  (* Cross-multiplied supply + one-step Gauss contradiction *)
  assert (Hcr : (k1 * (k1 + m * k2) = k2 * (m * k1 + D * k2))%Z).
  { replace (k1 * (k1 + m * k2))%Z with (k1 * k1 + m * k1 * k2)%Z by ring.
    rewrite Heq1. ring. }
  assert (Hsup : Z.divide k2 (k1 * (k1 + m * k2))).
  { unfold Z.divide. exists ((m * k1 + D * k2)%Z). lia. }
  assert (Hcop1 : Z.gcd k2 k1 = 1%Z) by (rewrite Z.gcd_comm; exact Hcop0).
  pose proof (Z.gauss k2 k1 (k1 + m * k2) Hsup Hcop1) as Hg1.
  assert (Hdm : Z.divide k2 (m * k2)) by
    (unfold Z.divide; exists (m%Z); ring).
  assert (Hgk1 : Z.divide k2 k1).
  { replace k1%Z with ((k1 + m * k2) + (-(m * k2)))%Z by ring.
    apply Z.divide_add_r. exact Hg1. apply Z.divide_opp_r. exact Hdm. }
  assert (Hgu : Z.divide k2 (k1 - m * k2)).
  { replace (k1 - m * k2)%Z with (k1 + (-(m * k2)))%Z by ring.
    apply Z.divide_add_r. exact Hgk1. apply Z.divide_opp_r. exact Hdm. }
  (* Endgame: 0 < u < k2 with k2 | u is impossible *)
  unfold Z.divide in Hgu. destruct Hgu as [k Hk].
  destruct k as [|p|p].
  - lia.
  - pose proof (Pos2Z.is_pos p). nia.
  - pose proof (Pos2Z.is_pos p). nia.
Qed.

(* b <> 0 form (Z.abs bridge; same shape as sqrt5_no_sqrtZ_ne in fib_norm_gap) *)
Lemma genD_no_sqrtZ_ne : forall (D a b : Z), (2 <= D)%Z ->
  (forall c : Z, (D <> c * c)%Z) -> b <> 0%Z -> (a * a = D * (b * b))%Z -> False.
Proof.
  intros D a b HD Hns Hb Heq.
  apply (genD_no_sqrtZ D a (Z.abs b) HD Hns).
  - apply Z.abs_pos. exact Hb.
  - rewrite <- (Z.abs_mul b b). rewrite (Z.abs_eq (b * b)) by lia. exact Heq.
Qed.

(* ============================================================ *)
(* Sec M. Even/odd non-square instances (D = 2,3 mod 4) + sqrt5 pool reuse *)
(* ============================================================ *)

Lemma sqrt2_nonsquare : forall c : Z, (2 <> c * c)%Z.
Proof.
  intro c. destruct (Z.Even_or_Odd c) as [[k Hk] | [k Hk]].
  - subst c. lia.
  - subst c. assert (Hx : ((2*k+1)*(2*k+1) = 4*(k*k) + 4*k + 1)%Z) by ring. lia.
Qed.

Lemma sqrt3_nonsquare : forall c : Z, (3 <> c * c)%Z.
Proof.
  intro c. destruct (Z.Even_or_Odd c) as [[k Hk] | [k Hk]].
  - subst c. lia.
  - subst c. assert (Hx : ((2*k+1)*(2*k+1) = 4*(k*k) + 4*k + 1)%Z) by ring. lia.
Qed.

(* Direct reuse of the library sqrt5_no_sqrtZ (one step at b := 1) *)
Lemma sqrt5_nonsquare : forall c : Z, (5 <> c * c)%Z.
Proof.
  intro c. intro Hc. apply (sqrt5_no_sqrtZ c 1%Z); [ lia | lia ].
Qed.

(* ============================================================ *)
(* Sec G. General integer-gap layer |a^2 - D*b^2| >= 1 (b <> 0, *)
(* D non-square) + special cases obtained directly. *)
(* ============================================================ *)

(* Computational face (transparent definitions, executable witnesses) *)
Definition genD_gap (D a b : Z) : Z := a * a - D * (b * b).
Definition genD_gapQ (D : Z) (a : Z) (b : positive) : Q :=
  (genD_gap D a (Z.pos b) # (b * b))%Q.

(* Universal form: for all integers a, b with b <> 0: |a^2 - D*b^2| >= 1 *)
Lemma gen_gapD_ne : forall (D a b : Z), (2 <= D)%Z ->
  (forall c : Z, (D <> c * c)%Z) -> b <> 0%Z ->
  Id (Z.leb 1 (Z.abs (a * a - D * (b * b)))) true.
Proof.
  intros D a b HD Hns Hb. apply zabs_ge1.
  intro H0. apply (genD_no_sqrtZ_ne D a b HD Hns Hb). lia.
Qed.

(* Positive-denominator use form (same slot as b5_gap_ge1 / fib_norm_gap5_pos) *)
Lemma gen_gapD_pos : forall (D a : Z) (b : positive), (2 <= D)%Z ->
  (forall c : Z, (D <> c * c)%Z) ->
  Id (Z.leb 1 (Z.abs (a * a - D * (Z.pos b * Z.pos b)))) true.
Proof.
  intros D a b HD Hns. apply (gen_gapD_ne D a (Z.pos b) HD Hns).
  intro Hc. pose proof (Pos2Z.is_pos b). lia.
Qed.

(* D = 2 special case, direct (generalizes the |a^2 - 2*b^2| >= 1 bound) *)
Lemma gen_gapD_2 : forall a b : Z, b <> 0%Z ->
  Id (Z.leb 1 (Z.abs (a * a - 2 * (b * b)))) true.
Proof.
  intros a b Hb. apply (gen_gapD_ne 2 a b); [ lia | exact sqrt2_nonsquare | exact Hb ].
Qed.

(* D = 3 special case, direct *)
Lemma gen_gapD_3 : forall a b : Z, b <> 0%Z ->
  Id (Z.leb 1 (Z.abs (a * a - 3 * (b * b)))) true.
Proof.
  intros a b Hb. apply (gen_gapD_ne 3 a b); [ lia | exact sqrt3_nonsquare | exact Hb ].
Qed.

(* D = 5 special case, direct (re-derives the general form of fib2_gap5_ne) *)
Lemma gen_gapD_5 : forall a b : Z, b <> 0%Z ->
  Id (Z.leb 1 (Z.abs (a * a - 5 * (b * b)))) true.
Proof.
  intros a b Hb. apply (gen_gapD_ne 5 a b); [ lia | exact sqrt5_nonsquare | exact Hb ].
Qed.

(* ============================================================ *)
(* Sec Q. Full rational-field assembly layer:
   |(a/b)^2 - D| >= 1/b^2 (QleT' all-Set carrier). *)
(* ============================================================ *)

(* Qeq cross identity (square form of fib_cross_mult) *)
Lemma q_square_cross : forall (a D0 : Z) (b : positive),
  QeqT ((a # b)%Q * (a # b)%Q - (D0 # 1))%Q
       ((a*a - D0*(Z.pos b * Z.pos b)) # (b * b))%Q.
Proof.
  intros a D0 b.
  assert (Hcore : ((a # b)%Q * (a # b)%Q - (D0 # 1))%Q
                  == ((a*a - D0*(Z.pos b * Z.pos b)) # (b * b))%Q).
  { unfold Qeq, Qminus, Qmult, Qopp, Qplus, Qnum, Qden. cbn.
    lia. }
  apply qeq_imp_qeqT. exact Hcore.
Qed.

(* Main statement of the rational-field assembly: for any rational a/b, *)
(* its square stays at distance >= 1/b^2 from D (no square root of D *)
(* named; all-Set carrier; general-D form of the separation *)
(* certificates). *)
Lemma q_square_gap : forall (D : Z) (a : Z) (b : positive), (2 <= D)%Z ->
  (forall c : Z, (D <> c * c)%Z) ->
  QleT' (Qinv ((Z.pos b * Z.pos b) # 1))
        (Qabs (((a # b)%Q * (a # b)%Q - (D # 1))%Q)).
Proof.
  intros D a b HD Hns.
  assert (Hgap := gen_gapD_pos D a b HD Hns).
  assert (HgapP : (1 <= Z.abs (a * a - D * (Z.pos b * Z.pos b)))%Z).
  { apply Z.leb_le.
    exact (match Hgap in (Id _ y)
             return (Z.leb 1 (Z.abs (a * a - D * (Z.pos b * Z.pos b))) = y)
           with id_refl => eq_refl end). }
  apply (fib_qleT_congr_r
        (Qabs ((a*a - D*(Z.pos b * Z.pos b)) # (b * b))%Q)
        (Qabs (((a # b)%Q * (a # b)%Q - (D # 1))%Q))
        (Qinv ((Z.pos b * Z.pos b) # 1)%Q)).
  - apply qeqT_imp_qeq. apply fib_qabs_congr.
    apply Qeq_sym. apply qeqT_imp_qeq. apply (q_square_cross a D).
  - exact (fib_qle_abs_ge (b * b)%positive
      (a * a - D * (Z.pos b * Z.pos b)) HgapP).
Qed.

(* ============================================================ *)
(* Sec A. Audit: Print Assumptions + Separate Extraction +
   vm_compute numerical anchors. *)
(* ============================================================ *)

Print Assumptions sqrtD_floor.
Print Assumptions genD_no_sqrtZ.
Print Assumptions genD_no_sqrtZ_ne.
Print Assumptions sqrt2_nonsquare.
Print Assumptions sqrt3_nonsquare.
Print Assumptions sqrt5_nonsquare.
Print Assumptions gen_gapD_ne.
Print Assumptions gen_gapD_pos.
Print Assumptions gen_gapD_2.
Print Assumptions gen_gapD_3.
Print Assumptions gen_gapD_5.
Print Assumptions q_square_cross.
Print Assumptions q_square_gap.

(* Numerical anchor 1 (Pell pair, D = 2): |3^2 - 2*2^2| = 1 *)
Lemma smoke_gapD2 : Id (Z.eqb (Z.abs (3 * 3 - 2 * (2 * 2))) 1%Z) true.
Proof. vm_compute. apply id_refl. Qed.

(* Numerical anchor 2 (Pell pair, D = 3): |7^2 - 3*4^2| = 1 *)
Lemma smoke_gapD3 : Id (Z.eqb (Z.abs (7 * 7 - 3 * (4 * 4))) 1%Z) true.
Proof. vm_compute. apply id_refl. Qed.

(* Numerical anchor 3 (Pell pair, D = 5): |9^2 - 5*4^2| = 1, via the general form *)
Lemma smoke_gapD5 : Id (Z.eqb (Z.abs (9 * 9 - 5 * (4 * 4))) 1%Z) true.
Proof. vm_compute. apply id_refl. Qed.

(* Numerical anchor 4 (floor-bound instance, D = 8 non-square): 2^2 < 8 < 3^2 *)
Lemma smoke_floor : Id (Z.eqb (Z.sqrt 8 * Z.sqrt 8) 4%Z,
                     Z.eqb ((Z.sqrt 8 + 1) * (Z.sqrt 8 + 1)) 9%Z) (true, true).
Proof. vm_compute. apply id_refl. Qed.

(* Numerical anchor 5 (Q square-gap exact equality): |(3/2)^2 - 2| = 1/4 *)
Lemma smoke_q_square : Id (Qeq_bool (Qabs (((3 # 2)%Q * (3 # 2)%Q - (2 # 1))%Q))
  (Qinv ((4 # 1)%Q))) true.
Proof. vm_compute. apply id_refl. Qed.

(* Numerical anchor 6 (Q square-gap strict case): |(4/3)^2 - 3| = 11/9 > 1/9 *)
Lemma smoke_q_square_strict : Id (Qeq_bool (Qabs (((4 # 3)%Q * (4 # 3)%Q - (3 # 1))%Q))
  ((11 # 9)%Q)) true.
Proof. vm_compute. apply id_refl. Qed.

(* Numerical anchor 7 (computational face, D = 3): genD_gap 3 7 4 = 1 *)
Lemma smoke_genD_gap : Id (Z.eqb (Z.abs (genD_gap 3 7 4)) 1%Z) true.
Proof. vm_compute. apply id_refl. Qed.

(* Numerical anchor 8 (Q face, D = 2): Qabs (genD_gapQ 2 3 2) = 1/4 *)
Lemma smoke_genD_gapQ : Id (Qeq_bool (Qabs (genD_gapQ 2 3 2)) (Qinv ((4 # 1)%Q))) true.
Proof. vm_compute. apply id_refl. Qed.

Print Assumptions smoke_gapD2.
Print Assumptions smoke_gapD3.
Print Assumptions smoke_gapD5.
Print Assumptions smoke_floor.
Print Assumptions smoke_q_square.
Print Assumptions smoke_q_square_strict.
Print Assumptions smoke_genD_gap.
Print Assumptions smoke_genD_gapQ.

From Stdlib Require Import Extraction.
Separate Extraction genD_gap genD_gapQ sqrtD_floor genD_no_sqrtZ
  genD_no_sqrtZ_ne sqrt2_nonsquare sqrt3_nonsquare sqrt5_nonsquare
  gen_gapD_ne gen_gapD_pos gen_gapD_2 gen_gapD_3 gen_gapD_5
  q_square_cross q_square_gap smoke_gapD2 smoke_gapD3 smoke_gapD5
  smoke_floor smoke_q_square smoke_q_square_strict smoke_genD_gap
  smoke_genD_gapQ.
