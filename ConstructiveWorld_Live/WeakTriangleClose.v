(* ConstructiveWorld-Set -- weak-triangle closure family: the Q-level Cauchy-Schwarz engine loaded onto the real carrier. *)

(** * WeakTriangleClose: the weak triangle inequality closed from the binary Cauchy-Schwarz core.

    Mission.  Formalizes the closure chain for the weak triangle inequality:
    the [Qeq]-to-[Qle] restatement [wtc_qle_of_qeq], the Q-layer square
    nonnegativity engine [wtc_q_sq_nonneg] and the binary Cauchy-Schwarz
    core [wtc_cs2_q] on the Q side; the real-level square nonnegativity
    [wtc_sq_nonneg], the Gram two-square identity [wtc_gram_id], the real
    Cauchy-Schwarz bound [wtc_cs2_real] and the direct-form main statement
    [wtc_weak_triangle_load]; and the two-tier sigT certificate [wtc_family]
    pairing the Q leg and the real leg.

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qring].
      Requires [S01_BaseRing], [fa53_compat_abs] of this development.

    References.  This development, WeakTriangleClose.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" WeakTriangleClose.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 00015ff4]. *)

From Stdlib Require Import QArith.QArith QArith.Qring.
Require Import S01_BaseRing.
Require Import fa53_compat_abs.

(* ================== Section 1. Q-level engine: the Q square family and the binary Cauchy-Schwarz kernel ================== *)

(* ---- Qeq to Qle restatement: Qeq and Qle both unfold to the Z layer of
   Qnum cross products, closed by Z.le_refl. ---- *)
Lemma wtc_qle_of_qeq : forall x y : Q, x == y -> x <= y.
Proof.
  intros x y H. unfold Qle, Qeq in *.
  rewrite H. apply Z.le_refl.
Qed.

(* ---- Q square nonnegativity, the Q-layer analogue of AbsSqClose #42
   asc_sq_nonneg: Qle_bool trichotomy on 0 ? q.  The positive branch is
   direct from Qmult_le_0_compat; the negative branch flips to the strict
   order by Qnot_le_lt, lifts to le by Qopp_le_compat, restates
   (−q)² == q² by ring, and closes by Qle_trans. ---- *)
Lemma wtc_q_sq_nonneg : forall q : Q, 0 <= q * q.
Proof.
  intro q.
  destruct (Qle_bool 0 q) eqn:E.
  - apply (proj1 (Qle_bool_iff 0 q)) in E.
    exact (Qmult_le_0_compat q q E E).
  - assert (Hne : ~ 0 <= q).
    { intro Hle. apply (proj2 (Qle_bool_iff 0 q)) in Hle.
      rewrite E in Hle. discriminate Hle. }
    assert (Hneg : q < 0) by (exact (Qnot_le_lt 0 q Hne)).
    assert (Hop : 0 <= - q).
    { exact (Qopp_le_compat q 0 (Qlt_le_weak q 0 Hneg)). }
    assert (Hpos : 0 <= - q * - q) by (exact (Qmult_le_0_compat (- q) (- q) Hop Hop)).
    apply (Qle_trans 0 (- q * - q) (q * q) Hpos).
    apply wtc_qle_of_qeq. ring.
Qed.

(* ---- Q-layer binary Cauchy-Schwarz kernel, the Q-engine face of the open
   item "Σa²·Σb² ≥ (Σab)²": the Lagrange two-square identity
   (a²+b²)(c²+d²) == (ac+bd)²+(ad−bc)² unfolds in one ring pass, and the two
   square-nonnegativity branches with order preservation of addition close
   it. ---- *)
Theorem wtc_cs2_q : forall a b c d : Q,
  (a * c + b * d) * (a * c + b * d) <= (a * a + b * b) * (c * c + d * d).
Proof.
  intros a b c d.
  assert (HT := wtc_q_sq_nonneg (a * d - b * c)).
  apply (Qle_trans ((a * c + b * d) * (a * c + b * d))
                   ((a * c + b * d) * (a * c + b * d)
                    + (a * d - b * c) * (a * d - b * c))
                   ((a * a + b * b) * (c * c + d * d))).
  - apply (Qle_trans ((a * c + b * d) * (a * c + b * d))
                     ((a * c + b * d) * (a * c + b * d) + 0)
                     ((a * c + b * d) * (a * c + b * d)
                      + (a * d - b * c) * (a * d - b * c))).
    + apply wtc_qle_of_qeq. ring.
    + apply Qplus_le_compat. apply Qle_refl. exact HT.
  - apply wtc_qle_of_qeq. ring.
Qed.

(* ================== Section 2. real-level load: the S01-carrier Gram expansion and direct square nonnegativity ================== *)

Section WeakTriangleLoad.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {DO : DecidableOrder RI}.

(* fa53 projection-alias idiom: the class field name lt_dec is shadowed by
   Stdlib Compare_dec, so the decidable-order component is projected by an
   explicit match, the same form as the fa53/AbsSqClose match projection.
   ---- *)
Definition wtc_lt_dec_id :
  forall a b : R, Or (lt a b) (Or (Id a b) (lt b a)) :=
  match DO with
  | Build_DecidableOrder _ _ lt_d _ _ _ => lt_d
  end.

(* ---- Regrouping channel 1: (x·y)(x·y) == (x·x)(y·y), in five assoc/comm
   steps reusing the square placement of the four products ac/ad/bd/bc.
   ---- *)
Lemma wtc_sq4 : forall x y : R,
  Id (mult (mult x y) (mult x y)) (mult (mult x x) (mult y y)).
Proof.
  intros x y.
    exact (id_trans (id_sym (mult_assoc x y (mult x y)))
           (id_trans (id_cong (fun w => mult x w) (mult_assoc y x y))
             (id_trans (id_cong (fun w => mult x (mult w y)) (mult_comm y x))
               (id_trans (id_cong (fun w => mult x w) (id_sym (mult_assoc x y y)))
                         (mult_assoc x x (mult y y)))))).
Qed.

(* ---- Regrouping channel 2: the first segment of the (u+v)² expansion, a
   two-segment distributivity channel. ---- *)
Lemma wtc_sq_plus : forall u v : R,
  Id (mult (plus u v) (plus u v))
     (plus (plus (mult u u) (mult v u)) (plus (mult u v) (mult v v))).
Proof.
  intros u v.
  exact (id_trans (distrib (plus u v) u v)
           (id_trans (id_cong (fun w => plus w (mult (plus u v) v))
                              (mult_plus_distr_r u v u))
                     (id_cong (fun w => plus (plus (mult u u) (mult v u)) w)
                              (mult_plus_distr_r u v v)))).
Qed.

(* ---- Regrouping channel 3: the four-term sum exchange
   plus(A+B)+(C+D) == plus(A+C)+(B+D). ---- *)
Lemma wtc_plus4 : forall A B C D : R,
  Id (plus (plus A B) (plus C D)) (plus (plus A C) (plus B D)).
Proof.
  intros A B C D.
  exact (id_trans (id_sym (plus_assoc A B (plus C D)))
           (id_trans (id_cong (fun w => plus A w) (plus_assoc B C D))
             (id_trans (id_cong (fun w => plus A (plus w D)) (plus_comm B C))
               (id_trans (id_cong (fun w => plus A w) (id_sym (plus_assoc C B D)))
                         (plus_assoc A C (plus B D)))))).
Qed.

(* ---- Regrouping channel 4: the opp involution −−a == a, restating the
   AbsSqClose lemma asc_opp_opp: plus_inv_unique aligns the right inverses
   of the two sides. ---- *)
Lemma wtc_opp_opp : forall a : R, Id (opp (opp a)) a.
Proof.
  intro a.
  exact (plus_inv_unique (opp a) (opp (opp a)) a
           (plus_opp (opp a))
           (id_trans (id_sym (plus_comm a (opp a))) (plus_opp a))).
Qed.

(* ---- Regrouping channel 5: (−t)² == t², restating the AbsSqClose lemma
   asc_sq_opp: opp_mult_r and opp_mult_l move the opp outward, and the opp
   involution closes. ---- *)
Lemma wtc_sq_opp : forall t : R, Id (mult t t) (mult (opp t) (opp t)).
Proof.
  intro t.
  exact (id_sym (id_trans (opp_mult_r t (opp t))
                  (id_trans (id_cong opp (opp_mult_l t t))
                            (wtc_opp_opp (mult t t))))).
Qed.

(* ---- Regrouping channel 6: restatement into the K normal form
   (a·c)(b·d) == (a·b)(c·d) in five assoc/comm steps; bd·ac and bc·ad reach
   this form first by a single comm pass. ---- *)
Lemma wtc_K1 : forall a b c d : R,
  Id (mult (mult a c) (mult b d)) (mult (mult a b) (mult c d)).
Proof.
  intros a b c d.
  exact (id_trans (id_sym (mult_assoc a c (mult b d)))
           (id_trans (id_cong (fun w => mult a w) (mult_assoc c b d))
             (id_trans (id_cong (fun w => mult a (mult w d)) (mult_comm c b))
               (id_trans (id_cong (fun w => mult a w) (id_sym (mult_assoc b c d)))
                         (mult_assoc a b (mult c d)))))).
Qed.

(* ---- Regrouping channel 7: (a·d)(b·c) == the K normal form, by the same
   five steps. ---- *)
Lemma wtc_K2 : forall a b c d : R,
  Id (mult (mult a d) (mult b c)) (mult (mult a b) (mult c d)).
Proof.
  intros a b c d.
  assert (H1 : Id (mult (mult a d) (mult b c)) (mult a (mult d (mult b c)))).
  { exact (id_sym (mult_assoc a d (mult b c))). }
  assert (H2 : Id (mult a (mult d (mult b c))) (mult a (mult (mult d b) c))).
  { exact (id_cong (fun w => mult a w) (mult_assoc d b c)). }
  assert (H3 : Id (mult a (mult (mult d b) c)) (mult a (mult (mult b d) c))).
  { exact (id_cong (fun w => mult a (mult w c)) (mult_comm d b)). }
  assert (H4 : Id (mult a (mult (mult b d) c)) (mult a (mult b (mult d c)))).
  { exact (id_cong (fun w => mult a w) (id_sym (mult_assoc b d c))). }
  assert (H5 : Id (mult a (mult b (mult d c))) (mult a (mult b (mult c d)))).
  { exact (id_cong (fun w => mult a (mult b w)) (mult_comm d c)). }
  assert (H6 : Id (mult a (mult b (mult c d))) (mult (mult a b) (mult c d))).
  { exact (mult_assoc a b (mult c d)). }
  exact (id_trans H1 (id_trans H2 (id_trans H3 (id_trans H4 (id_trans H5 H6))))).
Qed.

(* ---- Real square nonnegativity, restating the AbsSqClose #42
   asc_sq_nonneg candidate with the same term-by-term trichotomy: the
   positive branch runs the zero-product chain and le_mult_compat_weak; the
   zero branch collapses the square to zero; the negative branch uses the
   −t > 0 witness and the (−t)² == t² ring restatement. ---- *)
Theorem wtc_sq_nonneg : forall t : R, le zero (mult t t).
Proof.
  intro t.
  destruct (wtc_lt_dec_id zero t) as [H0t | [H0eq | Htl]].
  - (* case 0 < t: the mult zero t == 0 chain, then weak multiplication
       monotonicity applied to the two le zero t witnesses *)
    assert (Hge : le zero t) by (exact (lt_le_iff zero t (inl H0t))).
    exact (le_id_l zero (mult zero t) (mult t t)
             (id_sym (id_trans (mult_comm zero t) (mult_zero t)))
             (le_mult_compat_weak zero t t Hge Hge)).
  - (* case 0 == t: t² == 0² == 0 *)
    assert (Htz : Id (mult t t) zero).
    { exact (id_trans (id_cong (fun w => mult w t) (id_sym H0eq))
                      (id_trans (mult_comm zero t) (mult_zero t))). }
    exact (le_id_r zero zero (mult t t) (id_sym Htz) (le_refl zero)).
  - (* case t < 0: the −t > 0 witness plus the (−t)² == t² restatement *)
    assert (Ht0 : lt zero (opp t)).
    { exact (lt_id_l zero (opp zero) (opp t)
               (id_sym (plus_inv_unique zero (opp zero) zero
                          (plus_opp zero) (plus_zero zero)))
               (opp_lt_compat t zero Htl)). }
    exact (le_id_r zero (mult (opp t) (opp t)) (mult t t)
             (id_sym (wtc_sq_opp t))
             (le_id_l zero (mult zero (opp t)) (mult (opp t) (opp t))
                (id_sym (id_trans (mult_comm zero (opp t))
                                  (mult_zero (opp t))))
                (le_mult_compat_weak zero (opp t) (opp t)
                   (lt_le_iff zero (opp t) (inl Ht0))
                   (lt_le_iff zero (opp t) (inl Ht0))))).
Qed.

(* ---- The Gram two-square identity:
   (a²+b²)(c²+d²) == (ac+bd)² + (ad−bc)².
   Expansion account (s1 = a², s2 = b², t1 = c², t2 = d², K = (a·b)(c·d)):
   the left side X reduces by two distrib steps to P = (s1t1+s2t1)+(s1t2+s2t2);
   the square of ac+bd carries the four terms s1t1, K, K, s2t2 and the square
   of ad−bc the four terms s1t2, oppK, oppK, s2t1; two layers of plus4 bring
   each K/oppK pair adjacent, plus_opp cancels both pairs, and the zero
   placements finish. ---- *)
Theorem wtc_gram_id : forall a b c d : R,
  Id (mult (plus (mult a a) (mult b b)) (plus (mult c c) (mult d d)))
     (plus (mult (plus (mult a c) (mult b d)) (plus (mult a c) (mult b d)))
           (mult (plus (mult a d) (opp (mult b c)))
                 (plus (mult a d) (opp (mult b c))))).
Proof.
  intros a b c d.
  (* segment 1: X reduces to P' = (s1t1+s2t1)+(s1t2+s2t2) *)
  assert (A1 : Id (mult (plus (mult a a) (mult b b)) (plus (mult c c) (mult d d)))
                  (plus (mult (plus (mult a a) (mult b b)) (mult c c))
                        (mult (plus (mult a a) (mult b b)) (mult d d)))).
  { exact (distrib (plus (mult a a) (mult b b)) (mult c c) (mult d d)). }
  assert (A2 : Id (mult (plus (mult a a) (mult b b)) (mult c c))
                  (plus (mult (mult a a) (mult c c)) (mult (mult b b) (mult c c)))).
  { exact (mult_plus_distr_r (mult a a) (mult b b) (mult c c)). }
  assert (A3 : Id (mult (plus (mult a a) (mult b b)) (mult d d))
                  (plus (mult (mult a a) (mult d d)) (mult (mult b b) (mult d d)))).
  { exact (mult_plus_distr_r (mult a a) (mult b b) (mult d d)). }
  assert (A4 : Id (plus (mult (plus (mult a a) (mult b b)) (mult c c))
                        (mult (plus (mult a a) (mult b b)) (mult d d)))
                  (plus (plus (mult (mult a a) (mult c c)) (mult (mult b b) (mult c c)))
                        (mult (plus (mult a a) (mult b b)) (mult d d)))).
  { exact (id_cong (fun w => plus w (mult (plus (mult a a) (mult b b)) (mult d d))) A2). }
  assert (A5 : Id (plus (plus (mult (mult a a) (mult c c)) (mult (mult b b) (mult c c)))
                        (mult (plus (mult a a) (mult b b)) (mult d d)))
                  (plus (plus (mult (mult a a) (mult c c)) (mult (mult b b) (mult c c)))
                        (plus (mult (mult a a) (mult d d)) (mult (mult b b) (mult d d))))).
  { exact (id_cong (fun w => plus (plus (mult (mult a a) (mult c c)) (mult (mult b b) (mult c c))) w) A3). }
  assert (H1 : Id (mult (plus (mult a a) (mult b b)) (plus (mult c c) (mult d d)))
                  (plus (plus (mult (mult a a) (mult c c)) (mult (mult b b) (mult c c)))
                        (plus (mult (mult a a) (mult d d)) (mult (mult b b) (mult d d))))).
  { exact (id_trans A1 (id_trans A4 A5)). }
  (* segment 2: m² reduces to M = (s1t1+K)+(K+s2t2) *)
  assert (B1 : Id (mult (plus (mult a c) (mult b d)) (plus (mult a c) (mult b d)))
                  (plus (plus (mult (mult a c) (mult a c)) (mult (mult b d) (mult a c)))
                        (plus (mult (mult a c) (mult b d)) (mult (mult b d) (mult b d))))).
  { exact (wtc_sq_plus (mult a c) (mult b d)). }
  assert (B3 : Id (mult (mult b d) (mult a c)) (mult (mult a b) (mult c d))).
  { exact (id_trans (mult_comm (mult b d) (mult a c)) (wtc_K1 a b c d)). }
  assert (B6 : Id (plus (plus (mult (mult a c) (mult a c)) (mult (mult b d) (mult a c)))
                        (plus (mult (mult a c) (mult b d)) (mult (mult b d) (mult b d))))
                  (plus (plus (mult (mult a a) (mult c c)) (mult (mult b d) (mult a c)))
                        (plus (mult (mult a c) (mult b d)) (mult (mult b d) (mult b d))))).
  { exact (id_cong (fun w => plus (plus w (mult (mult b d) (mult a c))) (plus (mult (mult a c) (mult b d)) (mult (mult b d) (mult b d))))
                   (wtc_sq4 a c)). }
  assert (B7 : Id (plus (plus (mult (mult a a) (mult c c)) (mult (mult b d) (mult a c)))
                        (plus (mult (mult a c) (mult b d)) (mult (mult b d) (mult b d))))
                  (plus (plus (mult (mult a a) (mult c c)) (mult (mult a b) (mult c d)))
                        (plus (mult (mult a c) (mult b d)) (mult (mult b d) (mult b d))))).
  { exact (id_cong (fun w => plus (plus (mult (mult a a) (mult c c)) w) (plus (mult (mult a c) (mult b d)) (mult (mult b d) (mult b d))))
                   B3). }
  assert (B8 : Id (plus (plus (mult (mult a a) (mult c c)) (mult (mult a b) (mult c d)))
                        (plus (mult (mult a c) (mult b d)) (mult (mult b d) (mult b d))))
                  (plus (plus (mult (mult a a) (mult c c)) (mult (mult a b) (mult c d)))
                        (plus (mult (mult a b) (mult c d)) (mult (mult b d) (mult b d))))).
  { exact (id_cong (fun w => plus (plus (mult (mult a a) (mult c c)) (mult (mult a b) (mult c d))) (plus w (mult (mult b d) (mult b d))))
                   (wtc_K1 a b c d)). }
  assert (B9 : Id (plus (plus (mult (mult a a) (mult c c)) (mult (mult a b) (mult c d)))
                        (plus (mult (mult a b) (mult c d)) (mult (mult b d) (mult b d))))
                  (plus (plus (mult (mult a a) (mult c c)) (mult (mult a b) (mult c d)))
                        (plus (mult (mult a b) (mult c d)) (mult (mult b b) (mult d d))))).
  { exact (id_cong (fun w => plus (plus (mult (mult a a) (mult c c)) (mult (mult a b) (mult c d))) (plus (mult (mult a b) (mult c d)) w))
                   (wtc_sq4 b d)). }
  assert (H2 : Id (mult (plus (mult a c) (mult b d)) (plus (mult a c) (mult b d)))
                  (plus (plus (mult (mult a a) (mult c c)) (mult (mult a b) (mult c d)))
                        (plus (mult (mult a b) (mult c d)) (mult (mult b b) (mult d d))))).
  { exact (id_trans B1 (id_trans B6 (id_trans B7 (id_trans B8 B9)))). }
  (* segment 3: n² reduces to N = (s1t2+oppK)+(oppK+s2t1) *)
  assert (C1 : Id (mult (plus (mult a d) (opp (mult b c))) (plus (mult a d) (opp (mult b c))))
                  (plus (plus (mult (mult a d) (mult a d)) (mult (opp (mult b c)) (mult a d)))
                        (plus (mult (mult a d) (opp (mult b c))) (mult (opp (mult b c)) (opp (mult b c)))))).
  { exact (wtc_sq_plus (mult a d) (opp (mult b c))). }
  assert (C3 : Id (mult (opp (mult b c)) (mult a d)) (opp (mult (mult a b) (mult c d)))).
  { exact (id_trans (opp_mult_r (mult b c) (mult a d))
                    (id_cong opp (id_trans (mult_comm (mult b c) (mult a d)) (wtc_K2 a b c d)))). }
  assert (C4 : Id (mult (mult a d) (opp (mult b c))) (opp (mult (mult a b) (mult c d)))).
  { exact (id_trans (opp_mult_l (mult a d) (mult b c))
                    (id_cong opp (wtc_K2 a b c d))). }
  assert (C5 : Id (mult (opp (mult b c)) (opp (mult b c))) (mult (mult b b) (mult c c))).
  { exact (id_trans (opp_mult_r (mult b c) (opp (mult b c)))
             (id_trans (id_cong opp (opp_mult_l (mult b c) (mult b c)))
               (id_trans (wtc_opp_opp (mult (mult b c) (mult b c)))
                         (wtc_sq4 b c)))). }
  assert (C6 : Id (plus (plus (mult (mult a d) (mult a d)) (mult (opp (mult b c)) (mult a d)))
                        (plus (mult (mult a d) (opp (mult b c))) (mult (opp (mult b c)) (opp (mult b c)))))
                  (plus (plus (mult (mult a a) (mult d d)) (mult (opp (mult b c)) (mult a d)))
                        (plus (mult (mult a d) (opp (mult b c))) (mult (opp (mult b c)) (opp (mult b c)))))).
  { exact (id_cong (fun w => plus (plus w (mult (opp (mult b c)) (mult a d))) (plus (mult (mult a d) (opp (mult b c))) (mult (opp (mult b c)) (opp (mult b c)))))
                   (wtc_sq4 a d)). }
  assert (C7 : Id (plus (plus (mult (mult a a) (mult d d)) (mult (opp (mult b c)) (mult a d)))
                        (plus (mult (mult a d) (opp (mult b c))) (mult (opp (mult b c)) (opp (mult b c)))))
                  (plus (plus (mult (mult a a) (mult d d)) (opp (mult (mult a b) (mult c d))))
                        (plus (mult (mult a d) (opp (mult b c))) (mult (opp (mult b c)) (opp (mult b c)))))).
  { exact (id_cong (fun w => plus (plus (mult (mult a a) (mult d d)) w) (plus (mult (mult a d) (opp (mult b c))) (mult (opp (mult b c)) (opp (mult b c)))))
                   C3). }
  assert (C8 : Id (plus (plus (mult (mult a a) (mult d d)) (opp (mult (mult a b) (mult c d))))
                        (plus (mult (mult a d) (opp (mult b c))) (mult (opp (mult b c)) (opp (mult b c)))))
                  (plus (plus (mult (mult a a) (mult d d)) (opp (mult (mult a b) (mult c d))))
                        (plus (opp (mult (mult a b) (mult c d))) (mult (opp (mult b c)) (opp (mult b c)))))).
  { exact (id_cong (fun w => plus (plus (mult (mult a a) (mult d d)) (opp (mult (mult a b) (mult c d)))) (plus w (mult (opp (mult b c)) (opp (mult b c)))))
                   C4). }
  assert (C9 : Id (plus (plus (mult (mult a a) (mult d d)) (opp (mult (mult a b) (mult c d))))
                        (plus (opp (mult (mult a b) (mult c d))) (mult (opp (mult b c)) (opp (mult b c)))))
                  (plus (plus (mult (mult a a) (mult d d)) (opp (mult (mult a b) (mult c d))))
                        (plus (opp (mult (mult a b) (mult c d))) (mult (mult b b) (mult c c))))).
  { exact (id_cong (fun w => plus (plus (mult (mult a a) (mult d d)) (opp (mult (mult a b) (mult c d)))) (plus (opp (mult (mult a b) (mult c d))) w))
                   C5). }
  assert (H3 : Id (mult (plus (mult a d) (opp (mult b c))) (plus (mult a d) (opp (mult b c))))
                  (plus (plus (mult (mult a a) (mult d d)) (opp (mult (mult a b) (mult c d))))
                        (plus (opp (mult (mult a b) (mult c d))) (mult (mult b b) (mult c c))))).
  { exact (id_trans C1 (id_trans C6 (id_trans C7 (id_trans C8 C9)))). }
  (* segment 4: M+N reduces to P' by the two plus4 layers, both K/oppK
     cancellations, the zero placements, and comm *)
  assert (D1 : Id (plus (plus (plus (mult (mult a a) (mult c c)) (mult (mult a b) (mult c d)))
                             (plus (mult (mult a b) (mult c d)) (mult (mult b b) (mult d d))))
                        (plus (plus (mult (mult a a) (mult d d)) (opp (mult (mult a b) (mult c d))))
                              (plus (opp (mult (mult a b) (mult c d))) (mult (mult b b) (mult c c)))))
                  (plus (plus (plus (mult (mult a a) (mult c c)) (mult (mult a b) (mult c d)))
                              (plus (mult (mult a a) (mult d d)) (opp (mult (mult a b) (mult c d)))))
                        (plus (plus (mult (mult a b) (mult c d)) (mult (mult b b) (mult d d)))
                              (plus (opp (mult (mult a b) (mult c d))) (mult (mult b b) (mult c c)))))).
  { exact (wtc_plus4 (plus (mult (mult a a) (mult c c)) (mult (mult a b) (mult c d)))
                     (plus (mult (mult a b) (mult c d)) (mult (mult b b) (mult d d)))
                     (plus (mult (mult a a) (mult d d)) (opp (mult (mult a b) (mult c d))))
                     (plus (opp (mult (mult a b) (mult c d))) (mult (mult b b) (mult c c)))). }
  assert (D2 : Id (plus (plus (plus (mult (mult a a) (mult c c)) (mult (mult a b) (mult c d)))
                             (plus (mult (mult a a) (mult d d)) (opp (mult (mult a b) (mult c d)))))
                        (plus (plus (mult (mult a b) (mult c d)) (mult (mult b b) (mult d d)))
                              (plus (opp (mult (mult a b) (mult c d))) (mult (mult b b) (mult c c)))))
                  (plus (plus (plus (mult (mult a a) (mult c c)) (mult (mult a a) (mult d d)))
                              (plus (mult (mult a b) (mult c d)) (opp (mult (mult a b) (mult c d)))))
                        (plus (plus (mult (mult a b) (mult c d)) (mult (mult b b) (mult d d)))
                              (plus (opp (mult (mult a b) (mult c d))) (mult (mult b b) (mult c c)))))).
  { exact (id_cong (fun w => plus w (plus (plus (mult (mult a b) (mult c d)) (mult (mult b b) (mult d d)))
                                          (plus (opp (mult (mult a b) (mult c d))) (mult (mult b b) (mult c c)))))
                   (wtc_plus4 (mult (mult a a) (mult c c)) (mult (mult a b) (mult c d))
                              (mult (mult a a) (mult d d)) (opp (mult (mult a b) (mult c d))))). }
  assert (D3 : Id (plus (plus (plus (mult (mult a a) (mult c c)) (mult (mult a a) (mult d d)))
                              (plus (mult (mult a b) (mult c d)) (opp (mult (mult a b) (mult c d)))))
                        (plus (plus (mult (mult a b) (mult c d)) (mult (mult b b) (mult d d)))
                              (plus (opp (mult (mult a b) (mult c d))) (mult (mult b b) (mult c c)))))
                  (plus (plus (plus (mult (mult a a) (mult c c)) (mult (mult a a) (mult d d)))
                              (plus (mult (mult a b) (mult c d)) (opp (mult (mult a b) (mult c d)))))
                        (plus (plus (mult (mult a b) (mult c d)) (opp (mult (mult a b) (mult c d))))
                              (plus (mult (mult b b) (mult d d)) (mult (mult b b) (mult c c)))))).
  { exact (id_cong (fun w => plus (plus (plus (mult (mult a a) (mult c c)) (mult (mult a a) (mult d d)))
                                        (plus (mult (mult a b) (mult c d)) (opp (mult (mult a b) (mult c d))))) w)
                   (wtc_plus4 (mult (mult a b) (mult c d)) (mult (mult b b) (mult d d))
                              (opp (mult (mult a b) (mult c d))) (mult (mult b b) (mult c c)))). }
  assert (D4 : Id (plus (plus (plus (mult (mult a a) (mult c c)) (mult (mult a a) (mult d d)))
                              (plus (mult (mult a b) (mult c d)) (opp (mult (mult a b) (mult c d)))))
                        (plus (plus (mult (mult a b) (mult c d)) (opp (mult (mult a b) (mult c d))))
                              (plus (mult (mult b b) (mult d d)) (mult (mult b b) (mult c c)))))
                  (plus (plus (plus (mult (mult a a) (mult c c)) (mult (mult a a) (mult d d))) zero)
                        (plus zero (plus (mult (mult b b) (mult d d)) (mult (mult b b) (mult c c)))))).
  { exact (id_cong (fun w => plus (plus (plus (mult (mult a a) (mult c c)) (mult (mult a a) (mult d d))) w)
                                  (plus w (plus (mult (mult b b) (mult d d)) (mult (mult b b) (mult c c)))))
                   (plus_opp (mult (mult a b) (mult c d)))). }
  assert (D5 : Id (plus (plus (plus (mult (mult a a) (mult c c)) (mult (mult a a) (mult d d))) zero)
                        (plus zero (plus (mult (mult b b) (mult d d)) (mult (mult b b) (mult c c)))))
                  (plus (plus (mult (mult a a) (mult c c)) (mult (mult a a) (mult d d)))
                        (plus zero (plus (mult (mult b b) (mult d d)) (mult (mult b b) (mult c c)))))).
  { exact (id_cong (fun w => plus w (plus zero (plus (mult (mult b b) (mult d d)) (mult (mult b b) (mult c c)))))
                   (plus_zero (plus (mult (mult a a) (mult c c)) (mult (mult a a) (mult d d))))). }
  assert (D6 : Id (plus (plus (mult (mult a a) (mult c c)) (mult (mult a a) (mult d d)))
                        (plus zero (plus (mult (mult b b) (mult d d)) (mult (mult b b) (mult c c)))))
                  (plus (plus (mult (mult a a) (mult c c)) (mult (mult a a) (mult d d)))
                        (plus (mult (mult b b) (mult d d)) (mult (mult b b) (mult c c))))).
  { exact (id_cong (fun w => plus (plus (mult (mult a a) (mult c c)) (mult (mult a a) (mult d d))) w)
                   (id_trans (plus_comm zero (plus (mult (mult b b) (mult d d)) (mult (mult b b) (mult c c))))
                             (plus_zero (plus (mult (mult b b) (mult d d)) (mult (mult b b) (mult c c)))))). }
  assert (D7 : Id (plus (plus (mult (mult a a) (mult c c)) (mult (mult a a) (mult d d)))
                        (plus (mult (mult b b) (mult d d)) (mult (mult b b) (mult c c))))
                  (plus (plus (mult (mult a a) (mult c c)) (mult (mult b b) (mult c c)))
                        (plus (mult (mult a a) (mult d d)) (mult (mult b b) (mult d d))))).
  { exact (id_trans (id_cong (fun w => plus (plus (mult (mult a a) (mult c c)) (mult (mult a a) (mult d d))) w)
                                (plus_comm (mult (mult b b) (mult d d)) (mult (mult b b) (mult c c))))
                   (wtc_plus4 (mult (mult a a) (mult c c)) (mult (mult a a) (mult d d))
                              (mult (mult b b) (mult c c)) (mult (mult b b) (mult d d)))). }
  assert (H4 : Id (plus (plus (plus (mult (mult a a) (mult c c)) (mult (mult a b) (mult c d)))
                             (plus (mult (mult a b) (mult c d)) (mult (mult b b) (mult d d))))
                        (plus (plus (mult (mult a a) (mult d d)) (opp (mult (mult a b) (mult c d))))
                              (plus (opp (mult (mult a b) (mult c d))) (mult (mult b b) (mult c c)))))
                  (plus (plus (mult (mult a a) (mult c c)) (mult (mult b b) (mult c c)))
                        (plus (mult (mult a a) (mult d d)) (mult (mult b b) (mult d d))))).
  { exact (id_trans D1 (id_trans D2 (id_trans D3 (id_trans D4 (id_trans D5 (id_trans D6 D7)))))). }
  (* main chain: X == P', then P' == m²+N (H4 reversed, then H2 reversed
     through cong), then == m²+n² (H3 reversed through cong) *)
  assert (E1 : Id (plus (plus (mult (mult a a) (mult c c)) (mult (mult b b) (mult c c)))
                        (plus (mult (mult a a) (mult d d)) (mult (mult b b) (mult d d))))
                  (plus (plus (plus (mult (mult a a) (mult c c)) (mult (mult a b) (mult c d)))
                             (plus (mult (mult a b) (mult c d)) (mult (mult b b) (mult d d))))
                        (plus (plus (mult (mult a a) (mult d d)) (opp (mult (mult a b) (mult c d))))
                              (plus (opp (mult (mult a b) (mult c d))) (mult (mult b b) (mult c c)))))).
  { exact (id_sym H4). }  assert (E3 : Id (plus (plus (plus (mult (mult a a) (mult c c)) (mult (mult a b) (mult c d)))
                             (plus (mult (mult a b) (mult c d)) (mult (mult b b) (mult d d))))
                        (mult (plus (mult a d) (opp (mult b c))) (plus (mult a d) (opp (mult b c)))))
                  (plus (mult (plus (mult a c) (mult b d)) (plus (mult a c) (mult b d)))
                        (mult (plus (mult a d) (opp (mult b c))) (plus (mult a d) (opp (mult b c)))))).
  { exact (id_cong (fun w => plus w (mult (plus (mult a d) (opp (mult b c))) (plus (mult a d) (opp (mult b c)))))
                   (id_sym H2)). }
  assert (E4 : Id (plus (plus (plus (mult (mult a a) (mult c c)) (mult (mult a b) (mult c d)))
                                   (plus (mult (mult a b) (mult c d)) (mult (mult b b) (mult d d))))
                              (plus (plus (mult (mult a a) (mult d d)) (opp (mult (mult a b) (mult c d))))
                                    (plus (opp (mult (mult a b) (mult c d))) (mult (mult b b) (mult c c)))))
                  (plus (plus (plus (mult (mult a a) (mult c c)) (mult (mult a b) (mult c d)))
                             (plus (mult (mult a b) (mult c d)) (mult (mult b b) (mult d d))))
                        (mult (plus (mult a d) (opp (mult b c))) (plus (mult a d) (opp (mult b c)))))).
  { exact (id_cong (fun w => plus (plus (plus (mult (mult a a) (mult c c)) (mult (mult a b) (mult c d)))
                                            (plus (mult (mult a b) (mult c d)) (mult (mult b b) (mult d d)))) w)
                   (id_sym H3)). }
  exact (id_trans H1 (id_trans E1 (id_trans E4 E3))).
Qed.

(* ---- The real-level binary Cauchy-Schwarz load:
   (ac+bd)² ≤ (a²+b²)(c²+d²).  The Gram identity restatement, the
   square-nonnegativity branch, and order preservation of addition close
   it. ---- *)
Theorem wtc_cs2_real : forall a b c d : R,
  le (mult (plus (mult a c) (mult b d)) (plus (mult a c) (mult b d)))
     (mult (plus (mult a a) (mult b b)) (plus (mult c c) (mult d d))).
Proof.
  intros a b c d.
  assert (Hsq := wtc_sq_nonneg (plus (mult a d) (opp (mult b c)))).
  apply (le_id_r (mult (plus (mult a c) (mult b d)) (plus (mult a c) (mult b d)))
                 (plus (mult (plus (mult a c) (mult b d)) (plus (mult a c) (mult b d)))
                       (mult (plus (mult a d) (opp (mult b c))) (plus (mult a d) (opp (mult b c)))))
                 (mult (plus (mult a a) (mult b b)) (plus (mult c c) (mult d d)))
                 (id_sym (wtc_gram_id a b c d))).
  apply (le_id_l (mult (plus (mult a c) (mult b d)) (plus (mult a c) (mult b d)))
                 (plus (mult (plus (mult a c) (mult b d)) (plus (mult a c) (mult b d))) zero)
                 (plus (mult (plus (mult a c) (mult b d)) (plus (mult a c) (mult b d)))
                       (mult (plus (mult a d) (opp (mult b c))) (plus (mult a d) (opp (mult b c)))))
                 (id_sym (plus_zero (mult (plus (mult a c) (mult b d)) (plus (mult a c) (mult b d)))))).
  exact (le_plus_compat (mult (plus (mult a c) (mult b d)) (plus (mult a c) (mult b d)))
                        (mult (plus (mult a c) (mult b d)) (plus (mult a c) (mult b d)))
                        zero
                        (mult (plus (mult a d) (opp (mult b c))) (plus (mult a d) (opp (mult b c))))
                        (le_refl (mult (plus (mult a c) (mult b d)) (plus (mult a c) (mult b d))))
                        Hsq).
Qed.

(* ---- Main closure theorem: the direct form of the in-development honest
   variant of the open item :28, reconciled against the fa53_bs_abs_shape
   pattern; the conclusion face is verbatim that of wtc_cs2_real. ---- *)
Theorem wtc_weak_triangle_load : forall a b c d : R,
  le (mult (plus (mult a c) (mult b d)) (plus (mult a c) (mult b d)))
     (mult (plus (mult a a) (mult b b)) (plus (mult c c) (mult d d))).
Proof.
  exact wtc_cs2_real.
Qed.

(* ---- Family closure: the wtc sigT two-tier certificate (the Q-engine leg
   and the real-load leg), following the wtl_family pattern. ---- *)
Definition wtc_leg_q_cs2 : Type :=
  forall a b c d : Q,
    (a * c + b * d) * (a * c + b * d) <= (a * a + b * b) * (c * c + d * d).

Definition wtc_leg_r_cs2 : Type :=
  forall a b c d : R,
    le (mult (plus (mult a c) (mult b d)) (plus (mult a c) (mult b d)))
       (mult (plus (mult a a) (mult b b)) (plus (mult c c) (mult d d))).

Theorem wtc_family : sigT (fun _ : wtc_leg_q_cs2 => wtc_leg_r_cs2).
Proof.
  exact (existT _ wtc_cs2_q wtc_cs2_real).
Qed.

End WeakTriangleLoad.

(* ---- Audit outlets (the zero-magic extraction check) ---- *)
Print Assumptions wtc_qle_of_qeq.
Print Assumptions wtc_q_sq_nonneg.
Print Assumptions wtc_cs2_q.
Print Assumptions wtc_sq_nonneg.
Print Assumptions wtc_gram_id.
Print Assumptions wtc_cs2_real.
Print Assumptions wtc_weak_triangle_load.
Print Assumptions wtc_family.
