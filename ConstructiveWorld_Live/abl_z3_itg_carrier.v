(* ConstructiveWorld -- abl_z3_itg_carrier.v: iterated-integral carrier for the Beukers triple-integral family in the irrationality proof of zeta(3). *)
(** * abl_z3_itg_carrier: iterated-integral carrier of the Beukers zeta(3) triple-integral family.
    Mission.  A segment carries a rational coefficient and three factor
      lists (an [x]-polynomial, a [y]-polynomial, a [z]-polynomial);
      the [0,1]-polynomial integration operator [pint_integral] is
      applied three times, in [z] first, then [y], then [x].  Shown:
      (1) the iterated integral of a segment equals C(n+m,n)
      B(n+m,n)^3 (B the Beta value in closed form), three single
      integrations, no order-swapping lemma; (2) the pointwise value
      of a segment list is (x(1-x))^n (y(1-y))^n (z(1-z))^n [zb2_ps]
      n M (xyz); (3) the segment-list integral sum equals sum_{m<=M}
      C(n+m,n) B(n+m,n)^3, every term strictly positive.  The
      whole-family single-table aggregate is out of scope (Horner
      position misalignment).
    Dependencies.  Stdlib [QArith], [ZArith], [Arith], [Lia], [List],
      [Setoid]; compiled modules [S01_BaseRing], [S02_CauchyComplete],
      [S03_QExp], [BeukersLists], [PolyIntegral], [PadeErrorIntegral];
      slices [abl_z2_truncfam] ([zb2_ps]) and [abl_z2_itg_carrier]
      ([zb2_q_pow_mul], [zb2_ps_zero]).  No real-number layer.
    References.  F. Beukers, A note on the irrationality of zeta(2) and
      zeta(3), Bull. London Math. Soc. 11 (1979), iterated integrals.
    Constructivity.  Zero axioms, zero declared premises, zero proof
      abandonment.  Every statement face is Set-carried: equalities as
      [QeqT], strict positivity as [QltT]; no Prop statement, no sigT
      embedding of a Prop component.  Statement lemmas close with
      [Defined] for transparency; no opaque closer is used, since no
      pure-Prop bridge lemma stands alone.  [vm_compute] only in the
      three concrete numeric pins.
    Build.  [rocq c -native-compiler no -q -Q <world> "" abl_z3_itg_carrier.v]
      (Rocq 9.3), same-world dependency .vo chain, single shot. *)

From Stdlib Require Import QArith.QArith ZArith.ZArith Arith.Arith Lia.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Setoid.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp BeukersLists
              PolyIntegral PadeErrorIntegral.
Require Import abl_z2_truncfam.
Require Import abl_z2_itg_carrier.

Open Scope Q_scope.
Open Scope list_scope.

(* ============================================================ *)
(* Sec 0.  Base facts: multiplicative splitting of a power over a triple product. *)
(* ============================================================ *)

(* Power splits over a triple product base: (x*y*z)^k = x^k * y^k * z^k. *)
Lemma zb3_qpow3 : forall (x y z : Q) (k : nat),
  QeqT (q_pow (x * y * z) k)
       ((q_pow x k * q_pow y k * q_pow z k)%Q).
Proof.
  intros x y z k.
  assert (Hcore : q_pow (x * y * z) k
                  == (q_pow x k * q_pow y k * q_pow z k)%Q).
  { induction k as [| k IH].
    - reflexivity.
    - rewrite (qeqT_imp_qeq _ _ (q_pow_succ (x * y * z) k)).
      rewrite (qeqT_imp_qeq _ _ (q_pow_succ x k)).
      rewrite (qeqT_imp_qeq _ _ (q_pow_succ y k)).
      rewrite (qeqT_imp_qeq _ _ (q_pow_succ z k)).
      rewrite IH. ring. }
  apply qeq_imp_qeqT. exact Hcore.
Defined.

(* ============================================================ *)
(* Sec 1.  Carrier definitions (interface face, signatures fixed). *)
(* ============================================================ *)

Definition zb3_seg : Set := (Q * (list Q * (list Q * list Q)))%type.

(* Canonical form of segment m: the coefficient C(n+m,n) with three copies of the factor list of t^{n+m} (1-t)^n. *)
Definition zb3_segof (n m : nat) : zb3_seg :=
  ((Z.of_nat (bkC (n + m) n) # 1)%Q,
   (pei_list (n + m) n,
    (pei_list (n + m) n, pei_list (n + m) n))).

(* Segment list: head at m = M, descending to m = 0. *)
Fixpoint zb3_segl (n M : nat) : list zb3_seg :=
  match M with
  | O => ((Z.of_nat (bkC (n + 0) n) # 1,
           (pei_list (n + 0) n,
            (pei_list (n + 0) n, pei_list (n + 0) n))) :: nil)%list
  | Datatypes.S M' =>
      (Z.of_nat (bkC (n + Datatypes.S M') n) # 1,
       (pei_list (n + Datatypes.S M') n,
        (pei_list (n + Datatypes.S M') n,
         pei_list (n + Datatypes.S M') n))) :: zb3_segl n M'
  end.

(* Pointwise evaluation of a segment: the coefficient times the Horner value of the x factor list, of the y factor list, and of the z factor list. *)
Definition zb3_beval (s : zb3_seg) (x y z : Q) : Q :=
  fst s * pint_eval (fst (snd s)) x
        * pint_eval (fst (snd (snd s))) y
        * pint_eval (snd (snd (snd s))) z.

(* Pointwise evaluation of a segment list (summed segment by segment). *)
Fixpoint zb3_beval_l (l : list zb3_seg) (x y z : Q) : Q :=
  match l with
  | nil => 0
  | s :: l' => zb3_beval s x y z + zb3_beval_l l' x y z
  end.

(* The z-integration operator: a segment is sent to a coefficient together with the pair of factor lists left untouched (the x list and the y list). *)
Definition zb3_zint (s : zb3_seg) : (Q * (list Q * list Q))%type :=
  (fst s * pint_integral (snd (snd (snd s))),
   (fst (snd s), fst (snd (snd s)))).

(* The y-integration operator: the pair is sent to an x-polynomial (coefficient = coefficient times the z-integral value times the y-integral value). *)
Definition zb3_yint (p : (Q * (list Q * list Q))) : list Q :=
  pint_scale (fst p * pint_integral (snd (snd p))) (fst (snd p)).

(* Iterated triple integral of a segment: one more application of the integration operator, to the x-polynomial. *)
Definition zb3_di (s : zb3_seg) : Q := pint_integral (zb3_yint (zb3_zint s)).

(* Integral sum over a segment list (summed segment by segment). *)
Fixpoint zb3_di_l (l : list zb3_seg) : Q :=
  match l with
  | nil => 0
  | s :: l' => zb3_di s + zb3_di_l l'
  end.

(* Closed form of term m: C(n+m,n) B(n+m,n)^3, with B(a,n) = a! n! / (a+n+1)!. *)
Definition zb3_term (n m : nat) : Q :=
  (Z.of_nat (bkC (n + m) n) # 1)
    * (q_fact (n + m) * q_fact n / q_fact (n + m + n + 1))
    * (q_fact (n + m) * q_fact n / q_fact (n + m + n + 1))
    * (q_fact (n + m) * q_fact n / q_fact (n + m + n + 1)).

(* Closed-form term sum: sum_{m<=M} zb3_term n m. *)
Fixpoint zb3_Isum (n M : nat) : Q :=
  match M with
  | O => zb3_term n 0
  | Datatypes.S M' => zb3_Isum n M' + zb3_term n (Datatypes.S M')
  end.

(* ============================================================ *)
(* Sec 2.  Core statements: the thrice-integrated value of a segment, the segment-list sum, the pointwise face, positivity. *)
(* ============================================================ *)

(* Closed form of the iterated triple integral of a segment: three single
   integrations, z first, then y, then x.  The z- and y-integrations give
   the coefficient times B times B; the x-integration multiplies the
   scaled factor list by B once more, matching the three-factor closed
   form. *)
Lemma zb3_di_seg_eq : forall n m, QeqT (zb3_di (zb3_segof n m)) (zb3_term n m).
Proof.
  intros n m.
  assert (Hcore : zb3_di (zb3_segof n m) == zb3_term n m).
  { unfold zb3_di, zb3_yint, zb3_zint, zb3_segof, zb3_term.
    cbn [fst snd].
    assert (Hs := qeqT_imp_qeq _ _
               (pint_integral_scale
                 (((Z.of_nat (bkC (n + m) n) # 1)
                   * pint_integral (pei_list (n + m) n))
                  * pint_integral (pei_list (n + m) n))
                 (pei_list (n + m) n))).
    rewrite Hs.
    rewrite (qeqT_imp_qeq _ _ (pei_beta_value (n + m) n)). ring. }
  apply qeq_imp_qeqT. exact Hcore.
Defined.

(* The integral sum over the segment list equals the closed-form term sum (induction on M). *)
Lemma zb3_di_l_segl : forall n M, QeqT (zb3_di_l (zb3_segl n M)) (zb3_Isum n M).
Proof.
  intros n M.
  assert (Hcore : forall k, zb3_di_l (zb3_segl n k) == zb3_Isum n k).
  { induction k as [| k IH].
    - assert (H0 : zb3_segl n 0 = (zb3_segof n 0 :: nil)%list) by reflexivity.
      rewrite H0. cbn [zb3_di_l zb3_Isum].
      rewrite (qeqT_imp_qeq _ _ (zb3_di_seg_eq n 0)). ring.
    - assert (HS : zb3_segl n (Datatypes.S k)
                   = (zb3_segof n (Datatypes.S k)) :: zb3_segl n k) by reflexivity.
      rewrite HS. cbn [zb3_di_l zb3_Isum].
      rewrite (qeqT_imp_qeq _ _ (zb3_di_seg_eq n (Datatypes.S k))).
      rewrite IH. ring. }
  apply qeq_imp_qeqT. apply Hcore.
Defined.

(* Pointwise face: the value of the segment list is
   (x(1-x))^n (y(1-y))^n (z(1-z))^n zb2_ps n M (xyz).  Segment m
   contributes C(n+m,n) x^{n+m} (1-x)^n y^{n+m} (1-y)^n z^{n+m}
   (1-z)^n, folded into the last term of the partial sum. *)
Lemma zb3_beval_segl : forall n M x y z,
  QeqT (zb3_beval_l (zb3_segl n M) x y z)
       (q_pow (x * (1 - x)) n * q_pow (y * (1 - y)) n
        * q_pow (z * (1 - z)) n * zb2_ps n M (x * y * z)).
Proof.
  intros n M x y z.
  assert (Hcore : zb3_beval_l (zb3_segl n M) x y z
  == q_pow (x * (1 - x)) n * q_pow (y * (1 - y)) n
     * q_pow (z * (1 - z)) n * zb2_ps n M (x * y * z)).
  { induction M as [| M IH].
    - assert (H0 : zb3_segl n 0 = (zb3_segof n 0 :: nil)%list) by reflexivity.
      rewrite H0. cbn [zb3_beval_l].
      unfold zb3_beval, zb3_segof. cbn [fst snd].
      rewrite (qeqT_imp_qeq _ _ (pei_beta_eval (n + 0) n x)).
      rewrite (qeqT_imp_qeq _ _ (pei_beta_eval (n + 0) n y)).
      rewrite (qeqT_imp_qeq _ _ (pei_beta_eval (n + 0) n z)).
      rewrite !Nat.add_0_r.
      rewrite (S07_RealSetoidExpLog.RealSetoid.Id_eq _ _ (bkC_diag n)).
      cbn [Z.of_nat].
      rewrite (qeqT_imp_qeq _ _ (zb2_ps_zero n (x * y * z))).
      rewrite <- (qeqT_imp_qeq _ _ (zb2_q_pow_mul x (1 - x) n)).
      rewrite <- (qeqT_imp_qeq _ _ (zb2_q_pow_mul y (1 - y) n)).
      rewrite <- (qeqT_imp_qeq _ _ (zb2_q_pow_mul z (1 - z) n)).
      ring.
    - assert (HS : zb3_segl n (Datatypes.S M)
                   = (zb3_segof n (Datatypes.S M)) :: zb3_segl n M) by reflexivity.
      rewrite HS. cbn [zb3_beval_l].
      unfold zb3_beval, zb3_segof. cbn [fst snd].
      rewrite (qeqT_imp_qeq _ _ (pei_beta_eval (n + Datatypes.S M) n x)).
      rewrite (qeqT_imp_qeq _ _ (pei_beta_eval (n + Datatypes.S M) n y)).
      rewrite (qeqT_imp_qeq _ _ (pei_beta_eval (n + Datatypes.S M) n z)).
      rewrite (qeqT_imp_qeq _ _ (q_pow_add x n (Datatypes.S M))).
      rewrite (qeqT_imp_qeq _ _ (q_pow_add y n (Datatypes.S M))).
      rewrite (qeqT_imp_qeq _ _ (q_pow_add z n (Datatypes.S M))).
      rewrite IH.
      rewrite zb2_ps_unfold.
      rewrite (qeqT_imp_qeq _ _ (zb3_qpow3 x y z (Datatypes.S M))).
      rewrite (qeqT_imp_qeq _ _ (zb2_q_pow_mul x (1 - x) n)).
      rewrite (qeqT_imp_qeq _ _ (zb2_q_pow_mul y (1 - y) n)).
      rewrite (qeqT_imp_qeq _ _ (zb2_q_pow_mul z (1 - z) n)).
      ring. }
  apply qeq_imp_qeqT. exact Hcore.
Defined.

(* Term m is strictly positive: C(n+m,n) >= 1, and the numerator and denominator factorials of the Beta value are both positive. *)
Lemma zb3_term_pos : forall n m, QltT 0 (zb3_term n m).
Proof.
  intros n m. apply Qlt_to_QltT. unfold zb3_term.
  assert (Hc : Qlt 0 ((Z.of_nat (bkC (n + m) n) # 1))).
  { unfold Qlt. cbn [Qnum Qden Qmult Pos.mul].
    assert (Hb : (1 <= bkC (n + m) n)%nat)
      by (apply NatLe_drop, bkC_pos, NatLe_lift; lia).
    lia. }
  assert (Hbeta : Qlt 0 (q_fact (n + m) * q_fact n / q_fact (n + m + n + 1))).
  { exact (QltT_to_Qlt _ _
             (pei_qeq_lt _ _ 0 (pei_beta_value (n + m) n) (pei_beta_pos (n + m) n))). }
  apply (Qmult_lt_0_compat
           ((Z.of_nat (bkC (n + m) n) # 1)
            * (q_fact (n + m) * q_fact n / q_fact (n + m + n + 1))
            * (q_fact (n + m) * q_fact n / q_fact (n + m + n + 1)))
           (q_fact (n + m) * q_fact n / q_fact (n + m + n + 1))).
  - apply (Qmult_lt_0_compat
             ((Z.of_nat (bkC (n + m) n) # 1)
              * (q_fact (n + m) * q_fact n / q_fact (n + m + n + 1)))
             (q_fact (n + m) * q_fact n / q_fact (n + m + n + 1)))
    ; [ apply (Qmult_lt_0_compat _ _); assumption | exact Hbeta ].
  - exact Hbeta.
Defined.

(* The closed-form term sum is strictly positive: the first term is strictly positive, and summing nonnegative terms preserves strict positivity. *)
Lemma zb3_Isum_pos : forall n M, QltT 0 (zb3_Isum n M).
Proof.
  intros n M. induction M as [| M IH].
  - apply zb3_term_pos.
  - cbn [zb3_Isum]. apply pei_lt_le_plus.
    + exact IH.
    + apply qltT_leT'. apply zb3_term_pos.
Defined.

(* ============================================================ *)
(* Sec 3.  Numeric anchors (computation-chain pins on concrete indices). *)
(* ============================================================ *)

(* n = 1, m = 0: C(1,1) B(1,1)^3 = 1 * (1/6)^3 = 1/216. *)
Lemma zb3_term_1_0_anchor : QeqT (zb3_term 1 0) (1 # 216).
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Defined.

(* n = 2, m = 1: C(3,2) B(3,2)^3 = 3 * (1/60)^3 = 1/72000. *)
Lemma zb3_term_2_1_anchor : QeqT (zb3_term 2 1) (1 # 72000).
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Defined.

(* Isum 1 1 = 1/216 + 1/864 = 5/864 (the first two terms of zeta(3) - 1). *)
Lemma zb3_Isum_1_1_anchor : QeqT (zb3_Isum 1 1) (5 # 864).
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Defined.

(* ============================================================ *)
(* Sec 4.  Closing audit: Print Assumptions self-check on every statement. *)
(* ============================================================ *)

Print Assumptions zb3_qpow3.
Print Assumptions zb3_di_seg_eq.
Print Assumptions zb3_di_l_segl.
Print Assumptions zb3_beval_segl.
Print Assumptions zb3_term_pos.
Print Assumptions zb3_Isum_pos.
Print Assumptions zb3_term_1_0_anchor.
Print Assumptions zb3_term_2_1_anchor.
Print Assumptions zb3_Isum_1_1_anchor.
