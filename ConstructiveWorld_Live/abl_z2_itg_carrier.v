(* ConstructiveWorld -- abl_z2_itg_carrier.v: iterated-integral carrier for the Beukers double-integral family in the irrationality proof of zeta(2). *)
(** * abl_z2_itg_carrier: iterated-integral carrier of the double-integral family in the irrationality proof of zeta(2).
    Mission.  A segment carries a rational coefficient and a pair of factor
      lists (an [x]-polynomial, a [y]-polynomial); the [0,1]-polynomial
      integration operator [pint_integral] is applied twice, in [y]
      first and then in [x].  Shown: (1) the iterated integral of a
      segment equals C(n+m,n) B(n+m,n)^2, B the Beta value in
      coefficient-list closed form -- two single integrations, no
      order-swapping lemma; (2) the pointwise value of a segment list
      is (x(1-x))^n (y(1-y))^n [zb2_ps] n M (xy), the truncated
      integrand; (3) the integral sum over the segment list is
      sum_{m<=M} C(n+m,n) B(n+m,n)^2, every term strictly positive.
      Aggregating the whole family into one coefficient table is left
      out: factor lists grow with the segment index, and termwise
      addition would misalign Horner positions.
    Dependencies.  Stdlib [QArith], [ZArith], [Arith], [Lia]; the compiled
      modules [S01_BaseRing], [S02_CauchyComplete], [S03_QExp],
      [BeukersLists], [PolyIntegral], [PadeErrorIntegral]; the slice
      module [abl_z2_truncfam] ([zb2_ps]).  No external certificate
      checker, no real-number layer, no classical logic.
    References.  F. Beukers, A note on the irrationality of zeta(2) and
      zeta(3), Bull. London Math. Soc. 11 (1979): the iterated-integral
      representation of I_n and its polynomial kernel.
    Constructivity.  Purely constructive: no declared premises, no
      proof-abandoning statements, no pending premises; statement faces
      are [Qeq] equations and Set-level strict-positivity witnesses
      [QltT], positivity composed from binomial, factorial and Beta
      closed forms, no ordered-field decision procedure.
    Build.  [rocq c -native-compiler no -q -Q <world> "" abl_z2_itg_carrier.v]
      (Rocq 9.1.0), same-world dependency .vo chain. *)

From Stdlib Require Import QArith.QArith ZArith.ZArith Arith.Arith Lia.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Setoid.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp BeukersLists
              PolyIntegral PadeErrorIntegral.
Require Import abl_z2_truncfam.

Open Scope Q_scope.
Open Scope list_scope.

(* ============================================================ *)
(* Sec 0.  Base facts: multiplicative splitting of powers and the zero-degree partial sum. *)
(* ============================================================ *)

(* Power splits over a product base: (x*y)^k = x^k * y^k. *)
Lemma zb2_q_pow_mul : forall (x y : Q) (k : nat),
  QeqT (q_pow (x * y) k) ((q_pow x k * q_pow y k)%Q).
Proof.
  intros x y k.
  assert (Hcore : q_pow (x * y) k == (q_pow x k * q_pow y k)%Q).
  { induction k as [| k IH].
    - reflexivity.
    - rewrite (qeqT_imp_qeq _ _ (q_pow_succ (x * y) k)).
      rewrite (qeqT_imp_qeq _ _ (q_pow_succ x k)).
      rewrite (qeqT_imp_qeq _ _ (q_pow_succ y k)). rewrite IH. ring. }
  apply qeq_imp_qeqT. exact Hcore.
Qed.

(* The zero-degree partial sum is constantly 1: sum_{m<=0} C(n+m,n) t^m = C(n,n) = 1. *)
Lemma zb2_ps_zero : forall n t, QeqT (zb2_ps n 0 t) 1.
Proof.
  intros n t.
  assert (Hcore : zb2_ps n 0 t == 1).
  { unfold zb2_ps. cbn [bk_psQ q_pow].
    rewrite Nat.add_0_r.
    rewrite (S07_RealSetoidExpLog.RealSetoid.Id_eq _ _ (bkC_diag n)).
    cbn [Z.of_nat]. ring. }
  apply qeq_imp_qeqT. exact Hcore.
Qed.

(* ============================================================ *)
(* Sec 1.  Carrier definitions (interface face, signatures fixed). *)
(* ============================================================ *)

Definition zb2_seg : Set := (Q * (list Q * list Q))%type.

(* Canonical form of segment m: the coefficient C(n+m,n) with two copies of the factor list of t^{n+m} (1-t)^n. *)
Definition zb2_segof (n m : nat) : zb2_seg :=
  ((Z.of_nat (bkC (n + m) n) # 1)%Q,
   (pei_list (n + m) n, pei_list (n + m) n)).

(* Segment list: head at m = M, descending to m = 0. *)
Fixpoint zb2_segl (n M : nat) : list zb2_seg :=
  match M with
  | O => ((Z.of_nat (bkC (n + 0) n) # 1,
           (pei_list (n + 0) n, pei_list (n + 0) n)) :: nil)%list
  | Datatypes.S M' => (Z.of_nat (bkC (n + Datatypes.S M') n) # 1,
                       (pei_list (n + Datatypes.S M') n,
                        pei_list (n + Datatypes.S M') n)) :: zb2_segl n M'
  end.

(* Pointwise evaluation of a segment: the coefficient times the Horner value of the x factor list times the Horner value of the y factor list. *)
Definition zb2_beval (s : zb2_seg) (x y : Q) : Q :=
  fst s * pint_eval (fst (snd s)) x * pint_eval (snd (snd s)) y.

(* Pointwise evaluation of a segment list (summed segment by segment). *)
Fixpoint zb2_beval_l (l : list zb2_seg) (x y : Q) : Q :=
  match l with
  | nil => 0
  | s :: l' => zb2_beval s x y + zb2_beval_l l' x y
  end.

(* The y-integration operator: a segment is sent to an x-polynomial (coefficient = segment coefficient times the integral value of the y factor list). *)
Definition zb2_yint (s : zb2_seg) : list Q :=
  pint_scale (fst s * pint_integral (snd (snd s))) (fst (snd s)).

(* Iterated double integral of a segment: one more application of the integration operator, to the x-polynomial. *)
Definition zb2_di (s : zb2_seg) : Q := pint_integral (zb2_yint s).

(* Integral sum over a segment list (summed segment by segment). *)
Fixpoint zb2_di_l (l : list zb2_seg) : Q :=
  match l with
  | nil => 0
  | s :: l' => zb2_di s + zb2_di_l l'
  end.

(* Closed form of term m: C(n+m,n) B(n+m,n)^2, with B(a,n) = a! n! / (a+n+1)!. *)
Definition zb2_term (n m : nat) : Q :=
  (Z.of_nat (bkC (n + m) n) # 1)
    * (q_fact (n + m) * q_fact n / q_fact (n + m + n + 1))
    * (q_fact (n + m) * q_fact n / q_fact (n + m + n + 1)).

(* Closed-form term sum: sum_{m<=M} zb2_term n m. *)
Fixpoint zb2_Isum (n M : nat) : Q :=
  match M with
  | O => zb2_term n 0
  | Datatypes.S M' => zb2_Isum n M' + zb2_term n (Datatypes.S M')
  end.

(* ============================================================ *)
(* Sec 2.  Core statements: the twice-integrated value of a segment, the segment-list sum, the pointwise face, positivity. *)
(* ============================================================ *)

(* Closed form of the iterated double integral of a segment: two single
   integrations, y first and then x.  The y-integration gives the
   coefficient times B; the x-integration multiplies the scaled factor
   list by B once more, matching the two-factor closed form. *)
Lemma zb2_di_seg_eq : forall n m, QeqT (zb2_di (zb2_segof n m)) (zb2_term n m).
Proof.
  intros n m.
  assert (Hcore : zb2_di (zb2_segof n m) == zb2_term n m).
  { unfold zb2_di, zb2_yint, zb2_segof, zb2_term.
    cbn [fst snd].
    assert (Hs := qeqT_imp_qeq _ _
               (pint_integral_scale
                 ((Z.of_nat (bkC (n + m) n) # 1)
                  * pint_integral (pei_list (n + m) n))
                 (pei_list (n + m) n))).
    rewrite Hs. rewrite (qeqT_imp_qeq _ _ (pei_beta_value (n + m) n)). ring. }
  apply qeq_imp_qeqT. exact Hcore.
Qed.

(* The integral sum over the segment list equals the closed-form term sum (induction on M). *)
Lemma zb2_di_l_segl : forall n M, QeqT (zb2_di_l (zb2_segl n M)) (zb2_Isum n M).
Proof.
  intros n M.
  assert (Hcore : forall k, zb2_di_l (zb2_segl n k) == zb2_Isum n k).
  { induction k as [| k IH].
    - assert (H0 : zb2_segl n 0 = (zb2_segof n 0 :: nil)%list) by reflexivity.
      rewrite H0. cbn [zb2_di_l zb2_Isum].
      rewrite (qeqT_imp_qeq _ _ (zb2_di_seg_eq n 0)). ring.
    - assert (HS : zb2_segl n (Datatypes.S k)
                   = (zb2_segof n (Datatypes.S k)) :: zb2_segl n k) by reflexivity.
      rewrite HS. cbn [zb2_di_l zb2_Isum].
      rewrite (qeqT_imp_qeq _ _ (zb2_di_seg_eq n (Datatypes.S k))).
      rewrite IH. ring. }
  apply qeq_imp_qeqT. apply Hcore.
Qed.

(* Pointwise face: the value of the segment list is
   (x(1-x))^n (y(1-y))^n zb2_ps n M (xy).  Segment m contributes
   C(n+m,n) x^{n+m} (1-x)^n y^{n+m} (1-y)^n, folded into the last term
   of the partial sum. *)
Lemma zb2_beval_segl : forall n M x y,
  QeqT (zb2_beval_l (zb2_segl n M) x y)
       (q_pow (x * (1 - x)) n * q_pow (y * (1 - y)) n * zb2_ps n M (x * y)).
Proof.
  intros n M x y.
  assert (Hcore : zb2_beval_l (zb2_segl n M) x y
  == q_pow (x * (1 - x)) n * q_pow (y * (1 - y)) n * zb2_ps n M (x * y)).
  { induction M as [| M IH].
    - assert (H0 : zb2_segl n 0 = (zb2_segof n 0 :: nil)%list) by reflexivity.
      rewrite H0. cbn [zb2_beval_l].
      unfold zb2_beval, zb2_segof. cbn [fst snd].
      rewrite (qeqT_imp_qeq _ _ (pei_beta_eval (n + 0) n x)).
      rewrite (qeqT_imp_qeq _ _ (pei_beta_eval (n + 0) n y)).
      rewrite !Nat.add_0_r.
      rewrite (S07_RealSetoidExpLog.RealSetoid.Id_eq _ _ (bkC_diag n)).
      cbn [Z.of_nat].
      rewrite (qeqT_imp_qeq _ _ (zb2_ps_zero n (x * y))).
      rewrite (qeqT_imp_qeq _ _ (zb2_q_pow_mul x (1 - x) n)).
      rewrite (qeqT_imp_qeq _ _ (zb2_q_pow_mul y (1 - y) n)).
      ring.
    - assert (HS : zb2_segl n (Datatypes.S M)
                   = (zb2_segof n (Datatypes.S M)) :: zb2_segl n M) by reflexivity.
      rewrite HS. cbn [zb2_beval_l].
      unfold zb2_beval, zb2_segof. cbn [fst snd].
      rewrite (qeqT_imp_qeq _ _ (pei_beta_eval (n + Datatypes.S M) n x)).
      rewrite (qeqT_imp_qeq _ _ (pei_beta_eval (n + Datatypes.S M) n y)).
      rewrite (qeqT_imp_qeq _ _ (q_pow_add x n (Datatypes.S M))).
      rewrite (qeqT_imp_qeq _ _ (q_pow_add y n (Datatypes.S M))).
      rewrite IH.
      rewrite zb2_ps_unfold.
      rewrite (qeqT_imp_qeq _ _ (zb2_q_pow_mul x (1 - x) n)).
      rewrite (qeqT_imp_qeq _ _ (zb2_q_pow_mul y (1 - y) n)).
      rewrite (qeqT_imp_qeq _ _ (zb2_q_pow_mul x y (Datatypes.S M))).
      ring. }
  apply qeq_imp_qeqT. exact Hcore.
Qed.

(* Term m is strictly positive: C(n+m,n) >= 1, and the numerator and denominator factorials of the Beta value are both positive. *)
Lemma zb2_term_pos : forall n m, QltT 0 (zb2_term n m).
Proof.
  intros n m. apply Qlt_to_QltT. unfold zb2_term.
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
            * (q_fact (n + m) * q_fact n / q_fact (n + m + n + 1)))
           (q_fact (n + m) * q_fact n / q_fact (n + m + n + 1))).
  - apply Qmult_lt_0_compat; assumption.
  - exact Hbeta.
Qed.

(* The closed-form term sum is strictly positive: the first term is strictly positive, and summing nonnegative terms preserves strict positivity. *)
Lemma zb2_Isum_pos : forall n M, QltT 0 (zb2_Isum n M).
Proof.
  intros n M. induction M as [| M IH].
  - apply zb2_term_pos.
  - cbn [zb2_Isum]. apply pei_lt_le_plus.
    + exact IH.
    + apply qltT_leT'. apply zb2_term_pos.
Qed.

(* ============================================================ *)
(* Sec 3.  Closing audit: Print Assumptions self-check on the main statements. *)
(* ============================================================ *)

Print Assumptions zb2_di_seg_eq.
Print Assumptions zb2_di_l_segl.
Print Assumptions zb2_beval_segl.
Print Assumptions zb2_term_pos.
Print Assumptions zb2_Isum_pos.
