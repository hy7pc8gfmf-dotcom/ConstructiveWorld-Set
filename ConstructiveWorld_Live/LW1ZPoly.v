(* Five-field pointer | Module: LW1ZPoly.v.
   Mission.  The ring of univariate polynomials with integer coefficients:
   addition, scalar multiplication, multiplication, degree and the formal
   derivative, on coefficient tables carried low degree first (the zero
   polynomial is the empty table; trailing zeros are permitted and equality
   is table equality; the degree of the zero polynomial is 0 by convention),
   plus the homomorphism properties of the evaluation functor eval_Z at
   integer points (additive, multiplicative, scalar-linear) and the product
   rule for derivatives at the level of evaluated values.  Algebraic supply
   layer for downstream Hermite interpolation and transcendence chains.
   Dependencies.  Stdlib [ZArith], [Lia] only; no development-internal
   requires.  Statement faces are carried by the self-contained Set-level
   identity type [lw1_id] (same shape as the development base identity
   type, single reflective constructor, Set-sorted); the grouped export is
   a Set-level product (prod).
   References.  No external benchmark module is Required; the stdlib
   polynomial library was consulted for naming style only.  Statement
   names follow the baseline module verbatim (statement-face Set-carrier
   completion).
   Constructivity.  All operations are structural recursions; every proof
   is by induction and rewriting; each statement prints [Closed under the
   global context] and coqchk certifies the module with no assumed names;
   the extraction probe reports [Obj.magic] = 0 on both output faces.
   Prop-face equations appear only as in-body scaffolding asserts
   discharged by the kernel, never as statement faces.
   Build.  rocq c -native-compiler no -q -Q . "" LW1ZPoly.v, working
   directory = the seat sandbox world (flat single level, empty logical
   prefix); COQLIB and ROCQLIB environment variables are unset for the
   born compile.
*)

From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.

Open Scope Z_scope.

(* -------------------------------------------------------------------- *)
(* Set-level identity carrier.  Statements relate their two sides by     *)
(* [lw1_id], the Set-sorted Leibniz equality with the single reflective  *)
(* constructor; Prop-face [eq] serves only inside proof bodies.          *)
(* -------------------------------------------------------------------- *)

Inductive lw1_id {A : Set} (x : A) : A -> Set :=
  lw1_idrefl : lw1_id x x.

(* A polynomial is its coefficient table, low degree first:
   the table (cons a0 (cons a1 (cons a2 nil))) denotes
   a0 + a1*X + a2*X^2 + ... . *)
Definition zpoly := list Z.

(* -------------------------------------------------------------------- *)
(* Addition: pointwise, padding the shorter table with zeros.            *)
(* -------------------------------------------------------------------- *)

Fixpoint zpoly_add (p q : zpoly) : zpoly :=
  match p with
  | nil => q
  | cons a p' =>
      match q with
      | nil => p
      | cons b q' => cons (a + b) (zpoly_add p' q')
      end
  end.

Lemma zpoly_add_comm : forall p q : zpoly,
  lw1_id (zpoly_add p q) (zpoly_add q p).
Proof.
  assert (Hc : forall p q : zpoly, zpoly_add p q = zpoly_add q p).
  { induction p as [|a p' IH]; intros q; destruct q as [|b q'];
      simpl; try reflexivity.
    (* Induction step: the two heads add commutatively in Z, tails by IH. *)
    rewrite (IH q'). rewrite Z.add_comm. reflexivity. }
  intros p q. rewrite (Hc p q). apply lw1_idrefl.
Qed.

Lemma zpoly_add_assoc : forall p q r : zpoly,
  lw1_id (zpoly_add (zpoly_add p q) r) (zpoly_add p (zpoly_add q r)).
Proof.
  assert (Hc : forall p q r : zpoly,
    zpoly_add (zpoly_add p q) r = zpoly_add p (zpoly_add q r)).
  { induction p as [|a p' IH]; intros q r;
      destruct q as [|b q']; destruct r as [|c r']; simpl; try reflexivity.
    (* Induction step: heads associate in Z, tails by induction. *)
    rewrite (IH q' r'). f_equal. lia. }
  intros p q r. rewrite (Hc p q r). apply lw1_idrefl.
Qed.

(* Right unit: appending the empty table changes nothing. *)
Lemma zpoly_add_nil_r : forall p : zpoly, lw1_id (zpoly_add p nil) p.
Proof.
  assert (Hc : forall p : zpoly, zpoly_add p nil = p).
  { intros p. destruct p as [|a p']; reflexivity. }
  intros p. rewrite (Hc p). apply lw1_idrefl.
Qed.

(* -------------------------------------------------------------------- *)
(* Scalar multiplication by an integer coefficient.  Multiplying by 0    *)
(* returns the empty table exactly, which keeps the product recursion    *)
(* predictable at the degenerate coefficient.                            *)
(* -------------------------------------------------------------------- *)

Fixpoint zpoly_scalar (c : Z) (p : zpoly) : zpoly :=
  match p with
  | nil => nil
  | cons a p' => if Z.eqb c 0 then nil else cons (c * a) (zpoly_scalar c p')
  end.

Lemma zpoly_scalar_0 : forall p : zpoly, lw1_id (zpoly_scalar 0 p) nil.
Proof.
  assert (Hc : forall p : zpoly, zpoly_scalar 0 p = nil).
  { induction p as [|a p' IH]; simpl; reflexivity. }
  intros p. rewrite (Hc p). apply lw1_idrefl.
Qed.

Lemma zpoly_scalar_add : forall (c : Z) (p q : zpoly),
  lw1_id (zpoly_scalar c (zpoly_add p q))
         (zpoly_add (zpoly_scalar c p) (zpoly_scalar c q)).
Proof.
  assert (Hc : forall (c : Z) (p q : zpoly),
    zpoly_scalar c (zpoly_add p q) =
    zpoly_add (zpoly_scalar c p) (zpoly_scalar c q)).
  { intros c p q. destruct (Z.eqb c 0) eqn:Ec.
    - apply Z.eqb_eq in Ec. subst c.
      assert (Hs : forall r : zpoly, zpoly_scalar 0 r = nil).
      { intros [|a0 t0]; reflexivity. }
      rewrite !Hs. reflexivity.
    - revert q.
      induction p as [|a p' IH]; intros q; destruct q as [|b q'];
        simpl; try rewrite Ec; try reflexivity.
      (* Induction step: the coefficient distributes over the heads. *)
      rewrite IH. rewrite Z.mul_add_distr_l. reflexivity. }
  intros c p q. rewrite (Hc c p q). apply lw1_idrefl.
Qed.

(* -------------------------------------------------------------------- *)
(* Multiplication: convolution.  For p with head coefficient a and tail  *)
(* p' one has p * q = a * q + X * (p' * q), where X * r shifts the table *)
(* of r right by one position (a zero at the head, since the head        *)
(* carries degree 0).                                                    *)
(* -------------------------------------------------------------------- *)

Fixpoint zpoly_mul (p q : zpoly) : zpoly :=
  match p with
  | nil => nil
  | cons a p' =>
      zpoly_add (zpoly_scalar a q) (cons 0 (zpoly_mul p' q))
  end.

Lemma zpoly_mul_cons0 : forall (d q : zpoly),
  lw1_id (zpoly_mul (cons 0 d) q) (cons 0 (zpoly_mul d q)).
Proof.
  assert (Hc : forall (d q : zpoly),
    zpoly_mul (cons 0 d) q = cons 0 (zpoly_mul d q)).
  { intros d q. simpl.
    assert (Hs : zpoly_scalar 0 q = nil).
    { destruct q as [|a0 t0]; reflexivity. }
    rewrite Hs. reflexivity. }
  intros d q. rewrite (Hc d q). apply lw1_idrefl.
Qed.

(* -------------------------------------------------------------------- *)
(* Degree.  zpoly_deg_go scans the table carrying the index of its head; *)
(* the result is the largest index of a nonzero coefficient, and 0 for   *)
(* the zero polynomial (declared convention).                            *)
(* -------------------------------------------------------------------- *)

Fixpoint zpoly_deg_go (i : nat) (p : zpoly) : nat :=
  match p with
  | nil => 0
  | cons a p' =>
      if Z.eqb a 0
      then zpoly_deg_go (S i) p'
      else Nat.max i (zpoly_deg_go (S i) p')
  end.

Definition zpoly_degree (p : zpoly) : nat := zpoly_deg_go 0 p.

(* -------------------------------------------------------------------- *)
(* Formal derivative.  Writing p = a0 + X * t with t the polynomial of   *)
(* the tail coefficients, the derivative of p is t + X * t'.  This gives *)
(* a structural recursion with no index accumulator.                     *)
(* -------------------------------------------------------------------- *)

Fixpoint zpoly_deriv (p : zpoly) : zpoly :=
  match p with
  | nil => nil
  | cons a p' => zpoly_add p' (cons 0 (zpoly_deriv p'))
  end.

(* The derivative ignores the constant term, so a shifted table merely   *)
(* loses its head zero: deriv (X-shifted m) = m + X * deriv m. *)
Lemma zpoly_deriv_cons0 : forall m : zpoly,
  lw1_id (zpoly_deriv (cons 0 m)) (zpoly_add m (cons 0 (zpoly_deriv m))).
Proof.
  intros m. apply lw1_idrefl.
Qed.

Lemma zpoly_deriv_add : forall p q : zpoly,
  lw1_id (zpoly_deriv (zpoly_add p q))
         (zpoly_add (zpoly_deriv p) (zpoly_deriv q)).
Proof.
  assert (Hc : forall p q : zpoly,
    zpoly_deriv (zpoly_add p q) =
    zpoly_add (zpoly_deriv p) (zpoly_deriv q)).
  { induction p as [|a p' IH]; intros q.
    - reflexivity.
    - destruct q as [|b q'].
      + simpl.
        assert (Hnr : forall x : zpoly, zpoly_add x nil = x).
        { intros x0. destruct x0 as [|a0 t0]; reflexivity. }
        rewrite Hnr. reflexivity.
      + (* Induction step: differentiate termwise, then regroup the      *)
        (* three summands by associativity and commutativity of addition. *)
        simpl.
        rewrite IH.
        assert (Has : forall x y t : zpoly,
          zpoly_add (zpoly_add x y) t = zpoly_add x (zpoly_add y t)).
        { intros x y t. destruct (zpoly_add_assoc x y t). reflexivity. }
        assert (Hcm : forall x y : zpoly, zpoly_add x y = zpoly_add y x).
        { intros x y. destruct (zpoly_add_comm x y). reflexivity. }
        rewrite (Has p' q'
                   (cons 0 (zpoly_add (zpoly_deriv p') (zpoly_deriv q')))).
        rewrite (Has p' (cons 0 (zpoly_deriv p'))
                   (zpoly_add q' (cons 0 (zpoly_deriv q')))).
        rewrite <- (Has (cons 0 (zpoly_deriv p')) q'
                      (cons 0 (zpoly_deriv q'))).
        rewrite (Hcm (cons 0 (zpoly_deriv p')) q').
        rewrite (Has q' (cons 0 (zpoly_deriv p'))
                   (cons 0 (zpoly_deriv q'))).
        simpl. reflexivity. }
  intros p q. rewrite (Hc p q). apply lw1_idrefl.
Qed.

Lemma zpoly_deriv_scalar : forall (c : Z) (p : zpoly),
  lw1_id (zpoly_deriv (zpoly_scalar c p))
         (zpoly_scalar c (zpoly_deriv p)).
Proof.
  assert (Hc : forall (c : Z) (p : zpoly),
    zpoly_deriv (zpoly_scalar c p) = zpoly_scalar c (zpoly_deriv p)).
  { intros c p. destruct (Z.eqb c 0) eqn:Ec.
    - apply Z.eqb_eq in Ec. subst c.
      assert (Hs : forall r : zpoly, zpoly_scalar 0 r = nil).
      { intros [|a0 t0]; reflexivity. }
      rewrite !Hs. reflexivity.
    - induction p as [|a p' IH].
      + reflexivity.
      + (* Induction step: the constant c passes through the            *)
        (* differentiation, coefficientwise by c * 0 = 0.                 *)
        simpl. rewrite Ec. simpl. rewrite IH.
        assert (Hsa : forall (c0 : Z) (x y : zpoly),
          zpoly_scalar c0 (zpoly_add x y) =
          zpoly_add (zpoly_scalar c0 x) (zpoly_scalar c0 y)).
        { intros c0 x y. destruct (zpoly_scalar_add c0 x y). reflexivity. }
        rewrite Hsa. simpl. rewrite Ec.
        rewrite Z.mul_0_r. reflexivity. }
  intros c p. rewrite (Hc c p). apply lw1_idrefl.
Qed.

(* -------------------------------------------------------------------- *)
(* Evaluation at an integer point (ascending powers: each step           *)
(* contributes a_i * z^i and advances the running power by one factor z). *)
(* -------------------------------------------------------------------- *)

Fixpoint zpoly_eval_go (z pow : Z) (p : zpoly) : Z :=
  match p with
  | nil => 0
  | cons a p' => a * pow + zpoly_eval_go z (z * pow) p'
  end.

Definition zpoly_eval_Z (p : zpoly) (z : Z) : Z := zpoly_eval_go z 1 p.

Lemma zpoly_eval_go_add : forall (p q : zpoly) (z pow : Z),
  lw1_id (zpoly_eval_go z pow (zpoly_add p q))
         (zpoly_eval_go z pow p + zpoly_eval_go z pow q).
Proof.
  assert (Hc : forall (p q : zpoly) (z pow : Z),
    zpoly_eval_go z pow (zpoly_add p q) =
    zpoly_eval_go z pow p + zpoly_eval_go z pow q).
  { induction p as [|a p' IH]; intros q z pow; destruct q as [|b q'];
      simpl; try lia.
    (* Induction step: distribute over the heads, then apply the          *)
    (* induction conclusion to the padded tails.                          *)
    rewrite IH. rewrite Z.mul_add_distr_r. lia. }
  intros p q z pow. rewrite (Hc p q z pow). apply lw1_idrefl.
Qed.

Lemma zpoly_eval_add : forall (p q : zpoly) (z : Z),
  lw1_id (zpoly_eval_Z (zpoly_add p q) z)
         (zpoly_eval_Z p z + zpoly_eval_Z q z).
Proof.
  intros p q z. unfold zpoly_eval_Z. apply zpoly_eval_go_add.
Qed.

(* -------------------------------------------------------------------- *)
(* Evaluation is multiplicative.  The go-level statement carries a free  *)
(* running power: the value of a product table at power pow equals the   *)
(* value of p at pow times the value of q at power 1.  Two auxiliary     *)
(* identities (scaling and power rescaling of the running value) feed    *)
(* the induction; the top-level form instantiates pow with 1.            *)
(* -------------------------------------------------------------------- *)

(* Scaling every coefficient by c scales the value by c. *)
Lemma zpoly_eval_go_scalar : forall (c : Z) (q : zpoly) (z pow : Z),
  lw1_id (zpoly_eval_go z pow (zpoly_scalar c q))
         (c * zpoly_eval_go z pow q).
Proof.
  assert (Hc : forall (c : Z) (q : zpoly) (z pow : Z),
    zpoly_eval_go z pow (zpoly_scalar c q) = c * zpoly_eval_go z pow q).
  { intros c q. induction q as [|b q' IH]; intros z pow.
    - simpl. lia.
    - simpl. destruct (Z.eqb c 0) eqn:Ec.
      + apply Z.eqb_eq in Ec. subst c. simpl. lia.
      + (* Induction step: the factor c passes to the head product. *)
        simpl. rewrite IH. ring. }
  intros c q z pow. rewrite (Hc c q z pow). apply lw1_idrefl.
Qed.

(* Raising the running power to z is worth one factor of pow. *)
Lemma zpoly_eval_go_pow : forall (p : zpoly) (z pow : Z),
  lw1_id (zpoly_eval_go z pow p) (pow * zpoly_eval_go z 1 p).
Proof.
  assert (Hc : forall (p : zpoly) (z pow : Z),
    zpoly_eval_go z pow p = pow * zpoly_eval_go z 1 p).
  { induction p as [|a p' IH]; intros z pow.
    - simpl. lia.
    - (* Induction step: the running power advances on both sides, so the *)
      (* induction instance fires at z * pow and at z * 1.                 *)
      simpl. rewrite (IH z (z * pow)). rewrite (IH z (z * 1)). ring. }
  intros p z pow. rewrite (Hc p z pow). apply lw1_idrefl.
Qed.

Lemma zpoly_eval_go_mul : forall (p q : zpoly) (z pow : Z),
  lw1_id (zpoly_eval_go z pow (zpoly_mul p q))
         (zpoly_eval_go z pow p * zpoly_eval_go z 1 q).
Proof.
  assert (Hc : forall (p q : zpoly) (z pow : Z),
    zpoly_eval_go z pow (zpoly_mul p q) =
    zpoly_eval_go z pow p * zpoly_eval_go z 1 q).
  { intros p q. induction p as [|a p' IH]; intros z pow.
    - simpl. lia.
    - (* Induction step: split a*q + X*(p'*q), evaluate each part. *)
      simpl.
      assert (Hga : forall (x y : zpoly) (z0 pow0 : Z),
        zpoly_eval_go z0 pow0 (zpoly_add x y) =
        zpoly_eval_go z0 pow0 x + zpoly_eval_go z0 pow0 y).
      { intros x y z0 pow0. destruct (zpoly_eval_go_add x y z0 pow0).
        reflexivity. }
      assert (Hgs : forall (c0 : Z) (x : zpoly) (z0 pow0 : Z),
        zpoly_eval_go z0 pow0 (zpoly_scalar c0 x) =
        c0 * zpoly_eval_go z0 pow0 x).
      { intros c0 x z0 pow0. destruct (zpoly_eval_go_scalar c0 x z0 pow0).
        reflexivity. }
      rewrite Hga. rewrite Hgs. simpl.
      rewrite IH.
      assert (Hgp : forall (x : zpoly) (z0 pow0 : Z),
        zpoly_eval_go z0 pow0 x = pow0 * zpoly_eval_go z0 1 x).
      { intros x z0 pow0. destruct (zpoly_eval_go_pow x z0 pow0).
        reflexivity. }
      rewrite (Hgp q z pow). ring. }
  intros p q z pow. rewrite (Hc p q z pow). apply lw1_idrefl.
Qed.

Lemma zpoly_eval_Z_mul : forall (p q : zpoly) (x : Z),
  lw1_id (zpoly_eval_Z (zpoly_mul p q) x)
         (zpoly_eval_Z p x * zpoly_eval_Z q x).
Proof.
  intros p q x. unfold zpoly_eval_Z. apply zpoly_eval_go_mul.
Qed.

(* A leading zero contributes nothing by itself but multiplies the       *)
(* running power by z. *)
Lemma zpoly_eval_go_cons0 : forall (r : zpoly) (z pow : Z),
  lw1_id (zpoly_eval_go z pow (cons 0 r)) (zpoly_eval_go z (z * pow) r).
Proof.
  assert (Hc : forall (r : zpoly) (z pow : Z),
    zpoly_eval_go z pow (cons 0 r) = zpoly_eval_go z (z * pow) r).
  { intros r z pow. simpl. lia. }
  intros r z pow. rewrite (Hc r z pow). apply lw1_idrefl.
Qed.

(* -------------------------------------------------------------------- *)
(* The product rule at the level of values.  The list-level statement    *)
(* is false in this representation (zero pruning of scalar products),    *)
(* but both sides evaluate identically: induction on p reduces the       *)
(* goal, via the additivity and multiplicativity of the evaluator, to    *)
(* a ring identity between integer evaluation values.                    *)
(* -------------------------------------------------------------------- *)

Lemma zpoly_eval_go_deriv_mul : forall (p q : zpoly) (z pow : Z),
  lw1_id (zpoly_eval_go z pow (zpoly_deriv (zpoly_mul p q)))
         (zpoly_eval_go z pow
            (zpoly_add (zpoly_mul (zpoly_deriv p) q)
                       (zpoly_mul p (zpoly_deriv q)))).
Proof.
  assert (Hc : forall (p q : zpoly) (z pow : Z),
    zpoly_eval_go z pow (zpoly_deriv (zpoly_mul p q)) =
    zpoly_eval_go z pow
      (zpoly_add (zpoly_mul (zpoly_deriv p) q)
                 (zpoly_mul p (zpoly_deriv q)))).
  { intros p q. induction p as [|a p' IH]; intros z pow.
    - simpl. reflexivity.
    - (* Unfold the product by its defining recursion, then differentiate  *)
      (* the two summands by the add / cons0 / scalar derivative laws.      *)
      assert (Hm : zpoly_mul (cons a p') q =
                   zpoly_add (zpoly_scalar a q) (cons 0 (zpoly_mul p' q)))
        by reflexivity.
      rewrite Hm.
      assert (Hda : forall x y : zpoly,
        zpoly_deriv (zpoly_add x y) =
        zpoly_add (zpoly_deriv x) (zpoly_deriv y)).
      { intros x y. destruct (zpoly_deriv_add x y). reflexivity. }
      rewrite Hda.
      assert (Hdc : forall x : zpoly,
        zpoly_deriv (cons 0 x) = zpoly_add x (cons 0 (zpoly_deriv x)))
        by reflexivity.
      rewrite Hdc.
      assert (Hds : forall (c0 : Z) (x : zpoly),
        zpoly_deriv (zpoly_scalar c0 x) = zpoly_scalar c0 (zpoly_deriv x)).
      { intros c0 x. destruct (zpoly_deriv_scalar c0 x). reflexivity. }
      rewrite Hds.
      assert (Hd : zpoly_deriv (cons a p') =
                   zpoly_add p' (cons 0 (zpoly_deriv p'))) by reflexivity.
      rewrite Hd.
      (* Evaluate both sides additively / multiplicatively down to Z. *)
      assert (Hga : forall (x y : zpoly) (z0 pow0 : Z),
        zpoly_eval_go z0 pow0 (zpoly_add x y) =
        zpoly_eval_go z0 pow0 x + zpoly_eval_go z0 pow0 y).
      { intros x y z0 pow0. destruct (zpoly_eval_go_add x y z0 pow0).
        reflexivity. }
      assert (Hgm : forall (x y : zpoly) (z0 pow0 : Z),
        zpoly_eval_go z0 pow0 (zpoly_mul x y) =
        zpoly_eval_go z0 pow0 x * zpoly_eval_go z0 1 y).
      { intros x y z0 pow0. destruct (zpoly_eval_go_mul x y z0 pow0).
        reflexivity. }
      rewrite !Hga.
      rewrite !Hgm.
      rewrite !Hga.
      assert (Hgs : forall (c0 : Z) (x : zpoly) (z0 pow0 : Z),
        zpoly_eval_go z0 pow0 (zpoly_scalar c0 x) =
        c0 * zpoly_eval_go z0 pow0 x).
      { intros c0 x z0 pow0. destruct (zpoly_eval_go_scalar c0 x z0 pow0).
        reflexivity. }
      rewrite !Hgs.
      assert (Hgc : forall (x : zpoly) (z0 pow0 : Z),
        zpoly_eval_go z0 pow0 (cons 0 x) = zpoly_eval_go z0 (z0 * pow0) x).
      { intros x z0 pow0. destruct (zpoly_eval_go_cons0 x z0 pow0).
        reflexivity. }
      rewrite !Hgc.
      rewrite IH.
      rewrite !Hga.
      rewrite !Hgm.
      (* Unfold the head value of the shifted factor and normalise the      *)
      (* scalar term by the power rescaling, then the goal is a Z identity.  *)
      assert (Hc0 : zpoly_eval_go z pow (cons a p') =
                   a * pow + zpoly_eval_go z (z * pow) p') by reflexivity.
      rewrite Hc0.
      assert (Hgp : forall (x : zpoly) (z0 pow0 : Z),
        zpoly_eval_go z0 pow0 x = pow0 * zpoly_eval_go z0 1 x).
      { intros x z0 pow0. destruct (zpoly_eval_go_pow x z0 pow0).
        reflexivity. }
      rewrite (Hgp (zpoly_deriv q) z pow).
      ring. }
  intros p q z pow. rewrite (Hc p q z pow). apply lw1_idrefl.
Qed.

Lemma zpoly_deriv_mul : forall (p q : zpoly) (x : Z),
  lw1_id (zpoly_eval_Z (zpoly_deriv (zpoly_mul p q)) x)
         (zpoly_eval_Z (zpoly_add (zpoly_mul (zpoly_deriv p) q)
                                  (zpoly_mul p (zpoly_deriv q))) x).
Proof.
  intros p q x. unfold zpoly_eval_Z. apply zpoly_eval_go_deriv_mul.
Qed.

(* -------------------------------------------------------------------- *)
(* Ring export of the evaluator.  The three pointwise identities:        *)
(* additivity, multiplicativity and scalar linearity of zpoly_eval_Z,    *)
(* stated under one uniform naming scheme and grouped into a single      *)
(* entry for downstream consumers (Hermite coefficient accounting and    *)
(* evaluation of the e-transcendence chain at integer points).           *)
(* Packaging form (self-declared): one Lemma whose statement is the      *)
(* iterated Set-level product of the three eval_Z-level pointwise        *)
(* identity carriers; every carrier is Set-sorted data (zpoly, Z)        *)
(* compared by the Set-level identity type, and every component is       *)
(* discharged by an exact reference to a lemma proved above, so no       *)
(* identity is proved twice.                                             *)
(* -------------------------------------------------------------------- *)

(* Additive member under the uniform name: exact reference to the       *)
(* verified additive identity (the statements are alpha-equivalent).    *)
Lemma zpoly_eval_Z_add : forall (p q : zpoly) (x : Z),
  lw1_id (zpoly_eval_Z (zpoly_add p q) x)
         (zpoly_eval_Z p x + zpoly_eval_Z q x).
Proof.
  exact zpoly_eval_add.
Qed.

(* Scalar member: multiplying the table by k multiplies the value by k. *)
Lemma zpoly_eval_Z_scalar : forall (k : Z) (p : zpoly) (x : Z),
  lw1_id (zpoly_eval_Z (zpoly_scalar k p) x)
         (k * zpoly_eval_Z p x).
Proof.
  intros k p x. unfold zpoly_eval_Z. apply zpoly_eval_go_scalar.
Qed.

(* The grouped export: evaluation at any integer point respects the     *)
(* pointwise operations: addition, multiplication and scalar            *)
(* multiplication, in one conjunctive statement.                        *)
Lemma zpoly_eval_Z_ring_hom : forall (p q : zpoly) (k x : Z),
  prod (lw1_id (zpoly_eval_Z (zpoly_add p q) x)
               (zpoly_eval_Z p x + zpoly_eval_Z q x))
       (prod (lw1_id (zpoly_eval_Z (zpoly_mul p q) x)
                    (zpoly_eval_Z p x * zpoly_eval_Z q x))
             (lw1_id (zpoly_eval_Z (zpoly_scalar k p) x)
                     (k * zpoly_eval_Z p x))).
Proof.
  intros p q k x. split.
  - exact (zpoly_eval_add p q x).
  - split.
    + exact (zpoly_eval_Z_mul p q x).
    + exact (zpoly_eval_Z_scalar k p x).
Qed.

Print Assumptions zpoly_add_comm.
Print Assumptions zpoly_add_assoc.
Print Assumptions zpoly_add_nil_r.
Print Assumptions zpoly_scalar_0.
Print Assumptions zpoly_scalar_add.
Print Assumptions zpoly_mul_cons0.
Print Assumptions zpoly_deriv_cons0.
Print Assumptions zpoly_deriv_add.
Print Assumptions zpoly_deriv_scalar.
Print Assumptions zpoly_eval_go_add.
Print Assumptions zpoly_eval_add.
Print Assumptions zpoly_eval_go_scalar.
Print Assumptions zpoly_eval_go_pow.
Print Assumptions zpoly_eval_go_mul.
Print Assumptions zpoly_eval_Z_mul.
Print Assumptions zpoly_eval_go_cons0.
Print Assumptions zpoly_eval_go_deriv_mul.
Print Assumptions zpoly_deriv_mul.
Print Assumptions zpoly_eval_Z_add.
Print Assumptions zpoly_eval_Z_scalar.
Print Assumptions zpoly_eval_Z_ring_hom.
